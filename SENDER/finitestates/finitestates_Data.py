import sys
import signal
import os
import thread
from threading import *
from time import *
import xml.parsers.expat
import getopt
import random
import datetime
import re

########################################################################
# GLOBALS

import MySQLdb
sleepTime = None
hostDB = ""
userDB = ""
passwdDB = ""
dbDB = ""
tableDB = ""
connectionDB = None
cursorDB = None
lockDB = Lock()
primaryKeyField = ""
primaryKeyField2 = "dir"
statusField = ""
timeField = ""
fields = []
sleeper = Condition()
sleeper.status = "NESSUNO"
ruleList = []
logfilename = None
logfile = None
logLock = Lock()
allThreadsMustStop = False
maximumRuleNumber = 0
#########################################################################
# UTILITY

def indent(s, indentation = "  " ) :
    if s.strip()=="" : return ""
    r = ""
    if s[len(s)-1] == "\n" : s = s[:len(s)-1]
    for l in s.split("\n") :
        r += indentation+l+"\n"
    return r

sequenzatmp = 0
def tempname(s) :
    global sequenzatmp
    r = "pytemp-"
    r += str(os.getpid())+"-"
    r += str(thread.get_ident())+"-"
    r += s+"-"
    r += str(time())+"-"
    r += str(random.randint(0,900000))+"-"
    r += str(sequenzatmp)
    sequenzatmp += 1
    if sequenzatmp>100000 : sequenzatmp = 0
    r += ".tmp"
    try : r = os.path.join(os.environ['TMPDIR'], r)
    except KeyError : pass
    return r

class Watchdog(Thread):
    def __init__(this) :
        Thread.__init__(this)
        this.processes={}
        this.released=[]
        this.sleeper=Condition()
    def run(this) :
        while (True) :
            # remove already finished
            while this.released!=[] :
                rpid = this.released.pop()
                if rpid in this.processes.keys() : del this.processes[rpid]
            # kill if necessary
            for pid in this.processes.keys() :
                toolate = this.processes[pid]
                if time()>toolate :
                    # logging
                    (cstdout, cstdin) = os.popen2("ps u --pid "+str(pid))
                    ps_result = ""
                    for l in cstdin.readlines() : ps_result += l
                    ps_result=ps_result.strip()
                    dt = datetime.datetime.now().ctime()
                    indentationString = dt+": killing :"
                    st = indent(ps_result, indentationString)
                    logLock.acquire()
                    logfile.write(st)
                    logfile.flush()
                    logLock.release()
                    # kill
                    try : os.kill(pid,signal.SIGKILL)
                    except : pass
                    del this.processes[pid]
            # sleep
            mintoolate=-1
            for pid in this.processes.keys() :
                if mintoolate<0 : mintoolate=this.processes[pid]
                if mintoolate>this.processes[pid] : mintoolate=this.processes[pid]
            if mintoolate>0 :
                # print "sleep "+str(mintoolate-time())
                this.sleeper.acquire()
                this.sleeper.wait(mintoolate-time()+1)
                this.sleeper.release()
                # print "go on"
    def lookafter(this, pid, toolate) :
        # print "lookafter "+str(pid)
        this.processes[pid]=toolate
        this.sleeper.acquire()
        this.sleeper.notifyAll()
        this.sleeper.release()
    def release(this, pid) :
        # print "release "+str(pid)
        this.released.append(pid)
        this.sleeper.acquire()
        this.sleeper.notifyAll()
        this.sleeper.release()

watchdog = Watchdog()
watchdog.setDaemon(True)
watchdog.start()


#######################################################################
# RULE

class Rule (Thread):
    """ """
    def __init__(this) :
        Thread.__init__(this)
        this.status = []
        this.command = None
        this.queue = None
        this.timeout = None
        this.condit = {}
	this.elsestatus = None
	this.sleepTime = None
	this.count = 0

    def addCondit(this, code, status) :
        this.condit[code] = status

    def setCommand(this, command) :
        this.command = command

    def setQueue(this, queue = None) :
        this.queue = queue

    def setSleepTime(this, time = None) :
        this.sleepTime = time

    def setTimeout(this, timeout = None) :
        this.timeout = timeout

    def addStatus(this, status) :
        this.status.append(status)

    def setElseStatus(this, elsestatus) :
        this.elsestatus = elsestatus

    def __str__ (this) :
        return repr(this)

    def __repr__ (this) :
	r = ""
        for s in this.status :
            r += "<status>"+str(s)+"</status>\n"
        if this.command :
            r += "<command>\n"
            r += indent(this.command)
            r += "</command>\n"
        for c in this.condit.keys() :
            r += "<if code=\""+str(c)+"\" status=\""+this.condit[c]+"\" />\n"
	if this.elsestatus :
	    r += "<else status=\""+this.elsestatus+"\" />\n"
	st = "<rule"
        if this.timeout : st += " timeout=\""+str(this.timeout)+"\""
	if this.sleepTime : st += " sleep=\""+str(this.sleepTime)+"\""
	st += ">\n"
	r = st+indent(r)+"</rule>\n"
        return r

    def run(this) :
        global allThreadsMustStop
	# time to sleep
	timeToSleep = 1
	if this.sleepTime : timeToSleep = this.sleepTime
        elif sleepTime : timeToSleep = sleepTime
	# non-database rules
        if len(this.status)==0 :
	    while (not allThreadsMustStop) :
		if this.queue : this.queue.acquire()
                this.execute(None,None)
                if this.queue : this.queue.release()
	        sleeper.acquire()
		sleeper.wait(timeToSleep)
                sleeper.release()
	# database rules
        names = {} 
	fullnames = {}
	conditions = ""
	strada = ""
	for c in this.status :
	    if conditions!="" : conditions += " or "
	    conditions += statusField+" = \""+c+"\""
        while (not allThreadsMustStop) :
            # TO DO : temporizzazioni
            # TO DO : controllo code in push
            # try to read new elements from the database
            gotNewElements = False
	    lockDB.acquire()
	    ##print "MJB DEBUG sono in run(this)"
	    ###cursorDB.execute ("select "+primaryKeyField+" from "+tableDB+" where "+conditions);
	    cursorDB.execute ("select "+primaryKeyField+", dir from "+tableDB+" where "+conditions);

	    while (True) :
	        row = cursorDB.fetchone();
	        if not row : break
		name = row[0]
		strada = row[1]
		fullname = str(strada)+"?"+str(name)
		###print "MJB DEBUG "+fullname
		###if not name in names.keys() :
		if not fullname in fullnames.keys() : 
		    ###print "MJB DEBUG Newelement "+fullname
		    names[name] = 0.0
		    fullnames[fullname]=0.0
		    gotNewElements = True
	    lockDB.release()
            # if no new element, sleep
	    if not gotNewElements :
	        sleeper.acquire()
		sleepingDest = time()+timeToSleep
		while (time()<sleepingDest) :
			sleeper.wait(sleepingDest-time())
			if sleeper.status in this.status : break
		sleeper.release()
	    # process the elements
            ###for name in names.keys() :
            for fullname in fullnames.keys() :	
	        strada,name = fullname.split("?")    
		###if names[name]>time() : continue
		if fullnames[fullname]>time() : continue
                if this.queue : this.queue.acquire()
                if this.execute(name,strada) : 
			###print "MJB DEBUG name in del"+name+" "+strada+"---"
			##DAV del names[name]
			del fullnames[fullname]
                ###DAV else : names[name] = time()+timeToSleep
		else : fullnames[fullname] = time()+timeToSleep
                if this.queue : this.queue.release()
                
    def execute (this, name,strada) :
        """Execute the operation immediately on the item name;
	return True if state changed."""
	global allThreadsMustStop, maximumRuleNumber
	###print "MJB DEBUG sono in execute"+name+" "+strada
        # temp files
        tempEnv=tempname('env')
        tempOut=tempname('out')
        tempErr=tempname('err')
        # keyfields
        keyfields = ""
        for f in fields :
                if keyfields != "" : keyfields += ", "
                keyfields += f
        # Environment
        env = {}
	for k in os.environ : env[k] = os.environ[k] 
	if name and strada:
 	    lockDB.acquire()
            ###cursorDB.execute ("select "+keyfields+" from "+tableDB+" where "+primaryKeyField+" = \""+name+"\"");
            ###print "MJB DEBUG select "+keyfields+" from "+tableDB+" where "+primaryKeyField+" = \""+name+"\" and dir=\""+strada+"\" "
            cursorDB.execute ("select "+keyfields+" from "+tableDB+" where "+primaryKeyField+" = \""+name+"\" and dir=\""+strada+"\" ");
            row = cursorDB.fetchone();
	    lockDB.release()
	    if len(fields)>0:
            	for n in range(len(fields)) : 
	    		##print "MJB DEBUG ENNE "+str(n)+" "+this.command+" "+name+" "+strada+"---"
	    		env[fields[n]] = str(row[n])
        env['envDump'] = tempEnv
	
        # run
        command = this.command
        command_for_log = this.command
        dt = datetime.datetime.now().ctime()
        indentationString = dt+": starting"
        if name : indentationString += " "+primaryKeyField+" = "+name+" "+strada
        indentationString += " :"
	st = indent(command_for_log, indentationString)
	logLock.acquire()
	logfile.write(st)
	logfile.flush()
	logLock.release()
        command = "("+command+") >"+tempOut+" 2>"+tempErr
        pid = os.spawnlpe(os.P_NOWAIT, "bash", "bash", "-c", command, env)
        if this.timeout : watchdog.lookafter(pid,time()+this.timeout)
        (npid, r) = os.waitpid(pid, 0)
        if this.timeout : watchdog.release(pid)
        r>>=8
        # read environment
        if os.access(tempEnv, os.F_OK) :
            envF = open(tempEnv)
            for l in envF.readlines() :
                d=l.strip().split('=')
                env[d[0]]=d[1]
            envF.close()
        # read output
        outS = ""
        outF = open(tempOut)
        for l in outF.readlines() : outS += l
        outF.close()
        errS = ""
        errF = open(tempErr)
        for l in errF.readlines() : errS += l
        errF.close()
        # delete temp files
        os.system("rm -f "+tempEnv)
        os.system("rm -f "+tempOut)
        os.system("rm -f "+tempErr)
        # update status
	changed = False
	newStatus = "NESSUNO"
        try :
	    env[statusField] = this.condit[r]
            newStatus = this.condit[r]
	    if not (this.condit[r] in this.status) : changed = True
	except KeyError : 
	    if this.elsestatus : 
		env[statusField] = this.elsestatus
                newStatus = this.elsestatus
		if not (this.elsestatus in this.status) : changed = True
        # save in DB...
	if name :
	    setv = ""
            for f in fields :
		if setv != "" : setv += ", "
		setv += f + "=\"" +env[f]+ "\""
            lockDB.acquire()
            ### MJB cursorDB.execute ("update "+tableDB+" set "+setv+" where "+primaryKeyField+" = \""+name+"\"");
            cursorDB.execute ("update "+tableDB+" set "+setv+" where "+primaryKeyField+" = \""+name+"\" and dir=\""+env[primaryKeyField2]+"\" ");
            lockDB.release()
	# logging outS, errS
	outS = outS.strip()
	errS = errS.strip()
	dt = datetime.datetime.now().ctime()
        indentationString = dt+": finished"
        if name : indentationString += " "+primaryKeyField+" = "+name
        indentationString += " :"
	st = indent(command_for_log, indentationString)
	if outS!="" : st += indent(outS, dt+": out :")
	if errS!="" : st += indent(errS, dt+": err :")
	logLock.acquire()
	logfile.write(st)
	logfile.flush()
	logLock.release()
	# notify
        sleeper.acquire()
	sleeper.status = newStatus
        sleeper.notifyAll()
        sleeper.release()
	# return
	this.count += 1
	if (maximumRuleNumber>0 and this.count>=maximumRuleNumber) :
		allThreadsMustStop = True
	return changed




################################################################
# QUEUE

class FSQueue  :
    def __init__ (this) :
        this.lock = Lock()

    def acquire(this) :
        this.lock.acquire()

    def release(this) :
        this.lock.release()




########################################################################
# LETTURA XML


queue = None
rule = None
fsm = False
dbinfo = False
ruletype = None
def start_element(name, attrs):
    global rule, fsm, ruletype, queue, dbinfo, hostDB, userDB, passwdDB, dbDB, tableDB, primaryKeyField, statusField, fields, sleepTime, logfilename, timeField 
    if name=="finitestates_Data" : 
	fsm = True
	try : sleepTime = int(attrs["sleep"])
        except KeyError : pass
        try : logfilename = attrs["log"]
        except KeyError : pass
    if not fsm : return
    if name=="queue" : queue = FSQueue()
    if name=="rule" : 
	rule = Rule()
	try : rule.setTimeout(int(attrs["timeout"]))
	except KeyError : pass
	try : rule.setSleepTime(int(attrs["sleep"]))
        except KeyError : pass
	if queue : rule.setQueue(queue)
	ruleList.append(rule)
    if name=="database" :
	dbinfo = True
	try : hostDB = attrs["host"]
	except KeyError : pass
        try : userDB = attrs["user"]
	except KeyError : pass
        try : passwdDB = attrs["passwd"]
	except KeyError : pass
        try : dbDB = attrs["db"]
	except KeyError : pass
        try : tableDB = attrs["table"]
	except KeyError : pass
        try : primaryKeyField = attrs["primarykey"]
	except KeyError : pass
        try : statusField = attrs["status"]
	except KeyError : pass
        try : timeField = attrs["time"]
        except KeyError : pass
    if rule :
        if name=="status" : ruletype = "status"
        if name=="command" : ruletype = "command"
        if name=="if" : 
            ruletype = "condit"
	    rule.addCondit(int(attrs["code"]), str(attrs["status"]))
        if name=="else" :
            ruletype = "else"
            rule.setElseStatus(str(attrs["status"]))
    if dbinfo : 
	if name=="field" : ruletype = "field"
def end_element(name):
    global rule, fsm, ruletype, queue, dbinfo, hostDB, userDB, passwdDB, dbDB, tableDB, primaryKeyField, statusField, fields
    if name=="finitestates_Data" : fsm = False
    if not fsm : return
    if name=="queue" : queue = None
    if name=="rule" : rule = None
    if name=="database" : dbinfo = False
    if rule :
        if name=="status" : ruletype = None
        if name=="command" : ruletype = None
        if name=="condit" : ruletype = None
        if name=="else" : ruletype = None
    if dbinfo : 
	if name=="field" : ruletype = None
def char_data(data):
    global rule, fsm, ruletype, queue, dbinfo, hostDB, userDB, passwdDB, dbDB, tableDB, primaryKeyField, statusField, fields
    data=data.strip()
    if data=='' : return 
    if rule : 
        if ruletype=="status" : rule.addStatus(str(data))
        if ruletype=="command" : rule.setCommand(str(data))
    if dbinfo :
        if ruletype=="field" : fields.append(str(data))


def readXML(filename) :
    ruleList = []
    p = xml.parsers.expat.ParserCreate()
    p.StartElementHandler = start_element
    p.EndElementHandler = end_element
    p.CharacterDataHandler = char_data
    p.ParseFile(file(filename))



#####################################################################
# SCRITTURA XML

def writeRulesXML() :
    qs = {}
    st = ""
    for s in ruleList : 
	if s.queue : qs[s.queue] = 1
	else : st += repr(s)
    for q in qs.keys() :
	st += "<queue>\n"
        for s in ruleList :
            if s.queue==q : st += indent(repr(s))
        st += "</queue>\n"
    return st

def writeDatabase() :
    r = "<database"
    if hostDB : r += " host=\""+hostDB+"\""
    if userDB : r += " user=\""+userDB+"\""
    if passwdDB : r += " passwd=\""+passwdDB+"\""
    if dbDB : r += " db=\""+dbDB+"\""
    if tableDB : r += " table=\""+tableDB+"\""
    if primaryKeyField : r += " primarykey=\""+primaryKeyField+"\""
    if statusField : r += " status=\""+statusField+"\""
    if timeField : r += " time=\""+timeField+"\""
    r += ">\n"
    for f in fields :
	r +=indent("<field>"+f+"</field>\n")
    r += "</database>\n"
    return r

def writeXML() :
    st = "<finitestates_Data"
    if sleepTime : st += " sleep=\""+str(sleepTime)+"\""
    if logfilename : st += " log=\""+logfilename+"\""
    st += ">\n"
    st += indent(writeDatabase())
    st += indent(writeRulesXML())
    st += "</finitestates_Data>\n"
    print st



#############################################################################
# REPORT NUMBER OF STATES

def reportNumebrOfStates() :
    lockDB.acquire()
    cursorDB.execute ("select count(status) from "+tableDB);
    row = cursorDB.fetchone();
    print "Total items: "+str(row[0])
    cursorDB.execute ("select distinct(status) from "+tableDB);
    tuttiStatus = []
    while (True) :
        row = cursorDB.fetchone();
        if not row : break
        tuttiStatus.append(row[0])
    for s in tuttiStatus :
	query = "select count(status)"
	if timeField :
            query +=",from_unixtime(min("+timeField+"))"
	query += " from "+tableDB+" where status=\""+s+"\"";
	cursorDB.execute(query);
        row = cursorDB.fetchone();
        if not row : break
	answ = s+" : "+str(row[0])
	if timeField : answ += " ; first: "+str(row[1])
	print answ
    lockDB.release()

#############################################################################
# MAIN


# OPTIONS
#
# -t : only test; read and then output the xml as it understood it
# -s n : run no more than n times each rule
# -r : only report the number of states

onlyTest = False
onlyReport = False
try:
  optlist, args = getopt.getopt(sys.argv[1:], 'trs:')
except getopt.GetoptError:
  print "Usage:"
  print " python finitestates.py (options) file1.xml file2.xml"
  print "OPTIONS"
  print " -t : only test; read and then output the xml as it understood it"
  print " -s n : run no more than n times each rule"
  print " -r : only report the number of states"
  sys.exit(2)
for t, v in optlist : 
#	print t+" -> "+v
	if t=='-t' : onlyTest = True; continue;
	if t=='-s' : maximumRuleNumber = int(v); continue;
	if t=='-r' : onlyReport = True; continue;
for p in args : 
    try :
	readXML(p)
    except IOError, e:
        print e
        sys.exit(2)


if onlyTest :
	writeXML()
	sys.exit(0)

if hostDB :
    connectionDB = MySQLdb.connect (host = hostDB,
                                    user = userDB,
                                    passwd = passwdDB,
                                    db = dbDB)
    cursorDB = connectionDB.cursor()
else :
    connectionDB=None
    cursorDB=None

if logfilename : logfile = open(logfilename, "a") 
else : logfile=sys.stdout
dt = datetime.datetime.now().ctime()


if onlyReport :
        reportNumebrOfStates()
	sys.exit(0)

logLock.acquire()
logfile.write(dt+": BEGIN OF SESSION : finitestates\n")
logfile.flush()
logLock.release()

for s in ruleList : s.start()

# control-c handling
def control_c_handler(signum, frame):
  global allThreadsMustStop
  allThreadsMustStop = True
signal.signal(signal.SIGINT, control_c_handler)
while (not allThreadsMustStop) : sleep(1)

