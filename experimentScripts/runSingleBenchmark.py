#!/usr/bin/env python
# Receive the name of a single experiment (as in "real/fulsom") and settings. Run the experiment, saving the executable and log under appropriate directories.
# Assume: that make clean && make boot" and a baseline experiment have been run at the top level.
# Settings: debug mode includes -ddump-simpl and -ddump-stg.
import subprocess as sp
import os 
from sys import argv
from string import join

under = argv[1]
name = argv[2]
mode = argv[3]
logsLocation = argv[4]
verbosity = argv[5]

# Common settings
settings = ["-ticky", "-ddump-simpl", "-ddump-stg", "-fexpose-all-unfoldings", "-dcore-lint"] #, "-dverbose-core2core"]

if mode == "plain":
    modeName="Plain"
else:
    budget = float(mode)
    pluginSettings = ["-fplugin=BinaryMAB.Plugin", "-fplugin-opt=BinaryMAB.Plugin:%f:15:beforeSimplifier:[5,20,50,5,5,3]" % budget]
#    pluginSettings = ["-fplugin=BinaryMAB.Plugin", "-fplugin-opt=BinaryMAB.Plugin:%f:15:last:[2,8,20,2,2,1]" % budget]
#    pluginSettings = ["-fplugin=BinaryMAB.Plugin", "-fplugin-opt=BinaryMAB.Plugin:%f:15:last:[1,4,10,1,1,1]" % budget]
#    pluginSettings = ["-fplugin=BinaryMAB.Plugin", "-fplugin-opt=BinaryMAB.Plugin:%f:15:last:[1,1,1,1,1,1]" % budget]
    settings = settings + pluginSettings
    modeName = "B%04d"%budget

if verbosity == "core2core":
    settings = settings+["-dverbose-core2core"]
    modeName = modeName + "V"

hcParams = "EXTRA_HC_OPTS=\""+join(settings)+"\""

noftop = "/5playpen/t-davain/shadows/from-horse-ghc/nofib/"

targetDir = logsLocation + name + "/"

os.chdir(noftop+under+"/"+name)

sp.call("make clean > /dev/null", shell = True)

try:
    os.makedirs(targetDir)
except:
    pass

f = open(targetDir+"log"+modeName,"w")
sp.call("make -k "+hcParams, stdout=f,stderr=f, shell=True)
f.close()

targetExeName = targetDir+name+modeName

sp.call(["cp", name, targetExeName])
stdinName = name+".stdin"
if os.access(stdinName, os.F_OK):
    print "Found " + stdinName + "will try to create ticky."
    tickyName = name + modeName + ".ticky"
    sp.call("cat "+name+".stdin | ./" + name + " +RTS -r" + targetDir+tickyName + " > /dev/null", shell=True)
