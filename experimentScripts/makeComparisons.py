#!/usr/bin/env python
import subprocess as sp
import os 
from sys import argv
from string import join, split,strip

expDirName = "19thOvernight"
home = "/home/t-davain/"
noftop = "/5playpen/t-davain/shadows/from-horse-ghc/nofib/"
analyzerLocation = noftop + "nofib-analyse/nofib-analyse"
logLocation = "/5playpen/t-davain/experimental/raw/" + expDirName + "/"

targetRoot = logLocation

modes = ["plain", "10", "100", "300", "900"] #, "2700"]

def modeName(mode):
    if mode == "plain":
        return "Plain"
    else:
        return "B%04d" % float(mode)


for mode in modes:
    logFileName = "log"+modeName(mode)
    catCommand = "cat "+ logFileName + " >> ../" + logFileName
    for line in open(home+"experimental/code/toRun"):
        print "Going to process" + mode + line
        parts = split(strip(line),'/')
        name = parts.pop()
        targetDir = targetRoot + name + "/"
        under = join(parts,'/')
        if os.access(targetDir,os.F_OK):
            os.chdir(targetDir)
            sp.call(catCommand, shell=True)


print "Starting to analyze"
analyzeName = noftop + "nofib-analyse/nofib-analyse"
os.chdir(targetRoot)
f = open(targetRoot+"compareAll.txt","w")
sp.call([analyzeName] + ["log"+modeName(mode) for mode in modes], stdout=f)
f.close()


