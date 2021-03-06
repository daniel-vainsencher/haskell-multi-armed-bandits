#!/usr/bin/env python
import subprocess as sp
import os 
from sys import argv
from string import join, split, strip

home = "/home/t-davain/"
expDirName = argv[1]
noftop = "/5playpen/t-davain/shadows/from-horse-ghc/nofib/"
analyzerLocation = noftop + "nofib-analyse/nofib-analyse"
logLocation = "/5playpen/t-davain/experimental/raw/" + expDirName + "/"

modes = ["plain", "10"] #, "100", "300"] #, "900"]


verbosity = "regular"
for line in open("./toRun"):
    parts = split(strip(line),'/')
    name = parts.pop()
    under = join(parts,'/')
    runCommands = [join(["./runSingleBenchmark.py", under, name, mode, logLocation, verbosity]) for mode in modes]
    targetDir =  logLocation + name + "/"
    cdCommand = "cd " + targetDir
    logCommand = analyzerLocation + " logPlain logB* > comparison"
    total = join(runCommands+[cdCommand, logCommand],' && ')
    sp.call(total+' &', shell=True)
