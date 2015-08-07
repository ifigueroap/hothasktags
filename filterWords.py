#!/usr/bin/python

import argparse
import sys

parser = argparse.ArgumentParser(description="Filter tags file")
parser.add_argument('-f', '--file', help="Hothasktags file")
parser.add_argument('-r', '--filter', help="File with rejected strings, one per line", required=True)

def main():
   args = parser.parse_args()
   tagsFilePath = args.file

   if tagsFilePath == None:
	tagsFile = sys.stdin
   else:
	tagsFile = open(tagsFilePath)

   filterFile = args.filter

   rejectedStrings = []  
   for line in open(filterFile):
       rejectedStrings.append(line.split("\t")[0].strip())

   for line in tagsFile:
       splitString = line.split('\t')
       if not splitString[0] in rejectedStrings:
           sys.stdout.write(line)

   if tagsFile is not sys.stdin:
      tagsFile.close()

if __name__ == "__main__":
    main()
