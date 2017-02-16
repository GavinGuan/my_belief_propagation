#!/usr/bin/python
#@author: gbtux (gbtju85@gmail.com)
#

import sys
import os

if len(sys.argv)!= 4:
	print "{0} <bp_result_f> <node_index_f> <output_f>".format(sys.argv[0])
	exit()

bp_res_f = sys.argv[1]
node_ind_f = sys.argv[2]
outf = sys.argv[3]

ind_to_label = {}
with open(node_ind_f) as indata:
	for line in indata:
		ind, label = line.strip().split()[:2]
		ind_to_label[ind] = label


fd = open(outf, 'w+')
with open(bp_res_f) as indata:
	for line in indata:
		ind, score = line.strip().split(":")[0:2]
		fd.write("{0}:{1}\n".format(ind_to_label[ind], score))
fd.close()
