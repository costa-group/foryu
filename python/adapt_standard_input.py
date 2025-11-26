"""
Simplifies a standard-input.json file to produce only the yulCFGJson
when compiling with solc
"""

import json
import sys

with open(sys.argv[1], "r", encoding="utf8") as f:
	d = json.load(f)
	d['settings']['outputSelection']['*'] = {'*':['yulCFGJson']}
	with open(sys.argv[2], "w", encoding="utf8") as fout:
		json.dump(d, fout)


