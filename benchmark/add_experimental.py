"""
Reads a standard-input.json file, adds or removes `settings.experimental`
(required by solc >= 0.8.35 to emit yulCFGJson; rejected outright as an
unknown key by earlier versions), then writes the result to a separate
output path, leaving the input (including its outputSelection) untouched.

Usage: add_experimental.py <input> <output> <true|false>
"""

import json
import sys

with open(sys.argv[1], "r", encoding="utf8") as f:
	d = json.load(f)

d['settings'].pop('experimental', None)
if sys.argv[3] == 'true':
	d['settings']['experimental'] = True

with open(sys.argv[2], "w", encoding="utf8") as fout:
	json.dump(d, fout)
