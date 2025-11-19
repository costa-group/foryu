"""
Translates a JSON file containing the CFG of a smart contract to the Coq representation of the FORYU project
(https://github.com/costa-group/foryu/tree/main)
JSON are obtained using solc:
$ solc file_standard_input.json --standard-json --pretty-json > cfg.json
"""

import json
import pprint
import sys


"""
Layout of the JSON file
{
    'contracts':{
        'name.sol':{
          'entry'
            'yulCFGJson':{
                'entry1':{
                    'blocks': [],
                    'functions': {
                        'f1': ...
                        'f2': ...
                    } 
                },
                
                'entry2':{
                    'blocks': [],
                    'functions': {
                        'f1': ...
                        'f2': ...
                    } 
                } 
            } 
            ...
        }
    }
    
    'errors':...
}
"""

def process_json(path):
    """ Processes a JSON file """
    with open(path, 'r', encoding="utf-8") as f:
        data = json.load(f)

    scs = data['contracts']
    for sc_filename in scs:
        print(sc_filename)
        sc = scs[sc_filename]
        for comp in sc:
            print(comp)
            yulcfg = sc[comp]['yulCFGJson']
            assert yulcfg['type'] == 'Object'
            del yulcfg['type']
            for entryname in yulcfg:
                print(entryname)
                yulblocks = yulcfg[entryname]['blocks']
                yulfunctions = yulcfg[entryname]['functions']
                # yulsubobj = yulcfg[entryname]['subObjects']  # Ignore _deployed subobjects

                # each entry will generate a function 'entryname' with no arguments and no return value
                print(yulblocks)

                # Each YUL function will generate a function
                print(yulfunctions)


if __name__ == '__main__':
    process_json('constant_variables_standard_input.json_cfg.json')
