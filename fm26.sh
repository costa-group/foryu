#!/bin/bash

# ulimit -s unlimited

cfg_dir="benchmark/semanticTests_cfg"
#cfg_dir="benchmark/grey_stack_too_deep_cfg"
nblocks=0
ninstrs=0
output_size=""

echo "filename,nblocks,ninstrs,time(ns),verdict"

find ${cfg_dir} -type f -name "*.json" -print0 | while IFS= read -r -d '' f; do
    output_size=$(./ocaml_interface/checker -i ${f} -size)
	read nblocks ninstrs <<< "$output_size"
	start=$(date +%s%N)
	ret=`./ocaml_interface/checker -i ${f}`

	if [ $? -ne 0 ]; then
		echo "ERROR ${f}"
		exit -1
	fi

	end=$(date +%s%N)
	ts=$((end - start))
		
	echo "${f},$nblocks,$ninstrs,${ts},${ret}"		
done
