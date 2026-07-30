#!/bin/bash

# Runs the liveness+constancy checker over every *.json file in a cfg
# folder and prints one CSV line per file (header first).
#
# Usage (run from the repo root):
#   ./run_experiments.sh benchmark/semanticTests_cfg_0_8_34 > semanticTests_0_8_34.csv

# ulimit -s unlimited

cfg_dir="${1:?Usage: $0 <cfg_dir>}"
foryu="bin/static_foryu"

# --csv already reports json-processing status, size, and per-analysis timings
# and verdicts in one line -- column order matches the --liveness/--constancy
# order below (liveness first, then constancy).
echo "filename,json_processing,nblocks,ninstrs,preprocess_time(ns),liveness_extract_time(ns),liveness_check_time(ns),liveness_verdict,constancy_extract_time(ns),constancy_check_time(ns),constancy_verdict"

find ${cfg_dir} -type f -name "*.json" -print0 | while IFS= read -r -d '' f; do
	line=$("${foryu}" --liveness subset --constancy --csv -i "${f}")
	if [ -z "${line}" ]; then
		echo "${f},CRASH"
	else
		echo "${line}"
	fi
done
