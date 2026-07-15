#!/bin/bash

# ulimit -s unlimited

#cfg_dir="benchmark/semanticTests_cfg"
#cfg_dir="benchmark/grey_stack_too_deep_cfg"
cfg_dir="benchmark/1k_most_called_cfg"
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
