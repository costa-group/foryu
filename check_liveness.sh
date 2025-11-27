#!/bin/bash

ulimit -s unlimited

start_dir="$(pwd)"
cfg_dir="python/semanticTests_cfg"
#cfg_dir="python/stack_too_deep_cfg"
translated_file="test_translation.v"
output_file="output.txt"
counter=0
tr_status=0
checker_status=0
msg_subset=""
msg_optimal=""
nblocks=0
ninstrs=0
output_size=""

start_p=$(date +%s%N)
echo start_p

find ${cfg_dir} -type f -name "*.json" -print0 | while IFS= read -r -d '' f; do
    counter=$((counter + 1))
    dir="$(dirname "$f")"
    file="$(basename "$f")"

    echo "$counter) $f"

    cd ${start_dir}

    # Get size
    output_size=$(python3 python/json2coq.py -c subset --size "-i ${start_dir}/${dir}/${file}" "-o ${start_dir}/${translated_file}")
    read nblocks ninstrs <<< "$output_size"

    # cd "$dir" || continue
    # Translates with "subset" checker
    rm -f "${start_dir}/${translated_file}"
    start=$(date +%s%N)
    python3 "${start_dir}/python/json2coq.py" -c subset  "-i ${start_dir}/${dir}/${file}" "-o ${start_dir}/${translated_file}"
    tr_status=$?
    end=$(date +%s%N)
    duration_tr_ns_subset=$((end - start))

    # Executes with "subset" checker
    cd "$start_dir"
    start=$(date +%s%N)
    make
    cd ocaml_interface
    rm -f checker
    make > /dev/null 2>&1
    end=$(date +%s%N)
    duration_comp_ns_subset=$((end - start))
    rm -f "${output_file}"
    start=$(date +%s%N)
    ./checker > "${output_file}"
    checker_status=$?
    end=$(date +%s%N)
    duration_chk_ns_subset=$((end - start))

    # Generates message subset
    # checker=$(cat "$output_file" | grep '=' | awk '{print $2}')
    checker=$(cat "$output_file")
    msg_subset=""
    if [ $tr_status -ne 0 ]; then
      msg_subset="TRANSLATION_RUNTIME_ERROR"
    elif [ $checker_status -ne 0 ]; then
      msg_subset="CHECKER_RUNTIME_ERROR"
    elif [[ "$checker" == "true" ]]; then
      msg_subset="LIVENESS_VALID"
    elif [[ "$checker" == "false" ]]; then
      msg_subset="LIVENESS_INVALID"
    else
      msg_subset="LIVENESS_MSG_UNKNOWN"
    fi


    cd ${start_dir}
    # cd "$dir" || continue
    # Translates with "subset" checker
    rm -f "${start_dir}/${translated_file}"
    start=$(date +%s%N)
    python3 "${start_dir}/python/json2coq.py" -c optimal  "-i ${start_dir}/${dir}/${file}" "-o ${start_dir}/${translated_file}"
    tr_status=$?
    end=$(date +%s%N)
    duration_tr_ns_optimal=$((end - start))

    # Executes with "optimal" checker
    cd "$start_dir"
    start=$(date +%s%N)
    make
    cd ocaml_interface
    rm -f checker
    make > /dev/null 2>&1
    end=$(date +%s%N)
    duration_comp_ns_optimal=$((end - start))
    rm -f "${output_file}"
    start=$(date +%s%N)
    ./checker > "${output_file}"
    checker_status=$?
    end=$(date +%s%N)
    duration_chk_ns_optimal=$((end - start))

    # Generates message optimal
    checker=$(cat "$output_file")
    msg_optimal=""
    if [ $tr_status -ne 0 ]; then
      msg_optimal="TRANSLATION_RUNTIME_ERROR"
    elif [ $checker_status -ne 0 ]; then
      msg_optimal="CHECKER_RUNTIME_ERROR"
    elif [[ "$checker" == "true" ]]; then
      msg_optimal="LIVENESS_VALID"
    elif [[ "$checker" == "false" ]]; then
      msg_optimal="LIVENESS_INVALID"
    else
      msg_optimal="LIVENESS_MSG_UNKNOWN"
    fi

    # @@@,filename,nblocks,ninst,time_tr_subset,time_comp_subset,time_checker_subset,msg_subset,time_tr_optimal,time_comp_optimal,time_checker_optimal,msg_optimal
    echo "@@@,${f},$nblocks,$ninstrs,${duration_tr_ns_subset},${duration_comp_ns_subset},${duration_chk_ns_subset},${msg_subset},${duration_tr_ns_optimal},${duration_comp_ns_optimal},${duration_chk_ns_optimal},${msg_optimal}"

    echo
done

end_p=$(date +%s%N)
echo end_p
time_p=$((end_p - start_p))
echo "Total time ${time_p} ns"