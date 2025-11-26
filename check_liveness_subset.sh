#!/bin/bash

start_dir="$(pwd)"
cfg_dir="python/semanticTests_cfg"
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
subset_file=$1


if [ $# -eq 0 ]; then
    echo "Usage: $0 <filename>"
    exit 1
fi


find ${cfg_dir} -type f -name "*.json" -print0 | while IFS= read -r -d '' f; do
    counter=$((counter + 1))
    dir="$(dirname "$f")"
    file="$(basename "$f")"

    cd ${start_dir}

    if grep -qx "$f" "$subset_file"; then

      echo "$counter) $f"

      cd ${start_dir}

      # Get size
      output_size=$(python3 python/json2coq.py -c subset --size "-i ${start_dir}/${dir}/${file}" "-o ${start_dir}/${translated_file}")
      read nblocks ninstrs <<< "$output_size"
      # echo "&&&&&&&&&&&&&&&&&&&&& ${nblocks} ${ninstrs}"
      # cat ${output_size_file}
      # echo "&&&&&&&&&&&&&&&&&&&&& ${output_size}"
      # read nblocks ninstrs <<< "$output_size"

      # cd "$dir" || continue
      # Translates with "subset" checker
      rm -f "${start_dir}/${translated_file}"
      inicio=$(date +%s%N)
      python3 "${start_dir}/python/json2coq.py" -c subset  "-i ${start_dir}/${dir}/${file}" "-o ${start_dir}/${translated_file}"
      tr_status=$?
      fin=$(date +%s%N)
      duracion_tr_ns=$((fin - inicio))
      duracion_tr_ms_subset=$((duracion_tr_ns / 1000000))

      # Executes with "subset" checker
      cd "$start_dir"
      inicio=$(date +%s%N)
      make
      cd ocaml_interface
      make
      fin=$(date +%s%N)
      t_ns=$((fin - inicio))
      duracion_comp_ms_subset=$((t_ns / 1000000))
      rm -f "${output_file}"
      inicio=$(date +%s%N)
      ./checker > "${output_file}"
      checker_status=$?
      fin=$(date +%s%N)
      duracion_chk_ns=$((fin - inicio))
      duracion_chk_ms_subset=$((duracion_chk_ns / 1000000))

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
      inicio=$(date +%s%N)
      python3 "${start_dir}/python/json2coq.py" -c optimal  "-i ${start_dir}/${dir}/${file}" "-o ${start_dir}/${translated_file}"
      tr_status=$?
      fin=$(date +%s%N)
      duracion_tr_ns=$((fin - inicio))
      duracion_tr_ms_optimal=$((duracion_tr_ns / 1000000))

      # Executes with "optimal" checker
      cd "$start_dir"
      inicio=$(date +%s%N)
      make
      cd ocaml_interface
      make
      fin=$(date +%s%N)
      t_ns=$((fin - inicio))
      duracion_comp_ms_optimal=$((t_ns / 1000000))
      rm -f "${output_file}"
      inicio=$(date +%s%N)
      ./checker > "${output_file}"
      checker_status=$?
      fin=$(date +%s%N)
      duracion_chk_ns=$((fin - inicio))
      duracion_chk_ms_optimal=$((duracion_chk_ns / 1000000))

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
      echo "@@@,${f},$nblocks,$ninstrs,${duracion_tr_ms_subset},${duracion_comp_ms_subset},${duracion_chk_ms_subset},${msg_subset},${duracion_tr_ms_optimal},${duracion_comp_ms_optimal},${duracion_chk_ms_optimal},${msg_optimal}"

      echo

    fi

done
