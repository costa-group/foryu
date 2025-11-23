#!/bin/bash

start_dir="$(pwd)"
cfg_dir="python/semanticTests_cfg"
translated_file="test_translation.v"
output_file="output.txt"
counter=0

find ${cfg_dir} -type f -name "*.json" -print0 | while IFS= read -r -d '' f; do
    counter=$((counter + 1))
    dir="$(dirname "$f")"
    file="$(basename "$f")"

    cd "$dir" || continue

    echo "$counter) $f"
    rm -f "${start_dir}/${translated_file}"
    inicio=$(date +%s%N)
    python3 "${start_dir}/python/json2coq.py" "${file}" "${start_dir}/${translated_file}"
    fin=$(date +%s%N)
    duracion_tr_ns=$((fin - inicio))
    duracion_tr_ms=$((duracion_tr_ns / 1000000))

    cd "$start_dir"
    md5sum "${start_dir}/${translated_file}"
    inicio=$(date +%s%N)
    rm -f "${output_file}"
    coqc -R . FORYU "${translated_file}" > "${output_file}"
    fin=$(date +%s%N)
    duracion_chk_ns=$((fin - inicio))
    duracion_chk_ms=$((duracion_chk_ns / 1000000))

    checker=$(cat "$output_file" | grep '=' | awk '{print $2}')

    echo "${duracion_tr_ms} ${duracion_chk_ms} ${checker}"


	  # inicio=$(date +%s%N)
    # solc $file --standard-json --pretty-json > "${start_dir}/${exit_dir}/${file}_cfg.json"
    # fin=$(date +%s%N)
    # duracion_ns=$((fin - inicio))
    # duracion_ms=$((duracion_ns / 1000000))
    # echo "${counter}) ${duracion_ms} ms"
    # echo "$f"
    # echo 

    # timeout 5s "${start_dir}/solc-static-linux" $file --standard-json --pretty-json > "${start_dir}/${exit_dir}/${file}_cfg.json"
    # if [ $? -eq 0 ]; then
    #     echo "${counter}) Exito: $f"
    # else
    #     echo "${counter}) Timeout $f"
	  # fi

    echo
    cd "$start_dir"
done
