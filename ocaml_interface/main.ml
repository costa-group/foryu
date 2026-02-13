(*
let main () =
  let res = Checker.TestTranslation.check in
    Printf.fprintf stdout "%B\n%!" res;;


let _ = main ();;
*)

open Yojson.Basic.Util
open Yojson.Safe
open Yojson.Safe.Util


type assoc_t = (string * Yojson.Safe.t) list


let gen_name prefix fname_opt =
  let parts = match fname_opt with
    | Some f -> prefix @ [f]
    | None -> prefix
  in
  String.concat "__" parts
  |> String.map (fun c -> if c = '.' then '_' else c)


let process_blocks (blocks: Yojson.Safe.t) (prefix: string list): Yojson.Safe.t =
  `Assoc []  

let process_functions (funs: Yojson.Safe.t) (prefix: string list): assoc_t =
  []

let rec read_object (obj_json: Yojson.Safe.t) (prefix: string list) : Yojson.Safe.t =
  let subobjs = match obj_json |> member "subObjects" with
    | `Null -> []
    | subs -> read_objects' (to_assoc subs) prefix
  in let blocks = match obj_json |> member "blocks" with
    | `Null -> `Assoc []
    | bs -> process_blocks bs prefix
  in let funcs = match obj_json |> member "functions" with
    | `Null -> []
    | fs -> process_functions fs prefix
  in `Assoc []
  
and
read_objects' (objects: assoc_t) (prefix: string list) : assoc_t =
  match objects with
  | [] -> []
  | (obj_name, obj_json)::rest -> 
      let rest' = read_objects' rest prefix in
      if obj_name = "type" then 
        rest' 
      else
        let obj' = read_object obj_json (prefix @ [obj_name]) in
        (obj_name, obj')::rest'

let read_objects (json: Yojson.Safe.t) (prefix: string list) : Yojson.Safe.t =
  `Assoc (read_objects' (to_assoc json) prefix)


let read_comp (comp: Yojson.Safe.t) (prefix: string list) : Yojson.Safe.t = 
  match comp |> member "yulCFGJson" with
  | `Null -> `Assoc []
  | cfg -> read_objects cfg prefix
  

let rec read_contract' (l: assoc_t) (filename: string) : assoc_t =
  match l with
  | [] -> []
  | (comp_name, comp)::r -> let comp' = read_comp comp [filename; comp_name] in
                            let r' = read_contract' r filename in
                            (comp_name, comp') :: r'

let rec read_contract (json: Yojson.Safe.t) (filename: string) : Yojson.Safe.t =
  `Assoc (read_contract' (to_assoc json) filename)


let rec read_contracts' (l: assoc_t) : string * assoc_t =
  match l with
  | [] -> ("", [])
  | (k,v)::r -> let _, r' = read_contracts' r in
                let sc = read_contract v k in
                (k, (k,sc)::r')

let rec read_contracts (json: Yojson.Safe.t) : string * Yojson.Safe.t = 
  let main_contract, contracts_l = read_contracts' (to_assoc json) in
  (main_contract, `Assoc contracts_l)

let read_json path : (string * Yojson.Safe.t) =
  let data = from_file path in
  match data |> member "contracts" with
  | `Null -> ("", `Assoc [])
  | scs   -> read_contracts scs













(* process_json : string -> (string option * (string * Yojson.Safe.t) list)
   Returns: (sc_main_filename_opt, flat_d) where flat_d is an assoc list
   mapping generated function-names to their JSON definitions (Yojson.t).
*)
let process_json path : (string option * (string * Yojson.Safe.t) list) =
  let data = from_file path in
  let scs = data |> member "contracts" |> to_assoc in
  let flat = ref [] in
  let sc_main = ref None in

  List.iter (fun (sc_filename, sc_json) ->
    if !sc_main = None then sc_main := Some sc_filename;
    let comps = sc_json |> to_assoc in
    List.iter (fun (comp, comp_json) ->
      let yul = comp_json |> member "yulCFGJson" in
      match yul with
      | `Null -> ()
      | _ ->
        (match yul |> member "type" with
         | `String "Object" ->
           let rec process_object d prefix =
             let pairs = d |> to_assoc in
             List.fold_left (fun acc (object_name, obj_json) ->
               if object_name = "type" then acc else

               (* recurse into subObjects if present *)
               let acc =
                 match obj_json |> member "subObjects" with
                 | `Null -> acc
                 | sub -> process_object sub (prefix @ [object_name]) @ acc
               in

               (* handle functions: rename keys with prefix *)
               let acc =
                 match obj_json |> member "functions" with
                 | `Null -> acc
                 | funcs ->
                   let funcs_list = funcs |> to_assoc in
                   let renamed = List.map (fun (fname, fjson) ->
                     let newname = gen_name (prefix @ [object_name]) (Some fname) in
                     (newname, fjson)
                   ) funcs_list in
                   renamed @ acc
               in

               (* if blocks present, build an 'entry' synthetic function similar to Python version *)
               match obj_json |> member "blocks" with
               | `Null -> acc
               | blocks ->
                 let blocks_list = blocks |> to_list in
                 if blocks_list = [] then acc
                 else
                   let entry_name = gen_name (prefix @ [object_name]) (Some "entry") in
                   let entry_block_id = (List.hd blocks_list) |> member "id" in
                   let func_obj =
                     `Assoc [
                       ("arguments", `List []);
                       ("blocks", blocks);
                       ("entry", entry_block_id);
                       ("numReturns", `Int 0)
                     ]
                   in
                   (entry_name, func_obj) :: acc
             ) [] pairs
           in
           let processed = process_object yul [sc_filename; comp] in
           flat := processed @ !flat
         | _ -> ())
    ) comps
  ) scs;

  (!sc_main, !flat)

(*
let () =
  (* 1. Parse the raw string into a Yojson structure *)
  let json = Yojson.Basic.from_string json_content in

  (* 2. Access top-level fields *)
  let dialect = json |> member "dialect" |> to_string in
  let version = json |> member "version" |> to_int in

  (* 3. Access a subdocument (nested object) *)
  let settings = json |> member "settings" in
  let is_optimized = settings |> member "optimize" |> to_bool in

  (* 4. Access a sub-list *)
  let passes = settings |> member "passes" |> to_list |> filter_string in

  (* Print results *)
  Printf.printf "Dialect: %s (v%d)\n" dialect version;
  Printf.printf "Optimization enabled: %b\n" is_optimized;
  Printf.printf "Active passes: %s\n" (String.concat ", " passes)
*)

(*
let () =
  let sc_main_opt, flat_d = process_json "/home/kike/Personal/svn/foryu/benchmark/fm26/constructor_payable_constructor__payable_constructor_standard_input_cfg.json" in
  match sc_main_opt with
  | Some sc_main -> let _ = Printf.printf "Main contract: %s\n" sc_main in
                    List.iter (fun (fname, fjson) ->
                      Printf.printf "Function: %s\nDefinition: %s\n\n" fname 
                        (Yojson.Safe.pretty_to_string fjson) ) flat_d
  | None -> Printf.printf "No main contract found.\n";
*)  


let input_file = ref ""
(*let verbose = ref false
let optimize_level = ref 0*)

(* 1. Define the specifications for your flags *)
let speclist = [
  (*
  ("-v", Arg.Set verbose, "Enables verbose output");
  ("-opt", Arg.Set_int optimize_level, "Set optimization level (0-3)");
  *)
  ("-i", Arg.Set_string input_file, "Input JSON file");

]

(* 2. Define what to do with "anonymous" arguments (filenames) *)
let anon_fun arg =
  raise (Arg.Bad ("Unexpected argument: " ^ arg))

let usage_msg = "Usage: ./checker -i filename.json"

let () =
  (* 3. Parse the arguments *)
  Arg.parse speclist anon_fun usage_msg;

  (* 4. Use the parsed values *)
  if !input_file = "" then (
    prerr_endline "Error: No input file provided.";
    Arg.usage speclist usage_msg;
    exit 1
  );

  let sc_main_opt, flat_d = process_json !input_file in
  match sc_main_opt with
  | Some sc_main -> let json_object = `Assoc flat_d in
                    let json_string = Yojson.Safe.pretty_to_string json_object in
                    print_endline json_string

                    (*List.iter (fun (fname, fjson) ->
                      Printf.printf "Function: %s\nDefinition: %s\n\n" fname 
                        (Yojson.Safe.pretty_to_string fjson) ) flat_d *)

  | None -> Printf.printf "No main contract found.\n";
