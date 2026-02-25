open Yojson.Safe
open Yojson.Safe.Util
module StringSet = Set.Make(String)

(* Yojson as a list of pairs (key, value) *)
type assoc_t = (string * Yojson.Safe.t) list


(* Inserts/Replaces the value associated to 'key' in the JSON j *)
let upsert_yojson (key:string) (v:Yojson.Safe.t) (j:Yojson.Safe.t) : Yojson.Safe.t =
  match j with
  | `Assoc al ->
      let al' = (key, v) :: List.filter (fun (k,_) -> k <> key) al in
      `Assoc al'
  | _ -> j


(********** Auxiliary functions and datastructures for processing JSON solc files **********)

let fun_names : StringSet.t ref = ref StringSet.empty

let evm_opcode_list : (string * Checker.EVM_opcode.t) list = [
  ("stop", Checker.EVM_opcode.STOP);
  ("add", Checker.EVM_opcode.ADD);
  ("sub", Checker.EVM_opcode.SUB);
  ("mul", Checker.EVM_opcode.MUL);
  ("div", Checker.EVM_opcode.DIV);
  ("sdiv", Checker.EVM_opcode.SDIV);
  ("mod", Checker.EVM_opcode.MOD);
  ("smod", Checker.EVM_opcode.SMOD);
  ("exp", Checker.EVM_opcode.EXP);
  ("not", Checker.EVM_opcode.NOT);
  ("lt", Checker.EVM_opcode.LT);
  ("gt", Checker.EVM_opcode.GT);
  ("slt", Checker.EVM_opcode.SLT);
  ("sgt", Checker.EVM_opcode.SGT);
  ("eq", Checker.EVM_opcode.EQ);
  ("iszero", Checker.EVM_opcode.ISZERO);
  ("and", Checker.EVM_opcode.AND);
  ("or", Checker.EVM_opcode.OR);
  ("xor", Checker.EVM_opcode.XOR);
  ("byte", Checker.EVM_opcode.BYTE);
  ("shl", Checker.EVM_opcode.SHL);
  ("shr", Checker.EVM_opcode.SHR);
  ("sar", Checker.EVM_opcode.SAR);
  ("addmod", Checker.EVM_opcode.ADDMOD);
  ("mulmod", Checker.EVM_opcode.MULMOD);
  ("signextend", Checker.EVM_opcode.SIGNEXTEND);
  ("keccak256", Checker.EVM_opcode.KECCAK256);
  ("pop", Checker.EVM_opcode.POP);
  ("mload", Checker.EVM_opcode.MLOAD);
  ("mstore", Checker.EVM_opcode.MSTORE);
  ("mstore8", Checker.EVM_opcode.MSTORE8);
  ("sload", Checker.EVM_opcode.SLOAD);
  ("sstore", Checker.EVM_opcode.SSTORE);
  ("tload", Checker.EVM_opcode.TLOAD);
  ("tstore", Checker.EVM_opcode.TSTORE);
  ("msize", Checker.EVM_opcode.MSIZE);
  ("gas", Checker.EVM_opcode.GAS);
  ("address", Checker.EVM_opcode.ADDRESS);
  ("balance", Checker.EVM_opcode.BALANCE);
  ("selfbalance", Checker.EVM_opcode.SELFBALANCE);
  ("caller", Checker.EVM_opcode.CALLER);
  ("callvalue", Checker.EVM_opcode.CALLVALUE);
  ("calldataload", Checker.EVM_opcode.CALLDATALOAD);
  ("calldatasize", Checker.EVM_opcode.CALLDATASIZE);
  ("calldatacopy", Checker.EVM_opcode.CALLDATACOPY);
  ("codesize", Checker.EVM_opcode.CODESIZE);
  ("codecopy", Checker.EVM_opcode.CODECOPY);
  ("extcodesize", Checker.EVM_opcode.EXTCODESIZE);
  ("extcodecopy", Checker.EVM_opcode.EXTCODECOPY);
  ("returndatasize", Checker.EVM_opcode.RETURNDATASIZE);
  ("returndatacopy", Checker.EVM_opcode.RETURNDATACOPY);
  ("mcopy", Checker.EVM_opcode.MCOPY);
  ("extcodehash", Checker.EVM_opcode.EXTCODEHASH);
  ("create", Checker.EVM_opcode.CREATE);
  ("create2", Checker.EVM_opcode.CREATE2);
  ("call", Checker.EVM_opcode.CALL);
  ("callcode", Checker.EVM_opcode.CALLCODE);
  ("delegatecall", Checker.EVM_opcode.DELEGATECALL);
  ("staticcall", Checker.EVM_opcode.STATICCALL);
  ("return", Checker.EVM_opcode.RETURN);
  ("revert", Checker.EVM_opcode.REVERT);
  ("selfdestruct", Checker.EVM_opcode.SELFDESTRUCT);
  ("invalid", Checker.EVM_opcode.INVALID);
  ("log0", Checker.EVM_opcode.LOG0);
  ("log1", Checker.EVM_opcode.LOG1);
  ("log2", Checker.EVM_opcode.LOG2);
  ("log3", Checker.EVM_opcode.LOG3);
  ("log4", Checker.EVM_opcode.LOG4);
  ("chainid", Checker.EVM_opcode.CHAINID);
  ("basefee", Checker.EVM_opcode.BASEFEE);
  ("blobbasefee", Checker.EVM_opcode.BLOBBASEFEE);
  ("origin", Checker.EVM_opcode.ORIGIN);
  ("gasprice", Checker.EVM_opcode.GASPRICE);
  ("blockhash", Checker.EVM_opcode.BLOCKHASH);
  ("blobhash", Checker.EVM_opcode.BLOBHASH);
  ("coinbase", Checker.EVM_opcode.COINBASE);
  ("timestamp", Checker.EVM_opcode.TIMESTAMP);
  ("number", Checker.EVM_opcode.NUMBER);
  ("difficulty", Checker.EVM_opcode.DIFFICULTY);
  ("prevrandao", Checker.EVM_opcode.PREVRANDAO);
  ("gaslimit", Checker.EVM_opcode.GASLIMIT);
  ("memoryguard", Checker.EVM_opcode.MEMORYGUARD);
  ("datasize", Checker.EVM_opcode.DATASIZE);
  ("dataoffset", Checker.EVM_opcode.DATAOFFSET);
  ("datacopy", Checker.EVM_opcode.DATACOPY);
  (*("LiteralAssignment", EVMInstr.ASSIGN);*) (* Special case *)
  ("linkersymbol", Checker.EVM_opcode.LINKERSYMBOL);
  ("setimmutable",  Checker.EVM_opcode.SETIMMUTABLE);
  ("loadimmutable",  Checker.EVM_opcode.LOADIMMUTABLE);
]


let evm_opcode_tbl : (string, Checker.EVM_opcode.t) Hashtbl.t =
  let tbl = Hashtbl.create (List.length evm_opcode_list) in
  List.iter (fun (k,v) -> Hashtbl.add tbl k v) evm_opcode_list;
  tbl


let evm_opcode_get (k:string) : Checker.EVM_opcode.t option =
  (* requires OCaml with Hashtbl.find_opt, otherwise use try/with Not_found *)
  Hashtbl.find_opt evm_opcode_tbl k


(* Generates a string representing a prefix of the object path:
  ['source_import_subdir_sol', 'C', 'C_3'] => 'source_import_subdir_sol__C__C_3' *)
let gen_name (prefix: string list) (fname: string) : string =
  String.concat "__" (prefix @ [fname])
  |> String.map (fun c -> if c = '.' then '_' else c)


(* Convert between OCaml `string` and `char list` (extracted `FuncName.t`) *)
let string_to_char_list (s : string) : char list =
  let rec aux i acc =
    if i < 0 then acc else aux (i - 1) (s.[i] :: acc)
  in aux (String.length s - 1) []


let char_list_to_string (cl : char list) : string =
  let buf = Buffer.create (List.length cl) in
  List.iter (Buffer.add_char buf) cl;
  Buffer.contents buf


  
(******* Functions for flatenning a JSON solc file *******)



(* Extracts the PhiFunctions from the "instructions" entry and creates a different "__phi" entry for them 
   in each block *)
let split_phi_instr_block (block: Yojson.Safe.t): Yojson.Safe.t =
  let instructions = block |> member "instructions" |> to_list in
  let (phi_instrs, other_instrs) = List.partition (fun instr -> match instr |> member "op" with
                                                              | `String "PhiFunction" -> true
                                                              | _ -> false) instructions in
  let block' = upsert_yojson "instructions" (`List other_instrs) block in
  upsert_yojson "__phi" (`List phi_instrs) block'


let split_phi_instr_blocks (blocks: Yojson.Safe.t): Yojson.Safe.t =
  `List (List.map split_phi_instr_block (to_list blocks))



(* Receives a list of blocks of an entry function and generates the function definition *)
let process_blocks_entry (blocks: Yojson.Safe.t) (prefix: string list): assoc_t =
  let fname = gen_name prefix "entry" in
  let fcontents = `Assoc [("arguments", `List []); 
                          ("blocks", split_phi_instr_blocks blocks); (* We do not rename function calls yet *)
                          ("entry", List.hd (to_list blocks) |> member "id");
                          ("numReturns", `Int 0);
                          ("__prefix", `List (List.map (fun s -> `String s) prefix))] in
  [(fname, fcontents)]
  

let process_function (f: string * Yojson.Safe.t) (prefix: string list): string * Yojson.Safe.t =
  let (fname, fjson) = f in
  let newname = gen_name prefix fname in
  match StringSet.mem newname !fun_names with
  | true -> failwith ("Duplicate function name: " ^ newname)
  | false ->  fun_names := StringSet.add newname !fun_names;
              let blocks = match fjson |> member "blocks" with
                | `Null -> `List []
                | bs -> split_phi_instr_blocks bs in
              let fjson' = upsert_yojson "blocks" blocks fjson in
              let fjson'' = upsert_yojson "__prefix" (`List (List.map (fun s -> `String s) prefix)) fjson' in
              (*let fbody = to_assoc fjson'in
              let fbody' = fbody @ [("__prefix", `List (List.map (fun s -> `String s) prefix))] in*)
              (newname, fjson'')


let process_functions (funs: Yojson.Safe.t) (prefix: string list): assoc_t =
  List.map (fun f -> process_function f prefix) (to_assoc funs) 


let rec read_object (obj_json: Yojson.Safe.t) (prefix: string list) : Yojson.Safe.t =
  let subobjs = match obj_json |> member "subObjects" with
    | `Null -> []
    | subs -> read_objects' (to_assoc subs) prefix
  in let blocks = match obj_json |> member "blocks" with
    | `Null -> []
    | bs -> process_blocks_entry bs prefix
  in let funcs = match obj_json |> member "functions" with
    | `Null -> []
    | fs -> process_functions fs prefix
  in `Assoc (blocks @ funcs @ subobjs)
  
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
        (obj' |> to_assoc) @ rest'


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
                            (comp' |> to_assoc) @ r'


let rec read_contract (json: Yojson.Safe.t) (filename: string) : Yojson.Safe.t =
  `Assoc (read_contract' (to_assoc json) filename)


let rec read_contracts' (l: assoc_t) : string * assoc_t =
  match l with
  | [] -> ("", [])
  | (k,v)::r -> let _, r' = read_contracts' r in
                let sc = read_contract v k in
                (k, (sc |> to_assoc) @ r')


let rec read_contracts (json: Yojson.Safe.t) : string * Yojson.Safe.t = 
  let main_contract, contracts_l = read_contracts' (to_assoc json) in
  (main_contract, `Assoc contracts_l)


(* Return a flat version of the solc JSON, with functions and entries in the same level. 
   1) Function names have been expanded with their prefix
   2) Every function contains an entry __prefix with its prefix as a list 
   3) PhiFunctions have been removed from "instructions" and appear in an entry __phi in every block *)
let read_json_to_flat path : (string * Yojson.Safe.t) =
  let data = from_file path in
  match data |> member "contracts" with
  | `Null -> ("", `Assoc [])
  | scs   -> read_contracts scs



(******* Functions for renaming function calls in a flat JSON solc file *******)



let rename_function_calls_instruction (instr: Yojson.Safe.t) (prefix: string list): Yojson.Safe.t =
  let op = instr |> member "op" |> to_string in
  let op' = match evm_opcode_get op with
  | Some _ -> op
  | None -> if op = "LiteralAssignment" then op
            else 
            let newname = gen_name prefix op in 
            match StringSet.mem newname !fun_names with
            | false -> Printf.printf "[%s]\n" (String.concat "; " (StringSet.elements !fun_names));
                       let instr_str = Yojson.Safe.pretty_to_string instr in 
                       (*Printf.printf "Call to function defined outside the object. Op='%s'\n" op;
                       Printf.printf "Prefix: %s\n" (prefix |> String.concat "__");*)
                       failwith ("Call to function defined outside the object. \n Instr=" ^ instr_str ^ " Op='" ^ op  ^ "' with prefix " ^ (prefix |> String.concat "__"))
                       (*op*)
            | true -> newname in
  upsert_yojson "op" (`String op') instr


let rename_function_calls_instructions (instructions: Yojson.Safe.t list) (prefix: string list): Yojson.Safe.t list =
  List.map (fun instr -> rename_function_calls_instruction instr prefix) instructions


let rename_function_calls_block (block: Yojson.Safe.t) (prefix: string list): Yojson.Safe.t =
  let instructions = block |> member "instructions" |> to_list in
  let instructions' = rename_function_calls_instructions instructions prefix in 
  upsert_yojson "instructions" (`List instructions') block


let rename_function_calls_blocks (blocks: Yojson.Safe.t) (prefix: string list): Yojson.Safe.t =
  `List (List.map (fun b -> rename_function_calls_block b prefix) (to_list blocks))


let rename_fun_call (fname: string) (fbody: Yojson.Safe.t): string * Yojson.Safe.t =
  let blocks = match fbody |> member "blocks" with
    | `Null -> `List []
    | bs -> rename_function_calls_blocks bs (to_list (member "__prefix" fbody) |> List.map to_string) in
  let fbody' = upsert_yojson "blocks" blocks fbody in
  (fname, fbody')


(* Rename and check function calls in a flat JSON *)
let rename_fun_calls (flatjson: Yojson.Safe.t): Yojson.Safe.t =
  let funs' = List.map (fun (fname, fbody) -> (rename_fun_call fname fbody)) (to_assoc flatjson) in
  `Assoc funs'



(******* Takes a flat JSON and returns a program and liveness information *******) 

module IntSet = Set.Make(Z)
(* Detect duplicates in list of variables *)
let dup_vars (vars: Checker.VarID.t list) : bool =
  let rec loop seen = function
    | [] -> false
    | hd :: tl ->
        if IntSet.mem hd seen then true
        else loop (IntSet.add hd seen) tl
  in
  loop IntSet.empty vars


let extract_integer_str (s: string) (prefix: string): string =
  let prefix_len = String.length prefix in
  if not (String.starts_with ~prefix s) then
    failwith ("Invalid prefix: " ^ s ^ " does not start with " ^ prefix);
  let number_str = String.sub s prefix_len (String.length s - prefix_len) in
  number_str


(* Extract the number "X" in "BlockX" as a BlockID.t *)
let extract_bid (s: string) : Checker.BlockID.t =
  let str_num = extract_integer_str s "Block" in
  Z.of_string str_num
  

let base_phivar_number : Z.t = Z.of_string "1000000000000000000" (* 10^18, to avoid conflicts with normal variables *)
(* For compiled YulCFG with solc Version: 0.8.33+commit.64118f21.Linux.g++, variables are strings:
   - v0, v1, v23... 
   - phi0, phi1, phi36...
*)

(* Extracts the variable number "X" in "vX" or "phiX" as a VarID.t.
   phiX generates the VarID base_phivar_number + X *)
let extract_var (s: string) : Checker.VarID.t =
  if String.starts_with ~prefix:"phi" s then
    let str_num = extract_integer_str s "phi" in
    Z.add base_phivar_number (Z.of_string str_num)
  else
    let str_num = extract_integer_str s "v" in
    let varnum = Z.of_string str_num in
    if varnum >= base_phivar_number then
      failwith ("Variable number too large: " ^ s ^ " generates VarID " ^ (Z.to_string varnum) ^ " which is reserved for phi variables")
    else 
      varnum


(* Extracts an hexadecimal value like "0xFF" as a Z.t value *)
let extract_val (s: string) : Z.t =
  try
    let z = Z.of_string s in
    z
  with 
  | Invalid_argument _ -> 
      failwith (Printf.sprintf "Error: '%s' no es un formato numérico válido" s)


(* Extracts a SimpleExpr from a string *)
let extract_sexpr (s: string) : Checker.Checker.ExitInfo.SimpleExprD.t =
  if (String.starts_with ~prefix:"v" s) || (String.starts_with ~prefix:"phi" s) then
    Inl (extract_var s)
  else
    if String.starts_with ~prefix:"0x" s then
      Inr (extract_val s)
    else
      failwith ("Invalid simple expression string: " ^ s)


let extract_sexprs (sexprs_json: Yojson.Safe.t) : Checker.Checker.ExitInfo.SimpleExprD.t list =
  List.map (fun s -> match s with
                      | `String s' -> extract_sexpr s'
                      | _ -> failwith "Invalid simple expression")
           (to_list sexprs_json)


let rec extract_phi_instrs (phi_instrs_json: Yojson.Safe.t list) : 
    (Checker.Checker.ExitInfo.SimpleExprD.t list) list * Checker.VarID.t list = 
  match phi_instrs_json with
  | [] -> ([], [])
  | instr :: r -> let sexprs, vars = extract_phi_instrs r in
                  let v = match instr |> member "out" with
                          | `List [s] -> extract_var (to_string s)
                          | `List _ -> failwith "Invalid out var list in phi instruction (zero or 2+ vars)"
                          | _ -> failwith "Invalid out var in phi instruction (not list)" in
                  let s = extract_sexprs (member "in" instr)
                  in (s :: sexprs, v :: vars)


let pair_vars_with_columns
    (rows: Checker.Checker.ExitInfo.SimpleExprD.t list list)
    (vars: Checker.VarID.t list)
  : (Checker.VarID.t list * Checker.Checker.ExitInfo.SimpleExprD.t list) list =
  let row_count = List.length rows in
  if row_count <> List.length vars then
    failwith "pair_vars_with_columns: vars length must match number of rows";
  let rec transpose acc rows =
    match rows with
    | [] -> List.rev acc
    | _ ->
        if List.exists (fun r -> r = []) rows then
          if List.for_all (fun r -> r = []) rows then List.rev acc
          else failwith "pair_vars_with_columns: rows have different lengths"
        else
          let heads = List.map List.hd rows in
          let tails = List.map List.tl rows in
          transpose (heads :: acc) tails
  in
  let cols = transpose [] rows in
  List.map (fun col -> (vars, col)) cols       

(*
(* Debugging code *)
let print_pair_vars_with_columns (pvwc: (Checker.VarID.t list * Checker.Checker.ExitInfo.SimpleExprD.t list) list) : unit =
  List.iter (fun (vars, sexprs) ->
    let vars_str = String.concat ", " (List.map n_to_string vars) in
    let sexprs_str = String.concat ", " (List.map simple_expr_to_string sexprs) in
    Printf.printf "Vars: [%s] | SimpleExprs: [%s]\n" vars_str sexprs_str
  ) pvwc


let () =
  let l = pair_vars_with_columns 
    [[Inl (int_to_n 1); Inl (int_to_n 2); Inr (Checker.Zpos (int_to_pos 55))]; 
    [Inr (Checker.Zpos (int_to_pos 3)); Inr (Checker.Zpos (int_to_pos 4)); Inl (int_to_n 88)]]
    [int_to_n 42; int_to_n 0] in
  print_pair_vars_with_columns l;;
(*******************)
*)


let rec gen_phi_function (lp: (Checker.VarID.t list * Checker.Checker.ExitInfo.SimpleExprD.t list) list) 
                     (bids: Checker.BlockID.t list) : Checker.Checker.EVMPhiInfo.t =
  match (lp, bids) with
  | ([], []) -> fun _ -> Checker.Checker.EVMPhiInfo.Coq_in_phi_info ([], [])
  | ((vars, sexprs) :: lp_rest, bid :: bids_rest) ->
      let rest_phi = gen_phi_function lp_rest bids_rest in
      fun b -> if b = bid then Checker.Checker.EVMPhiInfo.Coq_in_phi_info (vars, sexprs)
               else rest_phi b
  | _ -> failwith "gen_phi_function: lp and bids must have the same length"               


let extract_phi_info (phi_instrs : Yojson.Safe.t list) (entries : Yojson.Safe.t list) = 
  (* TODO: checkd NoDup in phi_instr[out]
     TODO: check len(entries) = len(instr[in]) *)
  let bids = List.map (fun entry -> match entry with
                                | `String s -> extract_bid s
                                | _ -> failwith "Invalid entry in block") entries in
  let exprs, vars = extract_phi_instrs phi_instrs in
  if dup_vars vars then failwith "Duplicate variables in phi instructions";
  let lp = pair_vars_with_columns exprs vars in
  gen_phi_function lp bids


let extract_exit_info (exit_info: Yojson.Safe.t) : Checker.Checker.ExitInfo.t =
  match to_string (member "type" exit_info) with
  | "Terminated" -> Checker.Checker.ExitInfo.Terminate
  | "MainExit" -> Checker.Checker.ExitInfo.Terminate
  | "ConditionalJump" -> 
      let cond = extract_var (to_string (member "cond" exit_info)) in
      let btrue, bfalse = match to_list (member "targets" exit_info) with
        | [`String btrue; `String bfalse] -> (extract_bid btrue, extract_bid bfalse)
        | _ -> failwith "Invalid targets in ConditionalJump exit info (must be list of 2 strings)" in
      Checker.Checker.ExitInfo.ConditionalJump (cond, btrue, bfalse)
  | "Jump" -> let target = match to_list (member "targets" exit_info) with
                | [`String s] -> extract_bid s
                | _ -> failwith "Invalid target in Jump exit info (must be one string)" in
              Checker.Checker.ExitInfo.Jump target
  | "FunctionReturn" -> let lvars : Checker.Checker.ExitInfo.SimpleExprD.t list = 
      List.map (fun e -> extract_sexpr (to_string e))  (to_list (member "returnValues" exit_info)) in
      Checker.Checker.ExitInfo.ReturnBlock lvars
  | s -> failwith ("Unsupported exit type in block: " ^ s)


(* OCaml extraction does not generate the ASSIGN constructor, it uses the __ value *)
let __ = let rec f _ = Obj.repr f in Obj.repr f 


let extract_instruction (instr: Yojson.Safe.t) : Checker.Checker.EVMInstr.t =  
    let inp = match member "in" instr with
      | `List in_l -> List.map (fun e -> extract_sexpr (to_string e)) in_l
      | _ -> failwith "Invalid 'in' field in instruction (must be list)" in
    let outv = match member "out" instr with
      | `List out_l -> List.map (fun e -> extract_var (to_string e)) out_l
      | _ -> failwith "Invalid 'out' field in instruction (must be list)" in
    if dup_vars outv then failwith "Duplicate variables in 'out' field of instruction";
    let op = match member "op" instr with
      | `String s -> (if s = "LiteralAssignment" then (Checker.Inr __)
                      else match evm_opcode_get s with
                           | Some opcode -> (Checker.Inl (Checker.Inr opcode))
                           | None -> (Checker.Inl (Checker.Inl (string_to_char_list s))))
      | _ -> failwith "Invalid 'op' field in instruction (must be string)" in
    { Checker.Checker.EVMInstr.input = inp; 
      Checker.Checker.EVMInstr.output = outv;
      Checker.Checker.EVMInstr.op = op;
    }  


let extract_instructions (instrs: Yojson.Safe.t) : Checker.Checker.EVMInstr.t list =
  List.map extract_instruction (to_list instrs)
   

let extract_block (block: Yojson.Safe.t) : Checker.Checker.EVMBlock.t =
  let bid = match block |> member "id" with
    | `String s -> extract_bid s
    | _ -> failwith "Invalid block ID" in
  let phi_instr = match block |> member "__phi" with
    | `List phi_l -> phi_l
    | _ -> failwith "Invalid __phi in block" in
  let entries = match block |> member "entries" with
    | `List entries_l -> entries_l
    | _ -> [] in
  let phi_info = extract_phi_info phi_instr entries in 
  let exit_info = extract_exit_info (block |> member "exit") in
  let instrs = extract_instructions (block |> member "instructions") in

  { 
    Checker.Checker.EVMBlock.bid = bid; 
    Checker.Checker.EVMBlock.phi_function = phi_info;
    Checker.Checker.EVMBlock.exit_info = exit_info;
    Checker.Checker.EVMBlock.instructions = instrs;
  }


let extract_blocks (blocks_l : Yojson.Safe.t list) : Checker.Checker.EVMBlock.t list =
  List.map extract_block blocks_l


let extract_function (fname: string) (fbody: Yojson.Safe.t) : Checker.Checker.EVMCFGFun.t =
  let args = match fbody |> member "arguments" with
    | `List args_l -> List.map (fun e -> extract_var (to_string e)) args_l
        | _ -> failwith ("Invalid arguments in function " ^ fname) in
  if dup_vars args then failwith ("Duplicate variables in arguments of function " ^ fname);
  let blocks = match fbody |> member "blocks" with
    | `List blocks_l -> extract_blocks blocks_l 
    | _ -> failwith ("Invalid blocks in function " ^ fname) in
  let entry_bid = match fbody |> member "entry" with
    | `String s -> extract_bid s
    | _ -> failwith ("Invalid entry block ID in function " ^ fname) in

  { Checker.Checker.EVMCFGFun.name = string_to_char_list fname;
    Checker.Checker.EVMCFGFun.args = args;
    Checker.Checker.EVMCFGFun.blocks = blocks;
    Checker.Checker.EVMCFGFun.entry_bid = entry_bid;
  }


let extract_functions (flatjson: Yojson.Safe.t) : Checker.Checker.EVMCFGFun.t list =
  List.map (fun (fname, fbody) -> extract_function fname fbody) (to_assoc flatjson)


let extract_prog (flatjson: Yojson.Safe.t) (sc_name: string) : Checker.Checker.EVMCFGProg.t =
  let main_fun, _ = List.hd (to_assoc flatjson) in
  let funs = extract_functions flatjson in
  { Checker.Checker.EVMCFGProg.name = string_to_char_list sc_name;
    Checker.Checker.EVMCFGProg.functions = funs;
    Checker.Checker.EVMCFGProg.main = string_to_char_list main_fun;
  }


let rec create_block_liveness_info (blocks_liveness: (Checker.BlockID.t * (Checker.Checker.EVMLiveness.VarSet.t * Checker.Checker.EVMLiveness.VarSet.t) option ) list) : 
      Checker.Checker.EVMLiveness.func_live_info_t =
  match blocks_liveness with
  | [] -> fun _ -> None
  | (bid, live_info_pair) :: rest ->
      let rest_info = create_block_liveness_info rest in
      fun b -> if b = bid then live_info_pair else rest_info b


let extract_block_liveness (block: Yojson.Safe.t) : Checker.BlockID.t * (Checker.Checker.EVMLiveness.VarSet.t * Checker.Checker.EVMLiveness.VarSet.t) option =
  let bid = match block |> member "id" with
    | `String s -> extract_bid s
    | _ -> failwith "Invalid block ID in liveness info" in
  let live_info_json = match block |> member "liveness" with
    | `Null -> failwith ("Block without liveness information " ^ (to_string (block |> member "id")))
    | li -> li in
  let live_in = match live_info_json |> member "in" with
    | `List in_l -> Checker.Checker.EVMLiveness.list_to_set (List.map (fun e -> extract_var (to_string e)) in_l)
    | _ -> failwith "Invalid 'in' field in liveness info (must be list)" in
  let live_out = match live_info_json |> member "out" with
    | `List out_l -> Checker.Checker.EVMLiveness.list_to_set (List.map (fun e -> extract_var (to_string e)) out_l)
    | _ -> failwith "Invalid 'out' field in liveness info (must be list)" in
  (bid, Some (live_in, live_out))


let extract_blocks_liveness (blocks: Yojson.Safe.t list) : 
      (Checker.BlockID.t * (Checker.Checker.EVMLiveness.VarSet.t * Checker.Checker.EVMLiveness.VarSet.t) option ) list =
  List.map extract_block_liveness blocks


(* Extracts the liveness information from a function body in JSON *)
let extract_funct_liveness (fbody: Yojson.Safe.t) : Checker.Checker.EVMLiveness.func_live_info_t =
  let blocks = match fbody |> member "blocks" with
    | `List blocks_l -> blocks_l
    | _ -> failwith "Invalid blocks in function body for liveness info" in
  let blocks_liveness = extract_blocks_liveness blocks in
  create_block_liveness_info blocks_liveness



let rec create_liveness_info (funs: (string * Checker.Checker.EVMLiveness.func_live_info_t) list) : 
        Checker.Checker.EVMLiveness.prog_live_info_t =
  match funs with
  | [] -> fun _ -> None
  | (fname, finfo) :: rest -> 
      let rest_info = create_liveness_info rest in
      fun f -> if f = string_to_char_list fname then Some finfo
               else rest_info f


let extract_liveness_info (flatjson: Yojson.Safe.t) : Checker.Checker.EVMLiveness.prog_live_info_t =
  let funs_json_assoc = flatjson |> to_assoc in
  let liveness_func = List.map (fun (fname, fbody) -> (fname, extract_funct_liveness fbody)) funs_json_assoc in
  create_liveness_info liveness_func


let extract_prog_and_liveness (flatjson: Yojson.Safe.t) (sc_name: string) 
       : Checker.Checker.EVMCFGProg.t * Checker.Checker.EVMLiveness.prog_live_info_t =
  let p : Checker.Checker.EVMCFGProg.t = extract_prog flatjson sc_name in
  let liveness_info : Checker.Checker.EVMLiveness.prog_live_info_t = extract_liveness_info flatjson in
  (p, liveness_info)


let get_nintrs_block (block: Yojson.Safe.t) : int =
  match block |> member "instructions" with
  | `List bs -> List.length bs
  | _ -> failwith "Invalid blocks in function body for size calculation"


let get_size_blocks (blocks: Yojson.Safe.t list) : int * int =
  let nblocks = List.length blocks in
  let ninstrs = List.fold_left (fun acc block -> acc + get_nintrs_block block) 0 blocks in
  (nblocks, ninstrs)
  

let get_size (json: Yojson.Safe.t) : int * int =
  let sizes = List.map (fun (fname, fbody) -> match fbody |> member "blocks" with
                                  | `List blocks_l -> get_size_blocks blocks_l
                                  | _ -> failwith ("Invalid blocks in function " ^ fname)) (to_assoc json) in
  List.fold_left (fun (acc_blocks, acc_instr) (block_count, instr_count) -> (acc_blocks + block_count, acc_instr + instr_count)) (0, 0) sizes



(******* Main program *******)

(* Arguments *)
let input_file = ref ""
let size = ref false

let speclist = [
  ("-i", Arg.Set_string input_file, "Input JSON file");
  ("-size", Arg.Set size, "Print size of the input file");
]

let anon_fun arg =
  raise (Arg.Bad ("Unexpected argument: " ^ arg))

let usage_msg = "Usage: ./checker [-size] -i filename.json"

let () =
  Arg.parse speclist anon_fun usage_msg;

  if !input_file = "" then (
    prerr_endline "Error: No input file provided.";
    Arg.usage speclist usage_msg;
    exit 1
  );

  if !size then (
    let _, flat_d = read_json_to_flat !input_file in
    let block_count, instr_count = get_size flat_d in
    Printf.printf "%d %d\n" block_count instr_count;
    exit 0
  );

  let sc_main, flat_d = read_json_to_flat !input_file in
  let flat_d' = rename_fun_calls flat_d in
  (*let json_flatd' = Yojson.Safe.pretty_to_string flat_d' in
  let _ = print_endline json_flatd' in *)
  let prog, liveness_info = extract_prog_and_liveness flat_d' sc_main in
  let prog_str = char_list_to_string (Checker.Checker.EVMCFGProg.show prog) in
  let prog_str = Str.global_replace (Str.regexp "\\\\n") "\n" prog_str in
  let _ = Printf.printf "Program:\n%s\n" prog_str in
  let b = Checker.Checker.EVMLiveness.check_program prog liveness_info in
  if b then 
      Printf.printf "LIVENESS_VALID\n"
    else
      Printf.printf "LIVENESS_INVALID\n"


(***** Examples of Program and Liveness Info  as OCaml expressions ******)
(*

let bid : Checker.BlockID.t = int_to_n 3
let bid2 : Checker.BlockID.t = int_to_n 0
let var42 : Checker.VarID.t = int_to_n 42  
let var0 : Checker.VarID.t = int_to_n 0 
let val7 : Checker.z = Checker.Zpos (int_to_pos 7)
let varl : Checker.VarID.t list = [var42; var0]
let sexpr1 : Checker.Checker.ExitInfo.SimpleExprD.t = Inr val7
let sexpr2 : Checker.Checker.ExitInfo.SimpleExprD.t = Inl var42
let fname : Checker.FuncName.t = string_to_char_list "my_function"
let exit1 : Checker.Checker.ExitInfo.t = Checker.Checker.ExitInfo.ConditionalJump (var42, bid, bid)
let exit2 : Checker.Checker.ExitInfo.t = Checker.Checker.ExitInfo.Jump bid
let exit3 : Checker.Checker.ExitInfo.t = Checker.Checker.ExitInfo.ReturnBlock [sexpr1; sexpr2]
let exit4 : Checker.Checker.ExitInfo.t = Checker.Checker.ExitInfo.Terminate
let varl : Checker.VarID.t list = [var42; var0]
let sexprl : Checker.Checker.ExitInfo.SimpleExprD.t list = [sexpr1; sexpr2]
let phi_info : Checker.Checker.EVMPhiInfo.t = 
    fun b -> if b = bid then 
                Checker.Checker.EVMPhiInfo.Coq_in_phi_info (varl, sexprl)
             else
                Checker.Checker.EVMPhiInfo.Coq_in_phi_info ([], [])
let instr1 : Checker.Checker.EVMInstr.t =  
    { Checker.Checker.EVMInstr.input = sexprl; 
      Checker.Checker.EVMInstr.output = varl;
      Checker.Checker.EVMInstr.op = (Inl (Inr Checker.EVM_opcode.ISZERO))
    }
let instr2 : Checker.Checker.EVMInstr.t =  
    { Checker.Checker.EVMInstr.input = sexprl; 
      Checker.Checker.EVMInstr.output = varl;
      Checker.Checker.EVMInstr.op = (Inl (Inl fname))
    }
let __ = let rec f _ = Obj.repr f in Obj.repr f
let instr3 : Checker.Checker.EVMInstr.t =  
    { Checker.Checker.EVMInstr.input = sexprl; 
      Checker.Checker.EVMInstr.output = varl;
      Checker.Checker.EVMInstr.op = Inr __;
    }
let b1 : Checker.Checker.EVMBlock.t = 
    { Checker.Checker.EVMBlock.bid = bid; 
      Checker.Checker.EVMBlock.phi_function = phi_info;
      Checker.Checker.EVMBlock.exit_info = exit1; 
      Checker.Checker.EVMBlock.instructions = [instr1; instr2; instr3] }
let fun1 : Checker.Checker.EVMCFGFun.t = 
    { Checker.Checker.EVMCFGFun.name = fname;
      Checker.Checker.EVMCFGFun.args = varl;
      Checker.Checker.EVMCFGFun.blocks = [b1];
      Checker.Checker.EVMCFGFun.entry_bid = bid;
    }      
let prog : Checker.Checker.EVMCFGProg.t =
    { Checker.Checker.EVMCFGProg.name = string_to_char_list "Program";
      Checker.Checker.EVMCFGProg.functions = [fun1];
      Checker.Checker.EVMCFGProg.main = fname;
    } 
let liveness_info : Checker.Checker.EVMLiveness.prog_live_info_t = fun _ -> None
let liveness_info2 : Checker.Checker.EVMLiveness.prog_live_info_t = 
    let f1_liveness = function
    | N0 ->
      let vin = EVMLiveness.list_to_set (N0::((Npos XH)::[])) in
      let vout = EVMLiveness.list_to_set ((Npos XH)::((Npos (XI (XI (XI (XO XH)))))::[])) in
      Some (vin , vout)
    | Npos _ -> None
    in 
    fun _ => Some f1_liveness

(*
SUMMARY OF OCAML TYPES:
* Checker.BlockID.t = Checker.n
* Checker.VarID.t = Checker.n
* Checker.EVMDialect.value_t = Checker.z
* Checker.Checker.ExitInfo.SimpleExprD.t = Inl Checker.n | Inr Checker.z
* Checker.FuncName.t = char list
* Checker.Checker.ExitInfo.t = 
    | Checker.Checker.ExitInfo.ConditionalJump of VarID.t * BlockID.t * BlockID.t
    | Checker.Checker.ExitInfo.Jump of BlockID.t
    | Checker.Checker.ExitInfo.ReturnBlock of Checker.Checker.ExitInfo.SimpleExprD.t list
    | Checker.Checker.ExitInfo.Terminate
* Checker.Checker.EVMPhiInfo.t =
           Checker.BlockID.t -> Checker.Checker.EVMPhiInfo.coq_InBlockPhiInfo
* Checker.Checker.EVMPhiInfo.coq_InBlockPhiInfo =
    | Checker.Checker.EVMPhiInfo.Coq_in_phi_info (Checker.VarID.t list * Checker.Checker.ExitInfo.SimpleExprD.t list)
*)

*)