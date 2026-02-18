(*
let main () =
  let res = Checker.TestTranslation.check in
    Printf.fprintf stdout "%B\n%!" res;;


let _ = main ();;
*)

open Yojson.Safe
open Yojson.Safe.Util
module StringSet = Set.Make(String)

type assoc_t = (string * Yojson.Safe.t) list

(* Replaces the value associated to 'key' in the JSON j *)
let replace_assoc (key:string) (v:Yojson.Safe.t) (j:Yojson.Safe.t) : Yojson.Safe.t =
  match j with
  | `Assoc al ->
      let al' = (key, v) :: List.filter (fun (k,_) -> k <> key) al in
      `Assoc al'
  | _ -> j


let fun_names : StringSet.t ref = ref StringSet.empty

let evm_opcode_list = [
  ("stop","EVM_opcode.STOP");
  ("add","EVM_opcode.ADD");
  ("sub","EVM_opcode.SUB");
  ("mul","EVM_opcode.MUL");
  ("div","EVM_opcode.DIV");
  ("sdiv","EVM_opcode.SDIV");
  ("mod","EVM_opcode.MOD");
  ("smod","EVM_opcode.SMOD");
  ("exp","EVM_opcode.EXP");
  ("not","EVM_opcode.NOT");
  ("lt","EVM_opcode.LT");
  ("gt","EVM_opcode.GT");
  ("slt","EVM_opcode.SLT");
  ("sgt","EVM_opcode.SGT");
  ("eq","EVM_opcode.EQ");
  ("iszero","EVM_opcode.ISZERO");
  ("and","EVM_opcode.AND");
  ("or","EVM_opcode.OR");
  ("xor","EVM_opcode.XOR");
  ("byte","EVM_opcode.BYTE");
  ("shl","EVM_opcode.SHL");
  ("shr","EVM_opcode.SHR");
  ("sar","EVM_opcode.SAR");
  ("addmod","EVM_opcode.ADDMOD");
  ("mulmod","EVM_opcode.MULMOD");
  ("signextend","EVM_opcode.SIGNEXTEND");
  ("keccak256","EVM_opcode.KECCAK256");
  ("pop","EVM_opcode.POP");
  ("mload","EVM_opcode.MLOAD");
  ("mstore","EVM_opcode.MSTORE");
  ("mstore8","EVM_opcode.MSTORE8");
  ("sload","EVM_opcode.SLOAD");
  ("sstore","EVM_opcode.SSTORE");
  ("tload","EVM_opcode.TLOAD");
  ("tstore","EVM_opcode.TSTORE");
  ("msize","EVM_opcode.MSIZE");
  ("gas","EVM_opcode.GAS");
  ("address","EVM_opcode.ADDRESS");
  ("balance","EVM_opcode.BALANCE");
  ("selfbalance","EVM_opcode.SELFBALANCE");
  ("caller","EVM_opcode.CALLER");
  ("callvalue","EVM_opcode.CALLVALUE");
  ("calldataload","EVM_opcode.CALLDATALOAD");
  ("calldatasize","EVM_opcode.CALLDATASIZE");
  ("calldatacopy","EVM_opcode.CALLDATACOPY");
  ("codesize","EVM_opcode.CODESIZE");
  ("codecopy","EVM_opcode.CODECOPY");
  ("extcodesize","EVM_opcode.EXTCODESIZE");
  ("extcodecopy","EVM_opcode.EXTCODECOPY");
  ("returndatasize","EVM_opcode.RETURNDATASIZE");
  ("returndatacopy","EVM_opcode.RETURNDATACOPY");
  ("mcopy","EVM_opcode.MCOPY");
  ("extcodehash","EVM_opcode.EXTCODEHASH");
  ("create","EVM_opcode.CREATE");
  ("create2","EVM_opcode.CREATE2");
  ("call","EVM_opcode.CALL");
  ("callcode","EVM_opcode.CALLCODE");
  ("delegatecall","EVM_opcode.DELEGATECALL");
  ("staticcall","EVM_opcode.STATICCALL");
  ("return","EVM_opcode.RETURN");
  ("revert","EVM_opcode.REVERT");
  ("selfdestruct","EVM_opcode.SELFDESTRUCT");
  ("invalid","EVM_opcode.INVALID");
  ("log0","EVM_opcode.LOG0");
  ("log1","EVM_opcode.LOG1");
  ("log2","EVM_opcode.LOG2");
  ("log3","EVM_opcode.LOG3");
  ("log4","EVM_opcode.LOG4");
  ("chainid","EVM_opcode.CHAINID");
  ("basefee","EVM_opcode.BASEFEE");
  ("blobbasefee","EVM_opcode.BLOBBASEFEE");
  ("origin","EVM_opcode.ORIGIN");
  ("gasprice","EVM_opcode.GASPRICE");
  ("blockhash","EVM_opcode.BLOCKHASH");
  ("blobhash","EVM_opcode.BLOBHASH");
  ("coinbase","EVM_opcode.COINBASE");
  ("timestamp","EVM_opcode.TIMESTAMP");
  ("number","EVM_opcode.NUMBER");
  ("difficulty","EVM_opcode.DIFFICULTY");
  ("prevrandao","EVM_opcode.PREVRANDAO");
  ("gaslimit","EVM_opcode.GASLIMIT");
  ("memoryguard","EVM_opcode.MEMORYGUARD");
  ("datasize","EVM_opcode.DATASIZE");
  ("dataoffset","EVM_opcode.DATAOFFSET");
  ("datacopy","EVM_opcode.DATACOPY");
  (* FIXME TODO *)
  ("LiteralAssignment", "EVMInstr.ASSIGN");
  ("linkersymbol", "EVMInstr.LinkerSymbol");
  ("setimmutable", "EVM_opcode.setimmutable");
  ("loadimmutable", "EVM_opcode.loadimmutable");
]

let evm_opcode_tbl : (string, string) Hashtbl.t =
  let tbl = Hashtbl.create (List.length evm_opcode_list) in
  List.iter (fun (k,v) -> Hashtbl.add tbl k v) evm_opcode_list;
  tbl

let evm_opcode_get (k:string) : string option =
  (* requires OCaml with Hashtbl.find_opt, otherwise use try/with Not_found *)
  Hashtbl.find_opt evm_opcode_tbl k




(* Generates a string representing a prefix of the object path:
  ['source_import_subdir_sol', 'C', 'C_3'] => 'source_import_subdir_sol__C__C_3' *)
let gen_name prefix fname_opt =
  let parts = match fname_opt with
    | Some f -> prefix @ [f]
    | None -> prefix
  in
  String.concat "__" parts
  |> String.map (fun c -> if c = '.' then '_' else c

)(*******************************************)



(* Extracts the PhiFunctions from the "instructions" entry and creates a different "__phi" entry for them 
   in each block *)
let split_phi_instr_block (block: Yojson.Safe.t): Yojson.Safe.t =
  let instructions = block |> member "instructions" |> to_list in
  let (phi_instrs, other_instrs) = List.partition (fun instr -> match instr |> member "op" with
                                                              | `String "PhiFunction" -> true
                                                              | _ -> false) instructions in
  let block' = replace_assoc "instructions" (`List other_instrs) block in
  replace_assoc "__phi" (`List phi_instrs) block'


let split_phi_instr_blocks (blocks: Yojson.Safe.t): Yojson.Safe.t =
  `List (List.map split_phi_instr_block (to_list blocks))



(* Receives a list of blocks of an entry function and generates the function definition *)
let process_blocks_entry (blocks: Yojson.Safe.t) (prefix: string list): assoc_t =
  let fname = gen_name prefix (Some "entry") in
  let fcontents = `Assoc [("arguments", `List []); 
                          ("blocks", split_phi_instr_blocks blocks); (* We do not rename function calls yet *)
                          ("entry", List.hd (to_list blocks) |> member "id");
                          ("numReturns", `Int 0);
                          ("__prefix", `List (List.map (fun s -> `String s) prefix))] in
  [(fname, fcontents)]
  

let process_function (f: string * Yojson.Safe.t) (prefix: string list): string * Yojson.Safe.t =
  let (fname, fjson) = f in
  let newname = gen_name prefix (Some fname) in
  match StringSet.mem newname !fun_names with
  | true -> failwith ("Duplicate function name: " ^ newname)
  | false ->  fun_names := StringSet.add newname !fun_names;
              let blocks = match fjson |> member "blocks" with
                | `Null -> `List []
                | bs -> split_phi_instr_blocks bs in
              let fjson' = replace_assoc "blocks" blocks fjson in
              let fjson'' = replace_assoc "__prefix" (`List (List.map (fun s -> `String s) prefix)) fjson' in
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



(********************************************)



let rename_function_calls_instruction (instr: Yojson.Safe.t) (prefix: string list): Yojson.Safe.t =
  let op = instr |> member "op" |> to_string in
  let op' = match evm_opcode_get op with
  | Some _ -> op
  | None -> let newname = gen_name prefix (Some op) in 
            match StringSet.mem newname !fun_names with
            | false -> Printf.printf "[%s]\n" (String.concat "; " (StringSet.elements !fun_names));
                       let instr_str = Yojson.Safe.pretty_to_string instr in 
                       (*Printf.printf "Call to function defined outside the object. Op='%s'\n" op;
                       Printf.printf "Prefix: %s\n" (prefix |> String.concat "__");*)
                       failwith ("Call to function defined outside the object. \n Instr=" ^ instr_str ^ " Op='" ^ op  ^ "' with prefix " ^ (prefix |> String.concat "__"))
                       (*op*)
            | true -> newname in
  replace_assoc "op" (`String op') instr


let rename_function_calls_instructions (instructions: Yojson.Safe.t list) (prefix: string list): Yojson.Safe.t list =
  List.map (fun instr -> rename_function_calls_instruction instr prefix) instructions


let rename_function_calls_block (block: Yojson.Safe.t) (prefix: string list): Yojson.Safe.t =
  let instructions = block |> member "instructions" |> to_list in
  let instructions' = rename_function_calls_instructions instructions prefix in 
  replace_assoc "instructions" (`List instructions') block


let rename_function_calls_blocks (blocks: Yojson.Safe.t) (prefix: string list): Yojson.Safe.t =
  `List (List.map (fun b -> rename_function_calls_block b prefix) (to_list blocks))


let rename_fun_call (fname: string) (fbody: Yojson.Safe.t): string * Yojson.Safe.t =
  let blocks = match fbody |> member "blocks" with
    | `Null -> `List []
    | bs -> rename_function_calls_blocks bs (to_list (member "__prefix" fbody) |> List.map to_string) in
  let fbody' = replace_assoc "blocks" blocks fbody in
  (fname, fbody')


(* Rename and check function calls in a flat JSON *)
let rename_fun_calls (flatjson: Yojson.Safe.t): Yojson.Safe.t =
  let funs' = List.map (fun (fname, fbody) -> (rename_fun_call fname fbody)) (to_assoc flatjson) in
  `Assoc funs'


(********************************************************)

(* Main code *)
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

(*
let () =
  (* 3. Parse the arguments *)
  Arg.parse speclist anon_fun usage_msg;

  (* 4. Use the parsed values *)
  if !input_file = "" then (
    prerr_endline "Error: No input file provided.";
    Arg.usage speclist usage_msg;
    exit 1
  );

  let sc_main_opt, flat_d = read_json_to_flat !input_file in
  (*let json_flatd = Yojson.Safe.pretty_to_string flat_d in
  print_endline json_flatd;*)
  let flat_d' = rename_fun_calls flat_d in
  let json_flatd' = Yojson.Safe.pretty_to_string flat_d' in
  print_endline json_flatd'
  (*Printf.printf "[%s]\n" (String.concat "; " (StringSet.elements !fun_names))*)

*)


let nat_to_int (n : Checker.nat) : int =
  let rec aux n acc =
    match n with
    | Checker.O -> acc
    | Checker.S n' -> aux n' (acc + 1)
  in
  aux n 0

let int_to_nat (n : int) : Checker.nat =
  let rec aux n acc =
    if n <= 0 then acc
    else aux (n - 1) (Checker.S acc)
  in
  aux n Checker.O  

let string_of_checker_nat (n : Checker.nat) : string =
  string_of_int (nat_to_int n)

(* build positive from an OCaml int (>0) *)
let rec int_to_pos (n: int) : Checker.positive =
  if n = 1 then Checker.XH
  else if n mod 2 = 0 then Checker.XO (int_to_pos (n / 2))
  else Checker.XI (int_to_pos (n / 2))

let int_to_n (i: int) : Checker.n =
  if i <= 0 then Checker.N0 else Checker.Npos (int_to_pos i)

let rec pos_to_int (p: Checker.positive) : int =
  match p with
  | Checker.XH -> 1
  | Checker.XO p' -> 2 * (pos_to_int p')
  | Checker.XI p' -> 2 * (pos_to_int p') + 1

let n_to_string (n: Checker.n) : string =
  match n with
  | Checker.N0 -> "0"
  | Checker.Npos p -> string_of_int (pos_to_int p)

let z_to_string (z: Checker.z) : string =
  match z with
  | Checker.Z0 -> "0"
  | Checker.Zpos p -> string_of_int (pos_to_int p)
  | Checker.Zneg p -> "-" ^ string_of_int (pos_to_int p)

let simple_expr_to_string (s: Checker.Checker.ExitInfo.SimpleExprD.t) : string =
  match s with
  | Inl v -> "VarID(" ^ (n_to_string v) ^ ")"
  | Inr z -> "Value(" ^ (z_to_string z) ^ ")"  

(* Convert between OCaml `string` and `char list` (extracted `FuncName.t`) *)
let string_to_char_list (s : string) : char list =
  let rec aux i acc =
    if i < 0 then acc else aux (i - 1) (s.[i] :: acc)
  in aux (String.length s - 1) []

let char_list_to_string (cl : char list) : string =
  let buf = Buffer.create (List.length cl) in
  List.iter (Buffer.add_char buf) cl;
  Buffer.contents buf

let funcname_of_string = string_to_char_list
let string_of_funcname = char_list_to_string

(*let main () =
  let res = Checker.Checker.myfun (Terminate) in
  match res with
  | Terminate -> Printf.printf "Result: Terminate\n"
  | _ -> Printf.printf "Result: Otro\n"
*)


let bid : Checker.BlockID.t = int_to_n 3
let bid2 : Checker.BlockID.t = int_to_n 0
let var42 : Checker.VarID.t = int_to_n 42  
let var0 : Checker.VarID.t = int_to_n 0 
let val7 : Checker.z = Checker.Zpos (int_to_pos 7)
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


let main () =
  let res = Checker.Checker.myfun phi_info in
  let thebid = bid in
  match (res thebid) with
  | Checker.Checker.EVMPhiInfo.Coq_in_phi_info (vars, sexprs) -> 
      Printf.printf "Phi info for block %s:\n" (n_to_string thebid);
      Printf.printf "  Vars: [%s]\n" (String.concat "; " (List.map n_to_string vars));
      Printf.printf "  SimpleExprs: [%s]\n" (String.concat "; " (List.map simple_expr_to_string sexprs))
  | _ -> Printf.printf "Phi info for block %s: No info\n" (n_to_string thebid)
  
  
let _ = main ();;

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
