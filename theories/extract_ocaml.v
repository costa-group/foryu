(** NOTES:
 
  Some problems related to type extraction:
   
   - Types like bool, list and prod have straight forward representations
   in Ocaml. nat by other hand, is extracted and represented in a naive
   way, that might not be efficient for certain applications.
   Also, if we extract it as an ocaml int, we would lose consistency
   with w.r.t. to the proven theorems.
   
   Ways of addressing this problem are available here:
   https://softwarefoundations.cis.upenn.edu/vfa-current/Extract.html
   
   Currently, no fancy nat extraction might be enough.
 

    TODO:

    - Extract option
    - Extract nat into an efficient type.
    - Extract bbv library Word into an efficient type. *)

Require Import FORYU.checker.
Import Checker.
(*Require Import FORYU.test_translation.
Import TestTranslation.*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import extraction.ExtrOcamlString.
Import ExtrOcamlString.
From Stdlib Require Import extraction.ExtrOcamlZBigInt. (* Extracts Z.t *)

(** Type Extractions **)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "( , )" ].

(** Program Extractions **)
(*  Examples from example.v are extracted and directly tested.
    After running the next line, use "make run" in order to compile and
    run the test_examples.ml file. *)
Set Extraction Output Directory "ocaml_interface".
Extraction "checker.ml" Checker. 
