# FORYU
A FORmal semantics for Yul in Coq

## Requirements
1. Coq 8.20.1 (Rocq Prover 2025.01 with the first package pick from Jan 2025)

## Compilation

    $ coq_makefile -f _CoqProject -o Makefile
    $ make

## Installation of the Rocq Platform on Linux
The recommended way to install the Rocq Prover for the FORYU project is using the **Rocq Platform**, following the instructions at:
https://github.com/rocq-prover/platform/blob/2025.01.0/doc/README_Linux.md#installation-by-compiling-from-sources-using-scripts--opam

Recommended options:

* Coq Version 8.20

      Coq 8.20.1 (released Jan 2025) with the first package pick from Jan 2025`

* Full installation

      ====================== JUST COQ OR COMPLETE PLATFORM ? =======================
      Install full (f), extended (x), base (b) or IDE (i)? (f/x/b/i/c=cancel) f
 
* Do not install SW CompCert


      ================================== COMPCERT ==================================
      Install non open source SW CompCert (y) or (n)? (y/n/c=cancel) n


* Exclude large packages
      
      =============================== LARGE PACKAGES ===============================
      Include (i) exclude (e) or select (s) large packages? (i/e/s/c=cancel) e


  
