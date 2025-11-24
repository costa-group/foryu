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

**Important: use the installation scripts from the repository (`git clone --branch main https://github.com/coq/platform.git`) instead of the ZIP file that appears in the instructions. The scripts from the ZIP file has some problems with version of the packages. More information: https://rocq-prover.zulipchat.com/#narrow/channel/237977-Rocq-users/topic/Install.20.20Ubuntu.2024.2E04.20fails.20.3B.20dune.2Econfigurator.2C.20elpi/near/528321610**

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


  
