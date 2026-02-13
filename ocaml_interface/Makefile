.PHONY: default
default: all ;

MAIN = main.ml
EXE = checker
PACKAGES = yojson


all: executable 

executable: checker $(MAIN)
	ocamlfind ocamlopt -package $(PACKAGES) -linkpkg -o $(EXE) checker.cmx str.cmxa $(MAIN) 

checker: checker.ml checker.mli
	ocamlopt -c checker.mli -o checker.cmi
	ocamlopt -c checker.ml -o checker.cmx

clean:
	rm -f *.cmi
	rm -f *.cmx
	rm -f *.o
	rm -f $(EXE)

clean_all: clean
	rm -f checker.ml
	rm -f checker.mli

