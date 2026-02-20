.PHONY: default
default: all ;

MAIN = main.ml
EXE = checker
PACKAGES = yojson,zarith


all: executable 

executable: checker $(MAIN)
	ocamlfind ocamlopt -package $(PACKAGES) -linkpkg -o $(EXE) checker.cmx str.cmxa $(MAIN) 

checker: checker.ml checker.mli
	ocamlfind ocamlopt -package $(PACKAGES) -c checker.mli -o checker.cmi
	ocamlfind ocamlopt -package $(PACKAGES) -c checker.ml -o checker.cmx

clean:
	rm -f *.cmi
	rm -f *.cmx
	rm -f *.o
	rm -f $(EXE)

clean_all: clean
	rm -f checker.ml
	rm -f checker.mli

