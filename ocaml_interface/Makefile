.PHONY: default
default: all ;

MAIN = main.ml
PACKAGES = yojson,zarith
EXE = foryu
STATIC_EXE = static_foryu


all: executable static_executable
	mv $(EXE) ../bin
	mv $(STATIC_EXE) ../bin

executable: checker $(MAIN)
	ocamlfind ocamlopt -package $(PACKAGES) -linkpkg -o $(EXE) checker.cmx str.cmxa $(MAIN) 

checker: checker.ml checker.mli
	ocamlfind ocamlopt -package $(PACKAGES) -c checker.mli -o checker.cmi
	ocamlfind ocamlopt -package $(PACKAGES) -c checker.ml -o checker.cmx

static_executable: checker $(MAIN)
	ocamlfind ocamlopt -package $(PACKAGES) -linkpkg -o $(STATIC_EXE) -ccopt -static checker.cmx str.cmxa $(MAIN) 

static_checker: checker.ml checker.mli
	ocamlfind ocamlopt -package $(PACKAGES) -c checker.mli -ccopt -static -o checker.cmi
	ocamlfind ocamlopt -package $(PACKAGES) -c checker.ml -ccopt -static -o checker.cmx

clean:
	rm -f *.cmi
	rm -f *.cmx
	rm -f *.o
	rm -f $(EXE)
	rm -f $(STATIC_EXE)

clean_all: clean
	rm -f checker.ml
	rm -f checker.mli

