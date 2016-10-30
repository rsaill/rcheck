.PHONY: clean rcheck 

rcheck:
	ocamlbuild -lib unix -Is -use-ocamlfind -pkgs menhirLib -menhir 'menhir --table --explain' rcheck.native

clean:
	ocamlbuild -clean
