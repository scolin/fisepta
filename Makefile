
CILPATH=cil-code/lib/cil
GRAPHPATH=$(shell ocamlfind query ocamlgraph)

all: FunPointers.exe notcc.exe

FunPointers.exe: main.ml
	ocamlopt -o FunPointers.exe -I $(CILPATH) -I $(GRAPHPATH) bigarray.cmxa str.cmxa unix.cmxa nums.cmxa cil.cmxa graph.cmxa main.ml

notcc.exe: notcc.ml
	ocamlopt -o notcc.exe -I $(CILPATH) str.cmxa unix.cmxa nums.cmxa cil.cmxa notcc.ml

clean:
	rm -f *.cmi *.cmo *.cmx *.o version.ml

veryclean: clean
	rm -f FunPointers.exe notcc.exe

FORCE:
