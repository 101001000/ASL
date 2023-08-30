# Variables
OCAMLLEX = ocamllex
MENHIR = menhir --infer
SRCDIR = extracted

#SOURCES_ML = $(wildcard extracted/*.ml)
#SOURCES_MLI = $(wildcard extracted/*.mli)
#SORTED_FILES := $(shell ocamldep -sort $(SOURCES_MLI) $(SOURCES_ML))

OCAMLC = ocamlc
OCAMLOPT = ocamlopt

# Default target
all: main

coqextracted:
	make -C coq -f Makefile
	-patch -N -p0 < CRelationClasses.mli.patch
	
#SOURCES_ML =  $(wildcard extracted/*.ml) $(wildcard ../vellvm/src/ml/libvellvm/*.ml)
#SOURCES_MLI =  $(wildcard extracted/*.mli) $(wildcard ../vellvm/src/ml/libvellvm/*.mli)
#SORTED_FILES := $(shell ocamldep -sort $(SOURCES_MLI) $(SOURCES_ML))


# Rule for lexer
#lexer.ml: lexer.mll
#	$(OCAMLLEX) $<
#
## Rules for parser
#parser.ml : parser.mly
#	$(MENHIR) $<

#compile: $(SOURCES)
#	$(OCAMLC) -o main $(SOURCES)

#extracted/AST.cmx: extracted/AST.ml
#	$(OCAMLOPT) -c $<

# Compile the OCaml sources
#compile: $(SOURCES)
#	$(OCAMLC) -o main $(SOURCES)
#


#cmi:
#	$(OCAMLOPT) -I extracted -c $(SORTED_MLI)

#extractedcomp: coqextracted
#	-patch -N -p0 < CRelationClasses.mli.patch
#	$(OCAMLOPT) -I extracted -o main $(SORTED_FILES) 

main: coqextracted
	dune build
	#$(OCAMLOPT) -I extracted -I ../vellvm/src/ml/libvellvm -o main $(SORTED_FILES) parser.ml lexer.ml main.ml

# Generate dependency information
#.depend: $(SOURCES_ML) $(SOURCES_MI)
#	ocamldep -sort $(SOURCES_ML) $(SOURCES_MLI) > .depend

# Clean generated files
clean:
	rm -f lexer.ml parser.ml 
	rm -f extracted/*.ml extracted/*.mi extracted/*.o extracted/*.cmi extracted/*.cmx extracted/*.mli extracted/*.aux extracted/*.glob extracted/*.vo extracted/*.vok extracted/*.vos extracted/*.orig extracted/*.aux extracted/*.rej

.PHONY: all clean