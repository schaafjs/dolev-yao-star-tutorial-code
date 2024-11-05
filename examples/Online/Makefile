DY_HOME ?= ../../../dolev-yao-star-extrinsic

EXAMPLES = Online
EXAMPLE_DIRS = ../../dy-extensions $(addprefix ../, $(EXAMPLES))
include $(DY_HOME)/Makefile

test:
	cd $(DY_HOME)/obj; OCAMLPATH=$(FSTAR_HOME)/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_Online_Run.native
	$(DY_HOME)/obj/DY_Online_Run.native
