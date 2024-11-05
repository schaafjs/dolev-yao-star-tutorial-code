DY_HOME ?= ../../../dolev-yao-star-extrinsic

EXAMPLES = Online_with_secrecy
EXAMPLE_DIRS = ../../dy-extensions $(addprefix ../, $(EXAMPLES))
include $(DY_HOME)/Makefile

test:
	cd $(DY_HOME)/obj; OCAMLPATH=$(FSTAR_HOME)/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_OnlineS_Run.native
	$(DY_HOME)/obj/DY_OnlineS_Run.native
