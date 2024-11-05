DY_HOME ?= ../../../dolev-yao-star-extrinsic

EXAMPLES = nsl_pk_no_events_lookup
EXAMPLE_DIRS = ../../dy-extensions $(addprefix ../, $(EXAMPLES))
include $(DY_HOME)/Makefile

test:
	cd $(DY_HOME)/obj; OCAMLPATH=$(FSTAR_HOME)/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_Example_NSL_Debug.native
	$(DY_HOME)/obj/DY_Example_NSL_Debug.native
