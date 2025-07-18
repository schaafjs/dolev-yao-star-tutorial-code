TUTORIAL_HOME ?= ../..

#DY_HOME ?= $(TUTORIAL_HOME)

# Make path absolute
EXAMPLE_DIRS = $(TUTORIAL_HOME)/examples/NSL

include $(TUTORIAL_HOME)/Makefile

test:
		cd $(TUTORIAL_HOME)/obj; $(FSTAR_EXE) --ocamlenv ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_NSL_Run.native
		$(TUTORIAL_HOME)/obj/DY_NSL_Run.native
