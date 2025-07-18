TUTORIAL_HOME ?= ../..

DY_HOME ?= $(TUTORIAL_HOME)

# Make path absolute
EXAMPLE_DIRS = $(DY_HOME)/examples/TwoMessage

# Convert path to absolute one regardless of current working dir. Not needed.
#EXAMPLE_DIRS ?= $(abspath $(DY_HOME)/examples/TwoMessageP)

include $(TUTORIAL_HOME)/Makefile

test:
		cd $(TUTORIAL_HOME)/obj; $(FSTAR_EXE) --ocamlenv ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_TwoMessage_Run.native
		$(TUTORIAL_HOME)/obj/DY_TwoMessage_Run.native
