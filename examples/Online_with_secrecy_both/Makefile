# DY_HOME ?= ../../..

EXAMPLE_DIRS = . ../../dy-extensions
include $(DY_HOME)/Makefile


test:
	cd $(DY_HOME)/obj; OCAMLPATH=$(FSTAR_HOME)/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_OnlineSB_Run.native
	$(DY_HOME)/obj/DY_OnlineSB_Run.native
