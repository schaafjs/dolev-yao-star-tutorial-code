# DY_HOME ?= ../../..

EXAMPLES = nsl_pk_no_events_lookup TwoMessageP Online
EXAMPLE_DIRS = dy-extensions $(addprefix examples/, $(EXAMPLES))
include $(DY_HOME)/Makefile
