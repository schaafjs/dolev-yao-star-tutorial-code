DY_HOME ?= ../dolev-yao-star-extrinsic

EXAMPLES = nsl_pk_no_events_lookup TwoMessageP Online Online_with_secrecy
EXAMPLE_DIRS = dy-extensions $(addprefix examples/, $(EXAMPLES))
include $(DY_HOME)/Makefile
