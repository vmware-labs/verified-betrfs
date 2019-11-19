ROOT=./
TARGETS=

include $(ROOT)/tools/Makefile.template

exe:
	cd disk-betree && make exe
