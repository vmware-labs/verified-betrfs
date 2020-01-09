.DEFAULT_GOAL := build/libycsbc.a

CC=g++
CFLAGS=-std=c++11 -g -Wall -I../vendor/YCSB-C/core -fPIC -O3 -msse4.2 -g

YCSB_SRCPATH=../vendor/YCSB-C/core
YCSB_HEADERS=core_workload.h generator.h \
		counter_generator.h properties.h uniform_generator.h \
		const_generator.h scrambled_zipfian_generator.h utils.h \
		discrete_generator.h skewed_latest_generator.h \
		zipfian_generator.h db.h

YCSB_HEADER_TARGETS=$(addprefix build/include/,$(YCSB_HEADERS))

ycsb: build/libycsbc.a $(HEADER_TARGETS)

$(YCSB_HEADER_TARGETS): build/include/% : $(YCSB_SRCPATH)/%
	@mkdir -p build/include
	cp $< $@

build/ycsb_core_workload.o: $(addprefix $(YCSB_SRCPATH)/,$(YCSB_HEADERS)) $(YCSB_SRCPATH)/core_workload.cc
	@mkdir -p build
	$(CC) $(CFLAGS) -c \
		$(YCSB_SRCPATH)/core_workload.cc \
		-o build/ycsb_core_workload.o

build/include/ycsbwrappers.h: wrappers/ycsbwrappers.h
	@mkdir -p build/include
	cp $< $@

build/ycsbwrappers.o: wrappers/ycsbwrappers.h wrappers/ycsbwrappers.cpp $(YCSB_HEADER_TARGETS) build/include/ycsbwrappers.h
	@mkdir -p build
	$(CC) $(CFLAGS) -c \
		wrappers/ycsbwrappers.cpp \
		-o build/ycsbwrappers.o

build/libycsbc.a: build/ycsb_core_workload.o build/ycsbwrappers.o
	ar rvs build/libycsbc.a build/ycsb_core_workload.o build/ycsbwrappers.o

clean:
	- rm -rf build/

.PHONY: clean
