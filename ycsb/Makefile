.DEFAULT_GOAL := build/libycsbc-default.a

# libycsbc-default is compatible with the default standard library
# of the system.

# libycsbc-libcpp is compatible with libc++

CC=clang++
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

build/ycsb_core_workload-default.o: $(addprefix $(YCSB_SRCPATH)/,$(YCSB_HEADERS)) $(YCSB_SRCPATH)/core_workload.cc
	@mkdir -p build
	$(CC) $(CFLAGS) -c \
		$(YCSB_SRCPATH)/core_workload.cc \
		-o $@

build/ycsb_core_workload-libcpp.o: $(addprefix $(YCSB_SRCPATH)/,$(YCSB_HEADERS)) $(YCSB_SRCPATH)/core_workload.cc
	@mkdir -p build
	$(CC) $(CFLAGS) -c \
		$(YCSB_SRCPATH)/core_workload.cc \
		-stdlib=libc++ \
		-o $@

build/include/ycsbwrappers.h: wrappers/ycsbwrappers.h
	@mkdir -p build/include
	cp $< $@

build/ycsbwrappers-default.o: wrappers/ycsbwrappers.h wrappers/ycsbwrappers.cpp $(YCSB_HEADER_TARGETS) build/include/ycsbwrappers.h
	@mkdir -p build
	$(CC) $(CFLAGS) -c \
		wrappers/ycsbwrappers.cpp \
		-o $@

build/ycsbwrappers-libcpp.o: wrappers/ycsbwrappers.h wrappers/ycsbwrappers.cpp $(YCSB_HEADER_TARGETS) build/include/ycsbwrappers.h
	@mkdir -p build
	$(CC) $(CFLAGS) -c \
		wrappers/ycsbwrappers.cpp \
		-stdlib=libc++ \
		-o $@


build/libycsbc-default.a: build/ycsb_core_workload-default.o build/ycsbwrappers-default.o
	ar rvs $@ build/ycsb_core_workload-default.o build/ycsbwrappers-default.o

build/libycsbc-libcpp.a: build/ycsb_core_workload-libcpp.o build/ycsbwrappers-libcpp.o
	ar rvs $@ build/ycsb_core_workload-libcpp.o build/ycsbwrappers-libcpp.o

clean:
	- rm -rf build/

.PHONY: clean
