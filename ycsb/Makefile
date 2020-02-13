.DEFAULT_GOAL := build/libycsbc-$(STDLIB).a

CC=clang++
CFLAGS=-std=c++11 -g -Wall -I../vendor/YCSB-C/core -fPIC -O3 -msse4.2 -g

ifeq ($(STDLIB), libcpp)
	CFLAGS += -stdlib=libc++
endif

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

build/ycsb_core_workload-$(STDLIB).o: $(addprefix $(YCSB_SRCPATH)/,$(YCSB_HEADERS)) $(YCSB_SRCPATH)/core_workload.cc
	@mkdir -p build
	$(CC) $(CFLAGS) -c \
		$(YCSB_SRCPATH)/core_workload.cc \
		-o $@

build/include/ycsbwrappers.h: wrappers/ycsbwrappers.h
	@mkdir -p build/include
	cp $< $@

build/ycsbwrappers-$(STDLIB).o: wrappers/ycsbwrappers.h wrappers/ycsbwrappers.cpp $(YCSB_HEADER_TARGETS) build/include/ycsbwrappers.h
	@mkdir -p build
	$(CC) $(CFLAGS) -c \
		wrappers/ycsbwrappers.cpp \
		-o $@

build/libycsbc-$(STDLIB).a: build/ycsb_core_workload-$(STDLIB).o build/ycsbwrappers-$(STDLIB).o
	ar rvs $@ build/ycsb_core_workload-$(STDLIB).o build/ycsbwrappers-$(STDLIB).o

clean:
	- rm -rf build/

.PHONY: clean
