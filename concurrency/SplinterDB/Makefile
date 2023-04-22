# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: Apache-2.0

.DEFAULT_GOAL := release

PLATFORM = linux

#*************************************************************#
# DIRECTORIES, SRC, OBJ, ETC
#

SRCDIR   = src
TESTSDIR = tests
OBJDIR   = obj
VERI_OBJDIR   = veriobj
BINDIR   = bin

CC=clang-13
LD=clang-13

CPPSRC := $(shell find $(SRCDIR) -name "*.cpp")
SRC := $(shell find $(SRCDIR) -name "*.c")
TESTSRC := $(shell find $(TESTSDIR) -name "*.c")

OBJ := $(SRC:%.c=$(OBJDIR)/%.o)
TESTOBJ= $(TESTSRC:%.c=$(OBJDIR)/%.o)

VERI_OBJ := $(SRC:%.c=$(VERI_OBJDIR)/%.o) $(CPPSRC:%.cpp=$(VERI_OBJDIR)/%.o)
VERI_TESTOBJ := $(TESTSRC:%.c=$(VERI_OBJDIR)/%.o)

# Automatically create directories, based on
# http://ismail.badawi.io/blog/2017/03/28/automatic-directory-creation-in-make/
.SECONDEXPANSION:

.PRECIOUS: $(OBJDIR)/%/ $(VERI_OBJDIR)/%/.

$(OBJDIR)/. $(BINDIR)/. $(VERI_OBJDIR)/.:
	mkdir -p $@

$(OBJDIR)/%/. $(BINDIR)/%/. $(VERI_OBJDIR)/%/.:
	mkdir -p $@

#*************************************************************#
# CFLAGS, ETC
#

INCLUDE = -I $(SRCDIR) -I $(SRCDIR)/platform_$(PLATFORM)

DEFAULT_CFLAGS += -D_GNU_SOURCE -ggdb3 -Wall -pthread -Wfatal-errors -Werror
DEFAULT_CFLAGS += -msse4.2 -mpopcnt -DXXH_STATIC_LINKING_ONLY -fPIC -Wno-unused-but-set-variable
#DEFAULT_CFLAGS += -fsanitize=memory -fsanitize-memory-track-origins
#DEFAULT_CFLAGS += -fsanitize=address
#DEFAULT_CFLAGS += -fsanitize=integer
DEFAULT_CFLAGS += $(LIBCONFIG_CFLAGS)


CFLAGS += $(DEFAULT_CFLAGS) -Ofast -flto -march=native
DEFAULT_LDFLAGS = -ggdb3 -pthread
LDFLAGS = $(DEFAULT_LDFLAGS) -Ofast -flto
LIBS = -lm -lpthread -laio -lxxhash


#*********************************************************#
# Targets to track whether we have a release or debug build
#

all: $(BINDIR)/splinterdb.so $(BINDIR)/driver_test $(BINDIR)/veri_driver_test

release: .release all
	rm -f .debug
	rm -f .debug-log

debug: CFLAGS = -g -DSPLINTER_DEBUG $(DEFAULT_CFLAGS)
debug: LDFLAGS = -g $(DEFAULT_LDFLAGS)
debug: .debug all
	rm -f .release
	rm -f .debug-log

debug-log: CFLAGS = -g -DDEBUG -DCC_LOG $(DEFAULT_CFLAGS)
debug-log: LDFLAGS = -g $(DEFAULT_LDFLAGS)
debug-log: .debug-log all
	rm -f .release
	rm -f .debug

.release:
	$(MAKE) clean
	touch .release

.debug:
	$(MAKE) clean
	touch .debug

.debug-log:
	$(MAKE) clean
	touch .debug-log


#*************************************************************#
# RECIPES
#

$(BINDIR)/driver_test : $(TESTOBJ) $(BINDIR)/splinterdb.so | $$(@D)/.
	$(LD) $(LDFLAGS) -o $@ $^ $(LIBS)

$(BINDIR)/veri_driver_test : $(VERI_TESTOBJ) $(BINDIR)/veri_splinterdb.so | $$(@D)/.
	clang++-13 $(LDFLAGS) -o $@ $^ $(LIBS)

$(BINDIR)/splinterdb.so : $(OBJ) | $$(@D)/.
	$(LD) $(LDFLAGS) -shared -o $@ $^ $(LIBS)

$(BINDIR)/veri_splinterdb.so : $(VERI_OBJ) | $$(@D)/.
	$(LD) $(LDFLAGS) -shared -o $@ $^ $(LIBS)

DEPFLAGS = -MMD -MT $@ -MP -MF $(OBJDIR)/$*.d
VERI_DEPFLAGS = -MMD -MT $@ -MP -MF $(VERI_OBJDIR)/$*.d
CPP_DEPFLAGS = -MMD -MT $@ -MP -MF $*.d

COMPILE.c = $(CC) $(DEPFLAGS) $(CFLAGS) $(INCLUDE) $(TARGET_ARCH) -c
VERI_COMPILE.c = $(CC) $(VERI_DEPFLAGS) $(CFLAGS) $(INCLUDE) $(TARGET_ARCH) -c
VERI_COMPILE.cpp = clang++-13 $(CPP_DEPFLAGS) $(CFLAGS) $(INCLUDE) $(TARGET_ARCH) -c -std=c++17

$(VERI_OBJDIR)/src/verified-clockcache.o: src/verified-clockcache.cpp | $$(@D)/.
	$(VERI_COMPILE.cpp) $< -o $@ -DVERI_CLOCKCACHE

$(VERI_OBJDIR)/src/veri/Application.i.o: src/veri/Application.i.cpp | $$(@D)/.
	$(VERI_COMPILE.cpp) $< -o $@ -DVERI_CLOCKCACHE

$(VERI_OBJDIR)/%.o: %.c | $$(@D)/.
	$(VERI_COMPILE.c) $< -o $@ -DVERI_CLOCKCACHE

$(OBJDIR)/%.o: %.c | $$(@D)/.
	$(COMPILE.c) $< -o $@

-include $(SRC:%.c=$(OBJDIR)/%.d) $(TESTSRC:%.c=$(OBJDIR)/%.d) $(SRC:%.c=$(VERI_OBJDIR)/%.d) $(TESTSRC:%.c=$(VERI_OBJDIR)/%.d) $(CPPSRC:%.cpp=$(VERI_OBJDIR)/%.d)

#*************************************************************#

.PHONY : clean tags
clean :
	rm -rf $(OBJDIR)/*
	rm -rf $(VERI_OBJDIR)/*
	rm -f $(BINDIR)/*

tags:
	ctags -R src


#*************************************************************#
# Testing
#

.PHONY: test install

test: $(BINDIR)/driver_test
	./test.sh

INSTALL_PATH ?= /usr/local

install: $(BINDIR)/splinterdb.so
	mkdir -p $(INSTALL_PATH)/include/splinterdb $(INSTALL_PATH)/lib
	cp $(BINDIR)/splinterdb.so $(INSTALL_PATH)/lib/libsplinterdb.so
	cp $(SRCDIR)/data.h $(SRCDIR)/platform_public.h $(SRCDIR)/kvstore.h $(SRCDIR)/kvstore_basic.h $(INSTALL_PATH)/include/splinterdb/
