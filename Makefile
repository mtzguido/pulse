# Pulse's `Makefile`s rely on recent GNU Make's "shortest stem" rule,
# so we need to rule out older `make`s.

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

all: verify

# Find fstar.exe and the fstar.lib OCaml package
ifeq (,$(FSTAR_HOME))
  _check_fstar := $(shell which fstar.exe)
  ifeq ($(.SHELLSTATUS),0)
    _fstar_home := $(realpath $(dir $(_check_fstar))/..)
    ifeq ($(OS),Windows_NT)
      OCAMLPATH := $(shell cygpath -m $(_fstar_home)/lib);$(OCAMLPATH)
    else
      OCAMLPATH := $(_fstar_home)/lib:$(OCAMLPATH)
    endif
  endif
else
  _fstar_home := $(FSTAR_HOME)
  ifeq ($(OS),Windows_NT)
    OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
  else
    OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
  endif
endif
export OCAMLPATH
_check_fstar_lib_package := $(shell env OCAMLPATH="$(OCAMLPATH)" ocamlfind query fstar.lib)
ifneq ($(.SHELLSTATUS),0)
  $(error "Cannot find fstar.lib in $(OCAMLPATH). Please make sure fstar.exe is properly installed and in your PATH or FSTAR_HOME points to its prefix directory or the F* source repository.")
endif

# Define the Pulse root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
ifeq ($(OS),Windows_NT)
  PULSE_HOME := $(shell cygpath -m $(CURDIR))
else
  PULSE_HOME := $(CURDIR)
endif

.PHONY: ocaml
ocaml:
	cd src/ocaml && dune build
	cd src/ocaml && dune install --prefix=$(PULSE_HOME)

.PHONY: verify-pulse
verify-pulse:
	+$(MAKE) -C lib/pulse

.PHONY: verify-pulse-core
verify-pulse-core: 
	+$(MAKE) -C lib/pulse/core pulse_core

.PHONY: verify-pulse-lib
verify-pulse-lib: ocaml verify-pulse verify-pulse-core
	+$(MAKE) -C lib/pulse/lib

.PHONY: verify
verify: verify-pulse-lib

clean: clean_ocaml
	+$(MAKE) -C lib/pulse clean ; true

clean_ocaml:
	cd src/ocaml && { dune uninstall --prefix=$(PULSE_HOME) ; dune clean ; true ; }

.PHONY: test
test: all
	+$(MAKE) -C share/steel

PREFIX ?= /usr/local
ifeq ($(OS),Windows_NT)
  PULSE_INSTALL_PREFIX=$(shell cygpath -m $(PREFIX))
else
  PULSE_INSTALL_PREFIX=$(PREFIX)
endif
export PULSE_INSTALL_PREFIX

INSTALL := $(shell ginstall --version 2>/dev/null | cut -c -8 | head -n 1)
ifdef INSTALL
   INSTALL := ginstall
else
   INSTALL := install
endif
export INSTALL

.PHONY: install install-ocaml install-lib install-include install-share

install-ocaml:
	cd src/ocaml && dune install --prefix=$(PULSE_INSTALL_PREFIX)

install-lib:
	+$(MAKE) -C lib/pulse install

install-share:
	+$(MAKE) -C share/steel install

install: install-ocaml install-lib install-share

.PHONY: pulse2rust
pulse2rust:
	+$(MAKE) -C pulse2rust

boot:
	+$(MAKE) verify-pulse
	+$(MAKE) -C src extract-pulse-plugin
	+$(MAKE) ocaml

ci:
	+$(MAKE) -C src ci
