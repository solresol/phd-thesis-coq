FPSERIES_SOURCE := vendor/fpseries
FPSERIES_BUILD := _build/fpseries
FPSERIES_PATCH := patches/fpseries-coq816.patch
FPSERIES_STAMP := $(FPSERIES_BUILD)/.coq816-built
FPSERIES_MODULES := natbar auxresults directed invlim padic

all: $(FPSERIES_STAMP) Makefile.coq
	$(MAKE) -f Makefile.coq all

$(FPSERIES_STAMP): $(FPSERIES_PATCH) $(FPSERIES_SOURCE)/theories/padic.v
	mkdir -p _build
	rsync -a --delete $(FPSERIES_SOURCE)/ $(FPSERIES_BUILD)/
	patch -d $(FPSERIES_BUILD) -p1 < $(abspath $(FPSERIES_PATCH))
	cd $(FPSERIES_BUILD) && \
	  for module in $(FPSERIES_MODULES); do \
	    coqc -R theories Combi theories/$$module.v || exit 1; \
	  done
	touch $(FPSERIES_STAMP)

install: $(FPSERIES_STAMP) Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -rf $(FPSERIES_BUILD)

Makefile.coq: _CoqProject $(FPSERIES_STAMP)
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all install uninstall clean
