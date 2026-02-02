all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean

Makefile.rocq:
	rocq makefile -f _RocqProject -o Makefile.rocq

autosubst:
	cd theories/autosubst ; \
	$(MAKE) -f Makefile

clean-assumptions: all
	rm theories/Assumptions.vo

force _RocqProject Makefile: ;

%: Makefile.rocq force
	@+$(MAKE) -f Makefile.rocq $@

.PHONY: all clean clean-assumptions autosubst
