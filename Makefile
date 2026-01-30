all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean

Makefile.rocq:
	rocq makefile -f _CoqProject -o Makefile.rocq

autosubst:
	cd theories/autosubst ; \
	$(MAKE) -f Makefile

clean-assumptions: all
	rm theories/Assumptions.vo

force _CoqProject Makefile: ;

%: Makefile.rocq force
	@+$(MAKE) -f Makefile.rocq $@

.PHONY: all clean clean-assumptions autosubst
