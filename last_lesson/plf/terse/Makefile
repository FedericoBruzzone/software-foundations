COQMFFLAGS := -Q . PLF  

ALLVFILES := Maps.v Imp.v Preface.v Equiv.v HoareAM.v Vcg.v SmallstepAM.v TypesAM.v Stlc.v StlcPropAM.v 

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
