# Makefile originally taken from coq-club
# https://blog.zhen-zhang.com/2016/09/19/coq-dev.html

#Lib/%: Lib/Makefile.coq phony
#	+cd Lib && make -f Makefile.coq $@ 

%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq #Lib/Makefile.coq
#	+cd Lib && make -f Makefile.coq all
	+make -f Makefile.coq all

clean: Makefile.coq #Lib/Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
#	+cd Lib && make -f Makefile.coq clean
#	rm -f Lib/Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject ./CategoricalSemantics/*.v -o Makefile.coq

Lib/Makefile.coq: _CoqProject Makefile
	cd Lib && coq_makefile -f _CoqProject *.v -o Makefile.coq

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony