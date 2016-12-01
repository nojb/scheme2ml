OCAMLBUILD = ocamlbuild -classic-display

all:
	$(OCAMLBUILD) s2ml.native

.PHONY: clean all

clean:
	$(OCAMLBUILD) -clean

%.scm: s2ml.native
	./s2ml.native < $@ > `basename $@ .scm`.ml
	$(OCAMLBUILD) `basename $@ .scm`.native
