OBJS = scheme.cmx parser.cmx lexer.cmx emit.cmx \
					ast.cmx builtins.cmx s2ml.cmx
CAMLP = camlp5r
PP = -pp $(CAMLP)
INCLUDES =
OCAMLOPT = ocamlopt $(INCLUDES)
OCAMLYACC = menhir
OCAMLLEX = ocamllex
LIBS = nums.cmxa
YFLAGS =

simple:
	$(OCAMLOPT) $(PP) -c scheme.ml
	$(OCAMLYACC) parser.mly
	$(OCAMLOPT) -c parser.mli parser.ml
	$(OCAMLLEX) lexer.mll
	$(OCAMLOPT) -c lexer.ml
	$(OCAMLOPT) $(PP) -c emit.ml
	$(OCAMLOPT) $(PP) -c ast.ml
	$(OCAMLOPT) $(PP) -c builtins.ml
	$(OCAMLOPT) $(PP) -c s2ml.ml
	$(OCAMLOPT) $(LIBS) $(OBJS) -o s2ml.opt

s2ml.opt: $(OBJSOPT)
	$(OCAMLOPT) $(LIBSOPT) $(OBJSOPT) -o s2ml.opt

lexer.cmx: lexer.ml parser.cmx
	$(OCAMLOPT) -c lexer.ml

lexer.ml: lexer.mll
	ocamllex lexer.mll

parser.cmx: parser.ml parser.mli scheme.cmx
	$(OCAMLOPT) -c parser.mli parser.ml

parser.ml parser.mli: parser.mly
	menhir $(YFLAGS) parser.mly

ast.cmx: ast.ml scheme.cmx emit.cmx
	$(OCAMLOPT) $(PP) -c ast.ml

emit.cmx: emit.ml
	$(OCAMLOPT) $(PP) -c emit.ml

scheme.cmx: scheme.ml
	$(OCAMLOPT) $(PP) -c scheme.ml

builtins.cmx: builtins.ml ast.cmx emit.cmx
	$(OCAMLOPT) $(PP) -c builtins.ml

s2ml.cmx: s2ml.ml ast.cmx emit.cmx builtins.cmx
	$(OCAMLOPT) $(PP) -c s2ml.ml

.PHONY: all clean

all: s2ml.opt

clean:
	rm -f *.cm[iox]
	rm -f *.o
	rm -f parser.ml parser.mli
	rm -f lexer.ml

cleanall: clean
	rm -f s2ml.opt

# Pretty printing convenience targets
# 'r' stands for Revised syntax
# 'o' stands for Normal syntax
# so 'pro' means pretty print something
# written in the revised syntax in the
# normal syntax, etc.
%.pro.ml: %.ml
	camlp5r pr_o.cmo pr_op.cmo $<

%.pro.mli: %.mli
	camlp5r pr_o.cmo pr_op.cmo $<

%.por.ml: %.ml
	camlp5o pr_r.cmo pr_rp.cmo $<

%.por.mli: %.mli
	camlp5o pr_r.cmo pr_rp.cmo $<

%.prr.ml: %.ml
	camlp5r pr_r.cmo pr_rp.cmo $<

%.prr.mli: %.mli
	camlp5r pr_r.cmo pr_rp.cmo $<

%.poo.ml: %.ml
	camlp5o pr_o.cmo pr_op.cmo $<

%.poo.mli: %.mli
	camlp5o pr_o.cmo pr_op.cmo $<

scheme_read.cmx: scheme_read.ml lexer.cmx parser.cmx
	$(OCAMLOPT) $(PP) -c scheme_read.ml

%.scm: s2ml.opt scheme.cmx scheme_read.cmx
	./s2ml.opt < $@ | camlp5r pr_r.cmo pr_rp.cmo -impl - > `basename $@ .scm`.ml
	$(OCAMLOPT) $(PP) $(LIBS) scheme.cmx parser.cmx lexer.cmx scheme_read.cmx `basename $@ .scm`.ml -o `basename $@ .scm`
