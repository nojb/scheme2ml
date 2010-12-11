OBJSOPT = scheme.cmx parser.cmx lexer.cmx emit.cmx \
					ast.cmx builtins.cmx s2ml.cmx
OBJS = scheme.cmo parser.cmo lexer.cmo emit.cmo \
			 ast.cmo builtins.cmo s2ml.cmo
CAMLP = camlp5r
PP = -pp $(CAMLP)
INCLUDES = -I /usr/local/lib/ocaml
OCAMLOPT = ocamlopt $(INCLUDES)
OCAMLC = ocamlc $(INCLUDES)
LIBS = nums.cma
LIBSOPT = nums.cmxa
YFLAGS =

s2ml.opt: $(OBJSOPT)
	$(OCAMLOPT) $(LIBSOPT) $(OBJSOPT) -o s2ml.opt

s2ml: $(OBJS)
	$(OCAMLC) $(LIBS) $(OBJS) -o s2ml

lexer.cmx: lexer.ml parser.cmx
	$(OCAMLOPT) -c lexer.ml

lexer.cmo: lexer.ml parser.cmo
	$(OCAMLC) -c lexer.ml

lexer.ml: lexer.mll
	ocamllex lexer.mll

parser.cmx: parser.ml parser.mli scheme.cmx
	$(OCAMLOPT) -c parser.mli parser.ml

parser.cmo: parser.ml parser.mli scheme.cmo
	$(OCAMLC) -c parser.mli parser.ml

parser.ml parser.mli: parser.mly
	menhir $(YFLAGS) parser.mly

ast.cmx: ast.ml scheme.cmx emit.cmx
	$(OCAMLOPT) $(PP) -c ast.ml

ast.cmo: ast.ml scheme.cmo emit.cmo
	$(OCAMLC) $(PP) -c ast.ml

emit.cmx: emit.ml
	$(OCAMLOPT) $(PP) -c emit.ml

emit.cmo: emit.ml
	$(OCAMLC) $(PP) -c emit.ml

scheme.cmx: scheme.ml
	$(OCAMLOPT) $(PP) -c scheme.ml

scheme.cmo: scheme.ml
	$(OCAMLC) $(PP) -c scheme.ml

builtins.cmx: builtins.ml ast.cmx emit.cmx
	$(OCAMLOPT) $(PP) -c builtins.ml

builtins.cmo: builtins.ml ast.cmo emit.cmo
	$(OCAMLC) $(PP) -c builtins.ml

s2ml.cmx: s2ml.ml ast.cmx emit.cmx builtins.cmx
	$(OCAMLOPT) $(PP) -c s2ml.ml

s2ml.cmo: s2ml.ml ast.cmo emit.cmo builtins.cmo
	$(OCAMLC) $(PP) -c s2ml.ml

.PHONY: all
.PHONY: clean

all: s2ml s2ml.opt

clean:
	rm -f *.cm[iox]
	rm -f *.o
	rm -f parser.ml parser.mli
	rm -f lexer.ml

cleanall: clean
	rm -f s2ml s2ml.opt

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
	$(OCAMLOPT) $(PP) $(LIBSOPT) scheme.cmx parser.cmx lexer.cmx scheme_read.cmx `basename $@ .scm`.ml -o `basename $@ .scm`
