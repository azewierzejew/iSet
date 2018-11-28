# Executable name
PROG=iSet

# Required objects
CMOS=$(PROG).cmo
CMXS=$(CMOS:.cmo=.cmx)

# Choose target: byte, native, both
all: both
both: $(PROG).byte $(PROG).native
native: $(PROG).native
byte: $(PROG).byte

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLDOC=ocamldoc
INCLUDES=                    # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)       # options for ocamlc
OCAMLOPTFLAGS=$(INCLUDES)    # options for ocamlopt

$(PROG).byte: $(CMOS)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $^

$(PROG).native: $(CMXS)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $^

.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.depend:
	ocamldep *.mli *.ml > $@

doc:
	mkdir -p doc
	$(OCAMLDOC) $(INCLUDES) -html -charset Utf-8 -d doc *.mli *.ml

undoc:
	rm -r doc

depend:
	rm -f .depend
	$(MAKE) .depend

clean:
	rm -f *.cmi *.cmo *.cmx *.o .depend

purge:
	rm -f *.cmi *.cmo *.cmx *.byte *.native *.o .depend

include .depend
