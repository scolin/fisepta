
CC=gcc -E -C
CCOPTS=-nostdinc -I .
NOTCC=../notcc.exe
FUN=../FunPointers.exe

FILES=variadic
TESTFILES=$(FILES:%=%.test)
ORACLEFILES=$(FILES:%=%.oracle.sh)
.PRECIOUS: %.i %.cil %.test

%.i: %.c
	$(CC) $(CCOPTS) $< >$@

%.cil: %.i
	$(NOTCC) -o $@ $<

%.test: %.cil
	$(FUN) $< >$@

results: $(TESTFILES) $(ORACLEFILES)
	for i in $(TESTFILES); \
	do \
	  name=`basename $$i .test`; \
	  oracle="$$name".oracle.sh; \
	  r="FAIL"; \
	  ./"$$oracle" $$i && r="OK"; \
	  echo `basename $$i .res`: $$r | tee $@; \
	done

clean:
	rm -f *.i *.cil

veryclean: clean
	rm -f *.test results

