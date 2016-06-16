
CC=gcc -E -C
CCOPTS=-nostdinc -I .
NOTCC=../notcc.exe
FUN=../FunPointers.exe

CFILES=$(wildcard *.c)
FILES=$(CFILES:%.c=%)
TESTFILES=$(FILES:%=%.test)
ORACLEFILES=$(FILES:%=%.oracle.sh)
.PRECIOUS: %.i %.cil %.test

all: results

%.i: %.c
	@$(CC) $(CCOPTS) $< >$@

%.cil: %.i
	@$(NOTCC) -o $@ $<

%.test: %.cil
	@$(FUN) $< >$@ 2>/dev/null

results: $(TESTFILES) $(ORACLEFILES) $(FUN)
	@red=`tput setaf 1`; \
	green=`tput setaf 2`; \
	reset=`tput sgr0`; \
	rm -f $@; \
	for i in $(TESTFILES); \
	do \
	  name=`basename $$i .test`; \
	  oracle="$$name".oracle.sh; \
	  r=$${red}"FAIL"$${reset}; \
	  s="FAIL"; \
	  ./"$$oracle" $$i && r=$${green}"OK"$${reset} && s="OK"; \
	  echo "$$name": $$r; \
	  echo "$$name": $$s >>$@; \
	done

clean:
	rm -f *.i *.cil

veryclean: clean
	rm -f *.test results

