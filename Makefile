# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := Makefile.coq Makefile.test-suite.coq
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile Make Make.test-suite

.DEFAULT_GOAL := invoke-coqmakefile

Makefile.coq: Makefile Make
	$(COQBIN)coq_makefile -f Make -o Makefile.coq

Makefile.test-suite.coq: Makefile Make.test-suite
	$(COQBIN)coq_makefile -f Make.test-suite -o Makefile.test-suite.coq

invoke-coqmakefile: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

test-suite: Makefile.test-suite.coq
	$(MAKE) --no-print-directory -f Makefile.test-suite.coq

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
