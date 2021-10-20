# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := Makefile.coq Makefile.test-suite.coq test-suite \
				clean cleanall distclean
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile Make Make.test-suite

.DEFAULT_GOAL := invoke-coqmakefile

ifneq "$(TEST_SKIP_BUILD)" ""
TEST_DEP :=
LIBRARY_PATH :=
else
TEST_DEP := invoke-coqmakefile
LIBRARY_PATH := -R theories mathcomp.algebra_tactics
endif

COQMAKEFILE       = $(COQBIN)coq_makefile
COQMAKE           = $(MAKE) --no-print-directory -f Makefile.coq
COQMAKE_TESTSUITE = $(MAKE) --no-print-directory -f Makefile.test-suite.coq

Makefile.coq: Makefile Make
	$(COQMAKEFILE) -f Make -o Makefile.coq

Makefile.test-suite.coq: Makefile Make.test-suite
	$(COQMAKEFILE) -f Make.test-suite $(LIBRARY_PATH) -o Makefile.test-suite.coq

invoke-coqmakefile: Makefile.coq
	$(COQMAKE) $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

test-suite: Makefile.test-suite.coq invoke-coqmakefile
	$(COQMAKE_TESTSUITE)

clean::
	@if [ -f Makefile.coq ]; then $(COQMAKE) clean; fi
	@if [ -f Makefile.test-suite.coq ]; then $(COQMAKE_TESTSUITE) clean; fi

cleanall::
	@if [ -f Makefile.coq ]; then $(COQMAKE) cleanall; fi
	@if [ -f Makefile.test-suite.coq ]; then $(COQMAKE_TESTSUITE) cleanall; fi

distclean:: cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -f Makefile.test-suite.coq Makefile.test-suite.coq.conf

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
