# CertiFlash.
#
# The mechanized Rocq development lives in formal-proof/; real-system/ holds the
# DaisyPlus OpenSSD demonstration and needs no build. This file forwards every
# target to formal-proof/, so `make verify` and `make coqchk` work from the
# repository root as well as from inside formal-proof/.

.PHONY: all verify coqchk clean stats report help
all verify coqchk clean stats report help:
	$(MAKE) -C formal-proof $@
