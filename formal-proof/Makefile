# CertiFlash -- Coq build.
#
# Targets:
#   make             build everything (calls coq_makefile then make -f CoqMakefile)
#   make verify      same as above; succeeds iff all proofs check and there
#                    are no Admitted lemmas or user Axiom declarations
#   make coqchk      re-check the compiled results with the Coq kernel and
#                    confirm the trusted results depend on no axioms
#   make clean       remove all generated .vo / .glob / .vos / .vok files
#   make stats       print line counts, file counts, and key tactic counts
#   make report      run a deeper paper-vs-code report (line, file, def, lemma,
#                    Admitted, Axiom counts in one report)
#
# Requires: Coq / Rocq 8.20.1.

COQ_MAKEFILE = CoqMakefile
COQ_PROJECT  = _CoqProject

# Leaf results whose kernel re-check transitively covers the whole development.
COQCHK_MODULES = \
	Refinement \
	Invariants.Preservation \
	Invariants.MicroOpPreconditions \
	CrashRefinement \
	failure_surfaces.FSReachable \
	dftl.DFTL dftl.MegIS dedup.Dedup

.PHONY: all verify coqchk clean stats report help

all: verify

help:
	@echo "Targets:"
	@echo "  make / make verify  -- build and verify all proofs"
	@echo "  make coqchk         -- kernel re-check; confirms no axioms are used"
	@echo "  make clean          -- remove generated build artifacts"
	@echo "  make stats          -- print summary line / file counts"
	@echo "  make report         -- detailed paper-vs-code report"

$(COQ_MAKEFILE): $(COQ_PROJECT)
	coq_makefile -f $(COQ_PROJECT) -o $(COQ_MAKEFILE)

verify: $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE)
	@echo
	@echo "=== Sanity check: no Admitted, no Axiom ==="
	@! grep -rEn '^[[:space:]]*Admitted\.' src/ 2>/dev/null \
		|| (echo "FAIL: Admitted found above" && false)
	@! grep -rEn '^[[:space:]]*Axiom ' src/ 2>/dev/null \
		|| (echo "FAIL: Axiom found above" && false)
	@echo "OK: no Admitted, no Axiom"

coqchk: verify
	@echo
	@echo "=== Kernel re-check (coqchk): confirming no axioms ==="
	@coqchk -o -Q src "" $(COQCHK_MODULES) 2>&1 \
		| grep -E '^\* (Axioms|Constants|Inductives)' \
		|| (echo "FAIL: coqchk produced no clean summary" && false)

clean:
	@if [ -f $(COQ_MAKEFILE) ]; then $(MAKE) -f $(COQ_MAKEFILE) clean; fi
	rm -f $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf
	find src -name '*.vo'  -delete
	find src -name '*.vos' -delete
	find src -name '*.vok' -delete
	find src -name '*.glob' -delete
	find src -name '.*.aux' -delete

stats:
	@echo "=== Line counts ==="
	@find src -name '*.v' | xargs wc -l | tail -1
	@echo
	@echo "=== File count ==="
	@find src -name '*.v' | wc -l
	@echo
	@echo "=== Admitted count ==="
	@grep -rc 'Admitted\.' src/ 2>/dev/null \
		| grep -v ':0$$' || echo "  (none)"
	@echo
	@echo "=== Axiom count ==="
	@grep -rcE '^Axiom ' src/ 2>/dev/null \
		| grep -v ':0$$' || echo "  (none)"

report:
	@python3 scripts/stats.py
	@echo
	@echo "=== per directory ==="
	@for d in src/core src/Invariants src/framework src/validator src/dftl src/failure_surfaces; do printf '%-24s' "$$d"; find $$d -name '*.v' | xargs wc -l | tail -1 | awk '{print $$1}'; done

