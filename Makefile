.PHONY: test lint typecheck figures svg-to-pdf paper clean help \
        lean-build lean-audit lean-audit-strict lean-audit-update lean-rubric \
        lean-frontier-guard lean-statement-guard lean-import-guard lean-affected \
        frontier-status frontier-dag-check

# Cap Lake's build parallelism. Lake defaults to one worker per logical core
# (16 here); the generated exact-rational certificate modules routinely peak
# at 3-4 GB during kernel checking and the heaviest (the Base semantic
# bridge) near 15 GB, so an uncapped rebuild wave exhausts a 64 GB machine.
# This Lake version has no `--jobs` flag; LEAN_NUM_THREADS is the control
# (verified: it caps concurrent lean workers). One worker is the safe default;
# two or three require deliberate operator judgment and three is the hard host
# ceiling. The per-process ceiling remains mandatory in lean/lakefile.toml.
LEAN_JOBS ?= 1
LEAN_BASE ?= HEAD
LEAN_AUDIT_LOG ?=
LEAN_AUDIT_SOURCE = $(if $(strip $(LEAN_AUDIT_LOG)),--from-file "$(LEAN_AUDIT_LOG)",)

ifneq ($(words $(LEAN_JOBS)),1)
$(error LEAN_JOBS must be exactly one of 1, 2, or 3; got '$(LEAN_JOBS)')
endif
ifeq ($(filter 1 2 3,$(LEAN_JOBS)),)
$(error LEAN_JOBS must be 1, 2, or 3; got '$(LEAN_JOBS)')
endif

help:
	@echo "Targets:"
	@echo "  test                Run the pytest suite."
	@echo "  lint                Run ruff and mypy (strict)."
	@echo "  typecheck           Run mypy only."
	@echo "  figures             Regenerate plots in visualizations/ (no-op until Phase 1)."
	@echo "  paper               Build formal/main.tex to PDF via latexmk."
	@echo "  lean-build          HIGH-LOAD: full all-module build; explicit host approval required."
	@echo "  lean-audit          Check the axiom gate; builds unless LEAN_AUDIT_LOG=<log>."
	@echo "  lean-audit-strict   Same, plus fail on new/missing theorems."
	@echo "  lean-audit-update   Regenerate the baseline manifest from the current build."
	@echo "  lean-rubric         Compile-check the Clay scorecard against the pinned external rubric."
	@echo "  lean-frontier-guard Fail if a Clay-frontier type (Tier0Scorecard/ClayTarget/UniformSpacingFloor) is inhabited."
	@echo "  lean-statement-guard Fail if a Clay-frontier STATEMENT (type/field signature or shared param) is weakened."
	@echo "  lean-import-guard   Fail on missing imports or unreviewed modules outside the YMGap semantic root."
	@echo "  lean-affected       List reverse-dependency build targets (optionally LEAN_BASE=<git-ref>)."
	@echo "  frontier-status     Regenerate docs/frontier-status.md (partial-close + open-field ledger)."
	@echo "  frontier-dag-check  Fail if a new *Scorecard/*Frontier/*Target enumeration lacks a FrontierDAG bridge."
	@echo "  clean               Remove Python, mypy, ruff, pytest, and LaTeX build artifacts."

test:
	pytest

lint:
	ruff check .
	mypy

typecheck:
	mypy

figures:
	@echo "No figures yet; populated as Phase 1 milestones close."

# Convert every SVG under visualizations/ to a sibling PDF using rsvg-convert.
# pdflatex cannot embed SVGs directly, so the manuscript references the
# generated PDFs.  Idempotent: skips up-to-date PDFs.
svg-to-pdf:
	@command -v rsvg-convert >/dev/null || { echo "error: rsvg-convert not on PATH (brew install librsvg)"; exit 1; }
	@find visualizations -name '*.svg' | while read svg; do \
	    pdf="$${svg%.svg}.pdf"; \
	    if [ ! -f "$$pdf" ] || [ "$$svg" -nt "$$pdf" ]; then \
	        echo "  svg -> pdf: $$svg"; \
	        rsvg-convert -f pdf -o "$$pdf" "$$svg"; \
	    fi; \
	done

paper: svg-to-pdf
	cd formal && TEXINPUTS="../docs/arthur_tex_style/:../docs/arthur_tex_style/tex/:../docs/arthur_tex_style/assets/:$$TEXINPUTS" latexmk -pdf main.tex

lean-build:
	cd lean && LEAN_NUM_THREADS=$(LEAN_JOBS) lake build

lean-audit:
	LEAN_NUM_THREADS=$(LEAN_JOBS) python3 scripts/lean_axiom_audit.py $(LEAN_AUDIT_SOURCE)

lean-audit-strict:
	LEAN_NUM_THREADS=$(LEAN_JOBS) python3 scripts/lean_axiom_audit.py --strict $(LEAN_AUDIT_SOURCE)

lean-audit-update:
	LEAN_NUM_THREADS=$(LEAN_JOBS) python3 scripts/lean_axiom_audit.py --update $(LEAN_AUDIT_SOURCE)

# Static source/import-graph checks. These never invoke Lean or Lake.
lean-import-guard:
	python3 scripts/lean_import_guard.py

lean-affected:
	python3 scripts/lean_import_guard.py --affected $(LEAN_BASE)

# Frontier uninhabitedness guard. Builds YMGapGuard, which reflects over the
# YMGap.* environment and FAILS if any Clay-frontier type (Tier0Scorecard,
# UniformSpacingFloor, ClayTarget) has an UNCONDITIONAL inhabitant. This catches
# the exact failure mode AGENTS.md exists to prevent — an agent "accidentally"
# closing the Clay problem with a vacuous/circular term that still passes the
# axiom gate — applied at the frontier rather than the leaves. Independent of
# AXIOM_AUDIT.md, so `make lean-audit-update` cannot silence it. See
# lean/YMGapGuard.lean (`frontierAllowlist` is the human-reviewed escape hatch).
lean-frontier-guard:
	cd lean && LEAN_NUM_THREADS=$(LEAN_JOBS) lake build YMGapGuard

# Frontier STATEMENT-drift guard. Builds YMGapStatementGuard, which computes a
# stable structural hash of each Clay-frontier type's STATEMENT (type signature +
# field structure) and of the shared parameter defs they are built from, and
# FAILS the build if any hash drifts from the pinned literal. Catches silent
# WEAKENING of ClayTargetPinned / ClayTarget / FrontierDAG / Tier0Scorecard /
# UniformSpacingFloor (or a shared param such as RubricO4Restoration := True) —
# the exact attack the inhabitation guard (lean-frontier-guard) cannot see.
# Independent of AXIOM_AUDIT.md. See lean/YMGapStatementGuard.lean
# (`pinnedFrontierStatements` is the human-reviewed re-pin surface).
lean-statement-guard:
	cd lean && LEAN_NUM_THREADS=$(LEAN_JOBS) lake build YMGapStatementGuard

# Compile-check the Clay scorecard (constructive transcription of the external
# Clay rubric) against its pinned source. Verifies the fixed-spacing rubric
# clauses are genuinely MET (real proof terms typecheck) while the continuum
# clauses stay OPEN (no inhabitant). See lean/YMGap/Rubric/ClayScorecard.lean and
# reference/leanmillennium-pinned/.
lean-rubric:
	@test -f reference/leanmillennium-pinned/Millennium.lean.txt \
	  || { echo "error: pinned rubric source missing (reference/leanmillennium-pinned/)"; exit 1; }
	cd lean && LEAN_NUM_THREADS=$(LEAN_JOBS) lake build YMGap.Rubric.ClayScorecard
	@echo "Clay scorecard compiled: fixed-spacing clauses MET, continuum clauses OPEN (Clay remains open)."

# Regenerate the read-only frontier ledger docs/frontier-status.md: for each of
# the declared Clay-frontier bundles it records the current partial closes (with
# their axiom gate from lean/AXIOM_AUDIT.md) and the residual OPEN fields, parsed
# mechanically from the Lean sources. Edits no Lean source; every bundle stays
# OPEN by design. See scripts/frontier_status.py (--lake to layer a live build
# log over the baseline gates).
frontier-status:
	python3 scripts/frontier_status.py

# Static "no orphan scorecard" guard: fails the build if a new
# *Scorecard/*Frontier/*Target/*DAG enumeration structure carrying OPEN residual
# atoms is added without a bridge relating it to the unified FrontierDAG node (in
# either direction). Grep-only (no lake); complements lean-frontier-guard (which
# is build-time Lean, "no unconditional inhabitant of a frontier TYPE") with a
# static "no new parallel enumeration without a BRIDGE". The single reviewed
# blessing surfaces are frontier_status.FRONTIER / YMGapFrontierGuard.frontierAllowlist
# / frontier_dag_check.SCRIPT_ALLOWLIST. See scripts/frontier_dag_check.py.
frontier-dag-check:
	python3 scripts/frontier_dag_check.py

clean:
	rm -rf .pytest_cache .mypy_cache .ruff_cache build dist *.egg-info
	find . -type d -name "__pycache__" -prune -exec rm -rf {} +
	find . -type f -name "*.pyc" -delete
	-cd formal && latexmk -C >/dev/null 2>&1
