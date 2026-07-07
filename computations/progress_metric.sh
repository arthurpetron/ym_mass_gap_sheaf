#!/usr/bin/env bash
# Forward-progress metric for the YM mass-gap solve.
# Purpose: detect mathematical-theory LOOPS (re-deriving the same irreducible
# obligation) vs genuine forward progress (discharging or strictly reducing it).
#
# Run from repo root:  bash computations/progress_metric.sh
#
# Three counters + a status ladder. The ONLY true-north is D (discharged
# critical-path obligations); the solve is done when the goal obligation is
# discharged and the frontier guard BREAKS.

set -uo pipefail
cd "$(dirname "$0")/../lean" || exit 1

echo "=================================================================="
echo " YM MASS-GAP FORWARD-PROGRESS METRIC   ($(git -C .. rev-parse --short HEAD 2>/dev/null))"
echo "=================================================================="

# --- C: CONFIRMATION / LOOP counter ------------------------------------------
# Every  `X := SingleStepDefectBound`  alias is an attack that re-derived the
# SAME core obligation. Growth of C with no change in F/D = a LOOP.
# Robust: count `def X : Type := [...]SingleStepDefectBound` alias definitions
# (continuation-aware; ignores prose/comments that merely mention the string).
C=$(awk '/^[[:space:]]*def[[:space:]]+[A-Za-z0-9_]+[[:space:]]*:[[:space:]]*Type/{
           if($0 ~ /SingleStepDefectBound/){c++; next}
           getline nxt; if(nxt ~ /SingleStepDefectBound/) c++
         } END{print c+0}' YMGap/Continuum/*.lean)
echo
echo "C  (confirmation aliases 'def X := SingleStepDefectBound'; LOOP counter): $C"
echo "     ^ each is a distinct module that reduced to singleStep."
echo "     Adding to C without moving F or D = a mathematical loop."

# --- F: FRONTIER size --------------------------------------------------------
# Distinct OPEN obligations that are NOT provably equivalent to singleStep.
# These are the genuine, strictly-weaker sub-obligations still to prove.
# Maintained by hand in the ledger (a type that is `:= SingleStepDefectBound`
# does NOT count — it is the same obligation). Update FRONTIER below as the
# decomposition changes.
# ADJUDICATED (commit after 72f59ef): the 3-piece "decomposition" was FAKE.
#   channel_feedback = DEFEQ alias of singleStep (Iff.rfl)
#   real_defect_identification = LOGICALLY EQUAL (bi-implication proved)
#   uniform_in_m = strictly weaker BUT proved NOT core-shrinking (afr-only; singleStep
#                  varies with the free margin tm) -> closing it does not reduce the core.
# => the core is ATOMIC. Honest F = 1.
FRONTIER=(
  "singleStep_ATOMIC   # realδ_k ≤ 6(1−w_k)² over the full RG recursion on trueMargin ; NO known strictly-weaker reduction below it"
)
echo
echo "F  (distinct open frontier obligations, NOT singleStep-aliases): ${#FRONTIER[@]}"
for f in "${FRONTIER[@]}"; do echo "     - $f"; done

# --- D: DISCHARGED critical-path obligations (TRUE NORTH) ---------------------
# An obligation is DISCHARGED only if a load-bearing type is newly inhabited
# axiom-clean AND the frontier guard reacts (drops below 5). Until then D=0.
GUARD=$(lake build YMGapGuard 2>&1 | grep -oE "[0-9]+ Clay-frontier types" | grep -oE "^[0-9]+" || echo "?")
echo
echo "D  (critical-path obligations DISCHARGED; guard must break)  : $([ "$GUARD" = 5 ] && echo 0 || echo ">=1  (guard=$GUARD, CHECK!)")"
echo "     frontier-guard uninhabited types = $GUARD   (5 = nothing discharged; <5 = something closed)"

# --- STATUS LADDER for the top obligation (singleStep) ------------------------
echo
echo "singleStep status ladder (the whole continuum gap is conditional on it):"
echo "   [x] 0 conjectured"
echo "   [x] 1 numerically VERIFIED TRUE           (m-fold concentration, safety factor 45)"
echo "   [x] 2 DECOMPOSED into sub-obligations      (${#FRONTIER[@]} pieces; verify each is strictly weaker!)"
echo "   [ ] 3 sub-obligations discharged           (0 / ${#FRONTIER[@]} proved so far)"
echo "   [ ] 4 fully proved -> guard breaks -> SOLVE"

echo
echo "=================================================================="
echo " ANTI-LOOP RULE (enforce before spawning any attack):"
echo "   Predict the attack's honest outcome.  If it is \"produces another"
echo "   := SingleStepDefectBound alias\" / \"reduces to singleStep\", it is a"
echo "   LOOP (C++ only) -> DO NOT SPAWN.  Only spawn attacks that would"
echo "   (a) DISCHARGE a frontier obligation, or"
echo "   (b) DECOMPOSE one into provably-strictly-weaker independent pieces, or"
echo "   (c) REFUTE a genuinely-live candidate route."
echo "   'The honest expectation is another confirmation' == the loop signal."
echo "=================================================================="
