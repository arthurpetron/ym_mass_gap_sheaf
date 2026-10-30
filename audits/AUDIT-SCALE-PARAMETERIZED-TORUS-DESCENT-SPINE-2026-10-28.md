# Audit — Scale-Parameterized 4D Heat-Kernel Torus Family, Matched-Coupling Transfer Bridge & Inter-Scale Schur / Signed-Remainder Descent Spine (2026-10-28)

## Scope & Honest Label
- **Module**: `lean/YMGap/Continuum/ScaleParameterizedTorusDescentSpine.lean` (`YMGap.Continuum.ScaleParameterizedTorusDescentSpine`, 350 lines).
- **Label (corrected 2026-10-29 per YM Bot audit)**: U(1)-true bookkeeping only. **NOT gap evidence and NOT a proof of the 4D Yang–Mills mass gap.** Nothing here is unconditional beyond the items listed as proved below.

## Audit corrections (2026-10-29, YM Bot; independently re-checked)
1. `InterScaleAnchoredDescentPackage` is just `PathShortedGramLossBound` split at `j0` (`interScaleAnchoredDescent_implies_shortedGramLoss` is a two-case split). It is equivalent in content to the r44 interface (`d602fd7f2`) via `θ = 1 - r`, `D = 0`. Confirmed: only the direction package → conjecture is formalized.
2. `InterScaleSchurRemainderStep` is disconnected from `tr.response`; none of its fields enter the package. `interScale_schur_and_signedRemainder_bridge` is a conjunction of three existing facts. Confirmed.
3. `ir_anchor` is ASSUMED. `existingNome_allNome_strongCoupling` gives an upper contraction rate (`timeRate = 1/4`) at the single pilot nome `1/1024`. It is not a lower retention bound on `θ̄_j` at the trajectory nomes `w_j`, so it does not certify the anchor. Confirmed.
4. `ZHKAt_pos` needs the activity-nonnegativity hypothesis `hz`. The only unconditional positivity facts are `ZHKAt_zero_pos` (`S_trunc = 0`) and `ZSpinHKAt_pos` (the spin-sum object `slabParametricKPhysicalPartition`). These have not been proved equal to `ZHKAt` for `S_trunc > 0`. Confirmed.
5. The theorem names `interScale_descent_discharges_conjecture` / `interScale_descent_closes_shifted_anchor` are kept so nothing downstream breaks. They are conditional repackagings, not discharges.

## What Was Proved
1. **Link 1 — Parametric 4D Torus Family `𝒯_j = (2M_j, w_j, S_j)` for all `w_j ∈ (0, 1)`**:
   - `ZHKAt w M S_trunc`, `ZObsHKAt`, `covHKAt`, `EhatHKAt` for arbitrary rational nome `w : Q'`, recovering `ZHK`, `ZObsHK`, `covHK`, `EhatHK` at `w = w0` by `rfl` (`ZHKAt_w0`, `ZObsHKAt_w0`, `covHKAt_w0`, `EhatHKAt_w0`).
   - Positivity for all `w > 0`: `coeffW_pos`, `ZHKAt_zero_pos`, `ZSpinHKAt_pos` (spin-sum object; not identified with `ZHKAt`), `Xi_one_le_of_nonneg`, `ZHKAt_pos` (needs `hz`), and `ZHKAt_w0_pos`.
   - Matched-coupling transfer bridge `TorusSliceTraceIdentityAt w` and `HeatKernelTorusSemigroupBridgeAt w` (`torusSliceTraceIdentityAt_w0`, `schedule_backward_handle_le_forward_handle`, `torusSliceTraceIdentityAt_implies_bridgeAt`, `ehatHKAt_decay_of_torusSliceTraceIdentityAt`).
2. **Link 2 — Inter-Scale `2M_j → M_j` (`j+1 → j`) Schur Pullback & Signed-Remainder Descent**:
   - Dyadic half-side `torusHalfSide j = 2^(j-1)` (`two_mul_torusHalfSide`, `torusHalfSide_succ`, `torusHalfSide_shift`, `torusHalfSide_of_le`).
   - `InterScaleSchurRemainderStep` and `interScale_schur_and_signedRemainder_bridge` (connecting `VariationalLocalizationStep.gluingDefect_nonneg` and Milestone 447's `signedRemainderTelescope`).
   - `interScale_retention_descent_to_irAnchor`, `InterScaleAnchoredDescentPackage`, `interScaleAnchoredDescent_implies_shortedGramLoss`, `interScale_descent_discharges_conjecture`, `interScale_descent_closes_shifted_anchor`, and `afPadded_closed_by_interScale_descent`.

## Verification
- Checked via `LEAN_NUM_THREADS=1 python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 1.5 --check lean/YMGap/Continuum/ScaleParameterizedTorusDescentSpine.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/ScaleParameterizedTorusDescentSpine.olean --check-worker-limit-gib 3.4` (0 errors, 0 warnings).
- Axioms verified via `#print axioms`: all 41 declarations depend only on `⊆ {propext, Quot.sound}`.
