/-
# Window/gap NECESSARY compatibility for an arbitrary expression anchor

Companion to `audits/AUDIT-EXPR-ANCHOR-TRAJECTORY-2026-10-06.md` §4. ADDITIVE.

This ports `BF4WilsonAllNomeWindowGapCompatibility` from the padded plaquette
trajectory `Y_j` to any `ExprAnchorTrajectory`. It reuses that file's moment-only
core by import (`window_gap_compat`, `side_rate_of_contraction_power`,
`side_rate_le_c0`, `OrbitContraction`).

`ExprPathOrbitContraction tr r`: at every scale, the anchor orbit contracts, i.e.
`B(T y, T y) ≤ r_j² B(y, y)` for `y = T^k Y_j`. This is a hypothesis (the gap
branch) and is not proved for any anchor.

For `j ≥ 2`, `ExprShiftedWindowSurvival tr θ` together with
`ExprShiftedNondegenerate tr fl` and `ExprPathOrbitContraction tr r` force:
* `θ ≤ (r_j²)^(side_j/4)` (`= r_j^(side_j/2)`; the path window has no parity loss);
* `θ · side_j (1 - r_j) ≤ 2(1-θ)` when `0 ≤ r_j ≤ 1`;
* `side_j (1 - r_j) ≤ c0` for any `c0` with `2(1-θ) ≤ θ c0` (least `C(θ) = 2(1-θ)/θ`).

`expr_windowSurvival_forces_rate_c0_hvar_hray` gives the same with the nondegeneracy
supplied by H-var + H-ray. Via `toExprTrajectory` it specializes to the existing
`path_windowSurvival_forces_rate_c0` (`path_windowSurvival_forces_rate_c0_via_expr`).

HONEST SCOPE. This is a NECESSARY compatibility condition between the nontriviality
branch (window survival) and the gap branch (an orbit contraction `r_j < 1`). Both
can hold only if `side_j (1-r_j) = O(1)`. It proves NEITHER branch: window
survival, H-var/H-ray (for non-plaquette expressions) and every contraction stay
OPEN. No gap and no nontriviality follow.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeWindowGapCompatibility
import YMGap.Continuum.BF4WilsonAllNomeExprAnchorRegression

namespace YMGap.Continuum.BF4WilsonAllNomeExprWindowGapCompatibility

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (response_le_of_le)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (DyadicSmoothedTrajectory)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor (PathShiftedNondegenerate)
open YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival (PathShiftedWindowSurvival)
open YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate
  (PathFacesPadded paddedNondegFloor paddedNondegFloor_pos)
open YMGap.Continuum.BF4WilsonAllNomeWindowGapCompatibility
  (OrbitContraction window_gap_compat side_rate_of_contraction_power side_rate_le_c0
   PathOrbitContraction path_windowSurvival_forces_rate_c0)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorRegression

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

private theorem ew_side_quarter (j : Nat) (hj : 2 ≤ j) : side j = 2*(2*(side j/4)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i+2 := ⟨j-2, by omega⟩
  simp only [side, Nat.pow_succ]
  omega

/-- A contraction `r_j` on the orbit of the expression anchor `Y_j` at every scale
(hypothesis; the gap branch). -/
def ExprPathOrbitContraction (tr : ExprAnchorTrajectory) (r : Nat → Q') : Prop :=
  ∀ j, OrbitContraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (tr.state j) (r j)

/-- **Exponent.** For `j ≥ 2`: `θ ≤ (r_j²)^(side_j/4)`. NECESSARY condition only. -/
theorem expr_windowSurvival_contraction_exponent (tr : ExprAnchorTrajectory) (theta : Q')
    (r fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hw : ExprShiftedWindowSurvival tr theta) (Hnd : ExprShiftedNondegenerate tr fl)
    (Hc : ExprPathOrbitContraction tr r) (j : Nat) (hj : 2 ≤ j) :
    theta ≤ (r j * r j)^(side j / 4) := by
  have hq := ew_side_quarter j hj
  have hnd : RCle (Rq (fl j)) (tr.response j (side j / 2)) :=
    RCle_trans (Hnd j) (response_le_of_le (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (tr.state j) (Nat.div_le_self (side j) 2))
  have h := window_gap_compat (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (tr.state j) (r j) theta (fl j) (hfl j) (side j / 2) (side j) (by omega) (Hc j) hnd
    (Hw j (by omega))
  rwa [show (side j + 1)/2 - (side j/2 + 1)/2 = side j / 4 by omega] at h

/-- **Rate, cleared form.** For `j ≥ 2` and `0 ≤ r_j ≤ 1`:
`θ · side_j (1 - r_j) ≤ 2(1 - θ)`. NECESSARY condition only. -/
theorem expr_windowSurvival_forces_rate (tr : ExprAnchorTrajectory) (theta : Q')
    (r fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hw : ExprShiftedWindowSurvival tr theta) (Hnd : ExprShiftedNondegenerate tr fl)
    (Hc : ExprPathOrbitContraction tr r) (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (j : Nat) (hj : 2 ≤ j) :
    theta * (Q'.ofNat (side j) * (1 + -r j)) ≤ (1 + -theta) * Q'.ofNat 2 :=
  side_rate_of_contraction_power theta (r j) (side j / 4) (side j) (ew_side_quarter j hj)
    (hr0 j) (hr1 j) (expr_windowSurvival_contraction_exponent tr theta r fl hfl Hw Hnd Hc j hj)

/-- **Rate, `C(θ)` form.** With `0 < θ` and `2(1-θ) ≤ θ c0`:
`side_j (1 - r_j) ≤ c0` for every `j ≥ 2`. NECESSARY condition only. -/
theorem expr_windowSurvival_forces_rate_c0 (tr : ExprAnchorTrajectory) (theta c0 : Q')
    (r fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j) (ht0 : (0 : Q') < theta)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0)
    (Hw : ExprShiftedWindowSurvival tr theta) (Hnd : ExprShiftedNondegenerate tr fl)
    (Hc : ExprPathOrbitContraction tr r) (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (j : Nat) (hj : 2 ≤ j) :
    Q'.ofNat (side j) * (1 + -r j) ≤ c0 :=
  side_rate_le_c0 theta (r j) c0 (side j / 4) (side j) (ew_side_quarter j hj) (hr0 j) (hr1 j)
    ht0 (expr_windowSurvival_contraction_exponent tr theta r fl hfl Hw Hnd Hc j hj) hc0

/-- Same, with the nondegeneracy supplied by H-var + H-ray (floor
`ρ_j^(2M_j+side_j) v_j`). -/
theorem expr_windowSurvival_forces_rate_c0_hvar_hray (tr : ExprAnchorTrajectory)
    (theta c0 : Q') (r v rho : Nat → Q') (ht0 : (0 : Q') < theta)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0)
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) (Hw : ExprShiftedWindowSurvival tr theta)
    (Hc : ExprPathOrbitContraction tr r) (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (j : Nat) (hj : 2 ≤ j) :
    Q'.ofNat (side j) * (1 + -r j) ≤ c0 :=
  expr_windowSurvival_forces_rate_c0 tr theta c0 r (exprNondegFloor tr v rho)
    (exprNondegFloor_pos tr v rho Hv Hr) ht0 hc0 Hw
    (exprShiftedNondegenerate_of_hvar_hray tr v rho Hv Hr) Hc hr0 hr1 j hj

/-! ## Specialization to plaquette trajectories -/

theorem toExpr_orbitContraction_iff (tr : DyadicSmoothedTrajectory) (r : Nat → Q') :
    ExprPathOrbitContraction (toExprTrajectory tr) r ↔ PathOrbitContraction tr r := Iff.rfl

/-- The existing `path_windowSurvival_forces_rate_c0`, reproved through the
expression layer. -/
theorem path_windowSurvival_forces_rate_c0_via_expr (tr : DyadicSmoothedTrajectory)
    (theta c0 : Q') (r fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j) (ht0 : (0 : Q') < theta)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0)
    (Hw : PathShiftedWindowSurvival tr theta) (Hnd : PathShiftedNondegenerate tr fl)
    (Hc : PathOrbitContraction tr r) (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (j : Nat) (hj : 2 ≤ j) :
    Q'.ofNat (side j) * (1 + -r j) ≤ c0 :=
  expr_windowSurvival_forces_rate_c0 (toExprTrajectory tr) theta c0 r fl hfl ht0 hc0
    ((toExpr_window_iff tr theta).mpr Hw) ((toExpr_nondeg_iff tr fl).mpr Hnd)
    ((toExpr_orbitContraction_iff tr r).mpr Hc) hr0 hr1 j hj

/-- On a PADDED plaquette trajectory the nondegeneracy input is discharged
(H-var/H-ray from the plaquette floors): window survival + orbit contraction alone
force `side_j (1 - r_j) ≤ c0`. -/
theorem padded_windowSurvival_forces_rate_c0 (tr : DyadicSmoothedTrajectory)
    (theta c0 : Q') (r : Nat → Q') (ht0 : (0 : Q') < theta)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hpad : PathFacesPadded tr)
    (Hw : PathShiftedWindowSurvival tr theta) (Hc : PathOrbitContraction tr r)
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1) (j : Nat) (hj : 2 ≤ j) :
    Q'.ofNat (side j) * (1 + -r j) ≤ c0 :=
  expr_windowSurvival_forces_rate_c0_hvar_hray (toExprTrajectory tr) theta c0 r
    (paddedVar tr) (paddedRho tr) ht0 hc0 (toExpr_hvar tr) (toExpr_hray tr hpad)
    ((toExpr_window_iff tr theta).mpr Hw) ((toExpr_orbitContraction_iff tr r).mpr Hc)
    hr0 hr1 j hj

#print axioms ExprPathOrbitContraction
#print axioms expr_windowSurvival_contraction_exponent
#print axioms expr_windowSurvival_forces_rate
#print axioms expr_windowSurvival_forces_rate_c0
#print axioms expr_windowSurvival_forces_rate_c0_hvar_hray
#print axioms toExpr_orbitContraction_iff
#print axioms path_windowSurvival_forces_rate_c0_via_expr
#print axioms padded_windowSurvival_forces_rate_c0

end YMGap.Continuum.BF4WilsonAllNomeExprWindowGapCompatibility
