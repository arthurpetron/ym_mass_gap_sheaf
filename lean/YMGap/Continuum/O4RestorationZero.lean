/-
The rotation-breaking coefficient converges to zero, not merely to some limit.

`O4RestorationAF.RotationRestored` was defined as the Cauchy property of the
coefficient schedule.  Cauchy convergence alone does not express symmetry
restoration: a constant nonzero schedule is Cauchy.  The actual
`ScalingDimensionDecay` hypothesis is strong enough to prove the required
zero-limit statement.  This file records both facts constructively:

* a closed counterexample to "Cauchy implies vanishing";
* geometric decay gives an explicit eventual bound by every positive rational;
* the lifted rational sequence converges to `CReal.czero`; and
* the previously constructed `breakCoeffLimit` is equivalent to zero.
-/

import YMGap.Continuum.O4RestorationAF
import YMGap.Continuum.RegularLinearGeometricSymmetry

namespace YMGap.Continuum.O4RestorationZero

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.O4RestorationAF
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.RegularLinearGeometricSymmetry

/-! ## 1. Cauchy convergence is not vanishing -/

def QSeqCauchy (S : Nat → Q') : Prop :=
  ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
    S m ≤ S n + ε ∧ S n ≤ S m + ε

def QSeqVanishes (S : Nat → Q') : Prop :=
  ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ k : Nat, N ≤ k → S k ≤ ε

theorem constant_one_cauchy : QSeqCauchy (fun _ => (1 : Q')) := by
  intro ε hε
  have hnn : (0 : Q') ≤ ε := Q'.le_of_lt hε
  exact ⟨0, fun _ _ _ _ => ⟨
    Q'.add_le_self_of_nonneg 1 ε hnn,
    Q'.add_le_self_of_nonneg 1 ε hnn⟩⟩

theorem constant_one_not_vanishes :
    ¬ QSeqVanishes (fun _ => (1 : Q')) := by
  intro h
  obtain ⟨N, hN⟩ := h half (CReal.pos_of_num_pos (by decide))
  exact (by decide : ¬ ((1 : Q') ≤ half)) (hN N (Nat.le_refl N))

/-- Kernel-checked fence: replacing "the anisotropy tends to zero" by bare
Cauchy convergence is invalid. -/
theorem cauchy_does_not_imply_vanishing :
    ∃ S : Nat → Q', QSeqCauchy S ∧ ¬ QSeqVanishes S :=
  ⟨fun _ => (1 : Q'), constant_one_cauchy, constant_one_not_vanishes⟩

/-- The earlier `RotationRestored` predicate is definitionally only the Cauchy
property of the coefficient schedule. -/
theorem rotationRestored_iff_qseqCauchy (D : ScalingDimensionDecay) :
    RotationRestored D ↔ QSeqCauchy (breakCoeff D) := Iff.rfl

/-! ## 2. The decay hypothesis proves the sharp zero statement -/

def RotationBreakingVanishes (D : ScalingDimensionDecay) : Prop :=
  QSeqVanishes (breakCoeff D)

theorem breakCoeff_vanishes (D : ScalingDimensionDecay) :
    RotationBreakingVanishes D := by
  intro ε hε
  let C := breakCoeff D 0
  refine ⟨geoOuterModulus C ε, fun k hk => ?_⟩
  have hC : (0 : Q') ≤ C := breakCoeff_nonneg D 0
  have henv : breakCoeff D k ≤ geoIncr C k := breakCoeff_le_geo D k
  have hincr : geoIncr C k ≤ geoTail C k := geoIncr_le_geoTail C hC k
  have htail : geoTail C k ≤ ε :=
    geoTail_le_of_modulus C hC ε hε k hk
  exact Q'.le_trans' _ _ _ henv (Q'.le_trans' _ _ _ hincr htail)

/-! ## 3. Genuine convergence to zero -/

theorem breakCoeff_converges_czero (D : ScalingDimensionDecay) :
    CReal.ConvergesTo (fun k => CReal.ofQ' (breakCoeff D k)) CReal.czero := by
  intro ε hε
  obtain ⟨N, hN⟩ := breakCoeff_vanishes D ε hε
  refine ⟨N, fun k hk => ⟨0, fun n _ => ?_⟩⟩
  change breakCoeff D k ≤ (0 : Q') + ε ∧
    (0 : Q') ≤ breakCoeff D k + ε
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (hN k hk)
      (Q'.ge_of_eqv (QPoly.q_zero_add_eqv ε))
  · exact Q'.zero_le_add _ _ (breakCoeff_nonneg D k) (Q'.le_of_lt hε)

/-- The `CReal` produced earlier from the coefficient's Cauchy data is exactly
zero.  This is the corrected analytic conclusion needed for restoration. -/
theorem breakCoeffLimit_equiv_czero (D : ScalingDimensionDecay) :
    CReal.Equiv (breakCoeffLimit D) CReal.czero := by
  let S : Nat → CReal := fun k => CReal.ofQ' (breakCoeff D k)
  have hself : CReal.ConvergesTo S (breakCoeffLimit D) := by
    simpa [S] using CReal.convergesTo_self (breakCoeffLimit D)
  have hzero : CReal.ConvergesTo S CReal.czero := by
    exact breakCoeff_converges_czero D
  exact CReal.Equiv_of_limit_of_equal
    (aSeq := S) (bSeq := S)
    (fun _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))
    hself hzero

#print axioms QSeqCauchy
#print axioms QSeqVanishes
#print axioms constant_one_cauchy
#print axioms constant_one_not_vanishes
#print axioms cauchy_does_not_imply_vanishing
#print axioms rotationRestored_iff_qseqCauchy
#print axioms RotationBreakingVanishes
#print axioms breakCoeff_vanishes
#print axioms breakCoeff_converges_czero
#print axioms breakCoeffLimit_equiv_czero

end YMGap.Continuum.O4RestorationZero
