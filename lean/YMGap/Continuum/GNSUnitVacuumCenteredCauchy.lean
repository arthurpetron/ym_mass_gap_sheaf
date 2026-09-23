/-
# Constructive centering of GNS Cauchy representatives

Orthogonal projection off a unit vacuum preserves the supplied squared-distance
Cauchy modulus. If its scalar vacuum pairing tends to zero, the centered
sequence represents the same completed vector. The null modulus is returned
as Type-level data, using the existing choice-free recovery theorem.
-/

import YMGap.Continuum.GNSUnitVacuumProjection
import YMGap.Continuum.GNSNullModulusRecovery
import YMGap.Constructive.CRealMulMono

namespace YMGap.Continuum.GNSUnitVacuumCenteredCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSUnitVacuumProjection
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSNullModulusRecovery
open YMGap.Continuum.OSReconstructionProgress

/-- Centering retains the original computable Cauchy modulus, without any
inverse or lower coercivity assumption on another quadratic form. -/
def centeredCauchy (D : GNSData) (vacuum : D.V)
    (hunit : (D.B vacuum vacuum).eqv 1) (X : CauchyGNS D) : CauchyGNS D where
  seq := fun n => center D vacuum (X.seq n)
  modulus := X.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _ (center_distSq_le D vacuum hunit (X.seq p) (X.seq q))
      (X.isCauchy epsilon hepsilon p q hp hq)

private theorem eventual_abs_bound (r : Nat → Q')
    (h : CReal.ConvergesTo (fun n => CReal.ofQ' (r n)) CReal.czero)
    (delta : Q') (hdelta : (0 : Q') < delta) :
    ∃ N : Nat, ∀ n, N ≤ n → Q'.abs (r n) ≤ delta := by
  obtain ⟨N, hN⟩ := h delta hdelta
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨A, hA⟩ := hN n hn
  have hb := hA A (Nat.le_refl A)
  change r n ≤ 0 + delta ∧ 0 ≤ r n + delta at hb
  exact Q'.abs_le_of_bounds (Q'.neg_le_of_zero_le_add hb.2)
    (by simpa only [Q'.zero_add'] using hb.1)

private theorem eventual_square_bound (r : Nat → Q')
    (h : CReal.ConvergesTo (fun n => CReal.ofQ' (r n)) CReal.czero)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    ∃ N : Nat, ∀ n, N ≤ n → r n * r n ≤ epsilon := by
  have bound (delta : Q') (hd : (0 : Q') < delta)
      (hd1 : delta ≤ 1) (hde : delta ≤ epsilon) :
      ∃ N : Nat, ∀ n, N ≤ n → r n * r n ≤ epsilon := by
    obtain ⟨N, hN⟩ := eventual_abs_bound r h delta hd
    refine ⟨N, fun n hn => ?_⟩
    have hsquare : Q'.abs (r n) * Q'.abs (r n) ≤ delta * delta :=
      Q'.mul_le_mul_of_nonneg (hN n hn) (hN n hn)
        (Q'.le_of_lt hd) (Q'.abs_nonneg (r n))
    have hdSquare : delta * delta ≤ delta :=
      le_of_le_eqv
        (Q'.mul_le_mul_of_nonneg_left delta 1 delta hd1 (Q'.le_of_lt hd))
        (Q'.mul_one_eqv delta)
    exact Q'.le_trans' _ _ _
      (le_of_eqv_le (Q'.eqv_symm (Q'.abs_mul_self_eqv (r n))) hsquare)
      (Q'.le_trans' _ _ _ hdSquare hde)
  rcases Int.le_total (epsilon.num * ((1 : Q').den : Int))
      ((1 : Q').num * (epsilon.den : Int)) with he1 | h1e
  · exact bound epsilon hepsilon he1 (Q'.le_refl' epsilon)
  · exact bound 1 (by decide) (Q'.le_refl' 1) h1e

private theorem centeredCauchy_null (D : GNSData) (vacuum : D.V)
    (hunit : (D.B vacuum vacuum).eqv 1) (X : CauchyGNS D)
    (hmean : CReal.ConvergesTo
      (fun n => CReal.ofQ' (D.B (X.seq n) vacuum)) CReal.czero) :
    CauchyNull D X (centeredCauchy D vacuum hunit X) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := eventual_square_bound
    (fun n => D.B (X.seq n) vacuum) hmean epsilon hepsilon
  exact ⟨N, fun n hn => le_of_eqv_le
    (self_center_distSq_eqv D vacuum hunit (X.seq n)) (hN n hn)⟩

/-- Actual Type-level null-closeness data. The computable rate is obtained
from the original and centered Cauchy moduli, not selected from `hmean`. -/
def centeredNullModulus (D : GNSData) (vacuum : D.V)
    (hunit : (D.B vacuum vacuum).eqv 1) (X : CauchyGNS D)
    (hmean : CReal.ConvergesTo
      (fun n => CReal.ofQ' (D.B (X.seq n) vacuum)) CReal.czero) :
    CauchyNullModulus D X (centeredCauchy D vacuum hunit X) :=
  recoverNullModulus (centeredCauchy_null D vacuum hunit X hmean)

/-- The recovered null rate is explicitly the original Cauchy rate at one
tenth of the requested squared-distance tolerance. -/
theorem centeredNullModulus_modulus (D : GNSData) (vacuum : D.V)
    (hunit : (D.B vacuum vacuum).eqv 1) (X : CauchyGNS D)
    (hmean : CReal.ConvergesTo
      (fun n => CReal.ofQ' (D.B (X.seq n) vacuum)) CReal.czero)
    (epsilon : Q') :
    (centeredNullModulus D vacuum hunit X hmean).modulus epsilon =
      X.modulus (nullTolerance epsilon) := by
  change max (X.modulus (nullTolerance epsilon))
    (X.modulus (nullTolerance epsilon)) = _
  exact Nat.max_self _

#print axioms centeredCauchy
#print axioms centeredNullModulus
#print axioms centeredNullModulus_modulus

end YMGap.Continuum.GNSUnitVacuumCenteredCauchy
