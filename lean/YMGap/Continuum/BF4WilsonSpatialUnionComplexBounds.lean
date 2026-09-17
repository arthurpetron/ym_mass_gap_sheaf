/-
# The original vacuum and bounds on the direct Wilson complexification

Complex orthogonality to the embedded original unit is exactly real
orthogonality of BOTH components. Adding the two existing real estimates
therefore proves the SAME rate on the entire complex vacuum complement,
not merely on the embedded real subspace. The time and multiplier bounds
also retain their original constants. No new analytic input is supplied.

These are fixed-spacing, small-nome SU(2) statements about the actual
componentwise maps. They do not prove one-step form positivity, a full
complex Hilbert interface, a continuous-time generator, changing-spacing
survival or continuum QFT. In particular, q is a dimensionless two-step
rate, not a calibrated physical Hamiltonian mass.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionComplexification
import YMGap.Continuum.BF4WilsonSpatialUnionRelaxation

namespace YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator
open YMGap.Continuum.BF4WilsonSpatialUnionComplexification
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation (norm_decay)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_add_zero rc_sub_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "VC" => ComplexCarrier hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "I" => inner hw0 hw1 hsmall hd hs
local notation "E" => embedReal hw0 hw1 hsmall hd hs
local notation "CT" => complexTime hw0 hw1 hsmall hd hs
local notation "CM" => complexMultiply hw0 hw1 hsmall hd hs

/-- The original vacuum, embedded by the proved isometric real inclusion. -/
def complexUnit : VC := E U

local notation "CU" => complexUnit hw0 hw1 hsmall hd hs

theorem complexUnit_fixed (n : Nat) : CT n CU = CU := by
  unfold complexUnit
  rw [complexTime_embedReal, completedUnit_fixed]

theorem inner_unit_left (x : VC) : I CU x = (B x.1 U,B x.2 U) := by
  simp only [inner,complexUnit,embedReal,completedInner_zero_left,rc_add_zero,rc_sub_zero]
  rw [completedInner_symm hw0 hw1 hsmall hd hs U x.1,
    completedInner_symm hw0 hw1 hsmall hd hs U x.2]

/-- No imaginary component of the vacuum-orthogonality condition is dropped. -/
theorem complex_orthogonal_iff (x : VC) :
    I CU x = (RCzero,RCzero) ↔ B x.1 U = RCzero ∧ B x.2 U = RCzero := by
  rw [inner_unit_left]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩
  · rintro ⟨h1,h2⟩
    exact Prod.ext h1 h2

theorem inner_time_sum (m n : Nat) (x y : VC) :
    I (CT m x) (CT n y) = I x (CT (m+n) y) := by
  simp only [inner,complexTime,completedInner_time_sum]

/-- Exact complex-valued half-time norm identity, including zero imaginary part. -/
theorem inner_even_diagonal (n : Nat) (x : VC) : I x (CT (2*n) x) = I (CT n x) (CT n x) := by
  simpa only [Nat.two_mul] using (inner_time_sum hw0 hw1 hsmall hd hs n n x x).symm

theorem inner_even_nonnegative (n : Nat) (x : VC) :
    RCnonneg (I x (CT (2*n) x)).1 ∧ (I x (CT (2*n) x)).2 = RCzero := by
  rw [inner_even_diagonal]
  exact ⟨inner_nonnegative hw0 hw1 hsmall hd hs _,
    congrArg Prod.snd (inner_diagonal hw0 hw1 hsmall hd hs _)⟩

theorem complexTime_norm_contraction (n : Nat) (x : VC) :
    RCle (I (CT n x) (CT n x)).1 (I x x).1 :=
  RCadd_le_add (completedInner_time_contraction hw0 hw1 hsmall hd hs n x.1)
    (completedInner_time_contraction hw0 hw1 hsmall hd hs n x.2)

/-- EVERY complex vector orthogonal to the SAME unit retains the original q^n. -/
theorem complexTime_norm_decay (x : VC) (hx : I CU x = (RCzero,RCzero)) (n : Nat) :
    RCle (I (CT n x) (CT n x)).1 (RCscale ((twoStepRate w hd)^n) (I x x).1) := by
  obtain ⟨h1,h2⟩ := (complex_orthogonal_iff hw0 hw1 hsmall hd hs x).mp hx
  have h := RCadd_le_add (norm_decay hw0 hw1 hsmall hd hs x.1 h1 n)
    (norm_decay hw0 hw1 hsmall hd hs x.2 h2 n)
  rw [← RCscale_RCadd] at h
  exact h

theorem complex_even_form_decay (x : VC) (hx : I CU x = (RCzero,RCzero)) (n : Nat) :
    RCle (I x (CT (2*n) x)).1 (RCscale ((twoStepRate w hd)^n) (I x x).1) := by
  rw [inner_even_diagonal]
  exact complexTime_norm_decay hw0 hw1 hsmall hd hs x hx n

private theorem rc_mul_eq_scale (c : Q') (a : RC) :
    RCmul (Quotient.mk crealSetoid (ofQ' c)) a = RCscale c a := by
  refine Quotient.inductionOn a ?_
  exact fun _ => rfl

/-- Actual Wilson operators keep their original squared-norm cap on both components. -/
theorem complexMultiply_norm_bound {base : Nat} (L : SourceLoop base) (spin : Nat) (x : VC) :
    RCle (I (CM L spin x) (CM L spin x)).1 (RCscale (characterBound spin) (I x x).1) := by
  have h := RCadd_le_add (completedInner_multiplier_bound hw0 hw1 hsmall hd hs L spin x.1)
    (completedInner_multiplier_bound hw0 hw1 hsmall hd hs L spin x.2)
  simp only [rc_mul_eq_scale] at h
  rw [← RCscale_RCadd] at h
  exact h

end YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.complexUnit
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.complexUnit_fixed
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.inner_unit_left
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.complex_orthogonal_iff
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.inner_time_sum
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.inner_even_diagonal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.inner_even_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.complexTime_norm_contraction
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.complexTime_norm_decay
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.complex_even_form_decay
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionComplexBounds.complexMultiply_norm_bound
