/-
# Multiplication and inverse-time congruence for the original ambient mean

Two signed-time expressions are tested against every signed-time multiplier,
using equivalence of the original CReal expectations. Finite polynomial
identities survive the full action and reciprocal partition and therefore
hold in this relation. Inverse time and reflection pull the arbitrary test
back to the same carrier, proving congruence without a new decay assumption.

This is a fixed-base ambient observable relation, not the reflected OS null
relation or equality of arbitrary completed states. Extension across bases
needs its own proof because the larger base has additional test observables.
The canonical scalar and continuum obligations remain unchanged.
-/

import YMGap.Continuum.BF4WilsonSignedTimeExpectation

namespace YMGap.Continuum.BF4WilsonSignedTimeContext

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression
open YMGap.Continuum.BF4WilsonSignedTimeExpectation
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (placed_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent chartIds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (heatProduct_supported)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix (prefix_mul_one)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The literal full-window polynomial in the original padded chart. -/
def insertion {base : Nat} (H r t : Nat) (e : Expression base) : RatPoly :=
  chartInsertion r H t (window H e)

private theorem insertion_supported {base : Nat} (H r t : Nat) (e : Expression base) :
    SupportedQuaternionBlocks (B (chartExtent base r H t)) (insertion H r t e) :=
  placed_supported (chartExtent base r H t) (paddedWidth base r+1+t)
    (centeredExpression r (window H e))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0 < base)

local notation "E" => mean hw0 hw1 hsmall hd hs hb

private theorem chart_padded_congr (H r stage t : Nat) (e f : Expression base)
    (hp : PaddedPolynomialCoeffEqv (B (chartExtent base r H t))
      (insertion H r t e) (insertion H r t f)) :
    Q'.eqv (chartScalar hw0 hw1 H (window H e) r stage t)
      (chartScalar hw0 hw1 H (window H f) r stage t) := by
  let action := polynomialProduct
    (faceHeatPolynomial w (headCutoff w+stage) (chartExtent base r H t))
    (chartIds base r H t)
  have ha : SupportedQuaternionBlocks (B (chartExtent base r H t)) action :=
    heatProduct_supported w (headCutoff w+stage) (chartExtent base r H t) (chartIds base r H t)
  have h := (hp.mul (PaddedPolynomialCoeffEqv.refl _ action)).haar
    (supported_polyMul (insertion_supported H r t e) ha)
    (supported_polyMul (insertion_supported H r t f) ha)
  exact Q'.mul_eqv_congr_right _ _ _ h

/-- Every supplied identity is checked inside the same full selected action;
the computed common support radius is used only for the limit comparison. -/
theorem mean_of_polynomial_eq (e f : Expression base)
    (hp : ∀ H r t, PaddedPolynomialCoeffEqv (B (chartExtent base r H t))
      (insertion H r t e) (insertion H r t f)) : Equiv (E e) (E f) := by
  let H := max (radius e) (radius f)
  have he := within_mono (Nat.le_max_left (radius e) (radius f)) e (within_radius e)
  have hf := within_mono (Nat.le_max_right (radius e) (radius f)) f (within_radius f)
  exact (mean_at hw0 hw1 hsmall hd hs hb H e he).trans
    ((Equiv_of_limit_of_equal
      (fun n => SumOfSquares.Equiv_of_approx_eqv
        (fun _ => chart_padded_congr hw0 hw1 H n n n e f (hp H n n)))
      (spatial_diagonal_converges hw0 hw1 H (window H e) (window_within H e he) hsmall hd hs hb)
      (spatial_diagonal_converges hw0 hw1 H (window H f) (window_within H f hf) hsmall hd hs hb)).trans
      (mean_at hw0 hw1 hsmall hd hs hb H f hf).symm)

/-- Ordinary ambient testing, not the OS norm-null relation. -/
def ContextEq (e f : Expression base) : Prop :=
  ∀ test : Expression base, Equiv (E (.mul e test)) (E (.mul f test))

local notation "Ceq" => ContextEq hw0 hw1 hsmall hd hs hb

theorem context_refl (e : Expression base) : Ceq e e := fun _ => Equiv.refl _
theorem context_symm {e f : Expression base} (h : Ceq e f) : Ceq f e := fun t => (h t).symm
theorem context_trans {e f g : Expression base} (h : Ceq e f) (k : Ceq f g) : Ceq e g :=
  fun t => (h t).trans (k t)

/-- The arbitrary multiplier is retained before the finite identity is integrated. -/
theorem context_of_polynomial_eq (e f : Expression base)
    (hp : ∀ H r t, PaddedPolynomialCoeffEqv (B (chartExtent base r H t))
      (insertion H r t e) (insertion H r t f)) : Ceq e f := by
  intro test
  apply mean_of_polynomial_eq hw0 hw1 hsmall hd hs hb
  intro H r t
  exact (hp H r t).mul (PaddedPolynomialCoeffEqv.refl _ (insertion H r t test))

theorem context_mul_comm (e f : Expression base) : Ceq (.mul e f) (.mul f e) := by
  apply context_of_polynomial_eq hw0 hw1 hsmall hd hs hb
  intro H r t
  exact .of_coeff (RatPolyCoeffEqv.mul_comm _ _)

theorem context_mul_assoc (e f g : Expression base) : Ceq (.mul (.mul e f) g) (.mul e (.mul f g)) := by
  apply context_of_polynomial_eq hw0 hw1 hsmall hd hs hb
  intro H r t
  exact .of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)

theorem context_mul_one (e : Expression base) : Ceq (.mul e .one) e := by
  apply context_of_polynomial_eq hw0 hw1 hsmall hd hs hb
  intro H r t
  exact .of_prefix (prefix_mul_one _ _)

theorem mean_mul_one (e : Expression base) : Equiv (E (.mul e .one)) (E e) := by
  apply mean_of_polynomial_eq hw0 hw1 hsmall hd hs hb
  intro H r t
  exact .of_prefix (prefix_mul_one _ _)

theorem context_mean {e f : Expression base} (h : Ceq e f) : Equiv (E e) (E f) :=
  (mean_mul_one hw0 hw1 hsmall hd hs hb e).symm.trans
    ((h .one).trans (mean_mul_one hw0 hw1 hsmall hd hs hb f))

theorem context_add_comm (e f : Expression base) : Ceq (.add e f) (.add f e) := by
  apply context_of_polynomial_eq hw0 hw1 hsmall hd hs hb
  intro H r t
  exact .of_coeff (RatPolyCoeffEqv.add_comm _ _)

theorem context_add_assoc (e f g : Expression base) : Ceq (.add (.add e f) g) (.add e (.add f g)) := by
  apply context_of_polynomial_eq hw0 hw1 hsmall hd hs hb
  intro H r t
  exact .of_coeff (RatPolyCoeffEqv.add_assoc _ _ _)

theorem context_mul_add (e f g : Expression base) :
    Ceq (.mul e (.add f g)) (.add (.mul e f) (.mul e g)) := by
  apply context_of_polynomial_eq hw0 hw1 hsmall hd hs hb
  intro H r t
  exact .of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _)

theorem context_smul_mul (c : Q') (e f : Expression base) :
    Ceq (.mul (.smul c e) f) (.smul c (.mul e f)) := by
  apply context_of_polynomial_eq hw0 hw1 hsmall hd hs hb
  intro H r t
  exact .of_coeff (RatPolyCoeffEqv.polyMul_smul_left c _ _)

private theorem mean_mul_assoc (e f g : Expression base) :
    Equiv (E (.mul (.mul e f) g)) (E (.mul e (.mul f g))) :=
  context_mean hw0 hw1 hsmall hd hs hb (context_mul_assoc hw0 hw1 hsmall hd hs hb e f g)

private theorem mean_mul_comm (e f : Expression base) : Equiv (E (.mul e f)) (E (.mul f e)) :=
  context_mean hw0 hw1 hsmall hd hs hb (context_mul_comm hw0 hw1 hsmall hd hs hb e f)

/-- Product compatibility uses associativity under the mean, not raw syntax equality. -/
theorem context_mul_right {e f : Expression base} (h : Ceq e f) (g : Expression base) :
    Ceq (.mul e g) (.mul f g) := fun t =>
  (mean_mul_assoc hw0 hw1 hsmall hd hs hb e g t).trans
    ((h (.mul g t)).trans (mean_mul_assoc hw0 hw1 hsmall hd hs hb f g t).symm)

theorem context_mul_left {e f : Expression base} (h : Ceq e f) (g : Expression base) :
    Ceq (.mul g e) (.mul g f) :=
  context_trans hw0 hw1 hsmall hd hs hb (context_mul_comm hw0 hw1 hsmall hd hs hb g e)
    (context_trans hw0 hw1 hsmall hd hs hb (context_mul_right hw0 hw1 hsmall hd hs hb h g)
      (context_mul_comm hw0 hw1 hsmall hd hs hb f g))

theorem context_mul {a b c d : Expression base} (h : Ceq a b) (k : Ceq c d) :
    Ceq (.mul a c) (.mul b d) :=
  context_trans hw0 hw1 hsmall hd hs hb (context_mul_right hw0 hw1 hsmall hd hs hb h c)
    (context_mul_left hw0 hw1 hsmall hd hs hb k b)

private theorem mean_add_mul (e f g : Expression base) :
    Equiv (E (.mul (.add e f) g)) (add (E (.mul e g)) (E (.mul f g))) :=
  (mean_mul_comm hw0 hw1 hsmall hd hs hb (.add e f) g).trans
    ((context_mean hw0 hw1 hsmall hd hs hb (context_mul_add hw0 hw1 hsmall hd hs hb g e f)).trans
      ((mean_add hw0 hw1 hsmall hd hs hb (.mul g e) (.mul g f)).trans
        (Equiv_add (mean_mul_comm hw0 hw1 hsmall hd hs hb g e)
          (mean_mul_comm hw0 hw1 hsmall hd hs hb g f))))

theorem context_add {a b c d : Expression base} (h : Ceq a b) (k : Ceq c d) :
    Ceq (.add a c) (.add b d) := fun t =>
  (mean_add_mul hw0 hw1 hsmall hd hs hb a c t).trans
    ((Equiv_add (h t) (k t)).trans (mean_add_mul hw0 hw1 hsmall hd hs hb b d t).symm)

private theorem mean_smul_mul (s : Q') (a t : Expression base) :
    Equiv (E (.mul (.smul s a) t)) (mul (ofQ' s) (E (.mul a t))) :=
  (context_mean hw0 hw1 hsmall hd hs hb (context_smul_mul hw0 hw1 hsmall hd hs hb s a t)).trans
    (mean_smul hw0 hw1 hsmall hd hs hb s (.mul a t))

theorem context_smul (s : Q') {a b : Expression base} (h : Ceq a b) : Ceq (.smul s a) (.smul s b) :=
  fun t => (mean_smul_mul hw0 hw1 hsmall hd hs hb s a t).trans
    ((Pivot2.mul_congr (Equiv.refl (ofQ' s)) (h t)).trans
      (mean_smul_mul hw0 hw1 hsmall hd hs hb s b t).symm)

/-- Pull the arbitrary ambient test backward; one-sided time alone cannot justify this. -/
theorem context_forward (n : Nat) {a b : Expression base} (h : Ceq a b) :
    Ceq (forward n a) (forward n b) := by
  intro t
  have ha := mean_forward hw0 hw1 hsmall hd hs hb n (.mul a (backward n t))
  have hb' := mean_forward hw0 hw1 hsmall hd hs hb n (.mul b (backward n t))
  simp only [forward, forward_backward] at ha hb'
  exact ha.trans ((h (backward n t)).trans hb'.symm)

theorem context_backward (n : Nat) {a b : Expression base} (h : Ceq a b) :
    Ceq (backward n a) (backward n b) := by
  intro t
  have ha := mean_backward hw0 hw1 hsmall hd hs hb n (.mul a (forward n t))
  have hb' := mean_backward hw0 hw1 hsmall hd hs hb n (.mul b (forward n t))
  simp only [backward, backward_forward] at ha hb'
  exact ha.trans ((h (forward n t)).trans hb'.symm)

theorem context_reflect {a b : Expression base} (h : Ceq a b) : Ceq (reflect a) (reflect b) := by
  intro t
  have ha := mean_reflect hw0 hw1 hsmall hd hs hb (.mul a (reflect t))
  have hb' := mean_reflect hw0 hw1 hsmall hd hs hb (.mul b (reflect t))
  simp only [reflect, reflect_reflect] at ha hb'
  exact ha.trans ((h (reflect t)).trans hb'.symm)

end YMGap.Continuum.BF4WilsonSignedTimeContext

#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.insertion
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.mean_of_polynomial_eq
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.ContextEq
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_refl
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_symm
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_trans
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_of_polynomial_eq
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_mul_comm
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_mul_assoc
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_mul_one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.mean_mul_one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_mean
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_add_comm
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_add_assoc
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_mul_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_smul_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_mul_right
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_mul_left
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContext.context_reflect
