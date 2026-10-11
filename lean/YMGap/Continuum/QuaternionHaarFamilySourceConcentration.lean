/-
# Retained source entropy from its OWN selected first and second moments

Integrate the supporting LOWER tangent of the finite log polynomial against
the actual W*g. Its linear term cancels at m=P(W*g*g)/P(W*g), not at the
unbiased partition. This proves a finite source-concentration estimate without
discarding the negative entropy credit or pulling an interior source outside
the selected projection. No uniform kurtosis, logarithmic passage, completed
response identification, changing-family estimate or physical gap is asserted.
-/

import YMGap.Continuum.RegularizedLogPolynomialLowerTangent
import YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.QuaternionHaarFamilySourceConcentration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_smul)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder
open YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy
open YMGap.Continuum.QuaternionHaarFiniteEntropy (entropyStage entropyStage_eval)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst eval_subst)
open YMGap.Continuum.RegularizedLogPolynomial (partialSum)
open YMGap.Continuum.RegularizedLogPolynomialLowerTangent
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  tc (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem qr (p q : PolyExpr) (h : RingNormaliser.normalize p = RingNormaliser.normalize q)
    (rho : Nat → Q') : RingNormaliser.eval rho p ≈ RingNormaliser.eval rho q :=
  poly_identity_of_normal_eq p q h rho

/-- OWN biased mass at the retained assignment, not P(W). -/
def sourceMass (slots : List Nat) (W g : RatPoly) (qs : Nat → UnitNorm) : Q' :=
  evalRatPoly (environment qs) (familyProject slots (polyMul W g))

/-- SAME density and assignment, with a second occurrence of g retained. -/
def sourceSecond (slots : List Nat) (W g : RatPoly) (qs : Nat → UnitNorm) : Q' :=
  evalRatPoly (environment qs) (familyProject slots (polyMul (polyMul W g) g))

/-- The exact finite source entropy credit, before any normalization. -/
def sourceEntropy (slots : List Nat) (W g : RatPoly) (qs : Nat → UnitNorm)
    (N : Nat) : Q' :=
  evalRatPoly (environment qs) (familyProject slots (polyMul W (entropyStage N g)))

/-- Computed mean under W*g, using its own positive biased mass. -/
def sourceMean (slots : List Nat) (W g : RatPoly) (qs : Nat → UnitNorm)
    (ha : (0 : Q') < sourceMass slots W g qs) : Q' :=
  Q'.divPos (sourceSecond slots W g qs) (sourceMass slots W g qs) ha

theorem sourceMean_pin (slots : List Nat) (W g : RatPoly) (qs : Nat → UnitNorm)
    (ha : (0 : Q') < sourceMass slots W g qs) :
    sourceMean slots W g qs ha * sourceMass slots W g qs ≈ sourceSecond slots W g qs :=
  Q'.divPos_mul_eqv _ _ ha

/-- No exterior-independence assumption: the source stays inside P. -/
theorem sourceSecond_le_mass (slots : List Nat) (W g : RatPoly)
    (hW : ∀ heads : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment heads) W)
    (hg : ∀ heads : Nat → UnitNorm,
      (0 : Q') ≤ evalRatPoly (environment heads) g ∧ evalRatPoly (environment heads) g ≤ 1)
    (qs : Nat → UnitNorm) : sourceSecond slots W g qs ≤ sourceMass slots W g qs := by
  apply familyProject_pointwise_mono slots _ _ _ qs
  intro heads
  let rho := environment heads
  have hU : (0 : Q') ≤ evalRatPoly rho W * evalRatPoly rho g :=
    Q'.mul_nonneg _ _ (hW heads) (hg heads).1
  have h := Q'.mul_le_mul_of_nonneg_left _ _ _ (hg heads).2 hU
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (tc (evalRatPoly_mul rho _ _) (mc (evalRatPoly_mul rho W g) (Q'.eqv_refl _))))
    (Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (tc (Q'.mul_one_eqv _) (Q'.eqv_symm (evalRatPoly_mul rho W g)))))

theorem sourceMean_le_one (slots : List Nat) (W g : RatPoly)
    (hW : ∀ heads : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment heads) W)
    (hg : ∀ heads : Nat → UnitNorm,
      (0 : Q') ≤ evalRatPoly (environment heads) g ∧ evalRatPoly (environment heads) g ≤ 1)
    (qs : Nat → UnitNorm) (ha : (0 : Q') < sourceMass slots W g qs) :
    sourceMean slots W g qs ha ≤ 1 :=
  Q'.divPos_le_of_le_mul _ _ ha
    (Q'.le_trans' _ _ _ (sourceSecond_le_mass slots W g hW hg qs)
      (Q'.ge_of_eqv (Q'.one_mul_eqv _)))

private def weightedTangent (W g : RatPoly) (N : Nat) (m : Q') : RatPoly :=
  polyAdd (polySmul (ell m N) (polyMul W g))
    (polySmul (slope m N)
      (polyAdd (polyMul (polyMul W g) g) (polySmul (-m) (polyMul W g))))

private theorem weightedTangent_eval (W g : RatPoly) (N : Nat) (m : Q') (rho : Nat → Q') :
    evalRatPoly rho (weightedTangent W g N m) ≈
      (evalRatPoly rho W*evalRatPoly rho g)*(ell m N+slope m N*(evalRatPoly rho g-m)) := by
  have hU := evalRatPoly_mul rho W g
  have hUg := tc (evalRatPoly_mul rho (polyMul W g) g) (mc hU (Q'.eqv_refl _))
  have h : evalRatPoly rho (weightedTangent W g N m) ≈
      ell m N*(evalRatPoly rho W*evalRatPoly rho g)+
        slope m N*(evalRatPoly rho W*evalRatPoly rho g*evalRatPoly rho g+
          (-m)*(evalRatPoly rho W*evalRatPoly rho g)) := tc (evalRatPoly_add rho _ _)
    (Q'.add_eqv_congr' (tc (evalRatPoly_smul rho _ _) (mc (Q'.eqv_refl _) hU))
      (tc (evalRatPoly_smul rho _ _)
        (mc (Q'.eqv_refl _)
          (tc (evalRatPoly_add rho _ _)
            (Q'.add_eqv_congr' hUg (tc (evalRatPoly_smul rho _ _) (mc (Q'.eqv_refl _) hU)))))))
  exact tc h (qr
    (.add (.mul (.var 2) (.mul (.var 0) (.var 1)))
      (.mul (.var 3) (.add (.mul (.mul (.var 0) (.var 1)) (.var 1))
        (.mul (.neg (.var 4)) (.mul (.var 0) (.var 1))))))
    (.mul (.mul (.var 0) (.var 1))
      (.add (.var 2) (.mul (.var 3) (.add (.var 1) (.neg (.var 4))))))
    (by decide) (fun
      | 0 => evalRatPoly rho W
      | 1 => evalRatPoly rho g
      | 2 => ell m N
      | 3 => slope m N
      | _ => m))

private theorem weightedTangent_project (slots : List Nat) (W g : RatPoly)
    (qs : Nat → UnitNorm) (N : Nat) (m : Q') :
    evalRatPoly (environment qs) (familyProject slots (weightedTangent W g N m)) ≈
      ell m N*sourceMass slots W g qs+
        slope m N*(sourceSecond slots W g qs-m*sourceMass slots W g qs) := by
  unfold weightedTangent
  rw [familyProject_add]
  refine tc (evalRatPoly_add _ _ _)
    (Q'.add_eqv_congr' (familyProject_smul_eval slots _ _ _) ?_)
  refine tc (familyProject_smul_eval slots _ _ _) (mc (Q'.eqv_refl _) ?_)
  rw [familyProject_add]
  exact tc (evalRatPoly_add _ _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (tc (familyProject_smul_eval slots _ _ _)
        (Q'.neg_mul_eqv m (sourceMass slots W g qs))))

/-- The actual finite source credit has a produced moment-based lower bound.
N=0 and pointwise zeros of g are included; only its OWN positive mass is
needed to choose the numerical tangent. No source cap is inverted. -/
theorem source_entropy_lower (slots : List Nat) (W g : RatPoly)
    (hW : ∀ heads : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment heads) W)
    (hg : ∀ heads : Nat → UnitNorm,
      (0 : Q') ≤ evalRatPoly (environment heads) g ∧ evalRatPoly (environment heads) g ≤ 1)
    (qs : Nat → UnitNorm) (ha : (0 : Q') < sourceMass slots W g qs) (N : Nat) :
    sourceMass slots W g qs*ell (sourceMean slots W g qs ha) N ≤
      sourceEntropy slots W g qs N := by
  let m := sourceMean slots W g qs ha
  have hm : m ≤ 1 := sourceMean_le_one slots W g hW hg qs ha
  have hpoint (heads : Nat → UnitNorm) :
      evalRatPoly (environment heads) (weightedTangent W g N m) ≤
        evalRatPoly (environment heads) (polyMul W (entropyStage N g)) := by
    let rho := environment heads
    have hU : (0 : Q') ≤ evalRatPoly rho W*evalRatPoly rho g :=
      Q'.mul_nonneg _ _ (hW heads) (hg heads).1
    have ht := Q'.mul_le_mul_of_nonneg_left _ _ _
      (lower_tangent N (evalRatPoly rho g) m (hg heads).2 hm) hU
    have hp : (evalRatPoly rho W*evalRatPoly rho g)*ell (evalRatPoly rho g) N ≈
        evalRatPoly rho (polyMul W (entropyStage N g)) :=
      tc (Q'.mul_assoc_eqv _ _ _)
        (tc (mc (Q'.eqv_refl _) (Q'.eqv_symm (partial_pin _ N)))
          (Q'.eqv_symm (tc (evalRatPoly_mul rho _ _) (mc (Q'.eqv_refl _) (entropyStage_eval N g rho)))))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (weightedTangent_eval W g N m rho))
      (Q'.le_trans' _ _ _ ht (Q'.le_of_eqv hp))
  have hj := familyProject_pointwise_mono slots _ _ hpoint qs
  have hpin := weightedTangent_project slots W g qs N m
  have hc : sourceSecond slots W g qs-m*sourceMass slots W g qs ≈ 0 :=
    tc (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ (sourceMean_pin slots W g qs ha)))
      (qr (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
        (fun _ => sourceSecond slots W g qs))
  have hcollapse := tc hpin
    (tc (Q'.add_eqv_congr' (Q'.eqv_refl _) (mc (Q'.eqv_refl _) hc))
      (tc (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_zero_eqv _))
        (tc (Q'.eqv_of_eq (Q'.add_zero' _)) (Q'.mul_comm_eqv _ _))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcollapse) hj

/-- Keep the negative source-entropy credit. The new upper value depends on
the computed SAME first/second moments, not an assumed concentration bound. -/
theorem retained_credit_upper (slots : List Nat) (W g : RatPoly)
    (hW : ∀ heads : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment heads) W)
    (hg : ∀ heads : Nat → UnitNorm,
      (0 : Q') ≤ evalRatPoly (environment heads) g ∧ evalRatPoly (environment heads) g ≤ 1)
    (qs : Nat → UnitNorm) (ha : (0 : Q') < sourceMass slots W g qs) (N : Nat) :
    partialSum (sourceMass slots W g qs) N-sourceEntropy slots W g qs N ≤
      partialSum (sourceMass slots W g qs) N-
        sourceMass slots W g qs*ell (sourceMean slots W g qs ha) N :=
  Q'.add_le_add_left _ _ _ (Q'.neg_le_neg (source_entropy_lower slots W g hW hg qs ha N))

end YMGap.Continuum.QuaternionHaarFamilySourceConcentration

#print axioms YMGap.Continuum.QuaternionHaarFamilySourceConcentration.sourceMass
#print axioms YMGap.Continuum.QuaternionHaarFamilySourceConcentration.sourceSecond
#print axioms YMGap.Continuum.QuaternionHaarFamilySourceConcentration.sourceEntropy
#print axioms YMGap.Continuum.QuaternionHaarFamilySourceConcentration.sourceMean
#print axioms YMGap.Continuum.QuaternionHaarFamilySourceConcentration.sourceMean_pin
#print axioms YMGap.Continuum.QuaternionHaarFamilySourceConcentration.sourceSecond_le_mass
#print axioms YMGap.Continuum.QuaternionHaarFamilySourceConcentration.sourceMean_le_one
#print axioms YMGap.Continuum.QuaternionHaarFamilySourceConcentration.source_entropy_lower
#print axioms YMGap.Continuum.QuaternionHaarFamilySourceConcentration.retained_credit_upper
