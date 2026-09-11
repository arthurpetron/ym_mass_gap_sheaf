/-
# Finite-anchor bounds for strict staged reflection pairings

The first theorem is the geometric estimate needed to bound
the diagonal reflection pairing of a staged Cauchy representative.  The
remaining declarations expose, as data, the fixed-anchor rational cap hidden
inside the existing fixed-quadratic Cauchy proof and propagate it along a
`SquaredSeminorm.Cauchy` representative.

No scalar-completion or quotient lift is attempted here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingAnchorBound

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The staged quadratic triangle with a finite anchor -/

/-- The diagonal reflection pairing at `left` is bounded by twice the squared
distance to an arbitrary finite anchor plus twice the anchor diagonal.

Both stages are first co-presented in `max left.base anchor.base`.  There the
semantic identity `left = (left - anchor) + anchor`, followed by the existing
sqrt-free quadratic triangle, proves the estimate. -/
theorem strictJointCylinderStageReflectionBilinear_self_leEv_triangle
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left anchor : StrictJointCylinderStage) :
    CReal.leEv
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left left)
      (CReal.add
        (CReal.add
          (strictJointCylinderStageReflectionDistSq
            hcoupling hle left anchor)
          (strictJointCylinderStageReflectionDistSq
            hcoupling hle left anchor))
        (CReal.add
          (strictJointCylinderStageReflectionBilinear
            hcoupling hle anchor anchor)
          (strictJointCylinderStageReflectionBilinear
            hcoupling hle anchor anchor))) := by
  let outer := max left.base anchor.base
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hanchor : anchor.base <= outer := Nat.le_max_right _ _
  let L : StrictJointCylinderVector outer :=
    boxTransportStrictJointCylinderVector hleft left.vector
  let A : StrictJointCylinderVector outer :=
    boxTransportStrictJointCylinderVector hanchor anchor.vector
  let difference : StrictJointCylinderVector outer :=
    strictJointCylinderDifference L A
  have hrecover : StrictJointCylinderVectorEquivalent
      L (difference.add A) := by
    exact strictJointCylinderDifference_add_right_equivalent L A
  have hsourceCommon : CReal.Equiv
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left left)
      (L.reflectionQuadratic hcoupling hle) := by
    have hcommon := strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle left left hleft hleft
    exact CReal.Equiv.trans (CReal.Equiv.symm hcommon)
      (strictJointCylinderReflectionBilinear_self hcoupling hle L)
  have hrecoverQuadratic : CReal.Equiv
      (L.reflectionQuadratic hcoupling hle)
      ((difference.add A).reflectionQuadratic hcoupling hle) :=
    StrictJointCylinderVector.reflectionQuadratic_equiv
      hcoupling hle hrecover
  have htriangle := reflectionQuadratic_add_le
    hcoupling hle difference A
  have hdistCommon := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle left anchor hleft hanchor
  have hanchorCommon := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle anchor anchor hanchor hanchor
  have hanchorQuadratic : CReal.Equiv
      (A.reflectionQuadratic hcoupling hle)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle anchor anchor) :=
    CReal.Equiv.trans
      (CReal.Equiv.symm
        (strictJointCylinderReflectionBilinear_self
          hcoupling hle A))
      hanchorCommon
  have htargetCommon : CReal.Equiv
      (CReal.add
        (CReal.add
          (difference.reflectionQuadratic hcoupling hle)
          (difference.reflectionQuadratic hcoupling hle))
        (CReal.add
          (A.reflectionQuadratic hcoupling hle)
          (A.reflectionQuadratic hcoupling hle)))
      (CReal.add
        (CReal.add
          (strictJointCylinderStageReflectionDistSq
            hcoupling hle left anchor)
          (strictJointCylinderStageReflectionDistSq
            hcoupling hle left anchor))
        (CReal.add
          (strictJointCylinderStageReflectionBilinear
            hcoupling hle anchor anchor)
          (strictJointCylinderStageReflectionBilinear
            hcoupling hle anchor anchor))) := by
    exact CReal.Equiv_add
      (CReal.Equiv_add hdistCommon hdistCommon)
      (CReal.Equiv_add hanchorQuadratic hanchorQuadratic)
  exact CReal.leEv_trans (CReal.leEv_of_equiv hsourceCommon)
    (CReal.leEv_trans (CReal.leEv_of_equiv hrecoverQuadratic)
      (CReal.leEv_trans htriangle
        (CReal.leEv_of_equiv htargetCommon)))

/-! ## 2. Re-expose the fixed-quadratic modulus as Type-level data -/

/-- The concrete modulus already used internally by
`centralNormalizedStrictJointFixedQuadraticLimit`. -/
def strictJointFixedQuadraticCauchyModulus
    (roots : List (List Nat)) (coefficient : List Bool -> Q')
    (tolerance : Q') : Nat :=
  let cauchyCoefficient :=
    strictJointFixedQuadraticCauchyCoefficient roots coefficient
  (tolerance * Q'.invSucc cauchyCoefficient.num.toNat).den

/-- The fixed-quadratic sequence is Cauchy at the preceding explicit modulus.
This factors the proof already present in the constructor of
`centralNormalizedStrictJointFixedQuadraticLimit` into a reusable theorem. -/
theorem centralNormalizedStrictJointFixedQuadraticSequence_cauchy_at_modulus
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : forall root, root ∈ roots ->
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool -> Q')
    (tolerance : Q') (htolerance : (0 : Q') < tolerance)
    (m n : Nat)
    (hm : strictJointFixedQuadraticCauchyModulus
      roots coefficient tolerance <= m)
    (hn : strictJointFixedQuadraticCauchyModulus
      roots coefficient tolerance <= n) :
    centralNormalizedStrictJointFixedQuadraticSequence
          coupling hcoupling base roots coefficient m <=
        centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base roots coefficient n + tolerance ∧
      centralNormalizedStrictJointFixedQuadraticSequence
          coupling hcoupling base roots coefficient n <=
        centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base roots coefficient m + tolerance := by
  let cauchyCoefficient :=
    strictJointFixedQuadraticCauchyCoefficient roots coefficient
  let scaledTolerance :=
    tolerance * Q'.invSucc cauchyCoefficient.num.toNat
  have hcoefficient : (0 : Q') <= cauchyCoefficient :=
    strictJointFixedQuadraticCauchyCoefficient_nonnegative roots coefficient
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos htolerance
      (Q'.invSucc_pos cauchyCoefficient.num.toNat)
  have hscaledFinal : cauchyCoefficient * scaledTolerance <= tolerance :=
    ExpNeg.mul_le_of_mul_invSucc_toNat cauchyCoefficient tolerance
      hcoefficient (Q'.le_of_lt htolerance)
  change scaledTolerance.den <= m at hm
  change scaledTolerance.den <= n at hn
  rcases Nat.le_total m n with hmn | hnm
  · have hpair :=
      centralNormalizedStrictJointFixedQuadraticSequence_pair_abs_le
        hcoupling hle hmn hroots coefficient
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hm
    have hhalf : HalfPow.half ^ m <=
        HalfPow.half ^ scaledTolerance.den := by
      rw [hoffset]
      exact ExpNeg.pow_half_antitone scaledTolerance.den offset
    have hhalfTolerance : HalfPow.half ^ scaledTolerance.den <=
        scaledTolerance :=
      HalfPow.pow_half_le scaledTolerance hscaledPositive
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      (HalfPow.half ^ m) scaledTolerance cauchyCoefficient
      (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
    have habs : Q'.abs
        (centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base roots coefficient n +
          (-centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base roots coefficient m)) <= tolerance :=
      Q'.le_trans' _ _ _ hpair
        (Q'.le_trans' _ _ _ hscaled hscaledFinal)
    have htwo := Q'.two_sided_of_abs_sub_le habs
    exact ⟨htwo.2, htwo.1⟩
  · have hpair :=
      centralNormalizedStrictJointFixedQuadraticSequence_pair_abs_le
        hcoupling hle hnm hroots coefficient
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hn
    have hhalf : HalfPow.half ^ n <=
        HalfPow.half ^ scaledTolerance.den := by
      rw [hoffset]
      exact ExpNeg.pow_half_antitone scaledTolerance.den offset
    have hhalfTolerance : HalfPow.half ^ scaledTolerance.den <=
        scaledTolerance :=
      HalfPow.pow_half_le scaledTolerance hscaledPositive
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      (HalfPow.half ^ n) scaledTolerance cauchyCoefficient
      (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
    have habs : Q'.abs
        (centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base roots coefficient m +
          (-centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base roots coefficient n)) <= tolerance :=
      Q'.le_trans' _ _ _ hpair
        (Q'.le_trans' _ _ _ hscaled hscaledFinal)
    exact Q'.two_sided_of_abs_sub_le habs

/-! ## 3. A rational cap for one finite staged anchor -/

def strictJointCylinderStageAnchorModulus
    (stage : StrictJointCylinderStage) : Nat :=
  strictJointFixedQuadraticCauchyModulus
    stage.vector.roots stage.vector.coefficient (Q'.ofNat 1)

/-- A computable rational cap obtained from one approximation of the finite
anchor quadratic. -/
def strictJointCylinderStageAnchorCap
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) : Q' :=
  Q'.abs
      ((stage.vector.reflectionQuadratic hcoupling hle).approx
        (strictJointCylinderStageAnchorModulus stage)) +
    Q'.ofNat 1

theorem strictJointCylinderStageAnchorCap_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) :
    (0 : Q') <= strictJointCylinderStageAnchorCap hcoupling hle stage := by
  unfold strictJointCylinderStageAnchorCap
  exact Q'.zero_le_add _ _
    (Q'.abs_nonneg _)
    (by decide)

/-- The anchor's diagonal staged pairing is bounded by its explicit finite
cap. -/
theorem strictJointCylinderStageReflectionBilinear_self_leRat_anchorCap
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) :
    CReal.leRat
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle stage stage)
      (strictJointCylinderStageAnchorCap hcoupling hle stage) := by
  let modulus := strictJointCylinderStageAnchorModulus stage
  let quadratic := stage.vector.reflectionQuadratic hcoupling hle
  have hquadratic : CReal.leRat quadratic
      (strictJointCylinderStageAnchorCap hcoupling hle stage) := by
    apply CReal.leRat_of_eventually
    refine ⟨modulus, fun n hn => ?_⟩
    have hcauchy :=
      centralNormalizedStrictJointFixedQuadraticSequence_cauchy_at_modulus
        hcoupling hle stage.vector.rootsCanonical stage.vector.coefficient
          (Q'.ofNat 1) (by decide)
          n modulus hn (Nat.le_refl modulus)
    have htoAbs : quadratic.approx modulus <=
        Q'.abs (quadratic.approx modulus) :=
      Q'.le_abs_self _
    exact Q'.le_trans' _ _ _ hcauchy.1
      (Q'.add_le_add_right _ _ (Q'.ofNat 1) htoAbs)
  have hcommon := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle stage stage (Nat.le_refl _) (Nat.le_refl _)
  rw [boxTransportStrictJointCylinderVector_refl] at hcommon
  have hpairingToQuadratic : CReal.Equiv
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle stage stage)
      quadratic :=
    CReal.Equiv.trans (CReal.Equiv.symm hcommon)
      (strictJointCylinderReflectionBilinear_self
        hcoupling hle stage.vector)
  exact CReal.leRat_of_equiv hpairingToQuadratic hquadratic

/-! ## 4. Propagation of the finite cap along a staged Cauchy representative -/

variable {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
  (hle : coupling <= anchorCoupling)

private abbrev StageSeminorm : SquaredSeminorm :=
  strictJointCylinderStageSquaredSeminorm hcoupling hle

def strictJointCylinderCauchyNormBase
    (X : (StageSeminorm hcoupling hle).Cauchy) : Nat :=
  X.modulus (Q'.ofNat 1)

def strictJointCylinderCauchyAnchor
    (X : (StageSeminorm hcoupling hle).Cauchy) :
    StrictJointCylinderStage :=
  X.seq (strictJointCylinderCauchyNormBase hcoupling hle X)

def strictJointCylinderCauchyAnchorCap
    (X : (StageSeminorm hcoupling hle).Cauchy) : Q' :=
  strictJointCylinderStageAnchorCap hcoupling hle
    (strictJointCylinderCauchyAnchor hcoupling hle X)

def strictJointCylinderCauchyNormBoundQ
    (X : (StageSeminorm hcoupling hle).Cauchy) : Q' :=
  (Q'.ofNat 1 + Q'.ofNat 1) +
    (strictJointCylinderCauchyAnchorCap hcoupling hle X +
      strictJointCylinderCauchyAnchorCap hcoupling hle X)

def strictJointCylinderCauchyNormCeil
    (X : (StageSeminorm hcoupling hle).Cauchy) : Nat :=
  (strictJointCylinderCauchyNormBoundQ hcoupling hle X).num.toNat + 1

theorem strictJointCylinderCauchy_one_le_normCeil
    (X : (StageSeminorm hcoupling hle).Cauchy) :
    1 <= strictJointCylinderCauchyNormCeil hcoupling hle X :=
  Nat.le_add_left _ _

/-- Every term past the representative's finite anchor has diagonal pairing
bounded by one explicit rational. -/
theorem strictJointCylinderCauchy_self_leRat_normBoundQ
    (X : (StageSeminorm hcoupling hle).Cauchy)
    (n : Nat)
    (hn : strictJointCylinderCauchyNormBase hcoupling hle X <= n) :
    CReal.leRat
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle (X.seq n) (X.seq n))
      (strictJointCylinderCauchyNormBoundQ hcoupling hle X) := by
  let base := strictJointCylinderCauchyNormBase hcoupling hle X
  let anchor := strictJointCylinderCauchyAnchor hcoupling hle X
  let cap := strictJointCylinderCauchyAnchorCap hcoupling hle X
  have htriangle :=
    strictJointCylinderStageReflectionBilinear_self_leEv_triangle
      hcoupling hle (X.seq n) anchor
  have hdist : CReal.leEv
      (strictJointCylinderStageReflectionDistSq
        hcoupling hle (X.seq n) anchor)
      (CReal.ofQ' (Q'.ofNat 1)) := by
    exact X.isCauchy (Q'.ofNat 1) (by decide)
      n base hn (Nat.le_refl base)
  have hanchorRat :=
    strictJointCylinderStageReflectionBilinear_self_leRat_anchorCap
      hcoupling hle anchor
  have hanchor : CReal.leEv
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle anchor anchor)
      (CReal.ofQ' cap) := by
    exact hanchorRat
  have hsum := CReal.leEv_add
    (CReal.leEv_add hdist hdist)
    (CReal.leEv_add hanchor hanchor)
  have hbound := CReal.leEv_trans htriangle hsum
  change CReal.leEv
    (strictJointCylinderStageReflectionBilinear
      hcoupling hle (X.seq n) (X.seq n))
    (CReal.ofQ'
      (strictJointCylinderCauchyNormBoundQ hcoupling hle X))
  change CReal.leEv
    (strictJointCylinderStageReflectionBilinear
      hcoupling hle (X.seq n) (X.seq n))
    (CReal.add
      (CReal.add
        (CReal.ofQ' (Q'.ofNat 1))
        (CReal.ofQ' (Q'.ofNat 1)))
      (CReal.add (CReal.ofQ' cap) (CReal.ofQ' cap)))
  exact hbound

theorem strictJointCylinderCauchy_self_leRat_normCeil
    (X : (StageSeminorm hcoupling hle).Cauchy)
    (n : Nat)
    (hn : strictJointCylinderCauchyNormBase hcoupling hle X <= n) :
    CReal.leRat
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle (X.seq n) (X.seq n))
      (Q'.ofNat
        (strictJointCylinderCauchyNormCeil hcoupling hle X)) := by
  exact CReal.leRat_mono
    (strictJointCylinderCauchy_self_leRat_normBoundQ
      hcoupling hle X n hn)
    (Q'.le_ofNat_ceil
      (strictJointCylinderCauchyNormBoundQ hcoupling hle X))

#print axioms strictJointCylinderStageReflectionBilinear_self_leEv_triangle
#print axioms strictJointCylinderStageReflectionBilinear_self_leRat_anchorCap
#print axioms strictJointCylinderCauchy_self_leRat_normBoundQ
#print axioms strictJointCylinderCauchy_self_leRat_normCeil

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingAnchorBound
