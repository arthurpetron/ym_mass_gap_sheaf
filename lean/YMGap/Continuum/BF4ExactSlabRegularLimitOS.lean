/-
# Regular-real cutoff limits of the exact BF4 slab bounds

This file is the constructive limit bridge after the finite-slab analytic
estimate.  It proves three order-closed facts.

* A spacing/cutoff-uniform quarter quadratic bound survives any supplied
  `RegularCReal.ModCauchy` cutoff modulus.
* The normalized full physical reflection Gram stays nonnegative after
  cutoff and volume removal, and its unit channel stays normalized.
* A cutoff-uniform geometric correlation envelope survives the same limit.

The module does not manufacture the missing Yang--Mills moduli or the
semigroup/action identification.  It proves that once those constructive
witnesses are supplied, no compactness, subsequence, or classical choice is
needed to pass AF comparison, OS2 positivity, normalization, and clustering
to the limit.
-/

import YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison
import YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
import YMGap.Continuum.RegularLinearScalingLimit

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace YMGap.Continuum.BF4ExactSlabRegularLimitOS

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison
open YMGap.Continuum.BF4ExactSlabGroupedAFComparison
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.RegularLinearScalingLimit
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

/-! ## 1. Order bounds pass through constructive regular-real limits -/

/-- A pointwise rational bound `left_j <= c * right_j` survives two
constructive completeness limits.  The right limit is identified with
`c * lim right` by continuity of rational scaling, not by an assumed
limit law. -/
theorem scaledBound_survives_completeLimit
    (left right : Nat → Q') (c : Q')
    (leftCauchy : ModCauchy (fun j => ofQ' (left j)))
    (rightCauchy : ModCauchy (fun j => ofQ' (right j)))
    (bound : ∀ j, left j ≤ c * right j) :
    completeLimit (fun j => ofQ' (left j)) leftCauchy ≤
      qmul c
        (completeLimit (fun j => ofQ' (right j)) rightCauchy) := by
  apply le_of_convergesTo_le_convergesTo
    (convergesTo_completeLimit
      (fun j => ofQ' (left j)) leftCauchy)
    (convergesTo_qmul c
      (convergesTo_completeLimit
        (fun j => ofQ' (right j)) rightCauchy))
  intro j approximation
  change left j ≤ c * right j
  exact bound j

/-! ## 2. The concrete AF exact-slab sequence -/

/-- Exact normalized slab quadratic along the matched AF trajectory, using
the canonical all-cutoff normalization proved by selected-face Haar
orthogonality. -/
def exactAFQuadraticSeq
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling)
    (observable : EdgeLabelling → Q')
    (scale : Nat) : Q' :=
  finiteJointQuadratic
    (exactSlabPositiveHaarStates
      (matchedAllSpinCutoff family coupling scale))
    observable
    (normalizedExactSlabKernel_allCutoffs
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinCutoff family coupling scale))

/-- Haar-diagonal boundary norm along the same AF trajectory. -/
def exactAFWeightedSquareSeq
    {family : MatchedBlockFamily}
    {coupling : Nat → Q'}
    (observable : EdgeLabelling → Q')
    (scale : Nat) : Q' :=
  exactSlabBoundaryWeightedSquare
    (matchedAllSpinCutoff family coupling scale) observable

/-- The reduced AF certificate gives the exact pointwise quarter inequality
at every scale. -/
theorem exactAFQuadratic_abs_le_quarter
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling)
    (observable : EdgeLabelling → Q')
    (meanZero : ∀ scale,
      ExactSlabBoundaryMeanZero
        (matchedAllSpinCutoff family coupling scale) observable)
    (scale : Nat) :
    Q'.abs (exactAFQuadraticSeq certificate observable scale) ≤
      Q'.mkPos 1 4 (by decide) *
        exactAFWeightedSquareSeq
          (family := family) (coupling := coupling) observable scale :=
  (certificate.entrywise scale).exact_quadratic_abs_le_quarter
    observable (meanZero scale)

/-- Consequently the one-sided gap-form contraction holds at every AF
scale. -/
theorem exactAFQuadratic_le_quarter
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling)
    (observable : EdgeLabelling → Q')
    (meanZero : ∀ scale,
      ExactSlabBoundaryMeanZero
        (matchedAllSpinCutoff family coupling scale) observable)
    (scale : Nat) :
    exactAFQuadraticSeq certificate observable scale ≤
      Q'.mkPos 1 4 (by decide) *
        exactAFWeightedSquareSeq
          (family := family) (coupling := coupling) observable scale :=
  Q'.le_trans' _ _ _
    (Q'.le_abs_self (exactAFQuadraticSeq certificate observable scale))
    (exactAFQuadratic_abs_le_quarter
      certificate observable meanZero scale)

/-- **Cutoff-removal theorem for the exact AF contraction.**  Given explicit
constructive Cauchy moduli for the exact quadratic and its Haar norm, the
quarter bound survives the scaling/cutoff limit. -/
theorem exactAFQuarterContraction_survives_regularLimit
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling)
    (observable : EdgeLabelling → Q')
    (meanZero : ∀ scale,
      ExactSlabBoundaryMeanZero
        (matchedAllSpinCutoff family coupling scale) observable)
    (quadraticCauchy :
      ModCauchy (fun scale =>
        ofQ' (exactAFQuadraticSeq certificate observable scale)))
    (normCauchy :
      ModCauchy (fun scale =>
        ofQ' (exactAFWeightedSquareSeq
          (family := family) (coupling := coupling) observable scale))) :
    completeLimit
        (fun scale =>
          ofQ' (exactAFQuadraticSeq certificate observable scale))
        quadraticCauchy ≤
      qmul (Q'.mkPos 1 4 (by decide))
        (completeLimit
          (fun scale =>
            ofQ' (exactAFWeightedSquareSeq
              (family := family) (coupling := coupling) observable scale))
          normCauchy) :=
  scaledBound_survives_completeLimit
    (exactAFQuadraticSeq certificate observable)
    (exactAFWeightedSquareSeq
      (family := family) (coupling := coupling) observable)
    (Q'.mkPos 1 4 (by decide))
    quadraticCauchy normCauchy
    (exactAFQuadratic_le_quarter certificate observable meanZero)

/-! ## 2.1. The precise same-action OS2 identification seam -/

/-- The missing finite-scale identification between the normalized signed
Peter--Weyl exact-slab quadratic and the independently proved positive
corrected-slab physical reflection quadratic.  This proposition is deliberately
not inhabited here: it includes the carrier comparison (the positive
Haar-diagonal filter versus the complete lower-half carrier) as well as the
dual/physical action identity. -/
def ExactAFPhysicalReflectionIdentification
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling) : Prop :=
  ∀ scale coefficient,
    Q'.eqv (exactAFQuadraticSeq certificate coefficient scale)
      (centralNormalizedFullPhysicalReflectionQuadratic
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        0 coefficient)

/-- Once the same-action identification is supplied, finite corrected-slab
OS2 positivity transfers to the exact Peter--Weyl quadratic at every AF
scale. -/
theorem exactAFQuadratic_nonnegative_of_physicalIdentification
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling)
    (identification :
      ExactAFPhysicalReflectionIdentification certificate)
    (scale : Nat) (coefficient : EdgeLabelling → Q') :
    (0 : Q') ≤ exactAFQuadraticSeq certificate coefficient scale := by
  exact Q'.le_trans' _ _ _
    (centralNormalizedFullPhysicalReflectionQuadratic_nonnegative
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      0 coefficient)
    (Q'.ge_of_eqv (identification scale coefficient))

/-- Under the same identification, exact-slab OS2 is closed under the
constructive cutoff/volume limit. -/
theorem exactAFQuadraticLimit_nonnegative_of_physicalIdentification
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling)
    (identification :
      ExactAFPhysicalReflectionIdentification certificate)
    (coefficient : EdgeLabelling → Q')
    (cauchy : ModCauchy (fun scale =>
      ofQ' (exactAFQuadraticSeq certificate coefficient scale))) :
    czero ≤
      completeLimit
        (fun scale =>
          ofQ' (exactAFQuadraticSeq certificate coefficient scale))
        cauchy := by
  show ofQ' 0 ≤ completeLimit _ cauchy
  exact ofQ'_le_completeLimit _ cauchy (fun scale _ =>
    exactAFQuadratic_nonnegative_of_physicalIdentification
      certificate identification scale coefficient)

/-- The same-action identification also transfers exact unit normalization
to the signed Peter--Weyl presentation at every scale. -/
theorem exactAFQuadratic_unit_eqv_one_of_physicalIdentification
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling)
    (identification :
      ExactAFPhysicalReflectionIdentification certificate)
    (scale : Nat) :
    Q'.eqv (exactAFQuadraticSeq certificate (fun _ => 1) scale) 1 :=
  Q'.eqv_trans _ _ _
    (identification scale (fun _ => 1))
    (centralNormalizedFullPhysicalReflectionQuadratic_one
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)

/-! ## 3. OS reflection positivity and normalization survive the limit -/

/-- The normalized full physical reflection Gram along an arbitrary joint
cutoff/volume schedule. -/
def normalizedPhysicalReflectionSeq
    (w : Nat → Q') (hw : ∀ scale, (0 : Q') ≤ w scale)
    (cutoff half : Nat → Nat)
    (coefficient : EdgeLabelling → Q')
    (scale : Nat) : Q' :=
  centralNormalizedFullPhysicalReflectionQuadratic
    (w scale) (hw scale) (cutoff scale) (half scale) coefficient

/-- The constructive regular-real limit of one reflected physical
quadratic. -/
def normalizedPhysicalReflectionLimit
    (w : Nat → Q') (hw : ∀ scale, (0 : Q') ≤ w scale)
    (cutoff half : Nat → Nat)
    (coefficient : EdgeLabelling → Q')
    (cauchy : ModCauchy (fun scale =>
      ofQ' (normalizedPhysicalReflectionSeq
        w hw cutoff half coefficient scale))) : RegularCReal :=
  completeLimit
    (fun scale => ofQ'
      (normalizedPhysicalReflectionSeq
        w hw cutoff half coefficient scale))
    cauchy

/-- **OS2 is closed under cutoff and infinite-volume removal.**  Every
finite normalized physical reflection Gram is nonnegative, hence so is its
constructive regular-real limit. -/
theorem normalizedPhysicalReflectionLimit_nonnegative
    (w : Nat → Q') (hw : ∀ scale, (0 : Q') ≤ w scale)
    (cutoff half : Nat → Nat)
    (coefficient : EdgeLabelling → Q')
    (cauchy : ModCauchy (fun scale =>
      ofQ' (normalizedPhysicalReflectionSeq
        w hw cutoff half coefficient scale))) :
    czero ≤
      normalizedPhysicalReflectionLimit
        w hw cutoff half coefficient cauchy := by
  show ofQ' 0 ≤ completeLimit _ cauchy
  exact ofQ'_le_completeLimit _ cauchy (fun scale _ =>
    centralNormalizedFullPhysicalReflectionQuadratic_nonnegative
      (w scale) (hw scale) (cutoff scale) (half scale) coefficient)

/-- The unit reflected quadratic remains exactly normalized after the same
limit. -/
theorem normalizedPhysicalReflectionUnitLimit
    (w : Nat → Q') (hw : ∀ scale, (0 : Q') ≤ w scale)
    (cutoff half : Nat → Nat)
    (cauchy : ModCauchy (fun scale =>
      ofQ' (normalizedPhysicalReflectionSeq
        w hw cutoff half (fun _ => 1) scale))) :
    Equiv
      (normalizedPhysicalReflectionLimit
        w hw cutoff half (fun _ => 1) cauchy)
      (ofQ' 1) := by
  apply le_antisymm
  · exact completeLimit_le_ofQ' _ cauchy (fun scale _ =>
      Q'.le_of_eqv
        (centralNormalizedFullPhysicalReflectionQuadratic_one
          (w scale) (hw scale) (cutoff scale) (half scale)))
  · exact ofQ'_le_completeLimit _ cauchy (fun scale _ =>
      Q'.ge_of_eqv
        (centralNormalizedFullPhysicalReflectionQuadratic_one
          (w scale) (hw scale) (cutoff scale) (half scale)))

/-! ## 4. Uniform exponential envelopes survive the limit -/

/-- A cutoff-uniform absolute geometric envelope becomes a two-sided
regular-real envelope after cutoff/volume removal.  This is the order form
of exponential clustering appropriate before an absolute-value operation
is installed on the limiting observable algebra. -/
theorem geometricClustering_survives_regularLimit
    (correlation : Nat → Q')
    (cauchy : ModCauchy (fun cutoff => ofQ' (correlation cutoff)))
    (amplitude rate : Q') (separation : Nat)
    (uniformDecay : ∀ cutoff,
      Q'.abs (correlation cutoff) ≤ amplitude * rate ^ separation) :
    ofQ' (-(amplitude * rate ^ separation)) ≤
        completeLimit (fun cutoff => ofQ' (correlation cutoff)) cauchy ∧
      completeLimit (fun cutoff => ofQ' (correlation cutoff)) cauchy ≤
        ofQ' (amplitude * rate ^ separation) := by
  constructor
  · exact ofQ'_le_completeLimit _ cauchy (fun cutoff _ => by
      have hnegAbs : -(Q'.abs (correlation cutoff)) ≤
          correlation cutoff :=
        Q'.le_trans' _ _ _
          (Q'.neg_le_neg (Q'.neg_le_abs (correlation cutoff)))
          (Q'.le_of_eqv (Q'.neg_neg_eqv (correlation cutoff)))
      exact Q'.le_trans' _ _ _
        (Q'.neg_le_neg (uniformDecay cutoff)) hnegAbs)
  · exact completeLimit_le_ofQ' _ cauchy (fun cutoff _ =>
      Q'.le_trans' _ _ _
        (Q'.le_abs_self (correlation cutoff))
        (uniformDecay cutoff))

end YMGap.Continuum.BF4ExactSlabRegularLimitOS

#print axioms YMGap.Continuum.BF4ExactSlabRegularLimitOS.scaledBound_survives_completeLimit
#print axioms YMGap.Continuum.BF4ExactSlabRegularLimitOS.exactAFQuadratic_abs_le_quarter
#print axioms YMGap.Continuum.BF4ExactSlabRegularLimitOS.exactAFQuarterContraction_survives_regularLimit
#print axioms YMGap.Continuum.BF4ExactSlabRegularLimitOS.exactAFQuadraticLimit_nonnegative_of_physicalIdentification
#print axioms YMGap.Continuum.BF4ExactSlabRegularLimitOS.exactAFQuadratic_unit_eqv_one_of_physicalIdentification
#print axioms YMGap.Continuum.BF4ExactSlabRegularLimitOS.normalizedPhysicalReflectionLimit_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabRegularLimitOS.normalizedPhysicalReflectionUnitLimit
#print axioms YMGap.Continuum.BF4ExactSlabRegularLimitOS.geometricClustering_survives_regularLimit
