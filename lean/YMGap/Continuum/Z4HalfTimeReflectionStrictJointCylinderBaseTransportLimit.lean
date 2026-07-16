/-
# Constructive-real base transport of the strict reflection quadratic

The aligned centered-event comparison is lifted here through the literal Gram
entries and the finite coefficient quadratic.  The resulting theorem removes
the common-box source presentation from the doubled-time Young recurrence.
Every error has an explicit dyadic modulus; no covariance postulate is used.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransport

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 7000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem abs_sub_via_common_le
    {left common right leftError rightError : Q'}
    (hleft : Q'.abs (left + (-common)) ≤ leftError)
    (hright : Q'.abs (common + (-right)) ≤ rightError) :
    Q'.abs (left + (-right)) ≤ leftError + rightError := by
  have hdecompose : left + (-right) ≈
      (left + (-common)) + (common + (-right)) := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv left (-common) (common + (-right))) ?_
    refine Q'.add_eqv_congr_left left _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-common) common (-right))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right ((-common) + common) 0 (-right)
        (Q'.neg_add_self_eqv common)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-right))
  have htriangle := Q'.abs_add_le'
    (left + (-common)) (common + (-right))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.le_trans' _ _ _ htriangle (Q'.add_le_add hleft hright))

private theorem two_sided_add_of_abs_sub_le
    {left right error : Q'}
    (h : Q'.abs (left + (-right)) ≤ error) :
    left ≤ right + error ∧ right ≤ left + error := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm right left)) h

/-! ## 1. Same-index centered and Gram bounds -/

def strictJointBaseTransportCenteredCoefficient
    (roots : List (List Nat)) : Q' :=
  ((1 : Q') + 1) +
    spinSummedJointCylinderCoefficient (roots.length + roots.length)

theorem strictJointBaseTransportCenteredCoefficient_nonnegative
    (roots : List (List Nat)) :
    (0 : Q') ≤ strictJointBaseTransportCenteredCoefficient roots := by
  unfold strictJointBaseTransportCenteredCoefficient
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ (by decide) (by decide))
    (spinSummedJointCylinderCoefficient_nonnegative
      (roots.length + roots.length))

/-- The aligned comparison and the source sequence's own Cauchy estimate give
a same-index base-transport bound. -/
theorem couplingParametricStrictJointCenteredSequence_base_transport_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (base padding stage : Nat) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricStrictJointCenteredSequence
            coupling hcoupling (base + padding)
            (transportedCylinderRoots base (base + padding) roots)
            predicate stage +
          (-couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots predicate stage)) ≤
      strictJointBaseTransportCenteredCoefficient roots *
        HalfPow.half ^ stage := by
  let shifted := couplingParametricStrictJointCenteredSequence
    coupling hcoupling base roots predicate (stage + padding)
  have haligned :=
    couplingParametricStrictJointCenteredSequence_base_transport_aligned_abs_le
      hcoupling hle base padding stage hroots predicate
  have hsource := couplingParametricStrictJointCenteredSequence_pair_abs_le
    hcoupling hle (Nat.le_add_right stage padding) hroots predicate
  have hchain := abs_sub_via_common_le haligned hsource
  let h := HalfPow.half ^ stage
  let coefficient := spinSummedJointCylinderCoefficient
    (roots.length + roots.length)
  have htwo : (((1 : Q') + 1) * h) ≈ h + h := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (1 : Q') 1 h)
      (Q'.add_eqv_congr' (Q'.one_mul_eqv h) (Q'.one_mul_eqv h))
  have hcoefficient :
      strictJointBaseTransportCenteredCoefficient roots * h ≈
        (h + h) + coefficient * h := by
    unfold strictJointBaseTransportCenteredCoefficient
    exact Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv ((1 : Q') + 1) coefficient h)
      (Q'.add_eqv_congr' htwo (Q'.eqv_refl _))
  change Q'.abs
      (couplingParametricStrictJointCenteredSequence
          coupling hcoupling (base + padding)
          (transportedCylinderRoots base (base + padding) roots)
          predicate stage +
        (-couplingParametricStrictJointCenteredSequence
          coupling hcoupling base roots predicate stage)) ≤
    strictJointBaseTransportCenteredCoefficient roots * h
  exact Q'.le_trans' _ _ _ hchain (Q'.ge_of_eqv hcoefficient)

theorem centralNormalizedStrictJointGramSequence_to_centered_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    Q'.abs
        (centralNormalizedStrictJointGramSequence
            coupling hcoupling base roots left right stage +
          (-couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots
            (centralStrictJointPairPredicate roots.length left right)
            stage)) ≤
      strictJointConditionalCenteredCoefficient
          (roots.length + roots.length) * HalfPow.half ^ stage := by
  have hgram := centralNormalizedStrictJointGramSequence_eqv_givenSlab
    hcoupling hroots left right stage
  have hpoint :=
    couplingPhysicalGivenSlabStrictJoint_to_centeredSequence_half_pow
      (stage := stage) hcoupling hle hroots left right
  have hgiven : Q'.abs
      (couplingParametricStrictJointGivenSlabSequence
          coupling hcoupling hroots left right stage +
        (-couplingParametricStrictJointCenteredSequence
          coupling hcoupling base roots
          (centralStrictJointPairPredicate roots.length left right)
          stage)) ≤
      strictJointConditionalCenteredCoefficient
          (roots.length + roots.length) * HalfPow.half ^ stage := by
    simpa only [couplingParametricStrictJointGivenSlabSequence] using hpoint
  have hdifference :
      centralNormalizedStrictJointGramSequence
            coupling hcoupling base roots left right stage +
          (-couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots
            (centralStrictJointPairPredicate roots.length left right)
            stage) ≈
        couplingParametricStrictJointGivenSlabSequence
            coupling hcoupling hroots left right stage +
          (-couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots
            (centralStrictJointPairPredicate roots.length left right)
            stage) :=
    Q'.add_eqv_congr' hgram (Q'.eqv_refl _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) hgiven

def strictJointBaseTransportGramCoefficient
    (roots : List (List Nat)) : Q' :=
  strictJointConditionalCenteredCoefficient
      (roots.length + roots.length) +
    (strictJointBaseTransportCenteredCoefficient roots +
      strictJointConditionalCenteredCoefficient
        (roots.length + roots.length))

theorem strictJointBaseTransportGramCoefficient_nonnegative
    (roots : List (List Nat)) :
    (0 : Q') ≤ strictJointBaseTransportGramCoefficient roots := by
  unfold strictJointBaseTransportGramCoefficient
  exact Q'.zero_le_add _ _
    (strictJointConditionalCenteredCoefficient_nonnegative _)
    (Q'.zero_le_add _ _
      (strictJointBaseTransportCenteredCoefficient_nonnegative roots)
      (strictJointConditionalCenteredCoefficient_nonnegative _))

/-- Every literal strict Gram entry has a uniform same-index base-transport
modulus. -/
theorem centralNormalizedStrictJointGramSequence_base_transport_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (base padding stage : Nat) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    Q'.abs
        (centralNormalizedStrictJointGramSequence
            coupling hcoupling (base + padding)
            (transportedCylinderRoots base (base + padding) roots)
            left right stage +
          (-centralNormalizedStrictJointGramSequence
            coupling hcoupling base roots left right stage)) ≤
      strictJointBaseTransportGramCoefficient roots *
        HalfPow.half ^ stage := by
  have hbaseOuter : base ≤ base + padding :=
    Nat.le_add_right base padding
  have htransported := transportedCylinderRoots_canonical
    hbaseOuter hroots
  have htargetRaw :=
    centralNormalizedStrictJointGramSequence_to_centered_abs_le
      hcoupling hle htransported left right (stage := stage)
  have htarget : Q'.abs
      (centralNormalizedStrictJointGramSequence
          coupling hcoupling (base + padding)
          (transportedCylinderRoots base (base + padding) roots)
          left right stage +
        (-couplingParametricStrictJointCenteredSequence
          coupling hcoupling (base + padding)
          (transportedCylinderRoots base (base + padding) roots)
          (centralStrictJointPairPredicate roots.length left right)
          stage)) ≤
      strictJointConditionalCenteredCoefficient
          (roots.length + roots.length) * HalfPow.half ^ stage := by
    simpa only [transportedCylinderRoots, List.length_map] using htargetRaw
  have hcentered :=
    couplingParametricStrictJointCenteredSequence_base_transport_abs_le
      hcoupling hle base padding stage hroots
      (centralStrictJointPairPredicate roots.length left right)
  have hsourceRaw :=
    centralNormalizedStrictJointGramSequence_to_centered_abs_le
      hcoupling hle hroots left right (stage := stage)
  have hsource : Q'.abs
      (couplingParametricStrictJointCenteredSequence
          coupling hcoupling base roots
          (centralStrictJointPairPredicate roots.length left right) stage +
        (-centralNormalizedStrictJointGramSequence
          coupling hcoupling base roots left right stage)) ≤
      strictJointConditionalCenteredCoefficient
          (roots.length + roots.length) * HalfPow.half ^ stage := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          (couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots
            (centralStrictJointPairPredicate roots.length left right) stage)
          (centralNormalizedStrictJointGramSequence
            coupling hcoupling base roots left right stage)))
      hsourceRaw
  have hfirst := abs_sub_via_common_le htarget hcentered
  have hchain := abs_sub_via_common_le hfirst hsource
  let h := HalfPow.half ^ stage
  let conditional := strictJointConditionalCenteredCoefficient
    (roots.length + roots.length)
  let centered := strictJointBaseTransportCenteredCoefficient roots
  have hcoefficient :
      strictJointBaseTransportGramCoefficient roots * h ≈
        (conditional * h + centered * h) + conditional * h := by
    unfold strictJointBaseTransportGramCoefficient
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv conditional (centered + conditional) h) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_mul_eqv centered conditional h)) ?_
    exact Q'.eqv_symm
      (Q'.add_assoc_eqv (conditional * h) (centered * h)
        (conditional * h))
  change Q'.abs
      (centralNormalizedStrictJointGramSequence
          coupling hcoupling (base + padding)
          (transportedCylinderRoots base (base + padding) roots)
          left right stage +
        (-centralNormalizedStrictJointGramSequence
          coupling hcoupling base roots left right stage)) ≤
    strictJointBaseTransportGramCoefficient roots * h
  exact Q'.le_trans' _ _ _ hchain (Q'.ge_of_eqv hcoefficient)

/-! ## 2. Finite quadratic and constructive-real transport -/

def strictJointBaseTransportQuadraticCoefficient
    (roots : List (List Nat)) (coefficient : List Bool → Q') : Q' :=
  (coefficientL1 (strictJointFingerprintSpace roots.length) coefficient *
      coefficientL1 (strictJointFingerprintSpace roots.length) coefficient) *
    strictJointBaseTransportGramCoefficient roots

theorem strictJointBaseTransportQuadraticCoefficient_nonnegative
    (roots : List (List Nat)) (coefficient : List Bool → Q') :
    (0 : Q') ≤
      strictJointBaseTransportQuadraticCoefficient roots coefficient := by
  unfold strictJointBaseTransportQuadraticCoefficient
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (coefficientL1_nonnegative_local _ coefficient)
      (coefficientL1_nonnegative_local _ coefficient))
    (strictJointBaseTransportGramCoefficient_nonnegative roots)

theorem centralNormalizedStrictJointFixedQuadraticSequence_base_transport_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (base padding stage : Nat) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') :
    Q'.abs
        (centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling (base + padding)
            (transportedCylinderRoots base (base + padding) roots)
            coefficient stage +
          (-centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base roots coefficient stage)) ≤
      strictJointBaseTransportQuadraticCoefficient roots coefficient *
        HalfPow.half ^ stage := by
  let states := strictJointFingerprintSpace roots.length
  let error := strictJointBaseTransportGramCoefficient roots *
    HalfPow.half ^ stage
  have herror : (0 : Q') ≤ error :=
    Q'.mul_nonneg _ _
      (strictJointBaseTransportGramCoefficient_nonnegative roots)
      (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg stage)
  have hfinite := finiteJointQuadratic_abs_sub_le_square
    states coefficient
    (fun left right => centralNormalizedStrictJointGramSequence
      coupling hcoupling (base + padding)
      (transportedCylinderRoots base (base + padding) roots)
      left right stage)
    (fun left right => centralNormalizedStrictJointGramSequence
      coupling hcoupling base roots left right stage)
    error herror
    (fun left right _ _ =>
      centralNormalizedStrictJointGramSequence_base_transport_abs_le
        hcoupling hle base padding stage hroots left right)
  have hreorder :
      (coefficientL1 states coefficient * coefficientL1 states coefficient) *
          error ≈
        strictJointBaseTransportQuadraticCoefficient roots coefficient *
          HalfPow.half ^ stage := by
    unfold error strictJointBaseTransportQuadraticCoefficient
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (coefficientL1 states coefficient * coefficientL1 states coefficient)
        (strictJointBaseTransportGramCoefficient roots)
        (HalfPow.half ^ stage))
  have hbound := Q'.le_trans' _ _ _ hfinite (Q'.le_of_eqv hreorder)
  simpa only [centralNormalizedStrictJointFixedQuadraticSequence,
    transportedCylinderRoots, List.length_map] using hbound

/-- The limiting strict reflection quadratic is independent of canonical
source-box presentation. -/
theorem centralNormalizedStrictJointFixedQuadraticLimit_base_transport_equiv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (base padding : Nat) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') :
    CReal.Equiv
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle
        (transportedCylinderRoots_canonical
          (Nat.le_add_right base padding) hroots)
        coefficient)
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle hroots coefficient) := by
  let transportCoefficient :=
    strictJointBaseTransportQuadraticCoefficient roots coefficient
  have htransportCoefficient : (0 : Q') ≤ transportCoefficient :=
    strictJointBaseTransportQuadraticCoefficient_nonnegative roots coefficient
  intro epsilon hepsilon
  let scaledTolerance :=
    epsilon * Q'.invSucc transportCoefficient.num.toNat
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon
      (Q'.invSucc_pos transportCoefficient.num.toNat)
  have hscaledFinal : transportCoefficient * scaledTolerance ≤ epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat transportCoefficient epsilon
      htransportCoefficient (Q'.le_of_lt hepsilon)
  refine ⟨scaledTolerance.den, fun stage hstage => ?_⟩
  have hhalf : HalfPow.half ^ stage ≤
      HalfPow.half ^ scaledTolerance.den := by
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
    rw [hoffset]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (HalfPow.half ^ stage) scaledTolerance transportCoefficient
    (Q'.le_trans' _ _ _ hhalf hhalfTolerance) htransportCoefficient
  have hpoint :=
    centralNormalizedStrictJointFixedQuadraticSequence_base_transport_abs_le
      hcoupling hle base padding stage hroots coefficient
  have habs : Q'.abs
      ((centralNormalizedStrictJointFixedQuadraticLimit
          coupling hcoupling hle
          (transportedCylinderRoots_canonical
            (Nat.le_add_right base padding) hroots)
          coefficient).approx stage +
        (-(centralNormalizedStrictJointFixedQuadraticLimit
          coupling hcoupling hle hroots coefficient).approx stage)) ≤
      epsilon :=
    Q'.le_trans' _ _ _ hpoint
      (Q'.le_trans' _ _ _ hscaled hscaledFinal)
  exact two_sided_add_of_abs_sub_le habs

/-- Presentation-level form used by the doubled-time source vector. -/
theorem boxTransportStrictJointCylinderVector_reflectionQuadratic_equiv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (padding : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      ((boxTransportStrictJointCylinderVector
          (Nat.le_add_right base padding) vector).reflectionQuadratic
        hcoupling hle)
      (vector.reflectionQuadratic hcoupling hle) := by
  simpa only [StrictJointCylinderVector.reflectionQuadratic,
    boxTransportStrictJointCylinderVector_roots,
    boxTransportStrictJointCylinderVector_coefficient] using
    (centralNormalizedStrictJointFixedQuadraticLimit_base_transport_equiv
      hcoupling hle base padding vector.rootsCanonical vector.coefficient)

#print axioms couplingParametricStrictJointCenteredSequence_base_transport_abs_le
#print axioms centralNormalizedStrictJointGramSequence_to_centered_abs_le
#print axioms centralNormalizedStrictJointGramSequence_base_transport_abs_le
#print axioms centralNormalizedStrictJointFixedQuadraticSequence_base_transport_abs_le
#print axioms centralNormalizedStrictJointFixedQuadraticLimit_base_transport_equiv
#print axioms boxTransportStrictJointCylinderVector_reflectionQuadratic_equiv

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportLimit
