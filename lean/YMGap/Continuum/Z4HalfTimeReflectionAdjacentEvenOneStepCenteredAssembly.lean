/-
# Common-chart finite assembly for the one-step reflection cross

Arbitrary strict-cylinder presentations are first co-presented on the append
of their root lists.  The transported source and translated target then use
the same one-step root chart, so every finite reflection entry is controlled
by the centered-pair bridge.  The resulting finite L1 estimate identifies
each one-sided reflection cross with its constructive-real pair-limit
assembly.

This file does not yet use swap symmetry; it builds the two honest LR and RL
adapters over one fixed common chart.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEntryCenteredBridge
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointPolarizedDoubledTimeIdentity

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepCenteredAssembly

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEntryCenteredBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepLimitSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointPolarizedDoubledTimeIdentity
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One root chart with arbitrary coefficient tables -/

def adjacentEvenOneStepCommonVector
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') : StrictJointCylinderVector base where
  roots := roots
  rootsCanonical := hroots
  coefficient := coefficient

def adjacentEvenOneStepCommonCross
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') : CReal :=
  strictJointCylinderReflectionBilinear hcoupling hle
    (boxTransportStrictJointCylinderVector
      (Nat.le_add_right base 1)
      (adjacentEvenOneStepCommonVector hroots leftCoefficient))
    (timeTranslateStrictJointCylinderVector 1
      (adjacentEvenOneStepCommonVector hroots rightCoefficient))

/-- The CReal finite cross assembled from the one-step centered pair limits. -/
def adjacentEvenOneStepCenteredBilinear
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') : CReal :=
  listCRealSum
    (fun left => listCRealSum
      (fun right => CReal.mul
        (CReal.ofQ' (leftCoefficient left * rightCoefficient right))
        (couplingParametricAdjacentEvenOneStepCenteredPairLimit
          coupling hcoupling hle hroots left right))
      (strictJointFingerprintSpace roots.length))
    (strictJointFingerprintSpace roots.length)

theorem adjacentEvenOneStepCenteredBilinear_approx_eqv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    (adjacentEvenOneStepCenteredBilinear
        coupling hcoupling hle hroots
        leftCoefficient rightCoefficient).approx stage ≈
      finiteHeterogeneousCrossBilinear
        (strictJointFingerprintSpace roots.length)
        (strictJointFingerprintSpace roots.length)
        leftCoefficient rightCoefficient
        (fun left right =>
          couplingParametricAdjacentEvenOneStepCenteredPairSequence
            coupling hcoupling base roots left right stage) := by
  unfold adjacentEvenOneStepCenteredBilinear
    finiteHeterogeneousCrossBilinear
  rw [listCRealSum_approx]
  apply listQSum_congr
  intro left
  rw [listCRealSum_approx]
  apply listQSum_congr
  intro right
  exact Q'.eqv_refl _

/-! ## 2. Exact finite support expansion -/

theorem adjacentEvenOneStepCommonReflectionBilinearSequence_eqv_entries
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q')
    (stage : Nat) :
    strictJointCylinderReflectionBilinearSequence
        coupling hcoupling
        (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base 1)
          (adjacentEvenOneStepCommonVector hroots leftCoefficient))
        (timeTranslateStrictJointCylinderVector 1
          (adjacentEvenOneStepCommonVector hroots rightCoefficient))
        stage ≈
      finiteHeterogeneousCrossBilinear
        (strictJointFingerprintSpace roots.length)
        (strictJointFingerprintSpace roots.length)
        leftCoefficient rightCoefficient
        (fun left right =>
          adjacentEvenOneStepEntrySequence
            coupling hcoupling base roots left right stage) := by
  let outer := base + 1
  let radius := strictQueryBase outer + stage
  let source := boxTransportStrictJointCylinderVector
    (Nat.le_add_right base 1)
    (adjacentEvenOneStepCommonVector hroots leftCoefficient)
  let target := timeTranslateStrictJointCylinderVector 1
    (adjacentEvenOneStepCommonVector hroots rightCoefficient)
  let leftCode := centralStrictLocalQueryCode radius outer source.roots
  let rightCode := centralStrictLocalQueryCode radius outer target.roots
  have hsourceLength : source.roots.length = roots.length := by
    simp only [source, adjacentEvenOneStepCommonVector,
      boxTransportStrictJointCylinderVector_roots,
      transportedCylinderRoots, List.length_map]
  have htargetLength : target.roots.length = roots.length := by
    simp only [target, adjacentEvenOneStepCommonVector,
      timeTranslateStrictJointCylinderVector_roots, List.length_map]
  have hleft : ∀ support, support ∈ centralHalfSupportSpace radius →
      leftCode support ∈ strictJointFingerprintSpace roots.length := by
    intro support hsupport
    rw [← hsourceLength]
    exact centralStrictLocalQueryCode_mem_fixedSpace
      radius outer source.roots support
  have hright : ∀ support, support ∈ centralHalfSupportSpace radius →
      rightCode support ∈ strictJointFingerprintSpace roots.length := by
    intro support hsupport
    rw [← htargetLength]
    exact centralStrictLocalQueryCode_mem_fixedSpace
      radius outer target.roots support
  have hfinite :=
    centralNormalizedSupportReflectionBilinear_eqv_heterogeneousBipair
      coupling hcoupling
      (centralStrictJointCenteredStageCutoff outer stage) radius
      leftCode rightCode
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace_nodup roots.length)
      (strictJointFingerprintSpace_nodup roots.length)
      hleft hright leftCoefficient rightCoefficient
  simpa only [strictJointCylinderReflectionBilinearSequence,
    centralLocalSupportCoefficient,
    centralNormalizedSupportHeterogeneousBipairLaw,
    centralNormalizedSupportBipairLaw,
    finiteJointKernelHeterogeneousBipushforward,
    finiteJointKernelBipushforward,
    adjacentEvenOneStepEntrySequence,
    adjacentEvenOneStepCommonVector,
    boxTransportStrictJointCylinderVector_roots,
    boxTransportStrictJointCylinderVector_coefficient,
    timeTranslateStrictJointCylinderVector_roots,
    timeTranslateStrictJointCylinderVector_coefficient,
    outer, radius, source, target, leftCode, rightCode] using hfinite

/-! ## 3. Finite L1 comparison and constructive-real closure -/

def adjacentEvenOneStepComparisonCoefficient
    {base : Nat} {roots : List (List Nat)}
    (leftCoefficient rightCoefficient : List Bool → Q') : Q' :=
  heterogeneousCoefficientPairL1
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace roots.length)
      leftCoefficient rightCoefficient *
    strictJointConditionalCenteredCoefficient
      ((adjacentEvenOneStepProjectedRoots base roots).length +
        (adjacentEvenOneStepProjectedRoots base roots).length)

theorem adjacentEvenOneStepComparisonCoefficient_nonnegative
    {base : Nat} {roots : List (List Nat)}
    (leftCoefficient rightCoefficient : List Bool → Q') :
    (0 : Q') ≤ adjacentEvenOneStepComparisonCoefficient
      (base := base) (roots := roots)
      leftCoefficient rightCoefficient := by
  unfold adjacentEvenOneStepComparisonCoefficient
  exact Q'.mul_nonneg _ _
    (heterogeneousCoefficientPairL1_nonnegative
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace roots.length)
      leftCoefficient rightCoefficient)
    (strictJointConditionalCenteredCoefficient_nonnegative
      ((adjacentEvenOneStepProjectedRoots base roots).length +
        (adjacentEvenOneStepProjectedRoots base roots).length))

theorem adjacentEvenOneStepCommonCross_abs_sub_centeredBilinear_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q')
    (stage : Nat) :
    Q'.abs
        ((adjacentEvenOneStepCommonCross
              hcoupling hle hroots
              leftCoefficient rightCoefficient).approx stage -
          (adjacentEvenOneStepCenteredBilinear
              coupling hcoupling hle hroots
              leftCoefficient rightCoefficient).approx stage) ≤
      adjacentEvenOneStepComparisonCoefficient
          (base := base) (roots := roots)
          leftCoefficient rightCoefficient *
        HalfPow.half ^ stage := by
  let states := strictJointFingerprintSpace roots.length
  let entryCoefficient := strictJointConditionalCenteredCoefficient
    ((adjacentEvenOneStepProjectedRoots base roots).length +
      (adjacentEvenOneStepProjectedRoots base roots).length)
  let directLaw : List Bool → List Bool → Q' := fun left right =>
    adjacentEvenOneStepEntrySequence
      coupling hcoupling base roots left right stage
  let centeredLaw : List Bool → List Bool → Q' := fun left right =>
    couplingParametricAdjacentEvenOneStepCenteredPairSequence
      coupling hcoupling base roots left right stage
  have hbilinear :
      (adjacentEvenOneStepCommonCross hcoupling hle hroots
          leftCoefficient rightCoefficient).approx stage ≈
        strictJointCylinderReflectionBilinearSequence
          coupling hcoupling
          (boxTransportStrictJointCylinderVector
            (Nat.le_add_right base 1)
            (adjacentEvenOneStepCommonVector hroots leftCoefficient))
          (timeTranslateStrictJointCylinderVector 1
            (adjacentEvenOneStepCommonVector hroots rightCoefficient))
          stage := by
    simpa only [adjacentEvenOneStepCommonCross] using
      (StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
        hcoupling hle
        (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base 1)
          (adjacentEvenOneStepCommonVector hroots leftCoefficient))
        (timeTranslateStrictJointCylinderVector 1
          (adjacentEvenOneStepCommonVector hroots rightCoefficient))
        (stage := stage))
  have hentries :
      strictJointCylinderReflectionBilinearSequence
          coupling hcoupling
          (boxTransportStrictJointCylinderVector
            (Nat.le_add_right base 1)
            (adjacentEvenOneStepCommonVector hroots leftCoefficient))
          (timeTranslateStrictJointCylinderVector 1
            (adjacentEvenOneStepCommonVector hroots rightCoefficient))
          stage ≈
        finiteHeterogeneousCrossBilinear
          states states leftCoefficient rightCoefficient directLaw := by
    simpa only [states, directLaw] using
      (adjacentEvenOneStepCommonReflectionBilinearSequence_eqv_entries
        hcoupling hroots leftCoefficient rightCoefficient stage)
  have hleft :
      (adjacentEvenOneStepCommonCross hcoupling hle hroots
          leftCoefficient rightCoefficient).approx stage ≈
        finiteHeterogeneousCrossBilinear
          states states leftCoefficient rightCoefficient directLaw :=
    Q'.eqv_trans _ _ _ hbilinear hentries
  have hright :
      (adjacentEvenOneStepCenteredBilinear
          coupling hcoupling hle hroots
          leftCoefficient rightCoefficient).approx stage ≈
        finiteHeterogeneousCrossBilinear
          states states leftCoefficient rightCoefficient centeredLaw := by
    simpa only [states, centeredLaw] using
      (adjacentEvenOneStepCenteredBilinear_approx_eqv
        hcoupling hle hroots leftCoefficient rightCoefficient
        (stage := stage))
  have hentry : ∀ left right,
      left ∈ states → right ∈ states →
      Q'.abs (directLaw left right + (-centeredLaw left right)) ≤
        entryCoefficient * HalfPow.half ^ stage := by
    intro left right hleftMem hrightMem
    simpa only [directLaw, centeredLaw, entryCoefficient] using
      (adjacentEvenOneStepEntrySequence_abs_sub_centeredPair_le
        hcoupling hle hroots left right stage)
  have hfinite :
      Q'.abs
          (finiteHeterogeneousCrossBilinear
              states states leftCoefficient rightCoefficient directLaw +
            (-finiteHeterogeneousCrossBilinear
              states states leftCoefficient rightCoefficient centeredLaw)) ≤
        heterogeneousCoefficientPairL1
            states states leftCoefficient rightCoefficient *
          (entryCoefficient * HalfPow.half ^ stage) :=
    finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1
      states states leftCoefficient rightCoefficient
      directLaw centeredLaw
      (entryCoefficient * HalfPow.half ^ stage) hentry
  have hdifference :
      (adjacentEvenOneStepCommonCross hcoupling hle hroots
            leftCoefficient rightCoefficient).approx stage +
          (-(adjacentEvenOneStepCenteredBilinear
            coupling hcoupling hle hroots
            leftCoefficient rightCoefficient).approx stage) ≈
        finiteHeterogeneousCrossBilinear
            states states leftCoefficient rightCoefficient directLaw +
          (-finiteHeterogeneousCrossBilinear
            states states leftCoefficient rightCoefficient centeredLaw) :=
    Q'.add_eqv_congr' hleft
      (Q'.neg_eqv_congr _ _ hright)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (Q'.le_trans' _ _ _ hfinite ?_)
  apply Q'.le_of_eqv
  simpa only [adjacentEvenOneStepComparisonCoefficient,
    states, entryCoefficient] using
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (heterogeneousCoefficientPairL1
          states states leftCoefficient rightCoefficient)
        entryCoefficient (HalfPow.half ^ stage)))

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

private theorem creal_equiv_of_abs_sub_le_half_pow
    (left right : CReal) (bound : Q')
    (hbound : (0 : Q') ≤ bound)
    (hpointwise : ∀ stage : Nat,
      Q'.abs (left.approx stage - right.approx stage) ≤
        bound * HalfPow.half ^ stage) :
    CReal.Equiv left right := by
  intro epsilon hepsilon
  let scaledTolerance := epsilon * Q'.invSucc bound.num.toNat
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon (Q'.invSucc_pos bound.num.toNat)
  have hscaledFinal : bound * scaledTolerance ≤ epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat bound epsilon
      hbound (Q'.le_of_lt hepsilon)
  refine ⟨scaledTolerance.den, fun stage hstage => ?_⟩
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
  have hhalf : HalfPow.half ^ stage ≤
      HalfPow.half ^ scaledTolerance.den := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hscaled : bound * HalfPow.half ^ stage ≤
      bound * scaledTolerance :=
    Q'.mul_le_mul_of_nonneg_left _ _ bound
      (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hbound
  have habs : Q'.abs (left.approx stage - right.approx stage) ≤ epsilon :=
    Q'.le_trans' _ _ _ (hpointwise stage)
      (Q'.le_trans' _ _ _ hscaled hscaledFinal)
  exact two_sided_add_of_abs_sub_le_local habs

theorem adjacentEvenOneStepCommonCross_equiv_centeredBilinear
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    CReal.Equiv
      (adjacentEvenOneStepCommonCross
        hcoupling hle hroots leftCoefficient rightCoefficient)
      (adjacentEvenOneStepCenteredBilinear
        coupling hcoupling hle hroots
        leftCoefficient rightCoefficient) :=
  creal_equiv_of_abs_sub_le_half_pow
    (adjacentEvenOneStepCommonCross
      hcoupling hle hroots leftCoefficient rightCoefficient)
    (adjacentEvenOneStepCenteredBilinear
      coupling hcoupling hle hroots
      leftCoefficient rightCoefficient)
    (adjacentEvenOneStepComparisonCoefficient
      (base := base) (roots := roots)
      leftCoefficient rightCoefficient)
    (adjacentEvenOneStepComparisonCoefficient_nonnegative
      (base := base) (roots := roots)
      leftCoefficient rightCoefficient)
    (adjacentEvenOneStepCommonCross_abs_sub_centeredBilinear_le
      hcoupling hle hroots leftCoefficient rightCoefficient)

/-! ## 4. Arbitrary presentations on one fixed append chart -/

def adjacentEvenOneStepAppendRoots
    {base : Nat} (left right : StrictJointCylinderVector base) :
    List (List Nat) :=
  left.roots ++ right.roots

theorem adjacentEvenOneStepAppendRoots_canonical
    {base : Nat} (left right : StrictJointCylinderVector base) :
    ∀ root, root ∈ adjacentEvenOneStepAppendRoots left right →
      root ∈ canonicalSurfacePolymers base :=
  canonicalRoots_append left.rootsCanonical right.rootsCanonical

def adjacentEvenOneStepAppendLeftCoefficient
    {base : Nat} (left _right : StrictJointCylinderVector base)
    (bits : List Bool) : Q' :=
  left.coefficient
    (leftAppendStrictJointFingerprint left.roots.length bits)

def adjacentEvenOneStepAppendRightCoefficient
    {base : Nat} (left right : StrictJointCylinderVector base)
    (bits : List Bool) : Q' :=
  right.coefficient
    (rightAppendStrictJointFingerprint left.roots.length bits)

private theorem boxTransport_appendLeft_equivalent
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (boxTransportStrictJointCylinderVector
        (Nat.le_add_right base 1) left)
      (boxTransportStrictJointCylinderVector
        (Nat.le_add_right base 1)
        (adjacentEvenOneStepCommonVector
          (adjacentEvenOneStepAppendRoots_canonical left right)
          (adjacentEvenOneStepAppendLeftCoefficient left right))) := by
  intro radius support
  apply Q'.eqv_of_eq
  apply congrArg left.coefficient
  have hcode :=
    strictJointFingerprintRecoding_append_left
      (base + 1)
      (transportedCylinderRoots base (base + 1) left.roots)
      (transportedCylinderRoots base (base + 1) right.roots)
      radius support
  simpa only [adjacentEvenOneStepCommonVector,
    adjacentEvenOneStepAppendRoots,
    adjacentEvenOneStepAppendLeftCoefficient,
    boxTransportStrictJointCylinderVector_roots,
    boxTransportStrictJointCylinderVector_coefficient,
    transportedCylinderRoots, List.map_append, List.length_map] using hcode

private theorem boxTransport_appendRight_equivalent
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (boxTransportStrictJointCylinderVector
        (Nat.le_add_right base 1) right)
      (boxTransportStrictJointCylinderVector
        (Nat.le_add_right base 1)
        (adjacentEvenOneStepCommonVector
          (adjacentEvenOneStepAppendRoots_canonical left right)
          (adjacentEvenOneStepAppendRightCoefficient left right))) := by
  intro radius support
  apply Q'.eqv_of_eq
  apply congrArg right.coefficient
  have hcode :=
    strictJointFingerprintRecoding_append_right
      (base + 1)
      (transportedCylinderRoots base (base + 1) left.roots)
      (transportedCylinderRoots base (base + 1) right.roots)
      radius support
  simpa only [adjacentEvenOneStepCommonVector,
    adjacentEvenOneStepAppendRoots,
    adjacentEvenOneStepAppendRightCoefficient,
    boxTransportStrictJointCylinderVector_roots,
    boxTransportStrictJointCylinderVector_coefficient,
    transportedCylinderRoots, List.map_append, List.length_map] using hcode

private theorem timeTranslate_appendLeft_equivalent
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (timeTranslateStrictJointCylinderVector 1 left)
      (timeTranslateStrictJointCylinderVector 1
        (adjacentEvenOneStepCommonVector
          (adjacentEvenOneStepAppendRoots_canonical left right)
          (adjacentEvenOneStepAppendLeftCoefficient left right))) := by
  intro radius support
  apply Q'.eqv_of_eq
  apply congrArg left.coefficient
  have hcode :=
    strictJointFingerprintRecoding_append_left
      (base + 1)
      (left.roots.map (timeShiftCanonicalRoot 1 base))
      (right.roots.map (timeShiftCanonicalRoot 1 base))
      radius support
  simpa only [adjacentEvenOneStepCommonVector,
    adjacentEvenOneStepAppendRoots,
    adjacentEvenOneStepAppendLeftCoefficient,
    timeTranslateStrictJointCylinderVector_roots,
    timeTranslateStrictJointCylinderVector_coefficient,
    List.map_append, List.length_map] using hcode

private theorem timeTranslate_appendRight_equivalent
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (timeTranslateStrictJointCylinderVector 1 right)
      (timeTranslateStrictJointCylinderVector 1
        (adjacentEvenOneStepCommonVector
          (adjacentEvenOneStepAppendRoots_canonical left right)
          (adjacentEvenOneStepAppendRightCoefficient left right))) := by
  intro radius support
  apply Q'.eqv_of_eq
  apply congrArg right.coefficient
  have hcode :=
    strictJointFingerprintRecoding_append_right
      (base + 1)
      (left.roots.map (timeShiftCanonicalRoot 1 base))
      (right.roots.map (timeShiftCanonicalRoot 1 base))
      radius support
  simpa only [adjacentEvenOneStepCommonVector,
    adjacentEvenOneStepAppendRoots,
    adjacentEvenOneStepAppendRightCoefficient,
    timeTranslateStrictJointCylinderVector_roots,
    timeTranslateStrictJointCylinderVector_coefficient,
    List.map_append, List.length_map] using hcode

theorem strictJointOneSidedTimeCross_one_equiv_appendForward
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointOneSidedTimeCross hcoupling hle 1 left right)
      (adjacentEvenOneStepCenteredBilinear
        coupling hcoupling hle
        (adjacentEvenOneStepAppendRoots_canonical left right)
        (adjacentEvenOneStepAppendLeftCoefficient left right)
        (adjacentEvenOneStepAppendRightCoefficient left right)) := by
  have hpresentation :=
    StrictJointCylinderVector.reflectionBilinear_equiv
      hcoupling hle
      (boxTransport_appendLeft_equivalent left right)
      (timeTranslate_appendRight_equivalent left right)
  exact CReal.Equiv.trans
    (by simpa only [strictJointOneSidedTimeCross] using hpresentation)
    (adjacentEvenOneStepCommonCross_equiv_centeredBilinear
      hcoupling hle
      (adjacentEvenOneStepAppendRoots_canonical left right)
      (adjacentEvenOneStepAppendLeftCoefficient left right)
      (adjacentEvenOneStepAppendRightCoefficient left right))

theorem strictJointOneSidedTimeCross_one_equiv_appendReverse
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointOneSidedTimeCross hcoupling hle 1 right left)
      (adjacentEvenOneStepCenteredBilinear
        coupling hcoupling hle
        (adjacentEvenOneStepAppendRoots_canonical left right)
        (adjacentEvenOneStepAppendRightCoefficient left right)
        (adjacentEvenOneStepAppendLeftCoefficient left right)) := by
  have hpresentation :=
    StrictJointCylinderVector.reflectionBilinear_equiv
      hcoupling hle
      (boxTransport_appendRight_equivalent left right)
      (timeTranslate_appendLeft_equivalent left right)
  exact CReal.Equiv.trans
    (by simpa only [strictJointOneSidedTimeCross] using hpresentation)
    (adjacentEvenOneStepCommonCross_equiv_centeredBilinear
      hcoupling hle
      (adjacentEvenOneStepAppendRoots_canonical left right)
      (adjacentEvenOneStepAppendRightCoefficient left right)
      (adjacentEvenOneStepAppendLeftCoefficient left right))

#print axioms adjacentEvenOneStepCenteredBilinear_approx_eqv
#print axioms adjacentEvenOneStepCommonReflectionBilinearSequence_eqv_entries
#print axioms adjacentEvenOneStepComparisonCoefficient_nonnegative
#print axioms adjacentEvenOneStepCommonCross_abs_sub_centeredBilinear_le
#print axioms adjacentEvenOneStepCommonCross_equiv_centeredBilinear
#print axioms strictJointOneSidedTimeCross_one_equiv_appendForward
#print axioms strictJointOneSidedTimeCross_one_equiv_appendReverse

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepCenteredAssembly
