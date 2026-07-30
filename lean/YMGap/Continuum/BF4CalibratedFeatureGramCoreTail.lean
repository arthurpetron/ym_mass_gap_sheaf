/-
# Empty/nonempty feature decomposition of the calibrated BF4 Gram

The positive BF4 Mehler endpoint is a finite weighted Gram over ordered
kinetic-feature words.  Its empty word is a rank-one kernel; every genuine
cross feature lies in the complementary nonempty-word Gram.

This module splits the physically calibrated joint exactly into those two
pieces and proves the sharp row triangle

  rowAbs(calibratedJoint - pi tensor pi)
    <= rowAbs(emptyJoint - pi tensor pi)
       + rowAbs(nonemptyJoint).

Consequently two spacing-uniform `1/16` estimates imply the corrected
spectral `1/8`.  The split is exact and retains the factorial feature
weights, so subsequent Mehler decay can be proved directly on the
nonempty-word carrier.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalRecenteredEndpointRate

namespace YMGap.Continuum.BF4CalibratedFeatureGramCoreTail

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalRecenteredEndpointRate
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal empty/nonempty feature-word partition -/

/-- All nonempty ordered feature words of length at most `order`, preserving
the exact enumeration order of `bf4FeatureWordsAtMost`. -/
def bf4NonemptyFeatureWordsAtMost : Nat →
    List (List BF4KineticFeature)
  | 0 => []
  | order + 1 =>
      bf4NonemptyFeatureWordsAtMost order ++
        bf4FeatureWordsExact (order + 1)

/-- The complete feature carrier is the empty channel followed by the
nonempty carrier, definitionally at every finite order. -/
theorem bf4FeatureWordsAtMost_eq_empty_cons_nonempty :
    ∀ order,
      bf4FeatureWordsAtMost order =
        [] :: bf4NonemptyFeatureWordsAtMost order
  | 0 => rfl
  | order + 1 => by
      simp only [bf4FeatureWordsAtMost,
        bf4NonemptyFeatureWordsAtMost,
        bf4FeatureWordsAtMost_eq_empty_cons_nonempty order,
        List.cons_append]

/-! ## 2. Exact normalized Gram decomposition -/

/-- Empty-feature rank-one component of the normalized canonical Gram. -/
def normalizedBF4EmptyFeatureJoint
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) : Q' :=
  normalizedBF4FeatureWordWeight
      (shiftedDiagonalVacuumCertificate diagonalOrder)
      crossOrder [] *
    (bf4MehlerHalfAmplitude
        (diagonalOrder + 1) left [] *
      bf4MehlerHalfAmplitude
        (diagonalOrder + 1) right [])

/-- Nonempty-feature component of the normalized canonical Gram. -/
def normalizedBF4NonemptyFeatureJoint
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) : Q' :=
  weightedGram
    (bf4NonemptyFeatureWordsAtMost crossOrder)
    (normalizedBF4FeatureWordWeight
      (shiftedDiagonalVacuumCertificate diagonalOrder)
      crossOrder)
    (bf4MehlerHalfAmplitude (diagonalOrder + 1))
    left right

/-- Exact empty/nonempty decomposition of every normalized Gram entry. -/
theorem normalizedBF4MehlerGramJoint_eqv_empty_add_nonempty
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) :
    normalizedBF4MehlerGramJoint
        diagonalOrder crossOrder left right ≈
      normalizedBF4EmptyFeatureJoint
          diagonalOrder crossOrder left right +
        normalizedBF4NonemptyFeatureJoint
          diagonalOrder crossOrder left right := by
  refine Q'.eqv_trans _ _ _
    (normalized_bf4MehlerGram_entry_eqv
      (shiftedDiagonalVacuumCertificate diagonalOrder)
      crossOrder left right) ?_
  rw [bf4FeatureWordsAtMost_eq_empty_cons_nonempty]
  exact Q'.eqv_refl _

/-! ## 3. Physical square calibration of both components -/

/-- Empty-feature component after multiplication by the exact physical
vacuum square. -/
def calibratedBF4EmptyFeatureJoint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) : Q' :=
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  (pi0 * pi0) *
    normalizedBF4EmptyFeatureJoint
      diagonalOrder crossOrder left right

/-- Nonempty-feature component after the same physical vacuum-square
calibration. -/
def calibratedBF4NonemptyFeatureJoint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) : Q' :=
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  (pi0 * pi0) *
    normalizedBF4NonemptyFeatureJoint
      diagonalOrder crossOrder left right

/-- The physically recentered endpoint joint is exactly the calibrated
empty rank-one component plus the calibrated nonempty feature Gram. -/
theorem physicallyRecenteredJoint_eqv_empty_add_nonempty
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) :
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder).joint
        left right ≈
      calibratedBF4EmptyFeatureJoint
          w hw K halfExtent diagonalOrder crossOrder
          left right +
        calibratedBF4NonemptyFeatureJoint
          w hw K halfExtent diagonalOrder crossOrder
          left right := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  refine Q'.eqv_trans _ _ _
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_joint_eqv_scaled
      w hw K halfExtent diagonalOrder crossOrder
      left right) ?_
  refine Q'.eqv_trans _
    ((pi0 * pi0) *
      (normalizedBF4EmptyFeatureJoint
          diagonalOrder crossOrder left right +
        normalizedBF4NonemptyFeatureJoint
          diagonalOrder crossOrder left right)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left
      (pi0 * pi0) _ _
      (normalizedBF4MehlerGramJoint_eqv_empty_add_nonempty
        diagonalOrder crossOrder left right)
  · unfold calibratedBF4EmptyFeatureJoint
      calibratedBF4NonemptyFeatureJoint
    exact Q'.mul_add_eqv
      (pi0 * pi0)
      (normalizedBF4EmptyFeatureJoint
        diagonalOrder crossOrder left right)
      (normalizedBF4NonemptyFeatureJoint
        diagonalOrder crossOrder left right)

/-! ## 4. Row triangle and the two sixteenths -/

/-- Row mismatch of the calibrated empty feature against the exact physical
rank-one Perron joint. -/
def calibratedEmptyPhysicalMismatchRowMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) : Q' :=
  finiteJointDifferenceAbsRowMass
    (centralPositiveHalfStates w hw K halfExtent)
    (calibratedBF4EmptyFeatureJoint
      w hw K halfExtent diagonalOrder crossOrder)
    (centralPhysicalVacuumJoint
      w hw K halfExtent)
    source

/-- Absolute row mass of the calibrated nonempty feature Gram. -/
def calibratedNonemptyFeatureAbsRowMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      Q'.abs
        (calibratedBF4NonemptyFeatureJoint
          w hw K halfExtent diagonalOrder crossOrder
          source target))
    (centralPositiveHalfStates w hw K halfExtent)

/-- Exact row triangle for the physical-centered calibrated endpoint. -/
theorem physicalCenteredEndpointRowMass_le_emptyMismatch_add_nonempty
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) :
    physicalCenteredEndpointRowMass
        (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder crossOrder)
        source ≤
      calibratedEmptyPhysicalMismatchRowMass
          w hw K halfExtent diagonalOrder crossOrder source +
        calibratedNonemptyFeatureAbsRowMass
          w hw K halfExtent diagonalOrder crossOrder source := by
  let states :=
    centralPositiveHalfStates w hw K halfExtent
  let oldEndpoint :=
    vacuumCalibratedExactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder crossOrder
  let emptyJoint :=
    calibratedBF4EmptyFeatureJoint
      w hw K halfExtent diagonalOrder crossOrder
  let tailJoint :=
    calibratedBF4NonemptyFeatureJoint
      w hw K halfExtent diagonalOrder crossOrder
  let vacuum :=
    centralPhysicalVacuumJoint
      w hw K halfExtent
  let emptyDifference := fun target =>
    Q'.abs
      (emptyJoint source target +
        (-vacuum source target))
  let tailAbs := fun target =>
    Q'.abs (tailJoint source target)
  have hentry :
      ∀ target,
        Q'.abs
            (oldEndpoint.joint source target +
              (-vacuum source target)) ≤
          emptyDifference target + tailAbs target := by
    intro target
    have holdToRecentered :
        oldEndpoint.joint source target ≈
          (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
            w hw K halfExtent diagonalOrder crossOrder).joint
            source target :=
      Q'.eqv_symm
        (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_joint
          w hw K halfExtent diagonalOrder crossOrder
          source target)
    have hjoint :
        oldEndpoint.joint source target ≈
          emptyJoint source target +
            tailJoint source target :=
      Q'.eqv_trans _ _ _
        holdToRecentered
        (physicallyRecenteredJoint_eqv_empty_add_nonempty
          w hw K halfExtent diagonalOrder crossOrder
          source target)
    have hdifference :
        oldEndpoint.joint source target +
            (-vacuum source target) ≈
          (emptyJoint source target +
              (-vacuum source target)) +
            tailJoint source target := by
      refine Q'.eqv_trans _
        ((emptyJoint source target +
            tailJoint source target) +
          (-vacuum source target)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          hjoint
      · calc
          (emptyJoint source target +
                tailJoint source target) +
              (-vacuum source target) ≈
              emptyJoint source target +
                (tailJoint source target +
                  (-vacuum source target)) :=
            Q'.add_assoc_eqv _ _ _
          _ ≈ emptyJoint source target +
                ((-vacuum source target) +
                  tailJoint source target) :=
            Q'.add_eqv_congr_left _ _ _
              (Q'.add_comm_eqv _ _)
          _ ≈ (emptyJoint source target +
                (-vacuum source target)) +
                  tailJoint source target :=
            Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr hdifference))
      (Q'.abs_add_le'
        (emptyJoint source target +
          (-vacuum source target))
        (tailJoint source target))
  unfold physicalCenteredEndpointRowMass
    finiteJointDifferenceAbsRowMass
  refine Q'.le_trans' _ _ _
    (listQSum_mono
      (fun target =>
        Q'.abs
          (oldEndpoint.joint source target +
            (-vacuum source target)))
      (fun target =>
        emptyDifference target + tailAbs target)
      states
      (fun target _ => hentry target)) ?_
  unfold calibratedEmptyPhysicalMismatchRowMass
    calibratedNonemptyFeatureAbsRowMass
    finiteJointDifferenceAbsRowMass
    emptyDifference tailAbs emptyJoint tailJoint
    vacuum states
  exact Q'.le_of_eqv
    (listQSum_add _ _ _)

/-- Two row-relative bounds add without a carrier loss. -/
theorem physicalCenteredEndpointRowMass_le_of_core_tail
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    {source : EdgeLabelling}
    (core tail : Q')
    (hcore :
      calibratedEmptyPhysicalMismatchRowMass
          w hw K halfExtent diagonalOrder crossOrder source ≤
        core *
          centralPhysicalRowMarginal
            w hw K halfExtent source)
    (htail :
      calibratedNonemptyFeatureAbsRowMass
          w hw K halfExtent diagonalOrder crossOrder source ≤
        tail *
          centralPhysicalRowMarginal
            w hw K halfExtent source) :
    physicalCenteredEndpointRowMass
        (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder crossOrder)
        source ≤
      (core + tail) *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  exact Q'.le_trans' _ _ _
    (physicalCenteredEndpointRowMass_le_emptyMismatch_add_nonempty
      w hw K halfExtent diagonalOrder crossOrder source)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add hcore htail)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.add_mul_eqv core tail
            (centralPhysicalRowMarginal
              w hw K halfExtent source)))))

/-- A `1/16` empty-channel matching bound and a `1/16` nonempty-feature
tail bound prove the corrected spectral row `1/8`. -/
theorem physicalCenteredEndpointRowMass_le_eighth_of_sixteenths
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    {source : EdgeLabelling}
    (hcore :
      calibratedEmptyPhysicalMismatchRowMass
          w hw K halfExtent diagonalOrder crossOrder source ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K halfExtent source)
    (htail :
      calibratedNonemptyFeatureAbsRowMass
          w hw K halfExtent diagonalOrder crossOrder source ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K halfExtent source) :
    physicalCenteredEndpointRowMass
        (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder crossOrder)
        source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  exact Q'.le_trans' _ _ _
    (physicalCenteredEndpointRowMass_le_of_core_tail
      (Q'.mkPos 1 16 (by decide))
      (Q'.mkPos 1 16 (by decide))
      hcore htail)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.le_of_eqv (by decide))
      (centralPhysicalRowMarginal_nonnegative
        hw K halfExtent source))

end YMGap.Continuum.BF4CalibratedFeatureGramCoreTail

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CalibratedFeatureGramCoreTail.bf4FeatureWordsAtMost_eq_empty_cons_nonempty
#print axioms YMGap.Continuum.BF4CalibratedFeatureGramCoreTail.normalizedBF4MehlerGramJoint_eqv_empty_add_nonempty
#print axioms YMGap.Continuum.BF4CalibratedFeatureGramCoreTail.physicallyRecenteredJoint_eqv_empty_add_nonempty
#print axioms YMGap.Continuum.BF4CalibratedFeatureGramCoreTail.physicalCenteredEndpointRowMass_le_emptyMismatch_add_nonempty
#print axioms YMGap.Continuum.BF4CalibratedFeatureGramCoreTail.physicalCenteredEndpointRowMass_le_eighth_of_sixteenths
