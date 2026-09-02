/-
# Same-object OS clustering on the explicit coupling corridor

The exact face-event/Markov-form identification and OS positivity are already
valid at every positive coupling.  The new paired-support theorem supplies
their previously missing uniform geometric upper bound on the whole corridor

  0 < w <= 1/400.

This module transports that bound first to the literal same-object reflected
face moment, then through the representation-cutoff CReal limit, and finally
through the receding-slab family.  For every fixed rational coupling in the
corridor the bottom-face connected autocorrelation converges constructively
to zero with the same explicit dyadic modulus as at the production point.

This is still a family of finite-slab conditional operators at fixed lattice
spacing.  It does not identify them as powers of one common time-translation
operator, transport a beta/lattice-spacing trajectory, construct the
thermodynamic or continuum measure, or prove a physical mass gap.

Constructive contract: the generic same-object OS bridge, the proved corridor
covariance, Bishop-real cutoff limits, and exact rational geometry only; no
choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration, or
new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservableFaceRecedingVolumeClustering
import YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay

namespace YMGap.Continuum.CompactDualSlabObservableFaceCouplingCorridorClustering

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffConnectedLimit
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableFaceEventLaw
open YMGap.Continuum.CompactDualSlabObservableFaceRecedingVolumeClustering
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite-cutoff same-object OS interval -/

/-- The physical event-law covariance inherits the corridor bound from its
literal observable-carrier presentation. -/
theorem slabPhysicalFaceBooleanCovariance_le_couplingCorridorRate
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hwAnchor : D.coupling <= anchorCoupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabPhysicalFaceBooleanCovariance D rootFaceId targetFaceId <=
      slabObservablePairedSupportGlobalAnchorRate
        D rootFaceId targetFaceId := by
  have hphysical := slabObservableFaceBooleanCovariance_eqv_physical
    D rootFaceId targetFaceId
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hphysical))
    (slabObservableFaceBooleanCovariance_le_corridorRate
      D hw0 hw1 hwAnchor rootFaceId targetFaceId htarget)

/-- The literal same-object reflected face moment is nonnegative by OS
positivity and has the common geometric upper envelope on the corridor. -/
theorem slabPhysicalReflectedFaceSameObject_couplingCorridor_interval
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hwAnchor : D.coupling <= anchorCoupling)
    (rootFaceId : Nat)
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half) :
    (0 : Q') <=
        slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId ∧
      slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId <=
        slabObservablePairedSupportGlobalAnchorRate
          D rootFaceId (slabFaceReflectId D.extent rootFaceId) := by
  have hrootPhysical := (mem_centralLowerFaceIds.mp hroot).1
  have htarget := slabFaceReflectId_physical hrootPhysical
  have heq := slabPhysicalReflectedFaceBooleanCovariance_eqv_sameObject
    D hroot
  constructor
  · exact Q'.le_trans' _ _ _
      (slabPhysicalReflectedFaceBooleanCovariance_nonnegative D hroot)
      (Q'.le_of_eqv heq)
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm heq))
      (slabPhysicalFaceBooleanCovariance_le_couplingCorridorRate
        D hw0 hw1 hwAnchor rootFaceId
          (slabFaceReflectId D.extent rootFaceId) htarget)

/-! ## 2. Representation-cutoff removal at every corridor coupling -/

/-- Cutoff-removed connected autocorrelation of the literal lower-face
indicator at an arbitrary fixed positive subunit coupling. -/
def slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half rootFaceId : Nat) : CReal :=
  centralPhysicalConnectedAutocorrelationCutoffLimit
    hw0 hw1 half (slabPhysicalFacePositiveUnitObservable rootFaceId)

@[simp] theorem slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half rootFaceId cutoff : Nat) :
    (slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt
      hw0 hw1 half rootFaceId).approx cutoff =
      slabPhysicalFaceSameObjectConnectedMarkovMoment
        (observableCouplingSlabPhysicalData
          w (Q'.le_of_lt hw0) cutoff half) rootFaceId := rfl

theorem slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt_approx_eqv_covariance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half rootFaceId cutoff : Nat)
    (hroot : rootFaceId ∈ centralLowerFaceIds half) :
    (slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt
        hw0 hw1 half rootFaceId).approx cutoff ≈
      slabPhysicalFaceBooleanCovariance
        (observableCouplingSlabPhysicalData
          w (Q'.le_of_lt hw0) cutoff half)
        rootFaceId (slabFaceReflectId (centralExtent half) rootFaceId) := by
  exact Q'.eqv_symm
    (slabPhysicalReflectedFaceBooleanCovariance_eqv_sameObject
      (observableCouplingSlabPhysicalData
        w (Q'.le_of_lt hw0) cutoff half) hroot)

theorem slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half rootFaceId : Nat) :
    CReal.czero <=
      slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt
        hw0 hw1 half rootFaceId := by
  exact centralPhysicalConnectedAutocorrelationCutoffLimit_nonnegative
    hw0 hw1 half (slabPhysicalFacePositiveUnitObservable rootFaceId)

/-- The cutoff-removed same-object moment obeys the common corridor rate. -/
theorem slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt_le_corridorRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hwAnchor : w <= anchorCoupling)
    (half rootFaceId : Nat)
    (hroot : rootFaceId ∈ centralLowerFaceIds half) :
    slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt
        hw0 hw1 half rootFaceId <=
      CReal.ofQ'
        (slabObservablePairedSupportGlobalAnchorRate
          (observableCouplingSlabPhysicalData
            w (Q'.le_of_lt hw0) 0 half)
          rootFaceId (slabFaceReflectId (centralExtent half) rootFaceId)) := by
  apply CReal.le_ofQ'_of_approx_le
  intro cutoff
  have htarget := slabFaceReflectId_physical
    (mem_centralLowerFaceIds.mp hroot).1
  have hbridge :=
    slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt_approx_eqv_covariance
      hw0 hw1 half rootFaceId cutoff hroot
  have hcov := slabPhysicalFaceBooleanCovariance_le_couplingCorridorRate
    (observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    hw0 hw1 hwAnchor rootFaceId
      (slabFaceReflectId (centralExtent half) rootFaceId) htarget
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hbridge)
    (by simpa only [slabObservablePairedSupportGlobalAnchorRate,
      observableCouplingSlabPhysicalData, SlabPhysicalData.extent] using hcov)

/-! ## 3. Receding-slab clustering at every fixed corridor coupling -/

/-- The common geometric rate is independent of the stored coupling and
representation cutoff. -/
theorem centralBottomFace_couplingGlobalRate_eqv
    (w : Q') (hw0 : (0 : Q') <= w) (cutoff half : Nat) :
    slabObservablePairedSupportGlobalAnchorRate
        (observableCouplingSlabPhysicalData w hw0 cutoff half)
        (centralBottomSpatialFaceId half)
        (slabFaceReflectId (centralExtent half)
          (centralBottomSpatialFaceId half)) ≈
      centralBottomFacePairedRate half := by
  unfold slabObservablePairedSupportGlobalAnchorRate
    centralBottomFacePairedRate centralBottomFaceRateCoefficient
  simp only [observableCouplingSlabPhysicalData, SlabPhysicalData.extent]
  rw [centralBottomSpatialFace_reflection_linfDist]
  have hexponent : centralExtent half + 1 = 2 * (half + 1) := by
    unfold centralExtent
    omega
  rw [hexponent]
  exact Q'.eqv_refl _

/-- Representation-cutoff limit for the selected boundary-to-boundary face
at fixed coupling `w`. -/
def couplingCentralBottomFaceConnectedAutocorrelation
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CReal :=
  slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt
    hw0 hw1 half (centralBottomSpatialFaceId half)

@[simp] theorem couplingCentralBottomFaceConnectedAutocorrelation_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) :
    (couplingCentralBottomFaceConnectedAutocorrelation
      hw0 hw1 half).approx cutoff =
      slabPhysicalFaceSameObjectConnectedMarkovMoment
        (observableCouplingSlabPhysicalData
          w (Q'.le_of_lt hw0) cutoff half)
        (centralBottomSpatialFaceId half) := rfl

theorem couplingCentralBottomFaceConnectedAutocorrelation_approx_interval
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hwAnchor : w <= anchorCoupling)
    (half cutoff : Nat) :
    (0 : Q') <=
        (couplingCentralBottomFaceConnectedAutocorrelation
          hw0 hw1 half).approx cutoff ∧
      (couplingCentralBottomFaceConnectedAutocorrelation
          hw0 hw1 half).approx cutoff <=
        centralBottomFacePairedRate half := by
  have hinterval :=
    slabPhysicalReflectedFaceSameObject_couplingCorridor_interval
      (observableCouplingSlabPhysicalData
        w (Q'.le_of_lt hw0) cutoff half)
      hw0 hw1 hwAnchor (centralBottomSpatialFaceId half)
      (centralBottomSpatialFaceId_lower half)
  rw [couplingCentralBottomFaceConnectedAutocorrelation_approx]
  constructor
  · exact hinterval.1
  · exact Q'.le_trans' _ _ _ hinterval.2
      (Q'.le_of_eqv
        (centralBottomFace_couplingGlobalRate_eqv
          w (Q'.le_of_lt hw0) cutoff half))

theorem couplingCentralBottomFaceConnectedAutocorrelation_approx_le_dyadic
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hwAnchor : w <= anchorCoupling)
    (half cutoff : Nat) :
    (couplingCentralBottomFaceConnectedAutocorrelation
        hw0 hw1 half).approx cutoff <=
      centralBottomFaceRateCoefficient * HalfPow.half ^ (half + 1) := by
  exact Q'.le_trans' _ _ _
    (couplingCentralBottomFaceConnectedAutocorrelation_approx_interval
      hw0 hw1 hwAnchor half cutoff).2
    (centralBottomFacePairedRate_le_dyadic half)

theorem couplingCentralBottomFaceConnectedAutocorrelation_dyadic_interval
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hwAnchor : w <= anchorCoupling)
    (half : Nat) :
    CReal.czero <=
        couplingCentralBottomFaceConnectedAutocorrelation hw0 hw1 half ∧
      couplingCentralBottomFaceConnectedAutocorrelation hw0 hw1 half <=
        CReal.ofQ'
          (centralBottomFaceRateCoefficient *
            HalfPow.half ^ (half + 1)) := by
  constructor
  · exact slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt_nonnegative
      hw0 hw1 half (centralBottomSpatialFaceId half)
  · exact CReal.le_ofQ'_of_approx_le
      (couplingCentralBottomFaceConnectedAutocorrelation_approx_le_dyadic
        hw0 hw1 hwAnchor half)

theorem couplingCentralBottomFaceConnectedAutocorrelation_after_modulus
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hwAnchor : w <= anchorCoupling)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (half : Nat) (hhalf : centralBottomFaceClusteringModulus epsilon <= half)
    (cutoff : Nat) :
    (couplingCentralBottomFaceConnectedAutocorrelation
        hw0 hw1 half).approx cutoff <= (0 : Q') + epsilon ∧
      (0 : Q') <=
        (couplingCentralBottomFaceConnectedAutocorrelation
          hw0 hw1 half).approx cutoff + epsilon := by
  let scaledTolerance := epsilon *
    Q'.invSucc centralBottomFaceRateCoefficient.num.toNat
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon
      (Q'.invSucc_pos centralBottomFaceRateCoefficient.num.toNat)
  have hscaledFinal :
      centralBottomFaceRateCoefficient * scaledTolerance <= epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat
      centralBottomFaceRateCoefficient epsilon (by decide)
      (Q'.le_of_lt hepsilon)
  have hscaledDen : scaledTolerance.den <= half := by
    simpa only [scaledTolerance,
      centralBottomFaceClusteringModulus] using hhalf
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le
    (Nat.le_trans hscaledDen (Nat.le_succ half))
  have hhalfPower : HalfPow.half ^ (half + 1) <=
      HalfPow.half ^ scaledTolerance.den := by
    have hhalfSucc : half + 1 = scaledTolerance.den + offset := by omega
    rw [hhalfSucc]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den <=
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hrate :
      centralBottomFaceRateCoefficient * HalfPow.half ^ (half + 1) <=
        epsilon := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _
        centralBottomFaceRateCoefficient
        (Q'.le_trans' _ _ _ hhalfPower hhalfTolerance) (by decide))
      hscaledFinal
  have hinterval :=
    couplingCentralBottomFaceConnectedAutocorrelation_approx_interval
      hw0 hw1 hwAnchor half cutoff
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ hinterval.2
        (centralBottomFacePairedRate_le_dyadic half))
      (Q'.le_trans' _ _ _ hrate
        (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon))))
  · exact Q'.zero_le_add _ _ hinterval.1 (Q'.le_of_lt hepsilon)

/-- **Constructive corridor receding-volume clustering.**  At every fixed
rational `0 < w <= 1/400`, the cutoff-removed literal same-object connected
face moment converges to zero as the reflected boundary recedes. -/
theorem couplingCentralBottomFaceConnectedAutocorrelation_converges_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hwAnchor : w <= anchorCoupling) :
    CReal.ConvergesTo
      (couplingCentralBottomFaceConnectedAutocorrelation hw0 hw1)
      CReal.czero := by
  intro epsilon hepsilon
  refine ⟨centralBottomFaceClusteringModulus epsilon,
    fun half hhalf => ⟨0, fun cutoff _ => ?_⟩⟩
  exact couplingCentralBottomFaceConnectedAutocorrelation_after_modulus
    hw0 hw1 hwAnchor epsilon hepsilon half hhalf cutoff

#print axioms slabPhysicalFaceBooleanCovariance_le_couplingCorridorRate
#print axioms slabPhysicalReflectedFaceSameObject_couplingCorridor_interval
#print axioms slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt
#print axioms slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt_approx_eqv_covariance
#print axioms slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt_nonnegative
#print axioms slabPhysicalFaceConnectedAutocorrelationCutoffLimitAt_le_corridorRate
#print axioms centralBottomFace_couplingGlobalRate_eqv
#print axioms couplingCentralBottomFaceConnectedAutocorrelation
#print axioms couplingCentralBottomFaceConnectedAutocorrelation_approx_interval
#print axioms couplingCentralBottomFaceConnectedAutocorrelation_approx_le_dyadic
#print axioms couplingCentralBottomFaceConnectedAutocorrelation_dyadic_interval
#print axioms couplingCentralBottomFaceConnectedAutocorrelation_after_modulus
#print axioms couplingCentralBottomFaceConnectedAutocorrelation_converges_zero

end YMGap.Continuum.CompactDualSlabObservableFaceCouplingCorridorClustering
