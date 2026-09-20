/-
# Receding-slab clustering of one literal same-object BF4 face observable

The corrected reflection slab of half-width `half` has odd extent `2*half+1`.
This module selects the bottom spatial plaquette and follows its literal
face-positivity indicator through the physical BF4 conditional operator.  Its
reflection lies on the opposite boundary, at exact L-infinity separation
`2*half+1`.  The complete non-abelian component peel therefore gives

  `0 <= <a_half, P_half a_half> - E(a_half)^2
       <= (25/9) * (16/25)^(2*(half+1))`.

Pairing the two powers turns the rate base into `(16/25)^2 <= 1/2`.  Hence the
already cutoff-removed CReal same-object moment converges constructively to
zero as the slab half-width recedes, with an explicit dyadic modulus.

This is a boundary-to-boundary clustering theorem for a family of finite-slab
conditional operators `P_half`.  It does not identify these operators with
powers of one fixed Euclidean-time transfer, prove an all-observable spectral
gap, vary the coupling along an asymptotically-free trajectory, or take a
continuum limit.

Constructive contract: finite list indexing, exact `Nat` geometry, rational
power algebra, and the existing Bishop-real cutoff limit only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
import YMGap.Constructive.CRealConvergenceCertificate

namespace YMGap.Continuum.CompactDualSlabObservableFaceRecedingVolumeClustering

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A canonical lower boundary face and its exact separation -/

/-- Physical face identifier of the bottom spatial plaquette in the central
corrected slab. -/
def centralBottomSpatialFaceId (half : Nat) : Nat :=
  listIndexOf bottomSpatialPlaquette
    (boundaryCompleteSlabPlaquettes (centralExtent half))

theorem bottomSpatialPlaquette_mem_centralSlab (half : Nat) :
    bottomSpatialPlaquette ∈
      boundaryCompleteSlabPlaquettes (centralExtent half) := by
  rw [mem_boundaryCompleteSlabPlaquettes]
  constructor
  · exact bottomSpatialPlaquette_mem_boxPlaquettes (by
      unfold centralExtent
      omega)
  · unfold plaquetteTimeAdmissible bottomSpatialPlaquette
    exact Nat.zero_le _

theorem centralBottomSpatialFaceId_physical (half : Nat) :
    centralBottomSpatialFaceId half ∈
      slabPhysicalFaceEdges (centralExtent half) := by
  unfold centralBottomSpatialFaceId slabPhysicalFaceEdges
  exact List.mem_range.mpr
    (listIndexOf_lt_of_mem bottomSpatialPlaquette
      (boundaryCompleteSlabPlaquettes (centralExtent half))
      (bottomSpatialPlaquette_mem_centralSlab half))

@[simp] theorem slabPlaquetteAt_centralBottomSpatialFaceId (half : Nat) :
    slabPlaquetteAt (centralExtent half)
        (centralBottomSpatialFaceId half) =
      bottomSpatialPlaquette := by
  unfold slabPlaquetteAt centralBottomSpatialFaceId
  exact getD_listIndexOf_of_mem fallbackPlaquette bottomSpatialPlaquette
    (boundaryCompleteSlabPlaquettes (centralExtent half))
    (bottomSpatialPlaquette_mem_centralSlab half)

theorem centralBottomSpatialFaceId_lower (half : Nat) :
    centralBottomSpatialFaceId half ∈ centralLowerFaceIds half := by
  rw [mem_centralLowerFaceIds]
  constructor
  · exact centralBottomSpatialFaceId_physical half
  · rw [slabPlaquetteAt_centralBottomSpatialFaceId]
    simp [plaquetteHalfSide, spatialHalfSide, bottomSpatialPlaquette]

/-- The selected face and its reflection are separated by the full odd slab
extent. -/
theorem centralBottomSpatialFace_reflection_linfDist (half : Nat) :
    linfDist
        (slabPlaquetteAt (centralExtent half)
          (centralBottomSpatialFaceId half))
        (slabPlaquetteAt (centralExtent half)
          (slabFaceReflectId (centralExtent half)
            (centralBottomSpatialFaceId half))) =
      centralExtent half := by
  rw [slabPlaquetteAt_slabFaceReflectId
    (centralBottomSpatialFaceId_physical half)]
  rw [slabPlaquetteAt_centralBottomSpatialFaceId]
  unfold linfDist natDist cPlaq vComp bottomSpatialPlaquette
    timeReflectPlaquette
  simp

/-! ## 2. The paired component-peel rate becomes dyadic -/

def centralBottomFaceRateCoefficient : Q' :=
  Q'.mkPos 25 9 (by decide)

def centralBottomFacePairedRate (half : Nat) : Q' :=
  centralBottomFaceRateCoefficient *
    slabObservablePairedGlobalEntropyAnchorRatio ^ (2 * (half + 1))

theorem centralBottomFace_globalAnchorRate_eqv (cutoff half : Nat) :
    slabObservablePairedSupportGlobalAnchorRate
        (anchorSlabPhysicalData cutoff half)
        (centralBottomSpatialFaceId half)
        (slabFaceReflectId (centralExtent half)
          (centralBottomSpatialFaceId half)) ≈
      centralBottomFacePairedRate half := by
  unfold slabObservablePairedSupportGlobalAnchorRate
    centralBottomFacePairedRate centralBottomFaceRateCoefficient
  simp only [SlabPhysicalData.extent, anchorSlabPhysicalData]
  rw [centralBottomSpatialFace_reflection_linfDist]
  have hexponent : centralExtent half + 1 = 2 * (half + 1) := by
    unfold centralExtent
    omega
  rw [hexponent]
  exact Q'.eqv_refl _

private theorem mul_four_regroup_local (A B C D : Q') :
    ((A * B) * (C * D)) ≈ ((A * C) * (B * D)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

private theorem mulSelf_pow_eqv (w : Q') : ∀ n : Nat,
    (w * w) ^ n ≈ w ^ n * w ^ n
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | n + 1 => by
      show (w * w) * (w * w) ^ n ≈
        (w * w ^ n) * (w * w ^ n)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (w * w) _ _ (mulSelf_pow_eqv w n)) ?_
      exact mul_four_regroup_local w w (w ^ n) (w ^ n)

private theorem square_pow_eqv_double_pow (w : Q') (n : Nat) :
    (w * w) ^ n ≈ w ^ (n + n) := by
  exact Q'.eqv_trans _ _ _ (mulSelf_pow_eqv w n)
    (Q'.eqv_symm (Q'.pow_add_eqv w n n))

private theorem pow_base_mono_local
    (a b : Q') (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hab
          (Q'.pow_nonneg a ha n))
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (pow_base_mono_local a b ha hab n) hb)

theorem pairedEntropyAnchorRatio_square_le_half :
    slabObservablePairedGlobalEntropyAnchorRatio *
        slabObservablePairedGlobalEntropyAnchorRatio ≤
      HalfPow.half := by
  decide

theorem pairedEntropyAnchorRatio_doublePower_le_halfPower (n : Nat) :
    slabObservablePairedGlobalEntropyAnchorRatio ^ (2 * n) ≤
      HalfPow.half ^ n := by
  have hbase : (0 : Q') ≤
      slabObservablePairedGlobalEntropyAnchorRatio := by decide
  have hsquare := pow_base_mono_local
    (slabObservablePairedGlobalEntropyAnchorRatio *
      slabObservablePairedGlobalEntropyAnchorRatio)
    HalfPow.half
    (Q'.mul_nonneg _ _ hbase hbase)
    pairedEntropyAnchorRatio_square_le_half n
  have hexponent : 2 * n = n + n := by omega
  rw [hexponent]
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (square_pow_eqv_double_pow
          slabObservablePairedGlobalEntropyAnchorRatio n)))
    hsquare

theorem centralBottomFacePairedRate_le_dyadic (half : Nat) :
    centralBottomFacePairedRate half ≤
      centralBottomFaceRateCoefficient * HalfPow.half ^ (half + 1) := by
  unfold centralBottomFacePairedRate
  exact Q'.mul_le_mul_of_nonneg_left _ _ centralBottomFaceRateCoefficient
    (pairedEntropyAnchorRatio_doublePower_le_halfPower (half + 1))
    (by decide)

/-! ## 3. Cutoff-removed same-object autocorrelation and convergence -/

/-- The representation-cutoff limit of the selected boundary-to-boundary
same-object connected moment at slab half-width `half`. -/
def anchorCentralBottomFaceConnectedAutocorrelation (half : Nat) : CReal :=
  anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit half
    (centralBottomSpatialFaceId half)

@[simp] theorem anchorCentralBottomFaceConnectedAutocorrelation_approx
    (half cutoff : Nat) :
    (anchorCentralBottomFaceConnectedAutocorrelation half).approx cutoff =
      slabPhysicalFaceSameObjectConnectedMarkovMoment
        (anchorSlabPhysicalData cutoff half)
        (centralBottomSpatialFaceId half) := rfl

theorem anchorCentralBottomFaceConnectedAutocorrelation_approx_interval
    (half cutoff : Nat) :
    (0 : Q') ≤
        (anchorCentralBottomFaceConnectedAutocorrelation half).approx cutoff ∧
      (anchorCentralBottomFaceConnectedAutocorrelation half).approx cutoff ≤
        centralBottomFacePairedRate half := by
  have hinterval := slabPhysicalReflectedFaceSameObject_geometric_interval
    cutoff half (centralBottomSpatialFaceId half)
      (centralBottomSpatialFaceId_lower half)
  rw [anchorCentralBottomFaceConnectedAutocorrelation_approx]
  constructor
  · exact hinterval.1
  · exact Q'.le_trans' _ _ _ hinterval.2
      (Q'.le_of_eqv (centralBottomFace_globalAnchorRate_eqv cutoff half))

theorem anchorCentralBottomFaceConnectedAutocorrelation_approx_le_dyadic
    (half cutoff : Nat) :
    (anchorCentralBottomFaceConnectedAutocorrelation half).approx cutoff ≤
      centralBottomFaceRateCoefficient * HalfPow.half ^ (half + 1) := by
  exact Q'.le_trans' _ _ _
    (anchorCentralBottomFaceConnectedAutocorrelation_approx_interval
      half cutoff).2
    (centralBottomFacePairedRate_le_dyadic half)

/-- CReal-level positive dyadic interval after the representation cutoff has
been removed. -/
theorem anchorCentralBottomFaceConnectedAutocorrelation_dyadic_interval
    (half : Nat) :
    CReal.czero ≤ anchorCentralBottomFaceConnectedAutocorrelation half ∧
      anchorCentralBottomFaceConnectedAutocorrelation half ≤
        CReal.ofQ'
          (centralBottomFaceRateCoefficient *
            HalfPow.half ^ (half + 1)) := by
  constructor
  · exact
      anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit_nonnegative
        half (centralBottomSpatialFaceId half)
  · exact CReal.le_ofQ'_of_approx_le
      (anchorCentralBottomFaceConnectedAutocorrelation_approx_le_dyadic half)

/-- Executable outer-stage modulus for receding-volume clustering. -/
def centralBottomFaceClusteringModulus (epsilon : Q') : Nat :=
  (epsilon *
    Q'.invSucc centralBottomFaceRateCoefficient.num.toNat).den

/-- The displayed modulus controls every rational approximation of every
later cutoff-removed slab moment. -/
theorem anchorCentralBottomFaceConnectedAutocorrelation_after_modulus
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (half : Nat) (hhalf : centralBottomFaceClusteringModulus epsilon ≤ half)
    (cutoff : Nat) :
    (anchorCentralBottomFaceConnectedAutocorrelation half).approx cutoff ≤
        (0 : Q') + epsilon ∧
      (0 : Q') ≤
        (anchorCentralBottomFaceConnectedAutocorrelation half).approx cutoff +
          epsilon := by
  let scaledTolerance := epsilon *
    Q'.invSucc centralBottomFaceRateCoefficient.num.toNat
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon
      (Q'.invSucc_pos centralBottomFaceRateCoefficient.num.toNat)
  have hscaledFinal :
      centralBottomFaceRateCoefficient * scaledTolerance ≤ epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat
      centralBottomFaceRateCoefficient epsilon (by decide)
      (Q'.le_of_lt hepsilon)
  have hscaledDen : scaledTolerance.den ≤ half := by
    simpa only [scaledTolerance, centralBottomFaceClusteringModulus] using hhalf
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le
    (Nat.le_trans hscaledDen (Nat.le_succ half))
  have hhalfPower : HalfPow.half ^ (half + 1) ≤
      HalfPow.half ^ scaledTolerance.den := by
    have hhalfSucc : half + 1 = scaledTolerance.den + offset := by omega
    rw [hhalfSucc]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hrate :
      centralBottomFaceRateCoefficient * HalfPow.half ^ (half + 1) ≤
        epsilon := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _
        centralBottomFaceRateCoefficient
        (Q'.le_trans' _ _ _ hhalfPower hhalfTolerance) (by decide))
      hscaledFinal
  have hinterval :=
    anchorCentralBottomFaceConnectedAutocorrelation_approx_interval
      half cutoff
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        hinterval.2 (centralBottomFacePairedRate_le_dyadic half))
      (Q'.le_trans' _ _ _ hrate
        (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon))))
  · exact Q'.zero_le_add _ _ hinterval.1 (Q'.le_of_lt hepsilon)

/-! ## 4. The explicit certificate consumed by the limit -/

/-- The receding-volume same-object observable carries its outer-stage
modulus as data.  The approximation-stage modulus is zero because the bound
above holds for every rational approximation index.  This is the constructive
certificate needed by a later thermodynamic/continuum handoff; the certificate
does not manufacture an OS reconstruction or a physical mass gap. -/
def anchorCentralBottomFaceConnectedAutocorrelation_certificate :
    CReal.ExplicitConvergenceCertificate
      anchorCentralBottomFaceConnectedAutocorrelation CReal.czero where
  modulus := centralBottomFaceClusteringModulus
  approximationModulus := fun _ _ => 0
  bound := by
    intro epsilon hepsilon half hhalf cutoff hcutoff
    exact anchorCentralBottomFaceConnectedAutocorrelation_after_modulus
      epsilon hepsilon half hhalf cutoff

/-- **Constructive receding-volume clustering.**  After removing the
representation cutoff at every finite slab, the literal same-object connected
face moment tends to zero as the reflected boundary recedes. -/
theorem anchorCentralBottomFaceConnectedAutocorrelation_converges_zero :
    CReal.ConvergesTo anchorCentralBottomFaceConnectedAutocorrelation
      CReal.czero := by
  exact
    CReal.ExplicitConvergenceCertificate.toConvergesTo
      anchorCentralBottomFaceConnectedAutocorrelation_certificate

#print axioms centralBottomSpatialFaceId
#print axioms centralBottomSpatialFaceId_lower
#print axioms centralBottomSpatialFace_reflection_linfDist
#print axioms centralBottomFace_globalAnchorRate_eqv
#print axioms pairedEntropyAnchorRatio_square_le_half
#print axioms pairedEntropyAnchorRatio_doublePower_le_halfPower
#print axioms centralBottomFacePairedRate_le_dyadic
#print axioms anchorCentralBottomFaceConnectedAutocorrelation
#print axioms anchorCentralBottomFaceConnectedAutocorrelation_approx_interval
#print axioms anchorCentralBottomFaceConnectedAutocorrelation_approx_le_dyadic
#print axioms anchorCentralBottomFaceConnectedAutocorrelation_dyadic_interval
#print axioms centralBottomFaceClusteringModulus
#print axioms anchorCentralBottomFaceConnectedAutocorrelation_after_modulus
#print axioms anchorCentralBottomFaceConnectedAutocorrelation_certificate
#print axioms anchorCentralBottomFaceConnectedAutocorrelation_converges_zero

end YMGap.Continuum.CompactDualSlabObservableFaceRecedingVolumeClustering
