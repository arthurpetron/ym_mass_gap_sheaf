/-
# Physical-link pullback of the identity Cayley vector-jet quadratic

The identity-chart quadratic isolated from the ORIGINAL global Cayley carrier
is a scalar multiple of the squared oriented imaginary plaquette curl.  This
leaf realizes that curl on the existing finite rooted-comb FREE history:

* the four literal directed physical link rows are pulled through the exact
  rational Heron transform and the three disjoint color blocks;
* on every row used by the bulk source, that pullback equals the canonical
  bulk Heron curl row;
* the resulting weighted radial polynomial is therefore coefficientwise the
  existing FREE `A₂ = 4 |B|²` source at the exact residual scale `2^64`;
* the corresponding finite product-Gaussian covariance inherits the same
  two-slot scaling exactly.

This is a finite linear substitution and FREE-polynomial normalization.  It
does not identify the ORIGINAL interacting law with the FREE Gaussian law,
bound either Cayley-denominator remainder, remove a cutoff, construct a
continuum theory, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_congr_local {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → left item ≈ right item) →
    qListSum (items.map left) ≈ qListSum (items.map right)
  | [], _ => Q'.eqv_refl _
  | item :: items, hypothesis =>
      Q'.add_eqv_congr'
        (hypothesis item List.mem_cons_self)
        (qListSum_congr_local left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem pulledRow_congr
    (physicalSize : Nat) (transform : Nat → Nat → Q')
    (left right : Nat → Q')
    (rowsEqv : ∀ index, index < physicalSize → left index ≈ right index)
    (noiseIndex : Nat) :
    pulledRow physicalSize transform left noiseIndex ≈
      pulledRow physicalSize transform right noiseIndex := by
  unfold pulledRow
  apply qListSum_congr_local
  intro physicalIndex membership
  exact Q'.mul_eqv_congr_right _ _ _
    (rowsEqv physicalIndex (List.mem_range.mp membership))

private theorem threeColorRows_congr
    (size component coordinate : Nat) (left right : Nat → Q')
    (rowsEqv : ∀ index, left index ≈ right index) :
    threeColorRows size left component coordinate ≈
      threeColorRows size right component coordinate := by
  rcases component with _ | component
  · simp only [threeColorRows]
    unfold appendRow
    by_cases h0 : coordinate < size
    · rw [if_pos h0, if_pos h0]
      exact rowsEqv coordinate
    · rw [if_neg h0, if_neg h0]
      exact Q'.eqv_refl _
  · rcases component with _ | component
    · simp only [threeColorRows]
      unfold appendRow
      by_cases h0 : coordinate < size
      · rw [if_pos h0, if_pos h0]
        exact Q'.eqv_refl _
      · rw [if_neg h0, if_neg h0]
        by_cases h1 : coordinate - size < size
        · rw [if_pos h1, if_pos h1]
          exact rowsEqv (coordinate - size)
        · rw [if_neg h1, if_neg h1]
          exact Q'.eqv_refl _
    · rcases component with _ | component
      · simp only [threeColorRows]
        unfold appendRow
        by_cases h0 : coordinate < size
        · rw [if_pos h0, if_pos h0]
          exact Q'.eqv_refl _
        · rw [if_neg h0, if_neg h0]
          by_cases h1 : coordinate - size < size
          · rw [if_pos h1, if_pos h1]
            exact Q'.eqv_refl _
          · rw [if_neg h1, if_neg h1]
            exact rowsEqv (coordinate - size - size)
      · simp only [threeColorRows]
        exact Q'.eqv_refl _

private theorem polySum_congr_local {Index : Type}
    (left right : Index → RatPoly) : ∀ items : List Index,
    (∀ item, item ∈ items → RatPolyCoeffEqv (left item) (right item)) →
    RatPolyCoeffEqv (polySum (items.map left)) (polySum (items.map right))
  | [], _ => RatPolyCoeffEqv.refl _
  | item :: items, hypothesis =>
      RatPolyCoeffEqv.add
        (hypothesis item List.mem_cons_self)
        (polySum_congr_local left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem finiteGaussianRowSquare_congr
    (coordinateCount : Nat) (left right : Nat → Q')
    (rowsEqv : ∀ coordinate, coordinate < coordinateCount →
      left coordinate ≈ right coordinate) :
    RatPolyCoeffEqv
      (finiteGaussianRowSquare coordinateCount left)
      (finiteGaussianRowSquare coordinateCount right) := by
  unfold finiteGaussianRowSquare
  have hrow := finiteLinearRow_coeffEqv
    coordinateCount left right rowsEqv
  exact hrow.mul hrow

private theorem finiteGaussianWeightedRadialSquare_congr
    (coordinateCount rowCount : Nat) (weights : Nat → Q')
    (left right : Nat → Nat → Q')
    (rowsEqv : ∀ rowIndex, rowIndex < rowCount →
      ∀ coordinate, coordinate < coordinateCount →
        left rowIndex coordinate ≈ right rowIndex coordinate) :
    RatPolyCoeffEqv
      (finiteGaussianWeightedRadialSquare
        coordinateCount rowCount weights left)
      (finiteGaussianWeightedRadialSquare
        coordinateCount rowCount weights right) := by
  unfold finiteGaussianWeightedRadialSquare
  apply polySum_congr_local
  intro rowIndex membership
  exact (finiteGaussianRowSquare_congr coordinateCount
    (left rowIndex) (right rowIndex)
    (rowsEqv rowIndex (List.mem_range.mp membership))).smul (weights rowIndex)

/-- Explicit pullback of the four directed physical link rows for one actual
bulk face through the exact rational Heron transform and one color block. -/
def bulkSourcePhysicalLinkPullbackRow
    (timeBonds s stage time rowIndex coordinate : Nat) : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds
      (combGaugeEdgeCount (bulkSourceWidth s))
  threeColorRows coordinateCount
    (pulledRow coordinateCount
      (combGaugeFreeHistoryHeronTransform
        timeBonds (bulkSourceWidth s) stage)
      (combGaugeFreeHistoryPlaquettePhysicalActionRow
        (bulkSourceWidth s) time
        (selectedBulkSourceFace s (rowIndex / 3))))
    (rowIndex % 3) coordinate

/-- On every row used by the bulk source, the canonical Heron curl row is
exactly the pullback of the four directed physical plaquette-link rows. -/
theorem bulkSourceHeronColorCurlRow_eq_physicalLinkPullback
    (timeBonds s stage time rowIndex coordinate : Nat)
    (hrow : rowIndex < 3 * (bulkSourceFaces s).length) :
    bulkSourceHeronColorCurlRow
        timeBonds s stage time rowIndex coordinate ≈
      bulkSourcePhysicalLinkPullbackRow
        timeBonds s stage time rowIndex coordinate := by
  let coordinateCount :=
    historyCoordinateCount timeBonds
      (combGaugeEdgeCount (bulkSourceWidth s))
  let faceIndex := rowIndex / 3
  let face := selectedBulkSourceFace s faceIndex
  have hfaceIndex : faceIndex < (bulkSourceFaces s).length := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    simpa only [Nat.mul_comm] using hrow
  have hface : face ∈ internalOpenCubeFaces (bulkSourceWidth s) :=
    bulkSourceFace_internal (selectedBulkSourceFace_mem hfaceIndex)
  have hphysical : ∀ physicalIndex, physicalIndex < coordinateCount →
      combGaugeFreeHistoryCurlRow
          (bulkSourceWidth s) time
          (bulkSourceInternalFaceIndex s faceIndex) physicalIndex ≈
        combGaugeFreeHistoryPlaquettePhysicalActionRow
          (bulkSourceWidth s) time face physicalIndex := by
    intro physicalIndex hphysicalIndex
    exact Q'.eqv_symm (by
      simpa only [combGaugeFreeHistorySpatialActionRow,
        bulkSourceInternalFaceIndex, face, faceIndex] using
        combGaugeFreeHistoryPlaquettePhysicalActionRow_eq_spatialActionRow
          timeBonds (bulkSourceWidth s) time physicalIndex face
          hphysicalIndex hface)
  unfold bulkSourceHeronColorCurlRow
    combGaugeFreeHistoryHeronColorCurlRow
    bulkSourcePhysicalLinkPullbackRow
  dsimp only
  exact threeColorRows_congr coordinateCount (rowIndex % 3) coordinate _ _
    (fun noiseIndex => pulledRow_congr coordinateCount
      (combGaugeFreeHistoryHeronTransform
        timeBonds (bulkSourceWidth s) stage)
      (combGaugeFreeHistoryCurlRow
        (bulkSourceWidth s) time
        (bulkSourceInternalFaceIndex s faceIndex))
      (combGaugeFreeHistoryPlaquettePhysicalActionRow
        (bulkSourceWidth s) time face)
      hphysical noiseIndex)

/-- Weighted radial square formed from the explicit physical-link pullback
rows rather than the canonical comb-curl rows. -/
def bulkSourcePhysicalLinkPullbackRadialSquare
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) : RatPoly :=
  finiteGaussianWeightedRadialSquare
    (bulkSourceNoiseCount timeBonds s)
    (3 * (bulkSourceFaces s).length)
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (bulkSourcePhysicalLinkPullbackRow timeBonds s stage time)

/-- The canonical bulk radial square is coefficientwise the weighted radial
square obtained from the explicit directed physical-link pullbacks. -/
theorem bulkSourceHeronRadialSquare_coeff_physicalLinkPullback
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) :
    RatPolyCoeffEqv
      (bulkSourceHeronRadialSquare timeBonds s hs stage time)
      (bulkSourcePhysicalLinkPullbackRadialSquare
        timeBonds s hs stage time) := by
  unfold bulkSourceHeronRadialSquare
    combGaugeFreeHistoryHeronWeightedCurlRadialSquare
    bulkSourcePhysicalLinkPullbackRadialSquare
    bulkSourceNoiseCount
  exact finiteGaussianWeightedRadialSquare_congr
    _ (3 * (bulkSourceFaces s).length)
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (bulkSourceHeronColorCurlRow timeBonds s stage time)
    (bulkSourcePhysicalLinkPullbackRow timeBonds s stage time)
    (fun rowIndex hrow coordinate _ =>
      bulkSourceHeronColorCurlRow_eq_physicalLinkPullback
        timeBonds s stage time rowIndex coordinate hrow)

/-- Residual scalar after absorbing the trace-source factor `4` into the
identity vector-jet scale `2^66`. -/
def identityCayleyVectorJetFreeA2Scale : Q' :=
  Q'.ofNat 18446744073709551616

/-- Exact scale factorization `2^66 = 2^64 * 4`. -/
theorem identityCayleyVectorJetQuadraticScale_eq_freeA2Scale :
    identityCayleyVectorJetQuadraticScale ≈
      identityCayleyVectorJetFreeA2Scale * 4 := by
  decide

/-- The identity-normalized global Cayley vector-jet quadratic after the
explicit finite physical-link-to-Heron substitution. -/
def globalCayleyVectorJetBulkIdentityQuadraticFreePullback
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) : RatPoly :=
  polySmul identityCayleyVectorJetQuadraticScale
    (bulkSourcePhysicalLinkPullbackRadialSquare
      timeBonds s hs stage time)

/-- Exact normalized source pin: the physical-link pullback of the global
identity vector-jet quadratic is `2^64` times the existing FREE `A₂` source. -/
theorem globalCayleyVectorJetBulkIdentityQuadraticFreePullback_coeff_A2
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) :
    RatPolyCoeffEqv
      (globalCayleyVectorJetBulkIdentityQuadraticFreePullback
        timeBonds s hs stage time)
      (polySmul identityCayleyVectorJetFreeA2Scale
        (openCubeBulkCayleyTraceA2
          timeBonds s hs stage time)) := by
  let radial := bulkSourceHeronRadialSquare timeBonds s hs stage time
  have hpullback : RatPolyCoeffEqv
      (bulkSourcePhysicalLinkPullbackRadialSquare
        timeBonds s hs stage time) radial :=
    (bulkSourceHeronRadialSquare_coeff_physicalLinkPullback
      timeBonds s hs stage time).symm
  have hscale : RatPolyCoeffEqv
      (polySmul identityCayleyVectorJetQuadraticScale radial)
      (polySmul identityCayleyVectorJetFreeA2Scale
        (polySmul 4 radial)) :=
    (RatPolyCoeffEqv.smul_coefficient
      identityCayleyVectorJetQuadraticScale_eq_freeA2Scale radial).trans
        (RatPolyCoeffEqv.smul_assoc
          identityCayleyVectorJetFreeA2Scale 4 radial).symm
  unfold globalCayleyVectorJetBulkIdentityQuadraticFreePullback
    openCubeBulkCayleyTraceA2
  exact (hpullback.smul identityCayleyVectorJetQuadraticScale).trans hscale

/-- Finite product-Gaussian covariance consumer of the normalized source pin.
Both time placements retain the exact residual factor `2^64`. -/
theorem finiteGaussianCovariance_globalIdentityQuadraticFreePullback_eq_A2
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds s)
        (globalCayleyVectorJetBulkIdentityQuadraticFreePullback
          timeBonds s hs stage leftTime)
        (globalCayleyVectorJetBulkIdentityQuadraticFreePullback
          timeBonds s hs stage rightTime) ≈
      (identityCayleyVectorJetFreeA2Scale *
        identityCayleyVectorJetFreeA2Scale) *
        finiteGaussianCovariance (bulkSourceNoiseCount timeBonds s)
          (openCubeBulkCayleyTraceA2
            timeBonds s hs stage leftTime)
          (openCubeBulkCayleyTraceA2
            timeBonds s hs stage rightTime) := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv
      (bulkSourceNoiseCount timeBonds s)
      (globalCayleyVectorJetBulkIdentityQuadraticFreePullback_coeff_A2
        timeBonds s hs stage leftTime)
      (globalCayleyVectorJetBulkIdentityQuadraticFreePullback_coeff_A2
        timeBonds s hs stage rightTime))
    (finiteGaussianCovariance_smul
      (bulkSourceNoiseCount timeBonds s)
      identityCayleyVectorJetFreeA2Scale
      identityCayleyVectorJetFreeA2Scale
      (openCubeBulkCayleyTraceA2 timeBonds s hs stage leftTime)
      (openCubeBulkCayleyTraceA2 timeBonds s hs stage rightTime))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback.bulkSourceHeronColorCurlRow_eq_physicalLinkPullback
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback.bulkSourceHeronRadialSquare_coeff_physicalLinkPullback
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback.identityCayleyVectorJetQuadraticScale_eq_freeA2Scale
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback.globalCayleyVectorJetBulkIdentityQuadraticFreePullback_coeff_A2
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback.finiteGaussianCovariance_globalIdentityQuadraticFreePullback_eq_A2
