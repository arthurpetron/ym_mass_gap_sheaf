/-
# An explicit local harmonic-tail modulus for the ORIGINAL endpoint source

Swap one actual active link to the head, retain the computed harmonic groups
above L, then put the polynomial back on the original link carrier. The
Casimir threshold controls its raw Haar square by the angular energy of the
complete original projected source. Its local relative bound supplies an
explicit epsilon-to-degree modulus depending only on the nome and epsilon,
not spatial width, terminal depth or the original sufficiently-late cutoff.

This is a one-link raw-Haar tail estimate. The spectator-smoothed quadratic,
joint four-link truncation, retained heat floor and SAME centered-variance
comparison are not identified with this norm or asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
import YMGap.Continuum.SU2QuaternionGroupedHarmonicTail
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointSpectralTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionGroupedHarmonicTail
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight activeBlocks

/-- A computed high-degree polynomial returned to its original coordinate
positions. This is not a new Hilbert carrier or an assumed spectral projector. -/
def selectedSpectralHighPart (blocks selected : Nat) (hs : selected < blocks)
    (L : Nat) (p : RatPoly) : RatPoly :=
  let swap := headSwapBlockInvolution blocks selected hs
  reindexQuaternionPolynomial swap
    (spectralHighPart blocks (by omega) L (reindexQuaternionPolynomial swap p))

theorem selectedSpectralHighPart_supported (blocks selected : Nat) (hs : selected < blocks)
    (L : Nat) (p : RatPoly) :
    SupportedQuaternionBlocks blocks (selectedSpectralHighPart blocks selected hs L p) :=
  reindex_supported _ _

/-- The first omitted Casimir controls the actual selected-link high part
by the original polynomial's full angular energy at that link. -/
theorem selectedSpectralHighPart_threshold_le_energy
    (blocks selected : Nat) (hs : selected < blocks) (L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    Q'.ofNat ((L+1)*(L+3)) * quaternionHaar blocks
      (polyMul (selectedSpectralHighPart blocks selected hs L p)
        (selectedSpectralHighPart blocks selected hs L p)) ≤
      quaternionHaar blocks (blockAngularSquare selected p) := by
  cases blocks with
  | zero => exact False.elim (Nat.not_lt_zero selected hs)
  | succ tail =>
      let swap := headSwapBlockInvolution (tail+1) selected hs
      let q := reindexQuaternionPolynomial swap p
      let r := spectralHighPart (tail+1) (by omega) L q
      let a := Q'.ofNat ((L+1)*(L+3))
      have h := spectralHighPart_threshold_le_energy tail L q polyOne
        (reindex_supported swap p) (Certificate.one _)
        (hasQuaternionBlockDegree_one 0)
      have hn : quaternionHaar (tail+1)
          (polyMul (selectedSpectralHighPart (tail+1) selected hs L p)
            (selectedSpectralHighPart (tail+1) selected hs L p)) ≈
          quaternionHaar (tail+1) (polyMul r r) := by
        change quaternionHaar (tail+1)
          (polyMul (reindexQuaternionPolynomial swap r) (reindexQuaternionPolynomial swap r)) ≈ _
        rw [← reindexQuaternionPolynomial_mul]
        exact quaternionHaar_reindex swap (polyMul r r)
          (supported_polyMul (spectralHighPart_supported _ _ L q)
            (spectralHighPart_supported _ _ L q))
      have hhead : quaternionHaar (tail+1) (angularSquare q) ≈
          quaternionHaar (tail+1) (blockAngularSquare selected p) := by
        have he := reindex_blockAngularSquare_haar (block := 0) swap (by omega) p
        simp only [swap, headSwapBlockInvolution_map_zero] at he
        exact Q'.eqv_trans _ _ _ (Q'.eqv_symm he)
          (quaternionHaar_reindex swap _ (blockAngularSquare_supported hs hp))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_trans _ _ _ hn
          (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _))))))
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.one_mul _)) hhead)))

/-- The complete original projected source supplies the angular budget.
All terminal depths are included; no inverse spectral floor is assumed. -/
theorem projectedEndpoint_highTail_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (n : Nat)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width) (L : Nat) :
    let q := projectedEndpointSource w K width (terminalMessage w K width n)
    let high := selectedSpectralHighPart (N width) ((baseLinks width).idxOf selected)
      (List.idxOf_lt_length_of_mem hl) L q
    Q'.ofNat ((L+1)*(L+3)) * quaternionHaar (N width) (polyMul high high) ≤
      (6 * (endpointRelativeCap w * endpointRelativeCap w)) *
        quaternionHaar (N width) (polyMul q q) := by
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width n))
  have he := projectedEndpointAngularSquare_le hw0 hw1 K width hK n selected hl hs
    (Certificate.one (N width))
  exact Q'.le_trans' _ _ _
    (selectedSpectralHighPart_threshold_le_energy (N width) _
      (List.idxOf_lt_length_of_mem hl) L q hq)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_one _)))
      (Q'.le_trans' _ _ _ he
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_one _))))))

/-- An explicit epsilon-to-degree modulus. The numerator ceiling is coarse
but computed; no volume, depth, cutoff or observable is an input. -/
def endpointTailDegree (w epsilon : Q') (he : (0 : Q') < epsilon) : Nat :=
  (Q'.divPos (6 * (endpointRelativeCap w * endpointRelativeCap w)) epsilon he).num.toNat

theorem endpointTailDegree_sufficient (w epsilon : Q') (he : (0 : Q') < epsilon)
    (L : Nat) (hL : endpointTailDegree w epsilon he ≤ L) :
    6 * (endpointRelativeCap w * endpointRelativeCap w) ≤
      epsilon * Q'.ofNat ((L+1)*(L+3)) := by
  let c := 6 * (endpointRelativeCap w * endpointRelativeCap w)
  let r := Q'.divPos c epsilon he
  have hc : (0 : Q') ≤ c :=
    Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg _)
  have hr : (0 : Q') ≤ r :=
    Q'.mul_nonneg _ _ hc (Q'.le_of_lt (Q'.recipPos_pos epsilon he))
  have hn : L ≤ (L+1)*(L+3) :=
    Nat.le_trans (Nat.le_succ L) (Nat.le_mul_of_pos_right _ (by omega))
  have hbound : r ≤ Q'.ofNat ((L+1)*(L+3)) :=
    Q'.le_trans' _ _ _ (RatNat.le_ofNat_toNat r hr)
      (CReal.ofNat_le_ofNat (Nat.le_trans hL hn))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.divPos_mul_eqv c epsilon he))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hbound (Q'.le_of_lt he))
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

/-- The computed local tail is epsilon-small relative to the SAME raw
source norm at every width, terminal depth and sufficiently late cutoff.
This does not replace raw Haar norm by the interacting partition/variance. -/
theorem projectedEndpoint_highTail_small {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (n : Nat)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (epsilon : Q') (he : (0 : Q') < epsilon) (L : Nat)
    (hL : endpointTailDegree w epsilon he ≤ L) :
    let q := projectedEndpointSource w K width (terminalMessage w K width n)
    let high := selectedSpectralHighPart (N width) ((baseLinks width).idxOf selected)
      (List.idxOf_lt_length_of_mem hl) L q
    quaternionHaar (N width) (polyMul high high) ≤
      epsilon * quaternionHaar (N width) (polyMul q q) := by
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let a := Q'.ofNat ((L+1)*(L+3))
  have ha : (0 : Q') < a := by
    change (0 : Int) * 1 < (((L+1)*(L+3) : Nat) : Int) * 1
    simpa only [Int.zero_mul, Int.mul_one] using
      (Int.ofNat_lt.mpr (Nat.mul_pos (by omega : 0 < L+1) (by omega : 0 < L+3)))
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width n))
  have hnorm := (Certificate.square q hq).haar_nonnegative
  have hcost := Q'.mul_le_mul_of_nonneg_right _ _ _
    (endpointTailDegree_sufficient w epsilon he L hL) hnorm
  have hmul := Q'.le_trans' _ _ _
    (projectedEndpoint_highTail_bound hw0 hw1 K width hK n selected hl hs L) hcost
  apply Q'.le_of_mul_le_mul_left (c := a) (hc := ha)
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv
    (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => epsilon | 1 => a | _ => quaternionHaar (N width) (polyMul q q))))

#print axioms selectedSpectralHighPart
#print axioms selectedSpectralHighPart_supported
#print axioms selectedSpectralHighPart_threshold_le_energy
#print axioms projectedEndpoint_highTail_bound
#print axioms endpointTailDegree
#print axioms endpointTailDegree_sufficient
#print axioms projectedEndpoint_highTail_small

end YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointSpectralTail
