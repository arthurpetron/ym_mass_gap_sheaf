/-
# Bare Haar moments of an actual signed spatial plaquette family

The complete literal spatial span, including repeated faces and signed
coefficients, has zero bare-Haar mean. Its Casimir-12 eigenidentity gives
an exact bare-Haar angular square identity. Consequently any rational
recentering can only increase its bare squared norm.

These statements concern bare Haar, not the interacting odd marginal.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir
import YMGap.Continuum.SU2QuaternionSecondOrderCancellation
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.QuaternionHaarFamilySquare
import YMGap.Continuum.SU2QuaternionWeightedCasimirWard
import YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
  (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (plaquette spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy
  (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
  (activeGamma blockGamma)
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare (activeCasimirPolynomial)
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation (casimir_pair_gamma)
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularSquare)
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
  (weightedAngularEnergy sourceFirstOrder_eq_weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionWeightedCasimirWard
  (totalEnergy totalEnergy_finSum blockEnergy)
open YMGap.Continuum.QuaternionHaarFamilySquare
  (haar_weighted_sum_indexed)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
  (familyProject_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage plaquette projectedEndpointSource

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

/-- The weighted angular square is the full active carré du champ. No
independence or positivity of the weight is needed for this exact identity. -/
theorem weighted_gamma_finSum (n : Nat) (W f : RatPoly) :
    H n (polyMul W (activeGamma (List.range n) f f)) ≈
      finSum (fun i => H n (polyMul W (blockAngularSquare i f))) n := by
  have hsum : H n (polyMul W (activeGamma (List.range n) f f)) ≈
      totalEnergy n W f := by
    simpa only [activeGamma, totalEnergy, blockEnergy,
      blockGamma, blockAngularSquare] using
      (haar_weighted_sum_indexed n W
        (fun i => blockGamma i f f) (List.range n))
  exact Q'.eqv_trans _ _ _ hsum (totalEnergy_finSum n W f)

/-- First-order source energy for the actual projected terminal message and
the complete literal signed family. The same source square weights every
cross term; this is not an interacting-variance estimate. -/
theorem family_sourceFirstOrder_gamma (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    let f := spatialSpan width c qs
    let q := projectedEndpointSource w K width
      (terminalMessage w K width depth)
    sourceFirstOrder (N width - 1) q f ≈
      H (N width) (polyMul (polyMul q q)
        (activeGamma (List.range (N width)) f f)) := by
  dsimp only
  let q := projectedEndpointSource w K width
    (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  have hn : N width - 1 + 1 = N width :=
    Nat.sub_add_cancel (baseLinks_positive width)
  have hq : SupportedQuaternionBlocks (N width) q := by
    unfold q projectedEndpointSource
    exact familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hf : SupportedQuaternionBlocks (N width) f :=
    spatialSpan_supported width c qs
  have hfirst := sourceFirstOrder_eq_weightedAngularEnergy
    (N width - 1) q f (by simpa only [hn] using hq)
    (by simpa only [hn] using hf)
  have hgamma := weighted_gamma_finSum (N width) (polyMul q q) f
  exact Q'.eqv_trans _ _ _ hfirst (by
    simpa only [weightedAngularEnergy, hn] using Q'.eqv_symm hgamma)

/-- The complete original signed/repeated family is orthogonal to the bare
Haar constant. Physical membership is used only for each literal face pin. -/
theorem family_haar_zero (width : Nat) (c : Z4Plaq → Q') :
    ∀ (qs : List Z4Plaq),
      (∀ p, p ∈ qs → p ∈ spatialFaces width) →
      H (N width) (spatialSpan width c qs) ≈ 0
  | [], _ => Q'.eqv_refl 0
  | p::qs, hqs => by
      have hp : H (N width)
          (polySmul (c p) (characterPolynomial (plaquette width p).scalar 1)) ≈ 0 :=
        Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) (c p) _)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (c p) _ _
              (plaquette_mean_zero width p (hqs p List.mem_cons_self)))
            (Q'.mul_zero_eqv _))
      have ht := family_haar_zero width c qs
        (fun q hq => hqs q (List.mem_cons_of_mem p hq))
      change H (N width)
        (polyAdd
          (polySmul (c p) (characterPolynomial (plaquette width p).scalar 1))
          (spatialSpan width c qs)) ≈ 0
      exact Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hp ht)
          (Q'.eqv_of_eq (Q'.add_zero' 0)))

/-- The whole signed family's bare-Haar angular square retains every
off-diagonal face correlation; it is not a sum of facewise squares. -/
theorem family_gamma_square (width : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    let f := spatialSpan width c qs
    H (N width) (activeGamma (List.range (N width)) f f) ≈
      12 * H (N width) (polyMul f f) := by
  dsimp only
  let f := spatialSpan width c qs
  let active := List.range (N width)
  have hpair := casimir_pair_gamma (N width) active
    (fun i hi => List.mem_range.mp hi) f f
  have hCf := spatialSpan_casimir width c qs hqs
  have hscale : H (N width)
      (polyMul f (polySmul 12 f)) ≈
      12 * H (N width) (polyMul f f) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right 12 f f))
      (quaternionHaar_polySmul (N width) 12 (polyMul f f))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hpair)
    (Q'.eqv_trans _ _ _ (hCf f) hscale)

/-- With bare-Haar mean zero, any rational center leaves at least the
original whole-family squared norm. This does not recenter the odd marginal. -/
theorem family_shifted_square_ge (width : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) (center : Q') :
    let f := spatialSpan width c qs
    H (N width) (polyMul f f) ≤
      H (N width) (polyMul (shifted f center) (shifted f center)) := by
  dsimp only
  let f := spatialSpan width c qs
  have hzero : H (N width) f ≈ 0 := family_haar_zero width c qs hqs
  have hzeroSquare : H (N width) f * H (N width) f ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (H (N width) f) _ _ hzero)
      (Q'.mul_zero_eqv _)
  have hbare : H (N width) (polyMul f f) +
      -(H (N width) f * H (N width) f) ≈
      H (N width) (polyMul f f) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hzeroSquare)
          (by decide : -(0 : Q') ≈ 0)))
      (QPoly.q_add_zero_eqv _)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hbare)
    (bare_variance_le_shifted (spatialSpan_supported width c qs) center)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar.family_haar_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar.family_gamma_square
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar.family_shifted_square_ge
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar.weighted_gamma_finSum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar.family_sourceFirstOrder_gamma
