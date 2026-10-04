/-
# A retained cancellation in the COMPLETE original adjacent-family energy

The whole two-face angular identity is inserted under EVERY actual passive
channel-source square, not under a substituted odd marginal. It gives

  originalEnergy + (1-w)*retainedChannelSquare
    = (1-w)*paidChannelMoment + originalSignedTaylorDebt.

The retained term is a computed nonnegative square for nonnegative nome.
All exterior links, the actual projected V*g_depth source, passive-channel
weights and BOTH signed Taylor remainders remain. No assumed analytic budget,
source inverse, sign for the Taylor debt or scaling estimate is introduced.
The paid moment still contains an interacting higher holonomy word. This is
not a bound versus SAME surviving variance or a macroscopic response ratio.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentChannelEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound
  (familyChannelFirstOrder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentAngularCancellation
open YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage

/-- An existing literal family, not a replacement observable algebra. -/
def adjacentFaces : List Z4Plaq := [leftFace, rightFace]

def adjacentSpan (width : Nat) : RatPoly :=
  spatialSpan width (fun _ => 1) adjacentFaces

def adjacentDifference (width : Nat) : RatPoly :=
  polyAdd (leftTrace width) (polyNeg (rightTrace width))

theorem adjacent_span_pin (width : Nat) :
    RatPolyCoeffEqv (adjacentSpan width) (polyAdd (leftTrace width) (rightTrace width)) := by
  change RatPolyCoeffEqv
    (polyAdd (polySmul 1 (leftTrace width))
      (polyAdd (polySmul 1 (rightTrace width)) polyZero)) _
  exact (RatPolyCoeffEqv.one_smul _).add
    (((RatPolyCoeffEqv.one_smul _).add (RatPolyCoeffEqv.refl polyZero)).trans
      (RatPolyCoeffEqv.add_zero _))

/-- The unchanged original passive channels and complete projected terminal
source. The insertion is never identified with V*g_n*g_(n+1). -/
def adjacentChannelMoment (w : Q') (K width depth : Nat) (insertion : RatPoly) : Q' :=
  channelSquare (N width) w K (familySpectatorBlocks width adjacentFaces)
    (projectedEndpointSource w K width (terminalMessage w K width depth)) insertion

def retainedChannelSquare (w : Q') (K width depth : Nat) : Q' :=
  adjacentChannelMoment w K width depth
    (polyMul (adjacentDifference width) (adjacentDifference width))

def paidChannelMoment (w : Q') (K width depth : Nat) : Q' :=
  adjacentChannelMoment w K width depth (equalWeightPaidDensity width)

private theorem gamma_congr (ids : List Nat) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (activeGamma ids f f) (activeGamma ids g g) := by
  have hb (block : Nat) : RatPolyCoeffEqv (blockGamma block f f) (blockGamma block g g) := by
    have hd (i j : Nat) := angularDerivative_congr (4*block+i) (4*block+j) h
    unfold blockGamma six
    exact ((hd 0 1).mul (hd 0 1)).add
      (((hd 0 2).mul (hd 0 2)).add (((hd 0 3).mul (hd 0 3)).add
        (((hd 1 2).mul (hd 1 2)).add (((hd 1 3).mul (hd 1 3)).add
          ((hd 2 3).mul (hd 2 3))))))
  induction ids with
  | nil => exact RatPolyCoeffEqv.refl polyZero
  | cons i ids ih => exact (hb i).add ih

private theorem sum_add (left right : RatPoly → Q') : ∀ cs : List GramChannel,
    channelSum cs (fun z => left z+right z) ≈ channelSum cs left+channelSum cs right
  | [] => by change (0 : Q') ≈ 0+0; decide
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (sum_add left right cs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
        (fun | 0 => c.1*left c.2 | 1 => c.1*right c.2
             | 2 => channelSum cs left | _ => channelSum cs right))

/-- All original blocks and every actual channel are included. The actual
square is retained with its exact coefficient, not replaced by a norm debt. -/
theorem adjacent_channel_cancellation (w : Q') (K width depth : Nat)
    (hw : 2 ≤ width) :
    familyChannelFirstOrder w K width depth (fun _ => 1) adjacentFaces +
        retainedChannelSquare w K width depth ≈ paidChannelMoment w K width depth := by
  let ids := familySpectatorBlocks width adjacentFaces
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let cs := productChannels (N width) w K ids
  let W := fun z => polyMul (channelSource ids q z) (channelSource ids q z)
  let G := activeGamma (List.range (N width)) (adjacentSpan width) (adjacentSpan width)
  let D := polyMul (adjacentDifference width) (adjacentDifference width)
  let P := equalWeightPaidDensity width
  change channelSum cs (fun z => H (N width) (polyMul (W z) G)) +
    channelSum cs (fun z => H (N width) (polyMul (W z) D)) ≈
      channelSum cs (fun z => H (N width) (polyMul (W z) P))
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (sum_add _ _ cs)) ?_
  apply channelSum_congr
  intro c _
  let z := c.2
  have hg := gamma_congr (List.range (N width)) (adjacent_span_pin width)
  have hsum : H (N width) (polyMul (W z) G)+H (N width) (polyMul (W z) D) ≈
      H (N width) (polyMul (W z) (polyAdd G D)) :=
    Q'.eqv_symm (Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_add_right (W z) G D))
      (quaternionHaar_append (N width) _ _))
  exact Q'.eqv_trans _ _ _ hsum
    (Q'.eqv_trans _ _ _
      (haar_of_coeff ((hg.add (RatPolyCoeffEqv.refl D)).mul_left (W z)))
      (adjacent_full_angular_paid width hw (W z)))

private theorem sum_nonnegative (value : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
    (∀ c, c ∈ cs → (0 : Q') ≤ value c.2) → (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, hv => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw c List.mem_cons_self) (hv c List.mem_cons_self))
      (sum_nonnegative value cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => hv d (List.mem_cons_of_mem c hd)))

/-- Computed sign of the retained term; no positivity hypothesis for an
uncomputed correction is supplied. Cutoff zero and zero channels are allowed. -/
theorem retained_channel_square_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) : (0 : Q') ≤ retainedChannelSquare w K width depth := by
  let ids := familySpectatorBlocks width adjacentFaces
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hd : SupportedQuaternionBlocks (N width) (adjacentDifference width) := by
    have trace_supported (face : Z4Plaq) : SupportedQuaternionBlocks (N width)
        (characterPolynomial
          (BF4ExactSlabFixedSpatialSliceHeat.plaquette width face).scalar 1) :=
      SU2QuaternionRelativeHeatPairGeometry.character_supported
        (BF4ExactSlabFixedSpatialSpatialOrder.plaquette_supported width (N width)
          (Nat.le_refl _) face).scalar 1
    exact supported_add (trace_supported leftFace) (by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact trace_supported rightFace s hs)
  apply sum_nonnegative
  · exact productChannels_nonnegative (N width) hw0 K ids
  · intro z hz
    have ha := channelSource_supported (N width) w K ids
      (familySpectatorBlocks_lt width adjacentFaces) hq z hz
    exact ((Certificate.square _ ha).mul (Certificate.square _ hd)).haar_nonnegative

/-- The COMPLETE original two-face energy with the favorable subtraction
still paid. Strict padding is the existing channel-Taylor geometry guard. -/
theorem adjacent_energy_retained_square (w : Q') (K width depth : Nat)
    (hw : 2 < width) :
    energy w K width (terminalMessage w K width depth) (adjacentSpan width) +
        ((1 : Q')-w)*retainedChannelSquare w K width depth ≈
      ((1 : Q')-w)*paidChannelMoment w K width depth +
        familyChannelTaylorDebt w K width depth (fun _ => 1) adjacentFaces := by
  have hfaces : ∀ p, p ∈ adjacentFaces →
      p ∈ BF4ExactSlabFixedSpatialFacePlacement.spatialFaces 2 := by
    intro p hp
    have h := adjacent_faces_spatial 2 (Nat.le_refl _)
    simp only [adjacentFaces, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact h.1
    · exact h.2
  have he := padded_family_channel_energy_taylor w K hw depth
    (fun _ => 1) adjacentFaces hfaces
  have hc := adjacent_channel_cancellation w K width depth (Nat.le_of_lt hw)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' he (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 0) (.var 3)))
        (.add (.mul (.var 0) (.add (.var 1) (.var 3))) (.var 2))
        (by decide) (fun
          | 0 => (1 : Q')-w
          | 1 => familyChannelFirstOrder w K width depth (fun _ => 1) adjacentFaces
          | 2 => familyChannelTaylorDebt w K width depth (fun _ => 1) adjacentFaces
          | _ => retainedChannelSquare w K width depth))
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hc) (Q'.eqv_refl _)))

#print axioms adjacent_span_pin
#print axioms adjacent_channel_cancellation
#print axioms retained_channel_square_nonnegative
#print axioms adjacent_energy_retained_square

end YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentChannelEnergy
