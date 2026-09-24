/-
# Geometric square cap for the dyadic Wilson spectator channels

The literal fundamental Wilson character has the exact cap four inherited
from the Haar-unit quaternion word.  Summing the resulting square certificate
against the nonnegative computed channel weights gives `M <= 4*A` for the
actual signed projected-source channels.  No cutoff floor or normalization is
used.
-/

import YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Continuum.SU2QuaternionFamilyChannelLoss

namespace YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.ClusterCount4DProgress (Z4Link)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
  (polyQuaternionNorm_conj polyQuaternionNorm_one haarNorm_coordinate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceWord sourceWord_supported sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyChannelLoss (familyChannelQuadratic)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarWordDifference (word_unit)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks terminalMessage

/-- SAME conditional source mass used by the dyadic channel cost. -/
def squareChannelMass (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly) : Q' :=
  familyChannelQuadratic (N width) w K (spectatorBlocks scale width hwidth)
    (projectedEndpointSource w K width g)

/-- Square-inserted moment in the same computed spectator channels. -/
def squareChannelMoment (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly) : Q' :=
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
    (fun c => H width (polyMul
      (polyMul (squareChannelSource w K scale width hwidth g c)
        (squareChannelSource w K scale width hwidth g c))
      (polyMul f f)))

/-- Integrated cap-four defect, retaining the full signed channel sources. -/
def squareChannelGeometricCost (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly) : Q' :=
  (4 : Q') * squareChannelMass w K scale width hwidth g +
    -(squareChannelMoment w K scale width hwidth g)

private theorem source_link_unit (width : Nat) (l : Z4Link) :
    HaarCarrierEqv (N width) (polyQuaternionNorm (link width l)) polyOne := by
  unfold link
  split
  · exact haarNorm_coordinate (List.idxOf_lt_length_of_mem ‹l ∈ baseLinks width›)
  · exact RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one

private theorem source_oriented_unit (width : Nat) (entry : OrientedBF4Link) :
    HaarCarrierEqv (N width) (polyQuaternionNorm (orientedLink width entry)) polyOne := by
  unfold orientedLink
  split
  · exact (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans
      (source_link_unit width entry.link)
  · exact source_link_unit width entry.link

private theorem sourceWord_unit (width : Nat) (edges : List OrientedBF4Link) :
    HaarCarrierEqv (N width) (polyQuaternionNorm (sourceWord width edges)) polyOne := by
  unfold sourceWord
  exact word_unit (orientedLink width) edges
    (fun e _ => source_oriented_unit width e)

/-- The actual fundamental square has cap four independently of its perimeter. -/
def paddedSquareSquareBound (scale width : Nat) (hwidth : side scale < width) :
    SquareBound (N width)
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1) 4 :=
  let hs := sourceWord_supported width (paddedSquare scale width hwidth).edges
  SquareBound.changeCap (by decide : characterBound 1 ≈ (4 : Q'))
    (character_squareBound
      (SquareBound.scalar
        (⟨hs.scalar, hs.iPart, hs.jPart, hs.kPart⟩)
        (sourceWord_unit width (paddedSquare scale width hwidth).edges)) 1)

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c :: cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left c.1 _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_le (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → left c.2 ≤ right c.2) →
      channelSum cs left ≤ channelSum cs right
  | [], _, _ => Q'.le_refl' _
  | c :: cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (h c List.mem_cons_self) (hw c List.mem_cons_self))
      (channelSum_le left right cs
        (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_nonnegative (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → (0 : Q') ≤ value c.2) →
      (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | c :: cs, hw, h => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw c List.mem_cons_self) (h c List.mem_cons_self))
      (channelSum_nonnegative value cs
        (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_scale (a : Q') (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => a * value c) ≈ a * channelSum cs value
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c :: cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_scale a value cs))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.var 3)))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3)))
        (by decide)
        (fun | 0 => c.1 | 1 => a | 2 => value c.2
             | _ => channelSum cs value))

private theorem tested_square_le_four (scale width : Nat)
    (hwidth : side scale < width) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    H width (polyMul (polyMul q q) (polyMul f f)) ≤
      (4 : Q') * H width (polyMul q q) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  have hn := ((Certificate.square q hq).mul
    (paddedSquareSquareBound scale width hwidth).certificate).haar_nonnegative
  have he : H width (polyMul (polyMul q q) (gap 4 f)) ≈
      (4 : Q') * H width (polyMul q q) +
        -(H width (polyMul (polyMul q q) (polyMul f f))) := by
    have hc0 : H width (polyMul (polyMul q q) (cap 4)) ≈
        (4 : Q') * H width (polyMul (polyMul q q) polyOne) := by
      unfold cap
      exact quaternionHaar_polyMul_smul_right (N width) 4 (polyMul q q) polyOne
    have hone : H width (polyMul (polyMul q q) polyOne) ≈
        H width (polyMul q q) :=
      haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul q q))
    have hc : H width (polyMul (polyMul q q) (cap 4)) ≈
        (4 : Q') * H width (polyMul q q) :=
      Q'.eqv_trans _ _ _ hc0 (Q'.mul_eqv_congr_left 4 _ _ hone)
    have hneg : H width (polyMul (polyMul q q) (polyNeg (polyMul f f))) ≈
        -(H width (polyMul (polyMul q q) (polyMul f f))) :=
      Q'.eqv_trans _ _ _
        (haar_of_coeff ((RatPolyCoeffEqv.refl (polyMul q q)).mul
          (neg_smul (polyMul f f))))
        (Q'.eqv_trans _ _ _
          (quaternionHaar_polyMul_smul_right (N width) (-1)
            (polyMul q q) (polyMul f f))
          (poly_identity_of_normal_eq
            (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
            (by decide)
            (fun _ => H width (polyMul (polyMul q q) (polyMul f f)))))
    exact Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_add_right (N width) (polyMul q q)
        (cap 4) (polyNeg (polyMul f f)))
      (Q'.add_eqv_congr' hc hneg)
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- The complete conditional source mass is nonnegative. -/
theorem squareChannelMass_nonnegative {w : Q'}
    (hw0 : (0 : Q') ≤ w) (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) :
    (0 : Q') ≤ squareChannelMass w K scale width hwidth g := by
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := fun c => squareChannelSource w K scale width hwidth g c
  have hw := productChannels_nonnegative (N width) hw0 K
    (spectatorBlocks scale width hwidth)
  have hn := channelSum_nonnegative (fun c => H width (polyMul (b c) (b c))) cs hw
    (fun c hc => (Certificate.square (b c.2)
      (squareChannelSource_supported w K scale width hwidth g hg c hc)).haar_nonnegative)
  exact Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (by
    dsimp [squareChannelMass, familyChannelQuadratic, cs, b,
      squareChannelSource, channelSource]
    exact Q'.eqv_refl _))

/-- The literal cap-four certificate bounds the exact square-inserted channel
moment by four times the SAME conditional channel quadratic. -/
theorem squareChannelMoment_le_four_mass {w : Q'}
    (hw0 : (0 : Q') ≤ w) (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) :
    squareChannelMoment w K scale width hwidth g ≤
      (4 : Q') * squareChannelMass w K scale width hwidth g := by
  let ids := spectatorBlocks scale width hwidth
  let cs := productChannels (N width) w K ids
  let b := fun c => squareChannelSource w K scale width hwidth g c
  let mass := fun c => H width (polyMul (b c) (b c))
  have hw := productChannels_nonnegative (N width) hw0 K ids
  have hpoint : squareChannelMoment w K scale width hwidth g ≤
      channelSum cs (fun c => (4 : Q') * mass c) :=
    channelSum_le _ (fun c => (4 : Q') * mass c) cs hw (fun c hc =>
      tested_square_le_four scale width hwidth (b c.2)
        (squareChannelSource_supported w K scale width hwidth g hg c hc))
  have hmass : channelSum cs mass ≈
      familyChannelQuadratic (N width) w K ids
        (projectedEndpointSource w K width g) := by
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ hpoint
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (channelSum_scale 4 mass cs)
      (Q'.mul_eqv_congr_left 4 _ _ hmass)))

/-- Nonnegativity of the exact integrated defect `4*A-M`. -/
theorem squareChannelGeometricCost_nonnegative {w : Q'}
    (hw0 : (0 : Q') ≤ w) (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) :
    (0 : Q') ≤ squareChannelGeometricCost w K scale width hwidth g :=
  Q'.sub_nonneg_of_le
    (squareChannelMoment_le_four_mass hw0 K scale width hwidth g hg)

#print axioms squareChannelMass
#print axioms squareChannelMoment
#print axioms squareChannelGeometricCost
#print axioms paddedSquareSquareBound
#print axioms squareChannelMass_nonnegative
#print axioms squareChannelMoment_le_four_mass
#print axioms squareChannelGeometricCost_nonnegative

end YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
