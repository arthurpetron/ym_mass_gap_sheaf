/-
# Spectator-channel contraction of the plaquette vector defect

The conditional Gram channels retain the passive heat.  The three literal
nonscalar plaquette components give the sum-of-squares form of the geometric
gap; each component therefore contracts by the existing weighted Bessel
estimate.  No partial `productMap` identity is asserted.
-/

import YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
  (plaquetteVector_independent_index)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungGeometricBudget
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks plaquette

/-- The conditional passive-channel square with one retained multiplier. -/
def componentChannelCost (width : Nat) (face : Z4Plaq) (w : Q') (K : Nat)
    (q r : RatPoly) : Q' :=
  channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
    H width (polyMul
      (polyMul (channelSource (spectatorBlocks width face) q c)
        (channelSource (spectatorBlocks width face) q c))
      (polyMul r r)))

/-- The three-square conditional form underlying `4-f^2`. -/
def channelVectorCost (width : Nat) (face : Z4Plaq) (w : Q') (K : Nat)
    (q : RatPoly) : Q' :=
  componentChannelCost width face w K q (plaquette width face).iPart +
    (componentChannelCost width face w K q (plaquette width face).jPart +
      componentChannelCost width face w K q (plaquette width face).kPart)

/-- The conditional channel version of the literal geometric source cost. -/
def channelGeometricCost (width : Nat) (face : Z4Plaq) (w : Q') (K : Nat)
    (q : RatPoly) : Q' :=
  channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
    geometricSourceCost width face
      (channelSource (spectatorBlocks width face) q c))

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_add (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => left c + right c) ≈
        channelSum cs left + channelSum cs right
  | [] => Q'.eqv_refl _
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (channelSum_add left right cs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide) (fun | 0 => c.1*left c.2 | 1 => c.1*right c.2
                          | 2 => channelSum cs left | _ => channelSum cs right))

private theorem channelSum_scale (a : Q') (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => a * value c) ≈ a * channelSum cs value
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c.1 | 1 => a | _ => value c.2))
        (channelSum_scale a value cs))
      (Q'.eqv_symm (Q'.mul_add_eqv a _ _))

private theorem component_spectator_independent (width : Nat) (face : Z4Plaq)
    (i : Nat) (hi : i ∈ spectatorBlocks width face) :
    QuaternionBlockIndependent i (plaquette width face).iPart ∧
      QuaternionBlockIndependent i (plaquette width face).jPart ∧
      QuaternionBlockIndependent i (plaquette width face).kPart := by
  apply plaquetteVector_independent_index width face i
    (spectatorBlocks_lt width face i hi)
  intro l hl hlbase heq
  have hslot := faceSlot_mem width face hl
  have hobs : i ∈ observableBlocks width face := by
    apply List.mem_filter.mpr
    exact ⟨(List.mem_filter.mp hi).1, by
      have : i ∈ faceSlots width face := by simpa [heq] using hslot
      simp [this]⟩
  exact False.elim (spectator_not_observable width face i hi hobs)

private theorem add_le_add {a b c d : Q'} (hab : a ≤ b) (hcd : c ≤ d) :
    a+c ≤ b+d := Q'.add_le_add hab hcd

/-- The complete conditional three-vector cost is no larger than its raw
source-square counterpart.  This is three applications of weighted Bessel,
not a claim that the conditional form is a partial product map. -/
theorem channelVectorCost_le_raw (width : Nat) (face : Z4Plaq) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    channelVectorCost width face w K q ≤
      H width (polyMul (polyMul q q)
        (polyAdd (polyMul (plaquette width face).iPart (plaquette width face).iPart)
          (polyAdd (polyMul (plaquette width face).jPart (plaquette width face).jPart)
            (polyMul (plaquette width face).kPart (plaquette width face).kPart)))) := by
  let p := plaquette width face
  have hp := plaquette_supported width (N width) (Nat.le_refl _) face
  have hnd : (spectatorBlocks width face).Nodup :=
    List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width))
  have hi := productChannels_familyProject_weighted_square_le (N width) hw0 hw1 K
    (spectatorBlocks width face) hnd (spectatorBlocks_lt width face) q p.iPart hq hp.iPart
    (fun i hi => (component_spectator_independent width face i hi).1)
  have hj := productChannels_familyProject_weighted_square_le (N width) hw0 hw1 K
    (spectatorBlocks width face) hnd (spectatorBlocks_lt width face) q p.jPart hq hp.jPart
    (fun i hi => (component_spectator_independent width face i hi).2.1)
  have hk := productChannels_familyProject_weighted_square_le (N width) hw0 hw1 K
    (spectatorBlocks width face) hnd (spectatorBlocks_lt width face) q p.kPart hq hp.kPart
    (fun i hi => (component_spectator_independent width face i hi).2.2)
  unfold channelVectorCost componentChannelCost
  have hjk := quaternionHaar_polyMul_add_right (N width) (polyMul q q)
    (polyMul p.jPart p.jPart) (polyMul p.kPart p.kPart)
  have hall := Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_add_right (N width) (polyMul q q)
      (polyMul p.iPart p.iPart)
      (polyAdd (polyMul p.jPart p.jPart) (polyMul p.kPart p.kPart)))
    (Q'.add_eqv_congr_left _ _ _ hjk)
  exact Q'.le_trans' _ _ _ (add_le_add hi (add_le_add hj hk))
    (Q'.le_of_eqv hall.symm)

private def vectorSquare (p : PolyQuaternion) : RatPoly :=
  polyAdd (polyMul p.iPart p.iPart)
    (polyAdd (polyMul p.jPart p.jPart) (polyMul p.kPart p.kPart))

private theorem plaquette_gap_vector_carrier (width : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (N width)
      (gap 4 (characterPolynomial (plaquette width face).scalar 1))
      (polySmul 4 (vectorSquare (plaquette width face))) := by
  let p := plaquette width face
  have hcoeff : RatPolyCoeffEqv
      (gap 4 (characterPolynomial p.scalar 1))
      (polySmul 4 (polyAdd polyOne (polyNeg (polyMul p.scalar p.scalar)))) := by
    change RatPolyCoeffEqv
      (polyAdd (polySmul 4 polyOne)
        (polyNeg (polyMul (polySmul 2 p.scalar) (polySmul 2 p.scalar)))) _
    have hleft := (cap_mul_left 4 polyOne).symm.add
      (RatPolyCoeffEqv.neg
        ((cap_mul_left 2 p.scalar).symm.mul (cap_mul_left 2 p.scalar).symm))
    have hring := coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.const 4) (.var 0))
        (.neg (.mul (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 1)))))
      (.mul (.const 4) (.add (.var 0) (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => polyOne | _ => p.scalar)
    exact hleft.trans (hring.trans (cap_mul_left 4 _))
  have hnorm := BF4ExactSlabFixedSpatialSpatialOrder.plaquette_unit
    width (N width) (Nat.le_refl _) face
  have hreplace : HaarCarrierEqv (N width)
      (polyAdd polyOne (polyNeg (polyMul p.scalar p.scalar)))
      (polyAdd (polyQuaternionNorm p) (polyNeg (polyMul p.scalar p.scalar))) :=
    HaarCarrierEqv.add hnorm.symm (HaarCarrierEqv.refl _ _)
  have hvector : RatPolyCoeffEqv
      (polyAdd (polyQuaternionNorm p) (polyNeg (polyMul p.scalar p.scalar)))
      (vectorSquare p) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.mul (.var 0) (.var 0))
          (.add (.mul (.var 1) (.var 1))
            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
        (.neg (.mul (.var 0) (.var 0))))
      (.add (.mul (.var 1) (.var 1))
        (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))
      (by decide) (fun | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | _ => p.kPart)
  exact (RatPolyCoeffEqv.haarCarrier hcoeff).trans
    ((HaarCarrierEqv.smul 4 hreplace).trans
      (RatPolyCoeffEqv.haarCarrier (hvector.smul 4)))

private theorem geometric_eq_four_vector (width : Nat) (face : Z4Plaq) (q : RatPoly) :
    geometricSourceCost width face q ≈
      (4 : Q') * H width (polyMul (polyMul q q) (vectorSquare (plaquette width face))) := by
  exact Q'.eqv_trans _ _ _ (geometricSourceCost_eq_haar_gap width face q)
    (Q'.eqv_trans _ _ _
      (plaquette_gap_vector_carrier width face (polyMul q q))
      (quaternionHaar_polyMul_smul_right (N width) 4 (polyMul q q)
        (vectorSquare (plaquette width face))))

/-- The passive-channel geometric source cost contracts to the original raw
geometric source cost.  This is the requested gap-weighted Bessel estimate. -/
theorem channelGeometricCost_le_raw (width : Nat) (face : Z4Plaq) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    channelGeometricCost width face w K q ≤ geometricSourceCost width face q := by
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let b := fun c => channelSource (spectatorBlocks width face) q c
  have hrewrite : channelGeometricCost width face w K q ≈
      (4 : Q') * channelVectorCost width face w K q := by
    unfold channelGeometricCost channelVectorCost componentChannelCost
    have hc := channelSum_congr
      (fun c => geometricSourceCost width face (b c))
      (fun c => (4 : Q') * H width
        (polyMul (polyMul (b c) (b c)) (vectorSquare (plaquette width face))))
      cs (fun c _ => geometric_eq_four_vector width face (b c.2))
    exact Q'.eqv_trans _ _ _ hc
      (Q'.eqv_trans _ _ _ (channelSum_scale 4 _ cs)
        (Q'.mul_eqv_congr_left 4 _ _ (Q'.eqv_trans _ _ _
          (channelSum_congr _ _ cs (fun c _ => Q'.eqv_trans _ _ _
            (quaternionHaar_polyMul_add_right (N width) (polyMul (b c.2) (b c.2))
              (polyMul (plaquette width face).iPart (plaquette width face).iPart)
              (polyAdd
                (polyMul (plaquette width face).jPart (plaquette width face).jPart)
                (polyMul (plaquette width face).kPart (plaquette width face).kPart)))
            (Q'.add_eqv_congr_left _ _ _
              (quaternionHaar_polyMul_add_right (N width) (polyMul (b c.2) (b c.2))
                (polyMul (plaquette width face).jPart (plaquette width face).jPart)
                (polyMul (plaquette width face).kPart (plaquette width face).kPart)))))
          (Q'.eqv_trans _ _ _ (channelSum_add _ _ cs)
            (Q'.add_eqv_congr_left _ _ _ (channelSum_add _ _ cs))))))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (4 : Q')
    (channelVectorCost_le_raw width face hw0 hw1 K q hq) (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv
      (geometric_eq_four_vector width face q).symm))

/-- The companion raw mass contraction uses the same computed channels. -/
theorem channelSourceMass_le_raw (width : Nat) (face : Z4Plaq) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    channelSum (productChannels (N width) w K (spectatorBlocks width face))
      (fun c => rawSourceMass width (channelSource (spectatorBlocks width face) q c)) ≤
      rawSourceMass width q := by
  have hbase := productChannels_familyProject_square_le (N width) hw0 hw1 K
    (spectatorBlocks width face)
    (List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width)))
    (spectatorBlocks_lt width face) q hq
  let b := fun c => channelSource (spectatorBlocks width face) q c
  have hleft := channelSum_congr
    (fun c => rawSourceMass width (b c))
    (fun c => H width (polyMul (b c) (b c)))
    (productChannels (N width) w K (spectatorBlocks width face))
    (fun c _ => haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul (b c.2) (b c.2))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv
      (haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul q q))).symm))

/-- Retaining spectator heat never enlarges the complete geometric budget.
The two weights are nonnegative; the geometric contraction was proved via
three squares, not by subtracting two Bessel inequalities. -/
theorem channelBudget_le_raw (width : Nat) (face : Z4Plaq) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    channelSum (productChannels (N width) w K (spectatorBlocks width face))
      (fun c => geometricBudget w width face
        (channelSource (spectatorBlocks width face) q c)) ≤
      geometricBudget w width face q := by
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let b := fun c => channelSource (spectatorBlocks width face) q c
  let alpha : Q' := 8*(1-w)
  let beta : Q' := 960*((1-w)*(1-w))
  have heps := Q'.sub_nonneg_of_le hw1
  have ha : (0 : Q') ≤ alpha := Q'.mul_nonneg _ _ (by decide) heps
  have hb : (0 : Q') ≤ beta :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ heps heps)
  have hsplit : channelSum cs (fun c => geometricBudget w width face (b c)) ≈
      alpha * channelGeometricCost width face w K q +
        beta * channelSum cs (fun c => rawSourceMass width (b c)) :=
    Q'.eqv_trans _ _ _ (channelSum_add _ _ cs)
      (Q'.add_eqv_congr' (channelSum_scale alpha _ cs) (channelSum_scale beta _ cs))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ alpha
        (channelGeometricCost_le_raw width face hw0 hw1 K q hq) ha)
      (Q'.mul_le_mul_of_nonneg_left _ _ beta
        (channelSourceMass_le_raw width face hw0 hw1 K q hq) hb))

/-- Actual terminal-source consumer of the coefficient-one refinement. -/
theorem passiveGeometricBudget_le_original {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K width depth : Nat) (face : Z4Plaq) :
    passiveGeometricBudget w K width depth face ≤
      geometricBudget w width face
        (projectedEndpointSource w K width (terminalMessage w K width depth)) :=
  channelBudget_le_raw width face hw0 hw1 K _
    (familyProject_supported (fringeBlocks width)
      (supported_polyMul
        (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction.componentChannelCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction.channelVectorCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction.channelVectorCost_le_raw
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction.channelGeometricCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction.channelGeometricCost_le_raw
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction.channelSourceMass_le_raw
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction.channelBudget_le_raw
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction.passiveGeometricBudget_le_original
