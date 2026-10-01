/-
# Complete signed-family angular cost versus the SAME interacting variance

The actual marginal score certificates are used only on the family's literal
link footprint. Spectator derivatives vanish coefficientwise. The complete
Casimir-12 Ward identity then pays the angular cost by the original centered
variance, with an explicit nome-dependent coefficient and no full-width,
terminal-depth, late-cutoff or inverse-source-floor penalty.

This bounds the angular term, not the complete temporal energy: the original
Taylor consumer retains its entire signed remainder. The score coefficient
is not proved useful near nome one or on a physical scaling trajectory.
-/

import YMGap.Continuum.QuaternionHaarLocalRelativeWard
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint
import YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySourceVarianceBound
import YMGap.Continuum.SU2QuaternionAngularSquareLocality

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRelativeWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularSquareLocality
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarLocalRelativeWard
open YMGap.Continuum.SU2QuaternionWeightedCasimirWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram (oddCentered)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySourceVarianceBound
  (marginal_centered_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (marginalAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
  (endpointRelativeCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalRelativeBound
  (marginalRelativeBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound
  (marginalScoreCap marginalScoreCap_positive headCutoff_le_endpointRelativeCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks spatialWeight terminalMessage

private theorem qsum_append : ∀ left right : List Q',
    qListSum (left ++ right) ≈ qListSum left + qListSum right
  | [], _ => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | _::xs, right => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (qsum_append xs right))
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem qsum_perm {left right : List Q'} (h : left.Perm right) :
    qListSum left ≈ qListSum right := by
  induction h with
  | nil => exact Q'.eqv_refl _
  | cons x _ ih => exact Q'.add_eqv_congr' (Q'.eqv_refl x) ih
  | swap x y rest =>
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 1) (.add (.var 0) (.var 2))) (by decide)
        (fun | 0 => y | 1 => x | _ => qListSum rest)
  | trans _ _ ih ih' => exact Q'.eqv_trans _ _ _ ih ih'

private theorem qsum_zero (value : Nat → Q') : ∀ ids : List Nat,
    (∀ i, i ∈ ids → value i ≈ 0) → qListSum (ids.map value) ≈ 0
  | [], _ => Q'.eqv_refl _
  | i::ids, h => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (h i List.mem_cons_self)
        (qsum_zero value ids (fun j hj => h j (List.mem_cons_of_mem i hj))))
      (by decide)

private theorem remove_spectators (width : Nat) (qs : List Z4Plaq)
    (value : Nat → Q')
    (hz : ∀ i, i ∈ familySpectatorBlocks width qs → value i ≈ 0) :
    qListSum ((List.range (N width)).map value) ≈
      qListSum ((familyObservableBlocks width qs).map value) := by
  have hp := qsum_perm ((familySpectator_observable_cover width qs).map value)
  rw [List.map_append] at hp
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hp)
    (Q'.eqv_trans _ _ _ (qsum_append _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (qsum_zero value _ hz) (Q'.eqv_refl _))
        (QPoly.q_zero_add_eqv _)))

private theorem spectator_energy_zero (width : Nat) (qs : List Z4Plaq)
    (coeff : Z4Plaq → Q') (W : RatPoly) (b : Nat)
    (hb : b ∈ familySpectatorBlocks width qs) :
    blockEnergy (N width) b W (spatialSpan width coeff qs) ≈ 0 :=
  haar_of_coeff (((blockAngularSquare_zero
    (spatialSpan_familySpectator_independent width coeff qs b hb)).mul_left W).trans
      (RatPolyCoeffEqv.mul_zero_right W))

private theorem spectator_residual_zero (width : Nat) (qs : List Z4Plaq)
    (coeff : Z4Plaq → Q') (W : RatPoly) (center : Q') (b : Nat)
    (hb : b ∈ familySpectatorBlocks width qs) :
    blockResidual (N width) b W (spatialSpan width coeff qs) center ≈ 0 := by
  let f := spatialSpan width coeff qs
  have hz (i j : Nat) (hi : i < 4) (hj : j < 4) :
      H (N width) (polyMul (polyMul (polyAdd f (polySmul (-center) polyOne))
        (blockAngularDerivative b i j W)) (blockAngularDerivative b i j f)) ≈ 0 :=
    haar_of_coeff (((angularDerivative_blockIndependent_zero hi hj
      (spatialSpan_familySpectator_independent width coeff qs b hb)).mul_left _).trans
        (RatPolyCoeffEqv.mul_zero_right _))
  exact Q'.eqv_trans _ _ _ (sixValue_congr _ (fun _ _ => 0) hz) (by decide)

/-- Computed footprint count, not the full slice's link count. -/
def familyAngularVarianceFactor (w : Q') (width : Nat) (qs : List Z4Plaq) : Q' :=
  24 + 6*Q'.ofNat (familyObservableBlocks width qs).length*
    marginalScoreCap w*marginalScoreCap w

/-- A width-independent envelope; repeated faces are permitted and counted. -/
def familyLengthAngularVarianceFactor (w : Q') (qs : List Z4Plaq) : Q' :=
  24 + 6*Q'.ofNat (4*qs.length)*marginalScoreCap w*marginalScoreCap w

private theorem centered_square_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : BF4ExactSlabRetainedHeatHeadComparison.headCutoff w ≤ K)
    (n : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let center := normalizedMoment (N width) (marginalWeight w K width n) f
      (marginalMass_positive hw0 hw1 K width hK n)
    let fc := polyAdd f (polySmul (-center) polyOne)
    H (N width) (polyMul (marginalWeight w K width n) (polyMul fc fc)) ≈
      oddMass w K width n * oddVariance hw0 hw1 K width hK n f := by
  dsimp only
  let center := normalizedMoment (N width) (marginalWeight w K width n) f
    (marginalMass_positive hw0 hw1 K width hK n)
  let fc := polyAdd f (polySmul (-center) polyOne)
  have hone : RatPolyCoeffEqv (polySmul 1 f) f := by
    intro weight
    exact Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight 1 f) (Q'.one_mul_eqv _)
  have hfc : RatPolyCoeffEqv (oddCentered hw0 hw1 K width hK n f) fc :=
    hone.add (RatPolyCoeffEqv.refl _)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((hfc.symm.mul hfc.symm).mul_left (marginalWeight w K width n)))
    (marginal_centered_square hw0 hw1 K width hK n hf)

private theorem energy_of_ward (A S V B : Q')
    (hy : -(2*S) ≤ B*V+A) (hw : A+S ≈ 12*V) :
    A ≤ (24+B)*V := by
  have h0 := Q'.sub_nonneg_of_le hy
  have hrewrite : (B*V+A)+ -(-(2*S)) ≈ B*V+2*(A+S)+ -A :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1)) (.var 2))
        (.neg (.neg (.mul (.const 2) (.var 3)))))
      (.add (.add (.mul (.var 0) (.var 1))
        (.mul (.const 2) (.add (.var 2) (.var 3)))) (.neg (.var 2)))
      (by decide) (fun | 0 => B | 1 => V | 2 => A | _ => S)
  have hfinish : B*V+2*(12*V)+ -A ≈ (24+B)*V+ -A :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1))
        (.mul (.const 2) (.mul (.const 12) (.var 1)))) (.neg (.var 2)))
      (.add (.mul (.add (.const 24) (.var 0)) (.var 1)) (.neg (.var 2)))
      (by decide) (fun | 0 => B | 1 => V | _ => A)
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ hrewrite (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.mul_eqv_congr_left 2 _ _ hw)) (Q'.eqv_refl _)) hfinish))))

/-- Every score certificate is computed at a literal active physical link.
The selected link is data; no propositional existence witness is extracted. -/
def familyBlockRelativeBound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K n : Nat) {base width : Nat}
    (hwidth : base < width) (hK : endpointRelativeCutoff w ≤ K)
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (b : Nat) (hb : b ∈ familyObservableBlocks width qs)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound (N width) (4*b+i) (4*b+j)
      (marginalWeight w K width n) (marginalScoreCap w) := by
  let hlt := familyObservableBlocks_lt width qs b hb
  let selected := linkAt width b hlt
  have hidx : (baseLinks width).idxOf selected = b :=
    linkAt_idxOf width qs b hb
  have hs : (baseLinks width).idxOf selected ∈
      BF4ExactSlabFixedSpatialKineticMarginals.activeBlocks width := by
    rw [hidx]
    exact familyObservableBlocks_active_after_padding hwidth qs hqs b hb
  have R := marginalRelativeBound hw0 hw1 K width n hK selected
    (linkAt_mem width b hlt) hs hi hj
  simpa only [marginalScoreCap, hidx] using R

/-- Complete signed family, including repeated faces. The only count is
the deduplicated actual observable footprint, never the full slice width. -/
theorem family_angular_variance_cleared {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : endpointRelativeCutoff w ≤ K)
    (n : Nat) (qs : List Z4Plaq) (coeff : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
    marginalAngular w K width n (spatialSpan width coeff qs) ≤
      familyAngularVarianceFactor w width qs * (oddMass w K width n *
        oddVariance hw0 hw1 K width hhead n (spatialSpan width coeff qs)) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
  let f := spatialSpan width coeff qs
  let W := marginalWeight w K width n
  let J := familyObservableBlocks width qs
  let center := normalizedMoment (N width) W f
    (marginalMass_positive hw0 hw1 K width hhead n)
  let V := oddMass w K width n * oddVariance hw0 hw1 K width hhead n f
  let B := 6*Q'.ofNat J.length*marginalScoreCap w*marginalScoreCap w
  have he : qListSum (J.map fun b => blockEnergy (N width) b W f) ≈
      marginalAngular w K width n f :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm
      (remove_spectators width qs (fun b => blockEnergy (N width) b W f)
        (fun b hb => spectator_energy_zero width qs coeff W b hb)))
      (totalEnergy_finSum (N width) W f)
  have hs : wardResidual hw0 hw1 K width hhead n f ≈
      qListSum (J.map fun b => blockResidual (N width) b W f center) :=
    remove_spectators width qs (fun b => blockResidual (N width) b W f center)
      (fun b hb => spectator_residual_zero width qs coeff W center b hb)
  have hV := centered_square_pin hw0 hw1 K width hhead n
    (spatialSpan_supported width coeff qs)
  have hy := active_residual_lower (N width) J
    (familyObservableBlocks_lt width qs) (marginalScoreCap_positive hw0)
    (fun b hb i j hi hj => familyBlockRelativeBound hw0 hw1 K n hwidth hK
      qs hqs b hb hi hj) (spatialSpan_supported width coeff qs) center
  have hres : -(2*wardResidual hw0 hw1 K width hhead n f) ≤
      B*V + marginalAngular w K width n f :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ hs)))
      (Q'.le_trans' _ _ _ hy (Q'.le_of_eqv
        (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left B _ _ hV) he)))
  exact energy_of_ward _ _ V B hres
    (family_ward hw0 hw1 K width hhead n qs coeff
      (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp)))

/-- The same bound with an explicit coefficient independent of spatial
width, depth and every cutoff after the computed nome-dependent onset. -/
theorem family_angular_variance_length_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : endpointRelativeCutoff w ≤ K)
    (n : Nat) (qs : List Z4Plaq) (coeff : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
    marginalAngular w K width n (spatialSpan width coeff qs) ≤
      familyLengthAngularVarianceFactor w qs * (oddMass w K width n *
        oddVariance hw0 hw1 K width hhead n (spatialSpan width coeff qs)) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
  let f := spatialSpan width coeff qs
  let center := normalizedMoment (N width) (marginalWeight w K width n) f
    (marginalMass_positive hw0 hw1 K width hhead n)
  let fc := polyAdd f (polySmul (-center) polyOne)
  have hfc : SupportedQuaternionBlocks (N width) fc :=
    supported_add (spatialSpan_supported width coeff qs)
      (polySmul_supported (supported_one (N width)) (-center))
  have hraw := (marginalCertificate hw0 hw1 K width hhead n).square_insertion_nonnegative fc hfc
  have hV : (0 : Q') ≤ oddMass w K width n *
      oddVariance hw0 hw1 K width hhead n f :=
    Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm (polyMul fc fc)
        (marginalWeight w K width n)))
      (centered_square_pin hw0 hw1 K width hhead n
        (spatialSpan_supported width coeff qs))))
  have hc := Q'.le_of_lt (marginalScoreCap_positive hw0)
  have hcount := CReal.ofNat_le_ofNat (familyObservableBlocks_length_le_four width qs)
  have hfactor : familyAngularVarianceFactor w width qs ≤
      familyLengthAngularVarianceFactor w qs :=
    Q'.add_le_add (Q'.le_of_eqv (Q'.eqv_refl 24))
      (Q'.mul_le_mul_of_nonneg_right _ _ (marginalScoreCap w)
        (Q'.mul_le_mul_of_nonneg_right _ _ (marginalScoreCap w)
          (Q'.mul_le_mul_of_nonneg_left _ _ 6 hcount (by decide)) hc) hc)
  exact Q'.le_trans' _ _ _
    (family_angular_variance_cleared hw0 hw1 K hwidth hK n qs coeff hqs)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hfactor hV)

private theorem partition_cancel (B Z V : Q') (hZ : (0 : Q') < Z) :
    (B*(Z*V))*Q'.recipPos Z hZ ≈ B*V :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (by decide) (fun | 0 => B | 1 => Z | 2 => V | _ => Q'.recipPos Z hZ))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
      (Q'.mul_one_eqv _))

/-- Normalize only by the SAME proved-positive odd partition. There is no
division by the family variance or by a density minimum. -/
theorem family_normalized_angular_variance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : endpointRelativeCutoff w ≤ K)
    (n : Nat) (qs : List Z4Plaq) (coeff : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
    normalizedAngular hw0 hw1 K width hhead n (spatialSpan width coeff qs) ≤
      familyLengthAngularVarianceFactor w qs *
        oddVariance hw0 hw1 K width hhead n (spatialSpan width coeff qs) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
  let Z := oddMass w K width n
  let hZ := oddMass_positive hw0 hw1 K width hhead n
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos Z hZ)
      (family_angular_variance_length_cleared hw0 hw1 K hwidth hK n qs coeff hqs)
      (Q'.le_of_lt (Q'.recipPos_pos Z hZ)))
    (Q'.le_of_eqv (partition_cancel _ Z _ hZ))

/-- Actual temporal-energy consumer. The COMPLETE signed Taylor remainder,
including the angular-weight defect, remains on the same original law. -/
theorem padded_family_energy_relative_ward {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : endpointRelativeCutoff w ≤ K)
    (n : Nat) (qs : List Z4Plaq) (coeff : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
    normalizedEnergy hw0 hw1 K width hhead n (spatialSpan width coeff qs) ≤
      ((1 : Q')-w)*(familyLengthAngularVarianceFactor w qs *
        oddVariance hw0 hw1 K width hhead n (spatialSpan width coeff qs)) +
      normalizedRemainder hw0 hw1 K width hhead n (spatialSpan width coeff qs) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (padded_family_normalized_taylor hw0 hw1 K hwidth hhead n qs coeff hqs))
    (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ ((1 : Q')-w)
        (family_normalized_angular_variance hw0 hw1 K hwidth hK n qs coeff hqs)
        (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
      (Q'.le_of_eqv (Q'.eqv_refl _)))

#print axioms familyAngularVarianceFactor
#print axioms familyLengthAngularVarianceFactor
#print axioms familyBlockRelativeBound
#print axioms family_angular_variance_cleared
#print axioms family_angular_variance_length_cleared
#print axioms family_normalized_angular_variance
#print axioms padded_family_energy_relative_ward

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRelativeWard
