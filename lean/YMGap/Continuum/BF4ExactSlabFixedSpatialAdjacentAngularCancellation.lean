/-
# ORIGINAL neighboring spatial faces retain their shared-link interference

The origin p01 face and its positive-x0 neighbor are literal original
SliceHeat words on every width >= 2. Their seven physical links are indexed
in the ORIGINAL baseLinks carrier, not substituted into a fixture Haar law.
The shared link occurs forward in the first word and reverse in the second.
The exact angular identity holds against EVERY Haar insertion; its positive
square remainder yields a bound under the unchanged original odd marginal.

The difference trace uses both holonomies rebased at the shared link. It is
NOT the shared-link-eliminated outer rectangle. No interacting smallness,
SAME-variance estimate, signed Taylor cancellation or scaling is asserted.
-/

import YMGap.Continuum.SU2QuaternionAdjacentAngularCancellation
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
import YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentAngularCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary (SliceLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
  (haarNorm_coordinate haarNorm_mul polyQuaternionNorm_conj)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularSquare)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionAdjacentAngularCancellation
  (forwardTrace reverseTrace oriented_pair_angular_difference)
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing (first_cycle)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks marginalWeight

def leftFace : Z4Plaq := ((0,0,0,0), .p01)
def rightFace : Z4Plaq := ((1,0,0,0), .p01)

private def patchLink : Nat → Z4Link
  | 0 => ((1,0,0,0), .x1)
  | 1 => ((0,0,0,0), .x0)
  | 2 => ((1,0,0,0), .x0)
  | 3 => ((2,0,0,0), .x1)
  | 4 => ((1,1,0,0), .x0)
  | 5 => ((0,1,0,0), .x0)
  | _+6 => ((0,0,0,0), .x1)

private def slot (width i : Nat) : Nat := (baseLinks width).idxOf (patchLink i)
private def patchVariable (width i : Nat) : PolyQuaternion :=
  PolyQuaternion.coordinateVariable (slot width i)

def sharedBlock (width : Nat) : Nat := slot width 0
def leftTrace (width : Nat) : RatPoly := characterPolynomial (plaquette width leftFace).scalar 1
def rightTrace (width : Nat) : RatPoly := characterPolynomial (plaquette width rightFace).scalar 1

private def forwardTail (width : Nat) : PolyQuaternion :=
  (PolyQuaternion.conj (patchVariable width 5) ⋄ PolyQuaternion.conj (patchVariable width 6)) ⋄
    patchVariable width 1
private def reverseTail (width : Nat) : PolyQuaternion :=
  (patchVariable width 2 ⋄ patchVariable width 3) ⋄ PolyQuaternion.conj (patchVariable width 4)

def transportedDifferenceTrace (width : Nat) : RatPoly :=
  SU2QuaternionAdjacentAngularCancellation.differenceTrace (sharedBlock width)
    (forwardTail width) (reverseTail width)

private theorem patchLink_mem (width : Nat) (hw : 2 ≤ width) (i : Nat) :
    patchLink i ∈ baseLinks width := by
  apply (baseLinks_mem_iff width _).mpr
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | _+6 =>
      dsimp only [patchLink, SliceLink]
      exact ⟨by decide, by omega, by omega, by omega, rfl⟩

theorem sharedBlock_lt (width : Nat) (hw : 2 ≤ width) : sharedBlock width < N width :=
  List.idxOf_lt_length_of_mem (patchLink_mem width hw 0)

theorem adjacent_faces_spatial (width : Nat) (hw : 2 ≤ width) :
    leftFace ∈ BF4ExactSlabFixedSpatialFacePlacement.spatialFaces width ∧
      rightFace ∈ BF4ExactSlabFixedSpatialFacePlacement.spatialFaces width := by
  constructor
  · apply (spatialFaces_mem_iff width _).mpr
    exact ⟨by dsimp [leftFace]; omega, by dsimp [leftFace]; omega,
      by dsimp [leftFace]; omega, rfl, by decide⟩
  · apply (spatialFaces_mem_iff width _).mpr
    exact ⟨by dsimp [rightFace]; omega, by dsimp [rightFace]; omega,
      by dsimp [rightFace]; omega, rfl, by decide⟩

private theorem slot_ne_shared (width : Nat) (hw : 2 ≤ width) (i : Nat) (hi : i ≠ 0) :
    sharedBlock width ≠ slot width i := by
  intro he
  have h := idxOf_injective_on_members (patchLink_mem width hw 0)
    (patchLink_mem width hw i) he
  match i with
  | 0 => exact hi rfl
  | 1 | 2 | 3 | 4 | 5 | _+6 =>
      simp [patchLink] at h

private theorem variable_degree (width : Nat) (hw : 2 ≤ width) (i : Nat) (hi : i ≠ 0) :
    HasPolyQuaternionBlockDegree (sharedBlock width) 0 (patchVariable width i) := by
  have h := hasPolyQuaternionBlockDegree_coordinateVariable (slot width i) (sharedBlock width)
  simpa only [if_neg (slot_ne_shared width hw i hi)] using h

private theorem tails_degree (width : Nat) (hw : 2 ≤ width) :
    HasPolyQuaternionBlockDegree (sharedBlock width) 0 (forwardTail width) ∧
      HasPolyQuaternionBlockDegree (sharedBlock width) 0 (reverseTail width) := by
  exact ⟨((variable_degree width hw 5 (by decide)).conj.mul
    (variable_degree width hw 6 (by decide)).conj).mul
      (variable_degree width hw 1 (by decide)),
    ((variable_degree width hw 2 (by decide)).mul
      (variable_degree width hw 3 (by decide))).mul
        (variable_degree width hw 4 (by decide)).conj⟩

private theorem variable_unit (width : Nat) (hw : 2 ≤ width) (i : Nat) :
    HaarCarrierEqv (N width) (polyQuaternionNorm (patchVariable width i)) polyOne :=
  haarNorm_coordinate (List.idxOf_lt_length_of_mem (patchLink_mem width hw i))

private theorem variable_conj_unit (width : Nat) (hw : 2 ≤ width) (i : Nat) :
    HaarCarrierEqv (N width) (polyQuaternionNorm (PolyQuaternion.conj (patchVariable width i)))
      polyOne :=
  (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans (variable_unit width hw i)

private theorem tails_unit (width : Nat) (hw : 2 ≤ width) :
    HaarCarrierEqv (N width) (polyQuaternionNorm (forwardTail width)) polyOne ∧
      HaarCarrierEqv (N width) (polyQuaternionNorm (reverseTail width)) polyOne :=
  ⟨haarNorm_mul (haarNorm_mul (variable_conj_unit width hw 5) (variable_conj_unit width hw 6))
      (variable_unit width hw 1),
    haarNorm_mul (haarNorm_mul (variable_unit width hw 2) (variable_unit width hw 3))
      (variable_conj_unit width hw 4)⟩

private theorem link_variable (width : Nat) (hw : 2 ≤ width) (i : Nat) :
    link width (patchLink i) = patchVariable width i := by
  unfold link
  rw [if_pos (patchLink_mem width hw i)]
  rfl

private theorem original_words (width : Nat) (hw : 2 ≤ width) :
    PolyQuaternionCoeffEqv (plaquette width leftFace)
      (((patchVariable width 1 ⋄ patchVariable width 0) ⋄ PolyQuaternion.conj (patchVariable width 5)) ⋄
        PolyQuaternion.conj (patchVariable width 6)) ∧
    PolyQuaternionCoeffEqv (plaquette width rightFace)
      (((patchVariable width 2 ⋄ patchVariable width 3) ⋄ PolyQuaternion.conj (patchVariable width 4)) ⋄
        PolyQuaternion.conj (patchVariable width 0)) := by
  have hl : plaquette width leftFace =
      ((((PolyQuaternion.one ⋄ link width (patchLink 1)) ⋄ link width (patchLink 0)) ⋄
        PolyQuaternion.conj (link width (patchLink 5))) ⋄
        PolyQuaternion.conj (link width (patchLink 6))) := rfl
  have hr : plaquette width rightFace =
      ((((PolyQuaternion.one ⋄ link width (patchLink 2)) ⋄ link width (patchLink 3)) ⋄
        PolyQuaternion.conj (link width (patchLink 4))) ⋄
        PolyQuaternion.conj (link width (patchLink 0))) := rfl
  rw [hl, hr, link_variable width hw 0, link_variable width hw 1,
    link_variable width hw 2, link_variable width hw 3, link_variable width hw 4,
    link_variable width hw 5, link_variable width hw 6]
  exact ⟨(((PolyQuaternionCoeffEqv.one_mul _).mul (.refl _)).mul (.refl _)).mul (.refl _),
    (((PolyQuaternionCoeffEqv.one_mul _).mul (.refl _)).mul (.refl _)).mul (.refl _)⟩

theorem original_adjacent_trace_pins (width : Nat) (hw : 2 ≤ width) :
    RatPolyCoeffEqv (leftTrace width) (forwardTrace (sharedBlock width) (forwardTail width)) ∧
      RatPolyCoeffEqv (rightTrace width) (reverseTrace (sharedBlock width) (reverseTail width)) := by
  have h := original_words width hw
  have hc := first_cycle (patchVariable width 1) (patchVariable width 0)
    (PolyQuaternion.conj (patchVariable width 5)) (PolyQuaternion.conj (patchVariable width 6))
  have hs := polyQuaternion_mul_scalar_cyclic (forwardTail width) (patchVariable width 0)
  exact ⟨(h.1.scalar.trans (hc.trans hs)).smul 2, h.2.scalar.smul 2⟩

private theorem square_congr (block : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (blockAngularSquare block p) (blockAngularSquare block q) := by
  have hd (i j : Nat) := angularDerivative_congr (4*block+i) (4*block+j) h
  unfold blockAngularSquare six
  exact ((hd 0 1).mul (hd 0 1)).add
    (((hd 0 2).mul (hd 0 2)).add (((hd 0 3).mul (hd 0 3)).add
      (((hd 1 2).mul (hd 1 2)).add (((hd 1 3).mul (hd 1 3)).add
        ((hd 2 3).mul (hd 2 3))))))

/-- Every insertion, including the ORIGINAL full interacting action, is retained. -/
theorem original_adjacent_angular_difference (width : Nat) (hw : 2 ≤ width) :
    HaarCarrierEqv (N width)
      (polyAdd (blockAngularSquare (sharedBlock width) (polyAdd (leftTrace width) (rightTrace width)))
        (polyMul (polyAdd (leftTrace width) (polyNeg (rightTrace width)))
          (polyAdd (leftTrace width) (polyNeg (rightTrace width)))))
      (polySmul 4 (polyAdd (cap 2) (polyNeg (transportedDifferenceTrace width)))) := by
  have ht := original_adjacent_trace_pins width hw
  have hd := ht.1.add (RatPolyCoeffEqv.neg ht.2)
  exact (RatPolyCoeffEqv.haarCarrier
    ((square_congr _ (ht.1.add ht.2)).add (hd.mul hd))).trans
      (oriented_pair_angular_difference (sharedBlock_lt width hw) _ _
        (tails_degree width hw).1 (tails_degree width hw).2
        (tails_unit width hw).1 (tails_unit width hw).2)

/-- Drop only the actual supported difference square under the SAME positive weight. -/
theorem original_adjacent_weighted_angular_le (width : Nat) (hw : 2 ≤ width)
    (W : RatPoly) (PW : Certificate (N width) W) :
    quaternionHaar (N width) (polyMul W
      (blockAngularSquare (sharedBlock width) (polyAdd (leftTrace width) (rightTrace width)))) ≤
      4*quaternionHaar (N width) (polyMul W
        (polyAdd (cap 2) (polyNeg (transportedDifferenceTrace width)))) := by
  let f := polyAdd (leftTrace width) (rightTrace width)
  let d := polyAdd (leftTrace width) (polyNeg (rightTrace width))
  let A := blockAngularSquare (sharedBlock width) f
  let B := polyAdd (cap 2) (polyNeg (transportedDifferenceTrace width))
  have hd : SupportedQuaternionBlocks (N width) d :=
    supported_add (character_supported (plaquette_supported width (N width) (Nat.le_refl _) leftFace).scalar 1)
      (by
        intro t ht
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
        exact character_supported
          (plaquette_supported width (N width) (Nat.le_refl _) rightFace).scalar 1 s hs)
  have hz := (PW.mul (Certificate.square d hd)).haar_nonnegative
  have he : quaternionHaar (N width) (polyMul W A)+
      quaternionHaar (N width) (polyMul W (polyMul d d)) ≈
        4*quaternionHaar (N width) (polyMul W B) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_add_right W A (polyMul d d)))
        (quaternionHaar_append (N width) _ _)))
      (Q'.eqv_trans _ _ _ (original_adjacent_angular_difference width hw W)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right 4 W B))
          (quaternionHaar_polySmul (N width) 4 (polyMul W B))))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hz) (Q'.le_of_eqv he)

/-- Actual original depth-n odd marginal, with all spatial and terminal factors. -/
theorem original_adjacent_marginal_angular_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (hw : 2 ≤ width) (n : Nat) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (blockAngularSquare (sharedBlock width) (polyAdd (leftTrace width) (rightTrace width)))) ≤
      4*quaternionHaar (N width) (polyMul (marginalWeight w K width n)
        (polyAdd (cap 2) (polyNeg (transportedDifferenceTrace width)))) :=
  original_adjacent_weighted_angular_le width hw _ (marginalCertificate hw0 hw1 K width hK n)

#print axioms leftFace
#print axioms rightFace
#print axioms sharedBlock
#print axioms leftTrace
#print axioms rightTrace
#print axioms transportedDifferenceTrace
#print axioms sharedBlock_lt
#print axioms adjacent_faces_spatial
#print axioms original_adjacent_trace_pins
#print axioms original_adjacent_angular_difference
#print axioms original_adjacent_weighted_angular_le
#print axioms original_adjacent_marginal_angular_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentAngularCancellation
