/-
# Original active Wilson-loop time increments at every nome

The complete original central edge and positive odd-window partition remain
unchanged. A literal ordered-word telescope and finite Cauchy inequality turn
the proved one-link kinetic alignment into a squared path-length bound.
The active-edge premise is essential: SourceLoop.physical alone permits
uncoupled fringe links. This is an upper energy bound for the fundamental
Wilson character, not a lower variance bound, mass gap, or continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding
import YMGap.Continuum.QuaternionHaarChordalDifference
import YMGap.Continuum.QuaternionHaarWordLift

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (includeLoop_edges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding (includedLoop_edges_active)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.QuaternionHaarWordLift
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarChordalDifference
open YMGap.Continuum.SU2HeatFusionCutoffError

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks terminalMessage oddMass

/-- Explicit nome/cutoff cost; no width, time-depth, or path-size constant. -/
def displacementRate (w : Q') (K : Nat) : Q' := (2 + -(coeffW w 1)) + cutoffError w K

private theorem rearrange (c z j e : Q') (h : c*z ≤ j+e*z) :
    2*z + -j ≤ ((2 + -c)+e)*z := by
  have hi := Q'.add_le_add_right _ _ ((2*z + -(c*z)) + -j) h
  have hl : c*z + ((2*z + -(c*z)) + -j) ≈ 2*z + -j :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.add (.add (.mul (.const 2) (.var 1)) (.neg (.mul (.var 0) (.var 1)))) (.neg (.var 2))))
      (.add (.mul (.const 2) (.var 1)) (.neg (.var 2))) (by decide)
      (fun | 0 => c | 1 => z | 2 => j | _ => e)
  have hr : (j+e*z) + ((2*z + -(c*z)) + -j) ≈ ((2 + -c)+e)*z :=
    poly_identity_of_normal_eq
      (.add (.add (.var 2) (.mul (.var 3) (.var 1)))
        (.add (.add (.mul (.const 2) (.var 1)) (.neg (.mul (.var 0) (.var 1)))) (.neg (.var 2))))
      (.mul (.add (.add (.const 2) (.neg (.var 0))) (.var 3)) (.var 1)) (by decide)
      (fun | 0 => c | 1 => z | 2 => j | _ => e)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ hi (Q'.le_of_eqv hr))

/-- The original one-link four-coordinate displacement, with all spatial
weights and both terminal messages present, is bounded by the same mass. -/
theorem link_displacement_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth i : Nat) (hi : i ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width depth))
        (polyQuaternionNorm (difference (PolyQuaternion.coordinateVariable i)
          (PolyQuaternion.coordinateVariable (N width+i))))) ≤
      displacementRate w K * oddMass w K width depth := by
  have hin := activeBlocks_lt width i hi
  let W := edgeDensity w K width (terminalMessage w K width depth)
  have hc := norm_difference_character
    (haarNorm_coordinate (by omega : i < N width+N width))
    (haarNorm_coordinate (by omega : N width+i < N width+N width)) W
  have hm : quaternionHaar (N width+N width) (polyMul W (cap 2)) ≈
      2*oddMass w K width depth :=
    Q'.eqv_trans _ _ _ (weighted_scale _ W polyOne 2)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_one W)) (edge_total_mass w K width depth)))
  have he := Q'.eqv_trans _ _ _ hc
    (Q'.eqv_trans _ _ _ (weighted_difference _ W _ _)
      (Q'.add_eqv_congr' hm (Q'.eqv_refl _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (rearrange _ _ _ _ (alignment_cleared hw0 hw1 K width hK depth i hi))

/-- Literal opposite-slice coordinate, with the same traversal orientation.
Its support is asserted only for supplied physical source edges. -/
def upperOriented (width : Nat) (e : OrientedBF4Link) : PolyQuaternion :=
  let q := PolyQuaternion.coordinateVariable (N width+(baseLinks width).idxOf e.link)
  if e.reverse then PolyQuaternion.conj q else q

private theorem lower_supported {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) : Supported (N width+N width) (orientedLink width e) := by
  have hi := List.idxOf_lt_length_of_mem he
  have hs : Supported (N width+N width) (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf e.link)) :=
    Supported.coordinate (by omega)
  unfold orientedLink link
  rw [if_pos he]
  split
  · exact hs.conj
  · exact hs

private theorem upper_supported {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) : Supported (N width+N width) (upperOriented width e) := by
  have hi := List.idxOf_lt_length_of_mem he
  have hs : Supported (N width+N width)
      (PolyQuaternion.coordinateVariable (N width+(baseLinks width).idxOf e.link)) := Supported.coordinate (by omega)
  unfold upperOriented
  split
  · exact hs.conj
  · exact hs

private theorem lower_unit {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    HaarCarrierEqv (N width+N width) (polyQuaternionNorm (orientedLink width e)) polyOne := by
  have hi := List.idxOf_lt_length_of_mem he
  have hu := haarNorm_coordinate (by omega : (baseLinks width).idxOf e.link < N width+N width)
  unfold orientedLink link
  rw [if_pos he]
  split
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hu
  · exact hu

private theorem upper_unit {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    HaarCarrierEqv (N width+N width) (polyQuaternionNorm (upperOriented width e)) polyOne := by
  have hi := List.idxOf_lt_length_of_mem he
  have hu := haarNorm_coordinate (by omega : N width+(baseLinks width).idxOf e.link < N width+N width)
  unfold upperOriented
  split
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hu
  · exact hu

private theorem oriented_cost {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) (hi : (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width depth))
        (polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e)))) ≤
      displacementRate w K * oddMass w K width depth := by
  have h := link_displacement_bound hw0 hw1 K width hK depth _ hi
  unfold orientedLink link upperOriented
  rw [if_pos he]
  split
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (haar_of_coeff ((norm_difference_conj _ _).mul_left _))) h
  · exact h

/-- Squared path-length control of the ACTUAL ordered lower/upper word.
The explicit active-edge premise excludes uncoupled fringe links. -/
theorem word_increment_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width depth))
        (polyMul (difference (sourceWord width loop.edges) (wordWith (upperOriented width) loop.edges)).scalar
          (difference (sourceWord width loop.edges) (wordWith (upperOriented width) loop.edges)).scalar)) ≤
      (Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length) *
        (displacementRate w K * oddMass w K width depth) :=
  word_scalar_square_bound
    (edgeCertificate hw0 hw1 K width hK (terminalMessage_supported w K width depth)
      (terminalMessage_certificate hw0 hw1 K width hK depth))
    (orientedLink width) (upperOriented width) loop.edges
    (fun e he => lower_supported (loop.physical e he))
    (fun e he => upper_supported (loop.physical e he))
    (fun e he => lower_unit (loop.physical e he))
    (fun e he => upper_unit (loop.physical e he)) _
    (fun e he => oriented_cost hw0 hw1 K width hK depth (loop.physical e he) (hactive e he))

private theorem padded_neg {n : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv n p q) :
    PaddedPolynomialCoeffEqv n (polyNeg p) (polyNeg q) := by
  unfold PaddedPolynomialCoeffEqv
  rw [reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_neg]
  exact RatPolyCoeffEqv.neg h

/-- The opposite word is the literal coordinate lift of the SAME original
Wilson character, with the necessary common-carrier padding retained. -/
theorem upper_character_lift (width : Nat) (loop : SourceLoop width) :
    PaddedPolynomialCoeffEqv (N width+N width)
      (liftBoundary (N width) (sourceCharacter width loop.edges 1))
      (characterPolynomial (wordWith (upperOriented width) loop.edges).scalar 1) := by
  have hword := wordWith_lift (N width+N width) (N width)
    (orientedLink width) (upperOriented width) loop.edges
    (by
      intro e he
      unfold orientedLink link upperOriented
      rw [if_pos (loop.physical e he)]
      split
      · rw [liftQuaternion_conj, liftQuaternion_coordinateVariable]
        exact .refl _ _
      · rw [liftQuaternion_coordinateVariable]
        exact .refl _ _)
  exact (lift_character (N width+N width) (N width) (sourceWord width loop.edges).scalar 1).trans
    (PaddedPolynomialCoeffEqv.character hword.scalar 1)

private theorem jump_pin (width : Nat) (loop : SourceLoop width) :
    PaddedPolynomialCoeffEqv (N width+N width) (jump width (sourceCharacter width loop.edges 1))
      (polySmul 2 (difference (sourceWord width loop.edges) (wordWith (upperOriented width) loop.edges)).scalar) :=
  ((PaddedPolynomialCoeffEqv.refl _ _).add (padded_neg (upper_character_lift width loop))).trans
    (.of_coeff (by
      let p := (sourceWord width loop.edges).scalar
      let q := (wordWith (upperOriented width) loop.edges).scalar
      have h : RatPolyCoeffEqv (polyAdd (polyMul (cap 2) p) (polyNeg (polyMul (cap 2) q)))
          (polyMul (cap 2) (polyAdd p (polyNeg q))) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
          (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide)
          (fun | 0 => cap 2 | 1 => p | _ => q)
      exact ((QuaternionHaarPolynomialSquareBound.cap_mul_left 2 p).add
        (RatPolyCoeffEqv.neg (QuaternionHaarPolynomialSquareBound.cap_mul_left 2 q))).symm.trans
        (h.trans (QuaternionHaarPolynomialSquareBound.cap_mul_left 2 _))))

private theorem double_square (p : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul 2 p) (polySmul 2 p)) (polySmul 4 (polyMul p p)) :=
  (RatPolyCoeffEqv.polyMul_smul_left 2 p (polySmul 2 p)).trans
    (((RatPolyCoeffEqv.polyMul_smul_right 2 p p).smul 2).trans
      ((RatPolyCoeffEqv.smul_assoc 2 2 _).trans
        (RatPolyCoeffEqv.smul_coefficient (by decide) _)))

/-- Cleared energy bound for the SAME original transfer and fundamental
Wilson character. The factor 4 is the unnormalized trace's square. -/
theorem wilson_energy_cleared {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    (2 : Q') * energy w K width (terminalMessage w K width depth) (sourceCharacter width loop.edges 1) ≤
      ((4 : Q') * (Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length) * displacementRate w K) *
        oddMass w K width depth := by
  let W := edgeDensity w K width (terminalMessage w K width depth)
  let d := (difference (sourceWord width loop.edges) (wordWith (upperOriented width) loop.edges)).scalar
  have hw := edgeDensity_supported w K width (terminalMessage_supported w K width depth)
  have hj := jump_supported width (sourceCharacter_supported width loop.edges 1)
  have hd : SupportedQuaternionBlocks (N width+N width) d :=
    (difference_supported
      (word_supported (orientedLink width) loop.edges (fun e he => lower_supported (loop.physical e he)))
      (word_supported (upperOriented width) loop.edges (fun e he => upper_supported (loop.physical e he)))).scalar
  have hds := supported_smul hd (2 : Q')
  have hpin := ((jump_pin width loop).mul (jump_pin width loop)).haar_insert
    (supported_polyMul hj hj) (supported_polyMul hds hds) W hw
  have he := Q'.eqv_trans _ _ _
    (energy_identity w K width (terminalMessage_supported w K width depth)
      (sourceCharacter_supported width loop.edges 1))
    (Q'.eqv_trans _ _ _ hpin (Q'.eqv_trans _ _ _
      (haar_of_coeff ((double_square d).mul_left W)) (weighted_scale _ W _ 4)))
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (4 : Q')
    (word_increment_bound hw0 hw1 K width hK depth loop hactive) (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.const 4) (.mul (.var 0) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.mul (.const 4) (.var 0)) (.var 1)) (.var 2)) (by decide)
        (fun | 0 => Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length
             | 1 => displacementRate w K | _ => oddMass w K width depth))))

/-- Divide only by the existing positive odd-window partition. Width and
terminal depth do not enter the explicit path-length/nome/cutoff bound. -/
theorem wilson_energy_normalized {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    (2 : Q') * normalizedEnergy hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1) ≤
      (4 : Q') * (Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length) * displacementRate w K := by
  have hz := oddMass_positive hw0 hw1 K width hK depth
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos _ hz)
    (wilson_energy_cleared hw0 hw1 K width hK depth loop hactive) (Q'.le_of_lt (Q'.recipPos_pos _ hz))
  have hc : ∀ c : Q', (c*oddMass w K width depth)*Q'.recipPos _ hz ≈ c := fun c =>
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ hz)) (Q'.mul_one_eqv c))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (hc _)))

/-- The existing computed cutoff removes the explicit error uniformly in
width and terminal depth; the squared loop length remains in the statement. -/
theorem wilson_energy_tolerance {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (K width : Nat)
    (hK : headCutoff w ≤ K) (herror : cutoffErrorCutoff w epsilon ≤ K)
    (depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    (2 : Q') * normalizedEnergy hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1) ≤
      (4 : Q') * (Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length) *
        ((2 + -(coeffW w 1)) + epsilon) :=
  Q'.le_trans' _ _ _ (wilson_energy_normalized hw0 hw1 K width hK depth loop hactive)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.add_le_add_left _ _ _ (cutoffError_small hw0 hw1 epsilon he K herror))
      (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) (Q'.ofNat_nonneg _))))

/-- A fixed literal source word has this energy bound at EVERY strictly
larger width, with no unfilled active-link premise. Each energy uses its
own original ambient action; this does not identify states across widths. -/
theorem padded_wilson_energy_tolerance {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K)
    (herror : cutoffErrorCutoff w epsilon ≤ K) (depth : Nat) (loop : SourceLoop base) :
    (2 : Q') * normalizedEnergy hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1) ≤
      (4 : Q') * (Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length) *
        ((2 + -(coeffW w 1)) + epsilon) := by
  have h := wilson_energy_tolerance hw0 hw1 epsilon he K width hK herror depth
    (recenterLoop (space := 0) (by omega : base+0 ≤ width) loop)
    (includedLoop_edges_active hwidth loop)
  rw [includeLoop_edges (Nat.le_of_lt hwidth) loop] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement.displacementRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement.link_displacement_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement.upperOriented
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement.word_increment_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement.upper_character_lift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement.wilson_energy_cleared
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement.wilson_energy_normalized
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement.wilson_energy_tolerance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement.padded_wilson_energy_tolerance
