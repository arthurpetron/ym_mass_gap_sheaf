/-
# A numerical original-cube Haar contraction, without a character-basis claim

The two original faces p01 and p02 at the origin share a forward link.
Integrating that link fuses their fundamental traces into half the literal
bent six-link trace. All independent insertions are retained. Exposing a
different bent link gives its Haar square norm one, and hence the exact
original three-trace moment one half. No interacting variance, computed
32-state matrix, gain sign, cutoff guard or continuum estimate is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.SU2QuaternionIndependentTailMoments
import YMGap.Continuum.QuaternionHaarWordDifference

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 200000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (plaquette_fourWord)
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (conjugate_product)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt)
open YMGap.Continuum.SU2QuaternionIndependentTailMoments
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra (degree_zero_independent)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation "N" => List.length (baseLinks 2)
local notation "half" => HalfPow.half
local infix:50 " ≈ " => Q'.eqv
local infixr:70 " ⋄ " => PolyQuaternion.mul
local prefix:80 "bar " => PolyQuaternion.conj

private def coordinateAt (l : Z4Link) : PolyQuaternion :=
  PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf l)

private def shared : Z4Link := ((0,0,0,0),.x0)
private def first : Z4Link := ((0,0,0,0),.x1)
private def aTail : PolyQuaternion :=
  coordinateAt ((1,0,0,0),.x1) ⋄ bar (coordinateAt ((0,1,0,0),.x0)) ⋄ bar (coordinateAt first)
private def bTail : PolyQuaternion :=
  coordinateAt ((1,0,0,0),.x2) ⋄ bar (coordinateAt ((0,0,1,0),.x0)) ⋄ bar (coordinateAt ((0,0,0,0),.x2))
private def fTail : PolyQuaternion :=
  coordinateAt ((0,1,0,0),.x0) ⋄ bar (coordinateAt ((1,0,0,0),.x1)) ⋄ bTail

/-- The original first and third cube faces, not substitute independent traces. -/
def firstFaceTrace : RatPoly := characterPolynomial (plaquette 2 ((0,0,0,0),.p01)).scalar 1
def thirdFaceTrace : RatPoly := characterPolynomial (plaquette 2 ((0,0,0,0),.p02)).scalar 1

attribute [local irreducible] baseLinks coordinateAt aTail bTail fTail
  bentObservable firstFaceTrace thirdFaceTrace

private theorem four_reassociate (a b c d : PolyQuaternion) :
    PolyQuaternionCoeffEqv (((a ⋄ b) ⋄ c) ⋄ d) (a ⋄ b ⋄ c ⋄ d) :=
  (PolyQuaternionCoeffEqv.mul_assoc (a ⋄ b) c d).trans (PolyQuaternionCoeffEqv.mul_assoc a b (c ⋄ d))

private theorem firstFace_pin : RatPolyCoeffEqv firstFaceTrace
    (characterPolynomial (coordinateAt shared ⋄ aTail).scalar 1) := by
  unfold firstFaceTrace aTail coordinateAt
  have h := plaquette_fourWord (width := 2) (face := ((0,0,0,0),.p01))
    ((BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_mem_iff 2 _).mpr (by decide))
  have ha := four_reassociate
    (PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf shared))
    (PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf ((1,0,0,0),.x1)))
    (bar (PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf ((0,1,0,0),.x0))))
    (bar (PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf first)))
  exact characterPolynomial_coeffEqv (h.trans ha).scalar 1

private theorem thirdFace_pin : RatPolyCoeffEqv thirdFaceTrace
    (characterPolynomial (coordinateAt shared ⋄ bTail).scalar 1) := by
  unfold thirdFaceTrace bTail coordinateAt
  have h := plaquette_fourWord (width := 2) (face := ((0,0,0,0),.p02))
    ((BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_mem_iff 2 _).mpr (by decide))
  have ha := four_reassociate
    (PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf shared))
    (PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf ((1,0,0,0),.x2)))
    (bar (PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf ((0,0,1,0),.x0))))
    (bar (PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf ((0,0,0,0),.x2))))
  exact characterPolynomial_coeffEqv (h.trans ha).scalar 1

private theorem six_word_pin (value : OrientedBF4Link → PolyQuaternion)
    (e0 e1 e2 e3 e4 e5 : OrientedBF4Link) :
    PolyQuaternionCoeffEqv (wordWith value [e0,e1,e2,e3,e4,e5])
      (value e0 ⋄ value e1 ⋄ value e2 ⋄ value e3 ⋄ value e4 ⋄ value e5) :=
  (PolyQuaternionCoeffEqv.refl (value e0)).mul
    ((PolyQuaternionCoeffEqv.refl (value e1)).mul
      ((PolyQuaternionCoeffEqv.refl (value e2)).mul
        ((PolyQuaternionCoeffEqv.refl (value e3)).mul
          ((PolyQuaternionCoeffEqv.refl (value e4)).mul (PolyQuaternionCoeffEqv.mul_one (value e5))))))

private theorem bent_pin : RatPolyCoeffEqv bentObservable
    (characterPolynomial (coordinateAt first ⋄ fTail).scalar 1) := by
  unfold bentObservable fTail bTail coordinateAt
  have h := six_word_pin (fun e => orientedCoordinateQuaternion ((baseLinks 2).idxOf e.link) e.reverse)
    ⟨((0,0,0,0),.x1),false⟩ ⟨((0,1,0,0),.x0),false⟩
    ⟨((1,0,0,0),.x1),true⟩ ⟨((1,0,0,0),.x2),false⟩
    ⟨((0,0,1,0),.x0),true⟩ ⟨((0,0,0,0),.x2),true⟩
  exact characterPolynomial_coeffEqv h.scalar 1

#print axioms firstFace_pin
#print axioms thirdFace_pin
#print axioms bent_pin

private theorem double_conj (q : PolyQuaternion) : PolyQuaternionCoeffEqv (bar (bar q)) q := by
  have hn (p : RatPoly) : RatPolyCoeffEqv (polyNeg (polyNeg p)) p :=
    coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0) (by decide) (fun _ => p)
  exact ⟨RatPolyCoeffEqv.refl _, hn _, hn _, hn _⟩

private theorem conj_three (p q r : PolyQuaternion) :
    PolyQuaternionCoeffEqv (bar (p ⋄ bar q ⋄ bar r)) (r ⋄ q ⋄ bar p) :=
  (conjugate_product p (bar q ⋄ bar r)).trans
    ((((conjugate_product (bar q) (bar r)).trans ((double_conj r).mul (double_conj q))).mul
      (PolyQuaternionCoeffEqv.refl _)).trans (PolyQuaternionCoeffEqv.mul_assoc _ _ _))

private theorem tails_join : PolyQuaternionCoeffEqv (bar aTail ⋄ bTail) (coordinateAt first ⋄ fTail) := by
  unfold aTail fTail
  exact (((conj_three (coordinateAt ((1,0,0,0),.x1)) (coordinateAt ((0,1,0,0),.x0))
      (coordinateAt first)).mul (PolyQuaternionCoeffEqv.refl bTail)).trans
    (PolyQuaternionCoeffEqv.mul_assoc (coordinateAt first)
      (coordinateAt ((0,1,0,0),.x0) ⋄ bar (coordinateAt ((1,0,0,0),.x1))) bTail)).trans
      ((PolyQuaternionCoeffEqv.refl (coordinateAt first)).mul
        (PolyQuaternionCoeffEqv.mul_assoc (coordinateAt ((0,1,0,0),.x0))
          (bar (coordinateAt ((1,0,0,0),.x1))) bTail))

#print axioms tails_join

private theorem at_independent (selected l : Z4Link)
    (h : (baseLinks 2).idxOf selected ≠ (baseLinks 2).idxOf l) :
    HasPolyQuaternionBlockDegree ((baseLinks 2).idxOf selected) 0 (coordinateAt l) := by
  unfold coordinateAt
  have hc := hasPolyQuaternionBlockDegree_coordinateVariable
    ((baseLinks 2).idxOf l) ((baseLinks 2).idxOf selected)
  rw [if_neg h] at hc
  exact hc

private theorem index_ne (selected l : Z4Link) (hs : selected ∈ cubeLinks) (hl : l ∈ cubeLinks)
    (hne : selected ≠ l) : (baseLinks 2).idxOf selected ≠ (baseLinks 2).idxOf l :=
  fun he => hne (BF4ExactSlabTemporalGaugeLedger.idxOf_injective_on_members
    (cubeLinks_in_carrier selected hs) (cubeLinks_in_carrier l hl) he)

private theorem aTail_independent : HasPolyQuaternionBlockDegree ((baseLinks 2).idxOf shared) 0 aTail := by
  unfold aTail
  exact (at_independent shared ((1,0,0,0),.x1)
    (index_ne _ _ (by decide) (by decide) (by decide))).mul
    (((at_independent shared ((0,1,0,0),.x0)
      (index_ne _ _ (by decide) (by decide) (by decide))).conj).mul
      ((at_independent shared first (index_ne _ _ (by decide) (by decide) (by decide))).conj))

private theorem bTail_independent (selected : Z4Link) (hs : selected ∈ cubeLinks)
    (h0 : selected ≠ ((1,0,0,0),.x2))
    (h1 : selected ≠ ((0,0,1,0),.x0))
    (h2 : selected ≠ ((0,0,0,0),.x2)) :
    HasPolyQuaternionBlockDegree ((baseLinks 2).idxOf selected) 0 bTail := by
  unfold bTail
  exact (at_independent selected ((1,0,0,0),.x2) (index_ne _ _ hs (by decide) h0)).mul
    (((at_independent selected ((0,0,1,0),.x0) (index_ne _ _ hs (by decide) h1)).conj).mul
      ((at_independent selected ((0,0,0,0),.x2) (index_ne _ _ hs (by decide) h2)).conj))

private theorem fTail_independent : HasPolyQuaternionBlockDegree ((baseLinks 2).idxOf first) 0 fTail := by
  unfold fTail
  exact (at_independent first ((0,1,0,0),.x0)
    (index_ne _ _ (by decide) (by decide) (by decide))).mul
    (((at_independent first ((1,0,0,0),.x1)
      (index_ne _ _ (by decide) (by decide) (by decide))).conj).mul
      (bTail_independent first (by decide) (by decide) (by decide) (by decide)))

private theorem bent_shared_independent : QuaternionBlockIndependent ((baseLinks 2).idxOf shared) bentObservable := by
  have hmem : ∀ e, e ∈ bentEdges → e.link ∈ cubeLinks := by
    intro e he
    simp only [bentEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have hne : ∀ e, e ∈ bentEdges → shared ≠ e.link := by
    intro e he
    simp only [bentEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  unfold bentObservable
  exact degree_zero_independent
    (SU2QuaternionRelativeHeatPairGeometry.character_independent
      (SU2QuaternionProductHeatWilsonWord.word_independent ((baseLinks 2).idxOf shared)
      (fun e => (baseLinks 2).idxOf e.link) bentEdges
      (fun e he => index_ne shared e.link (by decide) (hmem e he) (hne e he))).scalar 1)

private theorem at_unit (l : Z4Link) (hl : l ∈ cubeLinks) :
    HaarCarrierEqv N (polyQuaternionNorm (coordinateAt l)) polyOne := by
  unfold coordinateAt
  exact haarNorm_coordinate (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier l hl))

private theorem conj_unit {p : PolyQuaternion}
    (h : HaarCarrierEqv N (polyQuaternionNorm p) polyOne) :
    HaarCarrierEqv N (polyQuaternionNorm (bar p)) polyOne :=
  HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj p)) h

private theorem fTail_unit : HaarCarrierEqv N (polyQuaternionNorm fTail) polyOne := by
  unfold fTail bTail
  exact haarNorm_mul (at_unit ((0,1,0,0),.x0) (by decide +kernel))
    (haarNorm_mul (conj_unit (at_unit ((1,0,0,0),.x1) (by decide +kernel)))
      (haarNorm_mul (at_unit ((1,0,0,0),.x2) (by decide +kernel))
        (haarNorm_mul (conj_unit (at_unit ((0,0,1,0),.x0) (by decide +kernel)))
          (conj_unit (at_unit ((0,0,0,0),.x2) (by decide +kernel))))))

#print axioms fTail_independent
#print axioms bent_shared_independent
#print axioms fTail_unit

/-- Exact square norm of the ORIGINAL bent observable on its retained slice carrier. -/
theorem bent_square_haar : quaternionHaar N (polyMul bentObservable bentObservable) ≈ 1 := by
  have hpfirst : coordinateAt first = PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf first) := by
    unfold coordinateAt
    rfl
  have hf := fundamental_second_moment N ((baseLinks 2).idxOf first)
    (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier first (by decide +kernel))) fTail polyOne
    fTail_independent (quaternionBlockIndependent_polyOne _) fTail_unit
  have hp : RatPolyCoeffEqv (polyMul bentObservable bentObservable)
      (polyMul (polyMul (characterPolynomial (coordinateAt first ⋄ fTail).scalar 1)
        (characterPolynomial (coordinateAt first ⋄ fTail).scalar 1)) polyOne) :=
    (bent_pin.mul bent_pin).trans (RatPolyCoeffEqv.mul_one _).symm
  rw [← hpfirst] at hf
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ hf (QPolyHaarPositiveSubstitution.haar_one N))

private theorem half_fundamental (s : RatPoly) :
    RatPolyCoeffEqv (polySmul half (characterPolynomial s 1)) s :=
  (RatPolyCoeffEqv.smul_assoc half 2 s).trans
    ((RatPolyCoeffEqv.smul_coefficient (by decide : half * (2 : Q') ≈ 1) s).trans
      (RatPolyCoeffEqv.one_smul s))

/-- The two original adjacent face traces fuse to half F under every insertion
independent of their shared physical link. The insertion may contain all six bent links. -/
theorem adjacent_faces_bent_fusion (r : RatPoly)
    (hr : QuaternionBlockIndependent ((baseLinks 2).idxOf shared) r) :
    quaternionHaar N (polyMul (polyMul firstFaceTrace thirdFaceTrace) r) ≈
      half * quaternionHaar N (polyMul bentObservable r) := by
  have hpshared : coordinateAt shared = PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf shared) := by
    unfold coordinateAt
    rfl
  have hf := fundamental_pair_moment N ((baseLinks 2).idxOf shared)
    (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier shared (by decide +kernel))) aTail bTail r
    aTail_independent (bTail_independent shared (by decide) (by decide) (by decide) (by decide)) hr
  rw [← hpshared] at hf
  have hs : RatPolyCoeffEqv (bar aTail ⋄ bTail).scalar (polySmul half bentObservable) :=
    tails_join.scalar.trans ((half_fundamental _).symm.trans (bent_pin.smul half).symm)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((firstFace_pin.mul thirdFace_pin).mul_right r))
    (Q'.eqv_trans _ _ _ hf
      (Q'.eqv_trans _ _ _ (haar_of_coeff (hs.mul_right r))
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left half bentObservable r))
          (quaternionHaar_polySmul N half _))))

/-- Actual original cube moment supplying the leading lower-perimeter fusion coefficient. -/
theorem original_bent_two_face_moment :
    quaternionHaar N (polyMul (polyMul firstFaceTrace thirdFaceTrace) bentObservable) ≈ half :=
  Q'.eqv_trans _ _ _ (adjacent_faces_bent_fusion bentObservable bent_shared_independent)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left half _ _ bent_square_haar) (Q'.mul_one_eqv half))

/-- The literal bent loop has zero bare Haar mean on its original carrier.
This is not a statement about its interacting OWN odd mean. -/
theorem bent_haar_zero : quaternionHaar N bentObservable ≈ 0 := by
  have hpfirst : coordinateAt first = PolyQuaternion.coordinateVariable ((baseLinks 2).idxOf first) := by
    unfold coordinateAt
    rfl
  have hf := fundamental_first_moment N ((baseLinks 2).idxOf first)
    (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier first (by decide))) fTail polyOne
    fTail_independent (quaternionBlockIndependent_polyOne _)
  rw [← hpfirst] at hf
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one bentObservable).symm)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (bent_pin.mul_right polyOne)) hf)

#print axioms bent_square_haar
#print axioms adjacent_faces_bent_fusion
#print axioms original_bent_two_face_moment
#print axioms bent_haar_zero

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion
