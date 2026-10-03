/-
# The surviving five-face original-cube bent moment

All words use the actual slice coordinates. Three shared-link integrations
retain their complete spectators; two adjacent backtracks are removed only
in the arbitrary-insertion Haar ideal. No interacting gain, cutoff guard,
completed estimate or continuum claim is made by this finite contraction.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
import YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentComplement

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
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity
  (selectedBentInsertion selectedFaceProduct singletonSelection complementSelection)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (plaquette_fourWord)
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (conjugate_product)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt word_independent)
open YMGap.Continuum.SU2QuaternionIndependentTailMoments
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra (degree_zero_independent)
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation (haarUnit_mul_conj character_haar_congr)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation "N" => List.length (baseLinks 2)
local notation "half" => HalfPow.half
local infix:50 " ≈ " => Q'.eqv
local infixr:70 " ⋄ " => PolyQuaternion.mul
local prefix:80 "bar " => PolyQuaternion.conj

private def fwd (l : Z4Link) : OrientedBF4Link := ⟨l,false⟩
private def rev (l : Z4Link) : OrientedBF4Link := ⟨l,true⟩
private def inverse (e : OrientedBF4Link) : OrientedBF4Link := ⟨e.link,!e.reverse⟩
private def inverseWord (es : List OrientedBF4Link) := es.reverse.map inverse
private def value (e : OrientedBF4Link) :=
  orientedCoordinateQuaternion ((baseLinks 2).idxOf e.link) e.reverse
private def W (es : List OrientedBF4Link) := wordWith value es
private def trace (es : List OrientedBF4Link) := characterPolynomial (W es).scalar 1
private def faceTrace (face : Z4Plaq) := characterPolynomial (plaquette 2 face).scalar 1
private def faceWord (face : Z4Plaq) : List OrientedBF4Link :=
  [fwd (face.1,(dirsOf face.2).1), fwd (addE face.1 (dirsOf face.2).1,(dirsOf face.2).2),
   rev (addE face.1 (dirsOf face.2).2,(dirsOf face.2).1), rev (face.1,(dirsOf face.2).2)]

attribute [local irreducible] baseLinks value W trace faceTrace bentObservable

private theorem W_cons (e : OrientedBF4Link) (es : List OrientedBF4Link) :
    W (e::es) = value e ⋄ W es := by unfold W; rfl

private theorem W_append (xs ys : List OrientedBF4Link) :
    PolyQuaternionCoeffEqv (W (xs++ys)) (W xs ⋄ W ys) := by
  induction xs with
  | nil =>
      simp only [List.nil_append]
      rw [show W [] = PolyQuaternion.one by unfold W; rfl]
      exact (PolyQuaternionCoeffEqv.one_mul (W ys)).symm
  | cons e es ih =>
      rw [List.cons_append, W_cons, W_cons]
      exact ((PolyQuaternionCoeffEqv.refl (value e)).mul ih).trans
        (PolyQuaternionCoeffEqv.mul_assoc (value e) (W es) (W ys)).symm

private theorem W_single (e : OrientedBF4Link) :
    PolyQuaternionCoeffEqv (W [e]) (value e) := by
  unfold W
  exact PolyQuaternionCoeffEqv.mul_one (value e)

private theorem double_conj (q : PolyQuaternion) : PolyQuaternionCoeffEqv (bar (bar q)) q := by
  have hn (p : RatPoly) : RatPolyCoeffEqv (polyNeg (polyNeg p)) p :=
    coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0) (by decide) (fun _ => p)
  exact ⟨RatPolyCoeffEqv.refl _,hn _,hn _,hn _⟩

private theorem value_inverse (e : OrientedBF4Link) :
    PolyQuaternionCoeffEqv (bar (value e)) (value (inverse e)) := by
  rcases e with ⟨l,b⟩
  unfold value inverse
  cases b
  · exact PolyQuaternionCoeffEqv.refl _
  · exact double_conj _

private theorem W_inverse (es : List OrientedBF4Link) :
    PolyQuaternionCoeffEqv (bar (W es)) (W (inverseWord es)) := by
  induction es with
  | nil => unfold W inverseWord; exact PolyQuaternionCoeffEqv.refl _
  | cons e es ih =>
      rw [W_cons]
      have h := (conjugate_product (value e) (W es)).trans (ih.mul (value_inverse e))
      have hs := (W_append (inverseWord es) [inverse e]).trans
        ((PolyQuaternionCoeffEqv.refl (W (inverseWord es))).mul (W_single (inverse e)))
      exact h.trans (by simpa only [inverseWord, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil] using hs.symm)

private theorem trace_inverse (es : List OrientedBF4Link) :
    RatPolyCoeffEqv (trace es) (trace (inverseWord es)) := by
  unfold trace
  exact characterPolynomial_coeffEqv (W_inverse es).scalar 1

private theorem trace_rotate (xs ys : List OrientedBF4Link) :
    RatPolyCoeffEqv (trace (xs++ys)) (trace (ys++xs)) := by
  unfold trace
  exact characterPolynomial_coeffEqv ((W_append xs ys).scalar.trans
    ((polyQuaternion_mul_scalar_cyclic (W xs) (W ys)).trans (W_append ys xs).scalar.symm)) 1

private theorem W_four (a b c d : OrientedBF4Link) :
    PolyQuaternionCoeffEqv (W [a,b,c,d]) (((value a ⋄ value b) ⋄ value c) ⋄ value d) := by
  rw [W_cons, W_cons, W_cons]
  have h := (PolyQuaternionCoeffEqv.refl (value a)).mul
    ((PolyQuaternionCoeffEqv.refl (value b)).mul
      ((PolyQuaternionCoeffEqv.refl (value c)).mul (W_single d)))
  exact h.trans ((PolyQuaternionCoeffEqv.mul_assoc (value a ⋄ value b) (value c) (value d)).trans
    (PolyQuaternionCoeffEqv.mul_assoc (value a) (value b) (value c ⋄ value d))).symm

private theorem face_pin (face : Z4Plaq)
    (hf : face ∈ BF4ExactSlabFixedSpatialFacePlacement.spatialFaces 2) :
    RatPolyCoeffEqv (faceTrace face) (trace (faceWord face)) := by
  have h := plaquette_fourWord hf
  have hw := W_four (fwd (face.1,(dirsOf face.2).1))
    (fwd (addE face.1 (dirsOf face.2).1,(dirsOf face.2).2))
    (rev (addE face.1 (dirsOf face.2).2,(dirsOf face.2).1))
    (rev (face.1,(dirsOf face.2).2))
  unfold value fwd rev at hw
  unfold faceTrace trace faceWord
  exact characterPolynomial_coeffEqv (h.trans hw.symm).scalar 1

private theorem bent_pin : RatPolyCoeffEqv bentObservable (trace bentEdges) := by
  unfold bentObservable trace W value
  exact RatPolyCoeffEqv.refl _

private theorem index_ne (selected l : Z4Link) (hs : selected ∈ cubeLinks) (hl : l ∈ cubeLinks)
    (hne : selected ≠ l) : (baseLinks 2).idxOf selected ≠ (baseLinks 2).idxOf l :=
  fun he => hne (BF4ExactSlabTemporalGaugeLedger.idxOf_injective_on_members
    (cubeLinks_in_carrier selected hs) (cubeLinks_in_carrier l hl) he)

private theorem W_independent (s : Z4Link) (es : List OrientedBF4Link)
    (hs : s ∈ cubeLinks) (hm : ∀ e, e ∈ es → e.link ∈ cubeLinks)
    (hn : ∀ e, e ∈ es → s ≠ e.link) :
    HasPolyQuaternionBlockDegree ((baseLinks 2).idxOf s) 0 (W es) := by
  unfold W value
  exact word_independent _ (fun e => (baseLinks 2).idxOf e.link) es
    (fun e he => index_ne s e.link hs (hm e he) (hn e he))

private theorem trace_independent (s : Z4Link) (es : List OrientedBF4Link)
    (hs : s ∈ cubeLinks) (hm : ∀ e, e ∈ es → e.link ∈ cubeLinks)
    (hn : ∀ e, e ∈ es → s ≠ e.link) :
    QuaternionBlockIndependent ((baseLinks 2).idxOf s) (trace es) := by
  unfold trace
  exact degree_zero_independent (SU2QuaternionRelativeHeatPairGeometry.character_independent
    (W_independent s es hs hm hn).scalar 1)

private theorem half_fundamental (s : RatPoly) :
    RatPolyCoeffEqv (polySmul half (characterPolynomial s 1)) s :=
  (RatPolyCoeffEqv.smul_assoc half 2 s).trans
    ((RatPolyCoeffEqv.smul_coefficient (by decide : half * (2 : Q') ≈ 1) s).trans
      (RatPolyCoeffEqv.one_smul s))

private theorem fusion (s : Z4Link) (p q : List OrientedBF4Link) (r : RatPoly)
    (hs : s ∈ cubeLinks)
    (hp : HasPolyQuaternionBlockDegree ((baseLinks 2).idxOf s) 0 (W p))
    (hq : HasPolyQuaternionBlockDegree ((baseLinks 2).idxOf s) 0 (W q))
    (hr : QuaternionBlockIndependent ((baseLinks 2).idxOf s) r) :
    quaternionHaar N (polyMul (polyMul (trace (fwd s::p)) (trace (fwd s::q))) r) ≈
      half * quaternionHaar N (polyMul (trace (inverseWord p++q)) r) := by
  have h := fundamental_pair_moment N ((baseLinks 2).idxOf s)
    (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier s hs)) (W p) (W q) r hp hq hr
  have hj : PolyQuaternionCoeffEqv (bar (W p) ⋄ W q) (W (inverseWord p++q)) :=
    ((W_inverse p).mul (PolyQuaternionCoeffEqv.refl (W q))).trans (W_append _ _).symm
  have hc : RatPolyCoeffEqv (bar (W p) ⋄ W q).scalar (polySmul half (trace (inverseWord p++q))) :=
    by unfold trace; exact hj.scalar.trans (half_fundamental _).symm
  have hin : quaternionHaar N (polyMul (polyMul (trace (fwd s::p)) (trace (fwd s::q))) r) ≈
      quaternionHaar N (polyMul (bar (W p) ⋄ W q).scalar r) := by
    unfold trace
    rw [W_cons, W_cons]
    unfold value fwd
    exact h
  exact Q'.eqv_trans _ _ _ hin (Q'.eqv_trans _ _ _ (haar_of_coeff (hc.mul_right r))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left half _ r))
      (quaternionHaar_polySmul N half _)))

private theorem W_cancel (pre suffix : List OrientedBF4Link) (l : Z4Link)
    (hl : l ∈ cubeLinks) :
    PolyQuaternionHaarCarrierEqv N (W (pre++fwd l::rev l::suffix)) (W (pre++suffix)) := by
  induction pre with
  | nil =>
      simp only [List.nil_append, W_cons]
      have hu : PolyQuaternionHaarCarrierEqv N (value (fwd l) ⋄ value (rev l)) PolyQuaternion.one := by
        unfold value fwd rev
        exact haarUnit_mul_conj
          (haarNorm_coordinate (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier l hl)))
      exact (PolyQuaternionHaarCarrierEqv.of_coeff
        (PolyQuaternionCoeffEqv.mul_assoc (value (fwd l)) (value (rev l)) (W suffix)).symm).trans
          ((hu.mul (PolyQuaternionHaarCarrierEqv.refl N (W suffix))).trans
            (PolyQuaternionHaarCarrierEqv.of_coeff (PolyQuaternionCoeffEqv.one_mul (W suffix))))
  | cons e es ih =>
      simp only [List.cons_append, W_cons]
      exact (PolyQuaternionHaarCarrierEqv.refl N (value e)).mul ih

private theorem checked_W_independent (s : Z4Link) (es : List OrientedBF4Link)
    (hs : s ∈ cubeLinks)
    (hc : es.all (fun e => decide (e.link ∈ cubeLinks ∧ s ≠ e.link)) = true) :
    HasPolyQuaternionBlockDegree ((baseLinks 2).idxOf s) 0 (W es) := by
  have h := fun e he => of_decide_eq_true (List.all_eq_true.mp hc e he)
  exact W_independent s es hs (fun e he => (h e he).1) (fun e he => (h e he).2)

private theorem checked_trace_independent (s : Z4Link) (es : List OrientedBF4Link)
    (hs : s ∈ cubeLinks)
    (hc : es.all (fun e => decide (e.link ∈ cubeLinks ∧ s ≠ e.link)) = true) :
    QuaternionBlockIndependent ((baseLinks 2).idxOf s) (trace es) := by
  have h := fun e he => of_decide_eq_true (List.all_eq_true.mp hc e he)
  exact trace_independent s es hs (fun e he => (h e he).1) (fun e he => (h e he).2)

local notation "e02" => fwd ((0,0,0,0),Dir4.x1)
local notation "e04" => fwd ((0,0,0,0),Dir4.x2)
local notation "e13" => fwd ((1,0,0,0),Dir4.x1)
local notation "e15" => fwd ((1,0,0,0),Dir4.x2)
local notation "e23" => fwd ((0,1,0,0),Dir4.x0)
local notation "e26" => fwd ((0,1,0,0),Dir4.x2)
local notation "e37" => fwd ((1,1,0,0),Dir4.x2)
local notation "e45" => fwd ((0,0,1,0),Dir4.x0)
local notation "e46" => fwd ((0,0,1,0),Dir4.x1)
local notation "e57" => fwd ((1,0,1,0),Dir4.x1)
local notation "e67" => fwd ((0,1,1,0),Dir4.x0)
local notation "b02" => rev ((0,0,0,0),Dir4.x1)
local notation "b04" => rev ((0,0,0,0),Dir4.x2)
local notation "b13" => rev ((1,0,0,0),Dir4.x1)
local notation "b15" => rev ((1,0,0,0),Dir4.x2)
local notation "b23" => rev ((0,1,0,0),Dir4.x0)
local notation "b37" => rev ((1,1,0,0),Dir4.x2)
local notation "b45" => rev ((0,0,1,0),Dir4.x0)
local notation "b46" => rev ((0,0,1,0),Dir4.x1)
local notation "b57" => rev ((1,0,1,0),Dir4.x1)
local notation "f1" => ((0,0,1,0),Z4Plane.p01)
local notation "f3" => ((0,1,0,0),Z4Plane.p02)
local notation "f4" => ((0,0,0,0),Z4Plane.p12)
local notation "f5" => ((1,0,0,0),Z4Plane.p12)

private def p1 : List OrientedBF4Link := [b57,b45,e46]
private def q1 : List OrientedBF4Link := [b37,b23,e26]
private def h1 : List OrientedBF4Link := [b46,e45,e57,b37,b23,e26]
private def p2 : List OrientedBF4Link := [b46,e45,e57,b37,b23]
private def q2 : List OrientedBF4Link := [b46,b04,e02]
private def h2 : List OrientedBF4Link := [e23,e37,b57,b45,b04,e02]
private def p3 : List OrientedBF4Link := [b57,b45,b04,e02,e23]
private def q3 : List OrientedBF4Link := [b57,b15,e13]
private def h3 : List OrientedBF4Link := [b23,b02,e04,e45,b15,e13]

private theorem face1_exposed : RatPolyCoeffEqv (faceTrace f1) (trace (e67::p1)) :=
  (face_pin f1 ((BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_mem_iff 2 _).mpr (by decide))).trans
    ((trace_inverse (faceWord f1)).trans (trace_rotate [e46] [e67,b57,b45]))

private theorem face3_exposed : RatPolyCoeffEqv (faceTrace f3) (trace (e67::q1)) :=
  (face_pin f3 ((BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_mem_iff 2 _).mpr (by decide))).trans
    ((trace_inverse (faceWord f3)).trans (trace_rotate [e26] [e67,b37,b23]))

private theorem h1_exposed : RatPolyCoeffEqv (trace h1) (trace (e26::p2)) :=
  trace_rotate [b46,e45,e57,b37,b23] [e26]

private theorem face4_exposed : RatPolyCoeffEqv (faceTrace f4) (trace (e26::q2)) :=
  (face_pin f4 ((BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_mem_iff 2 _).mpr (by decide))).trans
    (trace_rotate [e02] [e26,b46,b04])

private theorem h2_exposed : RatPolyCoeffEqv (trace h2) (trace (e37::p3)) :=
  trace_rotate [e23] [e37,b57,b45,b04,e02]

private theorem face5_exposed : RatPolyCoeffEqv (faceTrace f5) (trace (e37::q3)) :=
  (face_pin f5 ((BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_mem_iff 2 _).mpr (by decide))).trans
    (trace_rotate [e13] [e37,b57,b15])

private theorem h3_bent : RatPolyCoeffEqv (trace h3) bentObservable :=
  (trace_rotate [b23,b02] [e04,e45,b15,e13]).trans
    ((trace_inverse bentEdges).symm.trans bent_pin.symm)

private theorem first_fusion (r : RatPoly)
    (hr : QuaternionBlockIndependent ((baseLinks 2).idxOf ((0,1,1,0),.x0)) r) :
    quaternionHaar N (polyMul (polyMul (faceTrace f1) (faceTrace f3)) r) ≈
      half * quaternionHaar N (polyMul (trace h1) r) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((face1_exposed.mul face3_exposed).mul_right r))
    (fusion ((0,1,1,0),.x0) p1 q1 r (by decide)
      (checked_W_independent _ _ (by decide) (by decide))
      (checked_W_independent _ _ (by decide) (by decide)) hr)

private theorem cancel_second : HaarCarrierEqv N (trace (inverseWord p2++q2)) (trace h2) := by
  unfold trace
  exact character_haar_congr
    (W_cancel [e23,e37,b57,b45] [b04,e02] ((0,0,1,0),.x1) (by decide)).scalar 1

private theorem cancel_third : HaarCarrierEqv N (trace (inverseWord p3++q3)) (trace h3) := by
  unfold trace
  exact character_haar_congr
    (W_cancel [b23,b02,e04,e45] [b15,e13] ((1,0,1,0),.x1) (by decide)).scalar 1

private theorem haar_right {p q : RatPoly} (h : HaarCarrierEqv N p q) (r : RatPoly) :
    quaternionHaar N (polyMul p r) ≈ quaternionHaar N (polyMul q r) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm p r))
    (Q'.eqv_trans _ _ _ (h r) (haar_of_coeff (RatPolyCoeffEqv.mul_comm r q)))

private theorem second_fusion (r : RatPoly)
    (hr : QuaternionBlockIndependent ((baseLinks 2).idxOf ((0,1,0,0),.x2)) r) :
    quaternionHaar N (polyMul (polyMul (trace h1) (faceTrace f4)) r) ≈
      half * quaternionHaar N (polyMul (trace h2) r) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((h1_exposed.mul face4_exposed).mul_right r))
    (Q'.eqv_trans _ _ _ (fusion ((0,1,0,0),.x2) p2 q2 r (by decide)
      (checked_W_independent _ _ (by decide) (by decide))
      (checked_W_independent _ _ (by decide) (by decide)) hr)
      (Q'.mul_eqv_congr_left half _ _ (haar_right cancel_second r)))

private theorem third_fusion (r : RatPoly)
    (hr : QuaternionBlockIndependent ((baseLinks 2).idxOf ((1,1,0,0),.x2)) r) :
    quaternionHaar N (polyMul (polyMul (trace h2) (faceTrace f5)) r) ≈
      half * quaternionHaar N (polyMul bentObservable r) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((h2_exposed.mul face5_exposed).mul_right r))
    (Q'.eqv_trans _ _ _ (fusion ((1,1,0,0),.x2) p3 q3 r (by decide)
      (checked_W_independent _ _ (by decide) (by decide))
      (checked_W_independent _ _ (by decide) (by decide)) hr)
      (Q'.mul_eqv_congr_left half _ _ (Q'.eqv_trans _ _ _ (haar_right cancel_third r)
        (haar_of_coeff (h3_bent.mul_right r)))))

private theorem checked_face_independent (s : Z4Link) (face : Z4Plaq) (hs : s ∈ cubeLinks)
    (hc : (edgesOf face).all (fun l => decide (l ∈ cubeLinks ∧ s ≠ l)) = true) :
    QuaternionBlockIndependent ((baseLinks 2).idxOf s) (faceTrace face) := by
  unfold faceTrace
  apply BF4ExactSlabFixedSpatialFaceIndependence.characterFace_independent_index 2 face _ 1
    (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier s hs))
  intro l hl _ he
  have h := of_decide_eq_true (List.all_eq_true.mp hc l hl)
  exact index_ne s l hs h.1 h.2 he.symm

private theorem checked_bent_independent (s : Z4Link) (hs : s ∈ cubeLinks)
    (hc : bentEdges.all (fun e => decide (e.link ∈ cubeLinks ∧ s ≠ e.link)) = true) :
    QuaternionBlockIndependent ((baseLinks 2).idxOf s) bentObservable := by
  have h := checked_trace_independent s bentEdges hs hc
  unfold trace W value at h
  unfold bentObservable
  exact h

private theorem gather5 (f a b c d : RatPoly) :
    RatPolyCoeffEqv (polyMul f (polyMul a (polyMul b (polyMul c d))))
      (polyMul (polyMul a b) (polyMul f (polyMul c d))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))
    (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.mul (.var 3) (.var 4))))
    (by decide) (fun | 0 => f | 1 => a | 2 => b | 3 => c | _ => d)

private theorem gather4 (a b c d : RatPoly) :
    RatPolyCoeffEqv (polyMul a (polyMul b (polyMul c d)))
      (polyMul (polyMul a c) (polyMul b d)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

private theorem gather3 (a b c : RatPoly) :
    RatPolyCoeffEqv (polyMul a (polyMul b c)) (polyMul (polyMul a c) b) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.mul (.var 0) (.var 2)) (.var 1))
    (by decide) (fun | 0 => a | 1 => b | _ => c)

/-- The four original cube faces excluding the adjacent origin faces. -/
def remainingFourFaceProduct : RatPoly :=
  polyMul (faceTrace f1) (polyMul (faceTrace f3) (polyMul (faceTrace f4) (faceTrace f5)))

/-- Numerical original-carrier contraction: three local integrations, not a
32-state character-basis calculation or a substituted independent measure. -/
theorem four_face_bent_moment :
    quaternionHaar N (polyMul bentObservable remainingFourFaceProduct) ≈ Q'.mkPos 1 8 (by decide) := by
  have h67 := quaternionBlockIndependent_polyMul
    (checked_bent_independent ((0,1,1,0),.x0) (by decide) (by decide))
    (quaternionBlockIndependent_polyMul
      (checked_face_independent ((0,1,1,0),.x0) f4 (by decide) (by decide))
      (checked_face_independent ((0,1,1,0),.x0) f5 (by decide) (by decide)))
  have h26 := quaternionBlockIndependent_polyMul
    (checked_bent_independent ((0,1,0,0),.x2) (by decide) (by decide))
    (checked_face_independent ((0,1,0,0),.x2) f5 (by decide) (by decide))
  have h37 := checked_bent_independent ((1,1,0,0),.x2) (by decide) (by decide)
  have hlast : quaternionHaar N (polyMul (trace h2) (polyMul bentObservable (faceTrace f5))) ≈ half :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (gather3 _ _ _))
      (Q'.eqv_trans _ _ _ (third_fusion bentObservable h37)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left half _ _ bent_square_haar) (Q'.mul_one_eqv half)))
  have hmiddle : quaternionHaar N (polyMul (trace h1)
      (polyMul bentObservable (polyMul (faceTrace f4) (faceTrace f5)))) ≈ half * half :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (gather4 _ _ _ _))
      (Q'.eqv_trans _ _ _ (second_fusion _ h26) (Q'.mul_eqv_congr_left half _ _ hlast))
  have hfirst : quaternionHaar N (polyMul bentObservable remainingFourFaceProduct) ≈
      half * (half * half) := by
    unfold remainingFourFaceProduct
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (gather5 bentObservable
      (faceTrace f1) (faceTrace f3) (faceTrace f4) (faceTrace f5)))
      (Q'.eqv_trans _ _ _ (first_fusion _ h67) (Q'.mul_eqv_congr_left half _ _ hmiddle))
  exact Q'.eqv_trans _ _ _ hfirst (by decide)

attribute [local irreducible] plaquette characterPolynomial

private theorem W_unit (es : List OrientedBF4Link)
    (hc : es.all (fun e => decide (e.link ∈ cubeLinks)) = true) :
    HaarCarrierEqv N (polyQuaternionNorm (W es)) polyOne := by
  unfold W
  apply QuaternionHaarWordDifference.word_unit value es
  intro e he
  have hm := of_decide_eq_true (List.all_eq_true.mp hc e he)
  have hu := haarNorm_coordinate (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier e.link hm))
  rcases e with ⟨l,b⟩
  unfold value
  cases b
  · exact hu
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hu

private theorem first_square (r : RatPoly)
    (hr : QuaternionBlockIndependent ((baseLinks 2).idxOf ((0,0,0,0),.x0)) r) :
    quaternionHaar N (polyMul (polyMul firstFaceTrace firstFaceTrace) r) ≈ quaternionHaar N r := by
  let p : List OrientedBF4Link := [e13,b23,b02]
  have hp : RatPolyCoeffEqv firstFaceTrace (trace (fwd ((0,0,0,0),.x0)::p)) := by
    have h := face_pin ((0,0,0,0),.p01)
      ((BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_mem_iff 2 _).mpr (by decide))
    unfold faceTrace at h
    unfold firstFaceTrace
    exact h
  have h := fundamental_second_moment N ((baseLinks 2).idxOf ((0,0,0,0),.x0))
    (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier _ (by decide))) (W p) r
    (checked_W_independent _ _ (by decide) (by decide)) hr (W_unit p (by decide))
  have ht : quaternionHaar N (polyMul
      (polyMul (trace (fwd ((0,0,0,0),.x0)::p)) (trace (fwd ((0,0,0,0),.x0)::p))) r) ≈
      quaternionHaar N r := by
    unfold trace
    rw [W_cons]
    unfold value fwd
    exact h
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((hp.mul hp).mul_right r)) ht

private theorem remaining_independent :
    QuaternionBlockIndependent ((baseLinks 2).idxOf ((0,0,0,0),.x0))
      (polyMul bentObservable remainingFourFaceProduct) := by
  unfold remainingFourFaceProduct
  exact quaternionBlockIndependent_polyMul
    (checked_bent_independent _ (by decide) (by decide))
    (quaternionBlockIndependent_polyMul (checked_face_independent _ f1 (by decide) (by decide))
      (quaternionBlockIndependent_polyMul (checked_face_independent _ f3 (by decide) (by decide))
        (quaternionBlockIndependent_polyMul (checked_face_independent _ f4 (by decide) (by decide))
          (checked_face_independent _ f5 (by decide) (by decide)))))

private theorem product_strip (a b c d e : RatPoly) :
    RatPolyCoeffEqv (polyMul a (polyMul b (polyMul c (polyMul d (polyMul e polyOne)))))
      (polyMul a (polyMul b (polyMul c (polyMul d e)))) :=
  (RatPolyCoeffEqv.refl a).mul ((RatPolyCoeffEqv.refl b).mul
    ((RatPolyCoeffEqv.refl c).mul ((RatPolyCoeffEqv.refl d).mul (RatPolyCoeffEqv.mul_one e))))

private theorem five_product (factor : Z4Plaq → RatPoly) (a b c d e : Z4Plaq) :
    RatPolyCoeffEqv (polynomialProduct factor [a,b,c,d,e])
      (polyMul (factor a) (polyMul (factor b) (polyMul (factor c) (polyMul (factor d) (factor e))))) :=
  product_strip (factor a) (factor b) (factor c) (factor d) (factor e)

private theorem complement_product_pin :
    RatPolyCoeffEqv (selectedFaceProduct complementSelection)
      (polyMul firstFaceTrace remainingFourFaceProduct) := by
  have h := five_product (fun face => characterPolynomial (plaquette 2 face).scalar 1)
    ((0,0,0,0),.p01) f1 f3 f4 f5
  unfold selectedFaceProduct complementSelection remainingFourFaceProduct faceTrace firstFaceTrace
  exact h

private theorem square_reorder (p f r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul p f) (polyMul p r)) (polyMul (polyMul p p) (polyMul f r)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
    (by decide) (fun | 0 => p | 1 => f | _ => r)

/-- Exact surviving five-face term in the SAME original subset expansion.
The repeated P is integrated with the entire spectator retained. -/
theorem complement_selection_moment :
    quaternionHaar N (selectedBentInsertion complementSelection) ≈ Q'.mkPos 1 8 (by decide) := by
  unfold selectedBentInsertion
  exact Q'.eqv_trans _ _ _ (haar_of_coeff
    (((RatPolyCoeffEqv.refl _).mul complement_product_pin).trans
      (square_reorder firstFaceTrace bentObservable remainingFourFaceProduct)))
    (Q'.eqv_trans _ _ _ (first_square _ remaining_independent) four_face_bent_moment)

/-- Exact other surviving term, connected to the previously proved original
adjacent-face fusion instead of an independent character-basis assertion. -/
theorem singleton_selection_moment :
    quaternionHaar N (selectedBentInsertion singletonSelection) ≈ half := by
  have hp : RatPolyCoeffEqv (selectedFaceProduct singletonSelection) thirdFaceTrace := by
    unfold selectedFaceProduct singletonSelection thirdFaceTrace
    exact RatPolyCoeffEqv.mul_one _
  have hr : RatPolyCoeffEqv (polyMul (polyMul firstFaceTrace bentObservable) thirdFaceTrace)
      (polyMul (polyMul firstFaceTrace thirdFaceTrace) bentObservable) :=
    (RatPolyCoeffEqv.mul_assoc firstFaceTrace bentObservable thirdFaceTrace).trans
      (((RatPolyCoeffEqv.refl firstFaceTrace).mul
        (RatPolyCoeffEqv.mul_comm bentObservable thirdFaceTrace)).trans
        (RatPolyCoeffEqv.mul_assoc firstFaceTrace thirdFaceTrace bentObservable).symm)
  unfold selectedBentInsertion
  exact Q'.eqv_trans _ _ _ (haar_of_coeff
    (((RatPolyCoeffEqv.refl (polyMul firstFaceTrace bentObservable)).mul hp).trans hr))
    original_bent_two_face_moment

#print axioms W_inverse
#print axioms fusion
#print axioms W_cancel
#print axioms face1_exposed
#print axioms h3_bent
#print axioms first_fusion
#print axioms cancel_second
#print axioms cancel_third
#print axioms second_fusion
#print axioms third_fusion
#print axioms four_face_bent_moment
#print axioms first_square
#print axioms complement_selection_moment
#print axioms singleton_selection_moment

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentComplement
