/-
# Full ORIGINAL angular interference of two neighboring faces

The two literal origin p01 faces have exactly one common physical link.
Their mixed angular term is retained, not bounded by row Cauchy.  All
equalities are Haar-carrier equalities and hence retain the entire original
action as an arbitrary insertion. No smallness, variance comparison, or
continuum conclusion is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentAngularCancellation
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature (plaquette_gamma)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
open YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentAngularCancellation
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_smul)
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionFourBlockExposure
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionCyclicPathCasimir
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (eraseIndex select_perm mem_of_mem_erase not_mem_erase)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear (six_add six_smul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

def adjacentSource (width : Nat) (a b : Q') : RatPoly :=
  polyAdd (polySmul a (leftTrace width)) (polySmul b (rightTrace width))

private def faceGap (f : RatPoly) : RatPoly :=
  polyAdd (cap 4) (polyNeg (polyMul f f))

def adjacentFullDensity (width : Nat) (a b : Q') : RatPoly :=
  polyAdd (polyAdd
    (polySmul (4*(a*a)) (faceGap (leftTrace width)))
    (polySmul (4*(b*b)) (faceGap (rightTrace width))))
    (polySmul (2*(a*b)) (polyAdd (polyMul (leftTrace width) (rightTrace width))
      (polyNeg (polySmul 2 (transportedDifferenceTrace width)))))

def equalWeightPaidDensity (width : Nat) : RatPoly :=
  polyAdd (polyAdd (polySmul 3 (faceGap (leftTrace width)))
    (polySmul 3 (faceGap (rightTrace width))))
    (polySmul 4 (polyAdd (cap 2) (polyNeg (transportedDifferenceTrace width))))

private theorem six_congr {f g : Nat → Nat → RatPoly}
    (h : ∀ i j, RatPolyCoeffEqv (f i j) (g i j)) :
    RatPolyCoeffEqv (six f) (six g) := by
  unfold six
  exact (h 0 1).add ((h 0 2).add ((h 0 3).add
    ((h 1 2).add ((h 1 3).add (h 2 3)))))

private theorem square_congr (block : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (blockGamma block p p) (blockGamma block q q) :=
  six_congr (fun i j => (angularDerivative_congr (4*block+i) (4*block+j) h).mul
    (angularDerivative_congr (4*block+i) (4*block+j) h))

private theorem gamma_square_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    ∀ ids : List Nat, RatPolyCoeffEqv (activeGamma ids p p) (activeGamma ids q q)
  | [] => .refl _
  | i::ids => (square_congr i h).add (gamma_square_congr h ids)

private theorem first_square {n : Nat} (hn : 3 < n)
    (x y z t : Nat) (hx : x < n) (hy : y < n) (hz : z < n) (ht : t < n)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (r0 r1 r2 r3 : Bool) (p : RatPoly)
    (hp : RatPolyCoeffEqv p (characterPolynomial (word x y z t r0 r1 r2 r3).scalar 1)) :
    HaarCarrierEqv n (blockGamma x p p) (faceGap p) := by
  let a : Fin n := ⟨x,hx⟩
  let b : Fin n := ⟨y,hy⟩
  let c : Fin n := ⟨z,hz⟩
  let d : Fin n := ⟨t,ht⟩
  have h := oriented_fourWord_first_angularSquare_of_exposure hn a b c d
    (fourBlockExposure hn a b c d hxy hxz hxt hyz hyt hzt) r0 r1 r2 r3
  exact (RatPolyCoeffEqv.haarCarrier (square_congr x hp)).trans
    (h.trans (RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (hp.symm.mul hp.symm)))))

/-- Exact one-link curvature for an actual incident spatial face. -/
private theorem incident_square (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face) :
    let f := characterPolynomial (plaquette width face).scalar 1
    HaarCarrierEqv (N width) (blockGamma ((baseLinks width).idxOf l) f f) (faceGap f) := by
  dsimp only
  let S := fullRangePlaquetteSelection width face hf
  let f := characterPolynomial (plaquette width face).scalar 1
  have hn : (S.a::S.b::S.c::S.d::S.rest).Nodup :=
    (S.perm.nodup_iff).mp (CayleyParentInj.range_nodup (N width))
  have hna := (List.nodup_cons.mp hn).1
  have hnb := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have hnc := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).1
  have hab : S.a ≠ S.b := by
    intro h
    exact hna (by simp [h])
  have hac : S.a ≠ S.c := by
    intro h
    exact hna (by simp [h])
  have had : S.a ≠ S.d := by
    intro h
    exact hna (by simp [h])
  have hbc : S.b ≠ S.c := by
    intro h
    exact hnb (by simp [h])
  have hbd : S.b ≠ S.d := by
    intro h
    exact hnb (by simp [h])
  have hcd : S.c ≠ S.d := by
    intro h
    exact hnc (by simp [h])
  have hi (i : Nat) (hm : i ∈ [S.a,S.b,S.c,S.d]) : i < N width :=
    List.mem_range.mp (S.perm.mem_iff.mpr (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm ⊢
      rcases hm with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have ha := hi S.a (by simp)
  have hb := hi S.b (by simp)
  have hc := hi S.c (by simp)
  have hd := hi S.d (by simp)
  have hfour : 3 < N width := by
    have he := S.perm.length_eq
    simp only [List.length_range, List.length_cons] at he
    omega
  have h0 : RatPolyCoeffEqv f
      (characterPolynomial (word S.a S.b S.c S.d false false true true).scalar 1) :=
    characterPolynomial_coeffEqv S.scalar 1
  have h1 := h0.trans (characterPolynomial_coeffEqv
    (word_cyclic S.a S.b S.c S.d false false true true) 1)
  have h2 := h1.trans (characterPolynomial_coeffEqv
    (word_cyclic S.b S.c S.d S.a false true true false) 1)
  have h3 := h2.trans (characterPolynomial_coeffEqv
    (word_cyclic S.c S.d S.a S.b true true false false) 1)
  have hm := S.slots.mem_iff.mp (faceSlot_mem width face hl)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with h | h | h | h
  · rw [h]
    exact first_square hfour _ _ _ _ ha hb hc hd hab hac had hbc hbd hcd
      false false true true f h0
  · rw [h]
    exact first_square hfour _ _ _ _ hb hc hd ha hbc hbd hab.symm hcd hac.symm had.symm
      false true true false f h1
  · rw [h]
    exact first_square hfour _ _ _ _ hc hd ha hb hcd hac.symm hbc.symm had.symm hbd.symm hab
      true true false false f h2
  · rw [h]
    exact first_square hfour _ _ _ _ hd ha hb hc had.symm hbd.symm hcd.symm hab hac hbc
      true false false true f h3

private theorem common_edge (l : Z4Link)
    (hl : l ∈ edgesOf leftFace) (hr : l ∈ edgesOf rightFace) :
    l = ((1,0,0,0), Dir4.x1) := by
  simp only [leftFace, rightFace, edgesOf, dirsOf, addE,
    List.mem_cons, List.mem_nil_iff, or_false] at hl hr
  rcases hl with h | h | h | h
  · subst l
    rcases hr with h | h | h | h <;> cases h
  · subst l
    rcases hr with h | h | h | h <;> cases h
  · subst l
    rcases hr with h | h | h | h <;> cases h
  · exact h

private theorem common_row (width : Nat) (b : Nat)
    (hl : blockRow width b leftFace = true) (hr : blockRow width b rightFace = true) :
    b = sharedBlock width := by
  obtain ⟨l,hlf,hlp,hli⟩ := (blockRow_iff width b leftFace).mp hl
  obtain ⟨r,hrf,hrp,hri⟩ := (blockRow_iff width b rightFace).mp hr
  have he := idxOf_injective_on_members hlp hrp (hli.trans hri.symm)
  subst r
  have hl := common_edge l hlf hrf
  subst l
  exact hli.symm

private theorem block_cross_zero (width b : Nat) (hb : b < N width)
    (hne : b ≠ sharedBlock width) :
    RatPolyCoeffEqv (blockGamma b (leftTrace width) (rightTrace width)) polyZero := by
  have hz (face : Z4Plaq) (h : blockRow width b face = false) (i j : Nat)
      (hi : i < 4) (hj : j < 4) := blockRow_derivative_zero width b face hb h hi hj
  cases hl : blockRow width b leftFace with
  | false =>
      unfold blockGamma
      exact (by
        unfold six
        have h (i j : Nat) (hi : i < 4) (hj : j < 4) :=
          ((hz leftFace hl i j hi hj).mul_right
            (blockAngularDerivative b i j (rightTrace width))).trans
              (RatPolyCoeffEqv.mul_zero_left _)
        exact ((h 0 1 (by decide) (by decide)).add
          ((h 0 2 (by decide) (by decide)).add
            ((h 0 3 (by decide) (by decide)).add
              ((h 1 2 (by decide) (by decide)).add
                ((h 1 3 (by decide) (by decide)).add
                  (h 2 3 (by decide) (by decide))))))).trans (RatPolyCoeffEqv.refl _))
  | true =>
      have hr : blockRow width b rightFace = false := by
        cases hr : blockRow width b rightFace with
        | false => rfl
        | true => exact False.elim (hne (common_row width b hl hr))
      unfold blockGamma six
      have h (i j : Nat) (hi : i < 4) (hj : j < 4) :=
        ((hz rightFace hr i j hi hj).mul_left
          (blockAngularDerivative b i j (leftTrace width))).trans
            (RatPolyCoeffEqv.mul_zero_right _)
      exact ((h 0 1 (by decide) (by decide)).add
        ((h 0 2 (by decide) (by decide)).add
          ((h 0 3 (by decide) (by decide)).add
            ((h 1 2 (by decide) (by decide)).add
              ((h 1 3 (by decide) (by decide)).add
                (h 2 3 (by decide) (by decide))))))).trans (RatPolyCoeffEqv.refl _)

private theorem gamma_perm (f g : RatPoly) {xs ys : List Nat} (h : xs.Perm ys) :
    RatPolyCoeffEqv (activeGamma xs f g) (activeGamma ys f g) := by
  induction h with
  | nil => exact .refl _
  | cons i _ ih => exact (RatPolyCoeffEqv.refl _).add ih
  | swap i j rest =>
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 1) (.add (.var 0) (.var 2))) (by decide)
        (fun | 0 => blockGamma j f g | 1 => blockGamma i f g
             | _ => activeGamma rest f g)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem gamma_zero (f g : RatPoly) : ∀ ids : List Nat,
    (∀ i, i ∈ ids → RatPolyCoeffEqv (blockGamma i f g) polyZero) →
    RatPolyCoeffEqv (activeGamma ids f g) polyZero
  | [], _ => .refl _
  | i::ids, h =>
      ((h i List.mem_cons_self).add
        (gamma_zero f g ids (fun j hj => h j (List.mem_cons_of_mem i hj)))).trans
          (RatPolyCoeffEqv.add_zero _)

private theorem cross_local (width : Nat) (hw : 2 ≤ width) :
    RatPolyCoeffEqv (activeGamma (List.range (N width)) (leftTrace width) (rightTrace width))
      (blockGamma (sharedBlock width) (leftTrace width) (rightTrace width)) := by
  let ids := List.range (N width)
  let s := sharedBlock width
  have hperm := select_perm s (List.mem_range.mpr (sharedBlock_lt width hw))
  have hz := gamma_zero (leftTrace width) (rightTrace width) (eraseIndex s ids)
    (fun i hi => block_cross_zero width i
      (List.mem_range.mp (mem_of_mem_erase s hi))
      (fun he => by
        have his : i = s := he
        have ht : s ∈ eraseIndex s ids := by simpa only [his] using hi
        exact (not_mem_erase s (ids:=ids) (CayleyParentInj.range_nodup _)) ht))
  exact (gamma_perm _ _ hperm).trans
    (((RatPolyCoeffEqv.refl _).add hz).trans (RatPolyCoeffEqv.add_zero _))

private theorem block_expand (block : Nat) (f g : RatPoly) (a b : Q') :
    RatPolyCoeffEqv (blockGamma block (polyAdd (polySmul a f) (polySmul b g))
      (polyAdd (polySmul a f) (polySmul b g)))
      (polyAdd (polyAdd (polySmul (a*a) (blockGamma block f f))
        (polySmul (b*b) (blockGamma block g g)))
        (polySmul (a*b) (polySmul 2 (blockGamma block f g)))) := by
  let D := fun i j p => blockAngularDerivative block i j p
  have h (i j : Nat) : RatPolyCoeffEqv
      (polyMul (D i j (polyAdd (polySmul a f) (polySmul b g)))
        (D i j (polyAdd (polySmul a f) (polySmul b g))))
      (polyAdd (polyAdd (polySmul (a*a) (polyMul (D i j f) (D i j f)))
        (polySmul (b*b) (polyMul (D i j g) (D i j g))))
        (polySmul (a*b) (polySmul 2 (polyMul (D i j f) (D i j g))))) := by
    have hd := (angularDerivative_add (4*block+i) (4*block+j) _ _).trans
      ((angularDerivative_smul (4*block+i) (4*block+j) a f).add
        (angularDerivative_smul (4*block+i) (4*block+j) b g))
    have hm (a b : Q') (p q : RatPoly) : RatPolyCoeffEqv
        (polyMul (polySmul a p) (polySmul b q)) (polySmul (a*b) (polyMul p q)) :=
      (RatPolyCoeffEqv.polyMul_smul_left a p _).trans
        (((RatPolyCoeffEqv.polyMul_smul_right b p q).smul a).trans
          (RatPolyCoeffEqv.smul_assoc a b _))
    have he := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.const 2) (.mul (.var 0) (.var 1)))) (by decide)
      (fun | 0 => polySmul a (D i j f) | _ => polySmul b (D i j g))
    have hs := ((hm a a (D i j f) (D i j f)).add
      (hm b b (D i j g) (D i j g))).add
        ((cap_mul_left 2 _).trans ((hm a b (D i j f) (D i j g)).smul 2))
    have hc := (RatPolyCoeffEqv.smul_assoc 2 (a*b) (polyMul (D i j f) (D i j g))).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv 2 (a*b)) _).trans
        (RatPolyCoeffEqv.smul_assoc (a*b) 2 _).symm)
    exact (hd.mul hd).trans (he.trans (hs.trans ((RatPolyCoeffEqv.refl _).add hc)))
  exact (six_congr h).trans
    ((six_add _ _).trans (((six_add _ _).trans
      ((six_smul (a*a) _).add (six_smul (b*b) _))).add
        ((six_smul (a*b) _).trans ((six_smul 2 _).smul (a*b)))))

private theorem gamma_expand (ids : List Nat) (f g : RatPoly) (a b : Q') :
    RatPolyCoeffEqv (activeGamma ids (polyAdd (polySmul a f) (polySmul b g))
      (polyAdd (polySmul a f) (polySmul b g)))
      (polyAdd (polyAdd (polySmul (a*a) (activeGamma ids f f))
        (polySmul (b*b) (activeGamma ids g g)))
        (polySmul (a*b) (polySmul 2 (activeGamma ids f g)))) := by
  induction ids with
  | nil => exact .refl _
  | cons i ids ih =>
      exact ((block_expand i f g a b).add ih).trans
        ((coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.add (.var 0) (.var 1)) (.var 2))
            (.add (.add (.var 3) (.var 4)) (.var 5)))
          (.add (.add (.add (.var 0) (.var 3)) (.add (.var 1) (.var 4)))
            (.add (.var 2) (.var 5))) (by decide)
          (fun
            | 0 => polySmul (a*a) (blockGamma i f f)
            | 1 => polySmul (b*b) (blockGamma i g g)
            | 2 => polySmul (a*b) (polySmul 2 (blockGamma i f g))
            | 3 => polySmul (a*a) (activeGamma ids f f)
            | 4 => polySmul (b*b) (activeGamma ids g g)
            | _ => polySmul (a*b) (polySmul 2 (activeGamma ids f g)))).trans
          (((RatPolyCoeffEqv.smul_add (a*a) _ _).symm.add
            (RatPolyCoeffEqv.smul_add (b*b) _ _).symm).add
              ((RatPolyCoeffEqv.smul_add (a*b) _ _).symm.trans
                ((RatPolyCoeffEqv.smul_add 2 _ _).symm.smul (a*b)))))

private theorem block_add (s : Nat) (f g : RatPoly) :
    RatPolyCoeffEqv (blockGamma s (polyAdd f g) (polyAdd f g))
      (polyAdd (polyAdd (blockGamma s f f) (blockGamma s g g))
        (polySmul 2 (blockGamma s f g))) := by
  have hi := (RatPolyCoeffEqv.one_smul f).add (RatPolyCoeffEqv.one_smul g)
  have hu (p : RatPoly) : RatPolyCoeffEqv (polySmul ((1:Q')*1) p) p :=
    (RatPolyCoeffEqv.smul_coefficient (by decide) p).trans (RatPolyCoeffEqv.one_smul p)
  exact (square_congr s hi.symm).trans ((block_expand s f g 1 1).trans
    (((hu _).add (hu _)).add (hu _)))

private theorem shared_squares (width : Nat) (hw : 2 ≤ width) :
    HaarCarrierEqv (N width)
      (blockGamma (sharedBlock width) (leftTrace width) (leftTrace width))
      (faceGap (leftTrace width)) ∧
    HaarCarrierEqv (N width)
      (blockGamma (sharedBlock width) (rightTrace width) (rightTrace width))
      (faceGap (rightTrace width)) := by
  have hf := adjacent_faces_spatial width hw
  exact ⟨incident_square width leftFace hf.1 ((1,0,0,0),.x1)
      (by simp [leftFace, edgesOf, dirsOf, addE]),
    incident_square width rightFace hf.2 ((1,0,0,0),.x1)
      (by simp [rightFace, edgesOf, dirsOf, addE])⟩

private theorem shared_cross (width : Nat) (hw : 2 ≤ width) :
    HaarCarrierEqv (N width)
      (polySmul 2 (blockGamma (sharedBlock width) (leftTrace width) (rightTrace width)))
      (polySmul 2 (polyAdd (polyMul (leftTrace width) (rightTrace width))
        (polyNeg (polySmul 2 (transportedDifferenceTrace width))))) := by
  let f := leftTrace width
  let g := rightTrace width
  let d := transportedDifferenceTrace width
  let sf := blockGamma (sharedBlock width) f f
  let sg := blockGamma (sharedBlock width) g g
  let cross := polySmul 2 (blockGamma (sharedBlock width) f g)
  let diff := polyMul (polyAdd f (polyNeg g)) (polyAdd f (polyNeg g))
  let rhs := polySmul 4 (polyAdd (cap 2) (polyNeg d))
  have he : HaarCarrierEqv (N width) (polyAdd (polyAdd (polyAdd sf sg) cross) diff) rhs :=
    (RatPolyCoeffEqv.haarCarrier ((block_add _ f g).add (.refl _))).symm.trans
      (original_adjacent_angular_difference width hw)
  have hc := HaarCarrierEqv.add he
    (HaarCarrierEqv.refl (N width) (polyAdd (polyNeg diff)
      (polyAdd (polyNeg sf) (polyNeg sg))))
  have hleft : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyAdd (polyAdd sf sg) cross) diff)
        (polyAdd (polyNeg diff) (polyAdd (polyNeg sf) (polyNeg sg)))) cross :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.add (.neg (.var 3)) (.add (.neg (.var 0)) (.neg (.var 1)))))
      (.var 2) (by decide) (fun | 0 => sf | 1 => sg | 2 => cross | _ => diff)
  have hs := shared_squares width hw
  have hright := HaarCarrierEqv.add (HaarCarrierEqv.refl (N width) rhs)
    (HaarCarrierEqv.add (HaarCarrierEqv.refl (N width) (polyNeg diff))
      (HaarCarrierEqv.add (HaarCarrierEqv.neg hs.1) (HaarCarrierEqv.neg hs.2)))
  have hp : RatPolyCoeffEqv
      (polyAdd rhs (polyAdd (polyNeg diff)
        (polyAdd (polyNeg (faceGap f)) (polyNeg (faceGap g)))))
      (polySmul 2 (polyAdd (polyMul f g) (polyNeg (polySmul 2 d)))) := by
    let lhs : PolyExpr := .add (.mul (.const 4) (.add (.const 2) (.neg (.var 2))))
      (.add (.neg (.mul (.add (.var 0) (.neg (.var 1)))
        (.add (.var 0) (.neg (.var 1)))))
        (.add (.neg (.add (.const 4) (.neg (.mul (.var 0) (.var 0)))))
          (.neg (.add (.const 4) (.neg (.mul (.var 1) (.var 1)))))))
    let out : PolyExpr := .mul (.const 2)
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.const 2) (.var 2))))
    let env : Nat → RatPoly := fun | 0 => f | 1 => g | _ => d
    have hl : RatPolyCoeffEqv (coeffEvalExpr env lhs)
        (polyAdd rhs (polyAdd (polyNeg diff)
          (polyAdd (polyNeg (faceGap f)) (polyNeg (faceGap g))))) :=
      (cap_mul_left 4 _).add (.refl _)
    have hr : RatPolyCoeffEqv (coeffEvalExpr env out)
        (polySmul 2 (polyAdd (polyMul f g) (polyNeg (polySmul 2 d)))) :=
      (cap_mul_left 2 _).trans
        (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left 2 d))).smul 2)
    exact hl.symm.trans ((coeffEvalExpr_eqv_of_normalize_eq lhs out (by decide) env).trans hr)
  exact (RatPolyCoeffEqv.haarCarrier hleft).symm.trans
    (hc.trans (hright.trans (RatPolyCoeffEqv.haarCarrier hp)))

/-- Full mixed interference for arbitrary signed coefficients on the original carrier. -/
theorem adjacent_full_angular (width : Nat) (hw : 2 ≤ width) (a b : Q') :
    HaarCarrierEqv (N width)
      (activeGamma (List.range (N width)) (adjacentSource width a b) (adjacentSource width a b))
      (adjacentFullDensity width a b) := by
  have hf := adjacent_faces_spatial width hw
  have hl := plaquette_gamma width leftFace hf.1
  have hr := plaquette_gamma width rightFace hf.2
  have hc := (RatPolyCoeffEqv.haarCarrier ((cross_local width hw).smul 2)).trans
    (shared_cross width hw)
  have h := HaarCarrierEqv.add
    (HaarCarrierEqv.add (HaarCarrierEqv.smul (a*a) hl) (HaarCarrierEqv.smul (b*b) hr))
    (HaarCarrierEqv.smul (a*b) hc)
  have hs (q : Q') (p : RatPoly) :
      RatPolyCoeffEqv (polySmul q (polySmul 4 p)) (polySmul (4*q) p) :=
    (RatPolyCoeffEqv.smul_assoc q 4 p).trans
      (RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv q 4) p)
  have hc' (q : Q') (p : RatPoly) :
      RatPolyCoeffEqv (polySmul q (polySmul 2 p)) (polySmul (2*q) p) :=
    (RatPolyCoeffEqv.smul_assoc q 2 p).trans
      (RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv q 2) p)
  exact (RatPolyCoeffEqv.haarCarrier (gamma_expand _ _ _ a b)).trans
    (h.trans (RatPolyCoeffEqv.haarCarrier (((hs (a*a) _).add (hs (b*b) _)).add (hc' (a*b) _))))

attribute [local irreducible] leftTrace rightTrace transportedDifferenceTrace

/-- Equal-weight cancellation with all four-link contributions and the actual difference square. -/
theorem adjacent_full_angular_paid (width : Nat) (hw : 2 ≤ width) :
    HaarCarrierEqv (N width)
      (polyAdd (activeGamma (List.range (N width))
        (polyAdd (leftTrace width) (rightTrace width))
        (polyAdd (leftTrace width) (rightTrace width)))
        (polyMul (polyAdd (leftTrace width) (polyNeg (rightTrace width)))
          (polyAdd (leftTrace width) (polyNeg (rightTrace width)))))
      (equalWeightPaidDensity width) := by
  let f := leftTrace width
  let g := rightTrace width
  let d := transportedDifferenceTrace width
  have hp := (RatPolyCoeffEqv.one_smul f).add (RatPolyCoeffEqv.one_smul g)
  have hg : RatPolyCoeffEqv
      (activeGamma (List.range (N width)) (polyAdd f g) (polyAdd f g))
      (activeGamma (List.range (N width)) (adjacentSource width 1 1) (adjacentSource width 1 1)) := by
    exact gamma_square_congr hp.symm _
  have h := HaarCarrierEqv.add
    ((RatPolyCoeffEqv.haarCarrier hg).trans (adjacent_full_angular width hw 1 1))
    (HaarCarrierEqv.refl (N width) (polyMul (polyAdd f (polyNeg g)) (polyAdd f (polyNeg g))))
  have he : RatPolyCoeffEqv
      (polyAdd (adjacentFullDensity width 1 1)
        (polyMul (polyAdd f (polyNeg g)) (polyAdd f (polyNeg g))))
      (equalWeightPaidDensity width) := by
    let lhs : PolyExpr := .add
      (.add (.add (.mul (.const 4) (.add (.const 4) (.neg (.mul (.var 0) (.var 0)))))
        (.mul (.const 4) (.add (.const 4) (.neg (.mul (.var 1) (.var 1))))))
        (.mul (.const 2) (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.const 2) (.var 2))))))
      (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
    let out : PolyExpr := .add
      (.add (.mul (.const 3) (.add (.const 4) (.neg (.mul (.var 0) (.var 0)))))
        (.mul (.const 3) (.add (.const 4) (.neg (.mul (.var 1) (.var 1))))))
      (.mul (.const 4) (.add (.const 2) (.neg (.var 2))))
    let env : Nat → RatPoly := fun | 0 => f | 1 => g | _ => d
    have hl : RatPolyCoeffEqv (coeffEvalExpr env lhs)
        (polyAdd (adjacentFullDensity width 1 1)
          (polyMul (polyAdd f (polyNeg g)) (polyAdd f (polyNeg g)))) :=
      (((cap_mul_left 4 _).add (cap_mul_left 4 _)).add
        ((cap_mul_left 2 _).trans
          (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left 2 d))).smul 2))).add
            (.refl _)
    have hr : RatPolyCoeffEqv (coeffEvalExpr env out) (equalWeightPaidDensity width) :=
      ((cap_mul_left 3 _).add (cap_mul_left 3 _)).add (cap_mul_left 4 _)
    exact hl.symm.trans ((coeffEvalExpr_eqv_of_normalize_eq lhs out (by decide) env).trans hr)
  exact h.trans (RatPolyCoeffEqv.haarCarrier he)

end YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular.adjacentSource
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular.adjacentFullDensity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular.equalWeightPaidDensity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular.adjacent_full_angular
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular.adjacent_full_angular_paid
