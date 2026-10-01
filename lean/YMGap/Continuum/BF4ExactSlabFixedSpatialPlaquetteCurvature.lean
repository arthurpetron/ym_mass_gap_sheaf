/-
# Curvature of an original spatial plaquette

The four angular-square terms belong to the literal face selected from the
original spatial carrier. Cyclicity changes only the presentation of its
scalar word; every equality below retains arbitrary Haar insertions.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir
import YMGap.Continuum.SU2QuaternionActiveCasimirProduct
import YMGap.Continuum.SU2QuaternionAngularSquareLocality
import YMGap.Continuum.SU2QuaternionCyclicPathCasimir

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularSquareLocality
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionCyclicPathCasimir
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionFourBlockExposure
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

private theorem blockSquare_coeff (block : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (blockAngularSquare block p) (blockAngularSquare block q) := by
  have hd (i j : Nat) := angularDerivative_congr (4*block+i) (4*block+j) h
  unfold blockAngularSquare six
  exact ((hd 0 1).mul (hd 0 1)).add
    (((hd 0 2).mul (hd 0 2)).add
      (((hd 0 3).mul (hd 0 3)).add
        (((hd 1 2).mul (hd 1 2)).add
          (((hd 1 3).mul (hd 1 3)).add
            ((hd 2 3).mul (hd 2 3))))))

private theorem gamma_perm (p q : RatPoly) {first second : List Nat}
    (h : first.Perm second) :
    RatPolyCoeffEqv (activeGamma first p q) (activeGamma second p q) := by
  unfold activeGamma
  induction h with
  | nil => exact RatPolyCoeffEqv.refl polyZero
  | cons x h ih => exact (RatPolyCoeffEqv.refl (blockGamma x p q)).add ih
  | swap x y rest =>
      change RatPolyCoeffEqv
        (polyAdd (blockGamma y p q)
          (polyAdd (blockGamma x p q) (polySum (rest.map fun i => blockGamma i p q))))
        (polyAdd (blockGamma x p q)
          (polyAdd (blockGamma y p q) (polySum (rest.map fun i => blockGamma i p q))))
      exact (RatPolyCoeffEqv.add_assoc _ _ _).symm.trans
        (((RatPolyCoeffEqv.add_comm (blockGamma y p q) (blockGamma x p q)).add
          (RatPolyCoeffEqv.refl _)).trans
            (RatPolyCoeffEqv.add_assoc _ _ _))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem gamma_independent_zero : ∀ (rest : List Nat) (p : RatPoly),
    (∀ i, i ∈ rest → QuaternionBlockIndependent i p) →
    RatPolyCoeffEqv (activeGamma rest p p) polyZero
  | [], _, _ => RatPolyCoeffEqv.refl polyZero
  | i::rest, p, h => by
      change RatPolyCoeffEqv
        (polyAdd (blockGamma i p p) (activeGamma rest p p)) polyZero
      exact ((blockAngularSquare_zero (h i List.mem_cons_self)).add
        (gamma_independent_zero rest p
          (fun j hj => h j (List.mem_cons_of_mem i hj)))).trans
        (RatPolyCoeffEqv.add_zero polyZero)

private theorem first_square_of_word {n : Nat} (hfour : 3 < n)
    (x y z t : Nat) (hx : x < n) (hy : y < n) (hz : z < n) (ht : t < n)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (r0 r1 r2 r3 : Bool) (p : RatPoly)
    (hp : RatPolyCoeffEqv p
      (characterPolynomial (word x y z t r0 r1 r2 r3).scalar 1)) :
    HaarCarrierEqv n (blockGamma x p p)
      (polyAdd (cap 4) (polyNeg (polyMul p p))) := by
  let a : Fin n := ⟨x, hx⟩
  let b : Fin n := ⟨y, hy⟩
  let c : Fin n := ⟨z, hz⟩
  let d : Fin n := ⟨t, ht⟩
  let e := fourBlockExposure hfour a b c d hxy hxz hxt hyz hyt hzt
  have hw : HaarCarrierEqv n
      (blockAngularSquare x (characterPolynomial (word x y z t r0 r1 r2 r3).scalar 1))
      (polyAdd (cap 4)
        (polyNeg (polyMul
          (characterPolynomial (word x y z t r0 r1 r2 r3).scalar 1)
          (characterPolynomial (word x y z t r0 r1 r2 r3).scalar 1)))) := by
    simpa only [a, b, c, d] using
      oriented_fourWord_first_angularSquare_of_exposure hfour a b c d e r0 r1 r2 r3
  change HaarCarrierEqv n (blockAngularSquare x p)
    (polyAdd (cap 4) (polyNeg (polyMul p p)))
  exact (RatPolyCoeffEqv.haarCarrier (blockSquare_coeff x hp)).trans
    (hw.trans (RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.refl _).add
        (RatPolyCoeffEqv.neg (hp.symm.mul hp.symm)))))

/-- Literal four-link angular curvature, including all four original block
positions and no replacement by a canonical surrogate. -/
theorem plaquette_gamma (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    let f := characterPolynomial (plaquette width face).scalar 1
    HaarCarrierEqv (N width)
      (activeGamma (List.range (N width)) f f)
      (polySmul 4 (polyAdd (cap 4) (polyNeg (polyMul f f)))) := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  let S := fullRangePlaquetteSelection width face hf
  let gap := polyAdd (cap 4) (polyNeg (polyMul f f))
  have hn : (S.a::S.b::S.c::S.d::S.rest).Nodup :=
    (S.perm.nodup_iff).mp (CayleyParentInj.range_nodup (N width))
  have ha0 := (List.nodup_cons.mp hn).1
  have htailb := (List.nodup_cons.mp hn).2
  have hb0 := (List.nodup_cons.mp htailb).1
  have htailc := (List.nodup_cons.mp htailb).2
  have hc0 := (List.nodup_cons.mp htailc).1
  have htaild := (List.nodup_cons.mp htailc).2
  have hd0 := (List.nodup_cons.mp htaild).1
  have hab : S.a ≠ S.b := by
    intro he
    exact ha0 (by simpa [he] using (List.mem_cons_self S.b (S.c::S.d::S.rest)))
  have hac : S.a ≠ S.c := by
    intro he
    exact ha0 (by simpa [he] using
      (List.mem_cons_of_mem S.b (List.mem_cons_self S.c (S.d::S.rest))))
  have had : S.a ≠ S.d := by
    intro he
    exact ha0 (by simpa [he] using
      (List.mem_cons_of_mem S.b
        (List.mem_cons_of_mem S.c (List.mem_cons_self S.d S.rest))))
  have hbc : S.b ≠ S.c := by
    intro he
    exact hb0 (by simpa [he] using (List.mem_cons_self S.c (S.d::S.rest)))
  have hbd : S.b ≠ S.d := by
    intro he
    exact hb0 (by simpa [he] using
      (List.mem_cons_of_mem S.c (List.mem_cons_self S.d S.rest)))
  have hcd : S.c ≠ S.d := by
    intro he
    exact hc0 (by simpa [he] using (List.mem_cons_self S.d S.rest))
  have hin : ∀ i, i ∈ [S.a,S.b,S.c,S.d] → i < N width := by
    intro i hi
    exact List.mem_range.mp (S.perm.mem_iff.mpr (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi ⊢
      rcases hi with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have ha : S.a < N width := hin S.a (by simp)
  have hb : S.b < N width := hin S.b (by simp)
  have hc : S.c < N width := hin S.c (by simp)
  have hd : S.d < N width := hin S.d (by simp)
  have hfour : 3 < N width := by
    have hlen := S.perm.length_eq
    simp only [List.length_range, List.length_cons] at hlen
    omega
  have hword0 : RatPolyCoeffEqv f
      (characterPolynomial (word S.a S.b S.c S.d false false true true).scalar 1) :=
    characterPolynomial_coeffEqv S.scalar 1
  have hword1 : RatPolyCoeffEqv f
      (characterPolynomial (word S.b S.c S.d S.a false true true false).scalar 1) :=
    hword0.trans (characterPolynomial_coeffEqv
      (word_cyclic S.a S.b S.c S.d false false true true) 1)
  have hword2 : RatPolyCoeffEqv f
      (characterPolynomial (word S.c S.d S.a S.b true true false false).scalar 1) :=
    hword1.trans (characterPolynomial_coeffEqv
      (word_cyclic S.b S.c S.d S.a false true true false) 1)
  have hword3 : RatPolyCoeffEqv f
      (characterPolynomial (word S.d S.a S.b S.c true false false true).scalar 1) :=
    hword2.trans (characterPolynomial_coeffEqv
      (word_cyclic S.c S.d S.a S.b true true false false) 1)
  have hA : HaarCarrierEqv (N width) (blockGamma S.a f f) gap :=
    first_square_of_word hfour S.a S.b S.c S.d ha hb hc hd
      hab hac had hbc hbd hcd false false true true f hword0
  have hB : HaarCarrierEqv (N width) (blockGamma S.b f f) gap :=
    first_square_of_word hfour S.b S.c S.d S.a hb hc hd ha
      hbc hbd hab.symm hcd hac.symm had.symm false true true false f hword1
  have hC : HaarCarrierEqv (N width) (blockGamma S.c f f) gap :=
    first_square_of_word hfour S.c S.d S.a S.b hc hd ha hb
      hcd hac.symm hbc.symm had.symm hbd.symm hab true true false false f hword2
  have hD : HaarCarrierEqv (N width) (blockGamma S.d f f) gap :=
    first_square_of_word hfour S.d S.a S.b S.c hd ha hb hc
      had.symm hbd.symm hcd.symm hab hac hbc true false false true f hword3
  have hrest : ∀ i, i ∈ S.rest → QuaternionBlockIndependent i f := by
    intro i hi
    have hirange : i ∈ List.range (N width) := S.perm.mem_iff.mpr (by
      exact List.mem_cons_of_mem S.a
        (List.mem_cons_of_mem S.b
          (List.mem_cons_of_mem S.c (List.mem_cons_of_mem S.d hi))))
    have hna : S.a ≠ i := by
      intro he
      exact ha0 (by simpa [he] using
        (List.mem_cons_of_mem S.b
          (List.mem_cons_of_mem S.c (List.mem_cons_of_mem S.d hi))))
    have hnb : S.b ≠ i := by
      intro he
      exact hb0 (by simpa [he] using
        (List.mem_cons_of_mem S.c (List.mem_cons_of_mem S.d hi)))
    have hnc : S.c ≠ i := by
      intro he
      exact hc0 (by simpa [he] using (List.mem_cons_of_mem S.d hi))
    have hnd : S.d ≠ i := by
      intro he
      exact hd0 (by simpa [he] using hi)
    have hnot : i ∉ [S.a,S.b,S.c,S.d] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
      exact ⟨hna.symm, hnb.symm, hnc.symm, hnd.symm⟩
    have hslot : i ∉ faceSlots width face := by
      intro hs
      exact hnot (S.slots.mem_iff.mp hs)
    have hspec : i ∈ spectatorBlocks width face :=
      List.mem_filter.mpr ⟨hirange, by simp [hslot]⟩
    exact plaquette_spectator_independent width face i hspec
  have hzero := gamma_independent_zero S.rest f hrest
  have hreduce : RatPolyCoeffEqv
      (activeGamma (List.range (N width)) f f)
      (polyAdd (blockGamma S.a f f)
        (polyAdd (blockGamma S.b f f)
          (polyAdd (blockGamma S.c f f) (blockGamma S.d f f)))) := by
    refine (gamma_perm f f S.perm).trans ?_
    change RatPolyCoeffEqv
      (polyAdd (blockGamma S.a f f)
        (polyAdd (blockGamma S.b f f)
          (polyAdd (blockGamma S.c f f)
            (polyAdd (blockGamma S.d f f) (activeGamma S.rest f f))))) _
    exact ((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.refl _).add
          ((RatPolyCoeffEqv.refl _).add hzero)))).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.refl _).add
          ((RatPolyCoeffEqv.refl _).add
            (RatPolyCoeffEqv.add_zero _))))
  have hsum : RatPolyCoeffEqv
      (polyAdd gap (polyAdd gap (polyAdd gap gap)))
      (polySmul 4 gap) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.add (.var 0) (.add (.var 0) (.var 0))))
      (.mul (.const 4) (.var 0)) (by decide) (fun _ => gap)).trans
      (cap_mul_left 4 gap)
  exact (RatPolyCoeffEqv.haarCarrier hreduce).trans
    ((HaarCarrierEqv.add hA
      (HaarCarrierEqv.add hB (HaarCarrierEqv.add hC hD))).trans
      (RatPolyCoeffEqv.haarCarrier hsum))

/-- The square of the literal physical plaquette has the spin-two Casimir
with the constant mode removed. This follows from the four selected angular
squares; it does not infer a Casimir from a heat asymptotic. -/
theorem plaquette_square_casimir (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    let f := characterPolynomial (plaquette width face).scalar 1
    HaarCarrierEqv (N width)
      (activeCasimirPolynomial (List.range (N width)) (polyMul f f))
      (polySmul 32 (polyAdd (polyMul f f) (polyNeg polyOne))) := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  let active := List.range (N width)
  let gap := polyAdd (cap 4) (polyNeg (polyMul f f))
  let target := polyAdd (polyMul f f) (polyNeg polyOne)
  have hCf : HaarCarrierEqv (N width)
      (activeCasimirPolynomial active f) (polyMul (cap 12) f) :=
    (plaquette_casimir width face hf).trans
      (RatPolyCoeffEqv.haarCarrier (cap_mul_left 12 f).symm)
  have hG : HaarCarrierEqv (N width)
      (activeGamma active f f) (polyMul (cap 4) gap) :=
    (plaquette_gamma width face hf).trans
      (RatPolyCoeffEqv.haarCarrier (cap_mul_left 4 gap).symm)
  have hprod : HaarCarrierEqv (N width)
      (activeCasimirPolynomial active (polyMul f f))
      (polyAdd
        (polyAdd (polyMul (activeCasimirPolynomial active f) f)
          (polyMul f (activeCasimirPolynomial active f)))
        (polyMul (cap (-2)) (activeGamma active f f))) :=
    RatPolyCoeffEqv.haarCarrier
      ((activeCasimirPolynomial_mul active f f).trans
        ((RatPolyCoeffEqv.refl _).add (cap_mul_left (-2) _).symm))
  have hpins : HaarCarrierEqv (N width)
      (polyAdd
        (polyAdd (polyMul (activeCasimirPolynomial active f) f)
          (polyMul f (activeCasimirPolynomial active f)))
        (polyMul (cap (-2)) (activeGamma active f f)))
      (polyAdd
        (polyAdd (polyMul (polyMul (cap 12) f) f)
          (polyMul f (polyMul (cap 12) f)))
        (polyMul (cap (-2)) (polyMul (cap 4) gap))) :=
    HaarCarrierEqv.add
      (HaarCarrierEqv.add
        (HaarCarrierEqv.mul hCf (HaarCarrierEqv.refl _ f))
        (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ f) hCf))
      (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ (cap (-2))) hG)
  have hring : RatPolyCoeffEqv
      (polyAdd
        (polyAdd (polyMul (polyMul (cap 12) f) f)
          (polyMul f (polyMul (cap 12) f)))
        (polyMul (cap (-2)) (polyMul (cap 4) gap)))
      (polyMul (cap 32)
        (polyAdd (polyMul f f) (polyNeg (cap 1)))) := by
    change RatPolyCoeffEqv
      (polyAdd
        (polyAdd (polyMul (polyMul (cap 12) f) f)
          (polyMul f (polyMul (cap 12) f)))
        (polyMul (cap (-2))
          (polyMul (cap 4) (polyAdd (cap 4) (polyNeg (polyMul f f)))))) _
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add
          (.mul (.mul (.const 12) (.var 0)) (.var 0))
          (.mul (.var 0) (.mul (.const 12) (.var 0))))
        (.mul (.const (-2))
          (.mul (.const 4)
            (.add (.const 4) (.neg (.mul (.var 0) (.var 0)))))))
      (.mul (.const 32)
        (.add (.mul (.var 0) (.var 0)) (.neg (.const 1))))
      (by decide) (fun _ => f)
  have hunit : RatPolyCoeffEqv (cap 1) polyOne :=
    RatPolyCoeffEqv.one_smul polyOne
  have htarget : RatPolyCoeffEqv
      (polyMul (cap 32)
        (polyAdd (polyMul f f) (polyNeg (cap 1))))
      (polySmul 32 target) :=
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hunit)).mul_left
      (cap 32)).trans (cap_mul_left 32 target)
  exact hprod.trans (hpins.trans
    (RatPolyCoeffEqv.haarCarrier (hring.trans htarget)))

private theorem casimir_cap_zero : ∀ (active : List Nat) (c : Q'),
    RatPolyCoeffEqv (activeCasimirPolynomial active (cap c)) polyZero
  | [], _ => RatPolyCoeffEqv.refl polyZero
  | i::rest, c => by
      change RatPolyCoeffEqv
        (polyAdd (polyNeg (blockAngularLaplacian i (cap c)))
          (activeCasimirPolynomial rest (cap c))) polyZero
      exact ((RatPolyCoeffEqv.neg
        (blockAngularLaplacian_independent_zero i (cap c)
          (quaternionBlockIndependent_polySmul c
            (quaternionBlockIndependent_polyOne i)))).add
        (casimir_cap_zero rest c)).trans
        (RatPolyCoeffEqv.add_zero polyZero)

private theorem casimir_neg_carrier (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (p : RatPoly) :
    HaarCarrierEqv n (activeCasimirPolynomial active (polyNeg p))
      (polyNeg (activeCasimirPolynomial active p)) := by
  exact (activeCasimirPolynomial_carrier active hactive
    (RatPolyCoeffEqv.haarCarrier (neg_smul p))).trans
      ((RatPolyCoeffEqv.haarCarrier (activeCasimir_smul active (-1) p)).trans
        (RatPolyCoeffEqv.haarCarrier
          (neg_smul (activeCasimirPolynomial active p)).symm))

/-- Applying the original full-carrier Casimir to the physical angular
curvature leaves a signed spin-two mode. No sign for its insertion is claimed. -/
theorem plaquette_gamma_casimir (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    let f := characterPolynomial (plaquette width face).scalar 1
    HaarCarrierEqv (N width)
      (activeCasimirPolynomial (List.range (N width))
        (activeGamma (List.range (N width)) f f))
      (polySmul (-128) (polyAdd (polyMul f f) (polyNeg polyOne))) := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  let active := List.range (N width)
  let square := polyMul f f
  let gap := polyAdd (cap 4) (polyNeg square)
  let target := polyAdd square (polyNeg polyOne)
  have hactive : ∀ i, i ∈ active → i < N width :=
    fun i hi => List.mem_range.mp hi
  have hG := plaquette_gamma width face hf
  have hC : HaarCarrierEqv (N width)
      (activeCasimirPolynomial active (activeGamma active f f))
      (activeCasimirPolynomial active (polySmul 4 gap)) :=
    activeCasimirPolynomial_carrier active hactive hG
  have hgap : HaarCarrierEqv (N width)
      (activeCasimirPolynomial active gap)
      (polyNeg (activeCasimirPolynomial active square)) := by
    exact (RatPolyCoeffEqv.haarCarrier
      (activeCasimir_add active (cap 4) (polyNeg square))).trans
        ((HaarCarrierEqv.add
          (RatPolyCoeffEqv.haarCarrier (casimir_cap_zero active 4))
          (casimir_neg_carrier (N width) active hactive square)).trans
            (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_add _)))
  have hlinear : HaarCarrierEqv (N width)
      (activeCasimirPolynomial active (polySmul 4 gap))
      (polySmul 4 (polyNeg (activeCasimirPolynomial active square))) :=
    (RatPolyCoeffEqv.haarCarrier (activeCasimir_smul active 4 gap)).trans
      (HaarCarrierEqv.smul 4 hgap)
  have hmode : HaarCarrierEqv (N width)
      (polySmul 4 (polyNeg (activeCasimirPolynomial active square)))
      (polySmul 4 (polyNeg (polySmul 32 target))) :=
    HaarCarrierEqv.smul 4
      (HaarCarrierEqv.neg (plaquette_square_casimir width face hf))
  have hscalar : RatPolyCoeffEqv
      (polySmul 4 (polyNeg (polySmul 32 target)))
      (polySmul (-128) target) := by
    refine ((neg_smul (polySmul 32 target)).smul 4).trans ?_
    refine (RatPolyCoeffEqv.smul_assoc 4 (-1) (polySmul 32 target)).trans ?_
    refine ((RatPolyCoeffEqv.smul_coefficient (by decide : (4 : Q') * (-1) ≈ -4)
      (polySmul 32 target))).trans ?_
    refine (RatPolyCoeffEqv.smul_assoc (-4) 32 target).trans ?_
    exact RatPolyCoeffEqv.smul_coefficient
      (by decide : ((-4 : Q') * 32) ≈ -128) target
  exact hC.trans (hlinear.trans (hmode.trans
    (RatPolyCoeffEqv.haarCarrier hscalar)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature.plaquette_gamma
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature.plaquette_square_casimir
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature.plaquette_gamma_casimir
