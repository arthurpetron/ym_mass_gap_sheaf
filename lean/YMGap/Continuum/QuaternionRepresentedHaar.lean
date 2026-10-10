/-
ORIGINAL Haar on represented functions on the SAME completed quaternion Point.
DenseData retains actual CReal values, Type-level output rates, a sound bound
and an explicit continuity radius. Presentations are identified by equality
of their ACTUAL completed maps, not by agreement of sampling choices. The
functional descends the constructed original-Haar candidate; sum, signed
rational scaling and completed translations descend their produced inputs.

This is a positive, normalized rational-linear invariant functional on this
represented domain, NOT a representation theorem for every continuous
Point -> RC function. It supplies neither product closure/completeness of a
function algebra nor compact SU(2) realization, full Haar/J04, an interacting
scaling estimate, QFT axioms, a physical mass gap or the Clay theorem.
-/

import YMGap.Continuum.QuaternionDenseCRealPointLinearity
import YMGap.Continuum.QuaternionDenseCRealHaarNormalization
import YMGap.Continuum.QuaternionDenseCRealHaarPositivity
import YMGap.Continuum.QuaternionDenseCRealCompletedHaarTranslation

namespace YMGap.Continuum.QuaternionRepresentedHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.Continuum.QuaternionDenseCRealPointExtension
open YMGap.Continuum.QuaternionDenseCRealPointLinearity
open YMGap.Continuum.QuaternionDenseCRealHaarApproximation
open YMGap.Continuum.QuaternionDenseCRealHaarComparison
open YMGap.Continuum.QuaternionDenseCRealHaarAdditivity
open YMGap.Continuum.QuaternionDenseCRealHaarHomogeneity
open YMGap.Continuum.QuaternionDenseCRealHaarNormalization
open YMGap.Continuum.QuaternionDenseCRealHaarPositivity
open YMGap.Continuum.QuaternionDenseCRealCompletedHaarTranslation

/-- Admissibility DATA, without an integral value or assumed functional law.
The inner rate is Type-valued even though equality of maps will be quotiented. -/
structure DenseData where
  values : UnitNorm → CReal
  inner : ∀ q, InnerRegularity (values q)
  bound : Q'
  radius : Q' → Q'
  radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e
  bounded : ∀ q, leRat (CReal.abs (values q)) bound
  continuity : ∀ e, (0 : Q') < e → ∀ q x,
    distSq q.val x.val ≤ radius e →
      leRat (CReal.abs (CReal.add (values q) (CReal.neg (values x)))) e

namespace DenseData

/-- The existing actual extension, not a freely supplied completed map. -/
def map (D : DenseData) : Point → RC :=
  pointExtension D.values D.inner D.radius D.radius_positive D.continuity

theorem map_embed (D : DenseData) (q : UnitNorm) :
    D.map (embed q) = Quotient.mk crealSetoid (D.values q) :=
  pointExtension_embed D.values D.inner D.radius D.radius_positive D.continuity q

/-- The ACTUAL original-polynomial-Haar candidate for these data. -/
def haar (D : DenseData) : CReal :=
  haarApproximationReal D.values D.inner D.bound D.radius
    D.radius_positive D.bounded D.continuity

/-- Its computed rate remains recoverable for every supplied presentation.
No representative of an abstract function class is selected. -/
def haarInner (D : DenseData) : InnerRegularity D.haar :=
  haarApproximationInnerRegularity D.values D.inner D.bound D.radius
    D.radius_positive D.bounded D.continuity

theorem haar_congr (D E : DenseData) (h : ∀ x, D.map x = E.map x) :
    Equiv D.haar E.haar :=
  haarComparison_completed_maps
    D.values D.inner D.bound D.radius D.radius_positive D.bounded D.continuity
    E.values E.inner E.bound E.radius E.radius_positive E.bounded E.continuity h

/-- Actual sum with all its admissibility data produced. -/
def sum (D E : DenseData) : DenseData where
  values := sumInput D.values E.values
  inner := sumInner D.values D.inner E.values E.inner
  bound := D.bound + E.bound
  radius := sumRadius D.radius E.radius
  radius_positive := sumRadius_positive D.radius E.radius D.radius_positive E.radius_positive
  bounded := sum_bound D.values E.values D.bound E.bound D.bounded E.bounded
  continuity := sum_modulus D.values E.values D.radius E.radius D.continuity E.continuity

theorem sum_map (D E : DenseData) (x : Point) :
    (D.sum E).map x = RCadd (D.map x) (E.map x) :=
  pointExtension_sum D.values E.values D.inner E.inner D.radius E.radius
    D.radius_positive E.radius_positive D.continuity E.continuity x

/-- Signed rational scaling, including c=0, with produced rates and radius. -/
def scale (c : Q') (D : DenseData) : DenseData where
  values := scaleInput c D.values
  inner := scaleInner c D.values D.inner
  bound := Q'.abs c * D.bound
  radius := scaleRadius c D.radius
  radius_positive := scaleRadius_positive c D.radius D.radius_positive
  bounded := scale_bound c D.values D.bound D.bounded
  continuity := scale_modulus c D.values D.radius D.continuity

theorem scale_map (c : Q') (D : DenseData) (x : Point) :
    (D.scale c).map x = RCscale c (D.map x) :=
  pointExtension_scale c D.values D.inner D.radius D.radius_positive D.continuity x

/-- Constants actually inhabit the domain; no admissibility field is assumed. -/
def constant (c : Q') : DenseData where
  values := constantInput c
  inner := constantInner c
  bound := Q'.abs c
  radius := constantRadius
  radius_positive := constantRadius_positive
  bounded := constant_bound c
  continuity := constant_modulus c

theorem constant_map (c : Q') (x : Point) :
    (constant c).map x = Quotient.mk crealSetoid (CReal.ofQ' c) :=
  constantExtension_value c x

/-- Completed translations retain the SAME bound/radius. The multiplier is
a supplied row at this construction stage, not a selected quotient lift. -/
def translate (right : Bool) (G : CauchyPoint) (D : DenseData) : DenseData where
  values := completedInput right G D.values D.inner D.radius D.radius_positive D.continuity
  inner := completedInner right G D.values D.inner D.radius D.radius_positive D.continuity
  bound := D.bound
  radius := D.radius
  radius_positive := D.radius_positive
  bounded := completed_bound right G D.values D.inner D.radius D.radius_positive
    D.continuity D.bound D.bounded
  continuity := completed_modulus right G D.values D.inner D.radius D.radius_positive D.continuity

theorem translate_map (right : Bool) (G : CauchyPoint) (D : DenseData) (x : Point) :
    (D.translate right G).map x =
      D.map (if right then completedMul x (Quotient.mk chordSeminorm.completionSetoid G)
        else completedMul (Quotient.mk chordSeminorm.completionSetoid G) x) :=
  completedExtension_value right G D.values D.inner D.radius D.radius_positive D.continuity x

end DenseData

/-- Equality of ACTUAL maps, not equality of bounds, radii or inner rates. -/
def dataSetoid : Setoid DenseData where
  r D E := ∀ x : Point, D.map x = E.map x
  iseqv := ⟨fun _ _ => rfl, fun h x => (h x).symm,
    fun hDE hEF x => (hDE x).trans (hEF x)⟩

/-- Only represented maps; no all-continuous-functions representation claim. -/
def Represented : Type := Quotient dataSetoid

def classOf (D : DenseData) : Represented := Quotient.mk dataSetoid D

/-- Choice-free faithful evaluation of a represented function class. -/
def evaluate : Represented → Point → RC :=
  Quotient.lift (fun D => D.map) (fun _ _ h => funext h)

theorem evaluate_classOf (D : DenseData) (x : Point) :
    evaluate (classOf D) x = D.map x := rfl

theorem ext (f g : Represented) (h : ∀ x, evaluate f x = evaluate g x) : f = g := by
  revert h
  refine Quotient.inductionOn₂ f g ?_
  intro D E h
  exact Quotient.sound h

/-- Quotient descent of the ACTUAL original-Haar candidates, with no chosen
CReal representative and no invariant/linear/positive law supplied as a field. -/
def integral : Represented → RC :=
  Quotient.lift (fun D => Quotient.mk crealSetoid D.haar)
    (fun D E h => Quotient.sound (D.haar_congr E h))

theorem integral_classOf (D : DenseData) :
    integral (classOf D) = Quotient.mk crealSetoid D.haar := rfl

/-- Both presentation arguments descend through the actual Point-sum pin. -/
def add : Represented → Represented → Represented :=
  Quotient.lift₂ (s₁ := dataSetoid) (s₂ := dataSetoid)
    (fun D E => classOf (D.sum E))
    (fun D E D' E' hD hE => Quotient.sound (by
      intro x
      rw [DenseData.sum_map, DenseData.sum_map, hD x, hE x]))

theorem evaluate_add (f g : Represented) (x : Point) :
    evaluate (add f g) x = RCadd (evaluate f x) (evaluate g x) := by
  refine Quotient.inductionOn₂ f g ?_
  intro D E
  exact D.sum_map E x

theorem integral_add (f g : Represented) :
    integral (add f g) = RCadd (integral f) (integral g) := by
  refine Quotient.inductionOn₂ f g ?_
  intro D E
  exact Quotient.sound (sumHaar_additive
    D.values D.inner D.bound D.radius D.radius_positive D.bounded D.continuity
    E.values E.inner E.bound E.radius E.radius_positive E.bounded E.continuity)

def scale (c : Q') : Represented → Represented :=
  Quotient.lift (fun D => classOf (D.scale c))
    (fun D E h => Quotient.sound (by
      intro x
      rw [DenseData.scale_map, DenseData.scale_map, h x]))

theorem evaluate_scale (c : Q') (f : Represented) (x : Point) :
    evaluate (scale c f) x = RCscale c (evaluate f x) := by
  refine Quotient.inductionOn f ?_
  intro D
  exact DenseData.scale_map c D x

theorem integral_scale (c : Q') (f : Represented) :
    integral (scale c f) = RCscale c (integral f) := by
  refine Quotient.inductionOn f ?_
  intro D
  exact Quotient.sound (scaleHaar_homogeneous c D.values D.inner D.bound
    D.radius D.radius_positive D.bounded D.continuity)

def constant (c : Q') : Represented := classOf (DenseData.constant c)

theorem evaluate_constant (c : Q') (x : Point) :
    evaluate (constant c) x = Quotient.mk crealSetoid (CReal.ofQ' c) :=
  DenseData.constant_map c x

/-- c=1 is unit normalization of this ACTUAL descended functional. -/
theorem integral_constant (c : Q') :
    integral (constant c) = Quotient.mk crealSetoid (CReal.ofQ' c) :=
  constantHaar_quotient_value c

/-- Sound lower order is assumed only of the actual input function, and
preserved by the produced integral. In particular this includes positivity. -/
theorem integral_lower (f : Represented) (c : Q')
    (hlow : ∀ x : Point, RCle (Quotient.mk crealSetoid (CReal.ofQ' c)) (evaluate f x)) :
    RCle (Quotient.mk crealSetoid (CReal.ofQ' c)) (integral f) := by
  revert hlow
  refine Quotient.inductionOn f ?_
  intro D hlow
  apply haarLower_order D.values D.inner D.bound D.radius
    D.radius_positive D.bounded D.continuity c
  intro q
  have h := hlow (embed q)
  change RCle (Quotient.mk crealSetoid (CReal.ofQ' c)) (D.map (embed q)) at h
  rw [DenseData.map_embed] at h
  exact h

theorem integral_nonnegative (f : Represented)
    (hpos : ∀ x : Point, RCnonneg (evaluate f x)) : RCnonneg (integral f) :=
  integral_lower f 0 hpos

private theorem distance_of_order_pair {u v : CReal} {eta : Q'}
    (h1 : leEv u (CReal.add v (CReal.ofQ' eta)))
    (h2 : leEv v (CReal.add u (CReal.ofQ' eta))) :
    leRat (CReal.abs (CReal.add u (CReal.neg v))) eta := by
  intro e he
  obtain ⟨K, hK⟩ := h1 e he
  obtain ⟨L, hL⟩ := h2 e he
  refine ⟨max K L, fun n hn => ?_⟩
  apply abs_sub_le_of_bounds
  · exact Q'.le_trans' _ _ _ (hK n (Nat.le_trans (Nat.le_max_left _ _) hn))
      (Q'.le_of_eqv (Q'.add_assoc_eqv (v.approx n) eta e))
  · exact Q'.le_trans' _ _ _ (hL n (Nat.le_trans (Nat.le_max_right _ _) hn))
      (Q'.le_of_eqv (Q'.add_assoc_eqv (u.approx n) eta e))

/-- Uniform pointwise distance is retained in genuine RC order. This is a
comparison estimate, NOT an assertion that an intrinsic sup norm was built. -/
theorem integral_distance (f g : Represented) (eta : Q')
    (hD : ∀ x : Point,
      RCle (evaluate f x) (RCadd (evaluate g x) (Quotient.mk crealSetoid (CReal.ofQ' eta))) ∧
      RCle (evaluate g x) (RCadd (evaluate f x) (Quotient.mk crealSetoid (CReal.ofQ' eta)))) :
    RCle (integral f) (RCadd (integral g) (Quotient.mk crealSetoid (CReal.ofQ' eta))) ∧
    RCle (integral g) (RCadd (integral f) (Quotient.mk crealSetoid (CReal.ofQ' eta))) := by
  revert hD
  refine Quotient.inductionOn₂ f g ?_
  intro D E hD
  apply haarComparison_order
    D.values D.inner D.bound D.radius D.radius_positive D.bounded D.continuity
    E.values E.inner E.bound E.radius E.radius_positive E.bounded E.continuity eta
  intro q
  have h := hD (embed q)
  change RCle (D.map (embed q))
      (RCadd (E.map (embed q)) (Quotient.mk crealSetoid (CReal.ofQ' eta))) ∧
    RCle (E.map (embed q))
      (RCadd (D.map (embed q)) (Quotient.mk crealSetoid (CReal.ofQ' eta))) at h
  rw [DenseData.map_embed, DenseData.map_embed, RCadd_mk, RCadd_mk] at h
  exact distance_of_order_pair h.1 h.2

/-- BOTH the completed multiplier and function presentation descend. No
representative of either quotient is selected; the same-map pin proves it. -/
def translate (right : Bool) : Point → Represented → Represented :=
  Quotient.lift₂ (s₁ := chordSeminorm.completionSetoid) (s₂ := dataSetoid)
    (fun G D => classOf (D.translate right G))
    (fun G D H E hGH hDE => Quotient.sound (by
      intro x
      rw [DenseData.translate_map, DenseData.translate_map]
      have hg : Quotient.mk chordSeminorm.completionSetoid G =
          Quotient.mk chordSeminorm.completionSetoid H := Quotient.sound hGH
      rw [hg]
      exact hDE _))

theorem evaluate_translate (right : Bool) (g : Point) (f : Represented) (x : Point) :
    evaluate (translate right g f) x =
      evaluate f (if right then completedMul x g else completedMul g x) := by
  refine Quotient.inductionOn₂ g f ?_
  intro G D
  exact D.translate_map right G x

/-- Invariance of the actual descended ORIGINAL Haar functional, for either
order and EVERY completed multiplier, not an assumed invariant field. -/
theorem integral_translate (right : Bool) (g : Point) (f : Represented) :
    integral (translate right g f) = integral f := by
  refine Quotient.inductionOn₂ g f ?_
  intro G D
  exact Quotient.sound (completedHaar_invariant right G D.values D.inner
    D.radius D.radius_positive D.continuity D.bound D.bounded)

#print axioms DenseData.map
#print axioms DenseData.map_embed
#print axioms DenseData.haar
#print axioms DenseData.haarInner
#print axioms DenseData.haar_congr
#print axioms DenseData.sum
#print axioms DenseData.sum_map
#print axioms DenseData.scale
#print axioms DenseData.scale_map
#print axioms DenseData.constant
#print axioms DenseData.constant_map
#print axioms DenseData.translate
#print axioms DenseData.translate_map
#print axioms dataSetoid
#print axioms Represented
#print axioms classOf
#print axioms evaluate
#print axioms evaluate_classOf
#print axioms ext
#print axioms integral
#print axioms integral_classOf
#print axioms add
#print axioms evaluate_add
#print axioms integral_add
#print axioms scale
#print axioms evaluate_scale
#print axioms integral_scale
#print axioms constant
#print axioms evaluate_constant
#print axioms integral_constant
#print axioms integral_lower
#print axioms integral_nonnegative
#print axioms integral_distance
#print axioms translate
#print axioms evaluate_translate
#print axioms integral_translate

end YMGap.Continuum.QuaternionRepresentedHaar
