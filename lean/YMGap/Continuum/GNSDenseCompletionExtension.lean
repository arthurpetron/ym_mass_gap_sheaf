/-
# Extend a dense nonexpansive map whose values carry Cauchy representatives

The output of a dense map may be a genuinely completed vector rather than
a finite vector. If its representatives are supplied as data, an arbitrary
input Cauchy representative gives a GeneralCompletionCauchy family of those
outputs. Its existing cofinal diagonal constructs the extension.

Null inputs give null outputs by the three-hop quadratic estimate. No
representatives or moduli are selected from propositions or quotient points.
The interface is instantiated by the actual physical cube transfer.
-/

import YMGap.Continuum.RCDistBridge
import YMGap.Continuum.GNSNullModulusRecovery

namespace YMGap.Continuum.GNSDenseCompletionExtension

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSNullModulusRecovery

local infix:50 " ≈ " => Q'.eqv

/-- Read a completed rational distance bound on the ORIGINAL representative
indices, using the supplied QCauchy rate to compare with its QMhat diagonal. -/
theorem distance_eventually_le (D : GNSData) (u v : CauchyGNS D) (bound : Q')
    (h : CReal.RCle
      (D.cinnerCompl (D.cSub (Quotient.mk (cauchySetoid D) u) (Quotient.mk (cauchySetoid D) v))
        (D.cSub (Quotient.mk (cauchySetoid D) u) (Quotient.mk (cauchySetoid D) v)))
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' bound)))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    ∃ N, ∀ n, N ≤ n → D.distSqQ (u.seq n) (v.seq n) ≤ bound + epsilon := by
  let r := fun n => D.distSqQ (u.seq n) (v.seq n)
  let c := D.distSqSeqCauchy u v
  let q := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  change CReal.leEv (CReal.ofQ'CauchySeq r c) (CReal.ofQ' bound) at h
  obtain ⟨N, hN⟩ := h q hq
  refine ⟨max N (c.M q), fun n hn => ?_⟩
  have hnN := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnM := Nat.le_trans (Nat.le_max_right _ _) hn
  have hc := (c.bound q hq n (CReal.QMhat r c n) hnM
    (Nat.le_trans hnM (CReal.self_le_QMhat r c n))).1
  have ht := Q'.le_trans' _ _ _ hc (Q'.add_le_add_right _ _ q (hN n hnN))
  exact Q'.le_trans' _ _ _ ht (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv bound q q) (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon))))

/-- Data required by the completion construction; the physical application
supplies both fields without an analytic or strict-gap hypothesis. -/
structure DenseMap (D : GNSData) where
  toRep : D.V → CauchyGNS D
  nonexpansive : ∀ x y,
    CReal.RCle
      (D.cinnerCompl
        (D.cSub (Quotient.mk (cauchySetoid D) (toRep x)) (Quotient.mk (cauchySetoid D) (toRep y)))
        (D.cSub (Quotient.mk (cauchySetoid D) (toRep x)) (Quotient.mk (cauchySetoid D) (toRep y))))
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' (D.distSqQ x y)))

namespace DenseMap

variable {D : GNSData} (T : DenseMap D)

private theorem image_close {x y : D.V} (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hinput : D.distSqQ x y ≤ HalfPow.half * epsilon) :
    ∃ N, ∀ n, N ≤ n → D.distSqQ ((T.toRep x).seq n) ((T.toRep y).seq n) ≤ epsilon := by
  obtain ⟨N, hN⟩ := distance_eventually_le D (T.toRep x) (T.toRep y) _ (T.nonexpansive x y)
    (HalfPow.half * epsilon) (ExpNeg.half_mul_pos epsilon hepsilon)
  refine ⟨N, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (hN n hn) (Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ hinput) (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))

/-- The original input modulus at epsilon/2 is the outer rate. Every
completed output representative was already supplied by T. -/
def mapOuter (X : CauchyGNS D) : GeneralCompletionCauchy D where
  pt n := T.toRep (X.seq n)
  mod epsilon := X.modulus (HalfPow.half * epsilon)
  cauchy := fun epsilon hepsilon p q hp hq => T.image_close epsilon hepsilon
    (X.isCauchy _ (ExpNeg.half_mul_pos epsilon hepsilon) p q hp hq)

def mapRep (X : CauchyGNS D) : CauchyGNS D := (T.mapOuter X).lim

theorem mapRep_modulus (X : CauchyGNS D) (epsilon : Q') :
    (T.mapRep X).modulus epsilon = gMod epsilon := rfl

private theorem tiny_budget (epsilon : Q') : treeval (nullTolerance epsilon) ≤ epsilon := by
  refine Q'.le_trans' _ _ _ (treeval_le_ten _) (Q'.le_of_eqv ?_)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (by decide : (10 : Q') * Q'.mkPos 1 10 (by decide) ≈ 1)) (Q'.one_mul_eqv _))

/-- Three comparison hops prove descent; their witnesses are used only in
the proof, while the constructed diagonal and its modulus are unchanged. -/
theorem mapRep_null {X Y : CauchyGNS D} (h : CauchyNull D X Y) :
    CauchyNull D (T.mapRep X) (T.mapRep Y) := by
  intro epsilon hepsilon
  let tiny := nullTolerance epsilon
  have htiny : (0 : Q') < tiny := nullTolerance_pos hepsilon
  obtain ⟨PX, hPX⟩ := (T.mapOuter X).converges tiny htiny
  obtain ⟨PY, hPY⟩ := (T.mapOuter Y).converges tiny htiny
  obtain ⟨P0, hP0⟩ := h (HalfPow.half * tiny) (ExpNeg.half_mul_pos tiny htiny)
  let p := max (max PX PY) P0
  obtain ⟨NX, hNX⟩ := hPX p (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  obtain ⟨NY, hNY⟩ := hPY p (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  obtain ⟨NM, hNM⟩ := T.image_close tiny htiny (hP0 p (Nat.le_max_right _ _))
  refine ⟨max (max NX NY) NM, fun n hn => ?_⟩
  have hx := hNX n (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn)
  have hy := hNY n (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn)
  have hm := hNM n (Nat.le_trans (Nat.le_max_right _ _) hn)
  apply Q'.le_trans' _ _ _ (D.quad3 ((T.mapRep X).seq n)
    ((T.toRep (X.seq p)).seq n) ((T.toRep (Y.seq p)).seq n) ((T.mapRep Y).seq n) tiny
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (D.distSqQ_comm _ _)) hx) hm hy)
  exact tiny_budget epsilon

def completionMap : GNSCompletionSpace D → GNSCompletionSpace D :=
  Quotient.lift (fun X => Quotient.mk (cauchySetoid D) (T.mapRep X))
    (fun _ _ h => Quotient.sound (T.mapRep_null h))

theorem completionMap_mk (X : CauchyGNS D) :
    T.completionMap (Quotient.mk (cauchySetoid D) X) =
      Quotient.mk (cauchySetoid D) (T.mapRep X) := rfl

theorem mapRep_const_null (x : D.V) :
    CauchyNull D (T.mapRep (constCauchy D x)) (T.toRep x) := by
  intro epsilon hepsilon
  obtain ⟨P, hP⟩ := (T.mapOuter (constCauchy D x)).converges epsilon hepsilon
  obtain ⟨N, hN⟩ := hP P (Nat.le_refl _)
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (Q'.le_of_eqv (D.distSqQ_comm _ _)) (hN n hn)⟩

/-- The extension agrees with the supplied actual dense output. -/
theorem completionMap_embed (x : D.V) :
    T.completionMap (Quotient.mk (cauchySetoid D) (constCauchy D x)) =
      Quotient.mk (cauchySetoid D) (T.toRep x) := Quotient.sound (T.mapRep_const_null x)

end DenseMap
end YMGap.Continuum.GNSDenseCompletionExtension

#print axioms YMGap.Continuum.GNSDenseCompletionExtension.distance_eventually_le
#print axioms YMGap.Continuum.GNSDenseCompletionExtension.DenseMap.mapOuter
#print axioms YMGap.Continuum.GNSDenseCompletionExtension.DenseMap.mapRep
#print axioms YMGap.Continuum.GNSDenseCompletionExtension.DenseMap.mapRep_modulus
#print axioms YMGap.Continuum.GNSDenseCompletionExtension.DenseMap.mapRep_null
#print axioms YMGap.Continuum.GNSDenseCompletionExtension.DenseMap.completionMap
#print axioms YMGap.Continuum.GNSDenseCompletionExtension.DenseMap.completionMap_mk
#print axioms YMGap.Continuum.GNSDenseCompletionExtension.DenseMap.mapRep_const_null
#print axioms YMGap.Continuum.GNSDenseCompletionExtension.DenseMap.completionMap_embed
