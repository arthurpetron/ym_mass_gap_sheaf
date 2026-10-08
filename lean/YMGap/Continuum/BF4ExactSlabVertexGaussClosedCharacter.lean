/-
# Actual closed Wilson characters killed by the original vertex Gauss sum

Raw scalar and quaternion Leibniz rules act on the ORIGINAL finite
polynomials. Only after forming those derivatives do we substitute the
checked common-padded physical-link endpoint laws. Compatibility cancels
the internal endpoints of the literal ordered word, including every
repeated and reversed occurrence. Closed scalar trace cyclicity and the
literal character recurrence then give zero at every spin.

No sphere/unit premise, symbolic tangent replacement, differentiated padded
equivalence, continuum gauge domain, signed-response bound or gap is used.
-/

import YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord

namespace YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionLeftRightAngularAction
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.QuaternionHaarAngularCarrier

local notation:max "SlabB" extent:arg => List.length (boundaryCompleteSlabLinks extent)
attribute [local irreducible] boundaryCompleteSlabLinks

private def choose (c : Prop) [Decidable c] (p : RatPoly) := if c then p else polyZero

private theorem choose_congr (c : Prop) [Decidable c] {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : RatPolyCoeffEqv (choose c p) (choose c q) := by
  unfold choose; split
  · exact h
  · exact .refl _

private theorem choose_zero (c : Prop) [Decidable c] :
    RatPolyCoeffEqv (choose c polyZero) polyZero := by
  unfold choose; split <;> exact .refl _

private theorem choose_add (c : Prop) [Decidable c] (p q : RatPoly) :
    RatPolyCoeffEqv (choose c (polyAdd p q)) (polyAdd (choose c p) (choose c q)) := by
  unfold choose; split <;> exact .refl _

private theorem choose_neg (c : Prop) [Decidable c] (p : RatPoly) :
    RatPolyCoeffEqv (choose c (polyNeg p)) (polyNeg (choose c p)) := by
  unfold choose; split <;> exact .refl _

private theorem choose_smul (c : Prop) [Decidable c] (a : Q') (p : RatPoly) :
    RatPolyCoeffEqv (choose c (polySmul a p)) (polySmul a (choose c p)) := by
  unfold choose; split <;> exact .refl _

private theorem choose_leibniz (c : Prop) [Decidable c] (p q dp dq : RatPoly) :
    RatPolyCoeffEqv (choose c (polyAdd (polyMul dp q) (polyMul p dq)))
      (polyAdd (polyMul (choose c dp) q) (polyMul p (choose c dq))) := by
  unfold choose; split
  · exact .refl _
  · exact ((RatPolyCoeffEqv.mul_zero_left q).add (RatPolyCoeffEqv.mul_zero_right p)).symm

private theorem neg_add (p q : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polyAdd p q)) (polyAdd (polyNeg p) (polyNeg q)) :=
  coeffEvalExpr_eqv_of_normalize_eq (.neg (.add (.var 0) (.var 1)))
    (.add (.neg (.var 0)) (.neg (.var 1))) (by decide) (fun | 0 => p | _ => q)

private theorem neg_smul_comm (a : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul a p)) (polySmul a (polyNeg p)) :=
  ((neg_smul _).trans (RatPolyCoeffEqv.smul_assoc (-1) a p)).trans
    ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (-1) a) p).trans
      (((neg_smul p).smul a).trans (RatPolyCoeffEqv.smul_assoc a (-1) p)).symm)

private theorem neg_leibniz (p q dp dq : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polyAdd (polyMul dp q) (polyMul p dq)))
      (polyAdd (polyMul (polyNeg dp) q) (polyMul p (polyNeg dq))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.neg (.add (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3))))
    (.add (.mul (.neg (.var 2)) (.var 1)) (.mul (.var 0) (.neg (.var 3))))
    (by decide) (fun | 0 => p | 1 => q | 2 => dp | _ => dq)

private theorem merge_leibniz (p q a b c d : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul a q) (polyMul p b))
        (polyAdd (polyMul c q) (polyMul p d)))
      (polyAdd (polyMul (polyAdd a c) q) (polyMul p (polyAdd b d))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3)))
      (.add (.mul (.var 4) (.var 1)) (.mul (.var 0) (.var 5))))
    (.add (.mul (.add (.var 2) (.var 4)) (.var 1))
      (.mul (.var 0) (.add (.var 3) (.var 5))))
    (by decide) (fun | 0 => p | 1 => q | 2 => a | 3 => b | 4 => c | _ => d)

private theorem link_add (extent : Nat) (v : Z4Vertex) (i : Fin 3) (link : Z4Link)
    (p q : RatPoly) : RatPolyCoeffEqv (linkGauss extent v i link (polyAdd p q))
      (polyAdd (linkGauss extent v i link p) (linkGauss extent v i link q)) := by
  let b := (boundaryCompleteSlabLinks extent).idxOf link
  have hL := (choose_congr (v=link.1)
    ((RatPolyCoeffEqv.neg (frameDerivativeAt_add false b i p q)).trans (neg_add _ _))).trans
    (choose_add _ _ _)
  have hR := (choose_congr (v=addE link.1 link.2)
    (frameDerivativeAt_add true b i p q)).trans (choose_add _ _ _)
  exact (hL.add hR).trans (RatPolyCoeffEqv.four_add_swap _ _ _ _)

private theorem link_neg (extent : Nat) (v : Z4Vertex) (i : Fin 3) (link : Z4Link)
    (p : RatPoly) : RatPolyCoeffEqv (linkGauss extent v i link (polyNeg p))
      (polyNeg (linkGauss extent v i link p)) := by
  let b := (boundaryCompleteSlabLinks extent).idxOf link
  have hL := (choose_congr (v=link.1) (RatPolyCoeffEqv.neg (frameDerivativeAt_neg false b i p))).trans
    (choose_neg _ _)
  have hR := (choose_congr (v=addE link.1 link.2) (frameDerivativeAt_neg true b i p)).trans
    (choose_neg _ _)
  exact (hL.add hR).trans (neg_add _ _).symm

private theorem link_smul (extent : Nat) (v : Z4Vertex) (i : Fin 3) (link : Z4Link)
    (a : Q') (p : RatPoly) : RatPolyCoeffEqv (linkGauss extent v i link (polySmul a p))
      (polySmul a (linkGauss extent v i link p)) := by
  let b := (boundaryCompleteSlabLinks extent).idxOf link
  have hL := (choose_congr (v=link.1)
    ((RatPolyCoeffEqv.neg (frameDerivativeAt_smul false b i a p)).trans (neg_smul_comm a _))).trans
    (choose_smul _ a _)
  have hR := (choose_congr (v=addE link.1 link.2) (frameDerivativeAt_smul true b i a p)).trans
    (choose_smul _ a _)
  exact (hL.add hR).trans (RatPolyCoeffEqv.smul_add a _ _).symm

private theorem link_mul (extent : Nat) (v : Z4Vertex) (i : Fin 3) (link : Z4Link)
    (p q : RatPoly) : RatPolyCoeffEqv (linkGauss extent v i link (polyMul p q))
      (polyAdd (polyMul (linkGauss extent v i link p) q)
        (polyMul p (linkGauss extent v i link q))) := by
  let b := (boundaryCompleteSlabLinks extent).idxOf link
  have hL := (choose_congr (v=link.1)
    ((RatPolyCoeffEqv.neg (frameDerivativeAt_mul false b i p q)).trans (neg_leibniz p q _ _))).trans
    (choose_leibniz _ p q _ _)
  have hR := (choose_congr (v=addE link.1 link.2) (frameDerivativeAt_mul true b i p q)).trans
    (choose_leibniz _ p q _ _)
  exact (hL.add hR).trans (merge_leibniz p q _ _ _ _)

private theorem link_constant (extent : Nat) (v : Z4Vertex) (i : Fin 3) (link : Z4Link)
    (p : RatPoly) (hL : RatPolyCoeffEqv
      (frameDerivativeAt false ((boundaryCompleteSlabLinks extent).idxOf link) i p) polyZero)
    (hR : RatPolyCoeffEqv
      (frameDerivativeAt true ((boundaryCompleteSlabLinks extent).idxOf link) i p) polyZero) :
    RatPolyCoeffEqv (linkGauss extent v i link p) polyZero :=
  ((choose_congr (v=link.1) (RatPolyCoeffEqv.neg hL)).trans (choose_zero _)).add
    ((choose_congr (v=addE link.1 link.2) hR).trans (choose_zero _))

private theorem sum_congr (f g : Z4Link → RatPoly) : ∀ links : List Z4Link,
    (∀ link, link ∈ links → RatPolyCoeffEqv (f link) (g link)) →
    RatPolyCoeffEqv (finitePolySum f links) (finitePolySum g links)
  | [], _ => .refl _
  | link :: links, h => (h link List.mem_cons_self).add
      (sum_congr f g links (fun e he => h e (List.mem_cons_of_mem link he)))

private theorem sum_add (f g : Z4Link → RatPoly) : ∀ links : List Z4Link,
    RatPolyCoeffEqv (finitePolySum (fun e => polyAdd (f e) (g e)) links)
      (polyAdd (finitePolySum f links) (finitePolySum g links))
  | [] => .refl _
  | _ :: links => ((RatPolyCoeffEqv.refl _).add (sum_add f g links)).trans
      (RatPolyCoeffEqv.four_add_swap _ _ _ _)

private theorem sum_neg (f : Z4Link → RatPoly) : ∀ links : List Z4Link,
    RatPolyCoeffEqv (finitePolySum (fun e => polyNeg (f e)) links) (polyNeg (finitePolySum f links))
  | [] => .refl _
  | _ :: links => ((RatPolyCoeffEqv.refl _).add (sum_neg f links)).trans (neg_add _ _).symm

private theorem sum_smul (a : Q') (f : Z4Link → RatPoly) : ∀ links : List Z4Link,
    RatPolyCoeffEqv (finitePolySum (fun e => polySmul a (f e)) links)
      (polySmul a (finitePolySum f links))
  | [] => .refl _
  | _ :: links => ((RatPolyCoeffEqv.refl _).add (sum_smul a f links)).trans
      (RatPolyCoeffEqv.smul_add a _ _).symm

private theorem sum_mul_right (f : Z4Link → RatPoly) (p : RatPoly) : ∀ links : List Z4Link,
    RatPolyCoeffEqv (finitePolySum (fun e => polyMul (f e) p) links) (polyMul (finitePolySum f links) p)
  | [] => .refl _
  | _ :: links => by
      change RatPolyCoeffEqv (polyAdd _ _) (polyMul (polyAdd _ _) p)
      rw [polyMul_add_left_exact]
      exact (RatPolyCoeffEqv.refl _).add (sum_mul_right f p links)

private theorem sum_mul_left (p : RatPoly) (f : Z4Link → RatPoly) : ∀ links : List Z4Link,
    RatPolyCoeffEqv (finitePolySum (fun e => polyMul p (f e)) links) (polyMul p (finitePolySum f links))
  | [] => (RatPolyCoeffEqv.mul_zero_right p).symm
  | _ :: links => ((RatPolyCoeffEqv.refl _).add (sum_mul_left p f links)).trans
      (RatPolyCoeffEqv.mul_add_right p _ _).symm

private theorem sum_zero (f : Z4Link → RatPoly) : ∀ links : List Z4Link,
    (∀ link, link ∈ links → RatPolyCoeffEqv (f link) polyZero) →
    RatPolyCoeffEqv (finitePolySum f links) polyZero
  | [], _ => .refl _
  | link :: links, h => (h link List.mem_cons_self).add
      (sum_zero f links (fun e he => h e (List.mem_cons_of_mem link he)))

/-- Raw linearity of the ACTUAL finite generator. -/
theorem vertexGauss_add (extent : Nat) (v : Z4Vertex) (i : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv (vertexGauss extent v i (polyAdd p q))
      (polyAdd (vertexGauss extent v i p) (vertexGauss extent v i q)) :=
  (sum_congr _ _ _ (fun link _ => link_add extent v i link p q)).trans (sum_add _ _ _)

theorem vertexGauss_neg (extent : Nat) (v : Z4Vertex) (i : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (vertexGauss extent v i (polyNeg p)) (polyNeg (vertexGauss extent v i p)) :=
  (sum_congr _ _ _ (fun link _ => link_neg extent v i link p)).trans (sum_neg _ _)

theorem vertexGauss_smul (extent : Nat) (v : Z4Vertex) (i : Fin 3) (a : Q') (p : RatPoly) :
    RatPolyCoeffEqv (vertexGauss extent v i (polySmul a p))
      (polySmul a (vertexGauss extent v i p)) :=
  (sum_congr _ _ _ (fun link _ => link_smul extent v i link a p)).trans (sum_smul _ _ _)

/-- Raw Leibniz, before any coefficient padding. -/
theorem vertexGauss_mul (extent : Nat) (v : Z4Vertex) (i : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv (vertexGauss extent v i (polyMul p q))
      (polyAdd (polyMul (vertexGauss extent v i p) q) (polyMul p (vertexGauss extent v i q))) :=
  (sum_congr _ _ _ (fun link _ => link_mul extent v i link p q)).trans
    ((sum_add _ _ _).trans ((sum_mul_right _ _ _).add (sum_mul_left _ _ _)))

theorem vertexGauss_zero (extent : Nat) (v : Z4Vertex) (i : Fin 3) :
    RatPolyCoeffEqv (vertexGauss extent v i polyZero) polyZero :=
  sum_zero _ _ (fun link _ => link_constant extent v i link polyZero
    (frameDerivativeAt_zero false _ i) (frameDerivativeAt_zero true _ i))

theorem vertexGauss_one (extent : Nat) (v : Z4Vertex) (i : Fin 3) :
    RatPolyCoeffEqv (vertexGauss extent v i polyOne) polyZero :=
  sum_zero _ _ (fun link _ => link_constant extent v i link polyOne
    (frameDerivativeAt_one false _ i) (frameDerivativeAt_one true _ i))

attribute [local irreducible] vertexGauss

private def qAdd (p q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyAdd p.scalar q.scalar, polyAdd p.iPart q.iPart,
    polyAdd p.jPart q.jPart, polyAdd p.kPart q.kPart⟩

private def four (negative : Bool) (a b c d : RatPoly) : RatPoly :=
  if negative then polyAdd a (polyNeg (polyAdd b (polyAdd c d)))
  else polyAdd a (polyAdd b (polyAdd c (polyNeg d)))

private theorem four_congr (negative : Bool) {a a' b b' c c' d d' : RatPoly}
    (ha : RatPolyCoeffEqv a a') (hb : RatPolyCoeffEqv b b')
    (hc : RatPolyCoeffEqv c c') (hd : RatPolyCoeffEqv d d') :
    RatPolyCoeffEqv (four negative a b c d) (four negative a' b' c' d') := by
  cases negative
  · exact ha.add (hb.add (hc.add (RatPolyCoeffEqv.neg hd)))
  · exact ha.add (RatPolyCoeffEqv.neg (hb.add (hc.add hd)))

private theorem gauss_four (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (negative : Bool) (a b c d : RatPoly) :
    RatPolyCoeffEqv (vertexGauss extent v i (four negative a b c d))
      (four negative (vertexGauss extent v i a) (vertexGauss extent v i b)
        (vertexGauss extent v i c) (vertexGauss extent v i d)) := by
  cases negative
  · exact (vertexGauss_add extent v i a _).trans
      ((RatPolyCoeffEqv.refl _).add ((vertexGauss_add extent v i b _).trans
        ((RatPolyCoeffEqv.refl _).add ((vertexGauss_add extent v i c _).trans
          ((RatPolyCoeffEqv.refl _).add (vertexGauss_neg extent v i d))))))
  · exact (vertexGauss_add extent v i a _).trans
      ((RatPolyCoeffEqv.refl _).add ((vertexGauss_neg extent v i _).trans
        (RatPolyCoeffEqv.neg ((vertexGauss_add extent v i b _).trans
          ((RatPolyCoeffEqv.refl _).add (vertexGauss_add extent v i c d))))))

private theorem gauss_four_products (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (negative : Bool) (a b c d e f g h : RatPoly) :
    RatPolyCoeffEqv (vertexGauss extent v i
      (four negative (polyMul a b) (polyMul c d) (polyMul e f) (polyMul g h)))
      (four negative
        (polyAdd (polyMul (vertexGauss extent v i a) b) (polyMul a (vertexGauss extent v i b)))
        (polyAdd (polyMul (vertexGauss extent v i c) d) (polyMul c (vertexGauss extent v i d)))
        (polyAdd (polyMul (vertexGauss extent v i e) f) (polyMul e (vertexGauss extent v i f)))
        (polyAdd (polyMul (vertexGauss extent v i g) h) (polyMul g (vertexGauss extent v i h)))) :=
  (gauss_four extent v i negative _ _ _ _).trans
    (four_congr negative (vertexGauss_mul extent v i a b) (vertexGauss_mul extent v i c d)
      (vertexGauss_mul extent v i e f) (vertexGauss_mul extent v i g h))

private def exprAdd (p q : PolyQuaternionExpr) : PolyQuaternionExpr :=
  ⟨.add p.scalar q.scalar, .add p.iPart q.iPart, .add p.jPart q.jPart, .add p.kPart q.kPart⟩

private def exprNeg (p : PolyQuaternionExpr) : PolyQuaternionExpr :=
  ⟨.neg p.scalar, .neg p.iPart, .neg p.jPart, .neg p.kPart⟩

private def evalQ (env : Nat → RatPoly) (q : PolyQuaternionExpr) : PolyQuaternion :=
  ⟨coeffEvalExpr env q.scalar, coeffEvalExpr env q.iPart,
    coeffEvalExpr env q.jPart, coeffEvalExpr env q.kPart⟩

private def qenv (p q r s : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
  | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | 7 => q.kPart
  | 8 => r.scalar | 9 => r.iPart | 10 => r.jPart | 11 => r.kPart
  | 12 => s.scalar | 13 => s.iPart | 14 => s.jPart | 15 => s.kPart
  | _ => polyZero

private def jet (a b da db : PolyExpr) : PolyExpr := .add (.mul da b) (.mul a db)

private def jetProduct : PolyQuaternionExpr :=
  ⟨.add (jet (.var 0) (.var 4) (.var 8) (.var 12))
      (.neg (.add (jet (.var 1) (.var 5) (.var 9) (.var 13))
        (.add (jet (.var 2) (.var 6) (.var 10) (.var 14)) (jet (.var 3) (.var 7) (.var 11) (.var 15))))),
    .add (jet (.var 0) (.var 5) (.var 8) (.var 13))
      (.add (jet (.var 1) (.var 4) (.var 9) (.var 12))
        (.add (jet (.var 2) (.var 7) (.var 10) (.var 15)) (.neg (jet (.var 3) (.var 6) (.var 11) (.var 14))))),
    .add (jet (.var 0) (.var 6) (.var 8) (.var 14))
      (.add (jet (.var 2) (.var 4) (.var 10) (.var 12))
        (.add (jet (.var 3) (.var 5) (.var 11) (.var 13)) (.neg (jet (.var 1) (.var 7) (.var 9) (.var 15))))),
    .add (jet (.var 0) (.var 7) (.var 8) (.var 15))
      (.add (jet (.var 3) (.var 4) (.var 11) (.var 12))
        (.add (jet (.var 1) (.var 6) (.var 9) (.var 14)) (.neg (jet (.var 2) (.var 5) (.var 10) (.var 13)))))⟩

private def productRule : PolyQuaternionExpr :=
  exprAdd (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 8) (PolyQuaternionExpr.coordinate 4))
    (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 12))

/-- Raw quaternion Leibniz obtained from the actual scalar derivatives,
not from a supplied symbolic tangent or a differentiated padded identity. -/
theorem vertexGaussQuaternion_mul (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (vertexGaussQuaternion extent v i (PolyQuaternion.mul p q))
      (qAdd (PolyQuaternion.mul (vertexGaussQuaternion extent v i p) q)
        (PolyQuaternion.mul p (vertexGaussQuaternion extent v i q))) := by
  let env := qenv p q (vertexGaussQuaternion extent v i p) (vertexGaussQuaternion extent v i q)
  have h : PolyQuaternionCoeffEqv (vertexGaussQuaternion extent v i (PolyQuaternion.mul p q))
      (evalQ env jetProduct) :=
    ⟨gauss_four_products extent v i true p.scalar q.scalar p.iPart q.iPart p.jPart q.jPart p.kPart q.kPart,
      gauss_four_products extent v i false p.scalar q.iPart p.iPart q.scalar p.jPart q.kPart p.kPart q.jPart,
      gauss_four_products extent v i false p.scalar q.jPart p.jPart q.scalar p.kPart q.iPart p.iPart q.kPart,
      gauss_four_products extent v i false p.scalar q.kPart p.kPart q.scalar p.iPart q.jPart p.jPart q.iPart⟩
  apply h.trans
  exact ⟨coeffEvalExpr_eqv_of_normalize_eq jetProduct.scalar productRule.scalar (by decide) env,
    coeffEvalExpr_eqv_of_normalize_eq jetProduct.iPart productRule.iPart (by decide) env,
    coeffEvalExpr_eqv_of_normalize_eq jetProduct.jPart productRule.jPart (by decide) env,
    coeffEvalExpr_eqv_of_normalize_eq jetProduct.kPart productRule.kPart (by decide) env⟩

private theorem qReflect (p q : PolyQuaternionExpr) (env : Nat → RatPoly)
    (h : normalize p.scalar = normalize q.scalar ∧ normalize p.iPart = normalize q.iPart ∧
      normalize p.jPart = normalize q.jPart ∧ normalize p.kPart = normalize q.kPart) :
    PolyQuaternionCoeffEqv (evalQ env p) (evalQ env q) :=
  ⟨coeffEvalExpr_eqv_of_normalize_eq _ _ h.1 env,
    coeffEvalExpr_eqv_of_normalize_eq _ _ h.2.1 env,
    coeffEvalExpr_eqv_of_normalize_eq _ _ h.2.2.1 env,
    coeffEvalExpr_eqv_of_normalize_eq _ _ h.2.2.2 env⟩

private theorem qAdd_congr {p p' q q' : PolyQuaternion}
    (hp : PolyQuaternionCoeffEqv p p') (hq : PolyQuaternionCoeffEqv q q') :
    PolyQuaternionCoeffEqv (qAdd p q) (qAdd p' q') :=
  ⟨hp.scalar.add hq.scalar, hp.iPart.add hq.iPart, hp.jPart.add hq.jPart, hp.kPart.add hq.kPart⟩

private theorem qNeg_congr {p q : PolyQuaternion} (h : PolyQuaternionCoeffEqv p q) :
    PolyQuaternionCoeffEqv (negQuaternion p) (negQuaternion q) :=
  ⟨RatPolyCoeffEqv.neg h.scalar, RatPolyCoeffEqv.neg h.iPart,
    RatPolyCoeffEqv.neg h.jPart, RatPolyCoeffEqv.neg h.kPart⟩

private theorem padded_qAdd {B : Nat} {p p' q q' : PolyQuaternion}
    (hp : PaddedQuaternionCoeffEqv B p p') (hq : PaddedQuaternionCoeffEqv B q q') :
    PaddedQuaternionCoeffEqv B (qAdd p q) (qAdd p' q') :=
  ⟨PaddedPolynomialCoeffEqv.add hp.scalar hq.scalar, PaddedPolynomialCoeffEqv.add hp.iPart hq.iPart,
    PaddedPolynomialCoeffEqv.add hp.jPart hq.jPart, PaddedPolynomialCoeffEqv.add hp.kPart hq.kPart⟩

private theorem q_mul_add_left (p q r : PolyQuaternion) :
    PolyQuaternionCoeffEqv (PolyQuaternion.mul (qAdd p q) r)
      (qAdd (PolyQuaternion.mul p r) (PolyQuaternion.mul q r)) :=
  qReflect (PolyQuaternionExpr.mul
    (exprAdd (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4)) (PolyQuaternionExpr.coordinate 8))
    (exprAdd (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 8))
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 4) (PolyQuaternionExpr.coordinate 8)))
    (qenv p q r zeroQuaternion) (by decide)

private theorem q_mul_add_right (p q r : PolyQuaternion) :
    PolyQuaternionCoeffEqv (PolyQuaternion.mul p (qAdd q r))
      (qAdd (PolyQuaternion.mul p q) (PolyQuaternion.mul p r)) :=
  qReflect (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0)
    (exprAdd (PolyQuaternionExpr.coordinate 4) (PolyQuaternionExpr.coordinate 8)))
    (exprAdd (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4))
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 8)))
    (qenv p q r zeroQuaternion) (by decide)

private theorem q_mul_neg_left (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (PolyQuaternion.mul (negQuaternion p) q) (negQuaternion (PolyQuaternion.mul p q)) :=
  qReflect (PolyQuaternionExpr.mul (exprNeg (PolyQuaternionExpr.coordinate 0)) (PolyQuaternionExpr.coordinate 4))
    (exprNeg (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4)))
    (qenv p q zeroQuaternion zeroQuaternion) (by decide)

private theorem q_mul_neg_right (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (PolyQuaternion.mul p (negQuaternion q)) (negQuaternion (PolyQuaternion.mul p q)) :=
  qReflect (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (exprNeg (PolyQuaternionExpr.coordinate 4)))
    (exprNeg (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4)))
    (qenv p q zeroQuaternion zeroQuaternion) (by decide)

private theorem q_mul_zero_left (p : PolyQuaternion) :
    PolyQuaternionCoeffEqv (PolyQuaternion.mul zeroQuaternion p) zeroQuaternion := .refl _

private theorem q_mul_zero_right (p : PolyQuaternion) :
    PolyQuaternionCoeffEqv (PolyQuaternion.mul p zeroQuaternion) zeroQuaternion :=
  ⟨four_congr true (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _)
      (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _),
    four_congr false (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _)
      (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _),
    four_congr false (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _)
      (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _),
    four_congr false (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _)
      (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _)⟩

private theorem q_cancel_middle (p c q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (qAdd (qAdd p c) (qAdd (negQuaternion c) q)) (qAdd p q) :=
  qReflect (exprAdd (exprAdd (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4))
    (exprAdd (exprNeg (PolyQuaternionExpr.coordinate 4)) (PolyQuaternionExpr.coordinate 8)))
    (exprAdd (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 8))
    (qenv p c q zeroQuaternion) (by decide)

private theorem scalar_neg_add_zero (p : RatPoly) : RatPolyCoeffEqv (polyAdd (polyNeg p) p) polyZero :=
  (RatPolyCoeffEqv.add_comm _ _).trans
    (((RatPolyCoeffEqv.refl _).add (neg_smul p)).trans (RatPolyCoeffEqv.add_neg_smul p))

private theorem q_neg_add_zero (p : PolyQuaternion) :
    PolyQuaternionCoeffEqv (qAdd (negQuaternion p) p) zeroQuaternion :=
  ⟨scalar_neg_add_zero _, scalar_neg_add_zero _, scalar_neg_add_zero _, scalar_neg_add_zero _⟩

private def qChoose (c : Prop) [Decidable c] (q : PolyQuaternion) := if c then q else zeroQuaternion

private theorem qChoose_congr (c : Prop) [Decidable c] {p q : PolyQuaternion}
    (h : PolyQuaternionCoeffEqv p q) : PolyQuaternionCoeffEqv (qChoose c p) (qChoose c q) := by
  unfold qChoose; split
  · exact h
  · exact .refl _

private theorem qChoose_neg (c : Prop) [Decidable c] (q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (qChoose c (negQuaternion q)) (negQuaternion (qChoose c q)) := by
  unfold qChoose; split <;> exact .refl _

private theorem qChoose_mul_right (c : Prop) [Decidable c] (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (PolyQuaternion.mul (qChoose c p) q) (qChoose c (PolyQuaternion.mul p q)) := by
  unfold qChoose; split
  · exact .refl _
  · exact q_mul_zero_left q

private theorem qChoose_mul_left (c : Prop) [Decidable c] (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (PolyQuaternion.mul p (qChoose c q)) (qChoose c (PolyQuaternion.mul p q)) := by
  unfold qChoose; split
  · exact .refl _
  · exact q_mul_zero_right p

private def pathEndpoint (v : Z4Vertex) (i : Fin 3) (start finish : Z4Vertex)
    (q : PolyQuaternion) : PolyQuaternion :=
  qAdd (qChoose (v=start) (negQuaternion (PolyQuaternion.mul (imaginaryBasis i) q)))
    (qChoose (v=finish) (PolyQuaternion.mul q (imaginaryBasis i)))

private theorem endpoint_product (v : Z4Vertex) (i : Fin 3) (start middle finish : Z4Vertex)
    (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (qAdd (PolyQuaternion.mul (pathEndpoint v i start middle p) q)
        (PolyQuaternion.mul p (pathEndpoint v i middle finish q)))
      (pathEndpoint v i start finish (PolyQuaternion.mul p q)) := by
  let e := imaginaryBasis i
  have hA := (qChoose_mul_right (v=start) _ q).trans
    (qChoose_congr (v=start) ((q_mul_neg_left (PolyQuaternion.mul e p) q).trans
      (qNeg_congr (PolyQuaternionCoeffEqv.mul_assoc e p q))))
  have hC := (qChoose_mul_right (v=middle) _ q).trans
    (qChoose_congr (v=middle) (PolyQuaternionCoeffEqv.mul_assoc p e q))
  have hN := (qChoose_mul_left (v=middle) p _).trans
    ((qChoose_congr (v=middle) (q_mul_neg_right p (PolyQuaternion.mul e q))).trans
      (qChoose_neg (v=middle) _))
  have hB := (qChoose_mul_left (v=finish) p _).trans
    (qChoose_congr (v=finish) (PolyQuaternionCoeffEqv.mul_assoc p q e).symm)
  exact (qAdd_congr (q_mul_add_left _ _ q) (q_mul_add_right p _ _)).trans
    ((qAdd_congr (qAdd_congr hA hC) (qAdd_congr hN hB)).trans (q_cancel_middle _ _ _))

private theorem endpoint_one (v : Z4Vertex) (i : Fin 3) (start : Z4Vertex) :
    PolyQuaternionCoeffEqv (pathEndpoint v i start start PolyQuaternion.one) zeroQuaternion := by
  unfold pathEndpoint qChoose
  split
  · exact (qAdd_congr (qNeg_congr (PolyQuaternionCoeffEqv.mul_one _))
      (PolyQuaternionCoeffEqv.one_mul _)).trans (q_neg_add_zero _)
  · exact .refl _

/-- Actual ordered-word endpoint telescope. Internal occurrences are never
deduplicated; compatibility, not distinctness, supplies cancellation. -/
theorem compatibleWord_gauss_endpoint (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (start : Z4Vertex) : ∀ edges : List OrientedBF4Link,
    Compatible start edges →
    (∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent) →
    PaddedQuaternionCoeffEqv (SlabB extent) (vertexGaussQuaternion extent v i (word extent edges))
      (pathEndpoint v i start (pathFinish start edges) (word extent edges))
  | [], _, _ =>
      .of_coeff ((⟨vertexGauss_one extent v i, vertexGauss_zero extent v i,
        vertexGauss_zero extent v i, vertexGauss_zero extent v i⟩ :
        PolyQuaternionCoeffEqv (vertexGaussQuaternion extent v i PolyQuaternion.one) zeroQuaternion).trans
          (endpoint_one v i start).symm)
  | e :: es, hc, hp => by
      let p := orientedCorrectedSlabLinkPolynomial extent e
      let q := word extent es
      have he : PaddedQuaternionCoeffEqv (SlabB extent) (vertexGaussQuaternion extent v i p)
          (pathEndpoint v i start (entryFinish e) p) := by
        have h := oriented_link_endpoint extent v i e (hp e List.mem_cons_self)
        change PaddedQuaternionCoeffEqv _ _ (pathEndpoint v i (entryStart e) (entryFinish e) p) at h
        rw [hc.1] at h
        exact h
      have ht := compatibleWord_gauss_endpoint extent v i (entryFinish e) es hc.2
        (fun f hf => hp f (List.mem_cons_of_mem e hf))
      exact (PaddedQuaternionCoeffEqv.of_coeff (vertexGaussQuaternion_mul extent v i p q)).trans
        ((padded_qAdd (he.mul (.refl _ q)) ((PaddedQuaternionCoeffEqv.refl _ p).mul ht)).trans
          (.of_coeff (endpoint_product v i start (entryFinish e) (pathFinish (entryFinish e) es) p q)))

/-- Closedness kills the ACTUAL scalar derivative by ordinary scalar trace
cyclicity, at common-padded coefficient strength and without sphere equations. -/
theorem closedScalar_gauss_zero (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (start : Z4Vertex) (edges : List OrientedBF4Link) (hc : Compatible start edges)
    (hclosed : pathFinish start edges = start)
    (hp : ∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent) :
    PaddedPolynomialCoeffEqv (SlabB extent)
      (vertexGauss extent v i (word extent edges).scalar) polyZero := by
  have h := compatibleWord_gauss_endpoint extent v i start edges hc hp
  rw [hclosed] at h
  apply (show PaddedPolynomialCoeffEqv (SlabB extent) _ _ from h.scalar).trans
  unfold pathEndpoint qChoose
  split
  · exact .of_coeff (((RatPolyCoeffEqv.neg
      (polyQuaternion_mul_scalar_cyclic (imaginaryBasis i) (word extent edges))).add
      (RatPolyCoeffEqv.refl _)).trans (scalar_neg_add_zero _))
  · exact .refl _ _

private theorem character_zero {extent : Nat} (v : Z4Vertex) (i : Fin 3) (p : RatPoly)
    (hp : PaddedPolynomialCoeffEqv (SlabB extent) (vertexGauss extent v i p) polyZero) :
    ∀ spin, PaddedPolynomialCoeffEqv (SlabB extent)
      (vertexGauss extent v i (characterPolynomial p spin)) polyZero
  | 0 => .of_coeff (vertexGauss_one extent v i)
  | 1 => (PaddedPolynomialCoeffEqv.of_coeff (vertexGauss_smul extent v i 2 p)).trans
      ((hp.smul 2).trans (.of_coeff (RatPolyCoeffEqv.smul_zero 2)))
  | n+2 => by
      have htwo : PaddedPolynomialCoeffEqv (SlabB extent)
          (vertexGauss extent v i (polySmul 2 p)) polyZero :=
        (PaddedPolynomialCoeffEqv.of_coeff (vertexGauss_smul extent v i 2 p)).trans
        ((hp.smul 2).trans (.of_coeff (RatPolyCoeffEqv.smul_zero 2)))
      have hs := character_zero v i p hp (n+1)
      have hn := character_zero v i p hp n
      have hm : PaddedPolynomialCoeffEqv (SlabB extent)
          (vertexGauss extent v i (polyMul (polySmul 2 p) (characterPolynomial p (n+1)))) polyZero :=
        (PaddedPolynomialCoeffEqv.of_coeff
          (vertexGauss_mul extent v i (polySmul 2 p) (characterPolynomial p (n+1)))).trans
        ((PaddedPolynomialCoeffEqv.add
          (htwo.mul (PaddedPolynomialCoeffEqv.refl (SlabB extent) (characterPolynomial p (n+1))))
          ((PaddedPolynomialCoeffEqv.refl (SlabB extent) (polySmul 2 p)).mul hs)).trans
          (.of_coeff ((RatPolyCoeffEqv.mul_zero_left _).add (RatPolyCoeffEqv.mul_zero_right _))))
      have ht : PaddedPolynomialCoeffEqv (SlabB extent)
          (vertexGauss extent v i (polySmul (-1) (characterPolynomial p n))) polyZero :=
        (PaddedPolynomialCoeffEqv.of_coeff (vertexGauss_smul extent v i (-1) (characterPolynomial p n))).trans
        ((hn.smul (-1)).trans (.of_coeff (RatPolyCoeffEqv.smul_zero (-1))))
      exact (PaddedPolynomialCoeffEqv.of_coeff (vertexGauss_add extent v i _ _)).trans
        (PaddedPolynomialCoeffEqv.add hm ht)

/-- Every spin of the literal original closed physical Wilson word is killed
by the actual all-link vertex Gauss sum. All geometric guards remain explicit. -/
theorem closedCharacter_gauss_zero (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (start : Z4Vertex) (edges : List OrientedBF4Link) (hc : Compatible start edges)
    (hclosed : pathFinish start edges = start)
    (hp : ∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent) (spin : Nat) :
    PaddedPolynomialCoeffEqv (SlabB extent)
      (vertexGauss extent v i (character extent edges spin)) polyZero :=
  character_zero v i _ (closedScalar_gauss_zero extent v i start edges hc hclosed hp) spin

end YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter

#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter.vertexGauss_add
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter.vertexGauss_neg
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter.vertexGauss_smul
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter.vertexGauss_mul
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter.vertexGauss_zero
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter.vertexGauss_one
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter.vertexGaussQuaternion_mul
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter.compatibleWord_gauss_endpoint
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter.closedScalar_gauss_zero
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter.closedCharacter_gauss_zero
