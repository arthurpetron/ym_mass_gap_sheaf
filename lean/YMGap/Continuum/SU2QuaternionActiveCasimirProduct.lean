/-
# Product rule for the literal active angular Casimir

These are coefficient identities on the original quaternion polynomial
carrier.  No heat kernel, source stationarity, or positivity estimate enters.
-/

import YMGap.Continuum.SU2QuaternionChannelCasimirLocality
import YMGap.Continuum.QuaternionHaarAngularLaplacianLinear

namespace YMGap.Continuum.SU2QuaternionActiveCasimirProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality

/-- Mixed angular carré du champ on one original block. -/
def blockGamma (block : Nat) (p q : RatPoly) : RatPoly :=
  six (fun i j => polyMul (blockAngularDerivative block i j p)
    (blockAngularDerivative block i j q))

/-- The mixed angular carré du champ on exactly the listed original blocks. -/
def activeGamma (active : List Nat) (p q : RatPoly) : RatPoly :=
  polySum (active.map fun block => blockGamma block p q)

private theorem six_congr {a b : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 → RatPolyCoeffEqv (a i j) (b i j)) :
    RatPolyCoeffEqv (six a) (six b) := by
  unfold six
  exact (h 0 1 (by decide) (by decide)).add
    ((h 0 2 (by decide) (by decide)).add
      ((h 0 3 (by decide) (by decide)).add
        ((h 1 2 (by decide) (by decide)).add
          ((h 1 3 (by decide) (by decide)).add
            (h 2 3 (by decide) (by decide))))))

private theorem six_mul_right (r : RatPoly) (a : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polyMul (a i j) r))
      (polyMul (six a) r) :=
  (six_congr (fun i j _ _ => RatPolyCoeffEqv.mul_comm (a i j) r)).trans
    ((six_mul_left r a).trans (RatPolyCoeffEqv.mul_comm r (six a)))

private theorem weighted_neg (weight : List Nat → Q') (p : RatPoly) :
    ratWeightedSum weight (polyNeg p) ≈ -(ratWeightedSum weight p) :=
  Q'.eqv_trans _ _ _ (neg_smul p weight)
    (Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (-1) p)
      (poly_identity_of_normal_eq
        (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => ratWeightedSum weight p)))

private theorem secondDerivative_mul (i j : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j (polyMul p q)))
      (polyAdd
        (polyAdd
          (polyMul (angularDerivative i j (angularDerivative i j p)) q)
          (polyMul p (angularDerivative i j (angularDerivative i j q))))
        (polySmul 2
          (polyMul (angularDerivative i j p) (angularDerivative i j q)))) := by
  let dp := angularDerivative i j p
  let dq := angularDerivative i j q
  let ddp := angularDerivative i j dp
  let ddq := angularDerivative i j dq
  have h := (angularDerivative_congr i j (angularDerivative_mul i j p q)).trans
    ((angularDerivative_add i j (polyMul dp q) (polyMul p dq)).trans
      ((angularDerivative_mul i j dp q).add
        (angularDerivative_mul i j p dq)))
  have hring : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul ddp q) (polyMul dp dq))
        (polyAdd (polyMul dp dq) (polyMul p ddq)))
      (polyAdd (polyAdd (polyMul ddp q) (polyMul p ddq))
        (polySmul 2 (polyMul dp dq))) := by
    intro weight
    have ha := ratWeightedSum_add weight (polyAdd (polyMul ddp q) (polyMul dp dq))
      (polyAdd (polyMul dp dq) (polyMul p ddq))
    have hb := ratWeightedSum_add weight (polyMul ddp q) (polyMul dp dq)
    have hc := ratWeightedSum_add weight (polyMul dp dq) (polyMul p ddq)
    have hd := ratWeightedSum_add weight (polyAdd (polyMul ddp q) (polyMul p ddq))
      (polySmul 2 (polyMul dp dq))
    have he := ratWeightedSum_add weight (polyMul ddp q) (polyMul p ddq)
    have hf := ratWeightedSum_smul weight 2 (polyMul dp dq)
    exact Q'.eqv_trans _ _ _ ha
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hb hc)
        (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq
            (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
            (.add (.add (.var 0) (.var 2)) (.mul (.const 2) (.var 1)))
            (by decide)
            (fun | 0 => ratWeightedSum weight (polyMul ddp q)
                 | 1 => ratWeightedSum weight (polyMul dp dq)
                 | _ => ratWeightedSum weight (polyMul p ddq)))
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' he.symm hf.symm) hd.symm)))
  exact h.trans hring

private theorem blockLaplacian_mul (block : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (blockAngularLaplacian block (polyMul p q))
      (polyAdd
        (polyAdd (polyMul (blockAngularLaplacian block p) q)
          (polyMul p (blockAngularLaplacian block q)))
        (polySmul 2 (blockGamma block p q))) := by
  let D := fun i j (r : RatPoly) => blockAngularDerivative block i j r
  let A := fun i j => polyMul (D i j (D i j p)) q
  let B := fun i j => polyMul p (D i j (D i j q))
  let G := fun i j => polyMul (D i j p) (D i j q)
  have hplane : RatPolyCoeffEqv
      (six (fun i j => D i j (D i j (polyMul p q))))
      (six (fun i j => polyAdd (polyAdd (A i j) (B i j))
        (polySmul 2 (G i j)))) :=
    six_congr (fun i j _ _ => secondDerivative_mul (4*block+i) (4*block+j) p q)
  have hsum : RatPolyCoeffEqv
      (six (fun i j => polyAdd (polyAdd (A i j) (B i j))
        (polySmul 2 (G i j))))
      (polyAdd (polyAdd (six A) (six B)) (polySmul 2 (six G))) :=
    (six_add (fun i j => polyAdd (A i j) (B i j))
      (fun i j => polySmul 2 (G i j))).trans
      ((six_add A B).add (six_smul 2 G))
  have hfactor : RatPolyCoeffEqv
      (polyAdd (polyAdd (six A) (six B)) (polySmul 2 (six G)))
      (polyAdd
        (polyAdd (polyMul (blockAngularLaplacian block p) q)
          (polyMul p (blockAngularLaplacian block q)))
        (polySmul 2 (blockGamma block p q))) := by
    have ha := (six_mul_right q (fun i j => D i j (D i j p))).trans
      ((blockAngularLaplacian_eq_six block p).symm.mul_right q)
    have hb := (six_mul_left p (fun i j => D i j (D i j q))).trans
      ((blockAngularLaplacian_eq_six block q).symm.mul_left p)
    exact (ha.add hb).add (RatPolyCoeffEqv.refl _)
  exact (blockAngularLaplacian_eq_six block (polyMul p q)).trans
    (hplane.trans (hsum.trans hfactor))

private theorem blockCasimir_mul (block : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (polyNeg (blockAngularLaplacian block (polyMul p q)))
      (polyAdd
        (polyAdd (polyMul (polyNeg (blockAngularLaplacian block p)) q)
          (polyMul p (polyNeg (blockAngularLaplacian block q))))
        (polySmul (-2) (blockGamma block p q))) := by
  let Lp := blockAngularLaplacian block p
  let Lq := blockAngularLaplacian block q
  let G := blockGamma block p q
  have hring : RatPolyCoeffEqv
      (polyNeg (polyAdd (polyAdd (polyMul Lp q) (polyMul p Lq))
        (polySmul 2 G)))
      (polyAdd (polyAdd (polyMul (polyNeg Lp) q)
        (polyMul p (polyNeg Lq))) (polySmul (-2) G)) := by
    intro weight
    have ha := weighted_neg weight
      (polyAdd (polyAdd (polyMul Lp q) (polyMul p Lq)) (polySmul 2 G))
    have hb := ratWeightedSum_add weight (polyAdd (polyMul Lp q) (polyMul p Lq))
      (polySmul 2 G)
    have hc := ratWeightedSum_add weight (polyMul Lp q) (polyMul p Lq)
    have hd := ratWeightedSum_smul weight 2 G
    have he := ratWeightedSum_add weight
      (polyAdd (polyMul (polyNeg Lp) q) (polyMul p (polyNeg Lq)))
      (polySmul (-2) G)
    have hf := ratWeightedSum_add weight
      (polyMul (polyNeg Lp) q) (polyMul p (polyNeg Lq))
    have hg := ratWeightedSum_smul weight (-2) G
    have hi : ratWeightedSum weight (polyMul (polyNeg Lp) q) ≈
        -(ratWeightedSum weight (polyMul Lp q)) :=
      Q'.eqv_trans _ _ _ ((neg_smul Lp).mul_right q weight)
        (Q'.eqv_trans _ _ _ (RatPolyCoeffEqv.polyMul_smul_left (-1) Lp q weight)
          (Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (-1) (polyMul Lp q))
            (poly_identity_of_normal_eq
              (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
              (by decide) (fun _ => ratWeightedSum weight (polyMul Lp q)))))
    have hj : ratWeightedSum weight (polyMul p (polyNeg Lq)) ≈
        -(ratWeightedSum weight (polyMul p Lq)) :=
      Q'.eqv_trans _ _ _ ((neg_smul Lq).mul_left p weight)
        (Q'.eqv_trans _ _ _ (RatPolyCoeffEqv.polyMul_smul_right (-1) p Lq weight)
          (Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (-1) (polyMul p Lq))
            (poly_identity_of_normal_eq
              (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
              (by decide) (fun _ => ratWeightedSum weight (polyMul p Lq)))))
    exact Q'.eqv_trans _ _ _ ha
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _
        (Q'.eqv_trans _ _ _ hb (Q'.add_eqv_congr' hc hd)))
        (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq
            (.neg (.add (.add (.var 0) (.var 1))
              (.mul (.const 2) (.var 2))))
            (.add (.add (.neg (.var 0)) (.neg (.var 1)))
              (.mul (.const (-2)) (.var 2)))
            (by decide)
            (fun | 0 => ratWeightedSum weight (polyMul Lp q)
                 | 1 => ratWeightedSum weight (polyMul p Lq)
                 | _ => ratWeightedSum weight G))
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (Q'.add_eqv_congr' hi.symm hj.symm) hg.symm)
            (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hf.symm (Q'.eqv_refl _))
              he.symm))))
  exact (RatPolyCoeffEqv.neg (blockLaplacian_mul block p q)).trans hring

/-- Literal active Casimir Leibniz rule, including the complete mixed angular
cross term on every selected original block. -/
theorem activeCasimirPolynomial_mul (active : List Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial active (polyMul p q))
      (polyAdd
        (polyAdd (polyMul (activeCasimirPolynomial active p) q)
          (polyMul p (activeCasimirPolynomial active q)))
        (polySmul (-2) (activeGamma active p q))) := by
  induction active with
  | nil =>
      change RatPolyCoeffEqv polyZero
        (polyAdd (polyAdd (polyMul polyZero q) (polyMul p polyZero))
          (polySmul (-2) polyZero))
      have h := ((RatPolyCoeffEqv.mul_zero_left q).add
        (RatPolyCoeffEqv.mul_zero_right p)).add
        (RatPolyCoeffEqv.smul_zero (-2))
      have hz : RatPolyCoeffEqv
          (polyAdd (polyAdd polyZero polyZero) polyZero) polyZero :=
        ((RatPolyCoeffEqv.add_zero polyZero).add
          (RatPolyCoeffEqv.refl polyZero)).trans
          (RatPolyCoeffEqv.add_zero polyZero)
      exact hz.symm.trans h.symm
  | cons block rest ih =>
      change RatPolyCoeffEqv
        (polyAdd (polyNeg (blockAngularLaplacian block (polyMul p q)))
          (activeCasimirPolynomial rest (polyMul p q))) _
      refine ((blockCasimir_mul block p q).add ih).trans ?_
      let A := polyMul (polyNeg (blockAngularLaplacian block p)) q
      let B := polyMul p (polyNeg (blockAngularLaplacian block q))
      let G := polySmul (-2) (blockGamma block p q)
      let D := polyMul (activeCasimirPolynomial rest p) q
      let E := polyMul p (activeCasimirPolynomial rest q)
      let F := polySmul (-2) (activeGamma rest p q)
      have hshuffle : RatPolyCoeffEqv
          (polyAdd (polyAdd (polyAdd A B) G) (polyAdd (polyAdd D E) F))
          (polyAdd (polyAdd (polyAdd A D) (polyAdd B E)) (polyAdd G F)) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.add (.var 0) (.var 1)) (.var 2))
            (.add (.add (.var 3) (.var 4)) (.var 5)))
          (.add (.add (.add (.var 0) (.var 3))
            (.add (.var 1) (.var 4))) (.add (.var 2) (.var 5)))
          (by decide)
          (fun | 0 => A | 1 => B | 2 => G | 3 => D | 4 => E | _ => F)
      have hA : RatPolyCoeffEqv (polyAdd A D)
          (polyMul (activeCasimirPolynomial (block::rest) p) q) := by
        change RatPolyCoeffEqv (polyAdd A D)
          (polyMul (polyAdd (polyNeg (blockAngularLaplacian block p))
            (activeCasimirPolynomial rest p)) q)
        rw [polyMul_add_left_exact]
        exact RatPolyCoeffEqv.refl _
      have hB : RatPolyCoeffEqv (polyAdd B E)
          (polyMul p (activeCasimirPolynomial (block::rest) q)) := by
        change RatPolyCoeffEqv (polyAdd B E)
          (polyMul p (polyAdd (polyNeg (blockAngularLaplacian block q))
            (activeCasimirPolynomial rest q)))
        exact (RatPolyCoeffEqv.mul_add_right p _ _).symm
      have hG : RatPolyCoeffEqv (polyAdd G F)
          (polySmul (-2) (activeGamma (block::rest) p q)) := by
        change RatPolyCoeffEqv (polyAdd G F)
          (polySmul (-2) (polyAdd (blockGamma block p q)
            (activeGamma rest p q)))
        exact (RatPolyCoeffEqv.smul_add (-2) _ _).symm
      exact hshuffle.trans ((hA.add hB).add hG)

private theorem blockGamma_mul_right (block : Nat) (p q r : RatPoly) :
    RatPolyCoeffEqv (blockGamma block p (polyMul q r))
      (polyAdd (polyMul (blockGamma block p q) r)
        (polyMul q (blockGamma block p r))) := by
  let D := fun i j (s : RatPoly) => blockAngularDerivative block i j s
  let A := fun i j => polyMul (D i j p) (D i j q)
  let B := fun i j => polyMul (D i j p) (D i j r)
  have hplane (i j : Nat) : RatPolyCoeffEqv
      (polyMul (D i j p) (D i j (polyMul q r)))
      (polyAdd (polyMul (A i j) r) (polyMul q (B i j))) := by
    have hd := (angularDerivative_mul (4*block+i) (4*block+j) q r).mul_left
      (D i j p)
    have hm := RatPolyCoeffEqv.mul_add_right (D i j p)
      (polyMul (D i j q) r) (polyMul q (D i j r))
    have hr : RatPolyCoeffEqv
        (polyAdd (polyMul (D i j p) (polyMul (D i j q) r))
          (polyMul (D i j p) (polyMul q (D i j r))))
        (polyAdd (polyMul (A i j) r) (polyMul q (B i j))) :=
      (RatPolyCoeffEqv.mul_assoc (D i j p) (D i j q) r).symm.add
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2)))
          (by decide)
          (fun | 0 => D i j p | 1 => q | _ => D i j r))
    exact hd.trans (hm.trans hr)
  exact (six_congr (fun i j _ _ => hplane i j)).trans
    ((six_add (fun i j => polyMul (A i j) r)
      (fun i j => polyMul q (B i j))).trans
      ((six_mul_right r A).add (six_mul_left q B)))

/-- Carré-du-champ Leibniz rule on the SAME selected original blocks. -/
theorem activeGamma_mul_right (active : List Nat) (p q r : RatPoly) :
    RatPolyCoeffEqv (activeGamma active p (polyMul q r))
      (polyAdd (polyMul (activeGamma active p q) r)
        (polyMul q (activeGamma active p r))) := by
  induction active with
  | nil =>
      change RatPolyCoeffEqv polyZero
        (polyAdd (polyMul polyZero r) (polyMul q polyZero))
      have h := (RatPolyCoeffEqv.mul_zero_left r).add
        (RatPolyCoeffEqv.mul_zero_right q)
      exact (RatPolyCoeffEqv.add_zero polyZero).symm.trans h.symm
  | cons block rest ih =>
      change RatPolyCoeffEqv
        (polyAdd (blockGamma block p (polyMul q r))
          (activeGamma rest p (polyMul q r))) _
      refine ((blockGamma_mul_right block p q r).add ih).trans ?_
      let A := polyMul (blockGamma block p q) r
      let B := polyMul q (blockGamma block p r)
      let C := polyMul (activeGamma rest p q) r
      let D := polyMul q (activeGamma rest p r)
      have hshuffle : RatPolyCoeffEqv (polyAdd (polyAdd A B) (polyAdd C D))
          (polyAdd (polyAdd A C) (polyAdd B D)) :=
        RatPolyCoeffEqv.four_add_swap A B C D
      have hA : RatPolyCoeffEqv (polyAdd A C)
          (polyMul (activeGamma (block::rest) p q) r) := by
        change RatPolyCoeffEqv (polyAdd A C)
          (polyMul (polyAdd (blockGamma block p q) (activeGamma rest p q)) r)
        rw [polyMul_add_left_exact]
        exact RatPolyCoeffEqv.refl _
      have hB : RatPolyCoeffEqv (polyAdd B D)
          (polyMul q (activeGamma (block::rest) p r)) := by
        change RatPolyCoeffEqv (polyAdd B D)
          (polyMul q (polyAdd (blockGamma block p r) (activeGamma rest p r)))
        exact (RatPolyCoeffEqv.mul_add_right q _ _).symm
      exact hshuffle.trans (hA.add hB)

/-- Symmetry of the literal mixed angular polynomial. -/
theorem activeGamma_symm (active : List Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (activeGamma active p q) (activeGamma active q p) := by
  induction active with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons block rest ih =>
      change RatPolyCoeffEqv
        (polyAdd (blockGamma block p q) (activeGamma rest p q))
        (polyAdd (blockGamma block q p) (activeGamma rest q p))
      exact (six_congr (fun i j _ _ =>
        RatPolyCoeffEqv.mul_comm
          (blockAngularDerivative block i j p)
          (blockAngularDerivative block i j q))).add ih

private theorem six_supported {n : Nat} {f : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 → SupportedQuaternionBlocks n (f i j)) :
    SupportedQuaternionBlocks n (six f) := by
  unfold six
  exact polyAdd_supported (h 0 1 (by decide) (by decide))
    (polyAdd_supported (h 0 2 (by decide) (by decide))
      (polyAdd_supported (h 0 3 (by decide) (by decide))
        (polyAdd_supported (h 1 2 (by decide) (by decide))
          (polyAdd_supported (h 1 3 (by decide) (by decide))
            (h 2 3 (by decide) (by decide))))))

/-- A supported pair has supported carré du champ on any in-range active list. -/
theorem activeGamma_supported {n : Nat} (active : List Nat)
    (hactive : ∀ block, block ∈ active → block < n)
    {p q : RatPoly} (hp : SupportedQuaternionBlocks n p)
    (hq : SupportedQuaternionBlocks n q) :
    SupportedQuaternionBlocks n (activeGamma active p q) := by
  induction active with
  | nil =>
      intro t ht
      exact False.elim (List.not_mem_nil ht)
  | cons block rest ih =>
      change SupportedQuaternionBlocks n
        (polyAdd (blockGamma block p q) (activeGamma rest p q))
      apply polyAdd_supported
      · apply six_supported
        intro i j hi hj
        have hb : block < n := hactive block List.mem_cons_self
        apply supported_polyMul
        · exact angularDerivative_supported_at (by omega) (by omega) hp
        · exact angularDerivative_supported_at (by omega) (by omega) hq
      · exact ih (fun b hb => hactive b (List.mem_cons_of_mem block hb))

private def activeGamma_squareCertificate_aux {n : Nat} (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p) :
    (active : List Nat) →
    (∀ block, block ∈ active → block < n) →
    Certificate n (activeGamma active p p)
  | [], _ => by
      change Certificate n (polyMul polyZero polyZero)
      exact .square polyZero (by
        intro t ht
        exact False.elim (List.not_mem_nil ht))
  | block::rest, hactive => by
      have hb : block < n := hactive block List.mem_cons_self
      have hsq (i j : Nat) (hi : i < 4) (hj : j < 4) :
          Certificate n (polyMul (blockAngularDerivative block i j p)
            (blockAngularDerivative block i j p)) :=
        .square (blockAngularDerivative block i j p)
          (angularDerivative_supported_at (by omega) (by omega) hp)
      have hblock : Certificate n (blockGamma block p p) := by
        unfold blockGamma six
        exact .add (hsq 0 1 (by decide) (by decide))
          (.add (hsq 0 2 (by decide) (by decide))
            (.add (hsq 0 3 (by decide) (by decide))
              (.add (hsq 1 2 (by decide) (by decide))
                (.add (hsq 1 3 (by decide) (by decide))
                  (hsq 2 3 (by decide) (by decide))))))
      change Certificate n
        (polyAdd (blockGamma block p p) (activeGamma rest p p))
      exact .add hblock (activeGamma_squareCertificate_aux p hp rest
        (fun b hb' => hactive b (List.mem_cons_of_mem block hb')))

/-- The diagonal angular carré du champ is an explicit sum-of-squares
certificate on the original supported polynomial carrier. -/
def activeGamma_squareCertificate {n : Nat} (active : List Nat)
    (hactive : ∀ block, block ∈ active → block < n)
    {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    Certificate n (activeGamma active p p) :=
  activeGamma_squareCertificate_aux p hp active hactive

end YMGap.Continuum.SU2QuaternionActiveCasimirProduct

#print axioms YMGap.Continuum.SU2QuaternionActiveCasimirProduct.blockGamma
#print axioms YMGap.Continuum.SU2QuaternionActiveCasimirProduct.activeGamma
#print axioms YMGap.Continuum.SU2QuaternionActiveCasimirProduct.activeCasimirPolynomial_mul
#print axioms YMGap.Continuum.SU2QuaternionActiveCasimirProduct.activeGamma_mul_right
#print axioms YMGap.Continuum.SU2QuaternionActiveCasimirProduct.activeGamma_symm
#print axioms YMGap.Continuum.SU2QuaternionActiveCasimirProduct.activeGamma_supported
#print axioms YMGap.Continuum.SU2QuaternionActiveCasimirProduct.activeGamma_squareCertificate
