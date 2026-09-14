/-
# Three-way positive-spin expansion of the existing two-slot increment

Finite additivity expands each positive character sum inside both slots.
The result is precisely left-positive, right-positive, or both-positive
spin pairs. No rational-linearity or independent-variable law is assumed.
-/

import YMGap.Continuum.PolynomialBiadditiveMobius
import YMGap.Continuum.PairedPositiveFaceLabellings
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

namespace YMGap.Continuum.PolynomialBiadditivePositiveExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.PolynomialBiadditive
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

private theorem zero_of_double {x : Q'} (h : x ≈ x+x) : x ≈ 0 :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq (.var 0)
    (.add (.add (.var 0) (.var 0)) (.neg (.var 0))) (by decide) (fun _ => x))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_symm h) (Q'.eqv_refl _)) (Q'.add_neg_self_eqv x))

theorem zero_left (B : Biadditive) (p : RatPoly) : B.value polyZero p ≈ 0 :=
  zero_of_double (B.add_left polyZero polyZero p)

theorem zero_right (B : Biadditive) (p : RatPoly) : B.value p polyZero ≈ 0 :=
  zero_of_double (B.add_right p polyZero polyZero)

theorem sum_left {A : Type} (B : Biadditive) (f : A → RatPoly) (p : RatPoly) : ∀ xs : List A,
    B.value (finitePolySum f xs) p ≈ listQSum (fun a => B.value (f a) p) xs
  | [] => zero_left B p
  | a::xs => Q'.eqv_trans _ _ _ (B.add_left (f a) (finitePolySum f xs) p)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_left B f p xs))

theorem sum_right {A : Type} (B : Biadditive) (p : RatPoly) (f : A → RatPoly) : ∀ xs : List A,
    B.value p (finitePolySum f xs) ≈ listQSum (fun a => B.value p (f a)) xs
  | [] => zero_right B p
  | a::xs => Q'.eqv_trans _ _ _ (B.add_right p (f a) (finitePolySum f xs))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_right B p f xs))

theorem two_sums {A C : Type} (B : Biadditive) (f : A → RatPoly) (g : C → RatPoly)
    (xs : List A) (ys : List C) :
    B.value (finitePolySum f xs) (finitePolySum g ys) ≈
      listQSum (fun a => listQSum (fun c => B.value (f a) (g c)) ys) xs :=
  Q'.eqv_trans _ _ _ (sum_left B f (finitePolySum g ys) xs)
    (listQSum_congr_on _ _ _ (fun a _ => sum_right B (f a) g ys))

theorem sum_mul {A : Type} (f : A → RatPoly) (p : RatPoly) : ∀ xs : List A,
    RatPolyCoeffEqv (polyMul (finitePolySum f xs) p)
      (finitePolySum (fun a => polyMul (f a) p) xs)
  | [] => RatPolyCoeffEqv.refl _
  | a::xs => by
    change RatPolyCoeffEqv (polyMul (polyAdd (f a) (finitePolySum f xs)) p) _
    rw [polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.refl _).add (sum_mul f p xs)

theorem insert_sum_left {A : Type} (B : Biadditive) (f : A → RatPoly) (p q : RatPoly) (xs : List A) :
    B.value (polyMul (finitePolySum f xs) p) q ≈ listQSum (fun a => B.value (polyMul (f a) p) q) xs :=
  Q'.eqv_trans _ _ _ (B.congr (sum_mul f p xs) (RatPolyCoeffEqv.refl q)) (sum_left B _ q xs)

theorem insert_sum_right {A : Type} (B : Biadditive) (p q : RatPoly) (f : A → RatPoly) (xs : List A) :
    B.value p (polyMul (finitePolySum f xs) q) ≈ listQSum (fun a => B.value p (polyMul (f a) q)) xs :=
  Q'.eqv_trans _ _ _ (B.congr (RatPolyCoeffEqv.refl p) (sum_mul f q xs)) (sum_right B p _ xs)

theorem insert_two_sums {A C : Type} (B : Biadditive) (f : A → RatPoly) (g : C → RatPoly)
    (p q : RatPoly) (xs : List A) (ys : List C) :
    B.value (polyMul (finitePolySum f xs) p) (polyMul (finitePolySum g ys) q) ≈
      listQSum (fun a => listQSum (fun c => B.value (polyMul (f a) p) (polyMul (g c) q)) ys) xs :=
  Q'.eqv_trans _ _ _ (B.congr (sum_mul f p xs) (sum_mul g q ys)) (two_sums B _ _ xs ys)

/-- The existing increment, with a complete and explicit positive pair sum. -/
theorem increment_positive (B : Biadditive) (K : Nat) (g : Nat → RatPoly)
    (h0 : RatPolyCoeffEqv (g 0) polyOne) (p q : RatPoly) :
    (B.increment (finitePolySum (fun n => g (n+1)) (List.range K))).value p q ≈
      listQSum (fun spins => B.value (polyMul (g spins.1) p) (polyMul (g spins.2) q)) (positivePairs K) := by
  let value := fun spins : Nat × Nat => B.value (polyMul (g spins.1) p) (polyMul (g spins.2) q)
  let sl := listQSum (fun n => value (n+1,0)) (List.range K)
  let sr := listQSum (fun n => value (0,n+1)) (List.range K)
  let sb := listQSum (fun n => listQSum (fun m => value (n+1,m+1)) (List.range K)) (List.range K)
  have hp := (h0.mul (RatPolyCoeffEqv.refl p)).trans (RatPolyCoeffEqv.one_mul p)
  have hq := (h0.mul (RatPolyCoeffEqv.refl q)).trans (RatPolyCoeffEqv.one_mul q)
  have hl : B.value (polyMul (finitePolySum (fun n => g (n+1)) (List.range K)) p) q ≈ sl :=
    Q'.eqv_trans _ _ _ (insert_sum_left B _ p q _)
      (listQSum_congr_on _ _ _ (fun _ _ => B.congr (RatPolyCoeffEqv.refl _) hq.symm))
  have hr : B.value p (polyMul (finitePolySum (fun n => g (n+1)) (List.range K)) q) ≈ sr :=
    Q'.eqv_trans _ _ _ (insert_sum_right B p q _ _)
      (listQSum_congr_on _ _ _ (fun _ _ => B.congr hp.symm (RatPolyCoeffEqv.refl _)))
  have hb : B.value (polyMul (finitePolySum (fun n => g (n+1)) (List.range K)) p)
      (polyMul (finitePolySum (fun n => g (n+1)) (List.range K)) q) ≈ sb :=
    insert_two_sums B _ _ p q _ _
  have hs : listQSum value (positivePairs K) ≈ sl+sr+sb := by
    unfold positivePairs
    refine Q'.eqv_trans _ _ _ (listQSum_append _ _ _) (Q'.add_eqv_congr' ?_ ?_)
    · simpa only [listQSum_map] using listQSum_append value
        ((List.range K).map (fun n => (n+1,0))) ((List.range K).map (fun n => (0,n+1)))
    · simpa only [listQSum_map] using listQSum_flatMap value
        (fun n => (List.range K).map (fun m => (n+1,m+1))) (List.range K)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.add_eqv_congr' hl hr) hb) (Q'.eqv_symm hs)

end YMGap.Continuum.PolynomialBiadditivePositiveExpansion

#print axioms YMGap.Continuum.PolynomialBiadditivePositiveExpansion.zero_left
#print axioms YMGap.Continuum.PolynomialBiadditivePositiveExpansion.zero_right
#print axioms YMGap.Continuum.PolynomialBiadditivePositiveExpansion.sum_left
#print axioms YMGap.Continuum.PolynomialBiadditivePositiveExpansion.sum_right
#print axioms YMGap.Continuum.PolynomialBiadditivePositiveExpansion.two_sums
#print axioms YMGap.Continuum.PolynomialBiadditivePositiveExpansion.sum_mul
#print axioms YMGap.Continuum.PolynomialBiadditivePositiveExpansion.insert_sum_left
#print axioms YMGap.Continuum.PolynomialBiadditivePositiveExpansion.insert_sum_right
#print axioms YMGap.Continuum.PolynomialBiadditivePositiveExpansion.insert_two_sums
#print axioms YMGap.Continuum.PolynomialBiadditivePositiveExpansion.increment_positive
