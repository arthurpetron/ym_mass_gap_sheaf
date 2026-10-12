/-
# Coefficient-preserving three-color Gaussian quartic projection

On the existing `RatPoly` carrier put S=x_1^2+x_2^2+x_3^2. The polynomial
Q4=S^2-10*S+15 has zero partial Gaussian pairing with EVERY polynomial of
head degree at most two. All tail variables and their coefficients remain
arbitrary; the scalar head coordinate x_0 is also permitted in the test.

Consumer: the finite reference trace-source contraction
T_h^(2)=-(10/3):A_(h*sigma): in the adaptive-score audit. This checks the
standard three-color local projection, not an original compact-Haar law,
a curvature-mode pullback, cross-time covariance transport, a uniform
neighboring estimate, or H1. The actual covariance/pullback and original
section/source/OLD-center joins remain separate obligations.

No classical axiom, witness erasure, `sorry`, `native_decide`, or new axiom.
-/

import YMGap.Continuum.SU2QuaternionHeadGaussianIBP

namespace YMGap.Continuum.SU2QuaternionThreeColorQuarticProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP

local infix:50 " ≈ " => Q'.eqv

/-- Squared length of the three Gaussian color coordinates; x_0 is unused. -/
def threeColorSquare : RatPoly :=
  polyAdd (polyMul (polyVar 1) (polyVar 1))
    (polyAdd (polyMul (polyVar 2) (polyVar 2))
      (polyMul (polyVar 3) (polyVar 3)))

/-- The fourth-chaos remainder of the literal three-color radial quartic. -/
def threeColorQuartic : RatPoly :=
  polyAdd (polyMul threeColorSquare threeColorSquare)
    (polyAdd (polySmul (-10) threeColorSquare) (polyConst 15))

private def expandedQuartic : RatPoly :=
  [([0,4], 1), ([0,0,4], 1), ([0,0,0,4], 1),
   ([0,2,2], 2), ([0,2,0,2], 2), ([0,0,2,2], 2),
   ([0,2], -10), ([0,0,2], -10), ([0,0,0,2], -10), ([], 15)]

private theorem quartic_expanded :
    RatPolyCoeffEqv threeColorQuartic expandedQuartic := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide

private theorem expanded_head_support :
    ∀ term, term ∈ expandedQuartic → term.1.length ≤ 4 := by
  intro term ht
  simp only [expandedQuartic, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem exponentAt_monoMul (left right : List Nat) (i : Nat) :
    exponentAt (monoMul left right) i = exponentAt left i + exponentAt right i := by
  induction left generalizing right i with
  | nil => simp [monoMul, exponentAt]
  | cons a left ih =>
      cases right with
      | nil => simp [monoMul, exponentAt]
      | cons b right =>
          cases i with
          | zero => simp [monoMul, exponentAt]
          | succ i =>
              change exponentAt (monoMul left right) i =
                exponentAt left i + exponentAt right i
              exact ih right i

/-- Multiplication by a head monomial leaves the entire tail exponent list. -/
private theorem drop_monoMul_right (n : Nat) (left right : List Nat)
    (hr : right.length ≤ n) : (monoMul left right).drop n = left.drop n := by
  induction n generalizing left right with
  | zero =>
      have hnil : right = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hr)
      subst right
      cases left <;> rfl
  | succ n ih =>
      cases right with
      | nil => cases left <;> rfl
      | cons b right =>
          have ht : right.length ≤ n := by
            simp only [List.length_cons] at hr
            omega
          cases left with
          | nil =>
              simp only [monoMul, List.drop_nil]
              exact List.drop_eq_nil_of_le hr
          | cons a left =>
              simpa only [monoMul, List.drop_succ_cons] using ih left right ht

private def quarticMoment (a b c d : Nat) : Q' :=
  gaussianMoment4 a (b+4) c d +
    (gaussianMoment4 a b (c+4) d +
    (gaussianMoment4 a b c (d+4) +
    (2*gaussianMoment4 a (b+2) (c+2) d +
    (2*gaussianMoment4 a (b+2) c (d+2) +
    (2*gaussianMoment4 a b (c+2) (d+2) +
    ((-10)*gaussianMoment4 a (b+2) c d +
    ((-10)*gaussianMoment4 a b (c+2) d +
    ((-10)*gaussianMoment4 a b c (d+2) +
    (15*gaussianMoment4 a b c d + 0)))))))))

/-- Only the finite HEAD patterns are enumerated; no tail is evaluated. -/
private theorem quarticMoment_zero (a b c d : Nat) (h : a+b+c+d ≤ 2) :
    quarticMoment a b c d ≈ 0 := by
  have ha : a=0 ∨ a=1 ∨ a=2 := by omega
  have hb : b=0 ∨ b=1 ∨ b=2 := by omega
  have hc : c=0 ∨ c=1 ∨ c=2 := by omega
  have hd : d=0 ∨ d=1 ∨ d=2 := by omega
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    rcases hd with rfl | rfl | rfl
  all_goals first | omega | decide

private theorem expanded_moment (m : List Nat) :
    ratWeightedSum (fun n => headGaussianMoment (monoMul m n)) expandedQuartic ≈
      quarticMoment (exponentAt m 0) (exponentAt m 1)
        (exponentAt m 2) (exponentAt m 3) := by
  simp only [expandedQuartic, ratWeightedSum]
  simp only [headGaussianMoment]
  simp only [exponentAt_monoMul]
  simp only [exponentAt, List.getD_cons_zero, List.getD_cons_succ,
    List.getD_nil, Nat.add_zero]
  unfold quarticMoment
  apply Q'.add_eqv_congr'
  · exact Q'.one_mul_eqv _
  · apply Q'.add_eqv_congr'
    · exact Q'.one_mul_eqv _
    · apply Q'.add_eqv_congr'
      · exact Q'.one_mul_eqv _
      · exact Q'.eqv_refl _

private theorem row_rearrange (c a b t r : Q') :
    (c*a)*(b*t) + c*(r*t) ≈ c*((a*b+r)*t) :=
  poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 0) (.mul (.var 4) (.var 3))))
    (.mul (.var 0) (.mul (.add (.mul (.var 1) (.var 2)) (.var 4)) (.var 3)))
    (by decide) (fun | 0 => c | 1 => a | 2 => b | 3 => t | _ => r)

private theorem weighted_head_row (weight : List Nat → Q') (m : List Nat) (c : Q') :
    ∀ q : RatPoly, (∀ term, term ∈ q → term.1.length ≤ 4) →
      ratWeightedSum (gaussianHeadProbe weight)
          (q.map fun term => (monoMul m term.1, c*term.2)) ≈
        c*(ratWeightedSum (fun n => headGaussianMoment (monoMul m n)) q *
          weight (m.drop 4))
  | [], _ => Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) (Q'.mul_zero_eqv _))
  | term :: q, hq => by
      have ht : (monoMul m term.1).drop 4 = m.drop 4 :=
        drop_monoMul_right 4 m term.1 (hq term List.mem_cons_self)
      have ih := weighted_head_row weight m c q
        (fun other ho => hq other (List.mem_cons_of_mem term ho))
      simp only [List.map_cons, ratWeightedSum, gaussianHeadProbe, ht]
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ih)
        (row_rearrange c term.2 (headGaussianMoment (monoMul m term.1))
          (weight (m.drop 4))
          (ratWeightedSum (fun n => headGaussianMoment (monoMul m n)) q))

private theorem head_singleton_zero (q : RatPoly)
    (hq : ∀ term, term ∈ q → term.1.length ≤ 4) (m : List Nat) (c : Q')
    (hmoment : ratWeightedSum (fun n => headGaussianMoment (monoMul m n)) q ≈ 0) :
    RatPolyCoeffEqv (partialGaussianHead (polyMul [(m,c)] q)) polyZero := by
  intro weight
  have hrow := weighted_head_row weight m c q hq
  simp only [polyMul, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change ratWeightedSum weight (partialGaussianHead
    (q.map fun term => (monoMul m term.1, c*term.2))) ≈ 0
  exact Q'.eqv_trans _ _ _ (partialGaussianHead_probe weight _)
    (Q'.eqv_trans _ _ _ hrow
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ hmoment))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
          (Q'.mul_zero_eqv _))))

private theorem head_polynomial_zero (q : RatPoly)
    (hq : ∀ term, term ∈ q → term.1.length ≤ 4)
    (hzero : ∀ m, quaternionBlockDegree m 0 ≤ 2 →
      ratWeightedSum (fun n => headGaussianMoment (monoMul m n)) q ≈ 0) :
    ∀ p : RatPoly, (∀ term, term ∈ p → quaternionBlockDegree term.1 0 ≤ 2) →
      RatPolyCoeffEqv (partialGaussianHead (polyMul p q)) polyZero
  | [], _ => RatPolyCoeffEqv.refl polyZero
  | term :: p, hp => by
      have hs : RatPolyCoeffEqv
          (partialGaussianHead
            (q.map fun other => (monoMul term.1 other.1, term.2*other.2))) polyZero := by
        simpa only [polyMul, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
          head_singleton_zero q hq term.1 term.2
            (hzero term.1 (hp term List.mem_cons_self))
      have ih := head_polynomial_zero q hq hzero p
        (fun other ho => hp other (List.mem_cons_of_mem term ho))
      change RatPolyCoeffEqv
        (partialGaussianHead (polyAdd
          (q.map fun other => (monoMul term.1 other.1, term.2*other.2))
          (polyMul p q))) polyZero
      rw [partialGaussianHead_add]
      exact (hs.add ih).trans (RatPolyCoeffEqv.refl polyZero)

private theorem expanded_moment_zero (m : List Nat)
    (hm : quaternionBlockDegree m 0 ≤ 2) :
    ratWeightedSum (fun n => headGaussianMoment (monoMul m n)) expandedQuartic ≈ 0 := by
  have hdegree : exponentAt m 0 + exponentAt m 1 + exponentAt m 2 + exponentAt m 3 ≤ 2 := by
    simpa only [quaternionBlockDegree, Nat.mul_zero, Nat.zero_add] using hm
  exact Q'.eqv_trans _ _ _ (expanded_moment m) (quarticMoment_zero _ _ _ _ hdegree)

/-- The standard three-color quartic remainder annihilates every quadratic
head test, coefficientwise with arbitrary untouched tail variables. -/
theorem threeColorQuartic_quadratic_annihilation (p : RatPoly)
    (hp : ∀ term, term ∈ p → quaternionBlockDegree term.1 0 ≤ 2) :
    RatPolyCoeffEqv (partialGaussianHead (polyMul threeColorQuartic p)) polyZero :=
  (partialGaussianHead_congr (RatPolyCoeffEqv.mul_comm threeColorQuartic p)).trans
    ((partialGaussianHead_congr (quartic_expanded.mul_left p)).trans
      (head_polynomial_zero expandedQuartic expanded_head_support expanded_moment_zero p hp))

end YMGap.Continuum.SU2QuaternionThreeColorQuarticProjection

#print axioms YMGap.Continuum.SU2QuaternionThreeColorQuarticProjection.threeColorQuartic_quadratic_annihilation
