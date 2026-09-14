/-
# Evaluate retained coefficients without changing the head Haar calculation

An explicit rational environment evaluates all coordinates after a retained
prefix. This is a polynomial algebra homomorphism modulo coefficient
equality, and commutes with head Haar when at least four coordinates are
retained. It permits specializing auxiliary tail quaternions in an already
proved polynomial-valued orthogonality identity. This is evaluation, NOT
Haar integration or permission to set physical links to constants in a measure.
-/

import YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection

namespace YMGap.Continuum.SU2QuaternionTailEvaluation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini

local infix:50 " ≈ " => Q'.eqv

def evaluateTerm (keep : Nat) (rho : Nat → Q') (t : RatTerm) : RatTerm :=
  (t.1.take keep, t.2 * evalMono rho (t.1.drop keep))

def evaluateTail (keep : Nat) (rho : Nat → Q') (p : RatPoly) : RatPoly :=
  p.map (evaluateTerm keep rho)

theorem weighted_evaluate (keep : Nat) (rho weight : List Nat → Q') :
    ∀ p : RatPoly,
    ratWeightedSum weight (p.map fun t => (t.1.take keep, t.2 * rho (t.1.drop keep))) ≈
      ratWeightedSum (fun m => rho (m.drop keep) * weight (m.take keep)) p
  | [] => Q'.eqv_refl _
  | _::p => Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _) (weighted_evaluate keep rho weight p)

theorem evaluate_congr (keep : Nat) (rho : Nat → Q') {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (evaluateTail keep rho p) (evaluateTail keep rho q) := by
  intro weight
  exact Q'.eqv_trans _ _ _ (weighted_evaluate keep (evalMono rho) weight p)
    (Q'.eqv_trans _ _ _ (h _) (Q'.eqv_symm (weighted_evaluate keep (evalMono rho) weight q)))

private theorem map_coeff {A : Type} (f g : A → RatTerm)
    (h : ∀ a, (f a).1 = (g a).1 ∧ (f a).2 ≈ (g a).2) :
    ∀ xs : List A, RatPolyCoeffEqv (xs.map f) (xs.map g)
  | [] => RatPolyCoeffEqv.refl _
  | a::xs => by
    intro weight
    change (f a).2 * weight (f a).1 + ratWeightedSum weight (xs.map f) ≈
      (g a).2 * weight (g a).1 + ratWeightedSum weight (xs.map g)
    rw [(h a).1]
    exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ (h a).2) (map_coeff f g h xs weight)

theorem evaluate_add (keep : Nat) (rho : Nat → Q') (p q : RatPoly) :
    evaluateTail keep rho (polyAdd p q) = polyAdd (evaluateTail keep rho p) (evaluateTail keep rho q) := List.map_append

theorem evaluate_smul (keep : Nat) (rho : Nat → Q') (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (evaluateTail keep rho (polySmul c p)) (polySmul c (evaluateTail keep rho p)) := by
  simp only [evaluateTail, polySmul, List.map_map]
  apply map_coeff
  intro t
  exact ⟨rfl,Q'.mul_assoc_eqv c t.2 _⟩

theorem evaluate_one (keep : Nat) (rho : Nat → Q') :
    RatPolyCoeffEqv (evaluateTail keep rho polyOne) polyOne := by
  intro weight
  simp only [evaluateTail, evaluateTerm, polyOne, List.map_cons, List.map_nil,
    List.take_nil, List.drop_nil, evalMono, evalMonoFrom]
  exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv 1)) (Q'.eqv_refl _)

private theorem mono_nil : ∀ m : List Nat, monoMul m [] = m
  | [] => rfl
  | _::_ => rfl

private theorem mono_take : ∀ (n : Nat) (a b : List Nat),
    (monoMul a b).take n = monoMul (a.take n) (b.take n)
  | 0,_,_ => rfl
  | n+1,[],b => by simp [monoMul]
  | n+1,a,[] => by rw [mono_nil, List.take_nil, mono_nil]
  | n+1,_::a,_::b => by simp only [monoMul, List.take_succ_cons, mono_take n a b]

private theorem mono_drop : ∀ (n : Nat) (a b : List Nat),
    (monoMul a b).drop n = monoMul (a.drop n) (b.drop n)
  | 0,_,_ => rfl
  | n+1,[],b => by simp [monoMul]
  | n+1,a,[] => by rw [mono_nil, List.drop_nil, mono_nil]
  | n+1,_::a,_::b => by simp only [monoMul, List.drop_succ_cons, mono_drop n a b]

private theorem mul_term (keep : Nat) (rho : Nat → Q') (a b : RatTerm) :
    (evaluateTerm keep rho (monoMul a.1 b.1,a.2*b.2)).1 =
      monoMul (evaluateTerm keep rho a).1 (evaluateTerm keep rho b).1 ∧
    (evaluateTerm keep rho (monoMul a.1 b.1,a.2*b.2)).2 ≈
      (evaluateTerm keep rho a).2 * (evaluateTerm keep rho b).2 := by
  refine ⟨mono_take keep a.1 b.1, ?_⟩
  unfold evaluateTerm
  simp only [mono_drop]
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (evalMono_monoMul rho _ _))
    (q_mul4_swap _ _ _ _)

theorem evaluate_mul (keep : Nat) (rho : Nat → Q') : ∀ p q : RatPoly,
    RatPolyCoeffEqv (evaluateTail keep rho (polyMul p q))
      (polyMul (evaluateTail keep rho p) (evaluateTail keep rho q))
  | [],_ => RatPolyCoeffEqv.refl _
  | a::p,q => by
    simp only [evaluateTail, polyMul, List.flatMap_cons, List.map_append, List.map_cons, List.map_map]
    refine (map_coeff _ _ (mul_term keep rho a) q).add ?_
    simpa only [evaluateTail, polyMul, List.map_map] using evaluate_mul keep rho p q

private theorem exponent_take (m : List Nat) : ∀ n i, i < n →
    exponentAt (m.take n) i = exponentAt m i
  | 0,_,h => by omega
  | n+1,0,_ => by cases m <;> rfl
  | n+1,i+1,h => by
    cases m with
    | nil => rfl
    | cons a m => exact exponent_take m n i (by omega)

private theorem headMoment_take (keep : Nat) (m : List Nat) :
    headQuaternionMoment (m.take (keep+4)) = headQuaternionMoment m := by
  unfold headQuaternionMoment
  rw [exponent_take m _ 0 (by omega), exponent_take m _ 1 (by omega),
    exponent_take m _ 2 (by omega), exponent_take m _ 3 (by omega)]

private theorem take_drop_n : ∀ (count keep : Nat) (m : List Nat),
    (m.take (keep+count)).drop count = (m.drop count).take keep
  | 0,_,_ => rfl
  | _+1,_,[] => by simp only [List.take_nil, List.drop_nil]
  | count+1,keep,_::m => take_drop_n count keep m

/-- Evaluation affects only the retained coefficients, not the integrated block. -/
theorem partialHaarHead_evaluate (keep : Nat) (rho : Nat → Q') (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (evaluateTail (keep+4) rho p))
      (evaluateTail keep rho (partialHaarHead p)) := by
  simp only [evaluateTail, partialHaarHead, List.map_map]
  apply map_coeff
  intro t
  constructor
  · exact take_drop_n 4 keep t.1
  · simp only [evaluateTerm, partialHaarHeadTerm, Function.comp_apply, List.drop_drop,
      headMoment_take]
    rw [Nat.add_comm 4 keep]
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => t.2 | 1 => evalMono rho (t.1.drop (keep+4)) | _ => headQuaternionMoment t.1)

/-- A polynomial-valued Haar zero remains zero under explicit tail specialization. -/
theorem partialHaarHead_evaluate_zero (keep : Nat) (rho : Nat → Q') {p : RatPoly}
    (h : RatPolyCoeffEqv (partialHaarHead p) polyZero) :
    RatPolyCoeffEqv (partialHaarHead (evaluateTail (keep+4) rho p)) polyZero :=
  (partialHaarHead_evaluate keep rho p).trans (evaluate_congr keep rho h)

end YMGap.Continuum.SU2QuaternionTailEvaluation

#print axioms YMGap.Continuum.SU2QuaternionTailEvaluation.evaluateTerm
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluation.evaluateTail
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluation.weighted_evaluate
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluation.evaluate_congr
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluation.evaluate_add
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluation.evaluate_smul
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluation.evaluate_one
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluation.evaluate_mul
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluation.partialHaarHead_evaluate
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluation.partialHaarHead_evaluate_zero
