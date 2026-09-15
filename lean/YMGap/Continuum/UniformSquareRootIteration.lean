/-
# Division-free square-root iteration, uniformly including zero

Starting at zero, x_{n+1}=x_n+(t-x_n^2)/2 stays in [0,1],
increases, and has x_n^2<=t for every rational t in [0,1].
The decreasing residual e_n=t-x_n^2 satisfies n*e_n<=2*x_n<=2.
This gives a computed uniform residual rate without a positive lower
bound on t and without assuming a square root already exists.

These are rational approximation estimates, not yet an operator square
identity or an identification of geometric half time. Physical-scale
uniformity, continuum reconstruction and the Clay target remain open.
-/

import YMGap.Constructive.Soundness
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CauchyConv
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.UniformSquareRootIteration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

def residual (t x : Q') : Q' := t-x*x

def step (t x : Q') : Q' := x+HalfPow.half*residual t x

theorem twice_half (a : Q') : Q'.eqv (2*(HalfPow.half*a)) a :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 2 HalfPow.half a))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ 1 a (by decide)) (Q'.one_mul_eqv a))

theorem twice_step (t x : Q') : Q'.eqv (2*step t x) (2*x+residual t x) :=
  Q'.eqv_trans _ _ _ (Q'.mul_add_eqv 2 x (HalfPow.half*residual t x))
    (Q'.add_eqv_congr_left _ _ _ (twice_half _))

theorem step_upper_gap (t x : Q') :
    Q'.eqv (2-(2*x+residual t x)) ((1-x)*(1-x)+(1-t)) :=
  poly_identity_of_normal_eq
    (.add (.const 2) (.neg (.add (.mul (.const 2) (.var 1))
      (.add (.var 0) (.neg (.mul (.var 1) (.var 1)))))))
    (.add (.mul (.add (.const 1) (.neg (.var 1))) (.add (.const 1) (.neg (.var 1))))
      (.add (.const 1) (.neg (.var 0)))) (by decide) (fun | 0 => t | _ => x)

theorem step_square_expansion (t x : Q') :
    Q'.eqv (step t x*step t x) (x*x+(HalfPow.half*residual t x)*(x+step t x)) :=
  poly_identity_of_normal_eq
    (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
    (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.add (.var 0) (.add (.var 0) (.var 1)))))
    (by decide) (fun | 0 => x | _ => HalfPow.half*residual t x)

theorem square_add_residual (t x : Q') : Q'.eqv (x*x+residual t x) t :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 1) (.var 1)) (.add (.var 0) (.neg (.mul (.var 1) (.var 1)))))
    (.var 0) (by decide) (fun | 0 => t | _ => x)

theorem step_invariants (t x : Q') (hx : (0 : Q')≤x) (h1 : x≤1)
    (hs : x*x≤t) (ht : t≤1) :
    (0 : Q')≤step t x ∧ step t x≤1 ∧ step t x*step t x≤t ∧ x≤step t x := by
  have he : (0 : Q')≤residual t x := Q'.sub_nonneg_of_le hs
  have hd := Q'.mul_nonneg _ _ HalfPow.half_nonneg he
  have hmono : x≤step t x := Q'.add_le_self_of_nonneg _ _ hd
  have hnonneg := Q'.le_trans' _ _ _ hx hmono
  have hg := Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg (1-x)) (Q'.sub_nonneg_of_le ht)
  have hu : 2*x+residual t x≤2 :=
    Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hg (Q'.ge_of_eqv (step_upper_gap t x)))
  have hone : step t x≤1 := Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (twice_step t x))
      (Q'.le_trans' _ _ _ hu (by decide : (2 : Q')≤2*1))) (by decide : (0 : Q')<2)
  have hsum : x+step t x≤2 := Q'.le_trans' _ _ _ (Q'.add_le_add h1 hone) (by decide)
  have hinc : (HalfPow.half*residual t x)*(x+step t x)≤residual t x :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hsum hd)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (twice_half _)))
  have hsquare := Q'.le_trans' _ _ _ (Q'.le_of_eqv (step_square_expansion t x))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hinc) (Q'.le_of_eqv (square_add_residual t x)))
  exact ⟨hnonneg,hone,hsquare,hmono⟩

def iterate (t : Q') : Nat → Q'
  | 0 => 0
  | n+1 => step t (iterate t n)

theorem iterate_invariants (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) (n : Nat) :
    (0 : Q')≤iterate t n ∧ iterate t n≤1 ∧ iterate t n*iterate t n≤t := by
  induction n with
  | zero => exact ⟨Q'.le_refl' _,Q'.zero_le_one,Q'.le_trans' _ _ _ (by decide : (0 : Q')*0≤0) ht⟩
  | succ n ih => exact ⟨(step_invariants t _ ih.1 ih.2.1 ih.2.2 h1).1,
      (step_invariants t _ ih.1 ih.2.1 ih.2.2 h1).2.1,
      (step_invariants t _ ih.1 ih.2.1 ih.2.2 h1).2.2.1⟩

theorem iterate_step_mono (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) (n : Nat) :
    iterate t n≤iterate t (n+1) :=
  (step_invariants t _ (iterate_invariants t ht h1 n).1
    (iterate_invariants t ht h1 n).2.1 (iterate_invariants t ht h1 n).2.2 h1).2.2.2

theorem iterate_mono (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) {m n : Nat} (hmn : m≤n) :
    iterate t m≤iterate t n := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih => exact Q'.le_trans' _ _ _ ih (iterate_step_mono t ht h1 (m+d))

theorem residual_nonnegative (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) (n : Nat) :
    (0 : Q')≤residual t (iterate t n) := Q'.sub_nonneg_of_le (iterate_invariants t ht h1 n).2.2

theorem residual_antitone (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) {m n : Nat} (hmn : m≤n) :
    residual t (iterate t n)≤residual t (iterate t m) :=
  Q'.add_le_add_left _ _ _ (Q'.neg_le_neg (Q'.mul_le_mul_of_nonneg
    (iterate_mono t ht h1 hmn) (iterate_mono t ht h1 hmn)
    (iterate_invariants t ht h1 n).1 (iterate_invariants t ht h1 m).1))

theorem successor_product (n : Nat) (e : Q') :
    Q'.eqv (Q'.ofNat (n+1)*e) (Q'.ofNat n*e+e) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ e (Q'.ofNat_add_eqv n 1))
    (poly_identity_of_normal_eq (.mul (.add (.var 0) (.const 1)) (.var 1))
      (.add (.mul (.var 0) (.var 1)) (.var 1)) (by decide) (fun | 0 => Q'.ofNat n | _ => e))

/-- Telescoping paid increments control the current residual without a square-root premise. -/
theorem weighted_residual (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) (n : Nat) :
    Q'.ofNat n*residual t (iterate t n)≤2*iterate t n := by
  induction n with
  | zero => exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_zero_mul _)) (by decide : (0 : Q')≤2*0)
  | succ n ih =>
      have hn : (0 : Q')≤Q'.ofNat (n+1) := ofNat_le_ofNat (Nat.zero_le _)
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (residual_antitone t ht h1 (Nat.le_succ n)) hn)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (successor_product n _))
          (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ ih) (Q'.ge_of_eqv (twice_step t _))))

theorem weighted_residual_bound (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) (n : Nat) :
    Q'.ofNat n*residual t (iterate t n)≤2 :=
  Q'.le_trans' _ _ _ (weighted_residual t ht h1 n)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 2 (iterate_invariants t ht h1 n).2.1 (by decide))
      (by decide : (2 : Q')*1≤2))

def residualStage (epsilon : Q') : Nat := 2*epsilon.den

theorem residualStage_positive (epsilon : Q') : 0<residualStage epsilon :=
  Nat.mul_pos (by decide) epsilon.den_pos

theorem residualStage_budget (epsilon : Q') (he : (0 : Q')<epsilon) :
    (2 : Q')≤Q'.ofNat (residualStage epsilon)*epsilon := by
  have hn : (1 : Int)≤epsilon.num := Q'.num_pos_of_pos he
  have hd : (0 : Int)≤2*(epsilon.den : Int) := Int.mul_nonneg (by decide) (Int.natCast_nonneg _)
  have h := Int.mul_le_mul_of_nonneg_left hn hd
  show (2 : Int)*((Q'.ofNat (residualStage epsilon)*epsilon).den : Int)≤
    (Q'.ofNat (residualStage epsilon)*epsilon).num*(1 : Int)
  rw [Q'.mul_den_cast]
  change 2*(1*(epsilon.den : Int))≤((residualStage epsilon : Nat) : Int)*epsilon.num*1
  simpa only [residualStage,Int.natCast_mul,Int.one_mul,Int.mul_one] using h

/-- Explicit error rate uniform in every rational t in [0,1], including t=0. -/
theorem residual_bound (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : residualStage epsilon≤n) :
    residual t (iterate t n)≤epsilon := by
  have hnpos : (0 : Q')<Q'.ofNat n := by
    have hnat : 0<n := Nat.lt_of_lt_of_le (residualStage_positive epsilon) hn
    change (0 : Int)*1<(n : Int)*1
    simpa only [Int.zero_mul,Int.mul_one] using (Int.ofNat_lt.mpr hnat)
  apply Q'.le_of_mul_le_mul_left (c := Q'.ofNat n) _ hnpos
  exact Q'.le_trans' _ _ _ (weighted_residual_bound t ht h1 n)
    (Q'.le_trans' _ _ _ (residualStage_budget epsilon he)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (ofNat_le_ofNat hn) (Q'.le_of_lt he)))

end YMGap.Continuum.UniformSquareRootIteration

#print axioms YMGap.Continuum.UniformSquareRootIteration.residual
#print axioms YMGap.Continuum.UniformSquareRootIteration.step
#print axioms YMGap.Continuum.UniformSquareRootIteration.twice_half
#print axioms YMGap.Continuum.UniformSquareRootIteration.twice_step
#print axioms YMGap.Continuum.UniformSquareRootIteration.step_upper_gap
#print axioms YMGap.Continuum.UniformSquareRootIteration.step_square_expansion
#print axioms YMGap.Continuum.UniformSquareRootIteration.square_add_residual
#print axioms YMGap.Continuum.UniformSquareRootIteration.step_invariants
#print axioms YMGap.Continuum.UniformSquareRootIteration.iterate
#print axioms YMGap.Continuum.UniformSquareRootIteration.iterate_invariants
#print axioms YMGap.Continuum.UniformSquareRootIteration.iterate_step_mono
#print axioms YMGap.Continuum.UniformSquareRootIteration.iterate_mono
#print axioms YMGap.Continuum.UniformSquareRootIteration.residual_nonnegative
#print axioms YMGap.Continuum.UniformSquareRootIteration.residual_antitone
#print axioms YMGap.Continuum.UniformSquareRootIteration.successor_product
#print axioms YMGap.Continuum.UniformSquareRootIteration.weighted_residual
#print axioms YMGap.Continuum.UniformSquareRootIteration.weighted_residual_bound
#print axioms YMGap.Continuum.UniformSquareRootIteration.residualStage
#print axioms YMGap.Continuum.UniformSquareRootIteration.residualStage_positive
#print axioms YMGap.Continuum.UniformSquareRootIteration.residualStage_budget
#print axioms YMGap.Continuum.UniformSquareRootIteration.residual_bound
