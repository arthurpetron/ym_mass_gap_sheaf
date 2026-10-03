/-
# Finite rational polynomial quadrature and interval order

Signed coefficients are retained. Exact monomial antiderivative increments
are compared with an explicit rational mesh; the total error is bounded by
the mesh times a computed coefficient budget. Pointwise nonnegativity then
gives nonnegativity of the exact primitive by rational Archimedean closure.
This is finite algebra, not an assumed mean-value theorem or a CReal limit.
-/

import YMGap.Continuum.SemicircleAtanEndpointMonomialRiemann
import YMGap.Constructive.QPolyFormalDerivative
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.RationalPolynomialIntervalOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.SemicircleAtanEndpointMonomialRiemann

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (a : Q') : (-a).num = -a.num := rfl
private theorem zero_num : (0 : Q').num = 0 := rfl
private theorem zero_den : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, zero_num, zero_den, one_num, one_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-- Literal monomial expansion of a coefficient list, starting at degree k. -/
def powerEval : Nat → Poly → Q' → Q'
  | _, [], _ => 0
  | k, c::cs, x => c * qpow x k + powerEval (k+1) cs x

/-- Exact signed primitive increment. No positivity is built into it. -/
def primitiveIncrement : Nat → Poly → Q' → Q' → Q'
  | _, [], _, _ => 0
  | k, c::cs, a, b => c * monomialIncrement a b k + primitiveIncrement (k+1) cs a b

/-- Computed finite absolute coefficient budget. -/
def coefficientBudget : Poly → Q'
  | [] => 0
  | c::cs => Q'.abs c + coefficientBudget cs

theorem coefficientBudget_nonnegative : ∀ p : Poly, (0 : Q') ≤ coefficientBudget p
  | [] => Q'.le_refl' _
  | c::cs => Q'.zero_le_add _ _ (Q'.abs_nonneg c) (coefficientBudget_nonnegative cs)

theorem powerEval_horner (k : Nat) (p : Poly) (x : Q') :
    powerEval k p x ≈ qpow x k * eval p x := by
  induction p generalizing k with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  | cons c cs ih =>
      change c * qpow x k + powerEval (k+1) cs x ≈ qpow x k * (c + x * eval cs x)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (ih (k+1))) ?_
      change c * qpow x k + (qpow x k * x) * eval cs x ≈ _
      ring_qeqv

private theorem sum_le (f g : Nat → Q') : ∀ n,
    (∀ j, j < n → f j ≤ g j) → finSum f n ≤ finSum g n
  | 0, _ => Q'.le_refl' _
  | n+1, h => Q'.add_le_add
      (sum_le f g n (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h n (Nat.lt_succ_self n))

private theorem sum_nonnegative (f : Nat → Q') (n : Nat)
    (h : ∀ j, j < n → (0 : Q') ≤ f j) : (0 : Q') ≤ finSum f n := by
  have hs := sum_le (fun _ => 0) f n h
  rw [finSum_zero_seq] at hs
  exact hs

private theorem sum_congr (f g : Nat → Q') : ∀ n,
    (∀ j, j < n → f j ≈ g j) → finSum f n ≈ finSum g n
  | 0, _ => Q'.eqv_refl _
  | n+1, h => Q'.add_eqv_congr'
      (sum_congr f g n (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h n (Nat.lt_succ_self n))

/-- Left rectangles on an arbitrary supplied finite grid. -/
def monomialLeft (x : Nat → Q') (δ : Q') (k n : Nat) : Q' :=
  finSum (fun j => δ * qpow (x j) k) n

private theorem right_left_pin (x : Nat → Q') (δ : Q') (k n : Nat) :
    finSum (fun j => δ * qpow (x (j+1)) k) n ≈
      monomialLeft x δ k n + δ * (qpow (x n) k + -qpow (x 0) k) := by
  induction n with
  | zero =>
      change (0 : Q') ≈ 0 + δ * (qpow (x 0) k + -qpow (x 0) k)
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 0 _ 0 (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left δ _ 0 (Q'.add_neg_self_eqv _)) (Q'.mul_zero_eqv δ)))
        (Q'.eqv_refl 0))
  | succ n ih =>
      change finSum (fun j => δ * qpow (x (j+1)) k) n + δ * qpow (x (n+1)) k ≈ _
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ ih) ?_
      unfold monomialLeft
      rw [finSum_succ]
      ring_qeqv

/-- Uniform error for a monomial on a nonnegative unit-interval grid.
The actual equal cell widths are hypotheses, not an integration oracle. -/
theorem monomial_quadrature_error (x : Nat → Q') (δ : Q') (k n : Nat)
    (hδ : (0 : Q') ≤ δ)
    (hx : ∀ j, j ≤ n → (0 : Q') ≤ x j)
    (hmono : ∀ j, j < n → x j ≤ x (j+1))
    (hstep : ∀ j, j < n → x (j+1) + -x j ≈ δ)
    (hunit : x n ≤ (1 : Q')) :
    Q'.abs (monomialIncrement (x 0) (x n) k + -monomialLeft x δ k n) ≤ δ := by
  let I := finSum (fun j => monomialIncrement (x j) (x (j+1)) k) n
  have hl : monomialLeft x δ k n ≤ I := by
    apply sum_le
    intro j hj
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ (hstep j hj)))
      (leftRectangle_le_increment (hx j (Nat.le_of_lt hj)) (hmono j hj) k)
  have hr : I ≤ finSum (fun j => δ * qpow (x (j+1)) k) n := by
    apply sum_le
    intro j hj
    exact Q'.le_trans' _ _ _
      (increment_le_rightRectangle (hx j (Nat.le_of_lt hj)) (hmono j hj) k)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (hstep j hj)))
  have ht : I ≈ monomialIncrement (x 0) (x n) k :=
    finSum_monomialIncrement_telescope x k n
  have hend : qpow (x n) k + -qpow (x 0) k ≤ (1 : Q') := by
    have hneg : -qpow (x 0) k ≤ (0 : Q') := by
      exact Q'.neg_le_neg (qpow_nonneg _ (hx 0 (Nat.zero_le n)) k)
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add (qpow_le_one (hx n (Nat.le_refl n)) hunit k) hneg)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))
  have hup : monomialIncrement (x 0) (x n) k ≤ monomialLeft x δ k n + δ := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ht) ?_
    refine Q'.le_trans' _ _ _ hr ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (right_left_pin x δ k n)) ?_
    exact Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ δ hend hδ) (Q'.le_of_eqv (Q'.mul_one_eqv δ)))
  have hlo : (0 : Q') ≤ monomialIncrement (x 0) (x n) k + -monomialLeft x δ k n :=
    Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ hl (Q'.le_of_eqv ht))
  exact Q'.abs_le (Q'.le_trans' _ _ _ (Q'.neg_le_neg hδ) hlo)
    (Q'.sub_le_of_le_add hup)

/-- Signed polynomial rectangles, kept in the original coefficient order. -/
def polynomialLeft : Nat → Poly → (Nat → Q') → Q' → Nat → Q'
  | _, [], _, _, _ => 0
  | k, c::cs, x, δ, n => c * monomialLeft x δ k n + polynomialLeft (k+1) cs x δ n

theorem polynomial_quadrature_error (x : Nat → Q') (δ : Q') (n : Nat)
    (hδ : (0 : Q') ≤ δ)
    (hx : ∀ j, j ≤ n → (0 : Q') ≤ x j)
    (hmono : ∀ j, j < n → x j ≤ x (j+1))
    (hstep : ∀ j, j < n → x (j+1) + -x j ≈ δ)
    (hunit : x n ≤ (1 : Q')) : ∀ k p,
    Q'.abs (primitiveIncrement k p (x 0) (x n) + -polynomialLeft k p x δ n)
      ≤ δ * coefficientBudget p
  | _, [] => Q'.ge_of_eqv (Q'.mul_zero_eqv δ)
  | k, c::cs => by
      let A := monomialIncrement (x 0) (x n) k
      let B := monomialLeft x δ k n
      let C := primitiveIncrement (k+1) cs (x 0) (x n)
      let D := polynomialLeft (k+1) cs x δ n
      have he : (c*A+C) + -(c*B+D) ≈ c*(A + -B) + (C + -D) := by ring_qeqv
      have hc : Q'.abs (c * (A + -B)) ≤ Q'.abs c * δ :=
        Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (monomial_quadrature_error x δ k n hδ hx hmono hstep hunit) (Q'.abs_nonneg c))
      have hi := polynomial_quadrature_error x δ n hδ hx hmono hstep hunit (k+1) cs
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr he))
        (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
          (Q'.le_trans' _ _ _ (Q'.add_le_add hc hi) (Q'.le_of_eqv (by
            change Q'.abs c * δ + δ * coefficientBudget cs ≈ δ * (Q'.abs c + coefficientBudget cs)
            ring_qeqv))))

theorem polynomialLeft_samples (k : Nat) (p : Poly) (x : Nat → Q') (δ : Q') (n : Nat) :
    polynomialLeft k p x δ n ≈ finSum (fun j => δ * powerEval k p (x j)) n := by
  induction p generalizing k with
  | nil => exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (finSum_eqv_congr _ (fun _ => 0) (fun _ => Q'.mul_zero_eqv δ) n)
      (Q'.eqv_of_eq (finSum_zero_seq n)))
  | cons c cs ih =>
      change c * monomialLeft x δ k n + polynomialLeft (k+1) cs x δ n ≈ _
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (const_mul_finSum _ c n) (ih (k+1))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (finSum_add _ _ n)) ?_
      apply finSum_eqv_congr
      intro j
      change c * (δ * qpow (x j) k) + δ * powerEval (k+1) cs (x j) ≈
        δ * (c * qpow (x j) k + powerEval (k+1) cs (x j))
      ring_qeqv

/-- Explicit N+1-cell mesh of the actual rational interval. -/
def intervalMesh (a b : Q') (N : Nat) : Q' := (b + -a) * Q'.invSucc N

def intervalNode (a b : Q') (N j : Nat) : Q' :=
  a + intervalMesh a b N * Q'.ofNat j

theorem node_zero (a b : Q') (N : Nat) : intervalNode a b N 0 ≈ a := by
  unfold intervalNode
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a _ 0 (Q'.mul_zero_eqv _)) (Q'.eqv_of_eq (Q'.add_zero' a))

theorem node_endpoint (a b : Q') (N : Nat) : intervalNode a b N (N+1) ≈ b := by
  unfold intervalNode intervalMesh
  have hc : Q'.invSucc N * Q'.ofNat (N+1) ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.ofNat_succ_mul_invSucc N)
  refine Q'.eqv_trans _ (a + (b + -a) * (Q'.invSucc N * Q'.ofNat (N+1))) _ ?_ ?_
  · ring_qeqv
  · refine Q'.eqv_trans _ (a + (b + -a) * 1) _
      (Q'.add_eqv_congr_left a _ _ (Q'.mul_eqv_congr_left _ _ _ hc)) ?_
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.add (.var 1) (.neg (.var 0))) (.const 1)))
      (.var 1) (by decide) (fun | 0 => a | _ => b)

theorem node_step (a b : Q') (N j : Nat) :
    intervalNode a b N (j+1) + -intervalNode a b N j ≈ intervalMesh a b N := by
  unfold intervalNode
  refine Q'.eqv_trans _
    ((a + intervalMesh a b N * (Q'.ofNat j + 1)) + -(a + intervalMesh a b N * Q'.ofNat j)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left a _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.ofNat_add_eqv j 1)))
  · exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.var 1) (.add (.var 2) (.const 1))))
        (.neg (.add (.var 0) (.mul (.var 1) (.var 2)))))
      (.var 1) (by decide) (fun | 0 => a | 1 => intervalMesh a b N | _ => Q'.ofNat j)

theorem mesh_nonnegative {a b : Q'} (hab : a ≤ b) (N : Nat) :
    (0 : Q') ≤ intervalMesh a b N :=
  Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hab) (invSucc_nonnegative N)

theorem node_mono {a b : Q'} (hab : a ≤ b) (N : Nat) {j k : Nat} (hjk : j ≤ k) :
    intervalNode a b N j ≤ intervalNode a b N k :=
  Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
    (CReal.ofNat_le_ofNat hjk) (mesh_nonnegative hab N))

theorem node_in_interval {a b : Q'} (hab : a ≤ b) (N j : Nat) (hj : j ≤ N+1) :
    a ≤ intervalNode a b N j ∧ intervalNode a b N j ≤ b := by
  constructor
  · exact Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ (mesh_nonnegative hab N) (zero_le_ofNat j))
  · exact Q'.le_trans' _ _ _ (node_mono hab N hj) (Q'.le_of_eqv (node_endpoint a b N))

theorem mesh_le_inverse {a b : Q'}
    (ha : (0 : Q') ≤ a) (hb : b ≤ (1 : Q')) (N : Nat) :
    intervalMesh a b N ≤ Q'.invSucc N := by
  have hwidth : b + -a ≤ (1 : Q') := by
    exact Q'.le_trans' _ _ _ (Q'.add_le_add hb (Q'.neg_le_neg ha))
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hwidth (invSucc_nonnegative N))
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

private theorem qpow_congr {a b : Q'} (h : a ≈ b) : ∀ k, qpow a k ≈ qpow b k
  | 0 => Q'.eqv_refl _
  | k+1 => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ a (qpow_congr h k)) (Q'.mul_eqv_congr_left _ _ _ h)

private theorem primitive_endpoints_congr (k : Nat) (p : Poly)
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    primitiveIncrement k p a b ≈ primitiveIncrement k p a' b' := by
  induction p generalizing k with
  | nil => exact Q'.eqv_refl _
  | cons c cs ih =>
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left c _ _ (Q'.mul_eqv_congr_left (Q'.invSucc k) _ _
          (Q'.add_eqv_congr' (qpow_congr hb (k+1)) (Q'.neg_eqv_congr _ _ (qpow_congr ha (k+1))))))
        (ih (k+1))

private theorem le_add_of_sub_le {p q ε : Q'} (h : q + -p ≤ ε) : q ≤ p + ε := by
  have hs := Q'.add_le_add_right _ _ p h
  have he : ((q + -p) + p) ≈ q := RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
    (fun | 0 => q | _ => p)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.add_comm_eqv ε p)))

/-- The exact primitive of any pointwise nonnegative signed polynomial is
nonnegative on every ordered rational subinterval of [0,1]. -/
theorem primitiveIncrement_nonnegative (p : Poly) (a b : Q')
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) (hb : b ≤ (1 : Q'))
    (hp : ∀ x : Q', a ≤ x → x ≤ b → (0 : Q') ≤ eval p x) :
    (0 : Q') ≤ primitiveIncrement 0 p a b := by
  let B := (coefficientBudget p).num.toNat
  have hbudget : coefficientBudget p ≤ Q'.ofNat B :=
    RatNat.le_ofNat_toNat _ (coefficientBudget_nonnegative p)
  apply Q'.le_of_le_add_mul_invSucc 0 (primitiveIncrement 0 p a b) B
  intro N
  let x := intervalNode a b N
  let δ := intervalMesh a b N
  let R := polynomialLeft 0 p x δ (N+1)
  have hn : ∀ j, j ≤ N+1 → (0 : Q') ≤ x j := fun j hj =>
    Q'.le_trans' _ _ _ ha (node_in_interval hab N j hj).1
  have he := polynomial_quadrature_error x δ (N+1) (mesh_nonnegative hab N) hn
    (fun j _ => node_mono hab N (Nat.le_succ j)) (fun j _ => node_step a b N j)
    (Q'.le_trans' _ _ _ (node_in_interval hab N (N+1) (Nat.le_refl _)).2 hb) 0 p
  have hpin : primitiveIncrement 0 p (x 0) (x (N+1)) ≈ primitiveIncrement 0 p a b :=
    primitive_endpoints_congr 0 p (node_zero a b N) (node_endpoint a b N)
  have herr : Q'.abs (primitiveIncrement 0 p a b + -R) ≤ Q'.ofNat B * Q'.invSucc N := by
    refine Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv
        (Q'.abs_eqv_congr (Q'.add_eqv_congr_right _ _ (-R) hpin))) he) ?_
    refine Q'.le_trans' _ (Q'.invSucc N * coefficientBudget p) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg_right _ _ _ (mesh_le_inverse ha hb N)
        (coefficientBudget_nonnegative p)
    · exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hbudget (invSucc_nonnegative N))
        (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
  have hR : (0 : Q') ≤ R := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (polynomialLeft_samples 0 p x δ (N+1)))
    apply sum_nonnegative
    intro j hj
    have hinterval := node_in_interval hab N j (Nat.le_of_lt hj)
    have hev : powerEval 0 p (x j) ≈ eval p (x j) :=
      Q'.eqv_trans _ _ _ (powerEval_horner 0 p (x j)) (Q'.one_mul_eqv _)
    exact Q'.mul_nonneg _ _ (mesh_nonnegative hab N)
      (Q'.le_trans' _ _ _ (hp _ hinterval.1 hinterval.2) (Q'.ge_of_eqv hev))
  have hback : R + -primitiveIncrement 0 p a b ≤ Q'.ofNat B * Q'.invSucc N := by
    have heq : R + -primitiveIncrement 0 p a b ≈ -(primitiveIncrement 0 p a b + -R) :=
      RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 1) (.neg (.var 0)))
        (.neg (.add (.var 0) (.neg (.var 1)))) (by decide)
        (fun | 0 => primitiveIncrement 0 p a b | _ => R)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
      (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) herr)
  exact Q'.le_trans' _ _ _ hR (le_add_of_sub_le hback)

private theorem primitive_scaled (k : Nat) (p : Poly) (a b : Q') :
    primitiveIncrement k (scaleFrom (k+1) p) a b ≈
      powerEval (k+1) p b + -powerEval (k+1) p a := by
  induction p generalizing k with
  | nil => change (0 : Q') ≈ 0 + -0; decide
  | cons c cs ih =>
      change (Q'.ofNat (k+1)*c) * (Q'.invSucc k * (qpow b (k+1) + -qpow a (k+1))) +
        primitiveIncrement (k+1) (scaleFrom (k+1+1) cs) a b ≈ _
      have hc : (Q'.ofNat (k+1)*c) * (Q'.invSucc k * (qpow b (k+1) + -qpow a (k+1))) ≈
          c * (qpow b (k+1) + -qpow a (k+1)) := by
        refine Q'.eqv_trans _
          (c * (Q'.ofNat (k+1)*Q'.invSucc k) * (qpow b (k+1) + -qpow a (k+1))) _ ?_ ?_
        · ring_qeqv
        · exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left c _ _ (Q'.ofNat_succ_mul_invSucc k)))
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv c))
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hc (ih (k+1))) ?_
      change c * (qpow b (k+1) + -qpow a (k+1)) +
        (powerEval (k+1+1) cs b + -powerEval (k+1+1) cs a) ≈
        (c*qpow b (k+1)+powerEval (k+1+1) cs b) + -(c*qpow a (k+1)+powerEval (k+1+1) cs a)
      ring_qeqv

/-- Exact finite fundamental-theorem identity for the LITERAL formal
derivative. No analytic derivative or primitive pin is supplied as input. -/
theorem formal_derivative_increment (p : Poly) (a b : Q') :
    primitiveIncrement 0 (pderiv p) a b ≈ eval p b + -eval p a := by
  cases p with
  | nil => change (0 : Q') ≈ 0 + -0; decide
  | cons c cs =>
      refine Q'.eqv_trans _ _ _ (primitive_scaled 0 cs a b) ?_
      have he : powerEval 1 cs b + -powerEval 1 cs a ≈ b*eval cs b + -(a*eval cs a) :=
        Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (powerEval_horner 1 cs b)
            (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv b)))
          (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (powerEval_horner 1 cs a)
            (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv a))))
      refine Q'.eqv_trans _ _ _ he ?_
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 0) (.var 2))))
        (.add (.add (.var 4) (.mul (.var 1) (.var 3)))
          (.neg (.add (.var 4) (.mul (.var 0) (.var 2))))) (by decide)
        (fun | 0 => a | 1 => b | 2 => eval cs a | 3 => eval cs b | _ => c)

/-- Constructive rational interval monotonicity produced from the actual
formal derivative's pointwise sign, for every finite signed polynomial. -/
theorem monotone_of_formal_derivative_nonnegative (p : Poly) (a b : Q')
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) (hb : b ≤ (1 : Q'))
    (hp : ∀ x : Q', a ≤ x → x ≤ b → (0 : Q') ≤ eval (pderiv p) x) :
    eval p a ≤ eval p b := by
  have h := primitiveIncrement_nonnegative (pderiv p) a b ha hab hb hp
  have hs : (0 : Q') ≤ eval p b + -eval p a :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv (formal_derivative_increment p a b))
  have had := Q'.add_le_add_left (eval p a) _ _ hs
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _))) ?_
  exact Q'.le_trans' _ _ _ had (Q'.le_of_eqv
    (RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1) (by decide)
      (fun | 0 => eval p a | _ => eval p b)))

end YMGap.Continuum.RationalPolynomialIntervalOrder

#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.powerEval
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.primitiveIncrement
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.coefficientBudget
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.coefficientBudget_nonnegative
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.monomialLeft
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.polynomialLeft
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.intervalMesh
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.intervalNode
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.powerEval_horner
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.monomial_quadrature_error
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.polynomial_quadrature_error
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.polynomialLeft_samples
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.primitiveIncrement_nonnegative
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.formal_derivative_increment
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.monotone_of_formal_derivative_nonnegative
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.node_zero
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.node_endpoint
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.node_step
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.mesh_nonnegative
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.node_mono
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.node_in_interval
#print axioms YMGap.Continuum.RationalPolynomialIntervalOrder.mesh_le_inverse
