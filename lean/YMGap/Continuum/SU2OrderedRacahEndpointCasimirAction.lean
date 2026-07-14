/-
# Endpoint pair-Casimir action on the ordered Racah carrier

The ordered right channel of inner contraction order zero is a single outer
Hahn row.  Acting on its first two input legs can therefore be reduced to the
all-order adjacent-difference theorem.  The resulting coefficient is the
transpose (raw-coordinate) Jacobi coefficient, not the coefficient of the
dual reconstructed section.  This module keeps that normalization distinction
literal and denominator-free.

The general endpoint factorization isolates one remaining contiguous Hahn
identity.  At outer order one that identity collapses to the order-zero row,
giving a complete symbolic-label endpoint action rather than a finite-label
audit.
-/

import YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2OrderedRacahEndpointCasimirAction

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

private theorem ofNat_add_eq (a b : Nat) :
    Q'.ofNat (a + b) = Q'.ofNat a + Q'.ofNat b := by
  change Q'.ofNat (a + b) = Q'.add (Q'.ofNat a) (Q'.ofNat b)
  unfold Q'.ofNat Q'.add Q'.den
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  simp

private theorem ofNat_mul_eq (a b : Nat) :
    Q'.ofNat (a * b) = Q'.ofNat a * Q'.ofNat b := by
  change Q'.ofNat (a * b) = Q'.mul (Q'.ofNat a) (Q'.ofNat b)
  unfold Q'.ofNat Q'.mul Q'.den
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]

private theorem ofNat_sub_eq (a b : Nat) (h : b ≤ a) :
    Q'.ofNat (a - b) = Q'.ofNat a + -(Q'.ofNat b) := by
  change Q'.ofNat (a - b) =
    Q'.add (Q'.ofNat a) (Q'.neg (Q'.ofNat b))
  have hcast : Int.ofNat (a - b) = Int.ofNat a - Int.ofNat b :=
    Int.ofNat_sub h
  unfold Q'.ofNat Q'.add Q'.neg Q'.den
  rw [hcast]
  simp [Int.sub_eq_add_neg]

private def innerAffineLHS : PolyExpr :=
  .add
    (.mul (.var 2) (.add (.var 1) (.neg (.var 3))))
    (.neg (.mul (.add (.var 0) (.neg (.var 2))) (.var 3)))

private def innerAffineRHS : PolyExpr :=
  .add
    (.mul (.add (.var 0) (.var 1)) (.var 2))
    (.neg (.mul (.var 0) (.add (.var 2) (.var 3))))

private theorem innerAffine_normal :
    normalize innerAffineLHS = normalize innerAffineRHS := by decide

private theorem inner_affine_ring (B C J L : Q') :
    J * (C + -L) + -((B + -J) * L) ≈
      (B + C) * J + -(B * (J + L)) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then B else if r = 1 then C else if r = 2 then J else L
  have h := poly_identity_of_normal_eq innerAffineLHS innerAffineRHS
    innerAffine_normal ρ
  simpa [innerAffineLHS, innerAffineRHS, eval, ρ] using h

private theorem neg_mul_left (L V : Q') : -(L * V) ≈ (-L) * V := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den, neg_num,
    Int.neg_mul]

private def endpointRearrangeLHS : PolyExpr :=
  .mul (.var 0)
    (.add
      (.mul (.mul (.var 2) (.var 4)) (.mul (.var 6) (.var 7)))
      (.mul (.mul (.var 3) (.add (.var 1) (.neg (.var 4))))
        (.mul (.neg (.var 6)) (.var 8))))

private def endpointRearrangeRHS : PolyExpr :=
  .mul (.var 6)
    (.add
      (.mul
        (.add (.mul (.var 0) (.var 4))
          (.neg (.mul (.var 1) (.var 5))))
        (.add (.mul (.var 2) (.var 7)) (.mul (.var 3) (.var 8))))
      (.neg
        (.mul (.var 1)
          (.add
            (.mul (.mul (.var 3)
              (.add (.var 0) (.neg (.var 5)))) (.var 8))
            (.mul (.neg (.mul (.var 2) (.var 5))) (.var 7))))))

private theorem endpointRearrange_normal :
    normalize endpointRearrangeLHS = normalize endpointRearrangeRHS := by decide

private theorem endpoint_rearrange_ring
    (F B A I J T L U V : Q') :
    F * (A * J * (L * U) + I * (B + -J) * ((-L) * V)) ≈
      L * ((F * J + -(B * T)) * (A * U + I * V) +
        -(B * (I * (F + -T) * V + -(A * T) * U))) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then F else if r = 1 then B else if r = 2 then A else
    if r = 3 then I else if r = 4 then J else if r = 5 then T else
    if r = 6 then L else if r = 7 then U else V
  have h := poly_identity_of_normal_eq endpointRearrangeLHS
    endpointRearrangeRHS endpointRearrange_normal ρ
  simpa [endpointRearrangeLHS, endpointRearrangeRHS, eval, ρ] using h

/-- The raw order-zero right-associated coefficient carrier.  Its inner Hahn
row is one, leaving only the outer row on the combined shell `j+l`. -/
def endpointZeroCarrier (a b c q i j l : Nat) : Q' :=
  transvectFactorialCoeff a (b + c) q i (j + l)

/-- The reduced carrier produced by the two adjacent outer-row differences.
The next endpoint lemma identifies it with a neighboring right channel after
one further all-order contiguous identity. -/
def endpointReducedCarrier (a b c q i j l : Nat) : Q' :=
  Q'.ofNat (a - i) *
      transvectFactorialCoeff (a - 1) (b + c - 1) (q - 1) i (j + l - 1) +
    Q'.ofNat i *
      transvectFactorialCoeff (a - 1) (b + c - 1) (q - 1) (i - 1) (j + l)

/-- The raw neighboring channel carrier at inner contraction order one. -/
def endpointOneCarrier (a b c q i j l : Nat) : Q' :=
  transvectFactorialCoeff b c 1 j l *
    transvectFactorialCoeff a (b + c - 2) (q - 1) i (j + l - 1)

private theorem inner_order_one_affine (b c j l : Nat)
    (hj : j ≤ b) (hl : l ≤ c) :
    transvectFactorialCoeff b c 1 j l ≈
      Q'.ofNat (b + c) * Q'.ofNat j +
        -(Q'.ofNat b * Q'.ofNat (j + l)) := by
  have h := transvectFactorialCoeff_one b c j l
  rw [ofNat_mul_eq j (c - l), ofNat_sub_eq c l hl,
    ofNat_mul_eq (b - j) l, ofNat_sub_eq b j hj] at h
  refine Q'.eqv_trans _ _ _ h ?_
  rw [ofNat_add_eq b c, ofNat_add_eq j l]
  exact inner_affine_ring _ _ _ _

private theorem factorial_recurrence_product (m n k i j : Nat) :
    (Q'.ofNat i * Q'.ofNat (n - j)) *
        transvectFactorialCoeff (m - 1) (n - 1) k (i - 1) j +
      (-(Q'.ofNat (m - i) * Q'.ofNat j)) *
        transvectFactorialCoeff (m - 1) (n - 1) k i (j - 1) ≈
      transvectFactorialCoeff m n (k + 1) i j := by
  have h := transvectFactorialCoeff_succ m n k i j
  rw [ofNat_mul_eq i (n - j), ofNat_mul_eq (m - i) j] at h
  exact h

private theorem reverse_adjacent {k m n i j : Nat}
    (hkm : k ≤ m) (hkn : k ≤ n)
    (hi : 0 < i) (hj : j < n) (him : i ≤ m) :
    transvectFactorialCoeff m n k (i - 1) (j + 1) +
        -transvectFactorialCoeff m n k i j ≈
      -(Q'.ofNat (k * (m + n - k + 1)) *
        transvectFactorialCoeff (m - 1) (n - 1) (k - 1) (i - 1) j) := by
  have h := transvectFactorialCoeff_adjacent k m n (i - 1) (j + 1)
    hkm hkn (by omega) (by omega) (by omega)
  have hneg := Q'.neg_eqv_congr _ _ h
  have hneg' :
      -(transvectFactorialCoeff m n k i j +
        -transvectFactorialCoeff m n k (i - 1) (j + 1)) ≈
        -(Q'.ofNat (k * (m + n - k + 1)) *
          transvectFactorialCoeff (m - 1) (n - 1) (k - 1) (i - 1) j) := by
    simpa only [show i - 1 + 1 = i by omega,
      show j + 1 - 1 = j by omega] using hneg
  refine Q'.eqv_trans _
    (-(transvectFactorialCoeff m n k i j +
      -transvectFactorialCoeff m n k (i - 1) (j + 1))) _ ?_ hneg'
  ring_qeqv

private theorem endpoint_rearrange
    (F B A I J T BJ FT L U V H H1 : Q')
    (hBJ : BJ ≈ B + -J) (hFT : FT ≈ F + -T)
    (hH : I * FT * V + -(A * T) * U ≈ H)
    (hH1 : H1 ≈ F * J + -(B * T)) :
    F * (A * J * (L * U) + I * BJ * ((-L) * V)) ≈
      L * (H1 * (A * U + I * V) + -(B * H)) := by
  refine Q'.eqv_trans _
    (F * (A * J * (L * U) + I * (B + -J) * ((-L) * V))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left F _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ ((-L) * V)
          (Q'.mul_eqv_congr_left I _ _ hBJ)))
  refine Q'.eqv_trans _
    (L * ((F * J + -(B * T)) * (A * U + I * V) +
      -(B * (I * (F + -T) * V + -(A * T) * U)))) _
    (endpoint_rearrange_ring F B A I J T L U V) ?_
  exact Q'.mul_eqv_congr_left L _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ (A * U + I * V)
        (Q'.eqv_symm hH1))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left B _ _
          (Q'.eqv_trans _ (I * FT * V + -(A * T) * U) _
            (Q'.add_eqv_congr' 
              (Q'.mul_eqv_congr_right _ _ V
                (Q'.mul_eqv_congr_left I _ _ (Q'.eqv_symm hFT)))
              (Q'.eqv_refl _)) hH))))

/-- **General symbolic endpoint factorization.**  On every strict physical
source coordinate, multiplying the first-pair exchange action by the combined
inner degree `b+c` isolates the order-one inner Hahn row and one reduced outer
carrier.  No numerical label or measured constant occurs in the identity. -/
theorem endpoint_pairExchange_factorization
    (a b c q i j l : Nat)
    (hq0 : 0 < q) (hqa : q ≤ a) (hqf : q ≤ b + c)
    (hi0 : 0 < i) (hia : i < a)
    (hj0 : 0 < j) (hjb : j < b) (hl : l ≤ c) :
    Q'.ofNat (b + c) *
        pairExchange a b
          (fun x y => endpointZeroCarrier a b c q x y l) i j ≈
      Q'.ofNat (q * (a + (b + c) - q + 1)) *
        (transvectFactorialCoeff b c 1 j l *
            endpointReducedCarrier a b c q i j l +
          -(Q'.ofNat b * endpointZeroCarrier a b c q i j l)) := by
  let f := b + c
  let t := j + l
  let H : Q' := transvectFactorialCoeff a f q i t
  let U : Q' :=
    transvectFactorialCoeff (a - 1) (f - 1) (q - 1) i (t - 1)
  let V : Q' :=
    transvectFactorialCoeff (a - 1) (f - 1) (q - 1) (i - 1) t
  let L : Q' := Q'.ofNat (q * (a + f - q + 1))
  let A : Q' := Q'.ofNat (a - i)
  let I : Q' := Q'.ofNat i
  let J : Q' := Q'.ofNat j
  let B : Q' := Q'.ofNat b
  let T : Q' := Q'.ofNat t
  let F : Q' := Q'.ofNat f
  let BJ : Q' := Q'.ofNat (b - j)
  let FT : Q' := Q'.ofNat (f - t)
  let H1 : Q' := transvectFactorialCoeff b c 1 j l

  have ht0 : 0 < t := by dsimp only [t]; omega
  have htf : t < f := by dsimp only [t, f]; omega
  have ht_le : t ≤ f := by omega
  have hj_le : j ≤ b := by omega

  have hfwd0 := transvectFactorialCoeff_adjacent q a f i t
    hqa hqf hia ht0 ht_le
  have hfwd :
      transvectFactorialCoeff a f q (i + 1) (t - 1) + -H ≈ L * U := by
    simpa only [H, L, U] using hfwd0
  have hbwd0 := reverse_adjacent (k := q) (m := a) (n := f)
    (i := i) (j := t) hqa hqf hi0 htf (by omega)
  have hbwd :
      transvectFactorialCoeff a f q (i - 1) (t + 1) + -H ≈ (-L) * V := by
    refine Q'.eqv_trans _ (-(L * V)) _
      (by simpa only [H, L, V] using hbwd0) (neg_mul_left L V)

  have hrec0 := factorial_recurrence_product a f (q - 1) i t
  have hrec : I * FT * V + -(A * T) * U ≈ H := by
    simpa only [I, FT, V, A, T, U, H,
      show q - 1 + 1 = q by omega] using hrec0
  have hinner : H1 ≈ F * J + -(B * T) := by
    simpa only [H1, F, J, B, T, f, t] using
      inner_order_one_affine b c j l hj_le hl
  have hBJ : BJ ≈ B + -J := by
    rw [show BJ = Q'.ofNat (b - j) by rfl,
      show B = Q'.ofNat b by rfl, show J = Q'.ofNat j by rfl,
      ofNat_sub_eq b j hj_le]
    exact Q'.eqv_refl _
  have hFT : FT ≈ F + -T := by
    rw [show FT = Q'.ofNat (f - t) by rfl,
      show F = Q'.ofNat f by rfl, show T = Q'.ofNat t by rfl,
      ofNat_sub_eq f t (by omega)]
    exact Q'.eqv_refl _

  unfold pairExchange endpointZeroCarrier
  change F *
      (A * J *
          (transvectFactorialCoeff a f q (i + 1) (j - 1 + l) + -H) +
        I * BJ *
          (transvectFactorialCoeff a f q (i - 1) (j + 1 + l) + -H)) ≈
    L * (H1 *
        (A * transvectFactorialCoeff (a - 1) (f - 1) (q - 1)
              i (j + l - 1) +
          I * transvectFactorialCoeff (a - 1) (f - 1) (q - 1)
              (i - 1) (j + l)) +
      -(B * H))
  rw [show j - 1 + l = t - 1 by dsimp only [t]; omega,
    show j + 1 + l = t + 1 by dsimp only [t]; omega,
    show j + l - 1 = t - 1 by rfl,
    show j + l = t by rfl]
  refine Q'.eqv_trans _
    (F * (A * J * (L * U) + I * BJ * ((-L) * V))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left F _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (A * J) _ _ hfwd)
        (Q'.mul_eqv_congr_left (I * BJ) _ _ hbwd))
  · simpa only [F, A, I, J, BJ, L, U, V, H, H1, B,
      endpointReducedCarrier, endpointZeroCarrier, f, t] using
      endpoint_rearrange F B A I J T BJ FT L U V H H1
        hBJ hFT hrec hinner

private theorem reducedCarrier_order_one
    (a b c i j l : Nat) (hi : i ≤ a) :
    endpointReducedCarrier a b c 1 i j l ≈ Q'.ofNat a := by
  have h0 := transvectFactorialCoeff_zero
    (a - 1) (b + c - 1) i (j + l - 1)
  have h1 := transvectFactorialCoeff_zero
    (a - 1) (b + c - 1) (i - 1) (j + l)
  unfold endpointReducedCarrier
  simp only [Nat.one_sub]
  refine Q'.eqv_trans _
    (Q'.ofNat (a - i) * 1 + Q'.ofNat i * 1) _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ h0)
      (Q'.mul_eqv_congr_left _ _ _ h1)) ?_
  rw [ofNat_sub_eq a i hi]
  refine Q'.eqv_trans _
    ((Q'.ofNat a + -Q'.ofNat i) + Q'.ofNat i) _
    (Q'.add_eqv_congr'
      (Q'.mul_one_eqv _) (Q'.mul_one_eqv _)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat a + (-Q'.ofNat i + Q'.ofNat i)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (Q'.ofNat a + 0) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv _)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- **Complete outer-order-one endpoint action.**  For arbitrary symbolic
labels and every strict source coordinate, the raw right-channel endpoint has
exact neighbor numerator `a*(a+b+c)` and diagonal numerator
`-b*(a+b+c)`, with common denominator `b+c`.  In the fundamental block this
is the raw coefficient `3/2`; the dual section coefficient is its Gram-gauge
transpose `1/2`. -/
theorem endpoint_pairExchange_order_one
    (a b c i j l : Nat)
    (ha : 0 < a) (hbc : 0 < b + c)
    (hi0 : 0 < i) (hia : i < a)
    (hj0 : 0 < j) (hjb : j < b) (hl : l ≤ c) :
    Q'.ofNat (b + c) *
        pairExchange a b
          (fun x y => endpointZeroCarrier a b c 1 x y l) i j ≈
      Q'.ofNat (a + (b + c)) *
        (Q'.ofNat a * transvectFactorialCoeff b c 1 j l +
          -(Q'.ofNat b * endpointZeroCarrier a b c 1 i j l)) := by
  have hfactor := endpoint_pairExchange_factorization
    a b c 1 i j l (by omega) (by omega) (by omega)
      hi0 hia hj0 hjb hl
  have hred := reducedCarrier_order_one a b c i j l (by omega)
  refine Q'.eqv_trans _
    (Q'.ofNat (1 * (a + (b + c) - 1 + 1)) *
      (transvectFactorialCoeff b c 1 j l *
          endpointReducedCarrier a b c 1 i j l +
        -(Q'.ofNat b * endpointZeroCarrier a b c 1 i j l))) _
    hfactor ?_
  rw [show 1 * (a + (b + c) - 1 + 1) = a + (b + c) by omega]
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _
        (transvectFactorialCoeff b c 1 j l * Q'.ofNat a) _
        (Q'.mul_eqv_congr_left _ _ _ hred)
        (Q'.mul_comm_eqv _ _))
      (Q'.eqv_refl _))

end YMGap.Continuum.SU2OrderedRacahEndpointCasimirAction

#print axioms YMGap.Continuum.SU2OrderedRacahEndpointCasimirAction.endpoint_pairExchange_factorization
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointCasimirAction.endpoint_pairExchange_order_one
