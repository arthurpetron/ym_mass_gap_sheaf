/-
# All-order adjacent-column law for the factorial Hahn carrier

This module proves the general forward-difference identity for the actual
finite alternating factorial carrier.  The proof is constructive induction
on the contraction order through the already proved universal Pascal/falling-
factorial recurrence.  At a coordinate edge the absent induction branch is
multiplied by an exactly zero natural coefficient; no division or choice is
used.
-/

import YMGap.Continuum.SU2GeneralHahnAdjacentDifference
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2GeneralHahnAdjacentDifference
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

private theorem zero_scaled (A B : Q') :
    ((0 : Q') * A).eqv ((0 : Q') * B) := by
  exact Q'.eqv_trans _ 0 _ (q_zero_mul A) (Q'.eqv_symm (q_zero_mul B))

private def successorDifferenceLHS : PolyExpr :=
  .add
    (.add (.mul (.var 0) (.var 4)) (.mul (.neg (.var 1)) (.var 5)))
    (.neg (.add (.mul (.var 2) (.var 6)) (.mul (.neg (.var 3)) (.var 4))))

private def successorDifferenceRHS : PolyExpr :=
  .add
    (.mul
      (.add (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2))) (.var 3))
      (.var 4))
    (.add
      (.mul (.neg (.var 1)) (.add (.var 5) (.neg (.var 4))))
      (.mul (.var 2) (.add (.var 4) (.neg (.var 6)))))

private theorem successorDifference_normal :
    normalize successorDifferenceLHS = normalize successorDifferenceRHS := by
  decide

private theorem successor_difference_rearrange
    (Ap Bp A B X Y Z : Q') :
    ((Ap * X + (-Bp) * Y) + -(A * Z + (-B) * X)) ≈
      (Ap + -Bp + -A + B) * X +
        (((-Bp) * (Y + -X)) + A * (X + -Z)) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then Ap else if r = 1 then Bp else if r = 2 then A else
    if r = 3 then B else if r = 4 then X else if r = 5 then Y else Z
  have h := poly_identity_of_normal_eq successorDifferenceLHS
    successorDifferenceRHS successorDifference_normal ρ
  simpa [successorDifferenceLHS, successorDifferenceRHS, eval, ρ] using h

private theorem lower_branches_factor
    (S L A B X U V : Q') :
    (S * X + (((-B) * (L * U)) + A * (L * V))) ≈
      S * X + L * (A * V + (-B) * U) := by
  ring_qeqv

private theorem scale_sum_factor (S L T X : Q')
    (hSL : (S + L).eqv T) :
    (S * X + L * X).eqv (T * X) := by
  refine Q'.eqv_trans _ ((S + L) * X) _ ?_ ?_
  · ring_qeqv
  · exact Q'.mul_eqv_congr_right _ _ _ hSL

private theorem allOrderScale_nat
    (s m n : Nat) (hm : s + 2 ≤ m) (hn : s + 2 ≤ n) :
    (m + n) +
        (s + 1) * ((m - 1) + (n - 1) - (s + 1) + 1) =
      (s + 2) * (m + n - (s + 2) + 1) := by
  let q := m + n - (s + 2)
  have hmn : m + n = (s + 2) + q := by
    dsimp only [q]
    omega
  have hlow : (m - 1) + (n - 1) - (s + 1) + 1 = q := by
    dsimp only [q]
    omega
  have hsucc : (s + 2) * q = (s + 1) * q + q := by
    have := Nat.succ_mul (s + 1) q
    simpa only [Nat.add_assoc] using this
  have htail : m + n - (s + 2) + 1 = q + 1 := by
    dsimp only [q]
  rw [hlow, htail, hmn]
  calc
    (s + 2 + q) + (s + 1) * q =
        (s + 2) + ((s + 1) * q + q) := by omega
    _ = (s + 2) + (s + 2) * q := by rw [hsucc]
    _ = (s + 2) * q + (s + 2) := Nat.add_comm _ _
    _ = (s + 2) * (q + 1) := by
      rw [Nat.mul_add]
      simp

/-- **All-order factorial Hahn forward difference.**  For adjacent physical
source coordinates `(i,j)` and `(i+1,j-1)`, the order-`k` row difference is
the order-`k-1` row at reduced labels, multiplied by the exact pivot
`k*(m+n-k+1)`. -/
theorem transvectFactorialCoeff_adjacent :
    ∀ k m n i j : Nat,
      k ≤ m → k ≤ n → i < m → 0 < j → j ≤ n →
      (transvectFactorialCoeff m n k (i + 1) (j - 1) +
        -(transvectFactorialCoeff m n k i j)) ≈
        Q'.ofNat (k * (m + n - k + 1)) *
          transvectFactorialCoeff (m - 1) (n - 1) (k - 1) i (j - 1) := by
  intro k
  induction k with
  | zero =>
      intro m n i j _ _ _ _ _
      have hshift := transvectFactorialCoeff_zero m n (i + 1) (j - 1)
      have hbase := transvectFactorialCoeff_zero m n i j
      have hdiff := Q'.add_eqv_congr' hshift
        (Q'.neg_eqv_congr _ _ hbase)
      refine Q'.eqv_trans _ ((1 : Q') + -1) _ hdiff ?_
      simp only [Nat.zero_mul, Nat.zero_sub]
      refine Q'.eqv_trans _ 0 _ (Q'.add_neg_self_eqv 1) ?_
      exact Q'.eqv_symm (Q'.eqv_trans _
        ((0 : Q') * transvectFactorialCoeff (m - 1) (n - 1) 0 i (j - 1)) _
        (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
        (q_zero_mul _))
  | succ k ih =>
      cases k with
      | zero =>
          intro m n i j hm hn hi hj0 hj
          have hcore := transvectFactorialCoeff_one_adjacent m n i j hi hj0 hj
          have hzero := transvectFactorialCoeff_zero
            (m - 1) (n - 1) i (j - 1)
          have hscale : 1 * (m + n - 1 + 1) = m + n := by omega
          rw [hscale]
          refine Q'.eqv_trans _ (Q'.ofNat (m + n)) _ hcore ?_
          exact Q'.eqv_symm (Q'.eqv_trans _ (Q'.ofNat (m + n) * 1) _
            (Q'.mul_eqv_congr_left _ _ _ hzero) (Q'.mul_one_eqv _))
      | succ s =>
          intro m n i j hm hn hi hj0 hj
          let Ap : Q' := Q'.ofNat ((i + 1) * (n - (j - 1)))
          let Bp : Q' := Q'.ofNat ((m - (i + 1)) * (j - 1))
          let A : Q' := Q'.ofNat (i * (n - j))
          let B : Q' := Q'.ofNat ((m - i) * j)
          let X : Q' :=
            transvectFactorialCoeff (m - 1) (n - 1) (s + 1) i (j - 1)
          let Y : Q' :=
            transvectFactorialCoeff (m - 1) (n - 1) (s + 1) (i + 1) (j - 2)
          let Z : Q' :=
            transvectFactorialCoeff (m - 1) (n - 1) (s + 1) (i - 1) j
          let U : Q' :=
            transvectFactorialCoeff (m - 2) (n - 2) s i (j - 2)
          let V : Q' :=
            transvectFactorialCoeff (m - 2) (n - 2) s (i - 1) (j - 1)
          let Lnat : Nat :=
            (s + 1) * ((m - 1) + (n - 1) - (s + 1) + 1)
          let L : Q' := Q'.ofNat Lnat
          let Tnat : Nat := (s + 2) * (m + n - (s + 2) + 1)

          have hshift0 :=
            transvectFactorialCoeff_succ m n (s + 1) (i + 1) (j - 1)
          have hshift :
              transvectFactorialCoeff m n (s + 2) (i + 1) (j - 1) ≈
                Ap * X + (-Bp) * Y := by
            exact Q'.eqv_symm (by
              simpa only [Ap, Bp, X, Y, Nat.add_sub_cancel] using hshift0)

          have hbase0 := transvectFactorialCoeff_succ m n (s + 1) i j
          have hbase :
              transvectFactorialCoeff m n (s + 2) i j ≈
                A * Z + (-B) * X := by
            exact Q'.eqv_symm (by
              simpa only [A, B, X, Z] using hbase0)

          have hexpanded := Q'.add_eqv_congr' hshift
            (Q'.neg_eqv_congr _ _ hbase)

          have hscalar : (Ap + -Bp + -A + B).eqv (Q'.ofNat (m + n)) := by
            have honeShift := transvectFactorialCoeff_one m n (i + 1) (j - 1)
            have honeBase := transvectFactorialCoeff_one m n i j
            have hpairs := Q'.add_eqv_congr' honeShift
              (Q'.neg_eqv_congr _ _ honeBase)
            have hadj := transvectFactorialCoeff_one_adjacent m n i j hi hj0 hj
            refine Q'.eqv_trans _
              ((Ap + -Bp) + -(A + -B)) _ ?_ ?_
            · dsimp only [Ap, Bp, A, B]
              ring_qeqv
            · exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (by
                simpa only [Ap, Bp, A, B] using hpairs)) hadj

          have hY : ((-Bp) * (Y + -X)).eqv ((-Bp) * (L * U)) := by
            by_cases him1 : i < m - 1
            · by_cases hj1 : 0 < j - 1
              · have hih := ih (m - 1) (n - 1) i (j - 1)
                  (by omega) (by omega) him1 hj1 (by omega)
                have hYX : (Y + -X).eqv (L * U) := by
                  simpa only [Y, X, L, Lnat, U,
                    show (m - 1) - 1 = m - 2 by omega,
                    show (n - 1) - 1 = n - 2 by omega,
                    show (s + 1) - 1 = s by omega,
                    show (j - 1) - 1 = j - 2 by omega] using hih
                exact Q'.mul_eqv_congr_left (-Bp) _ _ hYX
              · have hjz : j - 1 = 0 := by omega
                have hzero : (m - (i + 1)) * (j - 1) = 0 := by
                  rw [hjz, Nat.mul_zero]
                dsimp only [Bp]
                rw [hzero]
                exact zero_scaled _ _
            · have hmz : m - (i + 1) = 0 := by omega
              have hzero : (m - (i + 1)) * (j - 1) = 0 := by
                rw [hmz, Nat.zero_mul]
              dsimp only [Bp]
              rw [hzero]
              exact zero_scaled _ _

          have hZ : (A * (X + -Z)).eqv (A * (L * V)) := by
            by_cases hi0 : 0 < i
            · by_cases hjn : j < n
              · have hih := ih (m - 1) (n - 1) (i - 1) j
                  (by omega) (by omega) (by omega) hj0 (by omega)
                have hXZ : (X + -Z).eqv (L * V) := by
                  simpa only [X, Z, L, Lnat, V,
                    show i - 1 + 1 = i by omega,
                    show (m - 1) - 1 = m - 2 by omega,
                    show (n - 1) - 1 = n - 2 by omega,
                    show (s + 1) - 1 = s by omega] using hih
                exact Q'.mul_eqv_congr_left A _ _ hXZ
              · have hnz : n - j = 0 := by omega
                have hzero : i * (n - j) = 0 := by
                  rw [hnz, Nat.mul_zero]
                dsimp only [A]
                rw [hzero]
                exact zero_scaled _ _
            · have hiz : i = 0 := by omega
              have hzero : i * (n - j) = 0 := by
                rw [hiz, Nat.zero_mul]
              dsimp only [A]
              rw [hzero]
              exact zero_scaled _ _

          have hrec0 :=
            transvectFactorialCoeff_succ (m - 1) (n - 1) s i (j - 1)
          have hrec : (A * V + (-Bp) * U).eqv X := by
            simpa only [A, Bp, X, U, V,
              show (n - 1) - (j - 1) = n - j by omega,
              show (m - 1) - i = m - (i + 1) by omega] using hrec0

          have hnat := allOrderScale_nat s m n hm hn
          have hscale :
              (Q'.ofNat (m + n) + L).eqv (Q'.ofNat Tnat) := by
            have hadd := Q'.ofNat_add_eqv (m + n) Lnat
            rw [hnat] at hadd
            exact Q'.eqv_symm (by simpa only [L, Tnat] using hadd)

          refine Q'.eqv_trans _
            ((Ap * X + (-Bp) * Y) + -(A * Z + (-B) * X)) _
            hexpanded ?_
          refine Q'.eqv_trans _
            ((Ap + -Bp + -A + B) * X +
              (((-Bp) * (Y + -X)) + A * (X + -Z))) _
            (successor_difference_rearrange Ap Bp A B X Y Z) ?_
          refine Q'.eqv_trans _
            (Q'.ofNat (m + n) * X +
              (((-Bp) * (L * U)) + A * (L * V))) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_right _ _ _ hscalar)
              (Q'.add_eqv_congr' hY hZ)
          · refine Q'.eqv_trans _
              (Q'.ofNat (m + n) * X + L * (A * V + (-Bp) * U)) _
              (lower_branches_factor _ _ _ _ _ _ _) ?_
            refine Q'.eqv_trans _
              (Q'.ofNat (m + n) * X + L * X) _
              (Q'.add_eqv_congr_left _ _ _
                (Q'.mul_eqv_congr_left L _ _ hrec)) ?_
            simpa only [Tnat] using
              scale_sum_factor (Q'.ofNat (m + n)) L (Q'.ofNat Tnat) X hscale

/-- Shell-form corollary with the exact requested reduced labels. -/
theorem hahnEntry_adjacent_all_order (m n t k i : Nat)
    (hkm : k ≤ m) (hkn : k ≤ n) (him : i < m)
    (hit : i < t) (hjn : t - i ≤ n) :
    (hahnEntry m n t k (i + 1) + -(hahnEntry m n t k i)) ≈
      Q'.ofNat (k * (m + n - k + 1)) *
        hahnEntry (m - 1) (n - 1) (t - 1) (k - 1) i := by
  have hj0 : 0 < t - i := by omega
  have hshift : t - (i + 1) = t - i - 1 := by omega
  have hreduced : t - 1 - i = t - i - 1 := by omega
  unfold hahnEntry
  rw [hshift, hreduced]
  exact transvectFactorialCoeff_adjacent k m n i (t - i)
    hkm hkn him hj0 hjn

end YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder

#print axioms YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder.transvectFactorialCoeff_adjacent
#print axioms YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder.hahnEntry_adjacent_all_order
