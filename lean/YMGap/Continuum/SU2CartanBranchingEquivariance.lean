/-
# Equivariance of the constructive SU(2) Cartan branching kernel

The normalized hypergeometric split constructed in
`SU2CartanBranchingKernel` is useful in a physical strand compiler only when
it is a morphism of the explicit `sl₂` representations.  This module proves
that verification at the coefficient level.  The split has no coefficients
outside its physical bidegree rectangle and intertwines all three generators
`E`, `F`, and `H`.  Lowering covariance names the necessary literal support
condition at the top coefficient; no representation-theoretic property is
hidden in a typeclass.

Constructive contract: Mathlib-free, exact `Q'` identities, no choice, no
`Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2CartanBranchingKernel
import YMGap.Continuum.SU2TransvectantBinaryGramInvariant
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2CartanBranchingEquivariance

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantRowToFullGram
open YMGap.Continuum.SU2TransvectantBinaryGramInvariant
open YMGap.Continuum.SU2CartanBranchingKernel

local infix:50 " ≈ " => Q'.eqv

private theorem scale_zero (q x : Q') (hx : x ≈ 0) : q * x ≈ 0 :=
  Q'.eqv_trans _ (q * 0) _ (Q'.mul_eqv_congr_left q _ _ hx)
    (Q'.mul_zero_eqv q)

private theorem zero_scale (q x : Q') (hx : x ≈ 0) : x * q ≈ 0 :=
  Q'.eqv_trans _ (0 * q) _ (Q'.mul_eqv_congr_right _ _ q hx)
    (Q'.zero_mul_eqv q)

private theorem tvBinomQ_zero_of_lt (n i : Nat) (hi : n < i) :
    tvBinomQ n i ≈ 0 := by
  refine Q'.eqv_trans _ (Q'.ofNat (PNPaths.choose n i)) _
    (tvBinomQ_eqv_choose_all n i) ?_
  rw [choose_zero_of_lt n i hi]
  exact Q'.ofNat_zero_eqv

private theorem cartan_denominator_positive (m n i j : Nat)
    (hs : i + j ≤ m + n) :
    (0 : Q') < tvBinomQ (m + n) (i + j) := by
  unfold tvBinomQ
  rw [if_pos hs]
  apply CReal.pos_of_num_pos
  change (0 : Int) < Int.ofNat (tvFact (m + n))
  exact Int.natCast_pos.mpr (tvFact_pos (m + n))

/-! ## Exact ratio transport used by the root operators -/

private theorem divPos_eqv_divPos_of_cross {p d p' d' : Q'}
    (hd : (0 : Q') < d) (hd' : (0 : Q') < d')
    (hcross : p * d' ≈ p' * d) :
    Q'.divPos p d hd ≈ Q'.divPos p' d' hd' := by
  let c := Q'.divPos p' d' hd'
  have hright : (c * d) * d' ≈ p' * d := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c d d') ?_
    refine Q'.eqv_trans _ (c * (d' * d)) _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv d d')) ?_
    refine Q'.eqv_trans _ ((c * d') * d) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c d' d)) ?_
    exact Q'.mul_eqv_congr_right _ _ d
      (Q'.divPos_mul_eqv p' d' hd')
  have hmul : p * d' ≈ (c * d) * d' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * d := by
    apply Q'.mul_left_cancel_of_pos hd'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv d' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * d) d'
  apply Q'.mul_left_cancel_of_pos hd
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv d (Q'.divPos p d hd)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv p d hd) ?_
  refine Q'.eqv_trans _ _ _ hcancel ?_
  exact Q'.mul_comm_eqv c d

private theorem divPos_mul_eqv (p d r : Q') (hd : (0 : Q') < d) :
    Q'.divPos p d hd * r ≈ Q'.divPos (p * r) d hd := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ (p * (Q'.recipPos d hd * r)) _
    (Q'.mul_assoc_eqv p (Q'.recipPos d hd) r) ?_
  refine Q'.eqv_trans _ (p * (r * Q'.recipPos d hd)) _
    (Q'.mul_eqv_congr_left p _ _
      (Q'.mul_comm_eqv (Q'.recipPos d hd) r)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv p r (Q'.recipPos d hd))

private theorem mul_divPos_eqv (r p d : Q') (hd : (0 : Q') < d) :
    r * Q'.divPos p d hd ≈ Q'.divPos (r * p) d hd := by
  unfold Q'.divPos
  exact Q'.eqv_symm (Q'.mul_assoc_eqv r p (Q'.recipPos d hd))

private theorem add_divPos_eqv (p p' d : Q') (hd : (0 : Q') < d) :
    Q'.divPos p d hd + Q'.divPos p' d hd ≈
      Q'.divPos (p + p') d hd := by
  unfold Q'.divPos
  exact Q'.eqv_symm
    (Q'.add_mul_eqv p p' (Q'.recipPos d hd))

private theorem cross_from_raw_step
    (p p' d d' r s : Q')
    (hpp : p' ≈ p * s) (hdd : d * s ≈ d' * r) :
    (p * r) * d' ≈ p' * d := by
  refine Q'.eqv_trans _ (p * (r * d')) _
    (Q'.mul_assoc_eqv p r d') ?_
  refine Q'.eqv_trans _ (p * (d' * r)) _
    (Q'.mul_eqv_congr_left p _ _ (Q'.mul_comm_eqv r d')) ?_
  refine Q'.eqv_trans _ (p * (d * s)) _
    (Q'.mul_eqv_congr_left p _ _ (Q'.eqv_symm hdd)) ?_
  refine Q'.eqv_trans _ ((p * s) * d) _ ?_ ?_
  · refine Q'.eqv_trans _ ((p * d) * s) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv p d s)) ?_
    refine Q'.eqv_trans _ ((d * p) * s) _
      (Q'.mul_eqv_congr_right _ _ s (Q'.mul_comm_eqv p d)) ?_
    refine Q'.eqv_trans _ (d * (p * s)) _
      (Q'.mul_assoc_eqv d p s) ?_
    exact Q'.mul_comm_eqv d (p * s)
  · exact Q'.mul_eqv_congr_right _ _ d (Q'.eqv_symm hpp)

private theorem normalized_step
    (p p' d d' r s : Q')
    (hd : (0 : Q') < d) (hd' : (0 : Q') < d')
    (hpp : p' ≈ p * s) (hdd : d * s ≈ d' * r) :
    Q'.divPos p d hd * r ≈ Q'.divPos p' d' hd' := by
  refine Q'.eqv_trans _ (Q'.divPos (p * r) d hd) _
    (divPos_mul_eqv p d r hd) ?_
  exact divPos_eqv_divPos_of_cross hd hd'
    (cross_from_raw_step p p' d d' r s hpp hdd)

private theorem weighted_previous_to_next
    (previous next other coefficient step : Q')
    (hadj : next * step ≈ previous * coefficient) :
    coefficient * (previous * other) ≈ (next * other) * step := by
  refine Q'.eqv_trans _ ((coefficient * previous) * other) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv coefficient previous other)) ?_
  refine Q'.eqv_trans _ ((previous * coefficient) * other) _
    (Q'.mul_eqv_congr_right _ _ other
      (Q'.mul_comm_eqv coefficient previous)) ?_
  refine Q'.eqv_trans _ ((next * step) * other) _
    (Q'.mul_eqv_congr_right _ _ other (Q'.eqv_symm hadj)) ?_
  refine Q'.eqv_trans _ (next * (step * other)) _
    (Q'.mul_assoc_eqv next step other) ?_
  refine Q'.eqv_trans _ (next * (other * step)) _
    (Q'.mul_eqv_congr_left next _ _ (Q'.mul_comm_eqv step other)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv next other step)

private theorem cartanRaw_raise_left (m n i j : Nat) (hi : i < m) :
    Q'.ofNat (m - i) * (tvBinomQ m i * tvBinomQ n j) ≈
      (tvBinomQ m (i + 1) * tvBinomQ n j) * Q'.ofNat (i + 1) :=
  weighted_previous_to_next _ _ _ _ _
    (tvBinomQ_adjacent_cross m i hi)

private theorem cartanRaw_raise_right (m n i j : Nat) (hj : j < n) :
    Q'.ofNat (n - j) * (tvBinomQ m i * tvBinomQ n j) ≈
      (tvBinomQ m i * tvBinomQ n (j + 1)) * Q'.ofNat (j + 1) := by
  have h := weighted_previous_to_next
    (tvBinomQ n j) (tvBinomQ n (j + 1)) (tvBinomQ m i)
    (Q'.ofNat (n - j)) (Q'.ofNat (j + 1))
    (tvBinomQ_adjacent_cross n j hj)
  refine Q'.eqv_trans _
    (Q'.ofNat (n - j) * (tvBinomQ n j * tvBinomQ m i)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv (tvBinomQ m i) (tvBinomQ n j))
  · refine Q'.eqv_trans _ _ _ h ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv (tvBinomQ n (j + 1)) (tvBinomQ m i))

private theorem cartanKernel_E_zero_succ (m n j : Nat) (hj : j < n)
    (hcur : j + 1 ≤ m + n) (hprev : j ≤ m + n) :
    cartanBranchKernelAt m n (j + 1) hcur 0 *
        Q'.ofNat (m + n - j) ≈
      Q'.ofNat (n - j) * cartanBranchKernelAt m n j hprev 0 := by
  let p := tvBinomQ m 0 * tvBinomQ n (j + 1)
  let p' := Q'.ofNat (n - j) * (tvBinomQ m 0 * tvBinomQ n j)
  let d := tvBinomQ (m + n) (j + 1)
  let d' := tvBinomQ (m + n) j
  let r := Q'.ofNat (m + n - j)
  let s := Q'.ofNat (j + 1)
  have hd : (0 : Q') < d := by
    simpa only [d, Nat.zero_add] using
      cartan_denominator_positive m n 0 (j + 1) (by omega)
  have hd' : (0 : Q') < d' := by
    simpa only [d', Nat.zero_add] using
      cartan_denominator_positive m n 0 j (by omega)
  have hpp : p' ≈ p * s := by
    simpa only [p, p', s] using cartanRaw_raise_right m n 0 j hj
  have hdd : d * s ≈ d' * r := by
    simpa only [d, d', r, s] using
      tvBinomQ_adjacent_cross (m + n) j (by omega)
  have hnorm := normalized_step p p' d d' r s hd hd' hpp hdd
  refine Q'.eqv_trans _ (Q'.divPos p' d' hd') _ ?_ ?_
  · simpa only [cartanBranchKernelAt, cartanBranchRawAt, Q'.divPos,
      Nat.add_zero, Nat.zero_add, Nat.sub_zero, p, d, r] using hnorm
  · refine Q'.eqv_trans _
      (Q'.ofNat (n - j) * Q'.divPos
        (tvBinomQ m 0 * tvBinomQ n j) d' hd') _ ?_ ?_
    · exact Q'.eqv_symm
        (mul_divPos_eqv (Q'.ofNat (n - j))
          (tvBinomQ m 0 * tvBinomQ n j) d' hd')
    · unfold cartanBranchKernelAt cartanBranchRawAt
      simp only [Nat.sub_zero, d']
      exact Q'.eqv_of_eq (by congr)

private theorem cartanKernel_E_succ_zero (m n i : Nat) (hi : i < m)
    (hcur : i + 1 ≤ m + n) (hprev : i ≤ m + n) :
    cartanBranchKernelAt m n (i + 1) hcur (i + 1) *
        Q'.ofNat (m + n - i) ≈
      Q'.ofNat (m - i) * cartanBranchKernelAt m n i hprev i := by
  let p := tvBinomQ m (i + 1) * tvBinomQ n 0
  let p' := Q'.ofNat (m - i) * (tvBinomQ m i * tvBinomQ n 0)
  let d := tvBinomQ (m + n) (i + 1)
  let d' := tvBinomQ (m + n) i
  let r := Q'.ofNat (m + n - i)
  let s := Q'.ofNat (i + 1)
  have hd : (0 : Q') < d := cartan_denominator_positive m n (i + 1) 0 (by omega)
  have hd' : (0 : Q') < d' := cartan_denominator_positive m n i 0 (by omega)
  have hpp : p' ≈ p * s := by
    simpa only [p, p', s] using cartanRaw_raise_left m n i 0 hi
  have hdd : d * s ≈ d' * r := by
    simpa only [d, d', r, s] using
      tvBinomQ_adjacent_cross (m + n) i (by omega)
  have hnorm := normalized_step p p' d d' r s hd hd' hpp hdd
  refine Q'.eqv_trans _ (Q'.divPos p' d' hd') _ ?_ ?_
  · simpa only [cartanBranchKernelAt, cartanBranchRawAt, Q'.divPos,
      Nat.add_zero, Nat.sub_self, p, d, r] using hnorm
  · refine Q'.eqv_trans _
      (Q'.ofNat (m - i) * Q'.divPos
        (tvBinomQ m i * tvBinomQ n 0) d' hd') _ ?_ ?_
    · exact Q'.eqv_symm
        (mul_divPos_eqv (Q'.ofNat (m - i))
          (tvBinomQ m i * tvBinomQ n 0) d' hd')
    · unfold cartanBranchKernelAt cartanBranchRawAt
      simp only [Nat.sub_self, d']
      exact Q'.eqv_of_eq (by congr)

private theorem cartanKernel_E_succ_succ (m n i j : Nat)
    (hi : i < m) (hj : j < n)
    (hcur : i + j + 2 ≤ m + n) (hprev : i + j + 1 ≤ m + n) :
    cartanBranchKernelAt m n (i + j + 2) hcur (i + 1) *
        Q'.ofNat (m + n - (i + j + 1)) ≈
      Q'.ofNat (m - i) *
          cartanBranchKernelAt m n (i + j + 1) hprev i +
        Q'.ofNat (n - j) *
          cartanBranchKernelAt m n (i + j + 1) hprev (i + 1) := by
  let p := tvBinomQ m (i + 1) * tvBinomQ n (j + 1)
  let pLeft := Q'.ofNat (m - i) *
    (tvBinomQ m i * tvBinomQ n (j + 1))
  let pRight := Q'.ofNat (n - j) *
    (tvBinomQ m (i + 1) * tvBinomQ n j)
  let p' := pLeft + pRight
  let d := tvBinomQ (m + n) (i + j + 2)
  let d' := tvBinomQ (m + n) (i + j + 1)
  let r := Q'.ofNat (m + n - (i + j + 1))
  let s := Q'.ofNat ((i + 1) + (j + 1))
  have hsum : (i + 1) + (j + 1) = i + j + 2 := by omega
  have hd : (0 : Q') < d := by
    simpa only [d, hsum] using
      cartan_denominator_positive m n (i + 1) (j + 1) (by omega)
  have hd' : (0 : Q') < d' := by
    simpa only [d'] using
      cartan_denominator_positive m n i (j + 1) (by omega)
  have hleft : pLeft ≈ p * Q'.ofNat (i + 1) := by
    simpa only [pLeft, p] using cartanRaw_raise_left m n i (j + 1) hi
  have hright : pRight ≈ p * Q'.ofNat (j + 1) := by
    simpa only [pRight, p] using cartanRaw_raise_right m n (i + 1) j hj
  have hpp : p' ≈ p * s := by
    refine Q'.eqv_trans _
      (p * Q'.ofNat (i + 1) + p * Q'.ofNat (j + 1)) _
      (Q'.add_eqv_congr' hleft hright) ?_
    refine Q'.eqv_trans _
      (p * (Q'.ofNat (i + 1) + Q'.ofNat (j + 1))) _
      (Q'.eqv_symm (Q'.mul_add_eqv p _ _)) ?_
    exact Q'.mul_eqv_congr_left p _ _
      (Q'.eqv_symm (Q'.ofNat_add_eqv (i + 1) (j + 1)))
  have hdd : d * s ≈ d' * r := by
    have hnext : i + j + 1 + 1 = i + j + 2 := by omega
    simpa only [d, d', r, s, hsum, hnext] using
      tvBinomQ_adjacent_cross (m + n) (i + j + 1) (by omega)
  have hnorm := normalized_step p p' d d' r s hd hd' hpp hdd
  have hsubCur : i + j + 2 - (i + 1) = j + 1 := by omega
  have hsubLeft : i + j + 1 - i = j + 1 := by omega
  have hsubRight : i + j + 1 - (i + 1) = j := by omega
  refine Q'.eqv_trans _ (Q'.divPos p' d' hd') _ ?_ ?_
  · simpa only [cartanBranchKernelAt, cartanBranchRawAt, Q'.divPos,
      hsubCur, p, d, r] using hnorm
  · refine Q'.eqv_trans _
      (Q'.divPos pLeft d' hd' + Q'.divPos pRight d' hd') _ ?_ ?_
    · exact Q'.eqv_symm (add_divPos_eqv pLeft pRight d' hd')
    · apply Q'.add_eqv_congr'
      · refine Q'.eqv_trans _
          (Q'.ofNat (m - i) * Q'.divPos
            (tvBinomQ m i * tvBinomQ n (j + 1)) d' hd') _ ?_ ?_
        · exact Q'.eqv_symm
            (mul_divPos_eqv (Q'.ofNat (m - i))
              (tvBinomQ m i * tvBinomQ n (j + 1)) d' hd')
        · unfold cartanBranchKernelAt cartanBranchRawAt
          simp only [hsubLeft, d']
          exact Q'.eqv_of_eq (by congr)
      · refine Q'.eqv_trans _
          (Q'.ofNat (n - j) * Q'.divPos
            (tvBinomQ m (i + 1) * tvBinomQ n j) d' hd') _ ?_ ?_
        · exact Q'.eqv_symm
            (mul_divPos_eqv (Q'.ofNat (n - j))
              (tvBinomQ m (i + 1) * tvBinomQ n j) d' hd')
        · unfold cartanBranchKernelAt cartanBranchRawAt
          simp only [hsubRight, d']
          exact Q'.eqv_of_eq (by congr)

private theorem cartanRaw_lower_left (m n i j : Nat) (hi : i < m) :
    Q'.ofNat (i + 1) *
        (tvBinomQ m (i + 1) * tvBinomQ n j) ≈
      (tvBinomQ m i * tvBinomQ n j) * Q'.ofNat (m - i) := by
  have h := cartanRaw_raise_left m n i j hi
  refine Q'.eqv_trans _
    ((tvBinomQ m (i + 1) * tvBinomQ n j) * Q'.ofNat (i + 1)) _
    (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (m - i) * (tvBinomQ m i * tvBinomQ n j)) _
    (Q'.eqv_symm h) ?_
  exact Q'.mul_comm_eqv _ _

private theorem cartanRaw_lower_right (m n i j : Nat) (hj : j < n) :
    Q'.ofNat (j + 1) *
        (tvBinomQ m i * tvBinomQ n (j + 1)) ≈
      (tvBinomQ m i * tvBinomQ n j) * Q'.ofNat (n - j) := by
  have h := cartanRaw_raise_right m n i j hj
  refine Q'.eqv_trans _
    ((tvBinomQ m i * tvBinomQ n (j + 1)) * Q'.ofNat (j + 1)) _
    (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (n - j) * (tvBinomQ m i * tvBinomQ n j)) _
    (Q'.eqv_symm h) ?_
  exact Q'.mul_comm_eqv _ _

private theorem cartanKernel_F_interior (m n i j : Nat)
    (hi : i < m) (hj : j < n)
    (hcur : i + j ≤ m + n) (hnext : i + j + 1 ≤ m + n) :
    cartanBranchKernelAt m n (i + j) hcur i * Q'.ofNat (i + j + 1) ≈
      Q'.ofNat (i + 1) *
          cartanBranchKernelAt m n (i + j + 1) hnext (i + 1) +
        Q'.ofNat (j + 1) *
          cartanBranchKernelAt m n (i + j + 1) hnext i := by
  let p := tvBinomQ m i * tvBinomQ n j
  let pLeft := Q'.ofNat (i + 1) *
    (tvBinomQ m (i + 1) * tvBinomQ n j)
  let pRight := Q'.ofNat (j + 1) *
    (tvBinomQ m i * tvBinomQ n (j + 1))
  let p' := pLeft + pRight
  let d := tvBinomQ (m + n) (i + j)
  let d' := tvBinomQ (m + n) (i + j + 1)
  let r := Q'.ofNat (i + j + 1)
  let s := Q'.ofNat (m + n - (i + j))
  have hd : (0 : Q') < d := by
    simpa only [d] using cartan_denominator_positive m n i j hcur
  have hd' : (0 : Q') < d' := by
    have hsum : i + 1 + j = i + j + 1 := by omega
    simpa only [d', hsum] using
      cartan_denominator_positive m n (i + 1) j (by omega)
  have hleft : pLeft ≈ p * Q'.ofNat (m - i) := by
    simpa only [pLeft, p] using cartanRaw_lower_left m n i j hi
  have hright : pRight ≈ p * Q'.ofNat (n - j) := by
    simpa only [pRight, p] using cartanRaw_lower_right m n i j hj
  have hremain : (m - i) + (n - j) = m + n - (i + j) := by omega
  have hpp : p' ≈ p * s := by
    refine Q'.eqv_trans _
      (p * Q'.ofNat (m - i) + p * Q'.ofNat (n - j)) _
      (Q'.add_eqv_congr' hleft hright) ?_
    refine Q'.eqv_trans _
      (p * (Q'.ofNat (m - i) + Q'.ofNat (n - j))) _
      (Q'.eqv_symm (Q'.mul_add_eqv p _ _)) ?_
    refine Q'.eqv_trans _
      (p * Q'.ofNat ((m - i) + (n - j))) _
      (Q'.mul_eqv_congr_left p _ _
        (Q'.eqv_symm (Q'.ofNat_add_eqv (m - i) (n - j)))) ?_
    simpa only [s, hremain] using
      Q'.eqv_refl (p * Q'.ofNat (m + n - (i + j)))
  have hdd : d * s ≈ d' * r := by
    exact Q'.eqv_symm (by
      simpa only [d, d', r, s] using
        tvBinomQ_adjacent_cross (m + n) (i + j) (by omega))
  have hnorm := normalized_step p p' d d' r s hd hd' hpp hdd
  have hsubCur : i + j - i = j := by omega
  have hsubLeft : i + j + 1 - (i + 1) = j := by omega
  have hsubRight : i + j + 1 - i = j + 1 := by omega
  refine Q'.eqv_trans _ (Q'.divPos p' d' hd') _ ?_ ?_
  · simpa only [cartanBranchKernelAt, cartanBranchRawAt, Q'.divPos,
      hsubCur, p, d, r] using hnorm
  · refine Q'.eqv_trans _
      (Q'.divPos pLeft d' hd' + Q'.divPos pRight d' hd') _ ?_ ?_
    · exact Q'.eqv_symm (add_divPos_eqv pLeft pRight d' hd')
    · apply Q'.add_eqv_congr'
      · refine Q'.eqv_trans _
          (Q'.ofNat (i + 1) * Q'.divPos
            (tvBinomQ m (i + 1) * tvBinomQ n j) d' hd') _ ?_ ?_
        · exact Q'.eqv_symm
            (mul_divPos_eqv (Q'.ofNat (i + 1))
              (tvBinomQ m (i + 1) * tvBinomQ n j) d' hd')
        · unfold cartanBranchKernelAt cartanBranchRawAt
          simp only [hsubLeft, d']
          exact Q'.eqv_of_eq (by congr)
      · refine Q'.eqv_trans _
          (Q'.ofNat (j + 1) * Q'.divPos
            (tvBinomQ m i * tvBinomQ n (j + 1)) d' hd') _ ?_ ?_
        · exact Q'.eqv_symm
            (mul_divPos_eqv (Q'.ofNat (j + 1))
              (tvBinomQ m i * tvBinomQ n (j + 1)) d' hd')
        · unfold cartanBranchKernelAt cartanBranchRawAt
          simp only [hsubRight, d']
          exact Q'.eqv_of_eq (by congr)

private theorem cartanKernel_F_top_left (m n j : Nat) (hj : j < n)
    (hcur : m + j ≤ m + n) (hnext : m + j + 1 ≤ m + n) :
    cartanBranchKernelAt m n (m + j) hcur m * Q'.ofNat (m + j + 1) ≈
      Q'.ofNat (j + 1) *
        cartanBranchKernelAt m n (m + j + 1) hnext m := by
  let p := tvBinomQ m m * tvBinomQ n j
  let p' := Q'.ofNat (j + 1) *
    (tvBinomQ m m * tvBinomQ n (j + 1))
  let d := tvBinomQ (m + n) (m + j)
  let d' := tvBinomQ (m + n) (m + j + 1)
  let r := Q'.ofNat (m + j + 1)
  let s := Q'.ofNat (n - j)
  have hd : (0 : Q') < d := by
    simpa only [d] using cartan_denominator_positive m n m j hcur
  have hd' : (0 : Q') < d' := by
    simpa only [d'] using cartan_denominator_positive m n m (j + 1) (by omega)
  have hpp : p' ≈ p * s := by
    simpa only [p', p, s] using cartanRaw_lower_right m n m j hj
  have hdd : d * s ≈ d' * r := by
    have hremain : m + n - (m + j) = n - j := by omega
    exact Q'.eqv_symm (by
      simpa only [d, d', r, s, hremain] using
        tvBinomQ_adjacent_cross (m + n) (m + j) (by omega))
  have hnorm := normalized_step p p' d d' r s hd hd' hpp hdd
  refine Q'.eqv_trans _ (Q'.divPos p' d' hd') _ ?_ ?_
  · simpa only [cartanBranchKernelAt, cartanBranchRawAt, Q'.divPos,
      Nat.add_sub_cancel_left, p, d, r] using hnorm
  · refine Q'.eqv_trans _
      (Q'.ofNat (j + 1) * Q'.divPos
        (tvBinomQ m m * tvBinomQ n (j + 1)) d' hd') _ ?_ ?_
    · exact Q'.eqv_symm
        (mul_divPos_eqv (Q'.ofNat (j + 1))
          (tvBinomQ m m * tvBinomQ n (j + 1)) d' hd')
    · unfold cartanBranchKernelAt cartanBranchRawAt
      have hsub : m + j + 1 - m = j + 1 := by omega
      simp only [hsub, d']
      exact Q'.eqv_of_eq (by congr)

private theorem cartanKernel_F_top_right (m n i : Nat) (hi : i < m)
    (hcur : i + n ≤ m + n) (hnext : i + n + 1 ≤ m + n) :
    cartanBranchKernelAt m n (i + n) hcur i * Q'.ofNat (i + n + 1) ≈
      Q'.ofNat (i + 1) *
        cartanBranchKernelAt m n (i + n + 1) hnext (i + 1) := by
  let p := tvBinomQ m i * tvBinomQ n n
  let p' := Q'.ofNat (i + 1) *
    (tvBinomQ m (i + 1) * tvBinomQ n n)
  let d := tvBinomQ (m + n) (i + n)
  let d' := tvBinomQ (m + n) (i + n + 1)
  let r := Q'.ofNat (i + n + 1)
  let s := Q'.ofNat (m - i)
  have hd : (0 : Q') < d := by
    simpa only [d] using cartan_denominator_positive m n i n hcur
  have hd' : (0 : Q') < d' := by
    have hsum : i + 1 + n = i + n + 1 := by omega
    simpa only [d', hsum] using
      cartan_denominator_positive m n (i + 1) n (by omega)
  have hpp : p' ≈ p * s := by
    simpa only [p', p, s] using cartanRaw_lower_left m n i n hi
  have hdd : d * s ≈ d' * r := by
    have hremain : m + n - (i + n) = m - i := by omega
    exact Q'.eqv_symm (by
      simpa only [d, d', r, s, hremain] using
        tvBinomQ_adjacent_cross (m + n) (i + n) (by omega))
  have hnorm := normalized_step p p' d d' r s hd hd' hpp hdd
  have hsubCur : i + n - i = n := by omega
  have hsubNext : i + n + 1 - (i + 1) = n := by omega
  refine Q'.eqv_trans _ (Q'.divPos p' d' hd') _ ?_ ?_
  · simpa only [cartanBranchKernelAt, cartanBranchRawAt, Q'.divPos,
      hsubCur, p, d, r] using hnorm
  · refine Q'.eqv_trans _
      (Q'.ofNat (i + 1) * Q'.divPos
        (tvBinomQ m (i + 1) * tvBinomQ n n) d' hd') _ ?_ ?_
    · exact Q'.eqv_symm
        (mul_divPos_eqv (Q'.ofNat (i + 1))
          (tvBinomQ m (i + 1) * tvBinomQ n n) d' hd')
    · unfold cartanBranchKernelAt cartanBranchRawAt
      simp only [hsubNext, d']
      exact Q'.eqv_of_eq (by congr)

private theorem scale_reassociated {K r A x : Q'} (h : K * r ≈ A) :
    K * (r * x) ≈ A * x := by
  refine Q'.eqv_trans _ ((K * r) * x) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv K r x)) ?_
  exact Q'.mul_eqv_congr_right _ _ x h

private theorem scale_sum_reassociated {K r A B x : Q'}
    (h : K * r ≈ A + B) :
    K * (r * x) ≈ A * x + B * x := by
  refine Q'.eqv_trans _ ((K * r) * x) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv K r x)) ?_
  refine Q'.eqv_trans _ ((A + B) * x) _
    (Q'.mul_eqv_congr_right _ _ x h) ?_
  exact Q'.add_mul_eqv A B x

private theorem cartanSplit_at (m n : Nat) (f : BForm) (i j : Nat)
    (hs : i + j ≤ m + n) :
    cartanSplit m n f i j ≈
      cartanBranchKernelAt m n (i + j) hs i * f (i + j) := by
  unfold cartanSplit
  rw [dif_pos hs]
  exact Q'.eqv_of_eq (by congr)

private theorem cartanSplit_at_total (m n : Nat) (f : BForm)
    (i j s : Nat) (hij : i + j = s) (hs : s ≤ m + n) :
    cartanSplit m n f i j ≈
      cartanBranchKernelAt m n s hs i * f s := by
  subst s
  exact cartanSplit_at m n f i j hs

/-! ## Raising equivariance -/

/-- **Raising equivariance of the Cartan split.**  The adjacent-binomial
identity is exactly the discrete Leibniz rule for the normalized branching
row. -/
theorem cartanSplit_E (m n : Nat) (f : BForm) :
    FormEqv2 (m + 1) (n + 1)
      (cartanSplit m n (Eop (m + n) f))
      (E2 m n (cartanSplit m n f)) := by
  intro i hi j hj
  cases i with
  | zero =>
      cases j with
      | zero =>
          have hs : 0 ≤ m + n := by omega
          have hL := cartanSplit_at_total m n (Eop (m + n) f)
            0 0 0 (by omega) hs
          simp only [E2]
          refine Q'.eqv_trans _
            (cartanBranchKernelAt m n 0 hs 0 * 0) _ ?_ ?_
          · simpa only [Eop] using hL
          · refine Q'.eqv_trans _ 0 _
              (scale_zero _ 0 (Q'.eqv_refl _)) ?_
            exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
      | succ j =>
          have hjn : j < n := by omega
          have hcur : j + 1 ≤ m + n := by omega
          have hprev : j ≤ m + n := by omega
          have hk := cartanKernel_E_zero_succ m n j hjn hcur hprev
          have hL := cartanSplit_at_total m n (Eop (m + n) f)
            0 (j + 1) (j + 1) (by omega) hcur
          have hR := cartanSplit_at_total m n f 0 j j (by omega) hprev
          simp only [E2]
          refine Q'.eqv_trans _
            (cartanBranchKernelAt m n (j + 1) hcur 0 *
              (Q'.ofNat (m + n - j) * f j)) _ ?_ ?_
          · simpa only [Eop] using hL
          · refine Q'.eqv_trans _
              ((Q'.ofNat (n - j) *
                cartanBranchKernelAt m n j hprev 0) * f j) _
              (scale_reassociated hk) ?_
            refine Q'.eqv_trans _
              (Q'.ofNat (n - j) *
                (cartanBranchKernelAt m n j hprev 0 * f j)) _
              (Q'.mul_assoc_eqv _ _ _) ?_
            refine Q'.eqv_trans _
              (Q'.ofNat (n - j) * cartanSplit m n f 0 j) _ ?_ ?_
            · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (by
                simpa only using hR))
            · exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | succ i =>
      cases j with
      | zero =>
          have him : i < m := by omega
          have hcur : i + 1 ≤ m + n := by omega
          have hprev : i ≤ m + n := by omega
          have hk := cartanKernel_E_succ_zero m n i him hcur hprev
          have hL := cartanSplit_at_total m n (Eop (m + n) f)
            (i + 1) 0 (i + 1) (by omega) hcur
          have hR := cartanSplit_at_total m n f i 0 i (by omega) hprev
          simp only [E2]
          refine Q'.eqv_trans _
            (cartanBranchKernelAt m n (i + 1) hcur (i + 1) *
              (Q'.ofNat (m + n - i) * f i)) _ ?_ ?_
          · simpa only [Eop] using hL
          · refine Q'.eqv_trans _
              ((Q'.ofNat (m - i) *
                cartanBranchKernelAt m n i hprev i) * f i) _
              (scale_reassociated hk) ?_
            refine Q'.eqv_trans _
              (Q'.ofNat (m - i) *
                (cartanBranchKernelAt m n i hprev i * f i)) _
              (Q'.mul_assoc_eqv _ _ _) ?_
            refine Q'.eqv_trans _
              (Q'.ofNat (m - i) * cartanSplit m n f i 0) _ ?_ ?_
            · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (by
                simpa only using hR))
            · exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))
      | succ j =>
          have him : i < m := by omega
          have hjn : j < n := by omega
          have hcur : i + j + 2 ≤ m + n := by omega
          have hprev : i + j + 1 ≤ m + n := by omega
          have hk := cartanKernel_E_succ_succ m n i j him hjn hcur hprev
          have hL := cartanSplit_at_total m n (Eop (m + n) f)
            (i + 1) (j + 1) (i + j + 2) (by omega) hcur
          have hR0 := cartanSplit_at_total m n f
            i (j + 1) (i + j + 1) (by omega) hprev
          have hR1 := cartanSplit_at_total m n f
            (i + 1) j (i + j + 1) (by omega) hprev
          simp only [E2]
          refine Q'.eqv_trans _
            (cartanBranchKernelAt m n (i + j + 2) hcur (i + 1) *
              (Q'.ofNat (m + n - (i + j + 1)) * f (i + j + 1))) _ ?_ ?_
          · simpa only [Eop] using hL
          · refine Q'.eqv_trans _
              ((Q'.ofNat (m - i) *
                  cartanBranchKernelAt m n (i + j + 1) hprev i) * f (i + j + 1) +
                (Q'.ofNat (n - j) *
                  cartanBranchKernelAt m n (i + j + 1) hprev (i + 1)) *
                    f (i + j + 1)) _
              (scale_sum_reassociated hk) ?_
            refine Q'.eqv_trans _
              (Q'.ofNat (m - i) *
                  (cartanBranchKernelAt m n (i + j + 1) hprev i * f (i + j + 1)) +
                Q'.ofNat (n - j) *
                  (cartanBranchKernelAt m n (i + j + 1) hprev (i + 1) *
                    f (i + j + 1))) _ ?_ ?_
            · exact Q'.add_eqv_congr'
                (Q'.mul_assoc_eqv _ _ _) (Q'.mul_assoc_eqv _ _ _)
            · apply Q'.add_eqv_congr'
              · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (by
                  simpa only using hR0))
              · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (by
                  simpa only using hR1))

/-- The coefficient-level Cartan split has exactly the physical bidegree
support required of an element of `V_m ⊗ V_n`. -/
theorem cartanSplit_bidegreeSupported (m n : Nat) (f : BForm) :
    BidegreeSupported m n (cartanSplit m n f) := by
  intro i j hij
  unfold cartanSplit
  by_cases hs : i + j ≤ m + n
  · rw [dif_pos hs]
    unfold cartanBranchKernelAt Q'.divPos cartanBranchRawAt
    rcases hij with hi | hj
    · have hzero : tvBinomQ m i * tvBinomQ n (i + j - i) ≈ 0 :=
      zero_scale (tvBinomQ n (i + j - i)) _
        (tvBinomQ_zero_of_lt m i hi)
      exact zero_scale (f (i + j)) _
        (zero_scale
          (Q'.recipPos (tvBinomQ (m + n) (i + j))
            (cartan_denominator_positive m n i j hs)) _ hzero)

    · have hji : i + j - i = j := by omega
      rw [hji]
      have hzero : tvBinomQ m i * tvBinomQ n j ≈ 0 :=
        scale_zero (tvBinomQ m i) _ (tvBinomQ_zero_of_lt n j hj)
      exact zero_scale (f (i + j)) _
        (zero_scale
          (Q'.recipPos (tvBinomQ (m + n) (i + j))
            (cartan_denominator_positive m n i j hs)) _ hzero)
  · rw [dif_neg hs]
    exact Q'.eqv_refl _

private theorem cartan_weight_add (m n i j : Nat) :
    2 * Int.ofNat (i + j) - Int.ofNat (m + n) =
      (2 * Int.ofNat i - Int.ofNat m) +
        (2 * Int.ofNat j - Int.ofNat n) := by
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

/-- **Cartan equivariance of the normalized split.**  Splitting a degree
`m+n` form and then applying the diagonal Cartan action is the same as first
applying the one-factor Cartan action and then splitting. -/
theorem cartanSplit_H (m n : Nat) (f : BForm) :
    FormEqv2 (m + 1) (n + 1)
      (cartanSplit m n (Hop (m + n) f))
      (H2 m n (cartanSplit m n f)) := by
  intro i hi j hj
  have hs : i + j ≤ m + n := by omega
  unfold cartanSplit Hop H2
  simp only [hs, dite_true]
  rw [cartan_weight_add m n i j]
  let K := cartanBranchKernelAt m n (i + j) hs i
  let W := Q'.ofInt
    ((2 * Int.ofNat i - Int.ofNat m) +
      (2 * Int.ofNat j - Int.ofNat n))
  change K * (W * f (i + j)) ≈ W * (K * f (i + j))
  refine Q'.eqv_trans _ ((K * W) * f (i + j)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv K W (f (i + j)))) ?_
  refine Q'.eqv_trans _ ((W * K) * f (i + j)) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv K W)) ?_
  exact Q'.mul_assoc_eqv W K (f (i + j))

/-! ## Lowering equivariance -/

/-- Literal zero support beyond a binary form's physical degree.  This is the
necessary boundary condition for `Fop`: its top physical coefficient reads
the first coefficient beyond the physical window. -/
def DegreeSupported (D : Nat) (f : BForm) : Prop :=
  ∀ s, D < s → f s ≈ 0

/-- **Lowering equivariance of the Cartan split.**  The only hypothesis is the
literal degree support needed at the top coefficient; the packet-boundary
terms are discharged by `cartanSplit_bidegreeSupported`. -/
theorem cartanSplit_F (m n : Nat) (f : BForm)
    (hf : DegreeSupported (m + n) f) :
    FormEqv2 (m + 1) (n + 1)
      (cartanSplit m n (Fop (m + n) f))
      (F2 m n (cartanSplit m n f)) := by
  intro i hi j hj
  have hcur : i + j ≤ m + n := by omega
  by_cases him : i < m
  · by_cases hjn : j < n
    · have hnext : i + j + 1 ≤ m + n := by omega
      have hk := cartanKernel_F_interior m n i j him hjn hcur hnext
      have hL := cartanSplit_at_total m n (Fop (m + n) f)
        i j (i + j) (by omega) hcur
      have hR0 := cartanSplit_at_total m n f
        (i + 1) j (i + j + 1) (by omega) hnext
      have hR1 := cartanSplit_at_total m n f
        i (j + 1) (i + j + 1) (by omega) hnext
      simp only [F2]
      refine Q'.eqv_trans _
        (cartanBranchKernelAt m n (i + j) hcur i *
          (Q'.ofNat (i + j + 1) * f (i + j + 1))) _ ?_ ?_
      · simpa only [Fop] using hL
      · refine Q'.eqv_trans _
          ((Q'.ofNat (i + 1) *
              cartanBranchKernelAt m n (i + j + 1) hnext (i + 1)) *
                f (i + j + 1) +
            (Q'.ofNat (j + 1) *
              cartanBranchKernelAt m n (i + j + 1) hnext i) *
                f (i + j + 1)) _
          (scale_sum_reassociated hk) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat (i + 1) *
              (cartanBranchKernelAt m n (i + j + 1) hnext (i + 1) *
                f (i + j + 1)) +
            Q'.ofNat (j + 1) *
              (cartanBranchKernelAt m n (i + j + 1) hnext i *
                f (i + j + 1))) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.mul_assoc_eqv _ _ _) (Q'.mul_assoc_eqv _ _ _)
        · apply Q'.add_eqv_congr'
          · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (by
              simpa only using hR0))
          · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (by
              simpa only using hR1))
    · have hjeq : j = n := by omega
      subst j
      have hnext : i + n + 1 ≤ m + n := by omega
      have hk := cartanKernel_F_top_right m n i him hcur hnext
      have hL := cartanSplit_at_total m n (Fop (m + n) f)
        i n (i + n) (by omega) hcur
      have hR := cartanSplit_at_total m n f
        (i + 1) n (i + n + 1) (by omega) hnext
      have hout := cartanSplit_bidegreeSupported m n f i (n + 1)
        (Or.inr (by omega))
      have houtScaled : Q'.ofNat (n + 1) * cartanSplit m n f i (n + 1) ≈ 0 :=
        scale_zero _ _ hout
      simp only [F2]
      refine Q'.eqv_trans _
        (cartanBranchKernelAt m n (i + n) hcur i *
          (Q'.ofNat (i + n + 1) * f (i + n + 1))) _ ?_ ?_
      · simpa only [Fop] using hL
      · refine Q'.eqv_trans _
          ((Q'.ofNat (i + 1) *
            cartanBranchKernelAt m n (i + n + 1) hnext (i + 1)) *
              f (i + n + 1)) _
          (scale_reassociated hk) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat (i + 1) *
            (cartanBranchKernelAt m n (i + n + 1) hnext (i + 1) *
              f (i + n + 1))) _
          (Q'.mul_assoc_eqv _ _ _) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat (i + 1) * cartanSplit m n f (i + 1) n) _ ?_ ?_
        · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (by
            simpa only using hR))
        · refine Q'.eqv_trans _ (Q'.ofNat (i + 1) *
              cartanSplit m n f (i + 1) n + 0) _
            (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))) ?_
          exact Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm houtScaled)
  · have hieq : i = m := by omega
    subst i
    by_cases hjn : j < n
    · have hnext : m + j + 1 ≤ m + n := by omega
      have hk := cartanKernel_F_top_left m n j hjn hcur hnext
      have hL := cartanSplit_at_total m n (Fop (m + n) f)
        m j (m + j) (by omega) hcur
      have hR := cartanSplit_at_total m n f
        m (j + 1) (m + j + 1) (by omega) hnext
      have hout := cartanSplit_bidegreeSupported m n f (m + 1) j
        (Or.inl (by omega))
      have houtScaled : Q'.ofNat (m + 1) * cartanSplit m n f (m + 1) j ≈ 0 :=
        scale_zero _ _ hout
      simp only [F2]
      refine Q'.eqv_trans _
        (cartanBranchKernelAt m n (m + j) hcur m *
          (Q'.ofNat (m + j + 1) * f (m + j + 1))) _ ?_ ?_
      · simpa only [Fop] using hL
      · refine Q'.eqv_trans _
          ((Q'.ofNat (j + 1) *
            cartanBranchKernelAt m n (m + j + 1) hnext m) *
              f (m + j + 1)) _
          (scale_reassociated hk) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat (j + 1) *
            (cartanBranchKernelAt m n (m + j + 1) hnext m *
              f (m + j + 1))) _
          (Q'.mul_assoc_eqv _ _ _) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat (j + 1) * cartanSplit m n f m (j + 1)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (by
            simpa only using hR))
        · refine Q'.eqv_trans _
            (0 + Q'.ofNat (j + 1) * cartanSplit m n f m (j + 1)) _
            (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))) ?_
          exact Q'.add_eqv_congr' (Q'.eqv_symm houtScaled) (Q'.eqv_refl _)
    · have hjeq : j = n := by omega
      subst j
      have hL := cartanSplit_at_total m n (Fop (m + n) f)
        m n (m + n) (by omega) (by omega)
      have htail : f (m + n + 1) ≈ 0 := hf (m + n + 1) (by omega)
      have hleftOut := cartanSplit_bidegreeSupported m n f (m + 1) n
        (Or.inl (by omega))
      have hrightOut := cartanSplit_bidegreeSupported m n f m (n + 1)
        (Or.inr (by omega))
      have hleftZero : Q'.ofNat (m + 1) * cartanSplit m n f (m + 1) n ≈ 0 :=
        scale_zero _ _ hleftOut
      have hrightZero : Q'.ofNat (n + 1) * cartanSplit m n f m (n + 1) ≈ 0 :=
        scale_zero _ _ hrightOut
      simp only [F2]
      refine Q'.eqv_trans _
        (cartanBranchKernelAt m n (m + n) (by omega) m *
          (Q'.ofNat (m + n + 1) * f (m + n + 1))) _ ?_ ?_
      · simpa only [Fop] using hL
      · refine Q'.eqv_trans _ 0 _ ?_ ?_
        · exact scale_zero _ _ (scale_zero _ _ htail)
        · refine Q'.eqv_trans _ (0 + 0) _
            (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))) ?_
          exact Q'.add_eqv_congr' (Q'.eqv_symm hleftZero)
            (Q'.eqv_symm hrightZero)

end YMGap.Continuum.SU2CartanBranchingEquivariance

#print axioms YMGap.Continuum.SU2CartanBranchingEquivariance.cartanSplit_bidegreeSupported
#print axioms YMGap.Continuum.SU2CartanBranchingEquivariance.cartanSplit_E
#print axioms YMGap.Continuum.SU2CartanBranchingEquivariance.cartanSplit_H
#print axioms YMGap.Continuum.SU2CartanBranchingEquivariance.cartanSplit_F
