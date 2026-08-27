/-
# All-label orthogonality of the ordered left SU(2) channels

The first-pair Casimir is self-adjoint for the invariant four-leg pairing,
and a left-associated channel with first contraction order `k` is its exact
eigenvector.  Distinct physical orders have distinct eigenvalues.  These
three facts give the missing left-basis Gram orthogonality, mirroring the
already proved right-basis theorem.

Constructive contract: exact rational Casimir algebra and natural-number
separation only, with no choice, no `Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
import YMGap.Continuum.SU2OrderedLeftCasimirPairing

namespace YMGap.Continuum.SU2OrderedLeftGramCasimirOrthogonality

open YMGap.Constructive
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2OrderedLeftCasimirPairing
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantMixedPentagon

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Move the first-pair Casimir across the pairing -/

theorem fixedLeft_triMapInner_eigenvalue_balance {a b c d : Nat}
    (q u : FixedLeftCGChannel a b c d) :
    pairEigenvalue a b q.k *
        triMapInner a b c d
          (triLeft a b c d q.intermediate)
          (triLeft a b c d u.intermediate) ≈
      pairEigenvalue a b u.k *
        triMapInner a b c d
          (triLeft a b c d q.intermediate)
          (triLeft a b c d u.intermediate) := by
  let L := triLeft a b c d q.intermediate
  let R := triLeft a b c d u.intermediate
  let G := triMapInner a b c d L R
  have hq := triMapFirstPairExchange_left_eigen q R
  have hself := triMapFirstPairExchange_self_adjoint a b c d L R
  have hu := triMapFirstPairExchange_left_eigen u L
  have hsym := triMapInner_symm a b c d R L
  have hnegative :
      (-(pairEigenvalue a b q.k)) * G ≈
        (-(pairEigenvalue a b u.k)) * G := by
    refine Q'.eqv_trans _
      (triMapFirstPairExchangeInner a b c d L R) _
      (Q'.eqv_symm (by simpa only [L, R, G] using hq)) ?_
    refine Q'.eqv_trans _
      (triMapFirstPairExchangeInner a b c d R L) _ hself ?_
    refine Q'.eqv_trans _
      ((-(pairEigenvalue a b u.k)) *
        triMapInner a b c d R L) _ hu ?_
    exact Q'.mul_eqv_congr_left _ _ _ hsym
  have hnegatedProducts :
      -(pairEigenvalue a b q.k * G) ≈
        -(pairEigenvalue a b u.k * G) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.neg_mul_eqv (pairEigenvalue a b q.k) G))
      (Q'.eqv_trans _ _ _ hnegative
        (Q'.neg_mul_eqv (pairEigenvalue a b u.k) G))
  exact Q'.eqv_trans _ (-(-(pairEigenvalue a b q.k * G))) _
    (Q'.eqv_symm (Q'.neg_neg_eqv _))
    (Q'.eqv_trans _ (-(-(pairEigenvalue a b u.k * G))) _
      (Q'.neg_eqv_congr _ _ hnegatedProducts)
      (Q'.neg_neg_eqv _))

/-! ## 2. Physical eigenvalues are distinct -/

theorem fixedLeft_pairEigenNat_ne {a b c d : Nat}
    (q u : FixedLeftCGChannel a b c d) (hku : q.k ≠ u.k) :
    pairEigenNat a b q.k ≠ pairEigenNat a b u.k := by
  intro heq
  have hq := Nat.le_min.mp q.k_le
  have hu := Nat.le_min.mp u.k_le
  rcases Nat.lt_or_gt_of_ne hku with hlt | hgt
  · have hsum : q.k + u.k ≤ a + b := by omega
    have hstrict := pairEigenNat_strict_mono_on_physical_half
      (a + b) q.k u.k hlt hsum
    unfold pairEigenNat at heq
    omega
  · have hsum : u.k + q.k ≤ a + b := by omega
    have hstrict := pairEigenNat_strict_mono_on_physical_half
      (a + b) u.k q.k hgt hsum
    unfold pairEigenNat at heq
    omega

private theorem ofNat_sub_add_eqv (A B : Nat) (hBA : B ≤ A) :
    Q'.ofNat A ≈ Q'.ofNat (A - B) + Q'.ofNat B := by
  have hnat : A - B + B = A := by omega
  have h := Q'.ofNat_add_eqv (A - B) B
  rw [hnat] at h
  exact h

private theorem difference_scale_of_scale_eq
    (A B : Nat) (X : Q') (hAB : A ≤ B)
    (h : Q'.ofNat A * X ≈ Q'.ofNat B * X) :
    Q'.ofNat (B - A) * X ≈ 0 := by
  have hB := ofNat_sub_add_eqv B A hAB
  have hcancel :
      Q'.ofNat B * X + -(Q'.ofNat A * X) ≈ 0 := by
    refine Q'.eqv_trans _
      (Q'.ofNat A * X + -(Q'.ofNat A * X)) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm h)) ?_
    exact Q'.add_neg_self_eqv _
  refine Q'.eqv_trans _
    ((Q'.ofNat (B - A) + Q'.ofNat A) * X +
      -(Q'.ofNat A * X)) _ ?_ ?_
  · refine Q'.eqv_trans _ (Q'.ofNat (B - A) * X + 0) _
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))) ?_
    refine Q'.eqv_trans _
      (Q'.ofNat (B - A) * X +
        (Q'.ofNat A * X + -(Q'.ofNat A * X))) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.add_neg_self_eqv _))) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat (B - A) * X + Q'.ofNat A * X) +
        -(Q'.ofNat A * X)) _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ X))
  refine Q'.eqv_trans _
    (Q'.ofNat B * X + -(Q'.ofNat A * X)) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ X (Q'.eqv_symm hB))) ?_
  exact hcancel

private theorem ofNat_pos_of_pos (N : Nat) (hN : 0 < N) :
    (0 : Q') < Q'.ofNat N := by
  cases N with
  | zero => omega
  | succ N => exact Q'.ofNat_succ_pos N

private theorem eqv_zero_of_distinct_nat_scales
    (A B : Nat) (X : Q') (hAB : A ≠ B)
    (h : Q'.ofNat A * X ≈ Q'.ofNat B * X) : X ≈ 0 := by
  rcases Nat.lt_or_gt_of_ne hAB with hlt | hgt
  · have hdiff := difference_scale_of_scale_eq A B X (by omega) h
    have hpos : (0 : Q') < Q'.ofNat (B - A) :=
      ofNat_pos_of_pos _ (by omega)
    apply Q'.mul_left_cancel_of_pos hpos
    exact Q'.eqv_trans _ 0 _ hdiff
      (Q'.eqv_symm (Q'.mul_zero_eqv _))
  · have hdiff := difference_scale_of_scale_eq B A X (by omega)
      (Q'.eqv_symm h)
    have hpos : (0 : Q') < Q'.ofNat (A - B) :=
      ofNat_pos_of_pos _ (by omega)
    apply Q'.mul_left_cancel_of_pos hpos
    exact Q'.eqv_trans _ 0 _ hdiff
      (Q'.eqv_symm (Q'.mul_zero_eqv _))

/-! ## 3. Complete left-channel Gram law -/

theorem leftChannel_offDiagonalOrthogonality_all
    {a b c d : Nat} (q u : FixedLeftCGChannel a b c d)
    (hku : q.k ≠ u.k) :
    triMapInner a b c d
        (triLeft a b c d q.intermediate)
        (triLeft a b c d u.intermediate) ≈ 0 := by
  let G := triMapInner a b c d
    (triLeft a b c d q.intermediate)
    (triLeft a b c d u.intermediate)
  have hbalance := fixedLeft_triMapInner_eigenvalue_balance q u
  have hne := fixedLeft_pairEigenNat_ne q u hku
  apply eqv_zero_of_distinct_nat_scales
    (pairEigenNat a b q.k) (pairEigenNat a b u.k) G hne
  simpa only [pairEigenvalue, pairEigenNat, G] using hbalance

/-- **Every fixed-output left channel is orthogonal to every distinct left
channel, with its exact physical Gram weight on the diagonal.** -/
theorem leftChannel_gram_all {a b c d : Nat}
    (q u : FixedLeftCGChannel a b c d) :
    triMapInner a b c d
        (triLeft a b c d q.intermediate)
        (triLeft a b c d u.intermediate) ≈
      if q.k = u.k then
        triLeftChannelWeight a b c d u.intermediate
      else 0 := by
  by_cases hku : q.k = u.k
  · rw [if_pos hku]
    have hqu := fixedLeftChannel_eq_of_k_eq q u hku
    subst u
    exact Q'.eqv_refl _
  · rw [if_neg hku]
    exact leftChannel_offDiagonalOrthogonality_all q u hku

#print axioms fixedLeft_triMapInner_eigenvalue_balance
#print axioms fixedLeft_pairEigenNat_ne
#print axioms leftChannel_offDiagonalOrthogonality_all
#print axioms leftChannel_gram_all

end YMGap.Continuum.SU2OrderedLeftGramCasimirOrthogonality
