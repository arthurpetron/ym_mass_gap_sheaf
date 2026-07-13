/-
# Exact Machin-side bounds for the semicircle value bridge

This module attacks the actual target used by `SemicircleValue` without adding
another residual record.  It proves an exact alternating-series telescope for
the paired Machin arctangent sums.  The first omitted magnitude then gives the
strictly sharper, uniform rational enclosure

    pi.approx n <= 16/5,       halfPi.approx n <= 8/5.

Thus `pi <= 16/5` and `pi/2 <= 8/5` at the constructive `leRat` layer.  This is
genuine progress on the analytic side of the missing common-refinement bridge:
the previous substrate bound was only `pi <= 4`.  Retaining three alternating
magnitudes at `1/5` and one pair at `1/239` sharpens this further to the exact
Archimedean fence `pi <= 22/7`, hence `halfPi <= 11/7`.

The module also kernel-refutes a tempting but invalid shortcut.  The first
actual semicircle midpoint sum has limit at least `2`, whereas `halfPi <= 8/5`;
hence it is not equivalent to `halfPi`.  A fixed coarse quadrature cannot replace
the required limiting/geometric argument.

No decimal input, classical choice, new axiom, or unproved residual is used.
-/

import YMGap.Continuum.SemicircleValue

set_option maxHeartbeats 1200000

namespace YMGap.Continuum.SemicircleMachinBridgeBounds

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SemicircleIntegral

theorem cPart_even_telescope (k : Nat) (hk : 0 < k) :
    ∀ n : Nat,
      Pi.cPart k hk n + Pi.bMag k hk (2 * n) ≤ Pi.bMag k hk 0
  | 0 => by
      show (0 : Q') + Pi.bMag k hk 0 ≤ Pi.bMag k hk 0
      exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (Pi.bMag k hk 0)))
  | n + 1 => by
      rw [Pi.cPart_succ]
      unfold Pi.cTerm
      have hmag : Pi.bMag k hk (2 * n + 2) ≤ Pi.bMag k hk (2 * n + 1) :=
        Pi.bMag_antitone hk (2 * n + 1)
      have hadd :
          (Pi.cPart k hk n +
              (Pi.bMag k hk (2 * n) + -Pi.bMag k hk (2 * n + 1)))
              + Pi.bMag k hk (2 * n + 2)
            ≤ Pi.cPart k hk n + Pi.bMag k hk (2 * n) := by
        have hs := Q'.add_le_add_left
          (-Pi.bMag k hk (2 * n + 1))
          (Pi.bMag k hk (2 * n + 2)) (Pi.bMag k hk (2 * n + 1)) hmag
        have hs0 :
            -Pi.bMag k hk (2 * n + 1) + Pi.bMag k hk (2 * n + 2) ≤ 0 := by
          exact Q'.le_trans' _ _ _ hs
            (Q'.le_of_eqv (Q'.neg_add_self_eqv (Pi.bMag k hk (2 * n + 1))))
        have ht := Q'.add_le_add_left
          (Pi.cPart k hk n)
          (Pi.bMag k hk (2 * n) +
            (-Pi.bMag k hk (2 * n + 1) + Pi.bMag k hk (2 * n + 2)))
          (Pi.bMag k hk (2 * n) + 0)
          (Q'.add_le_add_left
            (Pi.bMag k hk (2 * n))
            (-Pi.bMag k hk (2 * n + 1) + Pi.bMag k hk (2 * n + 2))
            0 hs0)
        refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_)
          (Q'.le_trans' _ _ _ ht (Q'.le_of_eqv ?_))
        · -- reassociate the three magnitude terms
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (Pi.cPart k hk n) _ _
              (Q'.eqv_symm (Q'.add_assoc_eqv
                (Pi.bMag k hk (2 * n))
                (-Pi.bMag k hk (2 * n + 1))
                (Pi.bMag k hk (2 * n + 2))))) ?_
          exact Q'.eqv_symm (Q'.add_assoc_eqv
            (Pi.cPart k hk n)
            (Pi.bMag k hk (2 * n) + -Pi.bMag k hk (2 * n + 1))
            (Pi.bMag k hk (2 * n + 2)))
        · exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _))
      exact Q'.le_trans' _ _ _ hadd (cPart_even_telescope k hk n)

theorem cPart_le_first (k : Nat) (hk : 0 < k) (n : Nat) :
    Pi.cPart k hk n ≤ Pi.bMag k hk 0 := by
  have h0 : (0 : Q') ≤ Pi.bMag k hk (2 * n) := Pi.bMag_nonneg hk (2 * n)
  have hle : Pi.cPart k hk n ≤
      Pi.cPart k hk n + Pi.bMag k hk (2 * n) :=
    Q'.add_le_self_of_nonneg _ _ h0
  exact Q'.le_trans' _ _ _ hle (cPart_even_telescope k hk n)

/-- The alternating-series energy `S_n + b_(2n)` decreases at every step. -/
theorem cPart_even_energy_step (k : Nat) (hk : 0 < k) (n : Nat) :
    Pi.cPart k hk (n + 1) + Pi.bMag k hk (2 * (n + 1))
      ≤ Pi.cPart k hk n + Pi.bMag k hk (2 * n) := by
  rw [Pi.cPart_succ]
  unfold Pi.cTerm
  have hmag : Pi.bMag k hk (2 * n + 2) ≤ Pi.bMag k hk (2 * n + 1) :=
    Pi.bMag_antitone hk (2 * n + 1)
  have hs := Q'.add_le_add_left
    (-Pi.bMag k hk (2 * n + 1))
    (Pi.bMag k hk (2 * n + 2)) (Pi.bMag k hk (2 * n + 1)) hmag
  have hs0 :
      -Pi.bMag k hk (2 * n + 1) + Pi.bMag k hk (2 * n + 2) ≤ 0 :=
    Q'.le_trans' _ _ _ hs
      (Q'.le_of_eqv (Q'.neg_add_self_eqv (Pi.bMag k hk (2 * n + 1))))
  have ht := Q'.add_le_add_left
    (Pi.cPart k hk n)
    (Pi.bMag k hk (2 * n) +
      (-Pi.bMag k hk (2 * n + 1) + Pi.bMag k hk (2 * n + 2)))
    (Pi.bMag k hk (2 * n) + 0)
    (Q'.add_le_add_left
      (Pi.bMag k hk (2 * n))
      (-Pi.bMag k hk (2 * n + 1) + Pi.bMag k hk (2 * n + 2))
      0 hs0)
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_)
    (Q'.le_trans' _ _ _ ht (Q'.le_of_eqv ?_))
  · rw [show 2 * (n + 1) = 2 * n + 2 by omega]
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (Pi.cPart k hk n) _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv
          (Pi.bMag k hk (2 * n))
          (-Pi.bMag k hk (2 * n + 1))
          (Pi.bMag k hk (2 * n + 2))))) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv
      (Pi.cPart k hk n)
      (Pi.bMag k hk (2 * n) + -Pi.bMag k hk (2 * n + 1))
      (Pi.bMag k hk (2 * n + 2)))
  · exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _))

/-- `S_q+b_(2q) ≤ S_p+b_(2p)` whenever `p ≤ q`. -/
theorem cPart_even_energy_antitone (k : Nat) (hk : 0 < k) {p q : Nat}
    (hpq : p ≤ q) :
    Pi.cPart k hk q + Pi.bMag k hk (2 * q)
      ≤ Pi.cPart k hk p + Pi.bMag k hk (2 * p) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hpq
  subst q
  clear hpq
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      have hs := cPart_even_energy_step k hk (p + d)
      exact Q'.le_trans' _ _ _ hs ih

/-- Once at least one pair is retained, every later paired partial sum is
bounded by `cPart 1 + b_2`, the usual alternating-series three-magnitude upper
bound `b_0-b_1+b_2`. -/
theorem cPart_le_three_magnitudes_of_pos (k : Nat) (hk : 0 < k)
    {n : Nat} (hn : 1 ≤ n) :
    Pi.cPart k hk n ≤ Pi.cPart k hk 1 + Pi.bMag k hk 2 := by
  have h0 : (0 : Q') ≤ Pi.bMag k hk (2 * n) := Pi.bMag_nonneg hk (2 * n)
  have htoEnergy : Pi.cPart k hk n ≤
      Pi.cPart k hk n + Pi.bMag k hk (2 * n) :=
    Q'.add_le_self_of_nonneg _ _ h0
  have hanti := cPart_even_energy_antitone k hk hn
  exact Q'.le_trans' _ _ _ htoEnergy
    (Q'.le_trans' _ _ _ hanti (by
      show Pi.cPart k hk 1 + Pi.bMag k hk (2 * 1)
        ≤ Pi.cPart k hk 1 + Pi.bMag k hk 2
      exact Q'.le_of_eqv (Q'.eqv_refl _)))

theorem pi_approx_le_sixteen_fifths (n : Nat) :
    Pi.pi.approx n ≤ Q'.mkPos 16 5 (by decide) := by
  rw [Pi.pi_approx, Pi.at5_approx, Pi.at239_approx]
  have h5 : Pi.cPart 5 (by decide) n ≤ Q'.mkPos 1 5 (by decide) := by
    refine Q'.le_trans' _ _ _ (cPart_le_first 5 (by decide) n) ?_
    decide
  have h16 := Q'.mul_le_mul_of_nonneg_left
    (Pi.cPart 5 (by decide) n) (Q'.mkPos 1 5 (by decide)) (16 : Q') h5 (by decide)
  have h239 : (0 : Q') ≤ (4 : Q') * Pi.cPart 239 (by decide) n :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.le_trans' _ _ _ (Q'.le_refl' 0)
        (finSum_monotone_of_nonneg (Pi.cTerm 239 (by decide))
          (fun j => Pi.cTerm_nonneg (by decide) j) 0 n (Nat.zero_le n)))
  have hneg : -((4 : Q') * Pi.cPart 239 (by decide) n) ≤ 0 := by
    exact Q'.le_trans' _ _ _ (Q'.neg_le_neg h239) (by decide)
  have hsum := Q'.add_le_add h16 hneg
  exact Q'.le_trans' _ _ _ hsum (by decide)

theorem pi_leRat_sixteen_fifths :
    CReal.leRat Pi.pi (Q'.mkPos 16 5 (by decide)) :=
  CReal.leRat_of_eventually
    ⟨0, fun n _ => pi_approx_le_sixteen_fifths n⟩

theorem halfPi_approx_le_eight_fifths (n : Nat) :
    Pi.halfPi.approx n ≤ Q'.mkPos 8 5 (by decide) := by
  rw [Pi.halfPi_approx]
  have hmul := Q'.mul_le_mul_of_nonneg_left
    (Pi.pi.approx n) (Q'.mkPos 16 5 (by decide))
    (Q'.mkPos 1 2 (by decide)) (pi_approx_le_sixteen_fifths n) (by decide)
  exact Q'.le_trans' _ _ _ hmul (by decide)

theorem halfPi_leRat_eight_fifths :
    CReal.leRat Pi.halfPi (Q'.mkPos 8 5 (by decide)) :=
  CReal.leRat_of_eventually
    ⟨0, fun n _ => halfPi_approx_le_eight_fifths n⟩

/-- The exact Machin-series Archimedean fence `pi.approx n ≤ 22/7`.
For positive stages, retain `b_0-b_1+b_2` above `atan(1/5)` and the first
paired term below `atan(1/239)`; stage zero is immediate. -/
theorem pi_approx_le_twenty_two_sevenths (n : Nat) :
    Pi.pi.approx n ≤ Q'.mkPos 22 7 (by decide) := by
  cases n with
  | zero =>
      rw [Pi.pi_approx, Pi.at5_approx, Pi.at239_approx]
      decide
  | succ m =>
      rw [Pi.pi_approx, Pi.at5_approx, Pi.at239_approx]
      have hn : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
      have h5 : Pi.cPart 5 (by decide) (m + 1)
          ≤ Pi.cPart 5 (by decide) 1 + Pi.bMag 5 (by decide) 2 :=
        cPart_le_three_magnitudes_of_pos 5 (by decide) hn
      have h16 := Q'.mul_le_mul_of_nonneg_left
        (Pi.cPart 5 (by decide) (m + 1))
        (Pi.cPart 5 (by decide) 1 + Pi.bMag 5 (by decide) 2)
        (16 : Q') h5 (by decide)
      have h239 : Pi.cPart 239 (by decide) 1
          ≤ Pi.cPart 239 (by decide) (m + 1) :=
        Pi.cPart_mono 239 (by decide) hn
      have h4 := Q'.mul_le_mul_of_nonneg_left
        (Pi.cPart 239 (by decide) 1)
        (Pi.cPart 239 (by decide) (m + 1)) (4 : Q') h239 (by decide)
      have hneg : -((4 : Q') * Pi.cPart 239 (by decide) (m + 1))
          ≤ -((4 : Q') * Pi.cPart 239 (by decide) 1) := Q'.neg_le_neg h4
      have hsum := Q'.add_le_add h16 hneg
      refine Q'.le_trans' _ _ _ hsum ?_
      show (16 : Q') *
            (Pi.cPart 5 (by decide) 1 + Pi.bMag 5 (by decide) 2)
          + -((4 : Q') * Pi.cPart 239 (by decide) 1)
        ≤ Q'.mkPos 22 7 (by decide)
      decide

theorem pi_leRat_twenty_two_sevenths :
    CReal.leRat Pi.pi (Q'.mkPos 22 7 (by decide)) :=
  CReal.leRat_of_eventually
    ⟨0, fun n _ => pi_approx_le_twenty_two_sevenths n⟩

theorem halfPi_approx_le_eleven_sevenths (n : Nat) :
    Pi.halfPi.approx n ≤ Q'.mkPos 11 7 (by decide) := by
  rw [Pi.halfPi_approx]
  have hmul := Q'.mul_le_mul_of_nonneg_left
    (Pi.pi.approx n) (Q'.mkPos 22 7 (by decide))
    (Q'.mkPos 1 2 (by decide)) (pi_approx_le_twenty_two_sevenths n) (by decide)
  exact Q'.le_trans' _ _ _ hmul (by decide)

theorem halfPi_leRat_eleven_sevenths :
    CReal.leRat Pi.halfPi (Q'.mkPos 11 7 (by decide)) :=
  CReal.leRat_of_eventually
    ⟨0, fun n _ => halfPi_approx_le_eleven_sevenths n⟩

theorem seqSemi_zero_geRat_two :
    ExpPos.geRat (seqSemi 0) (2 : Q') := by
  apply ExpPos.geRat_of_eventually
  refine ⟨0, fun m _ => ?_⟩
  rw [show seqSemi 0 = semiSum 1 (by decide) from rfl]
  unfold semiSum
  rw [CReal.csum_approx]
  rw [RationalTail.finSum_succ, RationalTail.finSum_zero, Q'.zero_add']
  show (2 : Q') ≤
    (CReal.mul (CReal.ofQ' (lebW 1 (by decide)))
      (nodeWeight 1 (by decide) 0)).approx m
  show (2 : Q') ≤ lebW 1 (by decide) * (nodeWeight 1 (by decide) 0).approx m
  unfold nodeWeight
  rw [dif_pos (by decide)]
  rw [CReal.sqrtFrom_approx]
  have hroot : (1 : Q') ≤
      CReal.heronSeq (oneMinusSqNode 1 0 (by decide) (by decide)) m := by
    refine Q'.le_trans' _ _ _ ?_
      (CReal.heronSeq_lb
        (oneMinusSqNode 1 0 (by decide) (by decide))
        (nodeLB 1 (by decide))
        (oneMinusSqNode_pos (by decide) (by decide))
        (nodeLB_pos (by decide))
        (nodeLB_sq_le (by decide) (by decide)) m)
    decide
  have hmul := Q'.mul_le_mul_of_nonneg_left
    (1 : Q')
    (CReal.heronSeq (oneMinusSqNode 1 0 (by decide) (by decide)) m)
    (lebW 1 (by decide)) hroot (lebW_nonneg (by decide))
  exact Q'.le_trans' _ _ _ (by decide) hmul

/-- The one-cell midpoint sum is genuinely too large to be the Machin target.
This kernel-checks the failure of the tempting finite-identification shortcut;
only a limiting/common-refinement argument can identify the value. -/
theorem not_equiv_seqSemi_zero_halfPi :
    ¬ CReal.Equiv (seqSemi 0) Pi.halfPi := by
  intro hEq
  have hupper : CReal.leRat (seqSemi 0) (Q'.mkPos 11 7 (by decide)) :=
    CReal.leRat_of_equiv hEq halfPi_leRat_eleven_sevenths
  let eps : Q' := Q'.mkPos 1 20 (by decide)
  have heps : (0 : Q') < eps := by
    unfold eps
    decide
  obtain ⟨Nlo, hlo⟩ := seqSemi_zero_geRat_two eps heps
  obtain ⟨Nhi, hhi⟩ := hupper eps heps
  let N := max Nlo Nhi
  have hloN : (2 : Q') ≤ (seqSemi 0).approx N + eps :=
    hlo N (Nat.le_max_left _ _)
  have hhiN : (seqSemi 0).approx N ≤ Q'.mkPos 11 7 (by decide) + eps :=
    hhi N (Nat.le_max_right _ _)
  have hadd : (seqSemi 0).approx N + eps ≤
      (Q'.mkPos 11 7 (by decide) + eps) + eps :=
    Q'.add_le_add_right _ _ _ hhiN
  have hbad : (2 : Q') ≤ (Q'.mkPos 11 7 (by decide) + eps) + eps :=
    Q'.le_trans' _ _ _ hloN hadd
  have hnot : ¬ ((2 : Q') ≤ (Q'.mkPos 11 7 (by decide) + eps) + eps) := by
    unfold eps
    decide
  exact hnot hbad

end YMGap.Continuum.SemicircleMachinBridgeBounds

#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.cPart_even_telescope
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.cPart_le_first
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.cPart_even_energy_step
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.cPart_even_energy_antitone
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.cPart_le_three_magnitudes_of_pos
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.pi_approx_le_sixteen_fifths
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.pi_leRat_sixteen_fifths
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.halfPi_approx_le_eight_fifths
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.halfPi_leRat_eight_fifths
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.pi_approx_le_twenty_two_sevenths
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.pi_leRat_twenty_two_sevenths
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.halfPi_approx_le_eleven_sevenths
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.halfPi_leRat_eleven_sevenths
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.seqSemi_zero_geRat_two
#print axioms YMGap.Continuum.SemicircleMachinBridgeBounds.not_equiv_seqSemi_zero_halfPi
