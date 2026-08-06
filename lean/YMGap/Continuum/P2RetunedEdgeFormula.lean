/-
Track 11.7-fusion / R2m -- exact channel-two formula for the retuned edge.

The first open adjacent edge compares channels one and two.  Channel one is
already the adjacent correlation.  This module removes the remaining Clebsch
double sum from channel two: only the positive diagonal and distance-two
bands survive.  The identity is symbolic in the cutoff and is proved by the
cutoff-addition recurrence, not by enumerating cutoffs.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.EndpointCutoffTailFormula

namespace YMGap.Continuum.P2RetunedEdgeFormula

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private def channelTwoStepLHSExpr : PolyExpr :=
  .add (.add (.var 0) (.mul (.const 2) (.var 1)))
    (.add (.var 2) (.add (.var 2) (.var 3)))

private def channelTwoStepRHSExpr : PolyExpr :=
  .add (.add (.var 0) (.var 3))
    (.mul (.const 2) (.add (.var 1) (.var 2)))

private theorem channelTwoStep_normal :
    normalize channelTwoStepLHSExpr = normalize channelTwoStepRHSExpr := by
  decide

private theorem channelTwoStepAlgebra (D J A B : Q') :
    (D + Q'.ofNat 2 * J) + (A + (A + B)) ≈
      (D + B) + Q'.ofNat 2 * (J + A) := by
  change
    (eval (fun i => if i = 0 then D else if i = 1 then J else
      if i = 2 then A else B) channelTwoStepLHSExpr).eqv
    (eval (fun i => if i = 0 then D else if i = 1 then J else
      if i = 2 then A else B) channelTwoStepRHSExpr)
  exact poly_identity_of_normal_eq _ _ channelTwoStep_normal _

private theorem zeroFsumTerm (x : Q') :
    (0 : Q') + 0 * x ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 0 (0 * x) 0 (Q'.zero_mul_eqv x)) ?_
  exact QPoly.q_zero_add_eqv 0

private theorem zeroFsumNested (x : Q') :
    (0 : Q') + (0 + 0 * x) ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 0 (0 + 0 * x) 0 (zeroFsumTerm x)) ?_
  exact QPoly.q_zero_add_eqv 0

/-- Exact support classification in channel two: the diagonal begins at one,
and the only off-diagonal bands have distance two. -/
theorem fusionOK_two_iff (a b : Nat) :
    fusionOK a b 2 = true ↔
      (a = b ∧ 1 ≤ a) ∨ a + 2 = b ∨ b + 2 = a := by
  rw [fusionOK_eq_true_iff]
  constructor
  · rintro ⟨hlo, hhi, hpar⟩
    rcases Nat.le_total a b with hab | hba
    · have hmax : Nat.max a b = b := Nat.max_eq_right hab
      have hmin : Nat.min a b = a := Nat.min_eq_left hab
      rw [hmax, hmin] at hlo
      by_cases heq : a = b
      · exact Or.inl ⟨heq, by omega⟩
      · exact Or.inr (Or.inl (by omega))
    · have hmax : Nat.max a b = a := Nat.max_eq_left hba
      have hmin : Nat.min a b = b := Nat.min_eq_right hba
      rw [hmax, hmin] at hlo
      by_cases heq : a = b
      · exact Or.inl ⟨heq, by omega⟩
      · exact Or.inr (Or.inr (by omega))
  · intro h
    rcases h with ⟨rfl, ha⟩ | hab | hba
    · have hmax : Nat.max a a = a := Nat.max_self a
      have hmin : Nat.min a a = a := Nat.min_self a
      rw [hmax, hmin]
      refine ⟨by omega, by omega, ?_⟩
      have he : a + a + 2 = 2 * (a + 1) := by omega
      rw [he, Nat.mul_comm 2 (a + 1), Nat.mul_mod_left]
    · have hle : a ≤ b := by omega
      have hmax : Nat.max a b = b := Nat.max_eq_right hle
      have hmin : Nat.min a b = a := Nat.min_eq_left hle
      rw [hmax, hmin]
      refine ⟨by omega, by omega, ?_⟩
      have he : a + b + 2 = 2 * b := by omega
      rw [he, Nat.mul_comm 2 b, Nat.mul_mod_left]
    · have hle : b ≤ a := by omega
      have hmax : Nat.max a b = a := Nat.max_eq_left hle
      have hmin : Nat.min a b = b := Nat.min_eq_right hle
      rw [hmax, hmin]
      refine ⟨by omega, by omega, ?_⟩
      have he : a + b + 2 = 2 * a := by omega
      rw [he, Nat.mul_comm 2 a, Nat.mul_mod_left]

private theorem fsum_collapse_bounded {g : Nat → Q'} {k n : Nat}
    (hk : k < n) (hz : ∀ i, i < n → i ≠ k → g i ≈ (0 : Q')) :
    fsum g n ≈ g k := by
  induction n with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      show fsum g n + g n ≈ g k
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkn | hkn
      · have hlast : g n ≈ (0 : Q') :=
          hz n (Nat.lt_succ_self n) (fun h => by subst h; omega)
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (ih hkn ?_) hlast) ?_
        · intro i hi hne
          exact hz i (Nat.lt_succ_of_lt hi) hne
        · exact QPoly.q_add_zero_eqv _
      · subst hkn
        have hpre : fsum g k ≈ (0 : Q') :=
          fsum_zero_below k
            (fun i hi => hz i (Nat.lt_succ_of_lt hi) (Nat.ne_of_lt hi))
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hpre) ?_
        exact QPoly.q_zero_add_eqv _

/-- The first channel-two cutoff increment contains only the new diagonal
term. -/
theorem boxSumDelta_two_zero (w : Q') :
    boxSumDelta w 0 2 ≈ coeffW w 1 * coeffW w 1 := by
  unfold boxSumDelta fsum
  have h01 : fusionInd 0 1 2 = (0 : Q') := by decide
  have h10 : fusionInd 1 0 2 = (0 : Q') := by decide
  have h11 : fusionInd 1 1 2 = (1 : Q') := by decide
  rw [h01, h10, h11]
  simp only [fsum]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (zeroFsumTerm _)
      (Q'.add_eqv_congr' (zeroFsumTerm _) (Q'.one_mul_eqv _))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 0 (0 + coeffW w 1 * coeffW w 1)
      (coeffW w 1 * coeffW w 1) (QPoly.q_zero_add_eqv _)) ?_
  exact QPoly.q_zero_add_eqv _

/-- Every later channel-two cutoff increment contains the new diagonal term
and the two orientations of the distance-two band. -/
theorem boxSumDelta_two_succ (w : Q') (N : Nat) :
    boxSumDelta w (N + 1) 2 ≈
      (coeffW w N * coeffW w (N + 2)) +
        ((coeffW w N * coeffW w (N + 2)) +
          coeffW w (N + 2) * coeffW w (N + 2)) := by
  unfold boxSumDelta
  have hleft :
      fsum (fun a => fusionInd a (N + 2) 2 *
        (coeffW w a * coeffW w (N + 2))) (N + 2) ≈
        coeffW w N * coeffW w (N + 2) := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N) (n := N + 2) (by omega)
        (fun a ha hne => ?_)) ?_
    · have hzero : fusionInd a (N + 2) 2 = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_two_iff a (N + 2)).mp hok with hdiag | hforward | hback
        · omega
        · omega
        · omega
      rw [hzero]
      exact Q'.zero_mul_eqv _
    · have hone : fusionInd N (N + 2) 2 = (1 : Q') := by
        unfold fusionInd
        rw [if_pos ((fusionOK_two_iff N (N + 2)).2 (Or.inr (Or.inl (by omega))))]
      rw [hone]
      exact Q'.one_mul_eqv _
  have hright :
      fsum (fun b => fusionInd (N + 2) b 2 *
        (coeffW w (N + 2) * coeffW w b)) (N + 2) ≈
        coeffW w N * coeffW w (N + 2) := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N) (n := N + 2) (by omega)
        (fun b hb hne => ?_)) ?_
    · have hzero : fusionInd (N + 2) b 2 = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_two_iff (N + 2) b).mp hok with hdiag | hforward | hback
        · omega
        · omega
        · omega
      rw [hzero]
      exact Q'.zero_mul_eqv _
    · have hone : fusionInd (N + 2) N 2 = (1 : Q') := by
        unfold fusionInd
        rw [if_pos ((fusionOK_two_iff (N + 2) N).2 (Or.inr (Or.inr (by omega))))]
      rw [hone]
      refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
      exact Q'.mul_comm_eqv _ _
  have hdiag : fusionInd (N + 2) (N + 2) 2 = (1 : Q') := by
    unfold fusionInd
    rw [if_pos ((fusionOK_two_iff (N + 2) (N + 2)).2
      (Or.inl ⟨rfl, by omega⟩))]
  have hdiagTerm :
      fusionInd (N + 2) (N + 2) 2 *
          (coeffW w (N + 2) * coeffW w (N + 2)) ≈
        coeffW w (N + 2) * coeffW w (N + 2) := by
    rw [hdiag]
    exact Q'.one_mul_eqv _
  exact Q'.add_eqv_congr' hleft
    (Q'.add_eqv_congr' hright hdiagTerm)

/-- Diagonal band, indexed from representation one. -/
def channelTwoDiag (w : Q') (a : Nat) : Q' :=
  coeffW w (a + 1) * coeffW w (a + 1)

/-- Distance-two band, with one orientation. -/
def channelTwoJump (w : Q') (a : Nat) : Q' :=
  coeffW w a * coeffW w (a + 2)

/-- The explicit band formula for channel two. -/
def channelTwoFormula (w : Q') (N : Nat) : Q' :=
  fsum (channelTwoDiag w) N +
    Q'.ofNat 2 * fsum (channelTwoJump w) (N - 1)

/-- **Exact all-cutoff channel-two formula.** -/
theorem boxSum_two_eq_formula (w : Q') : ∀ N,
    boxSum w N 2 ≈ channelTwoFormula w N
  | 0 => by
      unfold boxSum channelTwoFormula
      simp only [fsum]
      have h00 : fusionInd 0 0 2 = (0 : Q') := by decide
      rw [h00]
      exact zeroFsumNested _
  | N + 1 => by
      cases N with
      | zero =>
          refine Q'.eqv_trans _ _ _ (boxSum_succ_decomp w 0 2) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (boxSum_two_eq_formula w 0)
              (boxSumDelta_two_zero w)) ?_
          unfold channelTwoFormula channelTwoDiag channelTwoJump
          simp only [fsum]
          let B := coeffW w 1 * coeffW w 1
          have hz2 : Q'.ofNat 2 * (0 : Q') ≈ 0 := Q'.mul_zero_eqv _
          have hbase : (0 : Q') + Q'.ofNat 2 * 0 ≈ 0 := by
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_left 0 _ 0 hz2) ?_
            exact QPoly.q_zero_add_eqv 0
          have hleft : ((0 : Q') + Q'.ofNat 2 * 0) + B ≈ B := by
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right _ 0 B hbase) ?_
            exact QPoly.q_zero_add_eqv B
          have hright : ((0 : Q') + B) + Q'.ofNat 2 * 0 ≈ B := by
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_left (0 + B) _ 0 hz2) ?_
            refine Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _) ?_
            exact QPoly.q_zero_add_eqv B
          exact Q'.eqv_trans _ B _ hleft (Q'.eqv_symm hright)
      | succ k =>
          refine Q'.eqv_trans _ _ _ (boxSum_succ_decomp w (k + 1) 2) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (boxSum_two_eq_formula w (k + 1))
              (boxSumDelta_two_succ w k)) ?_
          unfold channelTwoFormula channelTwoDiag channelTwoJump
          have hprev : k + 1 - 1 = k := by omega
          have hnext : k + 1 + 1 - 1 = k + 1 := by omega
          rw [hprev, hnext]
          change
            (fsum (channelTwoDiag w) (k + 1) +
                Q'.ofNat 2 * fsum (channelTwoJump w) k) +
              ((coeffW w k * coeffW w (k + 2)) +
                ((coeffW w k * coeffW w (k + 2)) +
                  coeffW w (k + 2) * coeffW w (k + 2))) ≈
            (fsum (channelTwoDiag w) (k + 1) + channelTwoDiag w (k + 1)) +
              Q'.ofNat 2 *
                (fsum (channelTwoJump w) k + channelTwoJump w k)
          unfold channelTwoDiag channelTwoJump
          exact channelTwoStepAlgebra _ _ _ _

end YMGap.Continuum.P2RetunedEdgeFormula

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedEdgeFormula.fusionOK_two_iff
#print axioms YMGap.Continuum.P2RetunedEdgeFormula.boxSumDelta_two_zero
#print axioms YMGap.Continuum.P2RetunedEdgeFormula.boxSumDelta_two_succ
#print axioms YMGap.Continuum.P2RetunedEdgeFormula.boxSum_two_eq_formula
