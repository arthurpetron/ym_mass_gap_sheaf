/-
Track 11.7-fusion / R2o -- exact top Clebsch shell for the retuned Turan family.

At cutoff `N`, the last three two-fold fusion coefficients have only one,
two, and four contributing pairs.  This module derives those formulas from
the cutoff recurrence and the exact Clebsch support predicate.  They are the
finite-combinatorial input for discharging the canonical boundary Turan atom
`s = 2*N-2` uniformly in `N`.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs
import YMGap.Continuum.BoxSumTailGeneral

namespace YMGap.Continuum.P2RetunedFenceTopShell

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BoxSumTailGeneral
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

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
        · exact q_add_zero_eqv _
      · subst hkn
        have hpre : fsum g k ≈ (0 : Q') :=
          fsum_zero_below k
            (fun i hi => hz i (Nat.lt_succ_of_lt hi) (Nat.ne_of_lt hi))
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hpre) ?_
        exact q_zero_add_eqv _

private theorem zeroFsumTerm (x : Q') :
    (0 : Q') + 0 * x ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 0 (0 * x) 0 (Q'.zero_mul_eqv x)) ?_
  exact q_zero_add_eqv 0

private theorem fusionInd_top_diag (N : Nat) :
    fusionInd N N (2 * N) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  simp only [Nat.max_self, Nat.min_self]
  refine ⟨by omega, by omega, ?_⟩
  have he : N + N + 2 * N = 2 * (2 * N) := by omega
  rw [he, Nat.mul_comm 2 (2 * N), Nat.mul_mod_left]

private theorem fusionInd_top_odd_diag (N : Nat) (hN : 1 ≤ N) :
    fusionInd N N (2 * N - 1) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff N N (2 * N - 1)).mp hok with ⟨_, _, hp⟩
  omega

private theorem fusionInd_top_even_diag (N : Nat) (hN : 1 ≤ N) :
    fusionInd N N (2 * N - 2) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  simp only [Nat.max_self, Nat.min_self]
  refine ⟨by omega, by omega, ?_⟩
  have he : N + N + (2 * N - 2) = 2 * (2 * N - 1) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 1), Nat.mul_mod_left]

/-- The new-cutoff contribution to the top channel is only its diagonal. -/
theorem boxSumDelta_top (w : Q') (N : Nat) :
    boxSumDelta w N (2 * (N + 1)) ≈
      coeffW w (N + 1) * coeffW w (N + 1) := by
  unfold boxSumDelta
  have hleft :
      fsum (fun a => fusionInd a (N + 1) (2 * (N + 1)) *
        (coeffW w a * coeffW w (N + 1))) (N + 1) ≈ 0 :=
    fsum_zero_below (N + 1) (fun a ha => by
      have hz : fusionInd a (N + 1) (2 * (N + 1)) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff a (N + 1) (2 * (N + 1))).mp hok with
          ⟨_, hhi, _⟩
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _)
  have hright :
      fsum (fun b => fusionInd (N + 1) b (2 * (N + 1)) *
        (coeffW w (N + 1) * coeffW w b)) (N + 1) ≈ 0 :=
    fsum_zero_below (N + 1) (fun b hb => by
      have hz : fusionInd (N + 1) b (2 * (N + 1)) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff (N + 1) b (2 * (N + 1))).mp hok with
          ⟨_, hhi, _⟩
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _)
  rw [fusionInd_top_diag (N + 1)]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hleft
      (Q'.add_eqv_congr' hright (Q'.one_mul_eqv _))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 0 (0 + _) _ (q_zero_add_eqv _)) ?_
  exact q_zero_add_eqv _

/-- The top box coefficient has exactly one Clebsch pair. -/
theorem boxSum_top (w : Q') (N : Nat) :
    boxSum w N (2 * N) ≈ coeffW w N * coeffW w N := by
  cases N with
  | zero =>
      unfold boxSum
      simp only [fsum]
      rw [fusionInd_top_diag 0]
      have hinner :
          (0 : Q') + 1 * (coeffW w 0 * coeffW w 0) ≈
            coeffW w 0 * coeffW w 0 := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left 0 _ _ (Q'.one_mul_eqv _)) ?_
        exact q_zero_add_eqv _
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 0 _ _ hinner) ?_
      exact q_zero_add_eqv _
  | succ K =>
      refine Q'.eqv_trans _ _ _ (boxSum_succ_decomp w K (2 * (K + 1))) ?_
      have hold : boxSum w K (2 * (K + 1)) ≈ 0 :=
        boxSum_tail w K (2 * (K + 1)) (by omega)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hold (boxSumDelta_top w K)) ?_
      exact q_zero_add_eqv _

/-- The penultimate channel receives the two orientations of `(N-1,N)`. -/
theorem boxSumDelta_top_odd (w : Q') (N : Nat) (hN : 1 ≤ N) :
    boxSumDelta w (N - 1) (2 * N - 1) ≈
      (coeffW w (N - 1) * coeffW w N) +
        (coeffW w (N - 1) * coeffW w N) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft :
      fsum (fun a => fusionInd a N (2 * N - 1) *
        (coeffW w a * coeffW w N)) N ≈
        coeffW w (N - 1) * coeffW w N := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N - 1) (n := N) (by omega)
        (fun a ha hne => ?_)) ?_
    · have hz : fusionInd a N (2 * N - 1) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff a N (2 * N - 1)).mp hok with ⟨_, hhi, _⟩
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _
    · have hone : fusionInd (N - 1) N (2 * N - 1) = (1 : Q') := by
        unfold fusionInd
        rw [if_pos]
        rw [fusionOK_eq_true_iff]
        have hmax : Nat.max (N - 1) N = N := Nat.max_eq_right (by omega)
        have hmin : Nat.min (N - 1) N = N - 1 := Nat.min_eq_left (by omega)
        rw [hmax, hmin]
        refine ⟨by omega, by omega, ?_⟩
        have he : N - 1 + N + (2 * N - 1) = 2 * (2 * N - 1) := by omega
        rw [he, Nat.mul_comm 2 (2 * N - 1), Nat.mul_mod_left]
      rw [hone]
      exact Q'.one_mul_eqv _
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 1) *
        (coeffW w N * coeffW w b)) N ≈
        coeffW w (N - 1) * coeffW w N := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N - 1) (n := N) (by omega)
        (fun b hb hne => ?_)) ?_
    · have hz : fusionInd N b (2 * N - 1) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff N b (2 * N - 1)).mp hok with ⟨_, hhi, _⟩
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _
    · have hone : fusionInd N (N - 1) (2 * N - 1) = (1 : Q') := by
        unfold fusionInd
        rw [if_pos]
        rw [fusionOK_eq_true_iff]
        have hmax : Nat.max N (N - 1) = N := Nat.max_eq_left (by omega)
        have hmin : Nat.min N (N - 1) = N - 1 := Nat.min_eq_right (by omega)
        rw [hmax, hmin]
        refine ⟨by omega, by omega, ?_⟩
        have he : N + (N - 1) + (2 * N - 1) = 2 * (2 * N - 1) := by omega
        rw [he, Nat.mul_comm 2 (2 * N - 1), Nat.mul_mod_left]
      rw [hone]
      refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
      exact Q'.mul_comm_eqv _ _
  rw [fusionInd_top_odd_diag N hN]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hleft
      (Q'.add_eqv_congr' hright (Q'.zero_mul_eqv _))) ?_
  exact Q'.add_eqv_congr_left _ _ _ (q_add_zero_eqv _)

/-- The penultimate box coefficient has exactly two ordered pairs. -/
theorem boxSum_top_odd (w : Q') (N : Nat) (hN : 1 ≤ N) :
    boxSum w N (2 * N - 1) ≈
      (coeffW w (N - 1) * coeffW w N) +
        (coeffW w (N - 1) * coeffW w N) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 1)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold : boxSum w (N - 1) (2 * N - 1) ≈ 0 :=
    boxSum_tail w (N - 1) (2 * N - 1) (by omega)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hold (boxSumDelta_top_odd w N hN)) ?_
  exact q_zero_add_eqv _

/-- The last even-shell increment contains the two orientations of
`(N-2,N)` and the new diagonal `(N,N)`. -/
theorem boxSumDelta_top_even (w : Q') (N : Nat) (hN : 2 ≤ N) :
    boxSumDelta w (N - 1) (2 * N - 2) ≈
      (coeffW w (N - 2) * coeffW w N) +
        ((coeffW w (N - 2) * coeffW w N) +
          coeffW w N * coeffW w N) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft :
      fsum (fun a => fusionInd a N (2 * N - 2) *
        (coeffW w a * coeffW w N)) N ≈
        coeffW w (N - 2) * coeffW w N := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N - 2) (n := N) (by omega)
        (fun a ha hne => ?_)) ?_
    · have hz : fusionInd a N (2 * N - 2) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff a N (2 * N - 2)).mp hok with
          ⟨_, hhi, hp⟩
        have haeq : a = N - 1 := by omega
        subst a
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _
    · have hone : fusionInd (N - 2) N (2 * N - 2) = (1 : Q') := by
        unfold fusionInd
        rw [if_pos]
        rw [fusionOK_eq_true_iff]
        have hmax : Nat.max (N - 2) N = N := Nat.max_eq_right (by omega)
        have hmin : Nat.min (N - 2) N = N - 2 := Nat.min_eq_left (by omega)
        rw [hmax, hmin]
        refine ⟨by omega, by omega, ?_⟩
        have he : N - 2 + N + (2 * N - 2) = 2 * (2 * N - 2) := by omega
        rw [he, Nat.mul_comm 2 (2 * N - 2), Nat.mul_mod_left]
      rw [hone]
      exact Q'.one_mul_eqv _
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 2) *
        (coeffW w N * coeffW w b)) N ≈
        coeffW w (N - 2) * coeffW w N := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N - 2) (n := N) (by omega)
        (fun b hb hne => ?_)) ?_
    · have hz : fusionInd N b (2 * N - 2) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff N b (2 * N - 2)).mp hok with
          ⟨_, hhi, hp⟩
        have hbeq : b = N - 1 := by omega
        subst b
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _
    · have hone : fusionInd N (N - 2) (2 * N - 2) = (1 : Q') := by
        unfold fusionInd
        rw [if_pos]
        rw [fusionOK_eq_true_iff]
        have hmax : Nat.max N (N - 2) = N := Nat.max_eq_left (by omega)
        have hmin : Nat.min N (N - 2) = N - 2 := Nat.min_eq_right (by omega)
        rw [hmax, hmin]
        refine ⟨by omega, by omega, ?_⟩
        have he : N + (N - 2) + (2 * N - 2) = 2 * (2 * N - 2) := by omega
        rw [he, Nat.mul_comm 2 (2 * N - 2), Nat.mul_mod_left]
      rw [hone]
      refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
      exact Q'.mul_comm_eqv _ _
  rw [fusionInd_top_even_diag N (by omega)]
  exact Q'.add_eqv_congr' hleft
    (Q'.add_eqv_congr' hright (Q'.one_mul_eqv _))

/-- The last even box coefficient has exactly four contributing pairs. -/
theorem boxSum_top_even (w : Q') (N : Nat) (hN : 2 ≤ N) :
    boxSum w N (2 * N - 2) ≈
      (coeffW w (N - 1) * coeffW w (N - 1)) +
        ((coeffW w (N - 2) * coeffW w N) +
          ((coeffW w (N - 2) * coeffW w N) +
            coeffW w N * coeffW w N)) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 2)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold := boxSum_top w (N - 1)
  rw [show 2 * (N - 1) = 2 * N - 2 by omega] at hold
  exact Q'.add_eqv_congr' hold (boxSumDelta_top_even w N hN)

/-! ## Boundary Turan reduction -/

def topShellUpper (B C : Q') : Q' :=
  B * B + (B * B + (B * B + C * C))

def topShellDouble (B : Q') : Q' := B + B

/-- A one-dimensional scalar fence for the canonical boundary shell.  All
Clebsch sums have disappeared; only the last two heat coefficients remain. -/
def TopShellScalarFence (N : Nat) : Prop :=
  let B := coeffW fenceW (N - 1)
  let C := coeffW fenceW N
  (dimQ (2 * N - 1) * dimQ (2 * N - 1)) * topShellUpper B C ≤
    (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
      (dimQ (2 * N) * dimQ (2 * N - 2))) *
        (topShellDouble B * topShellDouble B)

private def topScaleLeftExpr : PolyExpr :=
  .mul (.mul (.var 0) (.var 1))
    (.mul (.var 0) (.mul (.var 2) (.var 2)))

private def topScaleLeftPackedExpr : PolyExpr :=
  .mul (.mul (.mul (.var 0) (.var 0)) (.var 1))
    (.mul (.var 2) (.var 2))

private theorem topScaleLeft_normal :
    normalize topScaleLeftExpr = normalize topScaleLeftPackedExpr := by decide

private theorem topScaleLeft (D U C : Q') :
    (D * U) * (D * (C * C)) ≈ ((D * D) * U) * (C * C) := by
  change
    (eval (fun i => if i = 0 then D else if i = 1 then U else C)
      topScaleLeftExpr).eqv
    (eval (fun i => if i = 0 then D else if i = 1 then U else C)
      topScaleLeftPackedExpr)
  exact poly_identity_of_normal_eq _ _ topScaleLeft_normal _

private def topScaleRightExpr : PolyExpr :=
  .mul
    (.mul (.var 0) (.mul (.var 1)
      (.add (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4)))))
    (.mul (.var 2)
      (.add (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4))))

private def topScaleRightPackedExpr : PolyExpr :=
  .mul
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.add (.var 3) (.var 3)) (.add (.var 3) (.var 3))))
    (.mul (.var 4) (.var 4))

private theorem topScaleRight_normal :
    normalize topScaleRightExpr = normalize topScaleRightPackedExpr := by decide

private theorem topScaleRight (q H L B C : Q') :
    (q * (H * ((B * C) + (B * C)))) *
        (L * ((B * C) + (B * C))) ≈
      ((q * (H * L)) * (topShellDouble B * topShellDouble B)) * (C * C) := by
  unfold topShellDouble
  change
    (eval (fun i => if i = 0 then q else if i = 1 then H else
      if i = 2 then L else if i = 3 then B else C)
      topScaleRightExpr).eqv
    (eval (fun i => if i = 0 then q else if i = 1 then H else
      if i = 2 then L else if i = 3 then B else C)
      topScaleRightPackedExpr)
  exact poly_identity_of_normal_eq _ _ topScaleRight_normal _

/-- Heat-weight log-concavity bounds the four-term lower shell by three
copies of the middle square plus the top square. -/
theorem boxSum_top_even_le_upper (N : Nat) (hN : 2 ≤ N) :
    boxSum fenceW N (2 * N - 2) ≤
      topShellUpper (coeffW fenceW (N - 1)) (coeffW fenceW N) := by
  let A := coeffW fenceW (N - 2)
  let B := coeffW fenceW (N - 1)
  let C := coeffW fenceW N
  have hlc0 := FusionGenFunction.coeffW_logConcave
    fenceW_nonneg fenceW_le_one (N - 2)
  have hlc : A * C ≤ B * B := by
    simpa only [A, B, C, show N - 2 + 1 = N - 1 by omega,
      show N - 2 + 2 = N by omega] using hlc0
  have hsum :
      B * B + (A * C + (A * C + C * C)) ≤
        B * B + (B * B + (B * B + C * C)) :=
    Q'.add_le_add (Q'.le_refl' _) (Q'.add_le_add hlc
      (Q'.add_le_add hlc (Q'.le_refl' _)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (boxSum_top_even fenceW N hN)) hsum

/-- A proof of the scalar fence discharges the actual canonical boundary
strong-Turan atom `s = 2*N-2`. -/
theorem fenceTopShellTuran_of_scalar (N : Nat) (hN : 2 ≤ N)
    (hscalar : TopShellScalarFence N) :
    (dimQ (2 * N - 1) * boxSum fenceW N (2 * N - 2)) *
        (dimQ (2 * N - 1) * boxSum fenceW N (2 * N)) ≤
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ (2 * N) * boxSum fenceW N (2 * N - 1))) *
        (dimQ (2 * N - 2) * boxSum fenceW N (2 * N - 1)) := by
  let B := coeffW fenceW (N - 1)
  let C := coeffW fenceW N
  let D := dimQ (2 * N - 1)
  let H := dimQ (2 * N)
  let L := dimQ (2 * N - 2)
  let q := RGTransport.qpow (p2RetunedWeight fenceW) 2
  let U := topShellUpper B C
  have hg0 : boxSum fenceW N (2 * N - 2) ≤ U :=
    boxSum_top_even_le_upper N hN
  have hg2 : boxSum fenceW N (2 * N) ≈ C * C := by
    simpa only [C] using boxSum_top fenceW N
  have hg1 : boxSum fenceW N (2 * N - 1) ≈ (B * C) + (B * C) := by
    simpa only [B, C] using boxSum_top_odd fenceW N (by omega)
  have hD0 : (0 : Q') ≤ D := dimQ_nonneg _
  have hC0 : (0 : Q') ≤ C := coeffW_nonneg fenceW_nonneg _
  have hDC0 : (0 : Q') ≤ D * (C * C) :=
    Q'.mul_nonneg _ _ hD0 (Q'.mul_nonneg _ _ hC0 hC0)
  have hleft0 :
      (D * boxSum fenceW N (2 * N - 2)) *
          (D * boxSum fenceW N (2 * N)) ≤
        (D * U) * (D * (C * C)) := by
    have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ D hg0 hD0
    have hprod := Q'.mul_le_mul_of_nonneg_right _ _ (D * (C * C)) hfirst hDC0
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left D _ _ hg2))) hprod
  have hscalar' : (D * D) * U ≤
      (q * (H * L)) * (topShellDouble B * topShellDouble B) := by
    simpa only [TopShellScalarFence, B, C, D, H, L, q, U] using hscalar
  have hCC0 : (0 : Q') ≤ C * C := Q'.mul_nonneg _ _ hC0 hC0
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ (C * C) hscalar' hCC0
  have hmiddle : (D * U) * (D * (C * C)) ≤
      ((q * (H * L)) * (topShellDouble B * topShellDouble B)) * (C * C) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (topScaleLeft D U C)) hscaled
  have hright :
      ((q * (H * L)) * (topShellDouble B * topShellDouble B)) * (C * C) ≈
        (q * (H * boxSum fenceW N (2 * N - 1))) *
          (L * boxSum fenceW N (2 * N - 1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (topScaleRight q H L B C)) ?_
    exact mul_eqv_both
      (Q'.mul_eqv_congr_left q _ _ (Q'.mul_eqv_congr_left H _ _
        (Q'.eqv_symm hg1)))
      (Q'.mul_eqv_congr_left L _ _ (Q'.eqv_symm hg1))
  exact Q'.le_trans' _ _ _ hleft0
    (Q'.le_trans' _ _ _ hmiddle (Q'.le_of_eqv hright))

/-- The smallest nontrivial boundary atom is closed directly; the deliberately
coarse `3 B^2 + C^2` upper fence begins at `N=3`. -/
theorem fenceTopShellTuran_two :
    (dimQ 3 * boxSum fenceW 2 2) * (dimQ 3 * boxSum fenceW 2 4) ≤
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ 4 * boxSum fenceW 2 3)) *
        (dimQ 2 * boxSum fenceW 2 3) := by
  decide

theorem topShellScalarFence_three : TopShellScalarFence 3 := by
  unfold TopShellScalarFence
  decide

/-- Exact worst-dimension anchor used by the all-`N` scalar proof. -/
theorem topShellRatioAnchor :
    Q'.ofNat 9 *
        topShellUpper (coeffW fenceW 2) (coeffW fenceW 3) ≤
      RGTransport.qpow (p2RetunedWeight fenceW) 2 *
        (Q'.ofNat 35 * (coeffW fenceW 2 * coeffW fenceW 2)) := by
  decide

/-- Every later terminal heat-coefficient ratio is bounded by the anchor
ratio `c_3/c_2`.  This is a shifted instance of the proved Hankel
log-concavity theorem, not a numerical scan. -/
theorem topShellCoeffRatio (N : Nat) (hN : 3 ≤ N) :
    coeffW fenceW N * coeffW fenceW 2 ≤
      coeffW fenceW (N - 1) * coeffW fenceW 3 := by
  rcases Nat.eq_or_lt_of_le hN with rfl | h4
  · exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
  · have hwp : (0 : Q') < fenceW := by decide
    have h := FusionCoreStepRoundE.coeffW_step
      fenceW_nonneg fenceW_le_one hwp 2 (N - 4)
    have hk :
        coeffW fenceW 2 * coeffW fenceW N ≤
          coeffW fenceW 3 * coeffW fenceW (N - 1) := by
      have eN : 2 + (N - 4) + 2 = N := by omega
      have ePrev : 2 + (N - 4) + 1 = N - 1 := by omega
      have e3 : 2 + 1 = 3 := by omega
      rw [eN, ePrev, e3] at h
      exact h
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ hk (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

end YMGap.Continuum.P2RetunedFenceTopShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSumDelta_top
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSum_top
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSumDelta_top_odd
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSum_top_odd
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSumDelta_top_even
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSum_top_even
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSum_top_even_le_upper
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.fenceTopShellTuran_of_scalar
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.fenceTopShellTuran_two
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.topShellScalarFence_three
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.topShellRatioAnchor
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.topShellCoeffRatio
