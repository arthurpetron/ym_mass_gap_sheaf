/-
Track 11.7-fusion / R2n -- the all-cutoff first retuned p=2 edge.

The channel-two Clebsch box is first rewritten as diagonal/distance-two
pairs.  Five pairs form a closed rational head certificate.  Every later
pair is paid for by the adjacent channel-one cell using only the proved
log-concavity of `coeffW`; a final diagonal is handled separately.  Thus the
unbounded cutoff is discharged by finite-sum induction, not by an unbounded
mode evaluator.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedEdgeFormula
import YMGap.Continuum.P2RetunedStrongTuranCompiler
import YMGap.Continuum.MultiLinkFusionDefect

namespace YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.EndpointCutoffTailFormula
open YMGap.Continuum.FusionCoreStepRoundE
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.P2RetunedStrongTuranCompiler
open YMGap.Continuum.P2RetunedEdgeFormula
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

/-- The scalar on the right after replacing channel one by twice the
adjacent correlation. -/
def edgeScale : Q' :=
  RGTransport.qpow (p2RetunedWeight fenceW) 5 * dimQ 2

def edgeAdj (a : Nat) : Q' :=
  coeffW fenceW a * coeffW fenceW (a + 1)

def edgePair (a : Nat) : Q' :=
  coeffW fenceW (a + 1) * coeffW fenceW (a + 1) +
    Q'.ofNat 2 * (coeffW fenceW a * coeffW fenceW (a + 2))

/-- The five-pair head is the smallest convenient exact block that absorbs
the exceptional bottom distance-two cell. -/
theorem edgeHeadFive :
    fsum edgePair 5 ≤ edgeScale * fsum edgeAdj 5 := by
  decide

/-- The two base adjacent-ratio constants fit below the physical retuned
edge scale.  This is the sole closed arithmetic atom in the infinite tail. -/
theorem edgeRatioBase :
    coeffW fenceW 2 * coeffW fenceW 2 +
        Q'.ofNat 2 * (coeffW fenceW 1 * coeffW fenceW 3) ≤
      edgeScale * (coeffW fenceW 1 * coeffW fenceW 2) := by
  decide

private def jumpLeftExpr : PolyExpr :=
  .mul (.mul (.const 2) (.mul (.var 0) (.var 1)))
    (.mul (.var 2) (.var 3))

private def jumpMiddleExpr : PolyExpr :=
  .mul (.mul (.const 2) (.mul (.var 0) (.var 2)))
    (.mul (.var 1) (.var 3))

private theorem jumpLeft_normal :
    normalize jumpLeftExpr = normalize jumpMiddleExpr := by decide

private theorem jumpLeft_rearrange (x z c1 c2 : Q') :
    (Q'.ofNat 2 * (x * z)) * (c1 * c2) ≈
      (Q'.ofNat 2 * (x * c1)) * (z * c2) := by
  change
    (eval (fun i => if i = 0 then x else if i = 1 then z else
      if i = 2 then c1 else c2) jumpLeftExpr).eqv
    (eval (fun i => if i = 0 then x else if i = 1 then z else
      if i = 2 then c1 else c2) jumpMiddleExpr)
  exact poly_identity_of_normal_eq _ _ jumpLeft_normal _

private def jumpRightExpr : PolyExpr :=
  .mul (.mul (.const 2) (.mul (.var 0) (.var 1)))
    (.mul (.var 2) (.var 3))

private def jumpRightPackedExpr : PolyExpr :=
  .mul (.mul (.var 0) (.var 2))
    (.mul (.const 2) (.mul (.var 1) (.var 3)))

private theorem jumpRight_normal :
    normalize jumpRightExpr = normalize jumpRightPackedExpr := by decide

private theorem jumpRight_rearrange (x c1 y c3 : Q') :
    (Q'.ofNat 2 * (x * c1)) * (y * c3) ≈
      (x * y) * (Q'.ofNat 2 * (c1 * c3)) := by
  change
    (eval (fun i => if i = 0 then x else if i = 1 then c1 else
      if i = 2 then y else c3) jumpRightExpr).eqv
    (eval (fun i => if i = 0 then x else if i = 1 then c1 else
      if i = 2 then y else c3) jumpRightPackedExpr)
  exact poly_identity_of_normal_eq _ _ jumpRight_normal _

private def cancelRightExpr : PolyExpr :=
  .mul (.mul (.var 0) (.var 1))
    (.mul (.var 2) (.mul (.var 3) (.var 4)))

private def cancelRightPackedExpr : PolyExpr :=
  .mul (.mul (.var 3) (.var 4))
    (.mul (.var 2) (.mul (.var 0) (.var 1)))

private theorem cancelRight_normal :
    normalize cancelRightExpr = normalize cancelRightPackedExpr := by decide

private theorem cancelRight_rearrange (x y R c1 c2 : Q') :
    (x * y) * (R * (c1 * c2)) ≈ (c1 * c2) * (R * (x * y)) := by
  change
    (eval (fun i => if i = 0 then x else if i = 1 then y else
      if i = 2 then R else if i = 3 then c1 else c2) cancelRightExpr).eqv
    (eval (fun i => if i = 0 then x else if i = 1 then y else
      if i = 2 then R else if i = 3 then c1 else c2) cancelRightPackedExpr)
  exact poly_identity_of_normal_eq _ _ cancelRight_normal _

private theorem pair_le_of_cross_ratios
    {x y z c1 c2 c3 R : Q'}
    (hx0 : (0 : Q') ≤ x) (hy0 : (0 : Q') ≤ y)
    (hc10 : (0 : Q') ≤ c1) (hc20 : (0 : Q') ≤ c2)
    (hfac : (0 : Q') < c1 * c2)
    (hr1 : y * c1 ≤ x * c2)
    (hr2 : z * c2 ≤ y * c3)
    (hbase : c2 * c2 + Q'.ofNat 2 * (c1 * c3) ≤ R * (c1 * c2)) :
    y * y + Q'.ofNat 2 * (x * z) ≤ R * (x * y) := by
  have hyc2 : (0 : Q') ≤ y * c2 := Q'.mul_nonneg _ _ hy0 hc20
  have hdiag0 := Q'.mul_le_mul_of_nonneg_right _ _ (y * c2) hr1 hyc2
  have hdiag :
      (y * y) * (c1 * c2) ≤ (x * y) * (c2 * c2) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (FusionGenFunction.mul_swap4 y c1 y c2)))
      (Q'.le_trans' _ _ _ hdiag0
        (Q'.le_of_eqv (FusionGenFunction.mul_swap4 x c2 y c2)))
  have htwo0 : (0 : Q') ≤ Q'.ofNat 2 * (x * c1) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hx0 hc10)
  have hjump0 := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat 2 * (x * c1)) hr2 htwo0
  have hjump :
      (Q'.ofNat 2 * (x * z)) * (c1 * c2) ≤
        (x * y) * (Q'.ofNat 2 * (c1 * c3)) := by
    -- Both endpoint rearrangements are commutative-semiring identities.
    have hL := jumpLeft_rearrange x z c1 c2
    have hR := jumpRight_rearrange x c1 y c3
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
      (Q'.le_trans' _ _ _ hjump0 (Q'.le_of_eqv hR))
  have hadd := Q'.add_le_add hdiag hjump
  have hpackL :
      (y * y + Q'.ofNat 2 * (x * z)) * (c1 * c2) ≈
        (y * y) * (c1 * c2) +
          (Q'.ofNat 2 * (x * z)) * (c1 * c2) :=
    Q'.add_mul_eqv _ _ _
  have hpackR :
      (x * y) * (c2 * c2 + Q'.ofNat 2 * (c1 * c3)) ≈
        (x * y) * (c2 * c2) +
          (x * y) * (Q'.ofNat 2 * (c1 * c3)) :=
    Q'.mul_add_eqv _ _ _
  have hsum :
      (y * y + Q'.ofNat 2 * (x * z)) * (c1 * c2) ≤
        (x * y) * (c2 * c2 + Q'.ofNat 2 * (c1 * c3)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hpackL)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (Q'.eqv_symm hpackR)))
  have hxy0 : (0 : Q') ≤ x * y := Q'.mul_nonneg _ _ hx0 hy0
  have hbaseScaled := Q'.mul_le_mul_of_nonneg_left _ _ (x * y) hbase hxy0
  have hchain :
      (c1 * c2) * (y * y + Q'.ofNat 2 * (x * z)) ≤
        (c1 * c2) * (R * (x * y)) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) ?_
    refine Q'.le_trans' _ _ _ hsum ?_
    refine Q'.le_trans' _ _ _ hbaseScaled ?_
    -- Reassociate and commute the four scalar factors.
    exact Q'.le_of_eqv (cancelRight_rearrange x y R c1 c2)
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos hfac hchain

/-- Every nonexceptional diagonal/distance-two pair is paid by the adjacent
channel-one cell.  The proof uses two shifted instances of single-step
Hankel log-concavity and the single closed base-ratio atom above. -/
theorem edgePair_le (a : Nat) (ha : 1 ≤ a) :
    edgePair a ≤ edgeScale * edgeAdj a := by
  have hwp : (0 : Q') < fenceW := by decide
  have hr1 :
      coeffW fenceW (a + 1) * coeffW fenceW 1 ≤
        coeffW fenceW a * coeffW fenceW 2 := by
    cases a with
    | zero => omega
    | succ a' =>
        cases a' with
        | zero => exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
        | succ k =>
            have h := coeffW_step fenceW_nonneg fenceW_le_one hwp 1 k
            have hk :
                coeffW fenceW 1 * coeffW fenceW (k + 3) ≤
                  coeffW fenceW 2 * coeffW fenceW (k + 2) := by
              rw [show k + 3 = 1 + k + 2 by omega,
                show 2 = 1 + 1 by omega,
                show k + 2 = 1 + k + 1 by omega]
              exact h
            exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
              (Q'.le_trans' _ _ _ hk
                (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  have hr2 :
      coeffW fenceW (a + 2) * coeffW fenceW 2 ≤
        coeffW fenceW (a + 1) * coeffW fenceW 3 := by
    cases a with
    | zero => omega
    | succ a' =>
        cases a' with
        | zero => exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
        | succ k =>
            have h := coeffW_step fenceW_nonneg fenceW_le_one hwp 2 k
            have hk :
                coeffW fenceW 2 * coeffW fenceW (k + 4) ≤
                  coeffW fenceW 3 * coeffW fenceW (k + 3) := by
              rw [show k + 4 = 2 + k + 2 by omega,
                show 3 = 2 + 1 by omega,
                show k + 3 = 2 + k + 1 by omega]
              exact h
            exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
              (Q'.le_trans' _ _ _ hk
                (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  unfold edgePair edgeAdj
  exact pair_le_of_cross_ratios
    (coeffW_nonneg fenceW_nonneg a)
    (coeffW_nonneg fenceW_nonneg (a + 1))
    (coeffW_nonneg fenceW_nonneg 1)
    (coeffW_nonneg fenceW_nonneg 2)
    (Q'.mul_pos (FusionResidualBound.coeffW_pos hwp 1)
      (FusionResidualBound.coeffW_pos hwp 2))
    hr1 hr2 edgeRatioBase

theorem edgeTerminalBase :
    coeffW fenceW 1 ≤ edgeScale * coeffW fenceW 0 := by
  decide

/-- The unpaired top diagonal is paid by the final adjacent cell. -/
theorem edgeTerminal_le (N : Nat) (hN : 1 ≤ N) :
    coeffW fenceW N * coeffW fenceW N ≤
      edgeScale * edgeAdj (N - 1) := by
  have hwp : (0 : Q') < fenceW := by decide
  have hratio0 := coeffW_ratio_le hwp fenceW_le_one (N - 1)
  have hratio :
      coeffW fenceW N * coeffW fenceW 0 ≤
        coeffW fenceW (N - 1) * coeffW fenceW 1 := by
    rw [show N = N - 1 + 1 by omega]
    exact hratio0
  have hprev0 : (0 : Q') ≤ coeffW fenceW (N - 1) :=
    coeffW_nonneg fenceW_nonneg _
  have hbaseScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (coeffW fenceW (N - 1)) edgeTerminalBase hprev0
  have hreorder :
      coeffW fenceW (N - 1) * (edgeScale * coeffW fenceW 0) ≈
        coeffW fenceW 0 * (edgeScale * coeffW fenceW (N - 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
  have hwithVac :
      coeffW fenceW 0 * coeffW fenceW N ≤
        coeffW fenceW 0 * (edgeScale * coeffW fenceW (N - 1)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ hratio
        (Q'.le_trans' _ _ _ hbaseScaled (Q'.le_of_eqv hreorder)))
  have hmode : coeffW fenceW N ≤ edgeScale * coeffW fenceW (N - 1) :=
    FusionQuotientCollapse.le_of_mul_le_mul_left_pos
      (FusionResidualBound.coeffW_pos hwp 0) hwithVac
  have hN0 : (0 : Q') ≤ coeffW fenceW N := coeffW_nonneg fenceW_nonneg _
  have hsquare := Q'.mul_le_mul_of_nonneg_right _ _ (coeffW fenceW N) hmode hN0
  unfold edgeAdj
  rw [show N - 1 + 1 = N by omega]
  refine Q'.le_trans' _ _ _ hsquare ?_
  exact Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)

private theorem fsum_const_mul (c : Q') (f : Nat → Q') : ∀ N,
    fsum (fun s => c * f s) N ≈ c * fsum f N
  | 0 => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | N + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (fsum_const_mul c f N)) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv c (fsum f N) (f N))

/-- Static pairing of the explicit channel-two bands: all distance-two cells
are paired with the following diagonal, leaving only the top diagonal. -/
theorem channelTwoFormula_eq_pairs (N : Nat) (hN : 1 ≤ N) :
    channelTwoFormula fenceW N ≈
      fsum edgePair (N - 1) + coeffW fenceW N * coeffW fenceW N := by
  let K := N - 1
  have hNK : N = K + 1 := by unfold K; omega
  have hpair :
      fsum edgePair K ≈
        fsum (channelTwoDiag fenceW) K +
          Q'.ofNat 2 * fsum (channelTwoJump fenceW) K := by
    unfold edgePair channelTwoDiag channelTwoJump
    refine Q'.eqv_trans _ _ _
      (fsum_add
        (fun a => coeffW fenceW (a + 1) * coeffW fenceW (a + 1))
        (fun a => Q'.ofNat 2 *
          (coeffW fenceW a * coeffW fenceW (a + 2))) K) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (fsum_const_mul (Q'.ofNat 2)
        (fun a => coeffW fenceW a * coeffW fenceW (a + 2)) K)
  rw [hNK]
  unfold channelTwoFormula
  simp only [Nat.add_sub_cancel, fsum]
  let D := fsum (channelTwoDiag fenceW) K
  let J := Q'.ofNat 2 * fsum (channelTwoJump fenceW) K
  let T := coeffW fenceW (K + 1) * coeffW fenceW (K + 1)
  have hreorder : (D + T) + J ≈ (D + J) + T := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv D T J) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left D _ _ (Q'.add_comm_eqv T J)) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv D J T)
  refine Q'.eqv_trans _ _ _ hreorder ?_
  exact Q'.add_eqv_congr_right _ _ T (Q'.eqv_symm hpair)

/-- The explicit channel-two band formula is bounded by the retuned scale
times the adjacent channel-one correlation, uniformly in the cutoff. -/
theorem channelTwoFormula_le_adjCorr (N : Nat) (hN : 1 ≤ N) :
    channelTwoFormula fenceW N ≤ edgeScale * adjCorr fenceW N := by
  by_cases hsmall : N ≤ 5
  · have cases : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> decide
  · have h6 : 6 ≤ N := by omega
    obtain ⟨M, rfl⟩ := Nat.le.dest h6
    have hpairSplit :
        fsum edgePair (6 + M - 1) ≈
          fsum edgePair 5 + fsum (fun j => edgePair (5 + j)) M := by
      rw [show 6 + M - 1 = 5 + M by omega]
      exact fsum_split_at edgePair 5 M
    have htailRaw :
        fsum (fun j => edgePair (5 + j)) M ≤
          fsum (fun j => edgeScale * edgeAdj (5 + j)) M :=
      fsum_mono_lt M (fun j _ => edgePair_le (5 + j) (by omega))
    have htail :
        fsum (fun j => edgePair (5 + j)) M ≤
          edgeScale * fsum (fun j => edgeAdj (5 + j)) M :=
      Q'.le_trans' _ _ _ htailRaw
        (Q'.le_of_eqv (fsum_const_mul edgeScale
          (fun j => edgeAdj (5 + j)) M))
    have hpaid :
        fsum edgePair 5 + fsum (fun j => edgePair (5 + j)) M ≤
          edgeScale * fsum edgeAdj 5 +
            edgeScale * fsum (fun j => edgeAdj (5 + j)) M :=
      Q'.add_le_add edgeHeadFive htail
    have hcollect :
        edgeScale * fsum edgeAdj 5 +
            edgeScale * fsum (fun j => edgeAdj (5 + j)) M ≈
          edgeScale *
            (fsum edgeAdj 5 + fsum (fun j => edgeAdj (5 + j)) M) :=
      Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
    have hpairs :
        fsum edgePair (6 + M - 1) ≤
          edgeScale *
            (fsum edgeAdj 5 + fsum (fun j => edgeAdj (5 + j)) M) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hpairSplit)
        (Q'.le_trans' _ _ _ hpaid (Q'.le_of_eqv hcollect))
    have hterminal := edgeTerminal_le (6 + M) (by omega)
    have hboth := Q'.add_le_add hpairs hterminal
    have hAdjSplit :
        adjCorr fenceW (6 + M) ≈
          (fsum edgeAdj 5 + fsum (fun j => edgeAdj (5 + j)) M) +
            edgeAdj (5 + M) := by
      unfold adjCorr edgeAdj
      rw [show 6 + M = (5 + M) + 1 by omega]
      simp only [fsum]
      exact Q'.add_eqv_congr_right _ _ _
        (fsum_split_at
          (fun a => coeffW fenceW a * coeffW fenceW (a + 1)) 5 M)
    have hcollectFinal :
        edgeScale *
              (fsum edgeAdj 5 + fsum (fun j => edgeAdj (5 + j)) M) +
            edgeScale * edgeAdj (6 + M - 1) ≈
          edgeScale * adjCorr fenceW (6 + M) := by
      rw [show 6 + M - 1 = 5 + M by omega]
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) ?_
      exact Q'.mul_eqv_congr_left edgeScale _ _ (Q'.eqv_symm hAdjSplit)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (channelTwoFormula_eq_pairs (6 + M) (by omega)))
      (Q'.le_trans' _ _ _ hboth (Q'.le_of_eqv hcollectFinal))

private def edgeLiftLHSExpr : PolyExpr :=
  .mul (.const 2) (.mul (.mul (.var 0) (.var 1)) (.var 2))

private def edgeLiftRHSExpr : PolyExpr :=
  .mul (.var 0) (.mul (.var 1) (.mul (.const 2) (.var 2)))

private theorem edgeLift_normal :
    normalize edgeLiftLHSExpr = normalize edgeLiftRHSExpr := by decide

private theorem edgeLift_rearrange (q D A : Q') :
    Q'.ofNat 2 * ((q * D) * A) ≈ q * (D * (Q'.ofNat 2 * A)) := by
  change
    (eval (fun i => if i = 0 then q else if i = 1 then D else A)
      edgeLiftLHSExpr).eqv
    (eval (fun i => if i = 0 then q else if i = 1 then D else A)
      edgeLiftRHSExpr)
  exact poly_identity_of_normal_eq _ _ edgeLift_normal _

/-- **All-cutoff first edge.**  The exceptional `s=1` datum in the strong
Turan compiler is now fully discharged at the physical fence weight. -/
theorem fenceBoxEdgeAllCutoffs (N : Nat) (hN : 1 < 2 * N) :
    dimQ 1 * boxSum fenceW N 2 ≤
      RGTransport.qpow (p2RetunedWeight fenceW) 5 *
        (dimQ 2 * boxSum fenceW N 1) := by
  have hN1 : 1 ≤ N := by omega
  have hbox : boxSum fenceW N 2 ≤ edgeScale * adjCorr fenceW N :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (boxSum_two_eq_formula fenceW N))
      (channelTwoFormula_le_adjCorr N hN1)
  have hdim1 : (0 : Q') ≤ dimQ 1 := dimQ_nonneg 1
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (dimQ 1) hbox hdim1
  have hone := boxSum_one_eq_twice_adjCorr fenceW N
  change boxSum fenceW N 1 ≈
    Q'.ofNat 2 * adjCorr fenceW N at hone
  have hright :
      dimQ 1 * (edgeScale * adjCorr fenceW N) ≈
        RGTransport.qpow (p2RetunedWeight fenceW) 5 *
          (dimQ 2 * boxSum fenceW N 1) := by
    unfold dimQ edgeScale
    change Q'.ofNat 2 *
        ((RGTransport.qpow (p2RetunedWeight fenceW) 5 * Q'.ofNat 3) *
          adjCorr fenceW N) ≈
      RGTransport.qpow (p2RetunedWeight fenceW) 5 *
        (Q'.ofNat 3 * boxSum fenceW N 1)
    refine Q'.eqv_trans _ _ _
      (edgeLift_rearrange
        (RGTransport.qpow (p2RetunedWeight fenceW) 5)
        (Q'.ofNat 3) (adjCorr fenceW N)) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _ (Q'.eqv_symm hone))
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright)

/-- The sole remaining all-cutoff box obligation after the first-edge
discharge: the dimension-weighted strong-Turan family on `1 ≤ s`. -/
def FenceBoxTuranTail (N : Nat) : Prop :=
  forall s, 1 ≤ s -> s + 2 ≤ 2 * N ->
    (dimQ (s + 1) * boxSum fenceW N s) *
        (dimQ (s + 1) * boxSum fenceW N (s + 2)) ≤
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ (s + 2) * boxSum fenceW N (s + 1))) *
        (dimQ s * boxSum fenceW N (s + 1))

/-- Package a proof of the now-unique Turan residual with the discharged
all-cutoff edge. -/
def fenceBoxStrongTuranOfTail (N : Nat) (tail : FenceBoxTuranTail N) :
    P2RetunedBoxStrongTuran N fenceW fenceW_nonneg fenceW_le_one where
  edge := fenceBoxEdgeAllCutoffs N
  turan := tail

/-- The reviewed physical `CanonicalBulkControl` now consumes only the
uniform strong-Turan tail; no separate edge premise remains. -/
def fenceCanonicalBulkControlOfTuran (N : Nat) (hN : 1 ≤ N)
    (tail : FenceBoxTuranTail N) : CanonicalBulkControl N fenceW 2 :=
  canonicalBulkControl_p2_of_boxStrongTuran hN (by decide) fenceW_le_one
    fenceW_near_continuum (fenceBoxStrongTuranOfTail N tail)

end YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs.edgePair_le
#print axioms YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs.channelTwoFormula_eq_pairs
#print axioms YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs.channelTwoFormula_le_adjCorr
#print axioms YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs.fenceBoxEdgeAllCutoffs
#print axioms YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs.fenceBoxStrongTuranOfTail
#print axioms YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs.fenceCanonicalBulkControlOfTuran
