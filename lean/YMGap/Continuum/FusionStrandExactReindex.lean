/-
`FusionStrandExactReindex` closes the finite A1 coordinate change left open by
`FusionCoreStepRoundD`.

For fixed output channel `t`, every active cutoff-square pair `(a,b)` has the
unique strand form

    (a,b) = (t-p+r, p+r),

with `0 <= p <= t` and the sharp common cutoff

    r < N + 1 - max(p,t-p).

The proof below is a finite computation theorem rather than a large evaluated
certificate.  It expands each fusion indicator into its unique strand delta,
uses constructive finite Fubini to move the `(p,r)` coordinates outside, and
collapses the `(a,b)` delta exactly.  The sharp cutoff is then recovered by a
generic masked-prefix lemma.  Thus the kernel checks one proof for every
`N,t`, instead of normalizing a separate large rational sum at each cutoff.

Honest scope: this proves only A1,

    boxSum w N t ~= lineSum (lagCorr w N) t.

It does not prove the antidiagonal line-sum log-concavity (A3), the physical
half-time adjacent inequality, or a spacing-uniform Yang--Mills margin.

Constructive contract: Mathlib-free `Nat`/`Q'`; no `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.FusionBoxStrandCeilings

namespace YMGap.Continuum.FusionStrandExactReindex

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundG
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionBoxStrandCeilings

/-! ## 1. Generic exact-prefix computation -/

private theorem fsum_zero_extension {f : Nat -> Q'} {n m : Nat}
    (hnm : n <= m) (hz : forall i, n <= i -> (f i).eqv 0) :
    (fsum f m).eqv (fsum f n) := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      rw [fsum_succ]
      exact Q'.eqv_trans _ (fsum f n + 0) _
        (Q'.add_eqv_congr' ih (hz m hnm))
        (Q'.eqv_of_eq (Q'.add_zero' _))

/-- A bounded Boolean mask computes the same finite sum as its exact prefix.
This is the reusable computation-sound replacement for evaluating all of the
zero terms above the sharp strand cutoff. -/
private theorem fsum_masked_prefix (f : Nat -> Q') {n m : Nat}
    (hnm : n <= m) :
    (fsum (fun i => if i < n then f i else 0) m).eqv (fsum f n) := by
  have hext :
      (fsum (fun i => if i < n then f i else 0) m).eqv
        (fsum (fun i => if i < n then f i else 0) n) := by
    apply fsum_zero_extension hnm
    intro i hi
    rw [if_neg (Nat.not_lt_of_ge hi)]
    exact Q'.eqv_refl 0
  have hprefix :
      (fsum (fun i => if i < n then f i else 0) n).eqv (fsum f n) := by
    apply fsum_eqv_congr_lt
    intro i hi
    rw [if_pos hi]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hext hprefix

private theorem bool_true_or_not_true (b : Bool) :
    b = true \/ ¬ b = true := by
  cases b <;> simp

/-! ## 2. Exact collapse of one strand bucket -/

/-- The sharp-cutoff strand term.  Its mask is definitionally the cutoff in
`lagCorr_ccT`. -/
def truncatedStrandTerm (w : Q') (N t p r : Nat) : Q' :=
  if r < nP N t p then ccT w t p r else 0

/-- For a fixed strand coordinate `(p,r)`, summing its delta over the entire
cutoff square returns the common-strand weight exactly when both endpoints lie
in the square, and zero otherwise. -/
theorem strandBucket_eq_truncated (w : Q') (N t p r : Nat) :
    (fsum (fun a => fsum (fun b =>
      strandWindowKernel w a b t p r) (N + 1)) (N + 1)).eqv
      (truncatedStrandTerm w N t p r) := by
  by_cases hr : r < nP N t p
  · have hpmax : p <= Nat.max p (t - p) := Nat.le_max_left _ _
    have hqmax : t - p <= Nat.max p (t - p) := Nat.le_max_right _ _
    have haLt : (t - p) + r < N + 1 := by
      unfold nP at hr
      omega
    have hbLt : p + r < N + 1 := by
      unfold nP at hr
      omega
    have hinner :
        (fsum (fun b =>
          strandWindowKernel w ((t - p) + r) b t p r) (N + 1)).eqv
          (strandWindowKernel w ((t - p) + r) (p + r) t p r) := by
      apply fsum_collapse
      intro b hne
      unfold strandWindowKernel strandPointInd
      rcases bool_true_or_not_true
          ((((t - p) + r == (t - p) + r) && (b == p + r))) with hm | hm
      · have hm' := (Bool.and_eq_true _ _).mp hm
        exfalso
        exact hne (beq_iff_eq.mp hm'.2)
      · rw [if_neg hm]
        exact Q'.zero_mul_eqv _
      exact hbLt
    have houter :
        (fsum (fun a => fsum (fun b =>
          strandWindowKernel w a b t p r) (N + 1)) (N + 1)).eqv
          (fsum (fun b =>
            strandWindowKernel w ((t - p) + r) b t p r) (N + 1)) := by
      apply fsum_collapse
      intro a hne
      apply fsum_zero_below
      intro b _
      unfold strandWindowKernel strandPointInd
      rcases bool_true_or_not_true
          (((a == (t - p) + r) && (b == p + r))) with hm | hm
      · have hm' := (Bool.and_eq_true _ _).mp hm
        exfalso
        exact hne (beq_iff_eq.mp hm'.1)
      · rw [if_neg hm]
        exact Q'.zero_mul_eqv _
      exact haLt
    have hmatch :
        ((((t - p) + r == (t - p) + r) && (p + r == p + r))) = true := by
      exact (Bool.and_eq_true _ _).mpr
        ⟨beq_iff_eq.mpr rfl, beq_iff_eq.mpr rfl⟩
    have hind : strandPointInd ((t - p) + r) (p + r) t p r = 1 := by
      unfold strandPointInd
      rw [if_pos hmatch]
    have hterm :
        (strandWindowKernel w ((t - p) + r) (p + r) t p r).eqv
          (ccT w t p r) := by
      unfold strandWindowKernel
      rw [hind]
      exact Q'.one_mul_eqv _
    unfold truncatedStrandTerm
    rw [if_pos hr]
    exact Q'.eqv_trans _ _ _ houter
      (Q'.eqv_trans _ _ _ hinner hterm)
  · have hzero :
        (fsum (fun a => fsum (fun b =>
          strandWindowKernel w a b t p r) (N + 1)) (N + 1)).eqv 0 := by
      apply fsum_zero_below
      intro a ha
      apply fsum_zero_below
      intro b hb
      unfold strandWindowKernel strandPointInd
      rcases bool_true_or_not_true
          (((a == (t - p) + r) && (b == p + r))) with hm | hm
      · have hm' := (Bool.and_eq_true _ _).mp hm
        have ha' : a = (t - p) + r := beq_iff_eq.mp hm'.1
        have hb' : b = p + r := beq_iff_eq.mp hm'.2
        have hr' : r < nP N t p := by
          unfold nP
          rcases Nat.le_total p (t - p) with hpq | hqp
          · have hcut : r < N + 1 - (t - p) := by omega
            simpa only [Nat.max_eq_right hpq] using hcut
          · have hcut : r < N + 1 - p := by omega
            simpa only [Nat.max_eq_left hqp] using hcut
        exact False.elim (hr hr')
      · rw [if_neg hm]
        exact Q'.zero_mul_eqv _
    unfold truncatedStrandTerm
    rw [if_neg hr]
    exact hzero

/-! ## 3. Finite Fubini and the exact A1 reindex -/

/-- Expanding each cutoff-square fusion kernel into its unique strand delta
and applying finite Fubini puts the strand buckets on the outside. -/
theorem boxSum_eq_strandBuckets (w : Q') (N t : Nat) :
    (boxSum w N t).eqv
      (fsum (fun p => fsum (fun r =>
        fsum (fun a => fsum (fun b =>
          strandWindowKernel w a b t p r) (N + 1)) (N + 1))
        (N + 1)) (t + 1)) := by
  have eexpand : (boxSum w N t).eqv
      (fsum (fun a => fsum (fun b =>
        fsum (fun p => fsum (fun r =>
          strandWindowKernel w a b t p r) (N + 1))
          (t + 1)) (N + 1)) (N + 1)) := by
    unfold boxSum
    apply fsum_eqv_congr_lt
    intro a ha
    apply fsum_eqv_congr_lt
    intro b _
    exact boxKer_eq_strandWindow (by omega)
  have eswapBP :
      (fsum (fun a => fsum (fun b =>
        fsum (fun p => fsum (fun r =>
          strandWindowKernel w a b t p r) (N + 1))
          (t + 1)) (N + 1)) (N + 1)).eqv
      (fsum (fun a => fsum (fun p =>
        fsum (fun b => fsum (fun r =>
          strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (t + 1)) (N + 1)) := by
    apply fsum_eqv_congr
    intro a
    exact fsum_swap
      (fun b p => fsum (fun r =>
        strandWindowKernel w a b t p r) (N + 1))
      (N + 1) (t + 1)
  have eswapAP :
      (fsum (fun a => fsum (fun p =>
        fsum (fun b => fsum (fun r =>
          strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (t + 1)) (N + 1)).eqv
      (fsum (fun p => fsum (fun a =>
        fsum (fun b => fsum (fun r =>
          strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)) (t + 1)) :=
    fsum_swap
      (fun a p => fsum (fun b => fsum (fun r =>
        strandWindowKernel w a b t p r) (N + 1)) (N + 1))
      (N + 1) (t + 1)
  have ereorder :
      (fsum (fun p => fsum (fun a =>
        fsum (fun b => fsum (fun r =>
          strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)) (t + 1)).eqv
      (fsum (fun p => fsum (fun r =>
        fsum (fun a => fsum (fun b =>
          strandWindowKernel w a b t p r) (N + 1)) (N + 1))
        (N + 1)) (t + 1)) := by
    apply fsum_eqv_congr
    intro p
    have eBR :
        (fsum (fun a => fsum (fun b => fsum (fun r =>
          strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)).eqv
        (fsum (fun a => fsum (fun r => fsum (fun b =>
          strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)) := by
      apply fsum_eqv_congr
      intro a
      exact fsum_swap (fun b r =>
        strandWindowKernel w a b t p r) (N + 1) (N + 1)
    have eAR :
        (fsum (fun a => fsum (fun r => fsum (fun b =>
          strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)).eqv
        (fsum (fun r => fsum (fun a => fsum (fun b =>
          strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)) :=
      fsum_swap
        (fun a r => fsum (fun b =>
          strandWindowKernel w a b t p r) (N + 1))
        (N + 1) (N + 1)
    exact Q'.eqv_trans _ _ _ eBR eAR
  exact Q'.eqv_trans _ _ _ eexpand
    (Q'.eqv_trans _ _ _ eswapBP
      (Q'.eqv_trans _ _ _ eswapAP ereorder))

/-- **A1, discharged.**  The finite cutoff-square Clebsch sum is exactly the
antidiagonal line-sum of the sharply truncated lag correlation, for every
weight and every cutoff/channel. -/
theorem boxSum_eq_lineSum_lagCorr (w : Q') (N t : Nat) :
    (boxSum w N t).eqv (lineSum (lagCorr w N) t) := by
  have ebuckets := boxSum_eq_strandBuckets w N t
  have etruncated :
      (fsum (fun p => fsum (fun r =>
        fsum (fun a => fsum (fun b =>
          strandWindowKernel w a b t p r) (N + 1)) (N + 1))
        (N + 1)) (t + 1)).eqv
      (fsum (fun p => fsum (fun r =>
        truncatedStrandTerm w N t p r) (N + 1)) (t + 1)) := by
    apply fsum_eqv_congr_lt
    intro p _
    apply fsum_eqv_congr_lt
    intro r _
    exact strandBucket_eq_truncated w N t p r
  have eprefix :
      (fsum (fun p => fsum (fun r =>
        truncatedStrandTerm w N t p r) (N + 1)) (t + 1)).eqv
      (fsum (fun p => fsum (ccT w t p) (nP N t p)) (t + 1)) := by
    apply fsum_eqv_congr_lt
    intro p _
    unfold truncatedStrandTerm
    exact fsum_masked_prefix (ccT w t p) (Nat.sub_le _ _)
  have eline :
      (fsum (fun p => fsum (ccT w t p) (nP N t p)) (t + 1)).eqv
        (lineSum (lagCorr w N) t) := by
    unfold lineSum
    apply fsum_eqv_congr_lt
    intro p _
    rw [lagCorr_ccT]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ ebuckets
    (Q'.eqv_trans _ _ _ etruncated
      (Q'.eqv_trans _ _ _ eprefix eline))

/-- Once a proof of A3 is supplied, the now-closed A1 coordinate change
packages it into the existing `StrandReduction` consumer without any further
finite certificate. -/
def strandReductionOfLineSumLogConcave {w : Q'}
    (hline : forall N s,
      lineSum (lagCorr w N) s * lineSum (lagCorr w N) (s + 2) <=
        lineSum (lagCorr w N) (s + 1) *
          lineSum (lagCorr w N) (s + 1)) : StrandReduction w where
  reindex := boxSum_eq_lineSum_lagCorr w
  lineSumLogConcave := hline

end YMGap.Continuum.FusionStrandExactReindex

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusionStrandExactReindex.strandBucket_eq_truncated
#print axioms YMGap.Continuum.FusionStrandExactReindex.boxSum_eq_strandBuckets
#print axioms YMGap.Continuum.FusionStrandExactReindex.boxSum_eq_lineSum_lagCorr
#print axioms YMGap.Continuum.FusionStrandExactReindex.strandReductionOfLineSumLogConcave
