/-
Track 11.7-fusion / R4ao -- strand-linear integral certificates.

The direct cleared evaluator for a `p = 2` coefficient visits the whole
`(N+1) x (N+1)` cutoff square, even though the fusion rule leaves only the
active A1 strands.  This module proves once, for every cutoff and channel,
that the cleared sharp-strand evaluator is exactly the existing square
evaluator.  Concrete certificates can therefore normalize `O((t+1)N)`
active terms rather than `O(N^2)` masked terms.

This is a proof about the computation, not a second definition of the
physical coefficient.  Soundness is transported through the already-proved
exact A1 reindex and the common-denominator reconstruction theorem.

No `Classical`, `native_decide`, explicit proof hole, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.P2HalfTimeParityStrandCompiler

namespace YMGap.Continuum.P2HalfTimeStrandIntegralCertificate

set_option maxHeartbeats 12000000
set_option maxRecDepth 300000
set_option exponentiation.threshold 300000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.P2HalfTimeParityStrandCompiler
open YMGap.Continuum.P2RetunedFenceIntegralCertificate
open YMGap.Continuum.P2VacNormIntegralCertificate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

/-- One active A1 strand term after clearing `den^(2*C4(N))`. -/
def scaledStrandTermAt
    (num den N t p r : Nat) : Nat :=
  let a := p + r
  let b := (t - p) + r
  (a + 1) * (b + 1) * num ^ (c4 a + c4 b) *
    den ^ (2 * c4 N - (c4 a + c4 b))

/-- The cleared sharp lag-correlation at antidiagonal coordinate `p`. -/
def scaledLagCorrAt
    (num den N t p : Nat) : Nat :=
  natSum (fun r => scaledStrandTermAt num den N t p r) (nP N t p)

/-- The cleared exact A1 line sum.  Only active strand terms are visited. -/
def scaledLineSumAt
    (num den N t : Nat) : Nat :=
  natSum (fun p => scaledLagCorrAt num den N t p) (t + 1)

private theorem ofNat_eqv_injective {left right : Nat}
    (h : Q'.ofNat left ≈ Q'.ofNat right) : left = right := by
  unfold Q'.eqv Q'.ofNat Q'.den at h
  simpa using (Int.ofNat.inj h)

/-- Reconstruction of one active cleared strand term. -/
theorem scaledStrandTermAt_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N t p r : Nat) (hr : r < nP N t p) :
    Q'.ofNat (den ^ (2 * c4 N)) * ccT w t p r ≈
      Q'.ofNat (scaledStrandTermAt num den N t p r) := by
  have hpmax : p <= Nat.max p (t - p) := Nat.le_max_left _ _
  have hqmax : t - p <= Nat.max p (t - p) := Nat.le_max_right _ _
  have ha : p + r <= N := by
    unfold nP at hr
    omega
  have hb : (t - p) + r <= N := by
    unfold nP at hr
    omega
  have hac : c4 (p + r) <= c4 N :=
    YMGap.Continuum.SpectralLocalizationCrux.c4_le_c4 ha
  have hbc : c4 ((t - p) + r) <= c4 N :=
    YMGap.Continuum.SpectralLocalizationCrux.c4_le_c4 hb
  have he : c4 (p + r) + c4 ((t - p) + r) <= 2 * c4 N := by
    omega
  unfold ccT scaledStrandTermAt
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (YMGap.Continuum.FusionRDFactor.coeffW_mul_rd_sym
        (p + r) ((t - p) + r))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (qpow_eqv_congr_base hw
          (c4 (p + r) + c4 ((t - p) + r))))) ?_
  exact scale_monomialAt_eqv num den (2 * c4 N)
    (c4 (p + r) + c4 ((t - p) + r))
    ((p + r + 1) * ((t - p) + r + 1)) hden he

/-- Uniform reconstruction of the strand-linear evaluator. -/
theorem scaledLineSumAt_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N t : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) * lineSum (lagCorr w N) t ≈
      Q'.ofNat (scaledLineSumAt num den N t) := by
  unfold lineSum scaledLineSumAt
  apply scale_fsum_eqv
  intro p _
  rw [lagCorr_ccT]
  unfold scaledLagCorrAt
  apply scale_fsum_eqv
  intro r hr
  exact scaledStrandTermAt_reconstruct num den hden w hw N t p r hr

/-- The strand-linear and cutoff-square cleared evaluators are identical.
This theorem is the computation-theoretic bridge that makes the faster
evaluator a certificate for the original physical coefficient. -/
theorem scaledLineSumAt_eq_scaledCoeffAt
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N t : Nat) :
    scaledLineSumAt num den N t = scaledCoeffAt num den N t := by
  apply ofNat_eqv_injective
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (scaledLineSumAt_reconstruct num den hden w hw N t)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (bondMovedCoeff_eq_boxSum N t)
          (boxSum_eq_lineSum_lagCorr w N t)))) ?_
  exact scaledCoeffAt_reconstruct num den hden w hw N t

/-- Cleared exact half-time cell using the strand-linear evaluator. -/
def halfTimeStrandIntegralAt (num den N s : Nat) : Prop :=
  (s + 1) * scaledLineSumAt num den N (s + 1) * den ^ (s + 2) <=
    num ^ (s + 2) * ((s + 2) * scaledLineSumAt num den N s)

instance halfTimeStrandIntegralAtDecidable (num den N s : Nat) :
    Decidable (halfTimeStrandIntegralAt num den N s) := by
  unfold halfTimeStrandIntegralAt
  infer_instance

/-- A strand-linear cell implies the original square-evaluator cell. -/
theorem halfTimeIntegralTailAt_of_strand
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N s : Nat) (h : halfTimeStrandIntegralAt num den N s) :
    halfTimeIntegralTailAt num den N s := by
  unfold halfTimeStrandIntegralAt at h
  unfold halfTimeIntegralTailAt
  simpa only [
    scaledLineSumAt_eq_scaledCoeffAt num den hden w hw N s,
    scaledLineSumAt_eq_scaledCoeffAt num den hden w hw N (s + 1)] using h

/-- Rational soundness of a strand-linear half-time certificate. -/
theorem halfTimeStrandIntegralAt_sound
    (num den N s : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (h : halfTimeStrandIntegralAt num den N s) :
    dimQ s * bondMovedCoeff N w 2 (s + 1) <=
      qpow w (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s) :=
  halfTimeIntegralTailAt_sound num den N s hden w hw
    (halfTimeIntegralTailAt_of_strand num den hden w hw N s h)

/-! ## Bounded certificate reflection -/

/-- Boolean scan of strand-linear half-time cells on a consecutive interval. -/
def halfTimeStrandIntegralBlockCheck
    (num den N start length : Nat) : Bool :=
  (List.range length).all fun i =>
    decide (halfTimeStrandIntegralAt num den N (start + i))

/-- A successful strand-linear scan supplies every cell in its interval. -/
theorem halfTimeStrandIntegralBlockCheck_sound
    {num den N start length s : Nat}
    (hcheck : halfTimeStrandIntegralBlockCheck
      num den N start length = true)
    (hstart : start <= s) (hstop : s < start + length) :
    halfTimeStrandIntegralAt num den N s := by
  unfold halfTimeStrandIntegralBlockCheck at hcheck
  have hmem : s - start ∈ List.range length := by
    rw [List.mem_range]
    omega
  have hrow := List.all_eq_true.mp hcheck (s - start) hmem
  have hindex : start + (s - start) = s := by omega
  rw [hindex] at hrow
  exact of_decide_eq_true hrow

end YMGap.Continuum.P2HalfTimeStrandIntegralCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeStrandIntegralCertificate.scaledStrandTermAt_reconstruct
#print axioms YMGap.Continuum.P2HalfTimeStrandIntegralCertificate.scaledLineSumAt_reconstruct
#print axioms YMGap.Continuum.P2HalfTimeStrandIntegralCertificate.scaledLineSumAt_eq_scaledCoeffAt
#print axioms YMGap.Continuum.P2HalfTimeStrandIntegralCertificate.halfTimeIntegralTailAt_of_strand
#print axioms YMGap.Continuum.P2HalfTimeStrandIntegralCertificate.halfTimeStrandIntegralAt_sound
#print axioms YMGap.Continuum.P2HalfTimeStrandIntegralCertificate.halfTimeStrandIntegralBlockCheck_sound
