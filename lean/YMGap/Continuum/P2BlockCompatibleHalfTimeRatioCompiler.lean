/-
Track 11.7-fusion / R4g -- a half-time adjacent-ratio compiler for the
physical block-compatible coefficient tail.

The direct physical frontier is an exact fixed-power parity family.  This
module records a stronger but structurally simpler sufficient input:

```text
  (s+1) B(s+1) <= (s+2) w^(s+2) B(s).
```

The corrected two-fold retune satisfies

```text
  w^(s+2) <= renormWFix(2,w)^(2*s+3),
```

by the already-proved per-mode decay theorem followed by antitonicity in the
exponent.  Consequently one adjacent half-time inequality compiles directly
to each canonical coefficient-tail atom and hence to the reviewed all-cutoff
control family.  The schedule-wide half-time inequality itself remains the
honest analytic input; this file only proves the reduction and does not claim
that input.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleIntegralTailCertificate
import YMGap.Continuum.FusionStrandExactReindex

namespace YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.P2BlockCompatibleIntegralTailCertificate
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RGTransport

/-- The half-time power is dominated by the canonical two-fold retuned power.
This is the computation-theoretic part of the reduction: one general theorem
replaces scale-by-scale evaluation of the retuned exponent. -/
theorem halfTimePower_le_p2Retuned (w : Q')
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (s : Nat) :
    qpow w (s + 2) <= qpow (p2RetunedWeight w) (2 * s + 3) := by
  have hdecay : qpow w (s + 2) <=
      qpow (p2RetunedWeight w) (2 * (s + 2)) := by
    simpa only [p2RetunedWeight] using
      renormWFix_decay_dom 2 (by decide) w hw0 hw1 (s + 2)
  have hdrop : qpow (p2RetunedWeight w) (2 * (s + 2)) <=
      qpow (p2RetunedWeight w) (2 * s + 3) :=
    qpow_antitone (p2RetunedWeight_nonneg hw0)
      (p2RetunedWeight_le_one hw1) (2 * s + 3) (2 * (s + 2)) (by omega)
  exact Q'.le_trans' _ _ _ hdecay hdrop

/-- Stronger adjacent coefficient input at the original heat weight. -/
structure P2HalfTimeCoeffTailRatio (N : Nat) (w : Q')
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) : Type where
  tail : forall s, 1 <= s -> s < 2 * N ->
    dimQ s * bondMovedCoeff N w 2 (s + 1) <=
      qpow w (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s)

/-- The same half-time input in exact strand coordinates.  A1 is no longer an
open premise: `boxSum_eq_lineSum_lagCorr` turns the physical Clebsch box into
this sharply truncated lag-correlation line sum for every cutoff. -/
structure P2HalfTimeLineSumTailRatio (N : Nat) (w : Q') : Type where
  tail : forall s, 1 <= s -> s < 2 * N ->
    dimQ s * lineSum (lagCorr w N) (s + 1) <=
      qpow w (s + 2) *
        (dimQ (s + 1) * lineSum (lagCorr w N) s)

/-- Transport one line-sum half-time inequality through the exact A1 strand
reindex and the proved Clebsch double-sum formula. -/
def P2HalfTimeLineSumTailRatio.toCoeff {N : Nat} {w : Q'}
    (T : P2HalfTimeLineSumTailRatio N w) {hw0 : (0 : Q') <= w}
    {hw1 : w <= (1 : Q')} : P2HalfTimeCoeffTailRatio N w hw0 hw1 where
  tail := fun s hs hsN => by
    have hBondSucc : (bondMovedCoeff N w 2 (s + 1)).eqv
        (lineSum (lagCorr w N) (s + 1)) :=
      Q'.eqv_trans _ _ _ (bondMovedCoeff_eq_boxSum N (s + 1))
        (boxSum_eq_lineSum_lagCorr w N (s + 1))
    have hBond : (bondMovedCoeff N w 2 s).eqv
        (lineSum (lagCorr w N) s) :=
      Q'.eqv_trans _ _ _ (bondMovedCoeff_eq_boxSum N s)
        (boxSum_eq_lineSum_lagCorr w N s)
    have eLeft :
        (dimQ s * bondMovedCoeff N w 2 (s + 1)).eqv
          (dimQ s * lineSum (lagCorr w N) (s + 1)) :=
      Q'.mul_eqv_congr_left _ _ _ hBondSucc
    have eInner :
        (dimQ (s + 1) * lineSum (lagCorr w N) s).eqv
          (dimQ (s + 1) * bondMovedCoeff N w 2 s) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hBond)
    have eRight :
        (qpow w (s + 2) *
          (dimQ (s + 1) * lineSum (lagCorr w N) s)).eqv
          (qpow w (s + 2) *
            (dimQ (s + 1) * bondMovedCoeff N w 2 s)) :=
      Q'.mul_eqv_congr_left _ _ _ eInner
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eLeft)
      (Q'.le_trans' _ _ _ (T.tail s hs hsN) (Q'.le_of_eqv eRight))

/-- Compile the stronger half-time adjacent ratio to the exact local ratio
consumed by `CanonicalBulkControl`. -/
def P2HalfTimeCoeffTailRatio.toRetuned {N : Nat} {w : Q'}
    {hw0 : (0 : Q') <= w} {hw1 : w <= (1 : Q')}
    (T : P2HalfTimeCoeffTailRatio N w hw0 hw1) :
    P2RetunedCoeffTailRatio N w hw0 hw1 where
  tail := fun s hs hsN => by
    let x := dimQ (s + 1) * bondMovedCoeff N w 2 s
    have hx : (0 : Q') <= x :=
      Q'.mul_nonneg _ _ (dimQ_nonneg (s + 1))
        (bondMovedCoeff_nonneg N hw0 2 s)
    have hscale : qpow w (s + 2) * x <=
        qpow (p2RetunedWeight w) (2 * s + 3) * x :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        (halfTimePower_le_p2Retuned w hw0 hw1 s) hx
    exact Q'.le_trans' _ _ _ (T.tail s hs hsN) hscale

/-- The remaining physical half-time input, beginning after the four complete
direct coefficient scans. -/
structure BlockCompatibleP2HalfTimeCoeffTailFromFour : Type where
  tail : forall k, 4 <= k ->
    P2HalfTimeCoeffTailRatio (blockNcut k) (blockWeight k)
      (blockWeight_nonneg k) (blockWeight_le_one k)

/-- Install the half-time family into the existing exact coefficient-tail
frontier. -/
def BlockCompatibleP2HalfTimeCoeffTailFromFour.toCoeffTailFromFour
    (T : BlockCompatibleP2HalfTimeCoeffTailFromFour) :
    BlockCompatibleP2CoeffTailFromFour where
  tail := fun k hk => (T.tail k hk).toRetuned

/-- Combine the compiled half-time tail with the four checked physical
prefixes to obtain all-scale coefficient data. -/
def BlockCompatibleP2HalfTimeCoeffTailFromFour.toAllScale
    (T : BlockCompatibleP2HalfTimeCoeffTailFromFour) :
    BlockCompatibleP2CoeffTailData :=
  T.toCoeffTailFromFour.toAllScale

/-- The stronger half-time family reaches the reviewed canonical control
consumer through the existing coefficient compiler. -/
def BlockCompatibleP2HalfTimeCoeffTailFromFour.toControlFamily
    (T : BlockCompatibleP2HalfTimeCoeffTailFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toAllScale.toControlFamily

/-- The remaining schedule-wide input in exact strand coordinates. -/
structure BlockCompatibleP2HalfTimeLineSumTailFromFour : Type where
  tail : forall k, 4 <= k ->
    P2HalfTimeLineSumTailRatio (blockNcut k) (blockWeight k)

/-- Exact A1 reindexing compiles a schedule of line-sum inequalities into the
reviewed all-scale canonical control family. -/
def BlockCompatibleP2HalfTimeLineSumTailFromFour.toControlFamily
    (T : BlockCompatibleP2HalfTimeLineSumTailFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  (BlockCompatibleP2HalfTimeCoeffTailFromFour.mk fun k hk =>
    (T.tail k hk).toCoeff).toControlFamily

#print axioms halfTimePower_le_p2Retuned
#print axioms P2HalfTimeLineSumTailRatio.toCoeff
#print axioms P2HalfTimeCoeffTailRatio.toRetuned
#print axioms BlockCompatibleP2HalfTimeCoeffTailFromFour.toCoeffTailFromFour
#print axioms BlockCompatibleP2HalfTimeCoeffTailFromFour.toAllScale
#print axioms BlockCompatibleP2HalfTimeCoeffTailFromFour.toControlFamily
#print axioms BlockCompatibleP2HalfTimeLineSumTailFromFour.toControlFamily

end YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler
