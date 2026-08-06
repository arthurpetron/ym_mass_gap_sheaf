/-
Track 11.7-fusion / R2h -- a local-ratio compiler for the all-cutoff p=2 family.

# Result

The first positive-exponent certificate used the cell-dependent effective
weight `23/25`.  Exact cutoff scouting shows that this weight does not persist
past `N=3`.  The canonical two-fold retune is instead

```text
q(w) = renormWFix 2 w = 1 - (1-w)/2 = (1+w)/2.
```

At this base the fundamental comparison is already a theorem for every
rational `0 <= w <= 1` and every cutoff (`lamPW_le_retuned_fundamental`).  This
module therefore removes the vacuum and fundamental modes from the open
all-cutoff certificate and reduces every remaining mode to the local successor
ratio

```text
vacNorm(s+1) <= q(w)^(2*s+3) * vacNorm(s),   1 <= s < 2*N.
```

Telescoping these ratios gives the stronger zero-shift envelope

```text
fusionEig(s) <= q(w)^C4(s),   s <= 2*N,
```

and hence constructs the reviewed `CanonicalBulkControl N w 2`.  The local
tail-ratio family remains the honest all-cutoff analytic residual; it is
strictly sharper than an opaque family of full mode bounds because its base
case is physically discharged and each remaining atom compares adjacent
fusion modes.

# Constructivity

Pure `Q'`/`Nat` induction and existing exact Peter--Weyl identities.  No
`Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.FusedFundamentalDefectFreeRetune
import YMGap.Continuum.RebasedBulkLocalizationBridge
import YMGap.Continuum.FusionMarginMono

namespace YMGap.Continuum.P2RetunedRatioCompiler

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusedFundamentalDefectFreeRetune
open YMGap.Continuum.FusionMarginMono
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.RebasedBulkShift
open YMGap.Continuum.RebasedExpShiftSupportReduction
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

/-- The canonical effective weight for a two-fold physical fusion step. -/
def p2RetunedWeight (w : Q') : Q' := renormWFix 2 (by decide) w

theorem p2RetunedWeight_nonneg {w : Q'} (hw0 : (0 : Q') <= w) :
    (0 : Q') <= p2RetunedWeight w :=
  renormWFix_nonneg hw0 2 (by decide)

theorem p2RetunedWeight_le_one {w : Q'} (hw1 : w <= (1 : Q')) :
    p2RetunedWeight w <= (1 : Q') :=
  renormWFix_le_one hw1 2 (by decide)

/-- The canonical positive vacuum denominator for the `p=2` spectrum. -/
def p2DenomPos (N : Nat) {w : Q'} (hw0 : (0 : Q') <= w)
    (hw1 : w <= (1 : Q')) (s : Nat) :
    (0 : Q') < dimQ s * bondMovedCoeff N w 2 0 :=
  fusionEigDenom_pos s
    (S1Dominance.bmc_zero_pos N hw0 hw1 2 (by decide))

/-- The vacuum-normalized eigenvalue written with the canonical denominator. -/
def p2VacNorm (N : Nat) {w : Q'} (hw0 : (0 : Q') <= w)
    (hw1 : w <= (1 : Q')) (s : Nat) : Q' :=
  vacNorm N 2 (by decide) hw0 hw1 s

/-- `fusionEig` and `vacNorm` are the same normalized physical spectrum. -/
theorem fusionEig_eqv_p2VacNorm (N : Nat) {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (s : Nat) :
    fusionEig N w 2 s (p2DenomPos N hw0 hw1 s) ≈
      p2VacNorm N hw0 hw1 s :=
  Q'.eqv_refl _

/-- The normalized vacuum is exactly one. -/
theorem p2VacNorm_zero_eqv_one (N : Nat) {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) :
    p2VacNorm N hw0 hw1 0 ≈ (1 : Q') := by
  unfold p2VacNorm vacNorm
  refine divPos_eqv_of_eqv_mul _ ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.one_mul_eqv (dimQ 0 * bondMovedCoeff N w 2 0)) ?_
  rw [dimQ_zero]
  exact Q'.one_mul_eqv (bondMovedCoeff N w 2 0)

/-- The all-cutoff fundamental theorem, restated on the exact normalized
fusion eigenvalue and the canonical `p=2` retune. -/
theorem p2VacNorm_one_le_retuned (N : Nat) {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) :
    p2VacNorm N hw0 hw1 1 <=
      qpow (p2RetunedWeight w) (c4 1) := by
  have hfund := lamPW_le_retuned_fundamental hw0 hw1 N
  have hid := lamPW_eq_vacNorm_p2 hw0 hw1 N 0
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hid) hfund

/-- **The reduced all-cutoff residual.**  Only successor ratios strictly above
the already-closed fundamental mode remain.  The upper limit is the exact
two-fold Clebsch support edge. -/
structure P2RetunedTailRatio (N : Nat) (w : Q')
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) : Type where
  tail : forall s, 1 <= s -> s < 2 * N ->
    p2VacNorm N hw0 hw1 (s + 1) <=
      qpow (p2RetunedWeight w) (2 * s + 3) *
        p2VacNorm N hw0 hw1 s

/-- **Division-free reduced residual.**  This is the cross-multiplied form of
`P2RetunedTailRatio`: the common positive vacuum mass has been canceled and
only raw adjacent bond-moved coefficients remain. -/
structure P2RetunedCoeffTailRatio (N : Nat) (w : Q')
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) : Type where
  tail : forall s, 1 <= s -> s < 2 * N ->
    dimQ s * bondMovedCoeff N w 2 (s + 1) <=
      qpow (p2RetunedWeight w) (2 * s + 3) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s)

/-- The raw coefficient inequality implies the normalized adjacent-ratio
inequality.  The proof multiplies by the nonnegative vacuum coefficient,
reassociates the four factors, and applies constructive cross-quotient
monotonicity. -/
def p2TailRatio_of_coeffTail {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (T : P2RetunedCoeffTailRatio N w hw0 hw1) :
    P2RetunedTailRatio N w hw0 hw1 where
  tail := fun s hs1 hsN => by
    let q := qpow (p2RetunedWeight w) (2 * s + 3)
    let b0 := bondMovedCoeff N w 2 0
    let bs := bondMovedCoeff N w 2 s
    let bs1 := bondMovedCoeff N w 2 (s + 1)
    have hb0 : (0 : Q') <= b0 := bondMovedCoeff_nonneg N hw0 2 0
    have hscaled :
        (dimQ s * bs1) * b0 <= (q * (dimQ (s + 1) * bs)) * b0 :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (T.tail s hs1 hsN) hb0
    have hleft :
        bs1 * (dimQ s * b0) ≈ (dimQ s * bs1) * b0 := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv bs1 (dimQ s) b0)) ?_
      exact Q'.mul_eqv_congr_right _ _ b0 (Q'.mul_comm_eqv bs1 (dimQ s))
    have hright :
        (q * (dimQ (s + 1) * bs)) * b0 ≈
          (q * bs) * (dimQ (s + 1) * b0) := by
      have hinner :
          (dimQ (s + 1) * bs) * b0 ≈ bs * (dimQ (s + 1) * b0) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ b0
            (Q'.mul_comm_eqv (dimQ (s + 1)) bs)) ?_
        exact Q'.mul_assoc_eqv bs (dimQ (s + 1)) b0
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv q (dimQ (s + 1) * bs) b0) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left q _ _ hinner) ?_
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv q bs (dimQ (s + 1) * b0))
    have hcross :
        bs1 * (dimQ s * b0) <= (q * bs) * (dimQ (s + 1) * b0) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
    have hquot := divPos_le_divPos_of_cross
      bs1 (dimQ (s + 1) * b0) (q * bs) (dimQ s * b0)
      (p2DenomPos N hw0 hw1 (s + 1)) (p2DenomPos N hw0 hw1 s) hcross
    have hrightQuot :
        Q'.divPos (q * bs) (dimQ s * b0) (p2DenomPos N hw0 hw1 s) ≈
          q * p2VacNorm N hw0 hw1 s := by
      unfold p2VacNorm vacNorm Q'.divPos
      exact Q'.mul_assoc_eqv q bs
        (Q'.recipPos (dimQ s * b0) (p2DenomPos N hw0 hw1 s))
    exact Q'.le_trans' _ _ _ hquot (Q'.le_of_eqv hrightQuot)

/-- The local tail ratios telescope to the complete retuned heat envelope on
the exact finite support window. -/
theorem p2VacNorm_le_retuned_of_tail {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (T : P2RetunedTailRatio N w hw0 hw1) :
    forall s, s <= 2 * N ->
      p2VacNorm N hw0 hw1 s <=
        qpow (p2RetunedWeight w) (c4 s)
  | 0, _ =>
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (p2VacNorm_zero_eqv_one N hw0 hw1))
        (Q'.le_of_eqv (Q'.eqv_refl 1))
  | 1, _ => p2VacNorm_one_le_retuned N hw0 hw1
  | s + 2, hs => by
      have hsTail : s + 1 < 2 * N := by omega
      have hprev : p2VacNorm N hw0 hw1 (s + 1) <=
          qpow (p2RetunedWeight w) (c4 (s + 1)) :=
        p2VacNorm_le_retuned_of_tail hw0 hw1 T (s + 1) (by omega)
      have hstep := T.tail (s + 1) (by omega) hsTail
      have hpow0 : (0 : Q') <=
          qpow (p2RetunedWeight w) (2 * (s + 1) + 3) :=
        qpow_nonneg _ (p2RetunedWeight_nonneg hw0) _
      have hscaled :
          qpow (p2RetunedWeight w) (2 * (s + 1) + 3) *
              p2VacNorm N hw0 hw1 (s + 1) <=
            qpow (p2RetunedWeight w) (2 * (s + 1) + 3) *
              qpow (p2RetunedWeight w) (c4 (s + 1)) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hprev hpow0
      have hcombine :
          (qpow (p2RetunedWeight w) (2 * (s + 1) + 3) *
              qpow (p2RetunedWeight w) (c4 (s + 1))) ≈
            qpow (p2RetunedWeight w) (c4 (s + 2)) := by
        refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
        have hc4 :
            c4 (s + 2) = c4 (s + 1) + (2 * (s + 1) + 3) :=
          c4_succ (s + 1)
        rw [hc4]
        exact Q'.eqv_symm
          (qpow_add (p2RetunedWeight w) (c4 (s + 1))
            (2 * (s + 1) + 3))
      exact Q'.le_trans' _ _ _ hstep
        (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcombine))

/-- The telescoped envelope in the canonical `fusionEig` notation. -/
theorem fusionEig_le_retuned_of_tail {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (T : P2RetunedTailRatio N w hw0 hw1) (s : Nat)
    (hs : s <= 2 * N) :
    fusionEig N w 2 s (p2DenomPos N hw0 hw1 s) <=
      rateP (p2RetunedWeight w) s := by
  have h := p2VacNorm_le_retuned_of_tail hw0 hw1 T s hs
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (fusionEig_eqv_p2VacNorm N hw0 hw1 s)) h

/-- A zero-shift heat envelope is stronger than the required `1/12` finite
re-based shift. -/
def finiteExpShiftBridge_p2_of_tail {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (T : P2RetunedTailRatio N w hw0 hw1) :
    FiniteExpShiftBridge N w 2 (p2RetunedWeight w)
      (p2DenomPos N hw0 hw1) where
  rebasedBulkShift := fun s hs => by
    have hle := fusionEig_le_retuned_of_tail hw0 hw1 T s hs
    have hadd : fusionEig N w 2 s (p2DenomPos N hw0 hw1 s) <=
        rateP (p2RetunedWeight w) s + q112 := by
      have hrate : rateP (p2RetunedWeight w) s <=
          rateP (p2RetunedWeight w) s + q112 := by
        have h := Q'.add_le_add_left (rateP (p2RetunedWeight w) s)
          (0 : Q') q112 (by decide)
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv _))) h
      exact Q'.le_trans' _ _ _ hle hrate
    exact Q'.sub_le_of_le_add hadd

/-- **All-cutoff canonical compiler.**  The local tail-ratio datum, together
with the already-proved all-cutoff fundamental comparison, constructs the
reviewed physical `p=2` carrier. -/
def canonicalBulkControl_p2_of_tail {N : Nat} {w : Q'}
    (hN : 1 <= N) (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (hnc : (1 : Q') - w <= q112)
    (T : P2RetunedTailRatio N w hw0 hw1) :
    CanonicalBulkControl N w 2 where
  hN := hN
  hp := by decide
  hw0 := hw0
  hw1 := hw1
  hnc := hnc
  denomPos := p2DenomPos N hw0 hw1
  weff := p2RetunedWeight w
  hweff0 := p2RetunedWeight_nonneg hw0
  hweff1 := p2RetunedWeight_le_one hw1
  finiteShift := finiteExpShiftBridge_p2_of_tail hw0 hw1 T

/-- Division-free all-cutoff compiler. -/
def canonicalBulkControl_p2_of_coeffTail {N : Nat} {w : Q'}
    (hN : 1 <= N) (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (hnc : (1 : Q') - w <= q112)
    (T : P2RetunedCoeffTailRatio N w hw0 hw1) :
    CanonicalBulkControl N w 2 :=
  canonicalBulkControl_p2_of_tail hN hw0 hw1 hnc
    (p2TailRatio_of_coeffTail hw0 hw1 T)

end YMGap.Continuum.P2RetunedRatioCompiler

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedRatioCompiler.fusionEig_eqv_p2VacNorm
#print axioms YMGap.Continuum.P2RetunedRatioCompiler.p2VacNorm_zero_eqv_one
#print axioms YMGap.Continuum.P2RetunedRatioCompiler.p2VacNorm_one_le_retuned
#print axioms YMGap.Continuum.P2RetunedRatioCompiler.p2TailRatio_of_coeffTail
#print axioms YMGap.Continuum.P2RetunedRatioCompiler.p2VacNorm_le_retuned_of_tail
#print axioms YMGap.Continuum.P2RetunedRatioCompiler.fusionEig_le_retuned_of_tail
#print axioms YMGap.Continuum.P2RetunedRatioCompiler.finiteExpShiftBridge_p2_of_tail
#print axioms YMGap.Continuum.P2RetunedRatioCompiler.canonicalBulkControl_p2_of_tail
#print axioms YMGap.Continuum.P2RetunedRatioCompiler.canonicalBulkControl_p2_of_coeffTail
