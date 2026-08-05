/-
Track 11.7-fusion / R2c -- finite-support reduction of the re-based exponential
shift bridge, plus a statement audit for the legacy saddle logarithm.

# Two kernel-visible facts

First, the truncated Clebsch--Gordan product has finite propagation.  Every
`fusionProduct N c d` vanishes above mode `2*N`, independently of the input
sequences.  Hence every positive fusion power `fusionPow ... (p+1)` and its
vacuum-normalized eigenvalue vanish there.  The all-mode field of
`RebasedBulkShift.ExpShiftBridge` is therefore equivalent (for nonnegative
`w_eff`) to only the finite family

    s <= 2*N.

`FiniteExpShiftBridge` records exactly that finite family, and
`expShiftBridge_of_finite` discharges the infinite tail structurally.  This is
the computation-theoretic reduction: no large canonical evaluation is needed
for modes outside the finite Clebsch cone.

Second, the legacy `CRealLogRangeReduction` does not constrain `logScale` by
`scale`.  The executable operation `shiftLogScale` keeps `x`, `scale`, `m`, and
the scaling proof fixed while adding an arbitrary constructive real to the
value returned by `CReal.log`; `log_shiftLogScale` proves the shift.  Thus the
old `SaddleLogForm.estimate` must not be treated as a faithful logarithmic
premise until that missing compatibility law is supplied.

To state the corrected finite saddle premise without changing any canonical
frontier field, this module introduces `DyadicLogReduction`: its scale is
literal dyadic data and its log-scale is definitionally the corresponding
signed multiple of the constructed `log 2`.  `FaithfulFiniteSaddleLogForm`
uses this deterministic rational logarithm only on the finite support window.
It is deliberately uninhabited here.  The remaining analytic step is now the
finite exp-Lipschitz transfer from that faithful estimate to
`FiniteExpShiftBridge`.

# Constructivity

Everything is computable `Nat`/`Q'`/`CReal` data.  There is no `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable definition.  All
load-bearing declarations are axiom-gated below.
-/

import YMGap.Continuum.RebasedBulkShift
import YMGap.Constructive.CRealAlg

namespace YMGap.Continuum.RebasedExpShiftSupportReduction

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.RebasedBulkShift

/-! ## 1. The legacy logarithm admits an arbitrary additive scale shift -/

/-- Change only the unconstrained `logScale` field of a general constructive-real
logarithm reduction.  The represented input, binary scale, mantissa, window
certificate, and scaling equality are all retained verbatim. -/
def shiftLogScale {x : CReal} (red : CRealLogRangeReduction x) (z : CReal) :
    CRealLogRangeReduction x where
  scale := red.scale
  m := red.m
  hm1 := red.hm1
  hyb := red.hyb
  scaling := red.scaling
  logScale := CReal.add z red.logScale

/-- **Statement fence for the legacy logarithm.**  Altering no represented
quantity, `shiftLogScale red z` adds the arbitrary value `z` to the result of
`CReal.log`.  Consequently a premise using the legacy reduction is not by
itself a pinned logarithmic estimate. -/
theorem log_shiftLogScale {x : CReal} (red : CRealLogRangeReduction x) (z : CReal) :
    CReal.Equiv
      (CReal.log x (shiftLogScale red z))
      (CReal.add z (CReal.log x red)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.add_assoc_eqv (z.approx n) (red.logScale.approx n)
      ((logRat red.m red.hm1 red.hyb).approx n))

/-! ## 2. A deterministic dyadic logarithm for rational values -/

/-- The constructive real `k * log 2`, built by primitive recursion. -/
def natLogTwo : Nat -> CReal
  | 0 => CReal.czero
  | k + 1 => CReal.add (natLogTwo k) log2

/-- The positive rational dyadic scale `2^up / 2^down`. -/
def dyadicScale (up down : Nat) : Q' :=
  Q'.ofNat (2 ^ up) * Q'.mkPos 1 (2 ^ down) (Nat.two_pow_pos down)

/-- The logarithm of `dyadicScale up down`, by construction:
`up * log 2 - down * log 2`. -/
def dyadicLogScale (up down : Nat) : CReal :=
  CReal.sub (natLogTwo up) (natLogTwo down)

/-- **Faithful rational logarithm data.**  Unlike
`CRealLogRangeReduction`, the logarithm of the scale is not a free `CReal`
field: the scale is literal dyadic data and `dyadicLogValue` computes its
log-scale definitionally. -/
structure DyadicLogReduction (q : Q') : Type where
  up : Nat
  down : Nat
  m : Q'
  hm1 : (0 : Q') < m + 1
  hyb : Q'.abs (yOf m hm1) <= recipOdd 1
  scaling : q.eqv (dyadicScale up down * m)

/-- The deterministic logarithm represented by a dyadic reduction. -/
def dyadicLogValue {q : Q'} (red : DyadicLogReduction q) : CReal :=
  CReal.add (dyadicLogScale red.up red.down)
    (logRat red.m red.hm1 red.hyb)

/-- A faithful dyadic reduction can be viewed as a legacy range reduction.
The reverse direction is intentionally absent because its free `logScale`
field need not be the logarithm of `scale`. -/
def DyadicLogReduction.toLegacy {q : Q'} (red : DyadicLogReduction q) :
    CRealLogRangeReduction (CReal.ofQ' q) where
  scale := CReal.ofQ' (dyadicScale red.up red.down)
  m := red.m
  hm1 := red.hm1
  hyb := red.hyb
  scaling := by
    have hscale : CReal.Equiv
        (CReal.ofQ' q)
        (CReal.ofQ' (dyadicScale red.up red.down * red.m)) :=
      SumOfSquares.Equiv_of_approx_eqv (fun _ => red.scaling)
    exact CReal.Equiv.trans hscale
      (CRealAlg.ofQ'_mul (dyadicScale red.up red.down) red.m)
  logScale := dyadicLogScale red.up red.down

/-- The legacy logarithm induced by a faithful dyadic reduction is exactly
the deterministic dyadic logarithm value. -/
theorem DyadicLogReduction.legacyLog_eq_value {q : Q'}
    (red : DyadicLogReduction q) :
    CReal.log (CReal.ofQ' q) red.toLegacy = dyadicLogValue red := rfl

/-- **Corrected finite-support saddle carrier.**  It asks for deterministic
dyadic logarithm data and the saddle estimate only on `s <= 2*N`, the exact
support window of every positive truncated fusion power.  This is a stronger,
faithful replacement premise; it is not inhabited in this module. -/
structure FaithfulFiniteSaddleLogForm (N : Nat) (w : Q') (p : Nat)
    (h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0) : Type where
  A : Q'
  eta : Q'
  logReduction : (s : Nat) -> s <= 2 * N ->
    DyadicLogReduction (fusionEig N w p s (h0' s))
  estimate : forall s (hs : s <= 2 * N), CReal.leEv
    (CReal.abs (CReal.add
      (dyadicLogValue (logReduction s hs))
      (CReal.ofQ' (A * Q'.ofNat (c4 s)))))
    (CReal.ofQ' (eta *
      (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))))

/-! ## 3. Finite propagation of the truncated fusion product -/

/-- A Clebsch--Gordan indicator vanishes above its triangle. -/
theorem fusionInd_zero_of_sum_lt (a b s : Nat) (h : a + b < s) :
    fusionInd a b s = (0 : Q') := by
  unfold fusionInd fusionOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [if_neg]
  intro hok
  exact (Nat.not_le_of_gt h) hok.1.2

/-- **Finite propagation.**  A truncated fusion product has no mode above
`2*N`, for arbitrary input sequences. -/
theorem fusionProduct_zero_above_two_cutoff (N : Nat) (c d : Nat -> Q')
    (s : Nat) (hs : 2 * N < s) :
    (fusionProduct N c d s).eqv 0 := by
  unfold fusionProduct
  refine fsum_zero_below (N + 1) (fun a ha => ?_)
  refine fsum_zero_below (N + 1) (fun b hb => ?_)
  have hab : a + b < s := by omega
  rw [fusionInd_zero_of_sum_lt a b s hab]
  exact Q'.zero_mul_eqv _

/-- Every positive fusion power inherits the same `2*N` support bound.  The
bound is independent of the exponent because each recursive product is
truncated back to input modes `0,...,N`. -/
theorem fusionPow_succ_zero_above_two_cutoff (N : Nat) (c : Nat -> Q')
    (p s : Nat) (hs : 2 * N < s) :
    (fusionPow N c (p + 1) s).eqv 0 :=
  fusionProduct_zero_above_two_cutoff N (fusionPow N c p) c s hs

/-- Heat-kernel bond-moving coefficients vanish above `2*N` at every positive
fusion exponent. -/
theorem bondMovedCoeff_succ_zero_above_two_cutoff (N : Nat) (w : Q')
    (p s : Nat) (hs : 2 * N < s) :
    (bondMovedCoeff N w (p + 1) s).eqv 0 :=
  fusionPow_succ_zero_above_two_cutoff N (coeffW w) p s hs

/-- The corresponding vacuum-normalized fusion eigenvalue vanishes exactly in
the tail: division by its positive vacuum denominator preserves the zero
numerator. -/
theorem fusionEig_succ_zero_above_two_cutoff {N : Nat} {w : Q'} {p s : Nat}
    (h0' : (0 : Q') < dimQ s * bondMovedCoeff N w (p + 1) 0)
    (hs : 2 * N < s) :
    (fusionEig N w (p + 1) s h0').eqv 0 := by
  unfold fusionEig Q'.divPos
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right
      (bondMovedCoeff N w (p + 1) s) 0
      (Q'.recipPos (dimQ s * bondMovedCoeff N w (p + 1) 0) h0')
      (bondMovedCoeff_succ_zero_above_two_cutoff N w p s hs))
    (Q'.zero_mul_eqv _)

/-- Order projection of exact tail vanishing, used by the finite bridge
compiler. -/
theorem fusionEig_succ_le_zero_above_two_cutoff {N : Nat} {w : Q'} {p s : Nat}
    (h0' : (0 : Q') < dimQ s * bondMovedCoeff N w (p + 1) 0)
    (hs : 2 * N < s) :
    fusionEig N w (p + 1) s h0' <= (0 : Q') :=
  Q'.le_of_eqv (fusionEig_succ_zero_above_two_cutoff h0' hs)

/-! ## 4. The all-mode exponential bridge is a finite obligation -/

/-- The exact finite core of `ExpShiftBridge`: only modes `s <= 2*N` are
retained. -/
structure FiniteExpShiftBridge (N : Nat) (w : Q') (p : Nat) (weff : Q')
    (h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0) : Type where
  rebasedBulkShift : forall s, s <= 2 * N ->
    fusionEig N w p s (h0' s) - rateP weff s <= q112

/-- Restriction of the historical all-mode bridge to its finite support core. -/
def finiteExpShiftBridge_of_expShiftBridge {N : Nat} {w : Q'} {p : Nat}
    {weff : Q'}
    {h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (B : ExpShiftBridge N w p weff h0') :
    FiniteExpShiftBridge N w p weff h0' where
  rebasedBulkShift := fun s _ => B.rebasedBulkShift s

/-- **Finite-support compiler for `ExpShiftBridge`.**  At a positive fusion
exponent, a finite bridge on `s <= 2*N` supplies the complete all-mode bridge.
Above `2*N`, the fusion eigenvalue vanishes by finite propagation and the
re-based rate is nonnegative. -/
def expShiftBridge_of_finite {N : Nat} {w : Q'} {p : Nat} {weff : Q'}
    {h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w (p + 1) 0}
    (hweff0 : (0 : Q') <= weff)
    (F : FiniteExpShiftBridge N w (p + 1) weff h0') :
    ExpShiftBridge N w (p + 1) weff h0' where
  rebasedBulkShift := fun s => by
    by_cases hs : s <= 2 * N
    · exact F.rebasedBulkShift s hs
    · have htail : 2 * N < s := by omega
      have heig : fusionEig N w (p + 1) s (h0' s) <= (0 : Q') :=
        fusionEig_succ_le_zero_above_two_cutoff (h0' s) htail
      have hrate : (0 : Q') <= rateP weff s := rateP_nonneg hweff0 s
      have hleRate : fusionEig N w (p + 1) s (h0' s) <= rateP weff s :=
        Q'.le_trans' _ _ _ heig hrate
      have hleAdd : fusionEig N w (p + 1) s (h0' s)
          <= rateP weff s + (0 : Q') :=
        Q'.le_trans' _ _ _ hleRate
          (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv _)))
      exact Q'.le_trans' _ _ _ (Q'.sub_le_of_le_add hleAdd)
        (by decide : (0 : Q') <= q112)

end YMGap.Continuum.RebasedExpShiftSupportReduction

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.shiftLogScale
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.log_shiftLogScale
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.DyadicLogReduction.toLegacy
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.DyadicLogReduction.legacyLog_eq_value
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.fusionInd_zero_of_sum_lt
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.fusionProduct_zero_above_two_cutoff
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.fusionPow_succ_zero_above_two_cutoff
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.bondMovedCoeff_succ_zero_above_two_cutoff
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.fusionEig_succ_zero_above_two_cutoff
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.fusionEig_succ_le_zero_above_two_cutoff
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.finiteExpShiftBridge_of_expShiftBridge
#print axioms YMGap.Continuum.RebasedExpShiftSupportReduction.expShiftBridge_of_finite
