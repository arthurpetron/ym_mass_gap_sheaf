/-
`FusionWeightedInterlacingCertificate` -- scalable reflected certificates for
the finite heat-weighted even/odd exchange.

# 1. A faster checker

`FusionWeightedBoxInterlacing.finiteInterlacingCheck` is intentionally the
most literal checker: it evaluates the four-fold Cauchy--Binet sum `quadDiff`
at every mode.  That is an excellent specification, but a poor evaluator.
There are `2*N-1` modes and `quadDiff` contains `(N+1)^4` summands, so direct
reflection exposes order `N^5` rational summands to the kernel.

The checker below uses the proved representation theorem
`boxDiff_eq_quadDiff` as a verified compiler optimization.  It decides the
equivalent box inequality

    boxSum(s) * boxSum(s+2) <= boxSum(s+1)^2

directly.  Each `boxSum` is only a double finite sum, reducing the reflected
scan to order `N^3` rational summands.  Soundness then transports the result
to the original `quadDiff` specification.  A block checker and split theorem
permit large certificates to be checked in independently bounded pieces,
following the repository's crash-safe certificate-decomposition policy.

# 2. The symbolic interval route

The box difference is a finite signed monomial polynomial in `w`.  Every
monomial exponent is even: admissibility fixes the parity of `a+b` to the
channel parity, and a product of two equal-parity channel sums has even total
Casimir exponent.  Hence the physical coordinate

    u = 4*w^2

from `CoreBBernsteinConsumer` carries the whole interval `0 <= w <= 1/2` to
`0 <= u <= 1` and halves the polynomial degree.  The final section gives a
reflected Bernstein-row consumer pinned to the ACTUAL box difference.  A
successful finite coefficient scan plus exact reconstruction proves every
coupling in the physical interval, not merely sampled rationals.

Exact external generation has found coefficientwise-nonnegative full-degree
`u`-Bernstein rows for every finite-triangle mode through `N = 12`.  That is
evidence for the compiler invariant, not a theorem asserted here.  The
remaining next-stage task is to connect the existing finite signed-monomial
compiler (`finiteSignedMonomialBernsteinRow_eval`) to the reconstruction field
below and reflect the generated rows.

# Honest scope

The direct checker closes new fixed rational cutoffs; it does not by itself
prove the all-`N`, all-coupling theorem.  The Bernstein family is a genuine
certificate interface with a reconstruction equation pinned to `boxSum`, not
an inhabitant of the open uniform theorem.  No continuum frontier bundle is
inhabited here.

# Constructive contract

Mathlib-free; pure `Q'`/`Nat`/`Int`.  No `Classical`, `native_decide`, `sorry`,
new axiom, or noncomputable definition.  All finite decisions are Lean-kernel
decisions, and every load-bearing declaration is axiom-gated below.
-/

import YMGap.Continuum.FusionWeightedBoxInterlacing
import YMGap.Continuum.CoreBBernsteinConsumer

namespace YMGap.Continuum.FusionWeightedInterlacingCertificate

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionWeightedBoxInterlacing
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.CoreBBernsteinConsumer

/-! ## 1. Direct box specification and the order-`N^3` reflected checker -/

/-- The direct, double-sum form of one finite heat-weighted even/odd exchange.
This is propositionally equivalent to nonnegativity of `quadDiff`, but is much
cheaper to evaluate because it does not expand the product into a quadruple
sum. -/
def boxInterlacingAt (w : Q') (N s : Nat) : Prop :=
  boxSum w N s * boxSum w N (s + 2)
    ≤ boxSum w N (s + 1) * boxSum w N (s + 1)

/-- The direct box specification is decidable by the constructive rational
order.  Naming the instance makes the verified optimized checker reducible
without asking typeclass search to unfold `boxInterlacingAt` heuristically. -/
instance boxInterlacingAtDecidable (w : Q') (N s : Nat) :
    Decidable (boxInterlacingAt w N s) := by
  unfold boxInterlacingAt
  infer_instance

/-- One direct box inequality implies nonnegativity of the literal
Cauchy--Binet specification. -/
theorem quadDiff_nonneg_of_boxInterlacingAt {w : Q'} {N s : Nat}
    (hbox : boxInterlacingAt w N s) :
    (0 : Q') ≤ quadDiff w N s := by
  have hdiff : (0 : Q') ≤
      boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2)) :=
    Q'.sub_nonneg_of_le hbox
  exact Q'.le_trans' _ _ _ hdiff
    (Q'.le_of_eqv (boxDiff_eq_quadDiff w N s))

/-- Conversely, nonnegativity of the literal Cauchy--Binet specification
implies the direct box inequality. -/
theorem boxInterlacingAt_of_quadDiff_nonneg {w : Q'} {N s : Nat}
    (hquad : (0 : Q') ≤ quadDiff w N s) :
    boxInterlacingAt w N s := by
  have hdiff : (0 : Q') ≤
      boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2)) :=
    Q'.le_trans' _ _ _ hquad
      (Q'.ge_of_eqv (boxDiff_eq_quadDiff w N s))
  exact Q'.le_of_sub_nonneg hdiff

/-- The optimized checker for the complete finite triangle.  It scans exactly
the same `2*N-1` modes as `finiteInterlacingCheck`, but evaluates three double
sums per mode instead of one quadruple sum. -/
def fastFiniteInterlacingCheck (w : Q') (N : Nat) : Bool :=
  (List.range (2 * N - 1)).all
    (fun s => decide (boxInterlacingAt w N s))

/-- Soundness of the optimized checker with respect to the original
`quadDiff` finite-triangle specification. -/
theorem fastFiniteInterlacingCheck_sound (w : Q') (N : Nat)
    (hcheck : fastFiniteInterlacingCheck w N = true) :
    ∀ s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s := by
  intro s hs
  have hmem : s ∈ List.range (2 * N - 1) :=
    List.mem_range.mpr (by omega)
  have hbox : boxInterlacingAt w N s :=
    of_decide_eq_true (List.all_eq_true.mp hcheck s hmem)
  exact quadDiff_nonneg_of_boxInterlacingAt hbox

/-- Completeness of the optimized checker relative to the original literal
finite-triangle specification.  Together with soundness this proves that the
order-`N^3` evaluator is a verified implementation of the order-`N^5`
specification. -/
theorem fastFiniteInterlacingCheck_complete (w : Q') (N : Nat)
    (hfinite : ∀ s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s) :
    fastFiniteInterlacingCheck w N = true := by
  apply List.all_eq_true.mpr
  intro s hmem
  apply decide_eq_true
  exact boxInterlacingAt_of_quadDiff_nonneg
    (hfinite s (by
      have hs := List.mem_range.mp hmem
      omega))

/-- The optimized and literal finite checkers accept exactly the same fixed
cutoffs and weights. -/
theorem fastFiniteInterlacingCheck_iff_finiteInterlacingCheck (w : Q') (N : Nat) :
    fastFiniteInterlacingCheck w N = true ↔
      finiteInterlacingCheck w N = true := by
  constructor
  · intro h
    exact finiteInterlacingCheck_complete w N
      (fastFiniteInterlacingCheck_sound w N h)
  · intro h
    exact fastFiniteInterlacingCheck_complete w N
      (finiteInterlacingCheck_sound w N h)

/-- A successful optimized scan builds the genuine fixed-cutoff
`FusionConvLogConcaveCore`. -/
def fusionConvLogConcaveCore_of_fast_check {N : Nat} {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q'))
    (hcheck : fastFiniteInterlacingCheck w N = true) :
    FusionConvLogConcaveCore N w hw0 hw1 :=
  fusionConvLogConcaveCore_of_finite_interlacing hw0 hw1 hstrong
    (fastFiniteInterlacingCheck_sound w N hcheck)

/-! ## 2. Bounded certificate blocks -/

/-- Check `length` consecutive direct box inequalities beginning at `start`.
This supports bounded kernel certificates without changing the mathematical
decision procedure. -/
def fastInterlacingBlockCheck
    (w : Q') (N start length : Nat) : Bool :=
  (List.range length).all
    (fun i => decide (boxInterlacingAt w N (start + i)))

/-- Soundness of one bounded checker block. -/
theorem fastInterlacingBlockCheck_sound (w : Q') (N start length : Nat)
    (hcheck : fastInterlacingBlockCheck w N start length = true)
    (s : Nat) (hlo : start ≤ s) (hhi : s < start + length) :
    boxInterlacingAt w N s := by
  have hi : s - start < length := by omega
  have hmem : s - start ∈ List.range length :=
    List.mem_range.mpr hi
  have h := of_decide_eq_true
    (List.all_eq_true.mp hcheck (s - start) hmem)
  have heq : start + (s - start) = s := by omega
  simpa only [heq] using h

/-- Two bounded blocks covering `[0,2*N-1)` assemble into the full optimized
checker.  The split point may be chosen to keep each individual kernel
certificate below the repository's memory ceiling. -/
theorem fastFiniteInterlacingCheck_of_split (w : Q') (N cut : Nat)
    (hcut : cut ≤ 2 * N - 1)
    (hleft : fastInterlacingBlockCheck w N 0 cut = true)
    (hright : fastInterlacingBlockCheck w N cut (2 * N - 1 - cut) = true) :
    fastFiniteInterlacingCheck w N = true := by
  apply List.all_eq_true.mpr
  intro s hmem
  apply decide_eq_true
  have hs : s < 2 * N - 1 := List.mem_range.mp hmem
  by_cases hsc : s < cut
  · exact fastInterlacingBlockCheck_sound w N 0 cut hleft s
      (by omega) (by omega)
  · exact fastInterlacingBlockCheck_sound w N cut
      (2 * N - 1 - cut) hright s (by omega) (by omega)

/-! ## 3. First new exact cutoff beyond the previous `N ≤ 6` wall -/

/-- Lower block of the exact `N=7`, `w=1/2` certificate. -/
theorem fastInterlacingBlockCheck_N7_half_lower :
    fastInterlacingBlockCheck wH 7 0 7 = true := by decide

/-- Upper block of the exact `N=7`, `w=1/2` certificate. -/
theorem fastInterlacingBlockCheck_N7_half_upper :
    fastInterlacingBlockCheck wH 7 7 6 = true := by decide

/-- The optimized reflected certificate closes the complete finite triangle
at the first cutoff beyond the previously compiled `N ≤ 6` family. -/
theorem fastFiniteInterlacingCheck_N7_half :
    fastFiniteInterlacingCheck wH 7 = true :=
  fastFiniteInterlacingCheck_of_split wH 7 7 (by decide)
    fastInterlacingBlockCheck_N7_half_lower
    fastInterlacingBlockCheck_N7_half_upper

/-- The new `N=7`, `w=1/2` finite certificate inhabits the genuine box
log-concavity core. -/
def fusionConvLogConcaveCore_N7_half_fast :
    FusionConvLogConcaveCore 7 wH (by decide) (by decide) :=
  fusionConvLogConcaveCore_of_fast_check (by decide) (by decide) (by decide)
    fastFiniteInterlacingCheck_N7_half

/-! ## 4. Reflected symbolic Bernstein interval certificates -/

/-- Kernel checker for coefficientwise nonnegativity of one finite signed
Bernstein row. -/
def bernsteinRowNonnegativeCheck
    (degree : Nat) (coefficient : Nat → Int) : Bool :=
  (List.range (degree + 1)).all
    (fun j => decide ((0 : Int) ≤ coefficient j))

/-- Soundness of the coefficient-row checker. -/
theorem bernsteinRowNonnegativeCheck_sound
    (degree : Nat) (coefficient : Nat → Int)
    (hcheck : bernsteinRowNonnegativeCheck degree coefficient = true) :
    ∀ j, j ≤ degree → (0 : Int) ≤ coefficient j := by
  intro j hj
  apply of_decide_eq_true
  exact List.all_eq_true.mp hcheck j
    (List.mem_range.mpr (by omega))

/-- A denominator-cleared Bernstein certificate for every mode of one fixed
cutoff.  The reconstruction field is pinned to the actual box difference;
therefore a detached positive polynomial cannot inhabit this interface.

The row checker is data rather than a propositional coefficient family: once
the reconstruction compiler supplies the row, positivity is verified by
finite kernel computation. -/
structure FiniteTriangleBernsteinCertificate (N : Nat) : Type where
  degree : Nat → Nat
  zeroOrder : Nat → Nat
  coefficient : Nat → Nat → Int
  scale : Nat → Q'
  scale_positive : ∀ s, s + 2 ≤ 2 * N → (0 : Q') < scale s
  coefficient_check : ∀ s, s + 2 ≤ 2 * N →
    bernsteinRowNonnegativeCheck (degree s) (coefficient s) = true
  boxDiff_scaled_reconstruction : ∀ (w : Q') s, s + 2 ≤ 2 * N →
    (scale s *
      (boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2)))).eqv
      (physicalSquareCoordinate w ^ zeroOrder s *
        signedBernsteinEval (degree s) (coefficient s)
          (physicalSquareCoordinate w))

/-- A reflected Bernstein family proves the complete heat-weighted even/odd
exchange at its fixed cutoff for EVERY coupling in `0 ≤ w ≤ 1/2`.
This is the computer-science route around repeated heavy rational evaluation:
exact reconstruction is checked once, while positivity reduces to a finite
scan of integer coefficients. -/
theorem finite_interlacing_of_bernstein_certificate
    {N : Nat} (C : FiniteTriangleBernsteinCertificate N)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    ∀ s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s := by
  intro s hs
  have hu0 : (0 : Q') ≤ physicalSquareCoordinate w :=
    physicalSquareCoordinate_nonnegative hw0
  have hu1 : physicalSquareCoordinate w ≤ (1 : Q') :=
    physicalSquareCoordinate_le_one hw0 hwH
  have hcoeff : ∀ j, j ≤ C.degree s →
      (0 : Int) ≤ C.coefficient s j :=
    bernsteinRowNonnegativeCheck_sound _ _ (C.coefficient_check s hs)
  have hrow : (0 : Q') ≤
      signedBernsteinEval (C.degree s) (C.coefficient s)
        (physicalSquareCoordinate w) :=
    signedBernsteinEval_nonnegative _ _ hu0 hu1 hcoeff
  have hrhs : (0 : Q') ≤
      physicalSquareCoordinate w ^ C.zeroOrder s *
        signedBernsteinEval (C.degree s) (C.coefficient s)
          (physicalSquareCoordinate w) :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg _ hu0 (C.zeroOrder s)) hrow
  have hscaled : (0 : Q') ≤ C.scale s *
      (boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2))) :=
    Q'.le_trans' _ _ _ hrhs
      (Q'.ge_of_eqv (C.boxDiff_scaled_reconstruction w s hs))
  have hdiff : (0 : Q') ≤
      boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2)) :=
    Q'.nonneg_of_mul_pos (C.scale_positive s hs) hscaled
  exact Q'.le_trans' _ _ _ hdiff
    (Q'.le_of_eqv (boxDiff_eq_quadDiff w N s))

/-- A reflected Bernstein family therefore builds the genuine fixed-cutoff
box core uniformly across the whole physical coupling interval. -/
def fusionConvLogConcaveCore_of_bernstein_certificate
    {N : Nat} (C : FiniteTriangleBernsteinCertificate N)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH)
    (hw1 : w ≤ (1 : Q'))
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q')) :
    FusionConvLogConcaveCore N w hw0 hw1 :=
  fusionConvLogConcaveCore_of_finite_interlacing hw0 hw1 hstrong
    (finite_interlacing_of_bernstein_certificate C hw0 hwH)

/-- A Bernstein certificate at every cutoff discharges the complete finite
triangle family and therefore inhabits the existing all-cutoff
`UniformBoxLogConcave` residual.  The quantifier over certificates is the
remaining constructive generation problem; this definition is its exact
end-to-end consumer. -/
def uniformBoxLogConcave_of_bernstein_certificates
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH)
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q'))
    (certificates : ∀ N, FiniteTriangleBernsteinCertificate N) :
    UniformBoxLogConcave w :=
  uniformBoxLogConcave_of_finite_interlacing hw0 hstrong
    (fun N => finite_interlacing_of_bernstein_certificate
      (certificates N) hw0 hwH)

/-! ## 5. PROVED vs. next certificate generation step

PROVED (axiom-clean):

* `fastFiniteInterlacingCheck` is a verified order-`N^3` implementation of
  the original order-`N^5` `quadDiff` checker;
* soundness, completeness, and equivalence with `finiteInterlacingCheck`;
* bounded block checking and two-block assembly;
* the complete `N=7`, `w=1/2` finite triangle and its genuine
  `FusionConvLogConcaveCore`;
* a reflected Bernstein-row checker and a consumer proving the complete
  fixed-`N` triangle for every `0 ≤ w ≤ 1/2` from rows exactly reconstructed
  against the actual box difference;
* `uniformBoxLogConcave_of_bernstein_certificates`: the exact all-cutoff
  certificate-family consumer landing in `UniformBoxLogConcave`.

NEXT (explicit certificate data, not assumed here):

* compile each box difference into its finite signed monomial list;
* use `finiteSignedMonomialBernsteinRow_eval` at the even-exponent coordinate
  `u=4*w^2` to discharge `boxDiff_scaled_reconstruction`;
* kernel-check the generated integer rows.  Exact external generation through
  `N=12` reports every full-degree row coefficient nonnegative, but those rows
  become theorems only when imported and checked by this interface.

This advances one finite weighted-interlacing wall; it is not a proof of the
Yang--Mills mass gap.
-/

end YMGap.Continuum.FusionWeightedInterlacingCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.quadDiff_nonneg_of_boxInterlacingAt
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.boxInterlacingAt_of_quadDiff_nonneg
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fastFiniteInterlacingCheck_sound
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fastFiniteInterlacingCheck_complete
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fastFiniteInterlacingCheck_iff_finiteInterlacingCheck
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fusionConvLogConcaveCore_of_fast_check
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fastInterlacingBlockCheck_sound
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fastFiniteInterlacingCheck_of_split
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fastInterlacingBlockCheck_N7_half_lower
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fastInterlacingBlockCheck_N7_half_upper
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fastFiniteInterlacingCheck_N7_half
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fusionConvLogConcaveCore_N7_half_fast
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.bernsteinRowNonnegativeCheck_sound
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.FiniteTriangleBernsteinCertificate
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.finite_interlacing_of_bernstein_certificate
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.fusionConvLogConcaveCore_of_bernstein_certificate
#print axioms YMGap.Continuum.FusionWeightedInterlacingCertificate.uniformBoxLogConcave_of_bernstein_certificates
