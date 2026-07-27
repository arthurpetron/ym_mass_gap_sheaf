/-
# BF4 terminal-smoothing projective domination

The pathwise Feynman--Kac window in
`BF4GroupedFeynmanKacHarnack` pays the full oscillation of every interior
spatial potential.  That estimate is valid but need not be sharp after
conditional integration.

This module records the stronger positive-kernel fact.  Suppose a grouped
kernel has been exactly regrouped as

  G(x,z) = sum_y prefix(x,y) * terminal(y,z),

where every prefix row is nonnegative and nonzero, while `terminal` is
strictly positive with a finite cross-ratio certificate.  Then:

* every entry of `G` is strictly positive;
* the complete four-boundary cross-ratio of `G` is bounded by the
  cross-ratio of `terminal`;
* arbitrary positive interior Feynman--Kac weights may be contained in
  `prefix`, so their pointwise oscillation does not appear in the result.

The proof is finite positive-cone algebra: two prefix rows are two
nonnegative activities, and
`FiniteCrossRatioDiameterCertificate.finiteKernelAction_projectiveSpread`
controls their images simultaneously.

For the BF4 23-cycle kinetic window this returns the exact spread

  (3489 / 1055)^23

provided the *terminal conditionally integrated kinetic factor* has the
already proved floor and ceiling.  This is a genuine improvement over the
generic pathwise factor

  (3489 / 1055)^23 * potentialSpread^interiorCount.

It is not yet a spacing-uniform physical Harnack theorem.  A microscopic
short-time terminal heat kernel need not satisfy the grouped BF4 window;
the remaining Yang--Mills step is an exact conditional regrouping that
places a uniformly smoothing factor at the terminal end, or a direct
spacing-uniform certificate for that terminal factor.

## Axiom gate

Exact `Q'` finite-sum and positive-order algebra only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4GroupedFeynmanKacHarnack

namespace YMGap.Continuum.BF4TerminalSmoothingProjective

open YMGap.Constructive
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.RationalCrossRatioDiameter

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact conditional regrouping -/

/-- A grouped kernel obtained by applying one terminal kernel to every
source-indexed prefix activity.

The prefix may already contain arbitrary conditional integrations and every
interior Feynman--Kac potential. -/
def terminalSmoothedKernel
    {Source Middle Target : Type}
    (prefixWeight : Source → Middle → Q')
    (terminal : Middle → Target → Q')
    (middles : List Middle)
    (source : Source) (target : Target) : Q' :=
  FiniteCrossRatioDiameterCertificate.finiteKernelAction
    terminal middles (prefixWeight source) target

/-- Constructive data saying that every selected prefix row is a nonzero
point of the nonnegative activity cone.

The positive coordinate is retained as `Type`-level witness data rather
than hidden in a propositional existence statement. -/
structure PositivePrefixRows
    {Source Middle : Type}
    (prefixWeight : Source → Middle → Q')
    (sources : List Source) (middles : List Middle) : Type where
  /-- Every selected prefix entry is nonnegative. -/
  nonnegative :
    ∀ source, source ∈ sources →
      ∀ middle, middle ∈ middles →
        (0 : Q') ≤ prefixWeight source middle
  /-- A computable positive coordinate for each source row. -/
  positiveMiddle : Source → Middle
  /-- The chosen positive coordinate belongs to the retained middle list. -/
  positiveMiddle_mem :
    ∀ source, source ∈ sources →
      positiveMiddle source ∈ middles
  /-- The chosen coordinate has strictly positive prefix weight. -/
  positiveValue :
    ∀ source, source ∈ sources →
      (0 : Q') < prefixWeight source (positiveMiddle source)

namespace PositivePrefixRows

/-- Each selected row is a certified nonzero nonnegative activity. -/
def row
    {Source Middle : Type}
    {prefixWeight : Source → Middle → Q'}
    {sources : List Source} {middles : List Middle}
    (rows : PositivePrefixRows prefixWeight sources middles)
    (source : Source) (hsource : source ∈ sources) :
    FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
      middles (prefixWeight source) where
  nonnegative := rows.nonnegative source hsource
  positiveSource := rows.positiveMiddle source
  positiveSource_mem := rows.positiveMiddle_mem source hsource
  positiveSource_value := rows.positiveValue source hsource

end PositivePrefixRows

/-! ## The terminal factor controls the entire projective diameter -/

/-- The images of any two nonnegative prefix rows have projective spread no
larger than the terminal kernel.

No bound on the magnitude or oscillation of the prefix is used. -/
theorem terminalSmoothedKernel_projectiveSpread
    {Source Middle Target : Type}
    {prefixWeight : Source → Middle → Q'}
    {terminal : Middle → Target → Q'}
    {sources : List Source} {middles : List Middle}
    {targets : List Target}
    (terminalCertificate :
      FiniteCrossRatioDiameterCertificate
        terminal middles targets)
    (prefixRows :
      PositivePrefixRows prefixWeight sources middles)
    (first : Source) (hfirst : first ∈ sources)
    (second : Source) (hsecond : second ∈ sources) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      terminalCertificate.spread targets
      (terminalSmoothedKernel prefixWeight terminal middles first)
      (terminalSmoothedKernel prefixWeight terminal middles second) := by
  unfold terminalSmoothedKernel
  exact
    terminalCertificate.finiteKernelAction_projectiveSpread
      (prefixWeight first) (prefixWeight second)
      (prefixRows.nonnegative first hfirst)
      (prefixRows.nonnegative second hsecond)

/-- **Terminal-smoothing certificate.**  Exact conditional integration of an
arbitrary nonzero nonnegative prefix followed by one certified terminal
kernel preserves the terminal kernel's cross-ratio spread exactly.

This is the division-free finite form of positive-kernel projective
smoothing. -/
def terminalSmoothedCertificate
    {Source Middle Target : Type}
    {prefixWeight : Source → Middle → Q'}
    {terminal : Middle → Target → Q'}
    {sources : List Source} {middles : List Middle}
    {targets : List Target}
    (terminalCertificate :
      FiniteCrossRatioDiameterCertificate
        terminal middles targets)
    (prefixRows :
      PositivePrefixRows prefixWeight sources middles) :
    FiniteCrossRatioDiameterCertificate
      (terminalSmoothedKernel prefixWeight terminal middles)
      sources targets where
  spread := terminalCertificate.spread
  one_le_spread := terminalCertificate.one_le_spread
  strictlyPositive := by
    intro source hsource target htarget
    unfold terminalSmoothedKernel
    exact terminalCertificate.finiteKernelAction_pos
      (prefixRows.row source hsource) htarget
  crossRatioBound := by
    intro first hfirst second hsecond left hleft right hright
    exact terminalSmoothedKernel_projectiveSpread
      terminalCertificate prefixRows
      first hfirst second hsecond
      left hleft right hright

/-- The terminal-smoothed certificate records exactly the terminal spread;
no interior-potential factor is introduced. -/
theorem terminalSmoothedCertificate_spread
    {Source Middle Target : Type}
    {prefixWeight : Source → Middle → Q'}
    {terminal : Middle → Target → Q'}
    {sources : List Source} {middles : List Middle}
    {targets : List Target}
    (terminalCertificate :
      FiniteCrossRatioDiameterCertificate
        terminal middles targets)
    (prefixRows :
      PositivePrefixRows prefixWeight sources middles) :
    (terminalSmoothedCertificate
      terminalCertificate prefixRows).spread =
        terminalCertificate.spread :=
  rfl

/-- The rational Birkhoff candidate rate is likewise unchanged by the
arbitrary nonnegative prefix. -/
theorem terminalSmoothedCertificate_candidateRate_eqv
    {Source Middle Target : Type}
    {prefixWeight : Source → Middle → Q'}
    {terminal : Middle → Target → Q'}
    {sources : List Source} {middles : List Middle}
    {targets : List Target}
    (terminalCertificate :
      FiniteCrossRatioDiameterCertificate
        terminal middles targets)
    (prefixRows :
      PositivePrefixRows prefixWeight sources middles) :
    (terminalSmoothedCertificate
      terminalCertificate prefixRows).candidateRate ≈
        terminalCertificate.candidateRate :=
  Q'.eqv_refl _

/-! ## Exact BF4 23-cycle specialization -/

/-- Package the proved BF4 23-cycle floor/ceiling as a cross-ratio
certificate for a terminal conditionally integrated kinetic kernel. -/
def bf4TerminalKineticCertificate
    {Middle Target : Type}
    (terminal : Middle → Target → Q')
    (middles : List Middle) (targets : List Target)
    (lower_bound :
      ∀ middle, middle ∈ middles →
        ∀ target, target ∈ targets →
          bf4KineticFloor ≤ terminal middle target)
    (upper_bound :
      ∀ middle, middle ∈ middles →
        ∀ target, target ∈ targets →
          terminal middle target ≤ bf4KineticCeiling) :
    FiniteCrossRatioDiameterCertificate
      terminal middles targets :=
  crossRatioCertificateOfWindow
    terminal middles targets
    bf4KineticFloor bf4KineticCeiling bf4KineticSpread
    bf4KineticFloor_pos
    bf4KineticCeiling_nonnegative
    bf4KineticSpread_one_le
    lower_bound upper_bound
    bf4KineticCeiling_le_spread_floor

/-- **BF4 terminal-smoothing Harnack certificate.**  Once the exact
conditionally integrated grouped kernel is split into a nonzero
nonnegative prefix and a terminal kinetic factor satisfying the established
23-cycle window, every interior spatial weight is absorbed into the prefix
and the full kernel has spread `(3489/1055)^23`.

The input is deliberately the terminal-factor floor/ceiling, not a bound on
the full Feynman--Kac potential. -/
def bf4TerminalSmoothedCertificate
    {Source Middle Target : Type}
    (prefixWeight : Source → Middle → Q')
    (terminal : Middle → Target → Q')
    (sources : List Source) (middles : List Middle)
    (targets : List Target)
    (prefixRows :
      PositivePrefixRows prefixWeight sources middles)
    (lower_bound :
      ∀ middle, middle ∈ middles →
        ∀ target, target ∈ targets →
          bf4KineticFloor ≤ terminal middle target)
    (upper_bound :
      ∀ middle, middle ∈ middles →
        ∀ target, target ∈ targets →
          terminal middle target ≤ bf4KineticCeiling) :
    FiniteCrossRatioDiameterCertificate
      (terminalSmoothedKernel prefixWeight terminal middles)
      sources targets :=
  terminalSmoothedCertificate
    (bf4TerminalKineticCertificate
      terminal middles targets lower_bound upper_bound)
    prefixRows

/-- The BF4 terminal-smoothed spread is independent of the prefix and hence
of every interior potential already integrated into it. -/
theorem bf4TerminalSmoothedCertificate_spread
    {Source Middle Target : Type}
    (prefixWeight : Source → Middle → Q')
    (terminal : Middle → Target → Q')
    (sources : List Source) (middles : List Middle)
    (targets : List Target)
    (prefixRows :
      PositivePrefixRows prefixWeight sources middles)
    (lower_bound :
      ∀ middle, middle ∈ middles →
        ∀ target, target ∈ targets →
          bf4KineticFloor ≤ terminal middle target)
    (upper_bound :
      ∀ middle, middle ∈ middles →
        ∀ target, target ∈ targets →
          terminal middle target ≤ bf4KineticCeiling) :
    (bf4TerminalSmoothedCertificate
      prefixWeight terminal sources middles targets
      prefixRows lower_bound upper_bound).spread =
        bf4KineticSpread :=
  rfl

/-! ## One spacing-uniform family -/

/-- A regulator family of exact conditional regroupings inherits one common
BF4 spread whenever every terminal factor obeys the same established
23-cycle kinetic window.

The prefix, its carrier, and its positive witness may all depend on the
regulator.  Thus localization and arbitrary spacing-dependence before the
last smoothing factor are allowed. -/
def bf4UniformTerminalSmoothedCertificate
    {Index : Type}
    {Source Middle Target : Index → Type}
    (prefixWeight :
      ∀ index, Source index → Middle index → Q')
    (terminal :
      ∀ index, Middle index → Target index → Q')
    (sources : ∀ index, List (Source index))
    (middles : ∀ index, List (Middle index))
    (targets : ∀ index, List (Target index))
    (prefixRows :
      ∀ index,
        PositivePrefixRows
          (prefixWeight index) (sources index) (middles index))
    (lower_bound :
      ∀ index middle, middle ∈ middles index →
        ∀ target, target ∈ targets index →
          bf4KineticFloor ≤ terminal index middle target)
    (upper_bound :
      ∀ index middle, middle ∈ middles index →
        ∀ target, target ∈ targets index →
          terminal index middle target ≤ bf4KineticCeiling) :
    UniformCrossRatioDiameterCertificate
      Index Source Target
      (fun index =>
        terminalSmoothedKernel
          (prefixWeight index) (terminal index) (middles index))
      sources targets where
  spread := bf4KineticSpread
  one_le_spread := bf4KineticSpread_one_le
  strictlyPositive := by
    intro index source hsource target htarget
    exact
      (bf4TerminalSmoothedCertificate
        (prefixWeight index) (terminal index)
        (sources index) (middles index) (targets index)
        (prefixRows index)
        (lower_bound index) (upper_bound index)).strictlyPositive
          source hsource target htarget
  crossRatioBound := by
    intro index first hfirst second hsecond left hleft right hright
    exact
      (bf4TerminalSmoothedCertificate
        (prefixWeight index) (terminal index)
        (sources index) (middles index) (targets index)
        (prefixRows index)
        (lower_bound index) (upper_bound index)).crossRatioBound
          first hfirst second hsecond left hleft right hright

end YMGap.Continuum.BF4TerminalSmoothingProjective

#print axioms YMGap.Continuum.BF4TerminalSmoothingProjective.PositivePrefixRows.row
#print axioms YMGap.Continuum.BF4TerminalSmoothingProjective.terminalSmoothedKernel_projectiveSpread
#print axioms YMGap.Continuum.BF4TerminalSmoothingProjective.terminalSmoothedCertificate
#print axioms YMGap.Continuum.BF4TerminalSmoothingProjective.terminalSmoothedCertificate_spread
#print axioms YMGap.Continuum.BF4TerminalSmoothingProjective.terminalSmoothedCertificate_candidateRate_eqv
#print axioms YMGap.Continuum.BF4TerminalSmoothingProjective.bf4TerminalKineticCertificate
#print axioms YMGap.Continuum.BF4TerminalSmoothingProjective.bf4TerminalSmoothedCertificate
#print axioms YMGap.Continuum.BF4TerminalSmoothingProjective.bf4TerminalSmoothedCertificate_spread
#print axioms YMGap.Continuum.BF4TerminalSmoothingProjective.bf4UniformTerminalSmoothedCertificate
