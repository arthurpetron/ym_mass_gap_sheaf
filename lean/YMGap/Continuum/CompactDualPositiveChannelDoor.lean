/-
# A finite positive-channel door for compact-dual CD-2

The exact-rational survival probe supplied on 2026-07-23 reports the
`(1,1,1,1)` rim activity

    1/4 + (9/2) s^16 + 6 s^24 + (21/4) s^32

together with a twelve-sector, termwise-positive page-spin ledger.  The
sectors form four exact permutation orbits whose exponent-compressed sum is
the displayed polynomial.  This module records that orbit ledger in the
kernel:

* representatives, multiplicities, exponents, and per-sector coefficients
  for all four orbits (total multiplicity twelve);
* nonnegativity of every orbit's per-sector monomial and total contribution;
* exact resummation to the displayed activity;
* the pinned specialization `s = D.coupling`;
* the generic square-factor consumer that a future physical rim-channel
  identification may use.

This is a candidate door, not CD-2.  The executable exact-Haar probe exists,
but no Lean theorem identifies its output with a physical Haar-network
integral or with a summand of `CompactDualPhysicalData.physicalTerm`.
The orbit-count data below faithfully distinguishes the twelve page-spin
sectors from their four exponent-compressed monomials.  The rational
coefficients are proved internally once defined; they are not imported as
trusted measurements.

The final section states the strictly larger all-label, source-dependent
kernel obligation over the actual fine and coarse physical labelling lists.
It has no inhabitant here.  No block pushforward, channel completeness,
remainder, cone-preservation, or norm claim is made.

## Axiom gate

Pure finite `Q'` arithmetic and structural sums.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or `noncomputable` declaration is used.
-/

import YMGap.Continuum.CompactDualBoundaryReflectionCone
import YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.CompactDualPositiveChannelDoor

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.CompactDualPinnedPhysicalData
open YMGap.Continuum.CompactDualPinnedPhysicalData.CompactDualPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity

local infix:50 " ≈ " => Q'.eqv

/-! ## The exact twelve-sector orbit ledger -/

def rimQuarter : Q' := Q'.mkPos 1 4 (by decide)
def rimThreeQuarters : Q' := Q'.mkPos 3 4 (by decide)
def rimThreeHalves : Q' := Q'.mkPos 3 2 (by decide)
def rimNineHalves : Q' := Q'.mkPos 9 2 (by decide)
def rimSix : Q' := Q'.ofNat 6
def rimTwentyOneQuarters : Q' := Q'.mkPos 21 4 (by decide)

/-- The four permutation orbits in the exact page-spin ledger. -/
inductive RimSectorOrbit : Type where
  | vacuum
  | pair
  | triple
  | full
  deriving DecidableEq

abbrev RimPageSpins := Nat × Nat × Nat × Nat

/-- All twelve nonzero page-spin sectors reported for rim `(1,1,1,1)`,
each tagged by its permutation orbit. -/
def rimPageSpinSectorLedger : List (RimPageSpins × RimSectorOrbit) :=
  [((0, 0, 0, 0), .vacuum),
    ((0, 0, 2, 2), .pair),
    ((0, 2, 0, 2), .pair),
    ((0, 2, 2, 0), .pair),
    ((2, 0, 0, 2), .pair),
    ((2, 0, 2, 0), .pair),
    ((2, 2, 0, 0), .pair),
    ((0, 2, 2, 2), .triple),
    ((2, 0, 2, 2), .triple),
    ((2, 2, 0, 2), .triple),
    ((2, 2, 2, 0), .triple),
    ((2, 2, 2, 2), .full)]

/-- The exact sector ledger has twelve entries. -/
theorem rimPageSpinSectorLedger_length :
    rimPageSpinSectorLedger.length = 12 := by
  decide

/-- The exact sector ledger has orbit multiplicities `1,6,4,1`. -/
theorem rimPageSpinSectorLedger_orbitCounts :
    (rimPageSpinSectorLedger.map Prod.snd).count .vacuum = 1 ∧
    (rimPageSpinSectorLedger.map Prod.snd).count .pair = 6 ∧
    (rimPageSpinSectorLedger.map Prod.snd).count .triple = 4 ∧
    (rimPageSpinSectorLedger.map Prod.snd).count .full = 1 := by
  decide

/-- One page-spin representative of each orbit. -/
def rimSectorOrbitRepresentative :
    RimSectorOrbit → RimPageSpins
  | .vacuum => (0, 0, 0, 0)
  | .pair => (0, 0, 2, 2)
  | .triple => (0, 2, 2, 2)
  | .full => (2, 2, 2, 2)

/-- Orbit sizes: `1 + 6 + 4 + 1 = 12` exact page-spin sectors. -/
def rimSectorOrbitMultiplicity : RimSectorOrbit → Nat
  | .vacuum => 1
  | .pair => 6
  | .triple => 4
  | .full => 1

/-- The common heat-kernel exponent on each orbit. -/
def rimSectorOrbitExponent : RimSectorOrbit → Nat
  | .vacuum => 0
  | .pair => 16
  | .triple => 24
  | .full => 32

/-- The exact coefficient of each individual page-spin sector in an orbit. -/
def rimSectorCoefficient : RimSectorOrbit → Q'
  | .vacuum => rimQuarter
  | .pair => rimThreeQuarters
  | .triple => rimThreeHalves
  | .full => rimTwentyOneQuarters

/-- One individual sector monomial in an orbit. -/
def rimSectorMonomial (s : Q') (orbit : RimSectorOrbit) : Q' :=
  rimSectorCoefficient orbit * qpow s (rimSectorOrbitExponent orbit)

/-- The complete contribution of one orbit, including its exact number of
page-spin sectors. -/
def rimSectorOrbitContribution (s : Q') : RimSectorOrbit → Q'
  | .vacuum => Q'.ofNat 1 * rimSectorMonomial s .vacuum
  | .pair => Q'.ofNat 6 * rimSectorMonomial s .pair
  | .triple => Q'.ofNat 4 * rimSectorMonomial s .triple
  | .full => Q'.ofNat 1 * rimSectorMonomial s .full

/-- The exact orbit-count form of the complete twelve-sector ledger. -/
def rimSectorOrbitActivity (s : Q') : Q' :=
  ((rimSectorOrbitContribution s .vacuum +
      rimSectorOrbitContribution s .pair) +
      rimSectorOrbitContribution s .triple) +
    rimSectorOrbitContribution s .full

/-- The displayed exact rim activity polynomial. -/
def rimChannelActivityPolynomial (s : Q') : Q' :=
  ((rimQuarter + rimNineHalves * qpow s 16) +
      rimSix * qpow s 24) +
    rimTwentyOneQuarters * qpow s 32

/-- The orbit counts cover exactly twelve page-spin sectors. -/
theorem rimSectorOrbit_totalMultiplicity :
    rimSectorOrbitMultiplicity .vacuum +
        rimSectorOrbitMultiplicity .pair +
        rimSectorOrbitMultiplicity .triple +
        rimSectorOrbitMultiplicity .full = 12 := by
  decide

/-- Every individual page-spin sector monomial is nonnegative at
nonnegative coupling. -/
theorem rimSectorMonomial_nonnegative
    {s : Q'} (hs : (0 : Q') ≤ s) (orbit : RimSectorOrbit) :
    (0 : Q') ≤ rimSectorMonomial s orbit := by
  cases orbit <;>
    exact Q'.mul_nonneg _ _ (by decide) (qpow_nonneg s hs _)

/-- Every full orbit contribution is nonnegative. -/
theorem rimSectorOrbitContribution_nonnegative
    {s : Q'} (hs : (0 : Q') ≤ s) (orbit : RimSectorOrbit) :
    (0 : Q') ≤ rimSectorOrbitContribution s orbit := by
  cases orbit <;>
    exact Q'.mul_nonneg _ _ (by decide)
      (rimSectorMonomial_nonnegative hs _)

private theorem rimPairOrbit_compresses (s : Q') :
    rimSectorOrbitContribution s .pair ≈
      rimNineHalves * qpow s 16 := by
  change
    Q'.ofNat 6 * (rimThreeQuarters * qpow s 16) ≈
      rimNineHalves * qpow s 16
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat 6) rimThreeQuarters (qpow s 16))) ?_
  exact Q'.mul_eqv_congr_right _ _ (qpow s 16) (by decide)

private theorem rimTripleOrbit_compresses (s : Q') :
    rimSectorOrbitContribution s .triple ≈
      rimSix * qpow s 24 := by
  change
    Q'.ofNat 4 * (rimThreeHalves * qpow s 24) ≈
      rimSix * qpow s 24
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat 4) rimThreeHalves (qpow s 24))) ?_
  exact Q'.mul_eqv_congr_right _ _ (qpow s 24) (by decide)

private theorem rimVacuumOrbit_compresses (s : Q') :
    rimSectorOrbitContribution s .vacuum ≈ rimQuarter := by
  change (1 : Q') * (rimQuarter * 1) ≈ rimQuarter
  exact Q'.eqv_trans _ _ _
    (Q'.one_mul_eqv (rimQuarter * 1))
    (Q'.mul_one_eqv rimQuarter)

private theorem rimFullOrbit_compresses (s : Q') :
    rimSectorOrbitContribution s .full ≈
      rimTwentyOneQuarters * qpow s 32 := by
  change
    (1 : Q') * (rimTwentyOneQuarters * qpow s 32) ≈
      rimTwentyOneQuarters * qpow s 32
  exact Q'.one_mul_eqv _

/-- The complete twelve-sector orbit ledger compresses and resums exactly to
the displayed four-monomial channel activity. -/
theorem rimSectorOrbitActivity_resums (s : Q') :
    rimSectorOrbitActivity s ≈ rimChannelActivityPolynomial s := by
  unfold rimSectorOrbitActivity rimChannelActivityPolynomial
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (rimVacuumOrbit_compresses s)
        (rimPairOrbit_compresses s))
      (rimTripleOrbit_compresses s))
    (rimFullOrbit_compresses s)

/-- The complete twelve-sector orbit ledger is nonnegative. -/
theorem rimSectorOrbitActivity_nonnegative
    {s : Q'} (hs : (0 : Q') ≤ s) :
    (0 : Q') ≤ rimSectorOrbitActivity s :=
  Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (rimSectorOrbitContribution_nonnegative hs .vacuum)
        (rimSectorOrbitContribution_nonnegative hs .pair))
      (rimSectorOrbitContribution_nonnegative hs .triple))
    (rimSectorOrbitContribution_nonnegative hs .full)

/-- The displayed polynomial itself is nonnegative, by exact resummation of
the positive ledger. -/
theorem rimChannelActivityPolynomial_nonnegative
    {s : Q'} (hs : (0 : Q') ≤ s) :
    (0 : Q') ≤ rimChannelActivityPolynomial s :=
  Q'.le_trans' _ _ _
    (rimSectorOrbitActivity_nonnegative hs)
    (Q'.le_of_eqv (rimSectorOrbitActivity_resums s))

/-! ## Pin the finite candidate to the already shared compact-dual coupling -/

/-- The finite scalar candidate evaluated at the exact rational coupling
already carried by `CompactDualPhysicalData`.  No claim identifies it with a
physical graph integral. -/
def pinnedRimChannelCandidate (D : CompactDualPhysicalData) : Q' :=
  rimChannelActivityPolynomial D.coupling

/-- The pinned finite candidate is nonnegative. -/
theorem pinnedRimChannelCandidate_nonnegative
    (D : CompactDualPhysicalData) :
    (0 : Q') ≤ pinnedRimChannelCandidate D :=
  rimChannelActivityPolynomial_nonnegative D.coupling_nonnegative

/-! ## The exact algebraic consumer for a future physical square identity -/

/-- If a future semantic bridge identifies a physical rim contribution with
the pinned activity times a square, its nonnegativity follows.  The equality
is an explicit argument: this theorem does not manufacture the identification
from the regression values. -/
theorem contribution_nonnegative_of_rim_activity_square
    (D : CompactDualPhysicalData) (contribution amplitude : Q')
    (hfactor :
      contribution ≈
        pinnedRimChannelCandidate D * (amplitude * amplitude)) :
    (0 : Q') ≤ contribution := by
  have hsquare : (0 : Q') ≤ amplitude * amplitude :=
    YMGap.Constructive.SumOfSquares.q_mul_self_nonneg amplitude
  have hproduct :
      (0 : Q') ≤
        pinnedRimChannelCandidate D * (amplitude * amplitude) :=
    Q'.mul_nonneg _ _
      (pinnedRimChannelCandidate_nonnegative D) hsquare
  exact Q'.le_trans' _ _ _ hproduct
    (Q'.le_of_eqv (Q'.eqv_symm hfactor))

/-! ## The still-open all-label source-dependent kernel obligation -/

/-- The actual finite physical labellings selected by the pinned datum. -/
def physicalLabellings (D : CompactDualPhysicalData) :
    List SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  explicitPhysicalLabellings D.cutoff D.boxExtent

/-- Push the actual fine spin-foam weight through a proposed source-dependent
kernel onto one actual coarse labelling. -/
def physicalKernelPushforward
    (fine : CompactDualPhysicalData)
    (kernel :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling →
        SU2FundamentalPentagonFiniteGraph.EdgeLabelling → Q')
    (target : SU2FundamentalPentagonFiniteGraph.EdgeLabelling) : Q' :=
  listQSum
    (fun source => fine.physicalTerm source * kernel source target)
    (physicalLabellings fine)

/-- The precise finite-kernel input still missing before the rim candidate can
participate in CD-2.

The kernel is indexed by the two actual pinned physical data values and is
normalized and supported on their actual finite labelling lists.  This
structure deliberately does not carry the block decomposition, a remainder,
or reflection preservation; those are later obligations, and no inhabitant is
constructed here. -/
structure AllLabelSourceDependentKernelObligation
    (fine coarse : CompactDualPhysicalData) : Type where
  kernel :
    SU2FundamentalPentagonFiniteGraph.EdgeLabelling →
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling → Q'
  kernelNonnegative :
    ∀ source target,
      source ∈ physicalLabellings fine →
      target ∈ physicalLabellings coarse →
      (0 : Q') ≤ kernel source target
  rowNormalized :
    ∀ source,
      source ∈ physicalLabellings fine →
      listQSum (kernel source) (physicalLabellings coarse) ≈ 1
  targetSupported :
    ∀ source target,
      source ∈ physicalLabellings fine →
      target ∉ physicalLabellings coarse →
      kernel source target ≈ 0

#print axioms rimSectorOrbit_totalMultiplicity
#print axioms rimPageSpinSectorLedger_length
#print axioms rimPageSpinSectorLedger_orbitCounts
#print axioms rimSectorMonomial_nonnegative
#print axioms rimSectorOrbitContribution_nonnegative
#print axioms rimSectorOrbitActivity_resums
#print axioms rimSectorOrbitActivity_nonnegative
#print axioms rimChannelActivityPolynomial_nonnegative
#print axioms pinnedRimChannelCandidate_nonnegative
#print axioms contribution_nonnegative_of_rim_activity_square
#print axioms physicalKernelPushforward
#print axioms AllLabelSourceDependentKernelObligation

end YMGap.Continuum.CompactDualPositiveChannelDoor
