/-
# The exact source/target kernel on a matched BF4 block step

`BF4MatchedPhysicalAFBridge.blockedWeight` is definitionally the finite
observable- or exponent-Gram-matching argmin.  The same two matching modules
also construct an actual source-indexed, target-indexed stochastic BF4
kernel, but the common `MatchedBlockFamily` interface previously exposed only
the selected scalar coupling.

This module closes that purely definitional gap.  It constructs, for every
matched family and rational chart coordinate, the exact physical scale pair
and its exact cutoff-one globally link-glued kernel.  Its coarse coupling is
literally

    blockedWeight family g.

Consequently every kernel entry, blocked marginal, source list, and target
list below belongs to the same matched action used by
`physicalAFEnvelope`.

This does not construct the square, normalized five-holonomy transfer
operator required for a Perron ratio.  The kernel here maps the fine slab
carrier to the coarse slab carrier.  In particular, the cutoff-free scalar
`nonlinearFiveHaarL2Sq` cannot be substituted for a source/target operator
ratio.

## Constructivity

Only case analysis and the already-constructed finite physical kernels are
used; every theorem is checked below with its exact dependency footprint.
-/

import YMGap.Continuum.BF4MatchedPhysicalAFBridge
import YMGap.Continuum.BF4GaussianPerronRatio
import YMGap.Continuum.FiniteCarrierHSPerronPerturbation
import YMGap.Continuum.FiveHolonomyPerronCutoff
import YMGap.Continuum.RationalCrossRatioDiameter

namespace YMGap.Continuum.BF4MatchedPhysicalKernelBridge

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteCarrierHSPerronPerturbation
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The matched scale pair -/

/-- The exact physical scale pair selected by a matched family.

Both branches use the same finite argmin that defines `blockedWeight`; no
surrogate Padé or dyadic weight is inserted. -/
def matchedPhysicalScalePair
    (family : MatchedBlockFamily) (g : Q') : SlabScalePair :=
  match family with
  | .observable data =>
      observableMatchedScalePair
        (data.geometry g)
        (data.fineWeight g)
        (data.fineWeight_nonnegative g)
        (data.atlas g)
        (data.observable g)
  | .exponentGram data =>
      exponentGramMatchedScalePair
        (data.geometry g)
        (data.fineWeight g)
        (data.fineWeight_nonnegative g)
        (data.atlas g)
        (data.coordinates g)

/-- The fine character cutoff of the exact matched step is one. -/
@[simp] theorem matchedPhysicalScalePair_fine_cutoff
    (family : MatchedBlockFamily) (g : Q') :
    (matchedPhysicalScalePair family g).fine.cutoff = 1 := by
  cases family <;> rfl

/-- The coarse coupling of the exact source/target step is definitionally
the same finite argmin exposed as `blockedWeight`. -/
@[simp] theorem matchedPhysicalScalePair_coarse_coupling
    (family : MatchedBlockFamily) (g : Q') :
    (matchedPhysicalScalePair family g).coarse.coupling =
      blockedWeight family g := by
  cases family <;> rfl

/-- Positivity of the selected coupling, now stated on the actual coarse
datum consumed by the physical kernel constructor. -/
theorem matchedPhysicalScalePair_coarse_coupling_pos
    (family : MatchedBlockFamily) (g : Q') :
    (0 : Q') <
      (matchedPhysicalScalePair family g).coarse.coupling := by
  rw [matchedPhysicalScalePair_coarse_coupling]
  exact blockedWeight_pos family g

/-! ## 2. The actual matched source/target kernel -/

/-- The complete finite cutoff-one globally link-glued BF4 kernel at the
coupling selected by the matching argmin. -/
def matchedPhysicalKernel
    (family : MatchedBlockFamily) (g : Q') :
    (matchedPhysicalScalePair family g).FiniteSlabKernel :=
  physicalKernel
    (matchedPhysicalScalePair family g)
    (matchedPhysicalScalePair_fine_cutoff family g)
    (matchedPhysicalScalePair_coarse_coupling_pos family g)

/-- The exact source-to-target entry of the matched physical block kernel. -/
def matchedPhysicalKernelEntry
    (family : MatchedBlockFamily) (g : Q')
    (source target : EdgeLabelling) : Q' :=
  (matchedPhysicalKernel family g).kernel source target

/-- The exact blocked target mass obtained by pushing the matched fine Gibbs
law through the matched source/target kernel. -/
def matchedPhysicalBlockedMass
    (family : MatchedBlockFamily) (g : Q')
    (target : EdgeLabelling) : Q' :=
  (matchedPhysicalKernel family g).blockedMass target

/-- Every physical entry is nonnegative on the literal matched source and
target carriers. -/
theorem matchedPhysicalKernelEntry_nonnegative
    (family : MatchedBlockFamily) (g : Q')
    (source target : EdgeLabelling)
    (hsource :
      source ∈
        (matchedPhysicalScalePair family g).fine.physicalLabellings)
    (htarget :
      target ∈
        (matchedPhysicalScalePair family g).coarse.physicalLabellings) :
    (0 : Q') ≤
      matchedPhysicalKernelEntry family g source target :=
  (matchedPhysicalKernel family g).nonnegative
    source target hsource htarget

/-- Every physical row has exact unit mass on the literal matched coarse
carrier. -/
theorem matchedPhysicalKernelEntry_row_normalized
    (family : MatchedBlockFamily) (g : Q')
    (source : EdgeLabelling)
    (hsource :
      source ∈
        (matchedPhysicalScalePair family g).fine.physicalLabellings) :
    listQSum
        (matchedPhysicalKernelEntry family g source)
        (matchedPhysicalScalePair family g).coarse.physicalLabellings
      ≈ 1 := by
  exact (matchedPhysicalKernel family g).row_normalized source hsource

/-- The matched blocked mass is definitionally the blocked mass of the exact
physical kernel; this theorem is supplied as a stable rewrite point for
later operator constructions. -/
theorem matchedPhysicalBlockedMass_eq
    (family : MatchedBlockFamily) (g : Q')
    (target : EdgeLabelling) :
    matchedPhysicalBlockedMass family g target =
      (matchedPhysicalKernel family g).blockedMass target :=
  rfl

/-- The matched blocked marginal has exact total mass one. -/
theorem matchedPhysicalBlockedMass_total
    (family : MatchedBlockFamily) (g : Q') :
    listQSum
        (matchedPhysicalBlockedMass family g)
        (matchedPhysicalScalePair family g).coarse.physicalLabellings
      ≈ 1 := by
  exact (matchedPhysicalKernel family g).blockedMass_total

/-- The matched blocked marginal is nonnegative on the actual target
carrier. -/
theorem matchedPhysicalBlockedMass_nonnegative
    (family : MatchedBlockFamily) (g : Q')
    (target : EdgeLabelling)
    (htarget :
      target ∈
        (matchedPhysicalScalePair family g).coarse.physicalLabellings) :
    (0 : Q') ≤ matchedPhysicalBlockedMass family g target := by
  exact (matchedPhysicalKernel family g).blockedMass_nonnegative htarget

/-! ## 3. A genuine square section and its executable projective rate

The matched block kernel is rectangular: its selected source states belong
to the fine slab and its selected target states belong to the coarse slab.
A Perron argument therefore first needs an explicitly identified common
carrier.  The structure below records that identification without assuming
that one exists.
-/

/-- A nonempty common carrier embedded into both the fine and coarse state
lists of the exact matched physical kernel. -/
structure MatchedSameCarrierSection
    (family : MatchedBlockFamily) (g : Q') : Type 1 where
  Carrier : Type
  head : Carrier
  tail : List Carrier
  source : Carrier → EdgeLabelling
  target : Carrier → EdgeLabelling
  source_mem :
    ∀ state, state ∈ head :: tail →
      source state ∈
        (matchedPhysicalScalePair family g).fine.physicalLabellings
  target_mem :
    ∀ state, state ∈ head :: tail →
      target state ∈
        (matchedPhysicalScalePair family g).coarse.physicalLabellings

namespace MatchedSameCarrierSection

variable {family : MatchedBlockFamily} {g : Q'}
    (carrierData : MatchedSameCarrierSection family g)

/-- The explicitly square matrix obtained by reading the exact matched
physical source/target entries on one common carrier. -/
def kernel (first second : carrierData.Carrier) : Q' :=
  matchedPhysicalKernelEntry family g
    (carrierData.source first) (carrierData.target second)

/-- Every selected entry is nonnegative. -/
theorem kernel_nonnegative
    (first second : carrierData.Carrier)
    (hfirst : first ∈ carrierData.head :: carrierData.tail)
    (hsecond : second ∈ carrierData.head :: carrierData.tail) :
    (0 : Q') ≤ carrierData.kernel first second :=
  matchedPhysicalKernelEntry_nonnegative family g
    (carrierData.source first) (carrierData.target second)
    (carrierData.source_mem first hfirst)
    (carrierData.target_mem second hsecond)

/-- The explicit nonempty enumeration retained by the common carrier. -/
def states : List carrierData.Carrier :=
  carrierData.head :: carrierData.tail

/-- Its exact finite function-space dimension. -/
def carrierSize : Nat :=
  carrierData.states.length

/-- Totalized lookup in the retained physical carrier.  Indices below
`carrierSize` read the corresponding state; the distinguished head is used
only outside the finite matrix. -/
def stateAt (index : Nat) : carrierData.Carrier :=
  carrierData.states.getD index carrierData.head

/-- Every in-range lookup is a member of the retained common carrier. -/
theorem stateAt_mem
    {index : Nat} (hindex : index < carrierData.carrierSize) :
    carrierData.stateAt index ∈ carrierData.states := by
  change index < carrierData.states.length at hindex
  change carrierData.states.getD index carrierData.head ∈
    carrierData.states
  rw [← List.getElem_eq_getD
    (l := carrierData.states)
    (i := index)
    (h := hindex)
    carrierData.head]
  exact List.getElem_mem hindex

/-- The exact physical square-section entries, totalized as the arbitrary
finite rational matrix consumed by the dimension-free HS theorem. -/
def rationalMatrix : RationalMatrix :=
  fun row column =>
    carrierData.kernel
      (carrierData.stateAt row)
      (carrierData.stateAt column)

/-- In-range entries of `rationalMatrix` are literal entries of the matched
BF4 source/target kernel. -/
theorem rationalMatrix_entry
    (row column : Nat) :
    carrierData.rationalMatrix row column =
      matchedPhysicalKernelEntry family g
        (carrierData.source (carrierData.stateAt row))
        (carrierData.target (carrierData.stateAt column)) :=
  rfl

/-- Every in-range entry of the totalized physical square section is
nonnegative. -/
theorem rationalMatrix_nonnegative
    {row column : Nat}
    (hrow : row < carrierData.carrierSize)
    (hcolumn : column < carrierData.carrierSize) :
    (0 : Q') ≤ carrierData.rationalMatrix row column := by
  exact carrierData.kernel_nonnegative
    (carrierData.stateAt row)
    (carrierData.stateAt column)
    (carrierData.stateAt_mem hrow)
    (carrierData.stateAt_mem hcolumn)

end MatchedSameCarrierSection

/-- A finite projective-diameter certificate on an actual square section of
the exact matched physical kernel.  Unlike the nonlinear Haar-square
completion, this datum has literal source and target indices.

It is still a projective certificate, not yet a proof that its Birkhoff
candidate equals the nonlinear BF4 Perron spectral ratio. -/
structure MatchedPhysicalProjectiveSection
    (family : MatchedBlockFamily) (g : Q') : Type 1 where
  carrierData : MatchedSameCarrierSection family g
  diameter :
    FiniteCrossRatioDiameterCertificate
      carrierData.kernel
      (carrierData.head :: carrierData.tail)
      (carrierData.head :: carrierData.tail)

namespace MatchedPhysicalProjectiveSection

variable {family : MatchedBlockFamily} {g : Q'}
    (projective : MatchedPhysicalProjectiveSection family g)

/-- The canonical rational Birkhoff--Hopf candidate attached to the exact
matched source/target kernel section. -/
def candidateRate : Q' :=
  projective.diameter.candidateRate

/-- The candidate is nonnegative, derived from the finite cross-ratio
certificate. -/
theorem candidateRate_nonnegative :
    (0 : Q') ≤ projective.candidateRate :=
  projective.diameter.candidateRate_nonnegative

/-- The minimal executable quarter check.  It is the cross-multiplied form
of

`(spread - 1) / (spread + 1) <= 1/4`.

For a concrete finite physical section this is a closed rational inequality
and can be discharged by kernel reduction with `decide`. -/
def QuarterCheck : Prop :=
  projective.diameter.spread + -(1 : Q') ≤
    BF4GaussianPerronRatio.oneQuarter *
      (projective.diameter.spread + 1)

/-- A successful exact rational check proves that the projective candidate
is at most one quarter. -/
theorem candidateRate_le_quarter
    (check : projective.QuarterCheck) :
    projective.candidateRate ≤
      BF4GaussianPerronRatio.oneQuarter := by
  unfold candidateRate
  unfold FiniteCrossRatioDiameterCertificate.candidateRate
  exact Q'.divPos_le_of_le_mul
    (projective.diameter.spread + -(1 : Q'))
    (projective.diameter.spread + 1)
    projective.diameter.candidateDenominator_pos
    check

/-- A second executable route uses the already-proved `7/100` Gaussian
buffer.  Here the candidate is definitionally evaluated on the exact matched
source/target section, rather than supplied as an unrelated scalar. -/
def GaussianBufferCheck (approximation : Nat) : Prop :=
  projective.candidateRate ≤
    BF4GaussianPerronRatio.gaussianPerronRatio.approx approximation +
      BF4GaussianPerronRatio.sevenHundredths

/-- The finite Gaussian-buffer check also gives the quarter bound. -/
theorem candidateRate_le_quarter_of_gaussianBuffer
    (approximation : Nat)
    (check : projective.GaussianBufferCheck approximation) :
    projective.candidateRate ≤
      BF4GaussianPerronRatio.oneQuarter :=
  BF4GaussianPerronRatio.perturbed_ratio_le_quarter
    approximation check

end MatchedPhysicalProjectiveSection

/-! ## 4. Exact physical-section specialization of the HS theorem -/

/-- A same-carrier BF4 HS comparison whose nonlinear matrix is
definitionally the exact matched physical square section above. -/
abbrev MatchedPhysicalBufferedHSPerturbation
    {family : MatchedBlockFamily} {g : Q'}
    (carrierData : MatchedSameCarrierSection family g)
    (gaussian : RationalMatrix) (approximation : Nat) : Type :=
  BF4BufferedFiniteCarrierHSPerturbation
    carrierData.rationalMatrix gaussian
    carrierData.carrierSize approximation

/-- A genuine eigenmode of the exact matched physical square-section
matrix. -/
abbrev MatchedPhysicalFiniteEigenmode
    {family : MatchedBlockFamily} {g : Q'}
    (carrierData : MatchedSameCarrierSection family g) : Type :=
  FiniteCarrierEigenmode
    carrierData.rationalMatrix carrierData.carrierSize

/-- **Nonlinear quarter theorem on literal matched BF4 entries.**

For any constructed common physical carrier, an exact `7/100` HS comparison
with the Gaussian reference bounds every nonnegative eigenmode of that
physical square section by `1/4`. -/
theorem matchedPhysical_eigenmode_ratio_le_quarter
    {family : MatchedBlockFamily} {g : Q'}
    {carrierData : MatchedSameCarrierSection family g}
    {gaussian : RationalMatrix} {approximation : Nat}
    (perturbation :
      MatchedPhysicalBufferedHSPerturbation
        carrierData gaussian approximation)
    (mode : MatchedPhysicalFiniteEigenmode carrierData) :
    mode.ratio ≤ BF4GaussianPerronRatio.oneQuarter :=
  bf4_nonlinear_eigenmode_ratio_le_quarter perturbation mode

/-- The stronger all-vector Rayleigh form on the exact matched physical
square section. -/
theorem matchedPhysical_quadratic_abs_le_quarter
    {family : MatchedBlockFamily} {g : Q'}
    {carrierData : MatchedSameCarrierSection family g}
    {gaussian : RationalMatrix} {approximation : Nat}
    (perturbation :
      MatchedPhysicalBufferedHSPerturbation
        carrierData gaussian approximation)
    (vector : RationalVector)
    (vectorNorm_pos :
      (0 : Q') <
        vectorNormSq vector carrierData.carrierSize) :
    Q'.abs
        (matrixQuadratic
          carrierData.rationalMatrix vector
          carrierData.carrierSize) ≤
      BF4GaussianPerronRatio.oneQuarter *
        vectorNormSq vector carrierData.carrierSize :=
  bf4_nonlinear_quadratic_abs_le_quarter
    perturbation vector vectorNorm_pos

/-! ## 5. Explicit physical Perron identification boundary -/

/-- The precise spectral-identification input still required after the
same-carrier matrix and HS estimate have been constructed.

`controlledByRayleigh` says that the physical largest nonvacuum contraction
is controlled by every uniform absolute Rayleigh bound on the literal
matched square-section matrix.  A future construction should derive this
field from normalization, self-adjointness, vacuum removal, and a
finite-carrier spectral theorem; it is not asserted by the rectangular
Markov kernel alone. -/
structure MatchedPhysicalPerronIdentification
    {family : MatchedBlockFamily} {g : Q'}
    (carrierData : MatchedSameCarrierSection family g) : Type where
  qS : Q'
  qS_nonnegative : (0 : Q') ≤ qS
  controlledByRayleigh :
    ∀ rate : Q',
      (∀ vector : RationalVector,
        (0 : Q') <
            vectorNormSq vector carrierData.carrierSize →
          Q'.abs
              (matrixQuadratic
                carrierData.rationalMatrix vector
                carrierData.carrierSize) ≤
            rate *
              vectorNormSq vector carrierData.carrierSize) →
      qS ≤ rate

/-- **Physical nonlinear `q ≤ 1/4` theorem.**

The conclusion concerns the `qS` retained by the explicit physical Perron
identification, while the analytic input is the exact same-carrier
`7/100` Hilbert--Schmidt comparison. -/
theorem matchedPhysical_perronRatio_le_quarter
    {family : MatchedBlockFamily} {g : Q'}
    {carrierData : MatchedSameCarrierSection family g}
    {gaussian : RationalMatrix} {approximation : Nat}
    (perturbation :
      MatchedPhysicalBufferedHSPerturbation
        carrierData gaussian approximation)
    (identification :
      MatchedPhysicalPerronIdentification carrierData) :
    identification.qS ≤ BF4GaussianPerronRatio.oneQuarter := by
  exact identification.controlledByRayleigh
    BF4GaussianPerronRatio.oneQuarter
    (fun vector vectorNorm_pos =>
      matchedPhysical_quadratic_abs_le_quarter
        perturbation vector vectorNorm_pos)

/-- Package the exact physical Perron ratio for the existing moving-cutoff
theorem after a spacing/depth choice has been made. -/
def matchedPhysicalNonlinearSpectralCertificate
    {family : MatchedBlockFamily} {g : Q'}
    {carrierData : MatchedSameCarrierSection family g}
    {gaussian : RationalMatrix} {approximation bits m : Nat}
    (perturbation :
      MatchedPhysicalBufferedHSPerturbation
        carrierData gaussian approximation)
    (identification :
      MatchedPhysicalPerronIdentification carrierData)
    (movingDepth : 192 * bits + 1 ≤ m - 2) :
    FiveHolonomyPerronCutoff.NonlinearSpectralCertificate bits where
  qS := identification.qS
  m := m
  qS_nonneg := identification.qS_nonnegative
  qS_le_quarter := by
    simpa only
      [FiveHolonomyPerronCutoff.quarter,
        BF4GaussianPerronRatio.oneQuarter]
      using
        matchedPhysical_perronRatio_le_quarter
          perturbation identification
  moving_depth := movingDepth

/-- **Physical same-carrier closure of
`C_s² q_s^(m-2) < 1`.**

All quantities in the conclusion are now tied either to the all-label
five-holonomy geometry or to the exact matched physical square-section
kernel. -/
theorem matchedPhysical_perron_cutoff_strict
    (D : FiveHolonomyPerronCutoff.AllLabelCutoffCertificate)
    (G : FiveHolonomyPerronCutoff.FiveHolonomyGeometry D)
    {family : MatchedBlockFamily} {g : Q'}
    {carrierData : MatchedSameCarrierSection family g}
    {gaussian : RationalMatrix} {approximation m : Nat}
    (perturbation :
      MatchedPhysicalBufferedHSPerturbation
        carrierData gaussian approximation)
    (identification :
      MatchedPhysicalPerronIdentification carrierData)
    (movingDepth : 192 * D.bits + 1 ≤ m - 2) :
    G.cSsq * identification.qS ^ (m - 2) < 1 := by
  exact FiveHolonomyPerronCutoff.perron_cutoff_strict D G
    (matchedPhysicalNonlinearSpectralCertificate
      perturbation identification movingDepth)

end YMGap.Continuum.BF4MatchedPhysicalKernelBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysicalScalePair_fine_cutoff
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysicalScalePair_coarse_coupling
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysicalScalePair_coarse_coupling_pos
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysicalKernel
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysicalKernelEntry_nonnegative
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysicalKernelEntry_row_normalized
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysicalBlockedMass_total
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysicalBlockedMass_nonnegative
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.MatchedSameCarrierSection.kernel_nonnegative
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.MatchedPhysicalProjectiveSection.candidateRate_nonnegative
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.MatchedPhysicalProjectiveSection.candidateRate_le_quarter
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.MatchedPhysicalProjectiveSection.candidateRate_le_quarter_of_gaussianBuffer
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.MatchedSameCarrierSection.stateAt_mem
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.MatchedSameCarrierSection.rationalMatrix_nonnegative
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysical_eigenmode_ratio_le_quarter
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysical_quadratic_abs_le_quarter
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysical_perronRatio_le_quarter
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysicalNonlinearSpectralCertificate
#print axioms YMGap.Continuum.BF4MatchedPhysicalKernelBridge.matchedPhysical_perron_cutoff_strict
