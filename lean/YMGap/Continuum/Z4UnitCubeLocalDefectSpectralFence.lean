/-
# A local block coordinate does not determine a transfer spectral gap

The exact finite spin-foam law now supplies two normalized unit-cube occurrence
probabilities and their absolute difference.  Those are one-time, one-coordinate
data.  A transfer spectral gap is instead a statement about Euclidean-time
correlations.  This file records the missing identification as a kernel-checked
fence.

`activityMatchedCoordinate` packages the actual coarse/refined probabilities
and defect from `Z4CouplingParametricFiniteCylinderLaw`.  A
`ReflectionPositiveTransferCompletion D` attaches a finite Kallen--Lehmann
transfer model to the same local datum `D`; its nonnegative spectral weights
give reflection positivity, its nonnegative eigenvalues give transfer
positivity, and `contractive` bounds them by one.

For every local datum there are two exact completions:

* `persistentCompletion`: one positive excited mode with eigenvalue `1`; it has
  no located gap;
* `decorrelatingCompletion`: the same positive mode with eigenvalue `0`; it has
  the maximal located separator `0`.

Both completions are reflection-positive contractions and are indexed by the
definitionally identical local coordinate.  Therefore even positive local
occurrences and a strict one-coordinate defect cannot imply a gap for an
otherwise-unidentified transfer operator.  The final witness is instantiated
with the genuine activity-matched law at every positive coupling, cutoff at
least one, and containing volume, so it is not a vacuous abstract
counterexample.  A viable bridge must add a time-shift / Schwinger-correlation
identity connecting the spin-foam law to the transfer model.

All declarations are constructive and exact over `Q'`.  There is no
`Classical.*`, `Real`, `native_decide`, `sorry`, or new axiom.  Closed rational
facts use kernel `decide` only.
-/

import YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.Z4UnitCubeLocalDefectSpectralFence

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

/-! ## The exact one-coordinate block datum -/

/-- The information exposed by one coarse/refined unit-cube coordinate.  The
probability bounds and exact absolute-difference identity are retained, but no
Euclidean time-shift or two-time correlation is smuggled into the datum. -/
structure UnitCubeLocalCoordinate : Type where
  coarseProbability : Q'
  refinedProbability : Q'
  defect : Q'
  coarse_nonnegative : (0 : Q') ≤ coarseProbability
  coarse_le_one : coarseProbability ≤ (1 : Q')
  refined_nonnegative : (0 : Q') ≤ refinedProbability
  refined_le_one : refinedProbability ≤ (1 : Q')
  defect_exact : defect = Q'.abs (coarseProbability + (-refinedProbability))

/-- The actual activity-matched physical spin-foam coordinate at arbitrary
nonnegative fine coupling, cutoff, and finite volume. -/
def activityMatchedCoordinate
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : UnitCubeLocalCoordinate where
  coarseProbability :=
    couplingKUnitCubeBlockCoarseProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume
  refinedProbability :=
    couplingKUnitCubeBlockRefinedProbability
      fineCoupling hfine cutoff volume
  defect := activityMatchedUnitCubeBlockDefect
    fineCoupling hfine cutoff volume
  coarse_nonnegative :=
    couplingKUnitCubeBlockCoarseProbability_nonnegative
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume
  coarse_le_one :=
    couplingKUnitCubeBlockCoarseProbability_le_one
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume
  refined_nonnegative :=
    couplingKUnitCubeBlockRefinedProbability_nonnegative
      fineCoupling hfine cutoff volume
  refined_le_one :=
    couplingKUnitCubeBlockRefinedProbability_le_one
      fineCoupling hfine cutoff volume
  defect_exact := rfl

/-! ## Reflection-positive finite transfer completions -/

/-- A reflection-positive, positive, contractive finite transfer completion of
the given local block coordinate.  `SpectralModel` carries nonnegative
Kallen--Lehmann weights and eigenvalues; the extra field is the transfer
contraction bound.  Crucially, this structure contains no unproved assertion
that the local block coordinate is a two-time transfer correlation. -/
structure ReflectionPositiveTransferCompletion
    (_D : UnitCubeLocalCoordinate) : Type where
  model : SpectralModel
  contractive : ∀ i, model.lam i ≤ (1 : Q')

/-- The diagonal reflection form of a finite transfer completion. -/
def reflectionForm {D : UnitCubeLocalCoordinate}
    (C : ReflectionPositiveTransferCompletion D)
    (coeff : Nat → Q') : Q' :=
  finSum (fun i => C.model.w i * (coeff i * coeff i)) C.model.k

private theorem finSum_nonnegative (f : Nat → Q')
    (hf : ∀ i, (0 : Q') ≤ f i) : ∀ n, (0 : Q') ≤ finSum f n
  | 0 => Q'.le_refl' 0
  | n + 1 => Q'.zero_le_add _ _ (finSum_nonnegative f hf n) (hf n)

/-- Every completion is reflection positive: its diagonal reflection form is
a finite sum of nonnegative spectral weights times exact squares. -/
theorem reflectionForm_nonnegative {D : UnitCubeLocalCoordinate}
    (C : ReflectionPositiveTransferCompletion D)
    (coeff : Nat → Q') :
    (0 : Q') ≤ reflectionForm C coeff := by
  unfold reflectionForm
  apply finSum_nonnegative
  intro i
  exact Q'.mul_nonneg _ _ (C.model.w_nonneg i)
    (SumOfSquares.q_mul_self_nonneg (coeff i))

/-! ## Two incompatible exact transfer spectra over the same local law -/

/-- A single positive excited mode that persists with transfer eigenvalue one. -/
def persistentModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => 1
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => by decide

/-- The same positive excited mode, killed after one time step. -/
def decorrelatingModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => 0
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => by decide

/-- A reflection-positive contractive completion with a persistent mode. -/
def persistentCompletion (D : UnitCubeLocalCoordinate) :
    ReflectionPositiveTransferCompletion D where
  model := persistentModel
  contractive := fun _ => by
    change (1 : Q') ≤ (1 : Q')
    exact Q'.le_refl' 1

/-- A reflection-positive contractive completion with immediate decorrelation. -/
def decorrelatingCompletion (D : UnitCubeLocalCoordinate) :
    ReflectionPositiveTransferCompletion D where
  model := decorrelatingModel
  contractive := fun _ => by
    change (0 : Q') ≤ (1 : Q')
    exact Q'.zero_le_one

/-- The decorrelating completion has the exact located separator zero. -/
def decorrelatingLocatedGap (D : UnitCubeLocalCoordinate) :
    LocatedSpectralGap (decorrelatingCompletion D).model where
  sep := 0
  sep_lt_one := by decide
  bound := fun _ => by
    change (0 : Q') ≤ (0 : Q')
    exact Q'.le_refl' 0

/-- The persistent completion cannot have any separator strictly below one. -/
theorem persistent_no_located_gap (D : UnitCubeLocalCoordinate) :
    LocatedSpectralGap (persistentCompletion D).model → False := by
  intro g
  have hone_le := g.bound 0
  change (1 : Q') ≤ g.sep at hone_le
  have hone_lt : (1 : Q') < (1 : Q') :=
    Q'.lt_of_le_of_lt hone_le g.sep_lt_one
  exact (by decide : ¬ ((1 : Q') < (1 : Q'))) hone_lt

/-- Type-level certificate that the definitionally same local coordinate has
both a maximally gapped and a gapless reflection-positive transfer completion. -/
structure IncompatibleTransferCompletions
    (D : UnitCubeLocalCoordinate) : Type where
  gapped : ReflectionPositiveTransferCompletion D
  gap : LocatedSpectralGap gapped.model
  gapless : ReflectionPositiveTransferCompletion D
  no_gap : LocatedSpectralGap gapless.model → False

/-- The incompatibility certificate exists for every local coordinate. -/
def incompatibleTransferCompletions (D : UnitCubeLocalCoordinate) :
    IncompatibleTransferCompletions D where
  gapped := decorrelatingCompletion D
  gap := decorrelatingLocatedGap D
  gapless := persistentCompletion D
  no_gap := persistent_no_located_gap D

/-! ## The current physical strict defect does not close the spectral wall -/

/-- A positive, strict-defect local coordinate together with a
reflection-positive contractive completion that provably has no located gap.
This packages the exact counterexample to the unlinked local-to-spectral
inference without turning the missing identification into a premise. -/
structure PositiveStrictDefectGaplessCompletion
    (D : UnitCubeLocalCoordinate) : Type where
  coarse_pos : (0 : Q') < D.coarseProbability
  refined_pos : (0 : Q') < D.refinedProbability
  defect_lt_one : D.defect < (1 : Q')
  completion : ReflectionPositiveTransferCompletion D
  no_gap : LocatedSpectralGap completion.model → False

/-- **Machine-checked physical fence.**  At every positive coupling, cutoff at
least one, and containing volume, the genuine activity-matched spin-foam
coordinate has positive coarse/refined probabilities and strict defect, yet it
admits the exact persistent reflection-positive completion with no located gap.
Thus the local estimates require a new time-translation/correlation
identification before they can feed the spectral-gap route. -/
def activityMatchedPositiveStrictDefectGaplessCompletion
    {fineCoupling : Q'} (hfine0 : (0 : Q') ≤ fineCoupling)
    (hfine : (0 : Q') < fineCoupling)
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    PositiveStrictDefectGaplessCompletion
      (activityMatchedCoordinate fineCoupling hfine0 cutoff volume) where
  coarse_pos := by
    change (0 : Q') < couplingKUnitCubeBlockCoarseProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine0) cutoff volume
    exact activityMatchedUnitCubeBlockCoarseProbability_pos
      hfine0 hfine hcutoff hvolume
  refined_pos := by
    change (0 : Q') < couplingKUnitCubeBlockRefinedProbability
      fineCoupling hfine0 cutoff volume
    exact activityMatchedUnitCubeBlockRefinedProbability_pos
      hfine0 hfine hcutoff hvolume
  defect_lt_one := by
    change activityMatchedUnitCubeBlockDefect
      fineCoupling hfine0 cutoff volume < (1 : Q')
    exact activityMatchedUnitCubeBlockDefect_lt_one
      hfine0 hfine hcutoff hvolume
  completion := persistentCompletion
    (activityMatchedCoordinate fineCoupling hfine0 cutoff volume)
  no_gap := persistent_no_located_gap
    (activityMatchedCoordinate fineCoupling hfine0 cutoff volume)

end YMGap.Continuum.Z4UnitCubeLocalDefectSpectralFence

#print axioms YMGap.Continuum.Z4UnitCubeLocalDefectSpectralFence.activityMatchedCoordinate
#print axioms YMGap.Continuum.Z4UnitCubeLocalDefectSpectralFence.reflectionForm_nonnegative
#print axioms YMGap.Continuum.Z4UnitCubeLocalDefectSpectralFence.decorrelatingLocatedGap
#print axioms YMGap.Continuum.Z4UnitCubeLocalDefectSpectralFence.persistent_no_located_gap
#print axioms YMGap.Continuum.Z4UnitCubeLocalDefectSpectralFence.incompatibleTransferCompletions
#print axioms YMGap.Continuum.Z4UnitCubeLocalDefectSpectralFence.activityMatchedPositiveStrictDefectGaplessCompletion
