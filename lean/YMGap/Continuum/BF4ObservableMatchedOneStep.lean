/-
# The first observable-matched BF4 block step

The physical trajectory must be derived from the blocked law, not stored in
the free `SlabScalePair.couplingFlow` field.  This module constructs the first
such derived step on the exact cutoff-one corrected-slab kernel.

Fix:

* a fine coupling `g ≥ 0`;
* a corrected-slab coarse half-extent;
* a finite nonempty atlas of strictly positive candidate coarse couplings;
* a rational observable on the common coarse Cartesian state space.

For every candidate `g'`, the existing globally link-glued cutoff-one kernel
pushes the normalized fine physical law to an exact rational coarse law.
The candidate score is the absolute difference between the pushed
expectation and the normalized coarse Gibbs expectation at `g'`.  A
constructive finite argmin selects the candidate with least score.  The
selected coarse physical datum, scale pair, and total physical kernel are
then rebuilt definitionally from that coupling.

Consequently the resulting one-step coupling is not a freely declared flow:
it belongs to the supplied positive atlas and minimizes the exact physical
observable-matching defect.  This is the executable `M = 1` starting point of
the observable-matched trajectory proposed in "The trajectory is the
theorem".

Honest scope:

* the atlas is finite, so this does not yet construct the all-label or
  continuum weak-coupling limit;
* no particular separator observable or U(1) control kernel is instantiated
  here;
* no marginal asymptotic envelope is claimed.

Those are now downstream data/computation obligations rather than a free
`couplingFlow` field.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, custom axiom, noncomputable declaration, or placeholder.
-/

import YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward

namespace YMGap.Continuum.BF4ObservableMatchedOneStep

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

abbrev SlabLabelling := EdgeLabelling

/-! ## 1. Constructive finite argmin -/

private theorem q_le_of_not_le {left right : Q'}
    (hnot : ¬ left ≤ right) :
    right ≤ left := by
  show
    right.num * (left.den : Int) ≤
      left.num * (right.den : Int)
  have hcross :
      ¬ left.num * (right.den : Int) ≤
        right.num * (left.den : Int) :=
    hnot
  exact Int.le_of_lt (Int.not_le.mp hcross)

/-- A selected member of a finite candidate list whose rational score is no
larger than the score of any listed candidate. -/
structure FiniteArgmin {A : Type}
    (score : A → Q') (candidates : List A) : Type where
  choice : A
  choice_mem : choice ∈ candidates
  minimal : ∀ candidate, candidate ∈ candidates →
    score choice ≤ score candidate

/-- A nonempty finite rational-score problem has a constructive argmin.
Ties retain the earlier candidate. -/
def finiteArgmin {A : Type} (score : A → Q') :
    (head : A) → (tail : List A) →
      FiniteArgmin score (head :: tail)
  | head, [] =>
      { choice := head
        choice_mem := List.mem_cons_self
        minimal := by
          intro candidate hcandidate
          have heq : candidate = head := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hcandidate
            exact hcandidate
          rw [heq]
          exact Q'.le_refl' _ }
  | head, next :: tail =>
      let rest := finiteArgmin score next tail
      if hhead : score head ≤ score rest.choice then
        { choice := head
          choice_mem := List.mem_cons_self
          minimal := by
            intro candidate hcandidate
            have hcases :
                candidate = head ∨ candidate ∈ next :: tail :=
              List.mem_cons.mp hcandidate
            cases hcases with
            | inl heq =>
                rw [heq]
                exact Q'.le_refl' _
            | inr hrest =>
                exact Q'.le_trans' _ _ _
                  hhead (rest.minimal candidate hrest) }
      else
        { choice := rest.choice
          choice_mem :=
            List.mem_cons_of_mem head rest.choice_mem
          minimal := by
            intro candidate hcandidate
            have hcases :
                candidate = head ∨ candidate ∈ next :: tail :=
              List.mem_cons.mp hcandidate
            cases hcases with
            | inl heq =>
                rw [heq]
                exact q_le_of_not_le hhead
            | inr hrest =>
                exact rest.minimal candidate hrest }

theorem finiteArgmin_choice_mem {A : Type}
    (score : A → Q') (head : A) (tail : List A) :
    (finiteArgmin score head tail).choice ∈ head :: tail :=
  (finiteArgmin score head tail).choice_mem

theorem finiteArgmin_minimal {A : Type}
    (score : A → Q') (head : A) (tail : List A)
    (candidate : A) (hcandidate : candidate ∈ head :: tail) :
    score (finiteArgmin score head tail).choice ≤ score candidate :=
  (finiteArgmin score head tail).minimal candidate hcandidate

/-! ## 2. Exact cutoff-one BF4 geometry at a supplied coupling -/

/-- Geometry of one corrected-slab dyadic step.  If the coarse half-extent is
`h`, the fine half-extent is `2h+1`; hence

`centralExtent (2h+1) = dyadicSlabFineExtent (centralExtent h)`.
-/
structure CutoffOneGeometry : Type where
  coarseHalf : Nat

namespace CutoffOneGeometry

/-- Fine half-extent forced by boundary-complete dyadic reflection. -/
def fineHalf (G : CutoffOneGeometry) : Nat :=
  2 * G.coarseHalf + 1

theorem extent_relation (G : CutoffOneGeometry) :
    centralExtent G.fineHalf =
      dyadicSlabFineExtent (centralExtent G.coarseHalf) := by
  unfold fineHalf centralExtent dyadicSlabFineExtent
  omega

/-- The cutoff-one fine physical datum at coupling `g`. -/
def fineData (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g) : SlabPhysicalData where
  coupling := g
  coupling_nonnegative := hg
  cutoff := 1
  half := G.fineHalf

/-- The lossless cutoff-four coarse physical datum at candidate coupling
`candidate`. -/
def coarseData (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    SlabPhysicalData where
  coupling := candidate
  coupling_nonnegative := Q'.le_of_lt hcandidate
  cutoff := 4
  half := G.coarseHalf

/-- A provisional scale pair used solely to evaluate one candidate.  Its
constant flow field carries no information: the selected coupling below is
derived by minimizing the physical matching defect. -/
def candidateScalePair (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    SlabScalePair where
  fine := G.fineData g hg
  coarse := G.coarseData candidate hcandidate
  couplingFlow := fun _ => candidate
  fine_extent := G.extent_relation
  coarse_cutoff := rfl
  coarse_coupling := Q'.eqv_refl candidate

@[simp] theorem candidateScalePair_fine_cutoff
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    (G.candidateScalePair g hg candidate hcandidate).fine.cutoff = 1 :=
  rfl

@[simp] theorem candidateScalePair_coarse_coupling
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    (G.candidateScalePair g hg candidate hcandidate).coarse.coupling =
      candidate :=
  rfl

end CutoffOneGeometry

/-! ## 3. Positive finite coupling atlas -/

/-- A nonempty finite atlas of strictly positive candidate coarse couplings.
The explicit head makes selection total without choice. -/
structure PositiveCouplingAtlas : Type where
  head : Q'
  tail : List Q'
  head_pos : (0 : Q') < head
  tail_pos : ∀ candidate, candidate ∈ tail →
    (0 : Q') < candidate

namespace PositiveCouplingAtlas

def candidates (A : PositiveCouplingAtlas) : List Q' :=
  A.head :: A.tail

theorem candidate_pos (A : PositiveCouplingAtlas)
    {candidate : Q'} (hcandidate : candidate ∈ A.candidates) :
    (0 : Q') < candidate := by
  unfold candidates at hcandidate
  simp only [List.mem_cons] at hcandidate
  cases hcandidate with
  | inl heq =>
      rw [heq]
      exact A.head_pos
  | inr htail =>
      exact A.tail_pos candidate htail

end PositiveCouplingAtlas

/-! ## 4. Physical observable matching -/

/-- Exact expectation of a rational observable under a finite rational mass
on a named state list. -/
def observableExpectation
    (mass : SlabLabelling → Q')
    (states : List SlabLabelling)
    (observable : SlabLabelling → Q') : Q' :=
  listQSum (fun state => mass state * observable state) states

/-- The actual pushed expectation at one candidate coupling, using the exact
globally link-glued cutoff-one physical kernel. -/
def blockedObservableExpectation
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (observable : SlabLabelling → Q') : Q' :=
  let S := G.candidateScalePair g hg candidate hcandidate
  let K := physicalKernel S rfl hcandidate
  observableExpectation K.blockedMass
    S.coarse.physicalLabellings observable

/-- The normalized coarse Gibbs expectation at the same candidate
coupling. -/
def coarseObservableExpectation
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (observable : SlabLabelling → Q') : Q' :=
  let coarse := G.coarseData candidate hcandidate
  observableExpectation coarse.normalizedMass
    coarse.physicalLabellings observable

/-- Exact observable-matching defect at one candidate. -/
def observableMatchDefect
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (observable : SlabLabelling → Q') : Q' :=
  Q'.abs
    (blockedObservableExpectation G g hg candidate hcandidate observable +
      -(coarseObservableExpectation G candidate hcandidate observable))

/-- The atlas score, with candidate positivity obtained internally from
membership.  Values outside the atlas receive score zero but can never be
selected or compared by the theorems below. -/
def atlasObservableScore
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q')
    (candidate : Q') : Q' :=
  if hcandidate : candidate ∈ atlas.candidates then
    observableMatchDefect G g hg candidate
      (atlas.candidate_pos hcandidate) observable
  else 0

theorem atlasObservableScore_of_mem
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q')
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    atlasObservableScore G g hg atlas observable candidate =
      observableMatchDefect G g hg candidate
        (atlas.candidate_pos hcandidate) observable := by
  unfold atlasObservableScore
  rw [dif_pos hcandidate]

/-- The finite, exact observable-matched coarse coupling. -/
def observableMatchedCoupling
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') : Q' :=
  (finiteArgmin
    (atlasObservableScore G g hg atlas observable)
    atlas.head atlas.tail).choice

theorem observableMatchedCoupling_mem
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') :
    observableMatchedCoupling G g hg atlas observable ∈
      atlas.candidates := by
  exact finiteArgmin_choice_mem
    (atlasObservableScore G g hg atlas observable)
    atlas.head atlas.tail

theorem observableMatchedCoupling_pos
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') :
    (0 : Q') <
      observableMatchedCoupling G g hg atlas observable :=
  atlas.candidate_pos
    (observableMatchedCoupling_mem G g hg atlas observable)

theorem observableMatchedCoupling_minimizes
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q')
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    observableMatchDefect G g hg
        (observableMatchedCoupling G g hg atlas observable)
        (observableMatchedCoupling_pos G g hg atlas observable)
        observable ≤
      observableMatchDefect G g hg candidate
        (atlas.candidate_pos hcandidate) observable := by
  have hminimal :=
    finiteArgmin_minimal
      (atlasObservableScore G g hg atlas observable)
      atlas.head atlas.tail candidate hcandidate
  change
    atlasObservableScore G g hg atlas observable
        (observableMatchedCoupling G g hg atlas observable) ≤
      atlasObservableScore G g hg atlas observable candidate at hminimal
  rw [
    atlasObservableScore_of_mem G g hg atlas observable
      (observableMatchedCoupling G g hg atlas observable)
      (observableMatchedCoupling_mem G g hg atlas observable),
    atlasObservableScore_of_mem G g hg atlas observable
      candidate hcandidate
  ] at hminimal
  exact hminimal

/-! ## 5. The derived physical step -/

/-- The physical scale pair rebuilt from the observable-matched coupling. -/
def observableMatchedScalePair
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') :
    SlabScalePair :=
  G.candidateScalePair g hg
    (observableMatchedCoupling G g hg atlas observable)
    (observableMatchedCoupling_pos G g hg atlas observable)

/-- The exact total physical kernel at the derived coupling. -/
def observableMatchedPhysicalKernel
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') :
    (observableMatchedScalePair G g hg atlas observable).FiniteSlabKernel :=
  physicalKernel
    (observableMatchedScalePair G g hg atlas observable)
    rfl
    (observableMatchedCoupling_pos G g hg atlas observable)

/-- **The trajectory is a theorem, one-step form.**  The coarse coupling of
the reconstructed physical step is definitionally the exact finite argmin of
the pushed-vs-coarse observable defect. -/
theorem observableMatchedScalePair_coupling
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') :
    (observableMatchedScalePair G g hg atlas observable).coarse.coupling =
      observableMatchedCoupling G g hg atlas observable :=
  rfl

/-- The actual reconstructed step inherits the exact matching optimum over
the entire candidate atlas. -/
theorem observableMatchedScalePair_minimizes
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q')
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    observableMatchDefect G g hg
        (observableMatchedScalePair G g hg atlas observable).coarse.coupling
        (observableMatchedCoupling_pos G g hg atlas observable)
        observable ≤
      observableMatchDefect G g hg candidate
        (atlas.candidate_pos hcandidate) observable := by
  exact observableMatchedCoupling_minimizes
    G g hg atlas observable candidate hcandidate

/-! ## 6. Exact discriminator against the two-dimensional rule -/

/-- The exact heat-kernel self-reproduction reference used by the DP
discriminator: one two-dimensional scale-four block sends `s` to `s^4`.

This is a comparison value, not an assertion that the four-dimensional
physical flow obeys that rule. -/
def twoDimensionalReference (s : Q') : Q' :=
  s ^ 4

/-- A computational, `Type`-valued result for comparing the derived BF4
coupling with a reference coupling.  Keeping the selected branch as data makes
the SU(2)/U(1) discriminator executable rather than hiding it in a
propositional existence statement. -/
inductive ReferenceComparison (actual reference : Q') : Type where
  | below : actual < reference → ReferenceComparison actual reference
  | matched : actual ≈ reference → ReferenceComparison actual reference
  | above : reference < actual → ReferenceComparison actual reference

private theorem q_eqv_of_neither_lt {left right : Q'}
    (hleft : ¬ left < right) (hright : ¬ right < left) :
    left ≈ right := by
  show
    left.num * (right.den : Int) =
      right.num * (left.den : Int)
  exact Int.le_antisymm (Int.not_lt.mp hright) (Int.not_lt.mp hleft)

/-- The exact, computable result of the first non-abelian discriminator.

The input coupling is compared with the selected observable-matched output,
not with a freely supplied `couplingFlow`.  This definition always returns one
of the three certificate-bearing branches.  It deliberately does not claim
which branch SU(2) occupies near `s = 1`; deciding that requires the named
separator observable and a refining weak-coupling atlas. -/
def observableMatchedReferenceComparison
    (G : CutoffOneGeometry)
    (s : Q') (hs : (0 : Q') ≤ s)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') :
    ReferenceComparison
      (observableMatchedCoupling G s hs atlas observable)
      (twoDimensionalReference s) :=
  if hbelow :
      observableMatchedCoupling G s hs atlas observable <
        twoDimensionalReference s then
    ReferenceComparison.below hbelow
  else if habove :
      twoDimensionalReference s <
        observableMatchedCoupling G s hs atlas observable then
    ReferenceComparison.above habove
  else
    ReferenceComparison.matched
      (q_eqv_of_neither_lt hbelow habove)

/-- Propositional view of the certificate returned by
`observableMatchedReferenceComparison`.  This is the exact trichotomy
`s' < s^4`, `s' ≈ s^4`, or `s^4 < s'` for the derived cutoff-one step. -/
theorem observableMatched_vs_twoDimensional
    (G : CutoffOneGeometry)
    (s : Q') (hs : (0 : Q') ≤ s)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') :
    observableMatchedCoupling G s hs atlas observable <
        twoDimensionalReference s ∨
      observableMatchedCoupling G s hs atlas observable ≈
        twoDimensionalReference s ∨
      twoDimensionalReference s <
        observableMatchedCoupling G s hs atlas observable := by
  cases observableMatchedReferenceComparison G s hs atlas observable with
  | below hbelow =>
      exact Or.inl hbelow
  | matched hmatched =>
      exact Or.inr (Or.inl hmatched)
  | above habove =>
      exact Or.inr (Or.inr habove)

end YMGap.Continuum.BF4ObservableMatchedOneStep

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4ObservableMatchedOneStep.finiteArgmin
#print axioms YMGap.Continuum.BF4ObservableMatchedOneStep.finiteArgmin_minimal
#print axioms YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry.extent_relation
#print axioms YMGap.Continuum.BF4ObservableMatchedOneStep.observableMatchedCoupling_mem
#print axioms YMGap.Continuum.BF4ObservableMatchedOneStep.observableMatchedCoupling_pos
#print axioms YMGap.Continuum.BF4ObservableMatchedOneStep.observableMatchedCoupling_minimizes
#print axioms YMGap.Continuum.BF4ObservableMatchedOneStep.observableMatchedScalePair_coupling
#print axioms YMGap.Continuum.BF4ObservableMatchedOneStep.observableMatchedScalePair_minimizes
#print axioms YMGap.Continuum.BF4ObservableMatchedOneStep.observableMatchedReferenceComparison
#print axioms YMGap.Continuum.BF4ObservableMatchedOneStep.observableMatched_vs_twoDimensional
