/-
# Atlas-uniform outer-cutoff tube for stochastic BF4 SU(2) Gram distances

The nonlinear exponent-Gram distance has an executable Cauchy modulus for
each fixed candidate coupling.  This module takes the constructive maximum
of those moduli over the literal finite positive coupling atlas.

`SU2AtlasOuterPhysicalMarkovFamily` carries one physically pinned all-cutoff
Markov contract for every atlas member.  Given that family and a strict
subunit bound on the atlas, one natural-number cutoff works simultaneously
for every candidate and every pair of later stages.

This closes only the finite-atlas maximum.  It remains pointwise in the fine
nome and corrected-slab geometry, and it does not construct the positive-row
family, a weak-coupling spacing schedule, a located limiting separator, or a
continuum trajectory.

## Axiom gate

Finite `List`, `Nat`, and `Q'` algebra only.  No classical principle, native
decision shortcut, custom axiom, hidden proof hole, or noncomputable
declaration.
-/

import YMGap.Continuum.BF4SU2StochasticOuterExponentGramDistanceCRealLimit
import YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics
import YMGap.Continuum.BF4ExponentGramLocatedStability

namespace YMGap.Continuum.BF4SU2OuterCutoffAtlasUniformScoreTube

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ExponentGramLocatedStability
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.BF4SU2OuterRawKernelCoherenceReduction
open YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics
open
  YMGap.Continuum.BF4SU2StochasticOuterExponentGramDistanceCRealLimit
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A physical contract at every atlas candidate -/

/-- Candidate-indexed positive-row proofs for the literal globally
link-glued raw BF4 kernel on one finite positive atlas.

The structure deliberately stores the raw inputs rather than an arbitrary
`SU2OuterPhysicalMarkovContract`: the latter interface by itself admits a
nonphysical Dirac completion on higher-spin rows.  Normalized cutoff
stability is derived from each positive-row proof by
`su2OuterRawKernelCutoffStability`. -/
structure SU2AtlasOuterPhysicalMarkovFamily
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) : Type where
  positiveRow :
    ∀ candidate,
      (hcandidate : candidate ∈ atlas.candidates) →
        SU2OuterPositiveRowClosure
          G g hg candidate
          (atlas.candidate_pos hcandidate)

namespace SU2AtlasOuterPhysicalMarkovFamily

/-- The physically pinned Markov contract derived from the stored literal
raw-kernel proofs. -/
def contract
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {atlas : PositiveCouplingAtlas}
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g hg atlas)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
  SU2OuterPhysicalMarkovContract
      G g hg candidate
      (atlas.candidate_pos hcandidate) :=
  su2OuterPhysicalMarkovContractOfPositiveRowClosure
    (family.positiveRow candidate hcandidate)

end SU2AtlasOuterPhysicalMarkovFamily

/-- Construct the atlas family from positive rows of the literal globally
link-glued raw BF4 kernel.  All cutoff laws are theorems of those rows, so
this path cannot insert arbitrary higher-spin Dirac rows. -/
def su2AtlasOuterPhysicalMarkovFamilyOfRawKernel
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {atlas : PositiveCouplingAtlas}
    (positiveRow :
      ∀ candidate,
        (hcandidate : candidate ∈ atlas.candidates) →
          SU2OuterPositiveRowClosure
            G g hg candidate
            (atlas.candidate_pos hcandidate)) :
    SU2AtlasOuterPhysicalMarkovFamily
      G g hg atlas where
  positiveRow := positiveRow

/-! ## 2. Constructive finite-atlas maximum -/

private def listNatMax : List Nat → Nat
  | [] => 0
  | head :: tail => max head (listNatMax tail)

private theorem le_listNatMax_of_mem :
    ∀ {n : Nat} {items : List Nat},
      n ∈ items → n ≤ listNatMax items
  | _, [], hmem => absurd hmem List.not_mem_nil
  | n, head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst n
        exact Nat.le_max_left _ _
      · exact Nat.le_trans
          (le_listNatMax_of_mem htail)
          (Nat.le_max_right _ _)

/-- Candidate-specific nonlinear distance moduli, enumerated on the exact
atlas list. -/
def stochasticAtlasOuterExponentGramDistanceModuli
    (G : CutoffOneGeometry)
    (g : Q')
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : List Nat :=
  atlas.candidates.map (fun candidate =>
    stochasticOuterExponentGramDistanceModulus
      G g candidate ε coordinates)

/-- One common cutoff dominating every candidate's nonlinear distance
modulus. -/
def stochasticAtlasOuterExponentGramDistanceModulus
    (G : CutoffOneGeometry)
    (g : Q')
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : Nat :=
  listNatMax
    (stochasticAtlasOuterExponentGramDistanceModuli
      G g atlas coordinates ε)

theorem candidateDistanceModulus_le_atlasModulus
    (G : CutoffOneGeometry)
    (g : Q')
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (ε candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    stochasticOuterExponentGramDistanceModulus
        G g candidate ε coordinates ≤
      stochasticAtlasOuterExponentGramDistanceModulus
        G g atlas coordinates ε := by
  apply le_listNatMax_of_mem
  unfold stochasticAtlasOuterExponentGramDistanceModuli
  exact List.mem_map.mpr
    ⟨candidate, hcandidate, rfl⟩

/-! ## 3. The atlas score and its simultaneous Cauchy estimate -/

/-- The stochastic nonlinear score on an arbitrary rational candidate.
Outside the finite atlas it is zero; on an atlas member it is the exact
distance generated by that candidate's physical Markov contract. -/
def stochasticAtlasOuterExponentGramScore
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {atlas : PositiveCouplingAtlas}
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g hg atlas)
    (coordinates : List ExponentGramCoordinate)
    (K : Nat)
    (candidate : Q') : Q' :=
  if hcandidate : candidate ∈ atlas.candidates then
    stochasticOuterExponentGramDistance
      (family.contract candidate hcandidate)
      K coordinates
  else 0

theorem stochasticAtlasOuterExponentGramScore_of_mem
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {atlas : PositiveCouplingAtlas}
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g hg atlas)
    (coordinates : List ExponentGramCoordinate)
    (K : Nat)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    stochasticAtlasOuterExponentGramScore
        family coordinates K candidate =
      stochasticOuterExponentGramDistance
        (family.contract candidate hcandidate)
        K coordinates := by
  unfold stochasticAtlasOuterExponentGramScore
  rw [dif_pos hcandidate]

/-- Every pair of stages beyond the constructive atlas maximum is
two-sided `ε`-close for every atlas candidate. -/
theorem stochasticAtlasOuterExponentGramScore_uniform_twoSided
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g (Q'.le_of_lt hg0) atlas)
    (coordinates : List ExponentGramCoordinate)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      stochasticAtlasOuterExponentGramDistanceModulus
          G g atlas coordinates ε ≤ first)
    (hsecond :
      stochasticAtlasOuterExponentGramDistanceModulus
          G g atlas coordinates ε ≤ second)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    stochasticAtlasOuterExponentGramScore
          family coordinates first candidate ≤
        stochasticAtlasOuterExponentGramScore
            family coordinates second candidate + ε ∧
      stochasticAtlasOuterExponentGramScore
          family coordinates second candidate ≤
        stochasticAtlasOuterExponentGramScore
            family coordinates first candidate + ε := by
  rw [stochasticAtlasOuterExponentGramScore_of_mem
      family coordinates first candidate hcandidate,
    stochasticAtlasOuterExponentGramScore_of_mem
      family coordinates second candidate hcandidate]
  apply stochasticOuterExponentGramDistance_twoSided_of_modulus
    hg0 hg1
    (atlas.candidate_pos hcandidate)
    (hatlas1 candidate hcandidate)
    (family.contract candidate hcandidate)
    coordinates hε
  · exact Nat.le_trans
      (candidateDistanceModulus_le_atlasModulus
        G g atlas coordinates ε candidate hcandidate)
      hfirst
  · exact Nat.le_trans
      (candidateDistanceModulus_le_atlasModulus
        G g atlas coordinates ε candidate hcandidate)
      hsecond

/-- Absolute-difference form of the simultaneous atlas Cauchy estimate. -/
theorem stochasticAtlasOuterExponentGramScore_uniform_abs_sub_le
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g (Q'.le_of_lt hg0) atlas)
    (coordinates : List ExponentGramCoordinate)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      stochasticAtlasOuterExponentGramDistanceModulus
          G g atlas coordinates ε ≤ first)
    (hsecond :
      stochasticAtlasOuterExponentGramDistanceModulus
          G g atlas coordinates ε ≤ second)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    Q'.abs
        (stochasticAtlasOuterExponentGramScore
            family coordinates first candidate +
          -stochasticAtlasOuterExponentGramScore
            family coordinates second candidate) ≤
      ε := by
  have htwo :=
    stochasticAtlasOuterExponentGramScore_uniform_twoSided
      G hg0 hg1 atlas hatlas1 family coordinates hε
      hfirst hsecond candidate hcandidate
  exact CReal.abs_sub_le_of_bounds htwo.1 htwo.2

/-! ## 4. A literal atlas score tube at the common reference cutoff -/

/-- Rational reference score at the executable common atlas cutoff.  It is a
finite-stage proxy, not a silently selected constructive-real limit. -/
def stochasticAtlasOuterExponentGramReferenceScore
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {atlas : PositiveCouplingAtlas}
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g hg atlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q')
    (candidate : Q') : Q' :=
  stochasticAtlasOuterExponentGramScore
    family coordinates
    (stochasticAtlasOuterExponentGramDistanceModulus
      G g atlas coordinates ε)
    candidate

/-- Every later finite score lies in a uniform two-sided atlas tube around
the rational common-cutoff reference score. -/
def stochasticAtlasOuterExponentGramScoreTube
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g (Q'.le_of_lt hg0) atlas)
    (coordinates : List ExponentGramCoordinate)
    {ε : Q'} (hε : (0 : Q') < ε)
    (K : Nat)
    (hK :
      stochasticAtlasOuterExponentGramDistanceModulus
          G g atlas coordinates ε ≤ K) :
    AtlasScoreTube
      atlas
      (stochasticAtlasOuterExponentGramScore
        family coordinates K)
      (stochasticAtlasOuterExponentGramReferenceScore
        family coordinates ε)
      ε where
  error_nonnegative := Q'.le_of_lt hε
  limit_le_cutoff_add := by
    intro candidate hcandidate
    exact
      (stochasticAtlasOuterExponentGramScore_uniform_twoSided
        G hg0 hg1 atlas hatlas1 family coordinates hε
        (Nat.le_refl _) hK candidate hcandidate).1
  cutoff_le_limit_add := by
    intro candidate hcandidate
    exact
      (stochasticAtlasOuterExponentGramScore_uniform_twoSided
        G hg0 hg1 atlas hatlas1 family coordinates hε
        (Nat.le_refl _) hK candidate hcandidate).2

/-- Located separation of the explicit rational reference score stabilizes
the literal later-cutoff argmin.  A separator for the actual limiting score
is still a separate analytic input. -/
def stableStochasticAtlasArgminOfOuterTube
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g (Q'.le_of_lt hg0) atlas)
    (coordinates : List ExponentGramCoordinate)
    {ε : Q'} (hε : (0 : Q') < ε)
    (located :
      LocatedAtlasMinimizer
        atlas
        (stochasticAtlasOuterExponentGramReferenceScore
          family coordinates ε))
    (error_small : ε + ε < located.margin)
    (K : Nat)
    (hK :
      stochasticAtlasOuterExponentGramDistanceModulus
          G g atlas coordinates ε ≤ K) :
    StableAtlasArgminCertificate
      atlas
      (stochasticAtlasOuterExponentGramScore
        family coordinates K)
      (stochasticAtlasOuterExponentGramReferenceScore
        family coordinates ε)
      located :=
  stableAtlasArgminCertificate
    atlas
    (stochasticAtlasOuterExponentGramScore
      family coordinates K)
    (stochasticAtlasOuterExponentGramReferenceScore
      family coordinates ε)
    ε located
    (stochasticAtlasOuterExponentGramScoreTube
      G hg0 hg1 atlas hatlas1 family coordinates hε K hK)
    error_small

/-! ## 5. Type-level uniform modulus package -/

/-- A computable simultaneous Cauchy modulus for the complete finite atlas.
No limit or located separator is inserted into the structure. -/
structure SU2AtlasOuterCutoffScoreCauchy
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g)
    (atlas : PositiveCouplingAtlas)
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g (Q'.le_of_lt hg0) atlas)
    (coordinates : List ExponentGramCoordinate) : Type where
  modulus : Q' → Nat
  cauchy :
    ∀ ε : Q',
      (0 : Q') < ε →
      ∀ {first second : Nat},
        modulus ε ≤ first →
        modulus ε ≤ second →
        ∀ candidate,
          candidate ∈ atlas.candidates →
            Q'.abs
                (stochasticAtlasOuterExponentGramScore
                    family coordinates first candidate +
                  -stochasticAtlasOuterExponentGramScore
                    family coordinates second candidate) ≤
              ε

/-- The constructive finite-atlas maximum supplies the canonical uniform
Cauchy package. -/
def canonicalSU2AtlasOuterCutoffScoreCauchy
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g (Q'.le_of_lt hg0) atlas)
    (coordinates : List ExponentGramCoordinate) :
    SU2AtlasOuterCutoffScoreCauchy
      G g hg0 atlas family coordinates where
  modulus := fun ε =>
    stochasticAtlasOuterExponentGramDistanceModulus
      G g atlas coordinates ε
  cauchy := by
    intro ε hε first second hfirst hsecond candidate hcandidate
    exact stochasticAtlasOuterExponentGramScore_uniform_abs_sub_le
      G hg0 hg1 atlas hatlas1 family coordinates hε
      hfirst hsecond candidate hcandidate

@[simp] theorem canonicalSU2AtlasOuterCutoffScoreCauchy_modulus
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    (family :
      SU2AtlasOuterPhysicalMarkovFamily
        G g (Q'.le_of_lt hg0) atlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') :
    (canonicalSU2AtlasOuterCutoffScoreCauchy
      G hg0 hg1 atlas hatlas1 family coordinates).modulus ε =
        stochasticAtlasOuterExponentGramDistanceModulus
          G g atlas coordinates ε :=
  rfl

#print axioms SU2AtlasOuterPhysicalMarkovFamily
#print axioms su2AtlasOuterPhysicalMarkovFamilyOfRawKernel
#print axioms stochasticAtlasOuterExponentGramDistanceModulus
#print axioms candidateDistanceModulus_le_atlasModulus
#print axioms stochasticAtlasOuterExponentGramScore
#print axioms stochasticAtlasOuterExponentGramScore_of_mem
#print axioms stochasticAtlasOuterExponentGramScore_uniform_twoSided
#print axioms stochasticAtlasOuterExponentGramScore_uniform_abs_sub_le
#print axioms stochasticAtlasOuterExponentGramReferenceScore
#print axioms stochasticAtlasOuterExponentGramScoreTube
#print axioms stableStochasticAtlasArgminOfOuterTube
#print axioms SU2AtlasOuterCutoffScoreCauchy
#print axioms canonicalSU2AtlasOuterCutoffScoreCauchy
#print axioms canonicalSU2AtlasOuterCutoffScoreCauchy_modulus

end YMGap.Continuum.BF4SU2OuterCutoffAtlasUniformScoreTube
