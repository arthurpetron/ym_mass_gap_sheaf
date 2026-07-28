/-
# Atlas-uniform outer-cutoff tube for the BF4 U(1) exponent-Gram score

At fixed rational nome, fixed corrected-slab geometry, and fixed finite
exponent-coordinate list, the outer-cutoff score estimate is pointwise in a
candidate coarse coupling.  This module pays all candidate-dependent coarse
thresholds at once by taking a constructive maximum over the finite positive
coupling atlas.

For tolerance `ε`, let

* `δ = ε / (2 * (coordinates.length + 1))`;
* the fine threshold be the normalized-event tensor cutoff at nome `g`;
* each coarse threshold be the corresponding tensor cutoff at that candidate;
* the common retained cutoff be the maximum of the fine threshold and the
  finite list of coarse thresholds.

The common cutoff deliberately overpays the induced coarse requirement:
every candidate threshold is at most `K`, hence at most `4K`.  Assuming every
atlas candidate also lies below one, the already-proved fixed-candidate score
transport therefore holds simultaneously for every atlas member and every
pair of later outer cutoffs.

The final certificate is Type-level Cauchy-tube data.  It does not construct
a rational or constructive-real limiting score, vary the nome, or take a
spacing, volume, or continuum limit.

## Axiom gate

Finite lists, `Nat.max`, and exact `Q'` arithmetic only.  No `Classical.*`,
`Real`, `native_decide`, `sorry`, custom axiom, choice, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4U1OuterCutoffBlockGramTransport

namespace YMGap.Continuum.BF4U1OuterCutoffAtlasUniformScoreTube

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
open YMGap.Continuum.BF4U1ActualExponentGramScoreTube
open YMGap.Continuum.BF4U1FiniteExponentGramTailTube
open YMGap.Continuum.BF4U1OuterCutoffBlockGramTransport
open YMGap.Continuum.BF4U1OuterCutoffTensorTailModulus
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Constructive finite-atlas maximum -/

/-- Candidate-dependent coarse tensor thresholds, one for every entry of the
finite atlas.  No positivity proof is needed to compute this list; positivity
and the strict upper bound are consumed only by the certified estimate. -/
def atlasCoarseOuterTensorCutoffs
    (G : CutoffOneGeometry)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : List Nat :=
  atlas.candidates.map (fun candidate =>
    signedChargeTensorTailCutoff candidate
      (twoEntryCoordinateTolerance coordinates ε)
      (slabPhysicalFaceEdges
        (centralExtent G.coarseHalf)).length)

/-- The maximum of all candidate-dependent coarse tensor thresholds. -/
def atlasCoarseOuterTensorCutoff
    (G : CutoffOneGeometry)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : Nat :=
  listNatMax
    (atlasCoarseOuterTensorCutoffs
      G atlas coordinates ε)

/-- One executable outer cutoff paying both the fixed fine threshold and
every candidate-dependent coarse threshold. -/
def atlasU1ExponentGramOuterCutoff
    (G : CutoffOneGeometry)
    (g : Q')
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : Nat :=
  max
    (signedChargeTensorTailCutoff g
      (twoEntryCoordinateTolerance coordinates ε)
      (slabPhysicalFaceEdges
        (centralExtent G.fineHalf)).length)
    (atlasCoarseOuterTensorCutoff
      G atlas coordinates ε)

theorem fineOuterTensorCutoff_le_atlasCutoff
    (G : CutoffOneGeometry)
    (g : Q')
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') :
    signedChargeTensorTailCutoff g
        (twoEntryCoordinateTolerance coordinates ε)
        (slabPhysicalFaceEdges
          (centralExtent G.fineHalf)).length ≤
      atlasU1ExponentGramOuterCutoff
        G g atlas coordinates ε :=
  Nat.le_max_left _ _

theorem candidateCoarseOuterTensorCutoff_le_atlasCutoff
    (G : CutoffOneGeometry)
    (g : Q')
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q')
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    signedChargeTensorTailCutoff candidate
        (twoEntryCoordinateTolerance coordinates ε)
        (slabPhysicalFaceEdges
          (centralExtent G.coarseHalf)).length ≤
      atlasU1ExponentGramOuterCutoff
        G g atlas coordinates ε := by
  have hmember :
      signedChargeTensorTailCutoff candidate
          (twoEntryCoordinateTolerance coordinates ε)
          (slabPhysicalFaceEdges
            (centralExtent G.coarseHalf)).length ∈
        atlasCoarseOuterTensorCutoffs
          G atlas coordinates ε := by
    unfold atlasCoarseOuterTensorCutoffs
    exact List.mem_map.mpr
      ⟨candidate, hcandidate, rfl⟩
  exact Nat.le_trans
    (le_listNatMax_of_mem hmember)
    (Nat.le_max_right _ _)

/-! ## 2. One cutoff for every atlas score -/

/-- Every two outer-cutoff scores past the common atlas cutoff are
`ε`-close, uniformly over all atlas members.  The atlas-wide strict subunit
hypothesis is explicit because `PositiveCouplingAtlas` itself stores only
strict positivity. -/
theorem atlasU1ExponentGramScore_uniform_outerCutoff_abs_le
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    (coordinates : List ExponentGramCoordinate)
    {K L : Nat}
    (hretained :
      atlasU1ExponentGramOuterCutoff
          G g atlas coordinates ε ≤ K)
    (hKL : K ≤ L)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    Q'.abs
        (atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas L
              coordinates candidate +
          -atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas K
              coordinates candidate) ≤
      ε := by
  have hFine :
      signedChargeTensorTailCutoff g
          (twoEntryCoordinateTolerance coordinates ε)
          (slabPhysicalFaceEdges
            (centralExtent G.fineHalf)).length ≤
        K :=
    Nat.le_trans
      (fineOuterTensorCutoff_le_atlasCutoff
        G g atlas coordinates ε)
      hretained
  have hCoarseAtK :
      signedChargeTensorTailCutoff candidate
          (twoEntryCoordinateTolerance coordinates ε)
          (slabPhysicalFaceEdges
            (centralExtent G.coarseHalf)).length ≤
        K :=
    Nat.le_trans
      (candidateCoarseOuterTensorCutoff_le_atlasCutoff
        G g atlas coordinates ε candidate hcandidate)
      hretained
  have hCoarse :
      signedChargeTensorTailCutoff candidate
          (twoEntryCoordinateTolerance coordinates ε)
          (slabPhysicalFaceEdges
            (centralExtent G.coarseHalf)).length ≤
        4 * K :=
    Nat.le_trans hCoarseAtK (by omega)
  exact
    atlasU1ExponentGramScore_outerCutoff_abs_le_of_cutoffs
      G hg0 hg1 atlas candidate hcandidate
      (hatlas1 candidate hcandidate)
      hε hKL coordinates hFine hCoarse

/-- Base-versus-later form: the executable common cutoff itself works for
every atlas candidate and every later outer cutoff. -/
theorem atlasU1ExponentGramScore_from_uniformCutoff_abs_le
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    (coordinates : List ExponentGramCoordinate)
    {L : Nat}
    (hL :
      atlasU1ExponentGramOuterCutoff
          G g atlas coordinates ε ≤ L)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    Q'.abs
        (atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas L
              coordinates candidate +
          -atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas
              (atlasU1ExponentGramOuterCutoff
                G g atlas coordinates ε)
              coordinates candidate) ≤
      ε :=
  atlasU1ExponentGramScore_uniform_outerCutoff_abs_le
    G hg0 hg1 atlas hatlas1 hε coordinates
    (Nat.le_refl _) hL candidate hcandidate

/-! The ordered estimate gives the usual all-pairs Cauchy form by decidable
totality of the natural cutoff order and symmetry of rational absolute
difference. -/

/-- Every pair of cutoffs past the common threshold is `ε`-close for every
atlas member; no ordering between the pair is required. -/
theorem atlasU1ExponentGramScore_uniform_cauchy_abs_le
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    (coordinates : List ExponentGramCoordinate)
    {K L : Nat}
    (hK :
      atlasU1ExponentGramOuterCutoff
          G g atlas coordinates ε ≤ K)
    (hL :
      atlasU1ExponentGramOuterCutoff
          G g atlas coordinates ε ≤ L)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    Q'.abs
        (atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas L
              coordinates candidate +
          -atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas K
              coordinates candidate) ≤
      ε := by
  rcases Nat.le_total K L with hKL | hLK
  · exact
      atlasU1ExponentGramScore_uniform_outerCutoff_abs_le
        G hg0 hg1 atlas hatlas1 hε coordinates
        hK hKL candidate hcandidate
  · have hreverse :=
      atlasU1ExponentGramScore_uniform_outerCutoff_abs_le
        G hg0 hg1 atlas hatlas1 hε coordinates
        hL hLK candidate hcandidate
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Constructive.ExpNeg.abs_sub_comm
          (atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas L
              coordinates candidate)
          (atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas K
              coordinates candidate)))
      hreverse

/-! ## 3. Type-level uniform Cauchy tube -/

/-- Constructive Cauchy-tube data for the complete finite atlas.  It records
one retained outer cutoff and a simultaneous score estimate for all atlas
members and all ordered pairs of later cutoffs.  No limiting score is a field
of this structure. -/
structure U1AtlasOuterCutoffScoreTube
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : Type where
  retainedCutoff : Nat
  score_cauchy :
    ∀ {K L : Nat},
      retainedCutoff ≤ K →
      retainedCutoff ≤ L →
      ∀ candidate,
        candidate ∈ atlas.candidates →
          Q'.abs
              (atlasU1ExponentGramScore
                  G g (Q'.le_of_lt hg0) atlas L
                    coordinates candidate +
                -atlasU1ExponentGramScore
                  G g (Q'.le_of_lt hg0) atlas K
                    coordinates candidate) ≤
            ε

/-- Canonical Type-level uniform tube whose retained cutoff is the executable
finite-atlas maximum defined above. -/
def canonicalU1AtlasOuterCutoffScoreTube
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate)
    {ε : Q'} (hε : (0 : Q') < ε) :
    U1AtlasOuterCutoffScoreTube
      G g hg0 atlas coordinates ε where
  retainedCutoff :=
    atlasU1ExponentGramOuterCutoff
      G g atlas coordinates ε
  score_cauchy := by
    intro K L hK hL candidate hcandidate
    exact
      atlasU1ExponentGramScore_uniform_cauchy_abs_le
        G hg0 hg1 atlas hatlas1 hε coordinates
        hK hL candidate hcandidate

@[simp] theorem canonicalU1AtlasOuterCutoffScoreTube_retainedCutoff
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate)
    {ε : Q'} (hε : (0 : Q') < ε) :
    (canonicalU1AtlasOuterCutoffScoreTube
      G hg0 hg1 atlas hatlas1 coordinates hε).retainedCutoff =
        atlasU1ExponentGramOuterCutoff
          G g atlas coordinates ε :=
  rfl

/-! ## 4. A full Type-level modulus package -/

/-- Uniform Cauchy data for the atlas-indexed rational score family.  The
modulus is executable and the estimate is simultaneous in every atlas
member.  This is only a Cauchy statement; it carries no selected limit. -/
structure U1AtlasOuterCutoffScoreCauchy
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate) : Type where
  modulus : Q' → Nat
  cauchy :
    ∀ ε : Q',
      (0 : Q') < ε →
      ∀ {K L : Nat},
        modulus ε ≤ K →
        modulus ε ≤ L →
        ∀ candidate,
          candidate ∈ atlas.candidates →
            Q'.abs
                (atlasU1ExponentGramScore
                    G g (Q'.le_of_lt hg0) atlas L
                      coordinates candidate +
                  -atlasU1ExponentGramScore
                    G g (Q'.le_of_lt hg0) atlas K
                      coordinates candidate) ≤
              ε

/-- The executable finite-atlas maximum is a full uniform Cauchy modulus for
the rational score family at fixed nome and geometry. -/
def canonicalU1AtlasOuterCutoffScoreCauchy
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate) :
    U1AtlasOuterCutoffScoreCauchy
      G g hg0 atlas coordinates where
  modulus := fun ε =>
    atlasU1ExponentGramOuterCutoff
      G g atlas coordinates ε
  cauchy := by
    intro ε hε K L hK hL candidate hcandidate
    exact
      atlasU1ExponentGramScore_uniform_cauchy_abs_le
        G hg0 hg1 atlas hatlas1 hε coordinates
        hK hL candidate hcandidate

@[simp] theorem canonicalU1AtlasOuterCutoffScoreCauchy_modulus
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate,
        candidate ∈ atlas.candidates →
          candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') :
    (canonicalU1AtlasOuterCutoffScoreCauchy
      G hg0 hg1 atlas hatlas1 coordinates).modulus ε =
        atlasU1ExponentGramOuterCutoff
          G g atlas coordinates ε :=
  rfl

#print axioms atlasCoarseOuterTensorCutoff
#print axioms atlasU1ExponentGramOuterCutoff
#print axioms candidateCoarseOuterTensorCutoff_le_atlasCutoff
#print axioms atlasU1ExponentGramScore_uniform_outerCutoff_abs_le
#print axioms atlasU1ExponentGramScore_from_uniformCutoff_abs_le
#print axioms atlasU1ExponentGramScore_uniform_cauchy_abs_le
#print axioms canonicalU1AtlasOuterCutoffScoreTube
#print axioms canonicalU1AtlasOuterCutoffScoreTube_retainedCutoff
#print axioms canonicalU1AtlasOuterCutoffScoreCauchy
#print axioms canonicalU1AtlasOuterCutoffScoreCauchy_modulus

end YMGap.Continuum.BF4U1OuterCutoffAtlasUniformScoreTube
