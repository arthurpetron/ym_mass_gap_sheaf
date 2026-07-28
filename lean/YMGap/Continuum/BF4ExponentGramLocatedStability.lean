/-
# Located stability of the BF4 exponent-Gram matcher

The finite SU(2)/U(1) exponent-Gram discriminator computes an exact argmin on
a supplied positive rational atlas.  Cutoff convergence of the scores alone
does not imply convergence of the chosen argmins: a limiting score may have a
flat minimum.  This module records and proves the exact constructive input
which does suffice.

`LocatedAtlasMinimizer` carries a named limiting minimizer and a strictly
positive rational score margin against every semantically different atlas
candidate.  `AtlasScoreTube` carries a two-sided uniform cutoff error on the
same finite atlas.  If twice the error is smaller than the located margin,
the literal `finiteArgmin` selected from the cutoff score is constructively
equivalent to the limiting minimizer.

The final two-lane certificate applies the theorem simultaneously to the
actual SU(2) and same-carrier U(1) exponent-Gram score functions.  It retains
the limiting SU(2)/U(1) comparison as Type-valued data and returns both
literal finite selections with their exact identifications.

## Honest scope

This is the missing *stability consumer*, not the Yang--Mills estimate which
inhabits it.  In particular this module does not construct:

* the all-label limiting SU(2) or U(1) scores;
* their spacing-dependent score tubes;
* the positive located separator margin near weak coupling; or
* a physical AF trajectory.

Those are analytic inputs and remain explicit fields.  No sign is inferred
from finite data without the located margin.

## Constructive contract

Finite lists and exact `Q'` order only.  No `Classical.*`, `Real`,
`native_decide`, custom axiom, `noncomputable`, or placeholder.
-/

import YMGap.Constructive.CRealExp
import YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator

namespace YMGap.Continuum.BF4ExponentGramLocatedStability

open YMGap.Constructive
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Located minimizers and uniform score tubes -/

/-- A limiting score has a located minimizer on a positive finite atlas when
one named candidate beats every semantically different candidate by an
explicit strictly positive rational margin. -/
structure LocatedAtlasMinimizer
    (atlas : PositiveCouplingAtlas)
    (limitScore : Q' → Q') : Type where
  target : Q'
  target_mem : target ∈ atlas.candidates
  margin : Q'
  margin_pos : (0 : Q') < margin
  separated :
    ∀ candidate : Q',
      candidate ∈ atlas.candidates →
      ¬ candidate ≈ target →
      limitScore target + margin ≤ limitScore candidate

/-- A uniform two-sided approximation tube for one rational score on the
complete finite atlas.  The two inequalities are the order form of
`|cutoffScore-limitScore| ≤ error`; keeping them as data avoids an unnecessary
absolute-value rewrite in downstream physical estimates. -/
structure AtlasScoreTube
    (atlas : PositiveCouplingAtlas)
    (cutoffScore limitScore : Q' → Q')
    (error : Q') : Type where
  error_nonnegative : (0 : Q') ≤ error
  limit_le_cutoff_add :
    ∀ candidate : Q',
      candidate ∈ atlas.candidates →
      limitScore candidate ≤ cutoffScore candidate + error
  cutoff_le_limit_add :
    ∀ candidate : Q',
      candidate ∈ atlas.candidates →
      cutoffScore candidate ≤ limitScore candidate + error

/-- A uniform absolute score error constructs the two-sided score tube used
by the stability theorem. -/
def atlasScoreTubeOfAbs
    (atlas : PositiveCouplingAtlas)
    (cutoffScore limitScore : Q' → Q')
    (error : Q')
    (error_nonnegative : (0 : Q') ≤ error)
    (absolute :
      ∀ candidate : Q',
        candidate ∈ atlas.candidates →
        Q'.abs (cutoffScore candidate + (-limitScore candidate)) ≤
          error) :
    AtlasScoreTube atlas cutoffScore limitScore error where
  error_nonnegative := error_nonnegative
  limit_le_cutoff_add := by
    intro candidate hcandidate
    apply YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Constructive.ExpNeg.abs_sub_comm
          (limitScore candidate) (cutoffScore candidate)))
      (absolute candidate hcandidate)
  cutoff_le_limit_add := by
    intro candidate hcandidate
    exact YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
      (absolute candidate hcandidate)

/-! ## 2. Exact additive cancellation -/

private theorem add_margin_cancel_left
    (base margin : Q') :
    ((base + margin) + (-base)) ≈ margin := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      (base + margin) (margin + base) (-base)
      (Q'.add_comm_eqv base margin)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv margin base (-base)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left margin
      (base + (-base)) 0 (Q'.add_neg_self_eqv base)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' margin)

private theorem add_double_error_cancel_left
    (base error : Q') :
    (((base + error) + error) + (-base)) ≈ error + error := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      ((base + error) + error) (base + (error + error)) (-base)
      (Q'.add_assoc_eqv base error error)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      (base + (error + error)) ((error + error) + base) (-base)
      (Q'.add_comm_eqv base (error + error))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (error + error) base (-base)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (error + error)
      (base + (-base)) 0 (Q'.add_neg_self_eqv base)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (error + error))

/-! ## 3. A located score gap stabilizes the literal finite argmin -/

/-- The finite cutoff argmin is the located limiting minimizer whenever the
two-sided uniform score error is smaller than half of the located margin. -/
theorem finiteArgmin_equiv_located_target
    (atlas : PositiveCouplingAtlas)
    (cutoffScore limitScore : Q' → Q')
    (error : Q')
    (located : LocatedAtlasMinimizer atlas limitScore)
    (tube : AtlasScoreTube atlas cutoffScore limitScore error)
    (error_small : error + error < located.margin) :
    (finiteArgmin cutoffScore atlas.head atlas.tail).choice ≈
      located.target := by
  let selected :=
    (finiteArgmin cutoffScore atlas.head atlas.tail).choice
  have selected_mem : selected ∈ atlas.candidates := by
    exact finiteArgmin_choice_mem
      cutoffScore atlas.head atlas.tail
  by_cases heq : selected ≈ located.target
  · exact heq
  · have hseparated :
        limitScore located.target + located.margin ≤
          limitScore selected :=
      located.separated selected selected_mem heq
    have hselectedTube :
        limitScore selected ≤ cutoffScore selected + error :=
      tube.limit_le_cutoff_add selected selected_mem
    have hminimal :
        cutoffScore selected ≤ cutoffScore located.target := by
      exact finiteArgmin_minimal
        cutoffScore atlas.head atlas.tail
        located.target located.target_mem
    have hminimalError :
        cutoffScore selected + error ≤
          cutoffScore located.target + error :=
      Q'.add_le_add_right
        (cutoffScore selected) (cutoffScore located.target)
        error hminimal
    have htargetTube :
        cutoffScore located.target ≤
          limitScore located.target + error :=
      tube.cutoff_le_limit_add located.target located.target_mem
    have htargetTubeError :
        cutoffScore located.target + error ≤
          (limitScore located.target + error) + error :=
      Q'.add_le_add_right
        (cutoffScore located.target)
        (limitScore located.target + error)
        error htargetTube
    have hmarginChain :
        limitScore located.target + located.margin ≤
          (limitScore located.target + error) + error :=
      Q'.le_trans' _ _ _ hseparated
        (Q'.le_trans' _ _ _ hselectedTube
          (Q'.le_trans' _ _ _ hminimalError htargetTubeError))
    have hshifted :
        (limitScore located.target + located.margin) +
            (-limitScore located.target) ≤
          ((limitScore located.target + error) + error) +
            (-limitScore located.target) :=
      Q'.add_le_add_right
        (limitScore located.target + located.margin)
        ((limitScore located.target + error) + error)
        (-limitScore located.target) hmarginChain
    have hmargin_le_double :
        located.margin ≤ error + error :=
      Q'.le_trans' _ _ _
        (Q'.ge_of_eqv
          (add_margin_cancel_left
            (limitScore located.target) located.margin))
        (Q'.le_trans' _ _ _ hshifted
          (Q'.le_of_eqv
            (add_double_error_cancel_left
              (limitScore located.target) error)))
    exact False.elim ((Int.not_lt_of_ge hmargin_le_double) error_small)

/-- Type-level witness returned by the stability theorem.  It retains the
literal candidate selected by `finiteArgmin`, rather than replacing it by the
limiting target after a propositional equality. -/
structure StableAtlasArgminCertificate
    (atlas : PositiveCouplingAtlas)
    (cutoffScore limitScore : Q' → Q')
    (located : LocatedAtlasMinimizer atlas limitScore) : Type where
  selected : Q'
  selected_mem : selected ∈ atlas.candidates
  selected_equiv_target : selected ≈ located.target

/-- Construct the literal stable argmin certificate. -/
def stableAtlasArgminCertificate
    (atlas : PositiveCouplingAtlas)
    (cutoffScore limitScore : Q' → Q')
    (error : Q')
    (located : LocatedAtlasMinimizer atlas limitScore)
    (tube : AtlasScoreTube atlas cutoffScore limitScore error)
    (error_small : error + error < located.margin) :
    StableAtlasArgminCertificate
      atlas cutoffScore limitScore located where
  selected :=
    (finiteArgmin cutoffScore atlas.head atlas.tail).choice
  selected_mem :=
    finiteArgmin_choice_mem cutoffScore atlas.head atlas.tail
  selected_equiv_target :=
    finiteArgmin_equiv_located_target
      atlas cutoffScore limitScore error located tube error_small

/-! ## 4. Simultaneous SU(2)/U(1) exponent-Gram stability -/

/-- Complete two-lane stability output.  The comparison is deliberately made
between the located limiting targets; the two equivalence fields identify the
literal finite SU(2) and U(1) selections with those targets. -/
structure StableExponentGramComparisonCertificate
    (atlas : PositiveCouplingAtlas)
    (su2CutoffScore su2LimitScore : Q' → Q')
    (u1CutoffScore u1LimitScore : Q' → Q')
    (su2Located : LocatedAtlasMinimizer atlas su2LimitScore)
    (u1Located : LocatedAtlasMinimizer atlas u1LimitScore) : Type where
  su2Selected : Q'
  u1Selected : Q'
  su2Selected_mem : su2Selected ∈ atlas.candidates
  u1Selected_mem : u1Selected ∈ atlas.candidates
  su2Selected_equiv_target : su2Selected ≈ su2Located.target
  u1Selected_equiv_target : u1Selected ≈ u1Located.target
  limitingComparison :
    SU2U1Comparison su2Located.target u1Located.target

/-- Apply located stability to the actual finite SU(2) and same-carrier U(1)
exponent-Gram atlas scores.

The limiting scores, their located minimizers, and the two score tubes are
the honest analytic inputs.  Once supplied, this definition returns both
literal finite matched couplings and their exact limiting identifications. -/
def stablePhysicalExponentGramComparison
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (fineChargeCutoff : Nat)
    (su2LimitScore u1LimitScore : Q' → Q')
    (su2Error u1Error : Q')
    (su2Located : LocatedAtlasMinimizer atlas su2LimitScore)
    (u1Located : LocatedAtlasMinimizer atlas u1LimitScore)
    (su2Tube :
      AtlasScoreTube atlas
        (atlasExponentGramScore G g hg atlas coordinates)
        su2LimitScore su2Error)
    (u1Tube :
      AtlasScoreTube atlas
        (atlasU1ExponentGramScore G g hg atlas
          fineChargeCutoff coordinates)
        u1LimitScore u1Error)
    (su2Error_small : su2Error + su2Error < su2Located.margin)
    (u1Error_small : u1Error + u1Error < u1Located.margin)
    (comparison :
      SU2U1Comparison su2Located.target u1Located.target) :
    StableExponentGramComparisonCertificate
      atlas
      (atlasExponentGramScore G g hg atlas coordinates)
      su2LimitScore
      (atlasU1ExponentGramScore G g hg atlas
        fineChargeCutoff coordinates)
      u1LimitScore su2Located u1Located := by
  let su2Certificate :=
    stableAtlasArgminCertificate
      atlas
      (atlasExponentGramScore G g hg atlas coordinates)
      su2LimitScore su2Error su2Located su2Tube su2Error_small
  let u1Certificate :=
    stableAtlasArgminCertificate
      atlas
      (atlasU1ExponentGramScore G g hg atlas
        fineChargeCutoff coordinates)
      u1LimitScore u1Error u1Located u1Tube u1Error_small
  exact
    { su2Selected := su2Certificate.selected
      u1Selected := u1Certificate.selected
      su2Selected_mem := su2Certificate.selected_mem
      u1Selected_mem := u1Certificate.selected_mem
      su2Selected_equiv_target :=
        su2Certificate.selected_equiv_target
      u1Selected_equiv_target :=
        u1Certificate.selected_equiv_target
      limitingComparison := comparison }

/-- Direct named SU(2) consequence: the physical exponent-Gram matched
coupling is the located minimizer of the supplied limiting score. -/
theorem exponentGramMatchedCoupling_equiv_located_target
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (limitScore : Q' → Q')
    (error : Q')
    (located : LocatedAtlasMinimizer atlas limitScore)
    (tube :
      AtlasScoreTube atlas
        (atlasExponentGramScore G g hg atlas coordinates)
        limitScore error)
    (error_small : error + error < located.margin) :
    exponentGramMatchedCoupling G g hg atlas coordinates ≈
      located.target := by
  exact finiteArgmin_equiv_located_target
    atlas
    (atlasExponentGramScore G g hg atlas coordinates)
    limitScore error located tube error_small

/-- Direct named U(1) consequence: the same-carrier U(1) matched coupling is
the located minimizer of the supplied limiting score. -/
theorem u1ExponentGramMatchedCoupling_equiv_located_target
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (limitScore : Q' → Q')
    (error : Q')
    (located : LocatedAtlasMinimizer atlas limitScore)
    (tube :
      AtlasScoreTube atlas
        (atlasU1ExponentGramScore G g hg atlas
          fineChargeCutoff coordinates)
        limitScore error)
    (error_small : error + error < located.margin) :
    u1ExponentGramMatchedCoupling G g hg atlas
        fineChargeCutoff coordinates ≈
      located.target := by
  exact finiteArgmin_equiv_located_target
    atlas
    (atlasU1ExponentGramScore G g hg atlas
      fineChargeCutoff coordinates)
    limitScore error located tube error_small

/-- The exact finite SU(2)/U(1) comparison branch stabilizes to the supplied
located limiting branch.  This is stronger than merely returning two
convergent values: strict `below`/`above` branches remain strict, and an
equivalent limiting branch remains equivalent. -/
def stablePhysicalExponentGramComparisonAtCutoff
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (fineChargeCutoff : Nat)
    (su2LimitScore u1LimitScore : Q' → Q')
    (su2Error u1Error : Q')
    (su2Located : LocatedAtlasMinimizer atlas su2LimitScore)
    (u1Located : LocatedAtlasMinimizer atlas u1LimitScore)
    (su2Tube :
      AtlasScoreTube atlas
        (atlasExponentGramScore G g hg atlas coordinates)
        su2LimitScore su2Error)
    (u1Tube :
      AtlasScoreTube atlas
        (atlasU1ExponentGramScore G g hg atlas
          fineChargeCutoff coordinates)
        u1LimitScore u1Error)
    (su2Error_small : su2Error + su2Error < su2Located.margin)
    (u1Error_small : u1Error + u1Error < u1Located.margin)
    (comparison :
      SU2U1Comparison su2Located.target u1Located.target) :
    SU2U1Comparison
      (exponentGramMatchedCoupling G g hg atlas coordinates)
      (u1ExponentGramMatchedCoupling G g hg atlas
        fineChargeCutoff coordinates) := by
  have hsu2 :
      exponentGramMatchedCoupling G g hg atlas coordinates ≈
        su2Located.target :=
    exponentGramMatchedCoupling_equiv_located_target
      G g hg atlas coordinates su2LimitScore su2Error
      su2Located su2Tube su2Error_small
  have hu1 :
      u1ExponentGramMatchedCoupling G g hg atlas
          fineChargeCutoff coordinates ≈
        u1Located.target :=
    u1ExponentGramMatchedCoupling_equiv_located_target
      G g hg atlas fineChargeCutoff coordinates
      u1LimitScore u1Error u1Located u1Tube u1Error_small
  cases comparison with
  | su2Below hbelow =>
      exact SU2U1Comparison.su2Below
        (YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
          (Q'.lt_of_le_of_lt (Q'.le_of_eqv hsu2) hbelow)
          (Q'.ge_of_eqv hu1))
  | matched hmatched =>
      exact SU2U1Comparison.matched
        (Q'.eqv_trans _ _ _
          hsu2
          (Q'.eqv_trans _ _ _
            hmatched (Q'.eqv_symm hu1)))
  | su2Above habove =>
      exact SU2U1Comparison.su2Above
        (YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
          (Q'.lt_of_le_of_lt (Q'.le_of_eqv hu1) habove)
          (Q'.ge_of_eqv hsu2))

end YMGap.Continuum.BF4ExponentGramLocatedStability

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4ExponentGramLocatedStability.finiteArgmin_equiv_located_target
#print axioms YMGap.Continuum.BF4ExponentGramLocatedStability.atlasScoreTubeOfAbs
#print axioms YMGap.Continuum.BF4ExponentGramLocatedStability.stableAtlasArgminCertificate
#print axioms YMGap.Continuum.BF4ExponentGramLocatedStability.stablePhysicalExponentGramComparison
#print axioms YMGap.Continuum.BF4ExponentGramLocatedStability.exponentGramMatchedCoupling_equiv_located_target
#print axioms YMGap.Continuum.BF4ExponentGramLocatedStability.u1ExponentGramMatchedCoupling_equiv_located_target
#print axioms YMGap.Continuum.BF4ExponentGramLocatedStability.stablePhysicalExponentGramComparisonAtCutoff
