/-
# Time-placement invariance of the ORIGINAL thermodynamic plaquette law

For every admissible off-center placement, the actual original finite-slab
means become close with the original expression's explicit volume modulus.
Their two already-constructed thermodynamic limits are therefore equal.

This is invariance of the original interacting plaquette-generated law at
w=1/1024 and fixed spacing, on both sides of the reflection plane. It is not
a completed time operator, strict spectral gap or continuum-limit theorem.
-/

import YMGap.Continuum.BF4ExactSlabOffsetSpacetimeDecay
import YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit
import YMGap.Constructive.CRealLimitClose

namespace YMGap.Continuum.BF4ExactSlabSpacetimeTimeInvariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabOffsetSpacetimeDecay
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression (SpacetimeExpression)
open YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit

/-- The ORIGINAL volume modulus; it has no padding or time-offset argument. -/
def comparisonModulus {base : Nat} (e : SpacetimeExpression base) : Q' → Nat := volumeModulus e

theorem difference_error_le (P : Placement) (e : SpacetimeExpression P.half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat) (hm : comparisonModulus e epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (meanSequence (embed P e) margin) (meanSequence e margin))) (ofQ' epsilon) :=
  leEv_trans (existingNome_difference_bound P e margin)
    (leEv_le_ofQ'_of_approx_le (fun _ => coefficient_small e epsilon he margin hm))

/-- The two existing ORIGINAL limits agree; no state-invariance premise is supplied. -/
theorem meanLimit_embed (P : Placement) (e : SpacetimeExpression P.half) :
    Equiv (meanLimit (embed P e)) (meanLimit e) := by
  apply Equiv_of_limit_of_close (meanLimit_converges (embed P e)) (meanLimit_converges e)
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  refine ⟨comparisonModulus e (HalfPow.half*epsilon), fun margin hm => ?_⟩
  obtain ⟨N, hN⟩ := difference_error_le P e (HalfPow.half*epsilon) hh margin hm (HalfPow.half*epsilon) hh
  refine ⟨N, fun n hn => ?_⟩
  have hb : Q'.abs ((meanSequence (embed P e) margin).approx n + -(meanSequence e margin).approx n) ≤ epsilon :=
    Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv (ExpNeg.two_halves epsilon))
  exact ⟨ExpNeg.le_add_of_abs_sub_le hb,
    ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hb)⟩

end YMGap.Continuum.BF4ExactSlabSpacetimeTimeInvariance

#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeTimeInvariance.comparisonModulus
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeTimeInvariance.difference_error_le
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeTimeInvariance.meanLimit_embed
