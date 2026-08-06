/-
Track 11.7-fusion / R2x -- polynomial envelope for the endpoint Lipschitz term.

The endpoint criterion replaces a fusion-quotient comparison by the explicit
continuity error `vacLip(N_k) * u_k`.  This file proves a coarse but uniform
degree-eight polynomial ceiling for `vacLip`.  It uses only termwise finite-sum
monotonicity, `C4(s)+1=(s+1)^2`, and character-dimension bounds.

Keeping the ceiling factored avoids a large polynomial normal form.  Its
growth is visibly eight factors of `N+1`, while `u_k=(1/12)2^-k`; a subsequent
geometric-versus-polynomial induction can therefore close the terminal tail
without evaluating growing fusion sums.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2DyadicFusionEndpointCriterion
import YMGap.Continuum.AbelianFusionCLT
import YMGap.Continuum.CumulativeBulkShift
import YMGap.Continuum.RenormalizedContinuumZ1
import YMGap.Continuum.AllWindowCorrDirichlet

namespace YMGap.Continuum.P2DyadicVacLipPolynomial

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CumulativeBulkShift
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.P2DyadicFusionEndpointCriterion
open YMGap.Continuum.P2DyadicFusionGapEnvelope
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RenormalizedContinuumZ1
open YMGap.Continuum.RGTransport

/-- `N+1`, embedded in the constructive rationals. -/
def cutoffScale (N : Nat) : Q' := Q'.ofNat (N + 1)

/-- Uniform ceiling for one dimension-dimension-Casimir pair. -/
def pairCeil (N : Nat) : Q' :=
  (cutoffScale N * cutoffScale N) *
    Q'.ofNat (2 * ((N + 1) * (N + 1)))

/-- Ceiling for either derivative sum. -/
def lipCeil (N : Nat) : Q' := cutoffScale N * pairCeil N

/-- Ceiling for either endpoint character mass. -/
def massCeil (N : Nat) : Q' :=
  cutoffScale N * (cutoffScale N * cutoffScale N)

/-- Factored degree-eight envelope `2 * lipCeil * massCeil`. -/
def vacLipPolynomialCeil (N : Nat) : Q' :=
  lipCeil N * massCeil N + massCeil N * lipCeil N

theorem cutoffScale_nonneg (N : Nat) : (0 : Q') <= cutoffScale N :=
  ExpNeg.ofNat_nonneg' _

theorem pairCeil_nonneg (N : Nat) : (0 : Q') <= pairCeil N := by
  unfold pairCeil
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (cutoffScale_nonneg N) (cutoffScale_nonneg N))
    (ExpNeg.ofNat_nonneg' _)

theorem lipCeil_nonneg (N : Nat) : (0 : Q') <= lipCeil N :=
  Q'.mul_nonneg _ _ (cutoffScale_nonneg N) (pairCeil_nonneg N)

theorem massCeil_nonneg (N : Nat) : (0 : Q') <= massCeil N := by
  unfold massCeil
  exact Q'.mul_nonneg _ _ (cutoffScale_nonneg N)
    (Q'.mul_nonneg _ _ (cutoffScale_nonneg N) (cutoffScale_nonneg N))

/-- `C4(a)` lies below the square of any enclosing character dimension. -/
theorem c4_le_scaleSq {a N : Nat} (ha : a + 1 <= N + 1) :
    c4 a <= (N + 1) * (N + 1) := by
  have hsquare := Nat.mul_le_mul ha ha
  have hid := AbelianFusionCLT.c4_succ_eq_sq a
  omega

theorem dimQ_le_cutoffScale {a N : Nat} (ha : a + 1 <= N + 1) :
    dimQ a <= cutoffScale N := by
  unfold dimQ cutoffScale
  exact Q'.ofNat_le_ofNat ha

/-- Every pair-Lipschitz summand in an enclosing cutoff box is below the
uniform pair ceiling. -/
theorem pairLip_le_pairCeil {a b N : Nat}
    (ha : a + 1 <= N + 1) (hb : b + 1 <= N + 1) :
    pairLip a b <= pairCeil N := by
  have hdim := Q'.mul_le_mul_of_nonneg
    (dimQ_le_cutoffScale ha) (dimQ_le_cutoffScale hb)
    (cutoffScale_nonneg N) (dimQ_nonneg b)
  have hca := c4_le_scaleSq ha
  have hcb := c4_le_scaleSq hb
  have hcasNat :
      c4 a + c4 b <= 2 * ((N + 1) * (N + 1)) := by omega
  have hcas :
      Q'.ofNat (c4 a + c4 b) <=
        Q'.ofNat (2 * ((N + 1) * (N + 1))) :=
    Q'.ofNat_le_ofNat hcasNat
  unfold pairLip pairCeil
  exact Q'.mul_le_mul_of_nonneg hdim hcas
    (Q'.mul_nonneg _ _ (cutoffScale_nonneg N) (cutoffScale_nonneg N))
    (ExpNeg.ofNat_nonneg' (c4 a + c4 b))

/-- The adjacent derivative sum has at most `N+1` terms of size
`pairCeil N`. -/
theorem adjLip_le_lipCeil (N : Nat) : adjLip N <= lipCeil N := by
  have hsum : adjLip N <= Q'.ofNat N * pairCeil N := by
    unfold adjLip
    apply fsum_le_const
    intro i hi
    apply pairLip_le_pairCeil
    · omega
    · omega
  have hcount : Q'.ofNat N <= cutoffScale N := by
    unfold cutoffScale
    exact Q'.ofNat_le_ofNat (by omega)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hcount (pairCeil_nonneg N))

/-- The diagonal derivative sum has exactly `N+1` terms of the same size. -/
theorem diagLip_le_lipCeil (N : Nat) : diagLip N <= lipCeil N := by
  unfold diagLip lipCeil cutoffScale
  apply fsum_le_const
  intro i hi
  apply pairLip_le_pairCeil
  · omega
  · omega

/-- The endpoint diagonal character mass is at most `(N+1)^3`. -/
theorem coordNormSq_endpoint_le_massCeil (N : Nat) :
    coordNormSq (1 : Q') N <= massCeil N := by
  have hsum : coordNormSq (1 : Q') N <=
      Q'.ofNat (N + 1) * (cutoffScale N * cutoffScale N) := by
    unfold coordNormSq
    apply fsum_le_const
    intro i hi
    have hiScale : i + 1 <= N + 1 := by omega
    have heq : (coeffW (1 : Q') i * coeffW (1 : Q') i).eqv
        (dimQ i * dimQ i) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (coeffW (1 : Q') i)
          (coeffW_at_one_eqv i))
        (Q'.mul_eqv_congr_left (dimQ i) _ _ (coeffW_at_one_eqv i))
    have hdim := Q'.mul_le_mul_of_nonneg
      (dimQ_le_cutoffScale hiScale) (dimQ_le_cutoffScale hiScale)
      (cutoffScale_nonneg N) (dimQ_nonneg i)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hdim
  simpa only [massCeil, cutoffScale] using hsum

/-- The adjacent endpoint mass is no larger than the diagonal mass, hence
inherits the same polynomial ceiling. -/
theorem adjCorr_endpoint_le_massCeil (N : Nat) :
    adjCorr (1 : Q') N <= massCeil N :=
  Q'.le_trans' _ _ _ (adjCorr_le_coordNormSq (1 : Q') N)
    (coordNormSq_endpoint_le_massCeil N)

/-- Uniform factored degree-eight bound for the finite-character continuity
constant. -/
theorem vacLip_le_polynomialCeil (N : Nat) :
    vacLip N <= vacLipPolynomialCeil N := by
  unfold vacLip vacLipPolynomialCeil
  exact Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg (adjLip_le_lipCeil N)
      (coordNormSq_endpoint_le_massCeil N)
      (lipCeil_nonneg N) (coordNormSq_nonneg (by decide) N))
    (Q'.mul_le_mul_of_nonneg (adjCorr_endpoint_le_massCeil N)
      (diagLip_le_lipCeil N)
      (massCeil_nonneg N) (diagLip_nonneg N))

/-- Therefore each dyadic endpoint error is bounded by a degree-eight
polynomial times the geometric heat-time margin. -/
theorem dyadicEndpointError_le_polynomial (k : Nat) :
    dyadicEndpointError k <=
      vacLipPolynomialCeil (Ncut k) * dyadicMargin k :=
  Q'.mul_le_mul_of_nonneg_right _ _ _
    (vacLip_le_polynomialCeil (Ncut k)) (dyadicMargin_nonneg k)

end YMGap.Continuum.P2DyadicVacLipPolynomial

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2DyadicVacLipPolynomial.pairLip_le_pairCeil
#print axioms YMGap.Continuum.P2DyadicVacLipPolynomial.adjLip_le_lipCeil
#print axioms YMGap.Continuum.P2DyadicVacLipPolynomial.diagLip_le_lipCeil
#print axioms YMGap.Continuum.P2DyadicVacLipPolynomial.coordNormSq_endpoint_le_massCeil
#print axioms YMGap.Continuum.P2DyadicVacLipPolynomial.vacLip_le_polynomialCeil
#print axioms YMGap.Continuum.P2DyadicVacLipPolynomial.dyadicEndpointError_le_polynomial
