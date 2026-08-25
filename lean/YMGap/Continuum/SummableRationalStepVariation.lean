/-
# Rational step budgets compile to constructive-real cutoff limits

Many physical cutoff streams in this development are literally rational but
are consumed by the common `CReal` convergence machinery.  For such a stream,
the inner approximation modulus is definitionally zero.  The only genuine
analytic inputs are therefore:

* a nonnegative rational one-step variation;
* an antitone summable-tail control for that variation; and
* two-sided rational inequalities between consecutive stream values.

This file packages exactly those data and compiles them into
`SummableCRealStepVariation` for the canonical `CReal.ofQ'` embedding.  It also
constructs the complete limit and proves convergence.  A pointwise-constant
up-to-`Q'.eqv` stream receives the zero variation certificate automatically.

No physical variation estimate is proved here.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Constructive.CRealInnerRegularity
import YMGap.Continuum.SummableCRealStepVariation

namespace YMGap.Continuum.SummableRationalStepVariation

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SummableCRealStepVariation

local infix:50 " ≈ " => Q'.eqv

/-- Minimal rational local data sufficient for constructive-real cutoff
removal of the canonical embedding `j ↦ ofQ' (stream j)`. -/
structure SummableRationalStepVariation
    (stream : Nat -> Q') : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall j, (0 : Q') <= variation j
  tailControl : AntitoneTailControl variation
  stepBound : forall j,
    stream (j + 1) <= stream j + variation j /\
    stream j <= stream (j + 1) + variation j

namespace SummableRationalStepVariation

/-- The canonical rational embedding has zero inner approximation cost, so a
rational step budget compiles directly to the common constructive-real
variation interface. -/
def toSummableCRealStepVariation
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream) :
    SummableCRealStepVariation
      (fun scale => CReal.ofQ' (stream scale)) where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailRate := data.tailControl.tailRate
  tailRate_antitone := data.tailControl.tailRate_antitone
  tailBound := data.tailControl.tailBound
  innerRate := fun _ _ => 0
  innerRegular := by
    intro scale epsilon hepsilon p q hp hq
    exact (CReal.InnerRegularity.ofQ' (stream scale)).regular
      epsilon hepsilon p q hp hq
  stepBound := by
    intro scale k
    simpa only [CReal.ofQ'_approx] using data.stepBound scale

/-- The modulus-Cauchy datum constructed from the rational local budget. -/
def toModCauchyEv
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream) :
    CReal.ModCauchyEv (fun scale => CReal.ofQ' (stream scale)) :=
  data.toSummableCRealStepVariation.toModCauchyEv

/-- The constructive-real cutoff limit selected by the rational variation
data. -/
def limit
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream) : CReal :=
  CReal.completeLimitCauchy
    (fun scale => CReal.ofQ' (stream scale)) data.toModCauchyEv

/-- The canonical rational stream converges to the limit constructed from its
summable step budget. -/
theorem converges
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ' (stream scale)) data.limit :=
  CReal.convergesTo_completeLimitCauchy
    (fun scale => CReal.ofQ' (stream scale)) data.toModCauchyEv

/-! ## An automatic eventual ceiling -/

/-- A canonical tail start, obtained by asking the summable variation budget
to make every later finite variation sum at most one. -/
def tailCeilingStart
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream) : Nat :=
  data.tailControl.tailRate 1

/-- The stream value at the canonical tail start plus one.  Summable
two-sided step variation forces this rational to bound the entire tail. -/
def tailCeiling
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream) : Q' :=
  stream data.tailCeilingStart + 1

/-- Every rational stream with summable two-sided step variation is
eventually bounded above by an explicit rational. -/
theorem le_tailCeiling
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    {scale : Nat} (hscale : data.tailCeilingStart <= scale) :
    stream scale <= data.tailCeiling := by
  obtain ⟨length, rfl⟩ := Nat.exists_eq_add_of_le hscale
  have htelescope :=
    data.toSummableCRealStepVariation.telescope_up
      0 data.tailCeilingStart length
  simp only [CReal.ofQ'_approx] at htelescope
  have htail :
      finSum
          (fun offset => data.variation
            (data.tailCeilingStart + offset)) length <= (1 : Q') := by
    exact data.tailControl.tailBound 1 (by decide)
      data.tailCeilingStart (by
        unfold tailCeilingStart
        exact Nat.le_refl _) length
  exact Q'.le_trans' _ _ _ htelescope
    (Q'.add_le_add_left _ _ _ htail)

/-! ## An automatic global ceiling -/

/-- A global ceiling obtained without a separate boundedness hypothesis.
The finite prefix is paid by its explicitly computed variation sum, and the
tail contributes the unit budget already built into `tailCeilingStart`. -/
def globalCeiling
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream) : Q' :=
  1 +
    (stream 0 +
      finSum data.variation data.tailCeilingStart)

/-- For a nonnegative stream, the automatic global ceiling is strictly
positive and may therefore be used to scale summable tail controls. -/
theorem globalCeiling_pos
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (stream_nonnegative : forall scale, (0 : Q') <= stream scale) :
    (0 : Q') < data.globalCeiling := by
  have sum_nonnegative : (0 : Q') <=
      finSum data.variation data.tailCeilingStart := by
    simpa only [finSum_zero] using
      finSum_monotone_of_nonneg
        data.variation data.variation_nonnegative
        0 data.tailCeilingStart (Nat.zero_le _)
  let remainder :=
    stream 0 + finSum data.variation data.tailCeilingStart
  have remainder_nonnegative : (0 : Q') <= remainder :=
    Q'.zero_le_add _ _ (stream_nonnegative 0) sum_nonnegative
  change (0 : Q') < 1 + remainder
  show (0 : Int) * (((1 : Q') + remainder).den : Int) <
    ((1 : Q') + remainder).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) <
    (1 : Q').num * (remainder.den : Int) +
      remainder.num * ((1 : Q').den : Int)
  have first_pos : (0 : Int) <
      (1 : Q').num * (remainder.den : Int) :=
    Int.mul_pos (by decide) (by exact_mod_cast remainder.den_pos)
  have second_nonnegative : (0 : Int) <=
      remainder.num * ((1 : Q').den : Int) :=
    Int.mul_nonneg
      ((Q'.zero_le_iff_num_nonneg remainder).mp remainder_nonnegative)
      (by exact_mod_cast Nat.zero_le (1 : Q').den)
  omega

/-- Every scale lies below the automatic global ceiling.  Below the
canonical tail start, rational telescoping is bounded by the computed finite
variation prefix.  At and above it, the existing unit tail ceiling applies. -/
theorem le_globalCeiling
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (scale : Nat) :
    stream scale <= data.globalCeiling := by
  let start := data.tailCeilingStart
  let prefixVariation := finSum data.variation start
  let prefixTop := stream 0 + prefixVariation
  have start_telescope : stream start <= prefixTop := by
    have bound :=
      data.toSummableCRealStepVariation.telescope_up 0 0 start
    simpa only [CReal.ofQ'_approx, Nat.zero_add] using bound
  rcases Nat.lt_or_ge scale start with before | after
  · have scale_telescope :
        stream scale <= stream 0 + finSum data.variation scale := by
      have bound :=
        data.toSummableCRealStepVariation.telescope_up 0 0 scale
      simpa only [CReal.ofQ'_approx, Nat.zero_add] using bound
    have variation_le :
        finSum data.variation scale <= prefixVariation := by
      exact finSum_monotone_of_nonneg
        data.variation data.variation_nonnegative
        scale start (Nat.le_of_lt before)
    have scale_le_prefixTop : stream scale <= prefixTop :=
      Q'.le_trans' _ _ _ scale_telescope
        (Q'.add_le_add_left _ _ _ variation_le)
    exact Q'.le_trans' _ _ _ scale_le_prefixTop
      (Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg prefixTop 1 (by decide))
        (Q'.le_of_eqv (Q'.add_comm_eqv prefixTop 1)))
  · have tail_bound : stream scale <= stream start + 1 := by
      change stream scale <= stream data.tailCeilingStart + 1
      exact data.le_tailCeiling after
    have tail_le_prefixTop : stream start + 1 <= prefixTop + 1 :=
      Q'.add_le_add_right _ _ _ start_telescope
    exact Q'.le_trans' _ _ _ tail_bound
      (Q'.le_trans' _ _ _ tail_le_prefixTop
        (Q'.le_of_eqv (Q'.add_comm_eqv prefixTop 1)))

/-- If one positive budget controls the entire variation tail from zero, then
initial slack plus that budget gives a pointwise global ceiling.  This is the
direct compiler used when a normalized analytic debt must stay below one at
every cutoff, rather than merely converge. -/
theorem le_of_initial_add_totalBudget_le
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    {budget ceiling : Q'}
    (hbudget : (0 : Q') < budget)
    (hfromZero : data.tailControl.tailRate budget = 0)
    (hclose : stream 0 + budget <= ceiling)
    (scale : Nat) :
    stream scale <= ceiling := by
  have htelescope :=
    data.toSummableCRealStepVariation.telescope_up 0 0 scale
  simp only [CReal.ofQ'_approx, Nat.zero_add] at htelescope
  have htail :
      finSum (fun offset => data.variation offset) scale <= budget := by
    simpa only [Nat.zero_add] using
      data.tailControl.tailBound budget hbudget 0 (by
        rw [hfromZero]
        exact Nat.le_refl 0) scale
  exact Q'.le_trans' _ _ _ htelescope
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_left _ _ _ htail)
      hclose)

/-- A rational stream pointwise equivalent to one constant has the zero
variation certificate.  This uses setoid equality rather than requiring the
chosen rational representations to be definitionally identical. -/
def ofPointwiseEqvConstant
    (stream : Nat -> Q') (value : Q')
    (constant : forall scale, stream scale ≈ value) :
    SummableRationalStepVariation stream where
  variation := fun _ => 0
  variation_nonnegative := fun _ => Q'.le_refl' 0
  tailControl := {
    tailRate := fun _ => 0
    tailRate_antitone := by
      intro epsilon delta hdelta hdeltaepsilon
      exact Nat.le_refl 0
    tailBound := by
      intro epsilon hepsilon start hstart length
      rw [finSum_zero_seq]
      exact Q'.le_of_lt hepsilon
  }
  stepBound := by
    intro scale
    have hnextValue : stream (scale + 1) <= value :=
      Q'.le_of_eqv (constant (scale + 1))
    have hvalueCurrent : value <= stream scale :=
      Q'.ge_of_eqv (constant scale)
    have hcurrentValue : stream scale <= value :=
      Q'.le_of_eqv (constant scale)
    have hvalueNext : value <= stream (scale + 1) :=
      Q'.ge_of_eqv (constant (scale + 1))
    exact
      ⟨Q'.le_trans' _ _ _ hnextValue
          (Q'.le_trans' _ _ _ hvalueCurrent
            (Q'.add_le_self_of_nonneg (stream scale) 0 (Q'.le_refl' 0))),
        Q'.le_trans' _ _ _ hcurrentValue
          (Q'.le_trans' _ _ _ hvalueNext
            (Q'.add_le_self_of_nonneg (stream (scale + 1)) 0
              (Q'.le_refl' 0)))⟩

end SummableRationalStepVariation

end YMGap.Continuum.SummableRationalStepVariation

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.SummableRationalStepVariation.SummableRationalStepVariation.toSummableCRealStepVariation
#print axioms
  YMGap.Continuum.SummableRationalStepVariation.SummableRationalStepVariation.toModCauchyEv
#print axioms
  YMGap.Continuum.SummableRationalStepVariation.SummableRationalStepVariation.converges
#print axioms
  YMGap.Continuum.SummableRationalStepVariation.SummableRationalStepVariation.le_tailCeiling
#print axioms
  YMGap.Continuum.SummableRationalStepVariation.SummableRationalStepVariation.globalCeiling_pos
#print axioms
  YMGap.Continuum.SummableRationalStepVariation.SummableRationalStepVariation.le_globalCeiling
#print axioms
  YMGap.Continuum.SummableRationalStepVariation.SummableRationalStepVariation.le_of_initial_add_totalBudget_le
#print axioms
  YMGap.Continuum.SummableRationalStepVariation.SummableRationalStepVariation.ofPointwiseEqvConstant
