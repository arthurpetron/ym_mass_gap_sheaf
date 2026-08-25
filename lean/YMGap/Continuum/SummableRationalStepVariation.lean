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
  YMGap.Continuum.SummableRationalStepVariation.SummableRationalStepVariation.ofPointwiseEqvConstant
