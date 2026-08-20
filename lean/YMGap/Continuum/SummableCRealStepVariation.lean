/-
M4c -- derive a constructive-real Cauchy modulus from summable two-sided
single-step variation.

A uniform lower floor and upper ceiling do not imply convergence, and the
one-sided normalized-loss recurrence used for mass persistence does not control
upward motion.  This file isolates the additional local estimate which really
does imply cutoff removal:

  |s_(j+1) - s_j| <= variation_j,

with a Type-level antitone tail modulus for the nonnegative variation stream.
The estimate is stated directly on the rational approximations of the
constructive reals.  Together with an explicit inner regularity modulus for
each term, it constructs `CReal.ModCauchyEv s`.

This is reduction machinery only.  It does not prove the two-sided variation
estimate for the four-dimensional Yang--Mills exact logarithmic rates.
-/

import YMGap.Constructive.CRealCompleteCauchy
import YMGap.Continuum.KPLimit
import YMGap.RG.StableDynamics

namespace YMGap.Continuum.SummableCRealStepVariation

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.RG.StableDynamics

/-- Local data sufficient to construct a cutoff Cauchy modulus for a sequence
of constructive reals.

The `tailRate` field is antitone in the requested tolerance, as required by the
constructive completion backbone.  `innerRate` keeps each term's regularity
modulus as Type-level data rather than attempting to extract it from the legacy
Prop-valued `CReal.cauchy` field. -/
structure SummableCRealStepVariation (s : Nat -> CReal) : Type 1 where
  /-- Nonnegative bound on the movement across one cutoff step. -/
  variation : Nat -> Q'
  variation_nonnegative : forall j : Nat, (0 : Q') <= variation j
  /-- Cutoff after which every finite variation tail is below `epsilon`. -/
  tailRate : Q' -> Nat
  tailRate_antitone : forall epsilon delta : Q',
    (0 : Q') < delta -> delta <= epsilon ->
      tailRate epsilon <= tailRate delta
  tailBound : forall epsilon : Q', (0 : Q') < epsilon ->
    forall start : Nat, tailRate epsilon <= start ->
      forall length : Nat,
        finSum (fun offset => variation (start + offset)) length <= epsilon
  /-- Type-level inner approximation modulus for each `s j`. -/
  innerRate : Nat -> Q' -> Nat
  innerRegular : forall j : Nat, forall epsilon : Q',
    (0 : Q') < epsilon -> forall p q : Nat,
      innerRate j epsilon <= p -> innerRate j epsilon <= q ->
        (s j).approx p <= (s j).approx q + epsilon /\
        (s j).approx q <= (s j).approx p + epsilon
  /-- Two-sided movement across one cutoff step, uniformly at every rational
  approximation index. -/
  stepBound : forall j k : Nat,
    (s (j + 1)).approx k <= (s j).approx k + variation j /\
    (s j).approx k <= (s (j + 1)).approx k + variation j

/-- A representation-invariant antitone tail control for a nonnegative
variation stream.

This is deliberately not required to dominate `SummableDistortion.modulus`.
Some legacy budgets choose a stage from `epsilon.den`; because `Q'` is an
unreduced rational representation, equivalent tolerances can have arbitrarily
different denominators, so that stored stage need not admit any antitone
majorant.  The tail estimate itself is sound; this record supplies a fresh
order-respecting rate for the same stream. -/
structure AntitoneTailControl (variation : Nat -> Q') : Type where
  tailRate : Q' -> Nat
  tailRate_antitone : forall epsilon delta : Q',
    (0 : Q') < delta -> delta <= epsilon ->
      tailRate epsilon <= tailRate delta
  tailBound : forall epsilon : Q', (0 : Q') < epsilon ->
    forall start : Nat, tailRate epsilon <= start ->
      forall length : Nat,
        finSum (fun offset => variation (start + offset)) length <= epsilon

/-- The exact local information not supplied by a rational summability
budget: explicit inner regularity of the constructive-real terms and a
two-sided comparison of consecutive terms by the budget's variation stream. -/
structure CRealStepTracking (s : Nat -> CReal)
    (variation : Nat -> Q') : Type 1 where
  innerRate : Nat -> Q' -> Nat
  innerRegular : forall j : Nat, forall epsilon : Q',
    (0 : Q') < epsilon -> forall p q : Nat,
      innerRate j epsilon <= p -> innerRate j epsilon <= q ->
        (s j).approx p <= (s j).approx q + epsilon /\
        (s j).approx q <= (s j).approx p + epsilon
  stepBound : forall j k : Nat,
    (s (j + 1)).approx k <= (s j).approx k + variation j /\
    (s j).approx k <= (s (j + 1)).approx k + variation j

namespace CRealStepTracking

/-- Reuse an existing summable distortion budget for the local exact-rate
tracking estimate.  Only an antitone refinement of its stored modulus is
additional bookkeeping. -/
def withSummableBudget
    {s : Nat -> CReal} {variation : Nat -> Q'}
    (tracking : CRealStepTracking s variation)
    (budget : SummableDistortion variation)
    (tailControl : AntitoneTailControl variation) :
    SummableCRealStepVariation s where
  variation := variation
  variation_nonnegative := budget.termNonnegative
  tailRate := tailControl.tailRate
  tailRate_antitone := tailControl.tailRate_antitone
  tailBound := tailControl.tailBound
  innerRate := tracking.innerRate
  innerRegular := tracking.innerRegular
  stepBound := tracking.stepBound

end CRealStepTracking

namespace SummableCRealStepVariation

variable {s : Nat -> CReal}

/-- Upper telescoping of the local variation estimate. -/
theorem telescope_up (V : SummableCRealStepVariation s)
    (k start length : Nat) :
    (s (start + length)).approx k <=
      (s start).approx k +
        finSum (fun offset => V.variation (start + offset)) length := by
  exact YMGap.Continuum.telescope_up
    (fun j => (s j).approx k) V.variation
    (fun j => (V.stepBound j k).1) start length

/-- Lower telescoping of the local variation estimate. -/
theorem telescope_lo (V : SummableCRealStepVariation s)
    (k start length : Nat) :
    (s start).approx k <=
      (s (start + length)).approx k +
        finSum (fun offset => V.variation (start + offset)) length := by
  exact YMGap.Continuum.telescope_lo
    (fun j => (s j).approx k) V.variation
    (fun j => (V.stepBound j k).2) start length

/-- The local summable variation data construct the global Type-level
eventual-outer Cauchy modulus. -/
def toModCauchyEv (V : SummableCRealStepVariation s) :
    CReal.ModCauchyEv s where
  M := V.tailRate
  reg := V.innerRate
  boundK := fun _ _ _ => 0
  bound := by
    intro epsilon hepsilon m n hm hn k _
    rcases Nat.le_total m n with hmn | hnm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have htail := V.tailBound epsilon hepsilon m hm d
      exact
        ⟨Q'.le_trans' _ _ _ (V.telescope_lo k m d)
            (Q'.add_le_add_left ((s (m + d)).approx k) _ _ htail),
          Q'.le_trans' _ _ _ (V.telescope_up k m d)
            (Q'.add_le_add_left ((s m).approx k) _ _ htail)⟩
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      have htail := V.tailBound epsilon hepsilon n hn d
      exact
        ⟨Q'.le_trans' _ _ _ (V.telescope_up k n d)
            (Q'.add_le_add_left ((s n).approx k) _ _ htail),
          Q'.le_trans' _ _ _ (V.telescope_lo k n d)
            (Q'.add_le_add_left ((s (n + d)).approx k) _ _ htail)⟩
  regular := V.innerRegular
  Mmono := V.tailRate_antitone

@[simp] theorem toModCauchyEv_M
    (V : SummableCRealStepVariation s) :
    V.toModCauchyEv.M = V.tailRate := rfl

end SummableCRealStepVariation

end YMGap.Continuum.SummableCRealStepVariation

#print axioms YMGap.Continuum.SummableCRealStepVariation.SummableCRealStepVariation.telescope_up
#print axioms YMGap.Continuum.SummableCRealStepVariation.SummableCRealStepVariation.telescope_lo
#print axioms YMGap.Continuum.SummableCRealStepVariation.SummableCRealStepVariation.toModCauchyEv
#print axioms YMGap.Continuum.SummableCRealStepVariation.CRealStepTracking.withSummableBudget
