/-
M4c -- cutoff Cauchy convergence from summable eventual step variation.

For constructive-real sequences, a physical comparison between consecutive
terms should concern the represented reals, not necessarily their coarsest
rational partial sums.  This module therefore weakens the all-approximation
step premise of `SummableCRealStepVariation` to a Type-level eventual premise:
for every positive tolerance, a computed approximation stage makes the
consecutive-step estimate valid with that extra tolerance.

Across a finite interval of length `d`, the proof assigns each step the
computed tolerance

  (epsilon/2) * 1/(d+1).

The sum of the `d` step tolerances is at most `epsilon/2`; the summable
variation tail contributes the other half.  A finite maximum of the local
step stages becomes `ModCauchyEv.boundK`.  Thus no all-index comparison and no
Prop-level modulus extraction is required.
-/

import YMGap.Constructive.FinSumAlg
import YMGap.Continuum.SummableCRealStepVariation

namespace YMGap.Continuum.SummableCRealEventualStepVariation

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.RG.StableDynamics
open YMGap.Continuum.SummableCRealStepVariation

/-- Maximum of the first `length` values of a natural-valued sequence. -/
def natPrefixMax (f : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | length + 1 => max (natPrefixMax f length) (f length)

/-- Every member of a finite prefix lies below its computed maximum. -/
theorem le_natPrefixMax (f : Nat -> Nat) (offset length : Nat)
    (hoffset : offset < length) :
    f offset <= natPrefixMax f length := by
  induction length with
  | zero => omega
  | succ length ih =>
      simp only [natPrefixMax]
      by_cases hlast : offset = length
      · subst offset
        exact Nat.le_max_right _ _
      · exact Nat.le_trans (ih (by omega)) (Nat.le_max_left _ _)

/-- A constant finite rational sum is the natural count times that constant. -/
theorem finSum_const_eqv (a : Q') : forall length : Nat,
    (finSum (fun _ => a) length).eqv (Q'.ofNat length * a)
  | 0 => by
      show ((0 : Q')).eqv (Q'.ofNat 0 * a)
      exact Q'.eqv_symm (Q'.zero_mul_eqv a)
  | length + 1 => by
      show (finSum (fun _ => a) length + a).eqv
        (Q'.ofNat (length + 1) * a)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ a (finSum_const_eqv a length)) ?_
      have hone : (a).eqv ((1 : Q') * a) := Q'.eqv_symm (Q'.one_mul_eqv a)
      have hadd : (Q'.ofNat length * a + a).eqv
          ((Q'.ofNat length + 1) * a) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ hone) ?_
        exact Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat length) 1 a)
      refine Q'.eqv_trans _ _ _ hadd ?_
      exact Q'.mul_eqv_congr_right _ _ a
        (Q'.eqv_symm (Q'.ofNat_add_eqv length 1))

/-- Natural embeddings are nonnegative. -/
theorem ofNat_nonnegative (length : Nat) :
    (0 : Q') <= Q'.ofNat length := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

/-- Per-step tolerance used over an interval of a known finite length. -/
def stepTolerance (epsilon : Q') (length : Nat) : Q' :=
  (HalfPow.half * epsilon) * Q'.invSucc length

/-- The per-step tolerance is positive. -/
theorem stepTolerance_pos (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (length : Nat) :
    (0 : Q') < stepTolerance epsilon length := by
  have hhalf : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  show (0 : Int) * ((stepTolerance epsilon length).den : Int) <
    (stepTolerance epsilon length).num * ((0 : Q').den : Int)
  rw [Int.zero_mul]
  show (0 : Int) <
    (HalfPow.half * epsilon).num * (Q'.invSucc length).num * 1
  rw [Q'.invSucc_num, Int.mul_one, Int.mul_one]
  exact CReal.num_pos_of_pos hhalf

/-- The accumulated step tolerance over an interval consumes at most half of
the requested error budget. -/
theorem count_mul_stepTolerance_le (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (length : Nat) :
    Q'.ofNat length * stepTolerance epsilon length <=
      HalfPow.half * epsilon := by
  have hcount : (0 : Q') <= Q'.ofNat length := ofNat_nonnegative length
  have hhalf : (0 : Q') <= HalfPow.half * epsilon :=
    Q'.le_of_lt (ExpNeg.half_mul_pos epsilon hepsilon)
  simpa only [stepTolerance] using
    (ExpNeg.mul_le_of_mul_invSucc_toNat
      (Q'.ofNat length) (HalfPow.half * epsilon) hcount hhalf)

/-- Type-level local tracking with an eventual-in-approximation consecutive
step estimate. -/
structure CRealEventualStepTracking (s : Nat -> CReal)
    (variation : Nat -> Q') : Type 1 where
  innerRate : Nat -> Q' -> Nat
  innerRegular : forall j : Nat, forall epsilon : Q',
    (0 : Q') < epsilon -> forall p q : Nat,
      innerRate j epsilon <= p -> innerRate j epsilon <= q ->
        (s j).approx p <= (s j).approx q + epsilon /\
        (s j).approx q <= (s j).approx p + epsilon
  /-- Approximation stage for one consecutive-rate comparison at the requested
  extra tolerance. -/
  stepRate : Nat -> Q' -> Nat
  stepBound : forall j : Nat, forall epsilon : Q',
    (0 : Q') < epsilon -> forall k : Nat, stepRate j epsilon <= k ->
      (s (j + 1)).approx k <=
          ((s j).approx k + variation j) + epsilon /\
      (s j).approx k <=
          ((s (j + 1)).approx k + variation j) + epsilon

/-- Summable eventual step variation, including the antitone tail rate needed
for constructive completion. -/
structure SummableCRealEventualStepVariation (s : Nat -> CReal) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall j : Nat, (0 : Q') <= variation j
  tailRate : Q' -> Nat
  tailRate_antitone : forall epsilon delta : Q',
    (0 : Q') < delta -> delta <= epsilon ->
      tailRate epsilon <= tailRate delta
  tailBound : forall epsilon : Q', (0 : Q') < epsilon ->
    forall start : Nat, tailRate epsilon <= start ->
      forall length : Nat,
        finSum (fun offset => variation (start + offset)) length <= epsilon
  innerRate : Nat -> Q' -> Nat
  innerRegular : forall j : Nat, forall epsilon : Q',
    (0 : Q') < epsilon -> forall p q : Nat,
      innerRate j epsilon <= p -> innerRate j epsilon <= q ->
        (s j).approx p <= (s j).approx q + epsilon /\
        (s j).approx q <= (s j).approx p + epsilon
  stepRate : Nat -> Q' -> Nat
  stepBound : forall j : Nat, forall epsilon : Q',
    (0 : Q') < epsilon -> forall k : Nat, stepRate j epsilon <= k ->
      (s (j + 1)).approx k <=
          ((s j).approx k + variation j) + epsilon /\
      (s j).approx k <=
          ((s (j + 1)).approx k + variation j) + epsilon

namespace CRealEventualStepTracking

/-- Combine local eventual step tracking with an existing summable budget and
its representation-invariant antitone tail control. -/
def withSummableBudget
    {s : Nat -> CReal} {variation : Nat -> Q'}
    (tracking : CRealEventualStepTracking s variation)
    (budget : SummableDistortion variation)
    (tailControl : AntitoneTailControl variation) :
    SummableCRealEventualStepVariation s where
  variation := variation
  variation_nonnegative := budget.termNonnegative
  tailRate := tailControl.tailRate
  tailRate_antitone := tailControl.tailRate_antitone
  tailBound := tailControl.tailBound
  innerRate := tracking.innerRate
  innerRegular := tracking.innerRegular
  stepRate := tracking.stepRate
  stepBound := tracking.stepBound

end CRealEventualStepTracking

namespace SummableCRealEventualStepVariation

variable {s : Nat -> CReal}

/-- Maximum local approximation threshold across one finite cutoff interval. -/
def intervalStepRate (V : SummableCRealEventualStepVariation s)
    (epsilon : Q') (start length : Nat) : Nat :=
  natPrefixMax
    (fun offset => V.stepRate (start + offset)
      (stepTolerance epsilon length)) length

/-- Every local step threshold in the interval lies below the interval
maximum. -/
theorem stepRate_le_intervalStepRate
    (V : SummableCRealEventualStepVariation s)
    (epsilon : Q') (start length offset : Nat) (hoffset : offset < length) :
    V.stepRate (start + offset) (stepTolerance epsilon length) <=
      V.intervalStepRate epsilon start length :=
  le_natPrefixMax
    (fun i => V.stepRate (start + i) (stepTolerance epsilon length))
    offset length hoffset

/-- A telescoping upper bound whose single-step premise is needed only inside
the finite interval being summed. -/
theorem telescope_up_bounded (S a : Nat -> Q') : forall length : Nat,
    (forall offset : Nat, offset < length ->
      S (offset + 1) <= S offset + a offset) ->
    S length <= S 0 + finSum a length
  | 0 => by
      intro _
      show S 0 <= S 0 + (0 : Q')
      rw [Q'.add_zero']
      exact Q'.le_refl' (S 0)
  | length + 1 => by
      intro hstep
      have ih := telescope_up_bounded S a length
        (fun offset hoffset => hstep offset (by omega))
      have hlast : S (length + 1) <= S length + a length :=
        hstep length (by omega)
      show S (length + 1) <= S 0 + (finSum a length + a length)
      refine Q'.le_trans' _ _ _ hlast ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ (a length) ih) ?_
      exact Q'.le_of_eqv
        (Q'.add_assoc_eqv (S 0) (finSum a length) (a length))

/-- A telescoping lower bound whose single-step premise is needed only inside
the finite interval being summed. -/
theorem telescope_lo_bounded (S a : Nat -> Q') : forall length : Nat,
    (forall offset : Nat, offset < length ->
      S offset <= S (offset + 1) + a offset) ->
    S 0 <= S length + finSum a length
  | 0 => by
      intro _
      show S 0 <= S 0 + (0 : Q')
      rw [Q'.add_zero']
      exact Q'.le_refl' (S 0)
  | length + 1 => by
      intro hstep
      have ih := telescope_lo_bounded S a length
        (fun offset hoffset => hstep offset (by omega))
      have hlast : S length <= S (length + 1) + a length :=
        hstep length (by omega)
      show S 0 <= S (length + 1) + (finSum a length + a length)
      refine Q'.le_trans' _ _ _ ih ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ (finSum a length) hlast) ?_
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (S (length + 1)) (a length) (finSum a length)) ?_
      exact Q'.add_eqv_congr_left (S (length + 1)) _ _
        (Q'.add_comm_eqv (a length) (finSum a length))

/-- The sum of variation and per-step approximation slack over an interval is
at most the requested tolerance once the variation tail consumes half. -/
theorem augmentedTail_le
    (V : SummableCRealEventualStepVariation s)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (start length : Nat)
    (hvariation :
      finSum (fun offset => V.variation (start + offset)) length <=
        HalfPow.half * epsilon) :
    finSum
        (fun offset => V.variation (start + offset) +
          stepTolerance epsilon length) length <= epsilon := by
  have hsplit := RationalTail.finSum_add
    (fun offset => V.variation (start + offset))
    (fun _ => stepTolerance epsilon length) length
  have hconstant :
      finSum (fun _ => stepTolerance epsilon length) length <=
        HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (finSum_const_eqv (stepTolerance epsilon length) length))
      (count_mul_stepTolerance_le epsilon hepsilon length)
  have hsum :
      finSum (fun offset => V.variation (start + offset)) length +
          finSum (fun _ => stepTolerance epsilon length) length <=
        HalfPow.half * epsilon + HalfPow.half * epsilon :=
    Q'.add_le_add hvariation hconstant
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))

/-- Telescoping across one ordered interval after the computed maximum local
step stage. -/
theorem intervalBound
    (V : SummableCRealEventualStepVariation s)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (start length k : Nat)
    (hk : V.intervalStepRate epsilon start length <= k)
    (hvariation :
      finSum (fun offset => V.variation (start + offset)) length <=
        HalfPow.half * epsilon) :
    (s (start + length)).approx k <= (s start).approx k + epsilon /\
    (s start).approx k <= (s (start + length)).approx k + epsilon := by
  have hstepTolerance : (0 : Q') < stepTolerance epsilon length :=
    stepTolerance_pos epsilon hepsilon length
  have hstep : forall offset : Nat, offset < length ->
      (s (start + (offset + 1))).approx k <=
          (s (start + offset)).approx k +
            (V.variation (start + offset) + stepTolerance epsilon length) /\
      (s (start + offset)).approx k <=
          (s (start + (offset + 1))).approx k +
            (V.variation (start + offset) + stepTolerance epsilon length) := by
    intro offset hoffset
    have hlocal :
        V.stepRate (start + offset) (stepTolerance epsilon length) <= k :=
      Nat.le_trans
        (V.stepRate_le_intervalStepRate epsilon start length offset hoffset) hk
    obtain ⟨hup, hlo⟩ :=
      V.stepBound (start + offset) (stepTolerance epsilon length)
        hstepTolerance k hlocal
    constructor
    · simpa only [Nat.add_assoc] using
        (Q'.le_trans' _ _ _ hup (Q'.le_of_eqv
          (Q'.add_assoc_eqv
            ((s (start + offset)).approx k) (V.variation (start + offset))
              (stepTolerance epsilon length))))
    · simpa only [Nat.add_assoc] using
        (Q'.le_trans' _ _ _ hlo (Q'.le_of_eqv
          (Q'.add_assoc_eqv
            ((s ((start + offset) + 1)).approx k)
              (V.variation (start + offset)) (stepTolerance epsilon length))))
  have hup := telescope_up_bounded
    (fun offset => (s (start + offset)).approx k)
    (fun offset => V.variation (start + offset) + stepTolerance epsilon length)
    length (fun offset hoffset => (hstep offset hoffset).1)
  have hlo := telescope_lo_bounded
    (fun offset => (s (start + offset)).approx k)
    (fun offset => V.variation (start + offset) + stepTolerance epsilon length)
    length (fun offset hoffset => (hstep offset hoffset).2)
  have htail := V.augmentedTail_le epsilon hepsilon start length hvariation
  exact
    ⟨Q'.le_trans' _ _ _ hup
        (Q'.add_le_add_left ((s start).approx k) _ _ htail),
     Q'.le_trans' _ _ _ hlo
        (Q'.add_le_add_left ((s (start + length)).approx k) _ _ htail)⟩

/-- The outer cutoff uses half the requested tolerance for the summable
variation tail. -/
def outerRate (V : SummableCRealEventualStepVariation s)
    (epsilon : Q') : Nat :=
  V.tailRate (HalfPow.half * epsilon)

/-- Pairwise approximation threshold for the eventual outer Cauchy bound. -/
def outerBoundK (V : SummableCRealEventualStepVariation s)
    (epsilon : Q') (m n : Nat) : Nat :=
  if m <= n then
    V.intervalStepRate epsilon m (n - m)
  else
    V.intervalStepRate epsilon n (m - n)

/-- Summable eventual consecutive-step variation constructs the global
eventual-outer Cauchy modulus. -/
def toModCauchyEv (V : SummableCRealEventualStepVariation s) :
    CReal.ModCauchyEv s where
  M := V.outerRate
  reg := V.innerRate
  boundK := V.outerBoundK
  bound := by
    intro epsilon hepsilon m n hm hn k hk
    have hhalf : (0 : Q') < HalfPow.half * epsilon :=
      ExpNeg.half_mul_pos epsilon hepsilon
    by_cases hmn : m <= n
    · obtain ⟨length, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have htail := V.tailBound (HalfPow.half * epsilon) hhalf m hm length
      have hk' : V.intervalStepRate epsilon m length <= k := by
        simpa [outerBoundK] using hk
      have hbound := V.intervalBound epsilon hepsilon m length k hk' htail
      exact ⟨hbound.2, hbound.1⟩
    · have hnm : n <= m := Nat.le_of_not_ge hmn
      obtain ⟨length, rfl⟩ := Nat.exists_eq_add_of_le hnm
      have htail := V.tailBound (HalfPow.half * epsilon) hhalf n hn length
      have hnot : ¬ (n + length <= n) := by omega
      have hk' : V.intervalStepRate epsilon n length <= k := by
        simpa [outerBoundK, hnot] using hk
      exact V.intervalBound epsilon hepsilon n length k hk' htail
  regular := V.innerRegular
  Mmono := by
    intro epsilon delta hdelta hdeltaepsilon
    have hhalfDelta : (0 : Q') < HalfPow.half * delta :=
      ExpNeg.half_mul_pos delta hdelta
    have hhalfLe : HalfPow.half * delta <= HalfPow.half * epsilon :=
      Q'.mul_le_mul_of_nonneg_left delta epsilon HalfPow.half
        hdeltaepsilon HalfPow.half_nonneg
    exact V.tailRate_antitone
      (HalfPow.half * epsilon) (HalfPow.half * delta) hhalfDelta hhalfLe

end SummableCRealEventualStepVariation

end YMGap.Continuum.SummableCRealEventualStepVariation

#print axioms YMGap.Continuum.SummableCRealEventualStepVariation.le_natPrefixMax
#print axioms YMGap.Continuum.SummableCRealEventualStepVariation.finSum_const_eqv
#print axioms YMGap.Continuum.SummableCRealEventualStepVariation.count_mul_stepTolerance_le
#print axioms YMGap.Continuum.SummableCRealEventualStepVariation.CRealEventualStepTracking.withSummableBudget
#print axioms YMGap.Continuum.SummableCRealEventualStepVariation.SummableCRealEventualStepVariation.intervalBound
#print axioms YMGap.Continuum.SummableCRealEventualStepVariation.SummableCRealEventualStepVariation.toModCauchyEv
