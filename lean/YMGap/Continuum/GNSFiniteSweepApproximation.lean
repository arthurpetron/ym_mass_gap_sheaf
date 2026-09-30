/-
# Quantitative approximation of a completed finite projection sweep

A polynomial update acts on the original dense GNS carrier, while the actual
projection acts on its completion. A uniform one-step squared-distance bound
propagates through any head-first finite schedule. The error budget is an
explicit finite recurrence evaluated on the successive polynomial states;
it does not assume a gap, a common fixed space, or a continuum limit.
-/

import YMGap.Continuum.GNSProjectionSweep
import YMGap.Continuum.GNSTransferMetric
import YMGap.Continuum.ContinuousTransferCalculus
import YMGap.Continuum.RCSignedPairBudget
import YMGap.Continuum.HamiltonianScalar

namespace YMGap.Continuum.GNSFiniteSweepApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep

variable {D : GNSData} {Index : Type}

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CReal.sub_self_eqv_zero A)

private theorem rc_scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem cSub_zero (x : GNSCompletionSpace D) :
    D.cSub x (embedV D D.zero) = x := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  rw [D.cinnerCompl_cSub_left, D.cinnerCompl_embedZero_left, rc_sub_zero]

private theorem cSub_self (x : GNSCompletionSpace D) :
    D.cSub x x = embedV D D.zero := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  rw [D.cinnerCompl_cSub_left, rc_sub_self, D.cinnerCompl_embedZero_left]

private theorem distance_self_zero (x : GNSCompletionSpace D) :
    GNSTransferMetric.distanceSq D x x = RCzero := by
  change normSq (D.cSub x x) = RCzero
  rw [cSub_self]
  exact D.cinnerCompl_embedZero_left _

private theorem distance_zero (x : GNSCompletionSpace D) :
    GNSTransferMetric.distanceSq D x (embedV D D.zero) = normSq x := by
  change normSq (D.cSub x (embedV D D.zero)) = normSq x
  rw [cSub_zero]

private theorem distance_comm (x y : GNSCompletionSpace D) :
    GNSTransferMetric.distanceSq D x y =
      GNSTransferMetric.distanceSq D y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  exact CReal.Equiv_of_limit_of_equal
    (fun n => CReal.ofQ'_equiv_of_eqv
      (D.distSqQ_comm (X.seq n) (Y.seq n)))
    (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy X Y))
    (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy Y X))

/-- The list head acts first, matching `Family.sweep`. Every state of this
approximation is the embedding of an explicitly given dense vector. -/
def approximateSweep (Q : Index → D.V → D.V) :
    List Index → D.V → GNSCompletionSpace D
  | [], p => embedV D p
  | i :: rest, p => approximateSweep Q rest (Q i p)

/-- A finite, computable squared-error budget. The final self-distance is
left in the formula so the base case uses reflexivity directly. In particular,
this budget does not hide a selected completed representative. -/
def errorBudget (Q : Index → D.V → D.V) (delta : Q') :
    List Index → D.V → RC
  | [], p => GNSTransferMetric.distanceSq D (embedV D p) (embedV D p)
  | i :: rest, p =>
      RCadd
        (RCadd (RCscale delta (normSq (embedV D p)))
          (RCscale delta (normSq (embedV D p))))
        (RCadd (errorBudget Q delta rest (Q i p))
          (errorBudget Q delta rest (Q i p)))

/-- Explicit scalar recurrence for a schedule-length-only error bound. -/
def errorCoefficient : Nat → Q'
  | 0 => 0
  | n + 1 => 2 + 8 * errorCoefficient n

/-- The explicit finite-sweep amplification coefficient is nonnegative. -/
theorem errorCoefficient_nonneg (n : Nat) :
    (0 : Q') ≤ errorCoefficient n := by
  induction n with
  | zero => exact Q'.le_refl' _
  | succ n ih =>
      change (0 : Q') ≤ 2 + 8 * errorCoefficient n
      exact Q'.zero_le_add _ _ (by decide : (0 : Q') ≤ 2)
        (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 8) ih)

/-- A computable one-step tolerance for a requested final squared-error
tolerance. The first reciprocal clamps the requested error below one; the
second pays the finite sweep amplification. -/
def stepTolerance (epsilon : Q') (n : Nat) : Q' :=
  (epsilon * ExpUBInstance.oneOver1p epsilon) *
    ExpUBInstance.oneOver1p (errorCoefficient n)

theorem stepTolerance_pos {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    (n : Nat) : (0 : Q') < stepTolerance epsilon n := by
  unfold stepTolerance
  exact Q'.mul_pos
    (Q'.mul_pos hepsilon (HamiltonianScalar.oneOver1p_pos epsilon))
    (HamiltonianScalar.oneOver1p_pos (errorCoefficient n))

theorem stepTolerance_le_one (epsilon : Q')
    (hepsilon : (0 : Q') ≤ epsilon) (n : Nat) :
    stepTolerance epsilon n ≤ 1 := by
  let e := ExpUBInstance.oneOver1p epsilon
  let c := errorCoefficient n
  have hc : ExpUBInstance.oneOver1p c ≤ 1 := by
    have h := ExpUBInstance.oneOver1p_antitone 0 c (errorCoefficient_nonneg n)
    rwa [ExpUBInstance.oneOver1p_zero] at h
  have heps : epsilon * e ≤ 1 := by
    have h := HamiltonianScalar.key_bound epsilon 1 hepsilon
      (by decide : (0 : Q') ≤ 1)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left epsilon e (1 * e)
        (Q'.eqv_symm (Q'.one_mul_eqv e)))) h
  have hprod : (epsilon * e) * ExpUBInstance.oneOver1p c ≤
      (epsilon * e) * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hc
      (Q'.mul_nonneg _ _ hepsilon (ExpUBInstance.oneOver1p_nonneg epsilon))
  change (epsilon * e) * ExpUBInstance.oneOver1p c ≤ 1
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) heps)

theorem stepTolerance_coefficient_le (epsilon : Q')
    (hepsilon : (0 : Q') ≤ epsilon) (n : Nat) :
    stepTolerance epsilon n * errorCoefficient n ≤ epsilon := by
  let e := epsilon * ExpUBInstance.oneOver1p epsilon
  let c := errorCoefficient n
  have he : e ≤ epsilon := by
    have hunit : ExpUBInstance.oneOver1p epsilon ≤ 1 := by
      have h := ExpUBInstance.oneOver1p_antitone 0 epsilon hepsilon
      rwa [ExpUBInstance.oneOver1p_zero] at h
    have h := Q'.mul_le_mul_of_nonneg_left _ _ epsilon hunit hepsilon
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_one_eqv epsilon))
  have hbudget := HamiltonianScalar.key_bound c e (errorCoefficient_nonneg n)
    (Q'.mul_nonneg _ _ hepsilon (ExpUBInstance.oneOver1p_nonneg epsilon))
  change (e * ExpUBInstance.oneOver1p c) * c ≤ epsilon
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv (e * ExpUBInstance.oneOver1p c) c))
    (Q'.le_trans' _ _ _ hbudget he)

private theorem four_copies (a : RC) :
    RCadd (RCadd a a) (RCadd a a) = RCscale 4 a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
      (.mul (.const 4) (.var 0)) (by decide)
      (fun _ => A.approx n)))

private theorem join_budget (delta coeff : Q') (a : RC) :
    RCadd (RCadd (RCscale delta a) (RCscale delta a))
      (RCadd (RCscale (delta * coeff) (RCscale 4 a))
        (RCscale (delta * coeff) (RCscale 4 a))) =
      RCscale (delta * (2 + 8 * coeff)) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2)))
        (.add
          (.mul (.mul (.var 0) (.var 1)) (.mul (.const 4) (.var 2)))
          (.mul (.mul (.var 0) (.var 1)) (.mul (.const 4) (.var 2)))))
      (.mul (.mul (.var 0) (.add (.const 2) (.mul (.const 8) (.var 1))))
        (.var 2)) (by decide)
      (fun | 0 => delta | 1 => coeff | _ => A.approx n)))

namespace Family

variable (P : GNSProjectionSweep.Family D Index)

/-- The actual completed sweep preserves subtraction, including for
noncommuting schedules. -/
theorem sweep_sub (schedule : List Index) (x y : GNSCompletionSpace D) :
    P.sweep schedule (D.cSub x y) =
      D.cSub (P.sweep schedule x) (P.sweep schedule y) := by
  induction schedule generalizing x y with
  | nil => rfl
  | cons i rest ih =>
      change P.sweep rest (P.op i (D.cSub x y)) =
        D.cSub (P.sweep rest (P.op i x)) (P.sweep rest (P.op i y))
      rw [P.op_sub, ih]

/-- The same sweep contracts squared distance between arbitrary completed
vectors. -/
theorem sweep_distance_le (schedule : List Index)
    (x y : GNSCompletionSpace D) :
    RCle (GNSTransferMetric.distanceSq D (P.sweep schedule x) (P.sweep schedule y))
      (GNSTransferMetric.distanceSq D x y) := by
  change RCle
    (normSq (D.cSub (P.sweep schedule x) (P.sweep schedule y)))
    (normSq (D.cSub x y))
  rw [← sweep_sub P schedule x y]
  exact P.sweep_norm schedule (D.cSub x y)

/-- A one-step squared error with coefficient at most one forces the explicit
dense update to have squared norm at most four times its input norm. -/
theorem approximate_update_norm_le_four
    (Q : Index → D.V → D.V) (delta : Q')
    (hdelta : delta ≤ 1)
    (hsingle : ∀ i p,
      RCle (GNSTransferMetric.distanceSq D
        (P.op i (embedV D p)) (embedV D (Q i p)))
        (RCscale delta (normSq (embedV D p))))
    (i : Index) (p : D.V) :
    RCle (normSq (embedV D (Q i p)))
      (RCscale 4 (normSq (embedV D p))) := by
  let a := normSq (embedV D p)
  have he : RCle
      (GNSTransferMetric.distanceSq D
        (embedV D (Q i p)) (P.op i (embedV D p)))
      (RCscale delta a) := by
    rw [distance_comm]
    exact hsingle i p
  have he' : RCle
      (GNSTransferMetric.distanceSq D
        (embedV D (Q i p)) (P.op i (embedV D p))) a := by
    exact RCle_trans he
      (by simpa only [RCscale_one] using
        RCscale_scalar_mono hdelta (D.cinner_self_nonneg (embedV D p)))
  have hop : RCle (normSq (P.op i (embedV D p))) a :=
    P.op_norm i (embedV D p)
  have htriangle := GNSTransferMetric.distance_triangle D
    (embedV D (Q i p)) (P.op i (embedV D p)) (embedV D D.zero)
  rw [distance_zero, distance_zero] at htriangle
  have h := RCle_trans htriangle
    (RCadd_le_add (RCadd_le_add he' he') (RCadd_le_add hop hop))
  rw [four_copies] at h
  exact h

/-- All explicit dense intermediate states obey a schedule-length-only norm
bound. This is the norm control used by the error recurrence. -/
theorem approximateSweep_norm_le
    (Q : Index → D.V → D.V) (delta : Q')
    (hdelta : delta ≤ 1)
    (hsingle : ∀ i p,
      RCle (GNSTransferMetric.distanceSq D
        (P.op i (embedV D p)) (embedV D (Q i p)))
        (RCscale delta (normSq (embedV D p))))
    (schedule : List Index) (p : D.V) :
    RCle (normSq (approximateSweep Q schedule p))
      (RCscale (4 ^ schedule.length) (normSq (embedV D p))) := by
  induction schedule generalizing p with
  | nil =>
      change RCle (normSq (embedV D p))
        (RCscale (4 ^ 0) (normSq (embedV D p)))
      rw [Q'.pow_zero, RCscale_one]
      exact RCle_refl _
  | cons i rest ih =>
      have htail := ih (Q i p)
      have hstep := approximate_update_norm_le_four P Q delta hdelta hsingle i p
      have hscaled := RCscale_mono
        (Q'.pow_nonneg 4 (by decide : (0 : Q') ≤ 4) rest.length) hstep
      rw [RCscale_RCscale,
        RCSignedPairBudget.scale_congr
          (Q'.mul_comm_eqv (4 ^ rest.length) 4) (normSq (embedV D p))] at hscaled
      change RCle (normSq (approximateSweep Q rest (Q i p)))
        (RCscale (4 ^ (rest.length + 1)) (normSq (embedV D p)))
      rw [Q'.pow_succ]
      exact RCle_trans htail hscaled

/-- The finite recurrence has an input-independent coefficient. The only
extra restriction is `delta ≤ 1`; nonnegativity of `delta` ensures all scalar
order steps preserve direction. -/
theorem errorBudget_le_coefficient
    (Q : Index → D.V → D.V) (delta : Q')
    (hdelta0 : (0 : Q') ≤ delta) (hdelta1 : delta ≤ 1)
    (hsingle : ∀ i p,
      RCle (GNSTransferMetric.distanceSq D
        (P.op i (embedV D p)) (embedV D (Q i p)))
        (RCscale delta (normSq (embedV D p))))
    (schedule : List Index) (p : D.V) :
    RCle (errorBudget Q delta schedule p)
      (RCscale (delta * errorCoefficient schedule.length)
        (normSq (embedV D p))) := by
  induction schedule generalizing p with
  | nil =>
      change RCle (GNSTransferMetric.distanceSq D (embedV D p) (embedV D p))
        (RCscale (delta * 0) (normSq (embedV D p)))
      rw [distance_self_zero,
        RCSignedPairBudget.scale_congr (Q'.mul_zero_eqv delta), rc_scale_zero]
      exact RCle_refl _
  | cons i rest ih =>
      let a := normSq (embedV D p)
      let c := errorCoefficient rest.length
      have hc : (0 : Q') ≤ delta * c :=
        Q'.mul_nonneg _ _ hdelta0 (errorCoefficient_nonneg _)
      have htail := ih (Q i p)
      have hnorm := approximate_update_norm_le_four P Q delta hdelta1 hsingle i p
      have hscaled := RCscale_mono hc hnorm
      have htail' := RCle_trans htail hscaled
      change RCle
        (RCadd (RCadd (RCscale delta a) (RCscale delta a))
          (RCadd (errorBudget Q delta rest (Q i p))
            (errorBudget Q delta rest (Q i p))))
        (RCscale (delta * (2 + 8 * c)) a)
      have h : RCle
          (RCadd (RCadd (RCscale delta a) (RCscale delta a))
            (RCadd (errorBudget Q delta rest (Q i p))
              (errorBudget Q delta rest (Q i p))))
          (RCadd (RCadd (RCscale delta a) (RCscale delta a))
            (RCadd (RCscale (delta * c) (RCscale 4 a))
              (RCscale (delta * c) (RCscale 4 a)))) :=
        RCadd_le_add
          (RCadd_le_add (RCle_refl (RCscale delta a))
            (RCle_refl (RCscale delta a)))
          (RCadd_le_add htail' htail')
      rw [join_budget delta c a] at h
      exact h

/-- An all-input single-update approximation transfers to every finite
head-first sweep on the *same* completed GNS carrier. The finite recurrence
retains the actual intermediate polynomial states and is available even when
no independent norm bound on the polynomial updates has been established. -/
theorem sweep_approximation_error
    (Q : Index → D.V → D.V) (delta : Q')
    (hsingle : ∀ i p,
      RCle (GNSTransferMetric.distanceSq D
        (P.op i (embedV D p)) (embedV D (Q i p)))
        (RCscale delta (normSq (embedV D p))))
    (schedule : List Index) (p : D.V) :
    RCle (GNSTransferMetric.distanceSq D
      (P.sweep schedule (embedV D p)) (approximateSweep Q schedule p))
      (errorBudget Q delta schedule p) := by
  induction schedule generalizing p with
  | nil =>
      exact RCle_refl _
  | cons i rest ih =>
      change RCle
        (GNSTransferMetric.distanceSq D
          (P.sweep rest (P.op i (embedV D p)))
          (approximateSweep Q rest (Q i p)))
        (RCadd
          (RCadd (RCscale delta (normSq (embedV D p)))
            (RCscale delta (normSq (embedV D p))))
          (RCadd (errorBudget Q delta rest (Q i p))
            (errorBudget Q delta rest (Q i p))))
      have hfirst := sweep_distance_le P rest
        (P.op i (embedV D p)) (embedV D (Q i p))
      have hfirst' := RCle_trans hfirst (hsingle i p)
      have htail := ih (Q i p)
      exact RCle_trans
        (GNSTransferMetric.distance_triangle D
          (P.sweep rest (P.op i (embedV D p)))
          (P.sweep rest (embedV D (Q i p)))
          (approximateSweep Q rest (Q i p)))
        (RCadd_le_add (RCadd_le_add hfirst' hfirst')
          (RCadd_le_add htail htail))

/-- Uniform all-input finite-sweep approximation with an explicit coefficient
that depends only on schedule length: `c₀=0`, `cₙ₊₁=2+8cₙ`. -/
theorem sweep_approximation_uniform
    (Q : Index → D.V → D.V) (delta : Q')
    (hdelta0 : (0 : Q') ≤ delta) (hdelta1 : delta ≤ 1)
    (hsingle : ∀ i p,
      RCle (GNSTransferMetric.distanceSq D
        (P.op i (embedV D p)) (embedV D (Q i p)))
        (RCscale delta (normSq (embedV D p))))
    (schedule : List Index) (p : D.V) :
    RCle (GNSTransferMetric.distanceSq D
      (P.sweep schedule (embedV D p)) (approximateSweep Q schedule p))
      (RCscale (delta * errorCoefficient schedule.length)
        (normSq (embedV D p))) :=
  RCle_trans (sweep_approximation_error P Q delta hsingle schedule p)
    (errorBudget_le_coefficient P Q delta hdelta0 hdelta1 hsingle schedule p)

end Family

end YMGap.Continuum.GNSFiniteSweepApproximation

#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.Family.sweep_sub
#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.errorCoefficient_nonneg
#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.stepTolerance_pos
#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.stepTolerance_le_one
#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.stepTolerance_coefficient_le
#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.Family.sweep_distance_le
#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.Family.approximate_update_norm_le_four
#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.Family.approximateSweep_norm_le
#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.Family.errorBudget_le_coefficient
#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.Family.sweep_approximation_error
#print axioms YMGap.Continuum.GNSFiniteSweepApproximation.Family.sweep_approximation_uniform
