/-
# Well-founded measure for the coupled Jacobi/correction induction

Both outer-height label transports and the common inner peel strictly reduce
`a+b+c` by two.  This module packages the full Jacobi and lifted peeled
families carried at one measure, constructs the lifted component from a full
family at smaller measure, records the proved correction bases, and fences
the upper-order-zero boundary where the outer shift is genuinely unavailable.
-/

import YMGap.Continuum.SU2OrderedRacahCorrectionConverse
import YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnOuterClosure

namespace YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant

set_option linter.unusedVariables false

open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnOuterClosure
open YMGap.Continuum.SU2OrderedRacahRightJacobiInduction
open YMGap.Continuum.SU2OrderedRacahRightJacobiLift
open YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation
open YMGap.Continuum.SU2OrderedRacahHeightOneCoordinateFamily
open YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily
open YMGap.Continuum.SU2OrderedRacahCorrectionConverse

/-- External-label measure decreased by every branch of the proposed mutual
induction. -/
def rightLabelMeasure (a b c : Nat) : Nat := a + b + c

theorem firstThirdShift_measure_lt
    (a b c : Nat) (ha : 0 < a) (hc : 0 < c) :
    rightLabelMeasure (a - 1) b (c - 1) < rightLabelMeasure a b c := by
  unfold rightLabelMeasure
  omega

theorem firstSecondShift_measure_lt
    (a b c : Nat) (ha : 0 < a) (hb : 0 < b) :
    rightLabelMeasure (a - 1) (b - 1) c < rightLabelMeasure a b c := by
  unfold rightLabelMeasure
  omega

theorem innerPeel_measure_lt
    (a b c : Nat) (hb : 0 < b) (hc : 0 < c) :
    rightLabelMeasure a (b - 1) (c - 1) < rightLabelMeasure a b c := by
  unfold rightLabelMeasure
  omega

theorem firstThirdThenInner_measure_lt
    (a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : 1 < c) :
    rightLabelMeasure (a - 1) (b - 1) ((c - 1) - 1) <
      rightLabelMeasure a b c := by
  unfold rightLabelMeasure
  omega

theorem firstSecondThenInner_measure_lt
    (a b c : Nat) (ha : 0 < a) (hb : 1 < b) (hc : 0 < c) :
    rightLabelMeasure (a - 1) ((b - 1) - 1) (c - 1) <
      rightLabelMeasure a b c := by
  unfold rightLabelMeasure
  omega

/-- Full Jacobi information strictly below a measure. -/
def FullJacobiBelow (N : Nat) : Prop :=
  ∀ a b c d (qm q qp : FixedRightCGChannel a b c d),
    rightLabelMeasure a b c < N →
    RightTransposeJacobiFullCoordinateFamily qm q qp

/-- Full Jacobi information exactly on one measure shell. -/
def FullJacobiAtMeasure (N : Nat) : Prop :=
  ∀ a b c d (qm q qp : FixedRightCGChannel a b c d),
    rightLabelMeasure a b c = N →
    RightTransposeJacobiFullCoordinateFamily qm q qp

/-- Full Jacobi information through a closed measure interval. -/
def FullJacobiThrough (N : Nat) : Prop :=
  ∀ a b c d (qm q qp : FixedRightCGChannel a b c d),
    rightLabelMeasure a b c ≤ N →
    RightTransposeJacobiFullCoordinateFamily qm q qp

/-- Recursive construction of the closed measure interval from shell steps. -/
theorem fullJacobiThrough_of_measure_step
    (hstep : ∀ N, FullJacobiBelow N → FullJacobiAtMeasure N) :
    ∀ N, FullJacobiThrough N
  | 0 => by
      intro a b c d qm q qp hmeasure
      apply hstep 0 (by
        intro a' b' c' d' qm' q' qp' hlt
        have hfalse : False := by
          unfold rightLabelMeasure at hlt
          omega
        exact False.elim hfalse) a b c d qm q qp
      omega
  | N + 1 => by
      have hN := fullJacobiThrough_of_measure_step hstep N
      intro a b c d qm q qp hmeasure
      by_cases hsmall : rightLabelMeasure a b c ≤ N
      · exact hN a b c d qm q qp hsmall
      · apply hstep (N + 1) (by
          intro a' b' c' d' qm' q' qp' hlt
          exact hN a' b' c' d' qm' q' qp' (by omega))
            a b c d qm q qp
        omega

/-- Constructive well-founded induction on the external-label measure.  A
shell step may use every strictly smaller full family, but cannot refer to
its own shell. -/
theorem fullJacobi_all_of_measure_step
    (hstep : ∀ N, FullJacobiBelow N → FullJacobiAtMeasure N) :
    ∀ a b c d (qm q qp : FixedRightCGChannel a b c d),
      RightTransposeJacobiFullCoordinateFamily qm q qp := by
  intro a b c d qm q qp
  exact fullJacobiThrough_of_measure_step hstep (rightLabelMeasure a b c)
    a b c d qm q qp (by omega)

/-- The simultaneous data carried at one physical three-channel block. -/
structure JacobiLiftedPackage {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) : Prop where
  full : RightTransposeJacobiFullCoordinateFamily qm q qp
  lifted : ∀ i j l s, j ≤ b →
    LiftedReducedRightTransposeJacobiAt qm q qp i j l s

/-- Specialize the below-measure hypothesis to the common inner peel. -/
theorem reducedFullFamily_of_fullJacobiBelow
    (N : Nat) {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = N)
    (hm : 0 < qm.p) (hp : 0 < q.p) (hpp : 0 < qp.p)
    (hbelow : FullJacobiBelow N) :
    RightTransposeJacobiFullCoordinateFamily
      (reducePositiveInnerRightChannel qm hm)
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel qp hpp) := by
  have hq := Nat.le_min.mp q.p_le
  apply hbelow a (b - 1) (c - 1) d
    (reducePositiveInnerRightChannel qm hm)
    (reducePositiveInnerRightChannel q hp)
    (reducePositiveInnerRightChannel qp hpp)
  rw [← hmeasure]
  exact innerPeel_measure_lt a b c (by omega) (by omega)

/-- The lifted half of the mutual invariant is genuinely well-founded: it is
constructed entirely from the inner-peeled full family at smaller measure. -/
theorem liftedFamily_of_fullJacobiBelow
    (N : Nat) {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = N)
    (hm : 0 < qm.p) (hp : 0 < q.p) (hpp : 0 < qp.p)
    (hp2 : 1 < q.p) (hbelow : FullJacobiBelow N) :
    ∀ i j l s, j ≤ b →
      LiftedReducedRightTransposeJacobiAt qm q qp i j l s := by
  have hreduced := reducedFullFamily_of_fullJacobiBelow
    N qm q qp hmeasure hm hp hpp hbelow
  intro i j l s _
  apply liftedReducedRightTransposeJacobiAt_of_reduced_family
    qm q qp hm hp hpp hp2 i j l s
  intro u v w
  exact hreduced u v w s

/-- Adding a current full family to the strictly-smaller induction hypothesis
produces the simultaneous Jacobi/lifted package. -/
theorem jacobiLiftedPackage_of_full_and_below
    (N : Nat) {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = N)
    (hm : 0 < qm.p) (hp : 0 < q.p) (hpp : 0 < qp.p)
    (hp2 : 1 < q.p)
    (hfull : RightTransposeJacobiFullCoordinateFamily qm q qp)
    (hbelow : FullJacobiBelow N) :
    JacobiLiftedPackage qm q qp where
  full := hfull
  lifted := liftedFamily_of_fullJacobiBelow
    N qm q qp hmeasure hm hp hpp hp2 hbelow

/-- Every simultaneous package supplies the complete higher-height correction
family by exact converse Jacobi cancellation. -/
theorem JacobiLiftedPackage.higherHeightCorrection
    {a b c d : Nat} {qm q qp : FixedRightCGChannel a b c d}
    (P : JacobiLiftedPackage qm q qp) (hp : 0 < q.p) :
    OmegaCorrectionHigherHeightCoordinateFamily qm q qp :=
  omegaCorrectionHigherHeightCoordinateFamily_of_jacobi_and_lifted
    qm q qp hp P.full P.lifted

/-- The already-proved positive-coordinate correction bases: off the total
shell, the lower support face, height zero on the admissible outer interval,
and the strict height-one shell. -/
structure PositiveCorrectionBaseRegimes {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) : Prop where
  offShell : ∀ (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) i j l s,
    0 < i → 0 < j → 0 < l →
    s + q.r + q.p ≠ i + j + l →
    OmegaCorrectionThreeCarrierAt qm q qp i j l s
  lowerSupport : ∀ (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) i j l s,
    0 < i → 0 < j → 0 < l →
    s + q.r + q.p = i + j + l → j + l = qm.p →
    OmegaCorrectionThreeCarrierAt qm q qp i j l s
  heightZero : ∀ (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) i j l s,
    0 < i → 0 < j → 0 < l →
    s + q.r + q.p = i + j + l → j + l = q.p →
    q.p < b → q.p < c → q.r ≤ i → i ≤ a →
    OmegaCorrectionThreeCarrierAt qm q qp i j l s
  heightOneStrict : ∀ (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) i j l s,
    s + q.r + q.p = i + j + l → 3 ≤ j → 3 ≤ l →
    j + l = q.p + 1 → q.p + 2 ≤ b → q.p + 2 ≤ c →
    4 ≤ q.r → q.r + 1 ≤ i → i + 1 ≤ a →
    q.r + 2 ≤ q.intermediate →
    OmegaCorrectionThreeCarrierAt qm q qp i j l s

theorem positiveCorrectionBaseRegimes
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d) :
    PositiveCorrectionBaseRegimes qm q qp where
  offShell := by
    intro hp hprev hnext i j l s hi hj hl hoff
    exact omegaCorrectionThreeCarrierAt_off_total_shell
      qm q qp hp hprev hnext i j l s hi hj hl hoff
  lowerSupport := by
    intro hp hprev hnext i j l s hi hj hl hshell hsum
    exact omegaCorrectionThreeCarrierAt_lower_boundary_on_shell
      qm q qp hp hprev hnext i j l s hi hj hl hshell hsum
  heightZero := by
    intro hp hprev hnext i j l s hi hj hl hshell hsum hpb hpc hri hia
    exact omegaCorrectionThreeCarrierAt_first_bulk_outer_closed_on_shell
      qm q qp hp hprev hnext i j l s hi hj hl hshell hsum hpb hpc hri hia
  heightOneStrict := by
    intro hp hprev hnext i j l s hshell hj hl hheight hpb hpc
      hr hri hia hrn
    exact omegaCorrectionThreeCarrierAt_height_one_strict_bulk_on_shell
      qm q qp hp hprev hnext i j l s hshell hj hl hheight hpb hpc
        hr hri hia hrn

/-- Machine-checked boundary fence for the outer-shift induction.  In the
smallest physical three-channel block the upper channel has order zero, and
after the first/third label shift there is no physical channel retaining its
inner order.  This boundary must therefore be discharged by an edge theorem;
it cannot be folded into the strict shifted-family recurrence. -/
theorem upperOrderZero_outerShift_fence :
    correctionFenceMiddle.r = 1 ∧ correctionFenceUpper.r = 0 ∧
    ¬ ∃ u : FixedRightCGChannel 1 2 1 2, u.p = 2 := by
  constructor
  · rfl
  constructor
  · rfl
  · intro hu
    rcases hu with ⟨u, hup⟩
    have hp := Nat.le_min.mp u.p_le
    omega

end YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant

#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.firstThirdShift_measure_lt
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.firstSecondShift_measure_lt
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.innerPeel_measure_lt
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.fullJacobiThrough_of_measure_step
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.fullJacobi_all_of_measure_step
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.reducedFullFamily_of_fullJacobiBelow
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.liftedFamily_of_fullJacobiBelow
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.jacobiLiftedPackage_of_full_and_below
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.JacobiLiftedPackage.higherHeightCorrection
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.positiveCorrectionBaseRegimes
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant.upperOrderZero_outerShift_fence
