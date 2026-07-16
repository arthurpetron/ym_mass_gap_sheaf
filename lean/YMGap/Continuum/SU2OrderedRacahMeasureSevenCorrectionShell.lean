/-
# Complete physical Omega correction on the first asymmetric shell

The measure-six positive-order shell is the symmetric correction fence.
At measure seven, exact channel admissibility leaves three asymmetric
blocks.  This file evaluates their complete physical correction families and
classifies every adjacent positive-order channel triple on that shell.
-/

import YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary

namespace YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell

open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant
open YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge

/-! ## The three admissible blocks -/

def measureSeven322Lower : FixedRightCGChannel 3 2 2 3 where
  p := 0
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureSeven322Middle : FixedRightCGChannel 3 2 2 3 where
  p := 1
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureSeven322Upper : FixedRightCGChannel 3 2 2 3 where
  p := 2
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

def measureSeven232Lower : FixedRightCGChannel 2 3 2 3 where
  p := 0
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureSeven232Middle : FixedRightCGChannel 2 3 2 3 where
  p := 1
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureSeven232Upper : FixedRightCGChannel 2 3 2 3 where
  p := 2
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

def measureSeven223Lower : FixedRightCGChannel 2 2 3 3 where
  p := 0
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureSeven223Middle : FixedRightCGChannel 2 2 3 3 where
  p := 1
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureSeven223Upper : FixedRightCGChannel 2 2 3 3 where
  p := 2
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

private theorem nat_lt_four_cases (n : Nat) (h : n < 4) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega

private theorem nat_lt_three_cases (n : Nat) (h : n < 3) :
    n = 0 ∨ n = 1 ∨ n = 2 := by omega

/-- Complete physical correction on `(a,b,c;d)=(3,2,2;3)`. -/
theorem measureSeven322_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureSeven322Lower
      measureSeven322Middle measureSeven322Upper := by
  intro i j l s hi hj hl hs
  have hi' := nat_lt_four_cases i hi
  have hj' := nat_lt_three_cases j hj
  have hl' := nat_lt_three_cases l hl
  have hs' := nat_lt_four_cases s hs
  rcases hi' with rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl <;>
    unfold OmegaCorrectionThreeCarrierAt measureSeven322Lower
      measureSeven322Middle measureSeven322Upper <;> decide

/-- Complete physical correction on `(a,b,c;d)=(2,3,2;3)`. -/
theorem measureSeven232_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureSeven232Lower
      measureSeven232Middle measureSeven232Upper := by
  intro i j l s hi hj hl hs
  have hi' := nat_lt_three_cases i hi
  have hj' := nat_lt_four_cases j hj
  have hl' := nat_lt_three_cases l hl
  have hs' := nat_lt_four_cases s hs
  rcases hi' with rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl <;>
    unfold OmegaCorrectionThreeCarrierAt measureSeven232Lower
      measureSeven232Middle measureSeven232Upper <;> decide

/-- Complete physical correction on `(a,b,c;d)=(2,2,3;3)`. -/
theorem measureSeven223_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureSeven223Lower
      measureSeven223Middle measureSeven223Upper := by
  intro i j l s hi hj hl hs
  have hi' := nat_lt_three_cases i hi
  have hj' := nat_lt_three_cases j hj
  have hl' := nat_lt_four_cases l hl
  have hs' := nat_lt_four_cases s hs
  rcases hi' with rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl <;>
    unfold OmegaCorrectionThreeCarrierAt measureSeven223Lower
      measureSeven223Middle measureSeven223Upper <;> decide

/-! ## Exhaustion of the shell -/

private theorem fixedRight_eq_of_p_r {a b c d : Nat}
    (q q' : FixedRightCGChannel a b c d)
    (hp : q.p = q'.p) (hr : q.r = q'.r) : q = q' := by
  cases q with
  | mk p p_le r r_le degree_eq =>
      cases q' with
      | mk p' p_le' r' r_le' degree_eq' =>
          dsimp only at hp hr
          subst p'
          subst r'
          rfl

/-- Measure six has exactly the symmetric correction-fence block. -/
theorem measureSix_adjacent_classification {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = 6)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) :
    a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 2 ∧
      qm.p = 0 ∧ qm.r = 2 ∧ q.p = 1 ∧ q.r = 1 ∧
      qp.p = 2 ∧ qp.r = 0 := by
  have hqmP := Nat.le_min.mp qm.p_le
  have hqP := Nat.le_min.mp q.p_le
  have hqpP := Nat.le_min.mp qp.p_le
  have hqmR := Nat.le_min.mp qm.r_le
  have hqR := Nat.le_min.mp q.r_le
  have hqpR := Nat.le_min.mp qp.r_le
  have hqmD := qm.degree_eq
  have hqD := q.degree_eq
  have hqpD := qp.degree_eq
  unfold rightLabelMeasure at hmeasure
  exact ⟨by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega⟩

/-- Universal form of the frozen symmetric measure-six correction base. -/
theorem omegaCorrectionPhysical_measureSix {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = 6)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) :
    OmegaCorrectionPhysicalCoordinateFamily qm q qp := by
  rcases measureSix_adjacent_classification
      qm q qp hmeasure hp hprev hnext with
    ⟨rfl, rfl, rfl, rfl, hmp, hmr, hqp, hqr, hpp, hpr⟩
  have hmEq : qm = correctionFenceLower :=
    fixedRight_eq_of_p_r qm correctionFenceLower hmp hmr
  have hqEq : q = correctionFenceMiddle :=
    fixedRight_eq_of_p_r q correctionFenceMiddle hqp hqr
  have hpEq : qp = correctionFenceUpper :=
    fixedRight_eq_of_p_r qp correctionFenceUpper hpp hpr
  subst qm
  subst q
  subst qp
  intro i j l s hi hj hl hs
  exact correctionFence_mutualMeasureBase.2.2.2 i j l s hi hj hl hs

/-- Admissibility completely classifies an adjacent positive-order triple
on measure seven. -/
theorem measureSeven_adjacent_classification {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = 7)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) :
    ((a = 3 ∧ b = 2 ∧ c = 2) ∨
      (a = 2 ∧ b = 3 ∧ c = 2) ∨
      (a = 2 ∧ b = 2 ∧ c = 3)) ∧
    d = 3 ∧ qm.p = 0 ∧ qm.r = 2 ∧
      q.p = 1 ∧ q.r = 1 ∧ qp.p = 2 ∧ qp.r = 0 := by
  have hqmP := Nat.le_min.mp qm.p_le
  have hqP := Nat.le_min.mp q.p_le
  have hqpP := Nat.le_min.mp qp.p_le
  have hqmR := Nat.le_min.mp qm.r_le
  have hqR := Nat.le_min.mp q.r_le
  have hqpR := Nat.le_min.mp qp.r_le
  have hqmD := qm.degree_eq
  have hqD := q.degree_eq
  have hqpD := qp.degree_eq
  unfold rightLabelMeasure at hmeasure
  have ha : 2 ≤ a := by omega
  have hb : 2 ≤ b := by omega
  have hc : 2 ≤ c := by omega
  have hlabels :
      (a = 3 ∧ b = 2 ∧ c = 2) ∨
        (a = 2 ∧ b = 3 ∧ c = 2) ∨
        (a = 2 ∧ b = 2 ∧ c = 3) := by
    by_cases ha2 : a = 2
    · by_cases hb2 : b = 2
      · exact Or.inr (Or.inr ⟨ha2, hb2, by omega⟩)
      · exact Or.inr (Or.inl ⟨ha2, by omega, by omega⟩)
    · exact Or.inl ⟨by omega, by omega, by omega⟩
  exact ⟨hlabels, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega⟩

/-- Every adjacent positive-order block on measure seven has the complete
physical Omega correction family. -/
theorem omegaCorrectionPhysical_measureSeven {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = 7)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) :
    OmegaCorrectionPhysicalCoordinateFamily qm q qp := by
  have hclass := measureSeven_adjacent_classification
    qm q qp hmeasure hp hprev hnext
  rcases hclass with ⟨hlabels, hd, hmp, hmr, hqp, hqr, hpp, hpr⟩
  rcases hlabels with h322 | h232 | h223
  · rcases h322 with ⟨rfl, rfl, rfl⟩
    subst d
    have hmEq : qm = measureSeven322Lower :=
      fixedRight_eq_of_p_r qm measureSeven322Lower hmp hmr
    have hqEq : q = measureSeven322Middle :=
      fixedRight_eq_of_p_r q measureSeven322Middle hqp hqr
    have hpEq : qp = measureSeven322Upper :=
      fixedRight_eq_of_p_r qp measureSeven322Upper hpp hpr
    subst qm
    subst q
    subst qp
    exact measureSeven322_correctionPhysical
  · rcases h232 with ⟨rfl, rfl, rfl⟩
    subst d
    have hmEq : qm = measureSeven232Lower :=
      fixedRight_eq_of_p_r qm measureSeven232Lower hmp hmr
    have hqEq : q = measureSeven232Middle :=
      fixedRight_eq_of_p_r q measureSeven232Middle hqp hqr
    have hpEq : qp = measureSeven232Upper :=
      fixedRight_eq_of_p_r qp measureSeven232Upper hpp hpr
    subst qm
    subst q
    subst qp
    exact measureSeven232_correctionPhysical
  · rcases h223 with ⟨rfl, rfl, rfl⟩
    subst d
    have hmEq : qm = measureSeven223Lower :=
      fixedRight_eq_of_p_r qm measureSeven223Lower hmp hmr
    have hqEq : q = measureSeven223Middle :=
      fixedRight_eq_of_p_r q measureSeven223Middle hqp hqr
    have hpEq : qp = measureSeven223Upper :=
      fixedRight_eq_of_p_r qp measureSeven223Upper hpp hpr
    subst qm
    subst q
    subst qp
    exact measureSeven223_correctionPhysical

/-- No adjacent positive-order block exists below measure six, so the two
classified shells give the complete physical correction family through
measure seven. -/
theorem omegaCorrectionPhysical_throughSeven {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c ≤ 7)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) :
    OmegaCorrectionPhysicalCoordinateFamily qm q qp := by
  have hqmP := Nat.le_min.mp qm.p_le
  have hqP := Nat.le_min.mp q.p_le
  have hqpP := Nat.le_min.mp qp.p_le
  have hqmR := Nat.le_min.mp qm.r_le
  have hqmD := qm.degree_eq
  have hqD := q.degree_eq
  have hqpD := qp.degree_eq
  have hlower : 6 ≤ rightLabelMeasure a b c := by
    unfold rightLabelMeasure
    omega
  by_cases h6 : rightLabelMeasure a b c = 6
  · exact omegaCorrectionPhysical_measureSix
      qm q qp h6 hp hprev hnext
  · have h7 : rightLabelMeasure a b c = 7 := by omega
    exact omegaCorrectionPhysical_measureSeven
      qm q qp h7 hp hprev hnext

end YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell

#print axioms YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell.measureSeven322_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell.measureSeven232_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell.measureSeven223_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell.measureSix_adjacent_classification
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell.omegaCorrectionPhysical_measureSix
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell.measureSeven_adjacent_classification
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell.omegaCorrectionPhysical_measureSeven
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell.omegaCorrectionPhysical_throughSeven
