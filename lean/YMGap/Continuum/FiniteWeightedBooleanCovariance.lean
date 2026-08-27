/-
# Boolean covariance of a finite weighted law

For any finite weighted carrier and two Boolean predicates, this module
proves the exact identity

  P(A and B) - P(A) P(B) = (TT * FF - TF * FT) / Z^2.

The theorem is independent of lattice geometry and representation theory.
It is the reusable algebraic compiler from a four-cell determinant estimate
to an ordinary centered Boolean covariance estimate.

Constructive contract: finite Boolean filters and exact rational quotient
algebra only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockProbabilityCovariance

namespace YMGap.Continuum.FiniteWeightedBooleanCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalTwoBlockProbabilityCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem divPos_numerator_eqv_local {p p' q : Q'}
    (hq : (0 : Q') < q) (hp : p ≈ p') :
    Q'.divPos p q hq ≈ Q'.divPos p' q hq := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ hp

private theorem filter_and_eq_filter_filter {A : Type}
    (first second : A → Bool) (ambient : List A) :
    ambient.filter (fun item => first item && second item) =
      (ambient.filter first).filter second := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (first item) (second item)

private theorem filters_commute {A : Type}
    (first second : A → Bool) (ambient : List A) :
    (ambient.filter first).filter second =
      (ambient.filter second).filter first := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (second item) (first item)

private theorem filter_and_eq_reverse_filter_filter {A : Type}
    (first second : A → Bool) (ambient : List A) :
    ambient.filter (fun item => first item && second item) =
      (ambient.filter second).filter first :=
  Eq.trans (filter_and_eq_filter_filter first second ambient)
    (filters_commute first second ambient)

/-! ## 1. Four cells and event probabilities -/

def finiteWeightedEventMass {A : Type}
    (states : List A) (weight : A → Q') (event : A → Bool) : Q' :=
  listQSum weight (states.filter event)

def finiteWeightedEventProbability {A : Type}
    (states : List A) (weight : A → Q')
    (partition : Q') (partition_pos : (0 : Q') < partition)
    (event : A → Bool) : Q' :=
  Q'.divPos (finiteWeightedEventMass states weight event)
    partition partition_pos

def finiteWeightedBooleanCovariance {A : Type}
    (states : List A) (weight : A → Q')
    (partition : Q') (partition_pos : (0 : Q') < partition)
    (first second : A → Bool) : Q' :=
  finiteWeightedEventProbability states weight partition partition_pos
      (fun state => first state && second state) -
    finiteWeightedEventProbability states weight partition partition_pos
        first *
      finiteWeightedEventProbability states weight partition partition_pos
        second

def finiteWeightedTT {A : Type}
    (states : List A) (weight : A → Q')
    (first second : A → Bool) : Q' :=
  finiteWeightedEventMass states weight
    (fun state => first state && second state)

def finiteWeightedTF {A : Type}
    (states : List A) (weight : A → Q')
    (first second : A → Bool) : Q' :=
  finiteWeightedEventMass states weight
    (fun state => first state && !(second state))

def finiteWeightedFT {A : Type}
    (states : List A) (weight : A → Q')
    (first second : A → Bool) : Q' :=
  finiteWeightedEventMass states weight
    (fun state => !(first state) && second state)

def finiteWeightedFF {A : Type}
    (states : List A) (weight : A → Q')
    (first second : A → Bool) : Q' :=
  finiteWeightedEventMass states weight
    (fun state => !(first state) && !(second state))

def finiteWeightedFourCellCrossNumerator {A : Type}
    (states : List A) (weight : A → Q')
    (first second : A → Bool) : Q' :=
  finiteWeightedTT states weight first second *
      finiteWeightedFF states weight first second -
    finiteWeightedFT states weight first second *
      finiteWeightedTF states weight first second

def finiteWeightedNormalizedFourCellCovariance {A : Type}
    (states : List A) (weight : A → Q')
    (partition : Q') (partition_pos : (0 : Q') < partition)
    (first second : A → Bool) : Q' :=
  Q'.divPos
    (finiteWeightedFourCellCrossNumerator states weight first second)
    (partition * partition) (Q'.mul_pos partition_pos partition_pos)

/-! ## 2. Exact four-cell partition -/

theorem finiteWeightedFirstEventMass_eqv_TT_add_TF {A : Type}
    (states : List A) (weight : A → Q')
    (first second : A → Bool) :
    finiteWeightedEventMass states weight first ≈
      finiteWeightedTT states weight first second +
        finiteWeightedTF states weight first second := by
  have hsplit := listQSum_filter_partition weight second
    (states.filter first)
  unfold finiteWeightedEventMass finiteWeightedTT finiteWeightedTF
  rw [← filter_and_eq_filter_filter first second,
    ← filter_and_eq_filter_filter first (fun state => !(second state))]
    at hsplit
  exact hsplit

theorem finiteWeightedSecondEventMass_eqv_TT_add_FT {A : Type}
    (states : List A) (weight : A → Q')
    (first second : A → Bool) :
    finiteWeightedEventMass states weight second ≈
      finiteWeightedTT states weight first second +
        finiteWeightedFT states weight first second := by
  have hsplit := listQSum_filter_partition weight first
    (states.filter second)
  unfold finiteWeightedEventMass finiteWeightedTT finiteWeightedFT
  rw [← filter_and_eq_reverse_filter_filter first second,
    ← filter_and_eq_reverse_filter_filter
      (fun state => !(first state)) second] at hsplit
  exact hsplit

theorem finiteWeightedPartition_eqv_fourCells {A : Type}
    (states : List A) (weight : A → Q')
    (first second : A → Bool) :
    listQSum weight states ≈
      (finiteWeightedTT states weight first second +
        finiteWeightedTF states weight first second) +
      (finiteWeightedFT states weight first second +
        finiteWeightedFF states weight first second) := by
  have hsplit := listQSum_filter_partition weight first states
  have htrue := finiteWeightedFirstEventMass_eqv_TT_add_TF
    states weight first second
  have hfalse := finiteWeightedFirstEventMass_eqv_TT_add_TF
    states weight (fun state => !(first state)) second
  unfold finiteWeightedEventMass at htrue hfalse
  refine Q'.eqv_trans _ _ _ hsplit ?_
  exact Q'.add_eqv_congr' htrue hfalse

private theorem fourCellCross_eqv_jointCross
    (tt tf ft ff z : Q')
    (hz : z ≈ (tt + tf) + (ft + ff)) :
    tt * z - (tt + tf) * (tt + ft) ≈ tt * ff - ft * tf := by
  refine Q'.eqv_trans _
    (tt * ((tt + tf) + (ft + ff)) -
      (tt + tf) * (tt + ft)) _ ?_ ?_
  · exact sub_eqv_both_local
      (mul_eqv_both_local (Q'.eqv_refl _) hz)
      (Q'.eqv_refl _)
  · refine Q'.eqv_trans _
      (((tt + tf) + (ft + ff)) * tt - (tt + tf) * (tt + ft)) _ ?_ ?_
    · exact sub_eqv_both_local
        (Q'.mul_comm_eqv tt ((tt + tf) + (ft + ff)))
        (Q'.eqv_refl _)
    refine Q'.eqv_trans _
      ((ft + ff) * tt - (tt + tf) * ft) _
      (crossDifference_split (tt + tf) (ft + ff) tt ft) ?_
    refine Q'.eqv_trans _
      ((ft + ff) * tt - ft * (tt + tf)) _ ?_ ?_
    · exact sub_eqv_both_local (Q'.eqv_refl _)
        (Q'.mul_comm_eqv (tt + tf) ft)
    refine Q'.eqv_trans _ (ff * tt - ft * tf) _
      (crossDifference_split ft ff tt tf) ?_
    exact sub_eqv_both_local
      (Q'.mul_comm_eqv ff tt) (Q'.eqv_refl _)

/-! ## 3. Covariance compiler -/

/-- **Finite Boolean covariance compiler.**  For a supplied positive total
partition equal to the carrier weight, ordinary centered Boolean covariance
is exactly the normalized four-cell determinant. -/
theorem finiteWeightedBooleanCovariance_eqv_normalizedFourCell
    {A : Type} (states : List A) (weight : A → Q')
    (partition : Q') (partition_pos : (0 : Q') < partition)
    (partition_eqv : listQSum weight states ≈ partition)
    (first second : A → Bool) :
    finiteWeightedBooleanCovariance states weight
        partition partition_pos first second ≈
      finiteWeightedNormalizedFourCellCovariance states weight
        partition partition_pos first second := by
  let tt := finiteWeightedTT states weight first second
  let tf := finiteWeightedTF states weight first second
  let ft := finiteWeightedFT states weight first second
  let ff := finiteWeightedFF states weight first second
  have hfirst := finiteWeightedFirstEventMass_eqv_TT_add_TF
    states weight first second
  have hsecond := finiteWeightedSecondEventMass_eqv_TT_add_FT
    states weight first second
  have hcarrier := finiteWeightedPartition_eqv_fourCells
    states weight first second
  have hz : partition ≈ (tt + tf) + (ft + ff) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm partition_eqv) hcarrier
  have hpfirst :
      finiteWeightedEventProbability states weight partition partition_pos
          first ≈ Q'.divPos (tt + tf) partition partition_pos := by
    unfold finiteWeightedEventProbability
    exact divPos_numerator_eqv_local partition_pos hfirst
  have hpsecond :
      finiteWeightedEventProbability states weight partition partition_pos
          second ≈ Q'.divPos (tt + ft) partition partition_pos := by
    unfold finiteWeightedEventProbability
    exact divPos_numerator_eqv_local partition_pos hsecond
  have hprobability :
      finiteWeightedBooleanCovariance states weight
          partition partition_pos first second ≈
        Q'.divPos tt partition partition_pos -
          Q'.divPos (tt + tf) partition partition_pos *
            Q'.divPos (tt + ft) partition partition_pos := by
    unfold finiteWeightedBooleanCovariance finiteWeightedEventProbability
      finiteWeightedEventMass tt
    exact sub_eqv_both_local (Q'.eqv_refl _)
      (mul_eqv_both_local hpfirst hpsecond)
  refine Q'.eqv_trans _ _ _ hprobability ?_
  have hgeneric := normalizedProductDifference_eqv_crossNumerator
    tt (tt + tf) (tt + ft) partition partition_pos
  refine Q'.eqv_trans _ _ _ hgeneric ?_
  have hcross := fourCellCross_eqv_jointCross tt tf ft ff partition hz
  have hquotient := divPos_numerator_eqv_local
    (Q'.mul_pos partition_pos partition_pos) hcross
  refine Q'.eqv_trans _ _ _ hquotient ?_
  dsimp only [tt, tf, ft, ff]
  unfold finiteWeightedNormalizedFourCellCovariance
    finiteWeightedFourCellCrossNumerator
  exact Q'.eqv_refl _

#print axioms finiteWeightedFirstEventMass_eqv_TT_add_TF
#print axioms finiteWeightedSecondEventMass_eqv_TT_add_FT
#print axioms finiteWeightedPartition_eqv_fourCells
#print axioms finiteWeightedBooleanCovariance_eqv_normalizedFourCell

end YMGap.Continuum.FiniteWeightedBooleanCovariance
