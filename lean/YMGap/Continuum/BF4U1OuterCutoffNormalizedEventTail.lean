/-
# Normalized outer-cutoff event tails for the canonical BF4 U(1) slab

The outer-cutoff Fubini estimate controls the unnormalized mass added between
two canonical charge cutoffs.  This module proves the exact finite rational
normalization algebra needed to transfer that estimate to every Boolean
event.

For nested nonnegative masses

  * old event mass `a`, old partition `d`,
  * new event mass `b`, new total mass `n`,

with `a ≤ d`, `b ≤ n`, and `1 ≤ d`, the normalized probabilities
`a / d` and `(a + b) / (d + n)` differ by at most `n`.  Thus the canonical
U(1) slab inherits the same outer-cutoff-independent tensor envelope as its
unnormalized new sector, without a carrier-cardinality loss.

This is a fixed-nome, fixed-geometry, finite-volume theorem.  It does not take
the spacing limit, vary the nome toward one, construct an infinite-volume
measure, or prove the corresponding SU(2) estimate.
-/

import YMGap.Continuum.BF4U1OuterCutoffFiniteFubiniTail
import YMGap.Continuum.BF4U1OuterCutoffTensorTailModulus
import YMGap.Continuum.FusionMarginMono
import YMGap.Continuum.FusionResidualBound
import YMGap.Continuum.VacNormEigShift

namespace YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4U1OuterCutoffFiniteFubiniTail
open YMGap.Continuum.BF4U1OuterCutoffNesting
open YMGap.Continuum.BF4U1OuterCutoffTensorTailModulus
open YMGap.Continuum.BF4U1OuterCutoffUniformTensorTail
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FusionMarginMono
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local
    (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic|
    (show _ * (_ : Int) = _ * (_ : Int)
     simp only [Q'.add_num_cast, Q'.add_den_cast,
       Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
       neg_num_cast_local, Int.add_mul, Int.mul_add,
       Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
       Int.one_mul, Int.mul_one]
     ac_rfl))

/-! ## 1. Exact quotient-difference algebra -/

private theorem positive_of_one_le_local
    {q : Q'} (hq : (1 : Q') ≤ q) :
    (0 : Q') < q :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide) hq

private theorem add_nonnegative_local
    {a b : Q'} (ha : (0 : Q') ≤ a)
    (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a + b := by
  have h := Q'.add_le_add ha hb
  rw [Q'.zero_add'] at h
  exact h

private theorem one_le_add_nonnegative_local
    {d n : Q'} (hd : (1 : Q') ≤ d)
    (hn : (0 : Q') ≤ n) :
    (1 : Q') ≤ d + n :=
  Q'.le_trans' _ _ _ hd
    (Q'.add_le_self_of_nonneg d n hn)

/-- Exact quotient-difference identity over the product denominator.

This is the constructive rational identity

`a/d - A/D = (aD - Ad)/(dD)`.

The positive-denominator proofs are explicit data and no field quotient or
choice principle is used. -/
theorem divPos_sub_divPos_eq_crossDifference
    (a A d D : Q')
    (hd : (0 : Q') < d) (hD : (0 : Q') < D) :
    Q'.divPos a d hd + -(Q'.divPos A D hD) ≈
      Q'.divPos
        (a * D + -(A * d))
        (d * D) (Q'.mul_pos hd hD) := by
  apply Q'.eqv_symm
  apply divPos_eqv_of_eqv_mul
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _
    ((Q'.divPos a d hd * d) * D +
      -((Q'.divPos A D hD * D) * d)) _ ?_ ?_
  · ring_qeqv
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ D
        (Q'.divPos_mul_eqv a d hd))
      (Q'.neg_eqv_congr
        _ _
        (Q'.mul_eqv_congr_right _ _ d
          (Q'.divPos_mul_eqv A D hD)))

/-- The exact quotient-difference identity in the nested presentation. -/
theorem nested_divPos_difference_exact
    (a b d n : Q')
    (hd : (0 : Q') < d)
    (hD : (0 : Q') < d + n) :
    Q'.divPos a d hd +
        -(Q'.divPos (a + b) (d + n) hD) ≈
      Q'.divPos
        (a * (d + n) + -((a + b) * d))
        (d * (d + n)) (Q'.mul_pos hd hD) := by
  exact divPos_sub_divPos_eq_crossDifference
    a (a + b) d (d + n) hd hD

/-! ## 2. Sharp normalized stability under a nested nonnegative extension -/

private theorem divPos_add_num_eqv
    (p q d : Q') (hd : (0 : Q') < d) :
    Q'.divPos (p + q) d hd ≈
      Q'.divPos p d hd + Q'.divPos q d hd := by
  unfold Q'.divPos
  exact Q'.add_mul_eqv p q (Q'.recipPos d hd)

private theorem divPos_le_self_of_one_le
    {p d : Q'} (hp : (0 : Q') ≤ p)
    (hd1 : (1 : Q') ≤ d) :
    Q'.divPos p d (positive_of_one_le_local hd1) ≤ p := by
  apply Q'.divPos_le_of_le_mul
  have hmul :
      p * (1 : Q') ≤ p * d :=
    Q'.mul_le_mul_of_nonneg_left
      _ _ _ hd1 hp
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_one_eqv p)) hmul

private theorem nested_probability_large_le_old_add_new
    {a b d n : Q'}
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (hn : (0 : Q') ≤ n)
    (hd1 : (1 : Q') ≤ d) (hbn : b ≤ n) :
    Q'.divPos (a + b) (d + n)
        (positive_of_one_le_local
          (one_le_add_nonnegative_local hd1 hn)) ≤
      Q'.divPos a d
          (positive_of_one_le_local hd1) + n := by
  let hd := positive_of_one_le_local hd1
  let hD :=
    positive_of_one_le_local
      (one_le_add_nonnegative_local hd1 hn)
  have hab0 : (0 : Q') ≤ a + b :=
    add_nonnegative_local ha hb
  have hden : d ≤ d + n :=
    Q'.add_le_self_of_nonneg d n hn
  have hdrop :
      Q'.divPos (a + b) (d + n) hD ≤
        Q'.divPos (a + b) d hd := by
    apply divPos_le_divPos_of_cross
    exact Q'.mul_le_mul_of_nonneg_left
      _ _ _ hden hab0
  have hsplit :
      Q'.divPos (a + b) d hd ≈
        Q'.divPos a d hd +
          Q'.divPos b d hd :=
    divPos_add_num_eqv a b d hd
  have hbdiv :
      Q'.divPos b d hd ≤ n := by
    refine Q'.le_trans' _ _ _
      (divPos_le_self_of_one_le hb hd1) hbn
  exact Q'.le_trans' _ _ _ hdrop
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hsplit)
      (Q'.add_le_add_left _ _ _ hbdiv))

private theorem nested_probability_old_le_large_add_new
    {a b d n : Q'}
    (hb : (0 : Q') ≤ b)
    (hn : (0 : Q') ≤ n)
    (hd1 : (1 : Q') ≤ d) (had : a ≤ d) :
    Q'.divPos a d
        (positive_of_one_le_local hd1) ≤
      Q'.divPos (a + b) (d + n)
          (positive_of_one_le_local
            (one_le_add_nonnegative_local hd1 hn)) + n := by
  let hd := positive_of_one_le_local hd1
  let hD :=
    positive_of_one_le_local
      (one_le_add_nonnegative_local hd1 hn)
  have hn_mul :
      a * n ≤ d * n :=
    Q'.mul_le_mul_of_nonneg_right
      _ _ _ had hn
  have hcross :
      a * (d + n) ≤ (a + n) * d := by
    have hexpandLeft :
        a * (d + n) ≤ a * d + a * n :=
      Q'.le_of_eqv
        (Q'.mul_add_eqv a d n)
    have hmiddle :
        a * d + a * n ≤ a * d + d * n :=
      Q'.add_le_add_left _ _ _ hn_mul
    have hexpandRight :
        a * d + d * n ≤ (a + n) * d :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.add_eqv_congr_left
            (a * d) (d * n) (n * d)
            (Q'.mul_comm_eqv d n)))
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.add_mul_eqv a n d)))
    exact Q'.le_trans' _ _ _ hexpandLeft
      (Q'.le_trans' _ _ _ hmiddle hexpandRight)
  have hfirst :
      Q'.divPos a d hd ≤
        Q'.divPos (a + n) (d + n) hD :=
    divPos_le_divPos_of_cross
      a d (a + n) (d + n) hd hD hcross
  have hnum :
      a + n ≤ (a + b) + n := by
    exact Q'.add_le_add_right _ _ n
      (Q'.add_le_self_of_nonneg a b hb)
  have hsecond :
      Q'.divPos (a + n) (d + n) hD ≤
        Q'.divPos ((a + b) + n) (d + n) hD := by
    apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ hnum
      (Q'.ge_of_eqv
        (Q'.divPos_mul_eqv
          ((a + b) + n) (d + n) hD))
  have hsplit :
      Q'.divPos ((a + b) + n) (d + n) hD ≈
        Q'.divPos (a + b) (d + n) hD +
          Q'.divPos n (d + n) hD :=
    divPos_add_num_eqv (a + b) n (d + n) hD
  have hnDiv :
      Q'.divPos n (d + n) hD ≤ n := by
    exact divPos_le_self_of_one_le hn
      (one_le_add_nonnegative_local hd1 hn)
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv hsplit)
        (Q'.add_le_add_left _ _ _ hnDiv)))

/-- Sharp Boolean-event normalization lemma for a nested finite law.

The absolute change of normalized event mass is at most the total mass `n`
of the new sector. -/
theorem nested_normalized_event_abs_le_newMass
    {a b d n : Q'}
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (hn : (0 : Q') ≤ n)
    (hd1 : (1 : Q') ≤ d)
    (had : a ≤ d) (hbn : b ≤ n) :
    absQ
        (Q'.divPos a d
            (positive_of_one_le_local hd1) +
          -(Q'.divPos (a + b) (d + n)
            (positive_of_one_le_local
              (one_le_add_nonnegative_local hd1 hn)))) ≤
      n := by
  apply absQ_le
  · have h :=
      nested_probability_large_le_old_add_new
        ha hb hn hd1 hbn
    have hneg := Q'.neg_le_neg h
    have hadd :=
      Q'.add_le_add_left
        (Q'.divPos a d
          (positive_of_one_le_local hd1))
        _ _ hneg
    refine Q'.le_trans' _ _ _ ?_ hadd
    let old :=
      Q'.divPos a d
        (positive_of_one_le_local hd1)
    have heq :
        old + -(old + n) ≈ -n := by
      refine Q'.eqv_trans _
        (old + (-old + -n)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left
          old _ _
          (Q'.neg_add_eqv old n)
      · refine Q'.eqv_trans _
          ((old + -old) + -n) _ ?_ ?_
        · exact Q'.eqv_symm
            (Q'.add_assoc_eqv old (-old) (-n))
        · refine Q'.eqv_trans _
            ((0 : Q') + -n) _ ?_ ?_
          · exact Q'.add_eqv_congr_right
              _ _ (-n)
              (Q'.add_neg_self_eqv old)
          · exact QPoly.q_zero_add_eqv (-n)
    exact Q'.le_of_eqv
      (Q'.eqv_symm heq)
  · have h :=
      nested_probability_old_le_large_add_new
        hb hn hd1 had
    have hadd :
        Q'.divPos a d
              (positive_of_one_le_local hd1) +
            -(Q'.divPos (a + b) (d + n)
              (positive_of_one_le_local
                (one_le_add_nonnegative_local hd1 hn))) ≤
          (Q'.divPos (a + b) (d + n)
                (positive_of_one_le_local
                  (one_le_add_nonnegative_local hd1 hn)) + n) +
            -(Q'.divPos (a + b) (d + n)
              (positive_of_one_le_local
                (one_le_add_nonnegative_local hd1 hn))) :=
      Q'.add_le_add_right
        (Q'.divPos a d
          (positive_of_one_le_local hd1))
        (Q'.divPos (a + b) (d + n)
          (positive_of_one_le_local
            (one_le_add_nonnegative_local hd1 hn)) + n)
        (-(Q'.divPos (a + b) (d + n)
          (positive_of_one_le_local
            (one_le_add_nonnegative_local hd1 hn)))) h
    refine Q'.le_trans' _ _ _ hadd ?_
    let large :=
      Q'.divPos (a + b) (d + n)
        (positive_of_one_le_local
          (one_le_add_nonnegative_local hd1 hn))
    have heq :
        (large + n) + -large ≈ n := by
      refine Q'.eqv_trans _
        (large + (n + -large)) _ ?_ ?_
      · exact Q'.add_assoc_eqv
          large n (-large)
      · refine Q'.eqv_trans _
          (large + (-large + n)) _ ?_ ?_
        · exact Q'.add_eqv_congr_left
            large _ _
            (Q'.add_comm_eqv n (-large))
        · refine Q'.eqv_trans _
            ((large + -large) + n) _ ?_ ?_
          · exact Q'.eqv_symm
              (Q'.add_assoc_eqv
                large (-large) n)
          · refine Q'.eqv_trans _
              ((0 : Q') + n) _ ?_ ?_
            · exact Q'.add_eqv_congr_right
                _ _ n
                (Q'.add_neg_self_eqv large)
            · exact QPoly.q_zero_add_eqv n
    exact Q'.le_of_eqv heq

/-! ## 3. Boolean events on the canonical U(1) slab -/

def canonicalU1SlabEventNumerator
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (event : ChargeLabelling → Bool) : Q' :=
  let D := canonicalU1Slab w hw half K
  listQSum
    (fun state =>
      if event state then D.physicalTerm state else 0)
    D.states

def canonicalU1SlabNewEventMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K L : Nat)
    (event : ChargeLabelling → Bool) : Q' :=
  let D := canonicalU1Slab w hw half L
  listQSum
    (fun state =>
      if event state then D.physicalTerm state else 0)
    (newChargeSector w hw half K L)

def canonicalU1SlabEventProbability
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (event : ChargeLabelling → Bool) : Q' :=
  let D := canonicalU1Slab w hw half K
  Q'.divPos
    (canonicalU1SlabEventNumerator
      w hw half K event)
    D.partition D.partition_pos

private theorem listQSum_nonnegative_local
    {A : Type} (weight : A → Q')
    (hweight : ∀ item, (0 : Q') ≤ weight item) :
    ∀ source : List A,
      (0 : Q') ≤ listQSum weight source
  | [] => Q'.le_refl' 0
  | head :: tail =>
      add_nonnegative_local
        (hweight head)
        (listQSum_nonnegative_local
          weight hweight tail)

private theorem listQSum_mono_local
    {A : Type} (lower upper : A → Q') :
    ∀ source : List A,
      (∀ item, item ∈ source →
        lower item ≤ upper item) →
      listQSum lower source ≤
        listQSum upper source
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpoint =>
      Q'.add_le_add
        (hpoint head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hmem =>
            hpoint item
              (List.mem_cons_of_mem head hmem)))

private theorem eventPhysicalTerm_nonnegative
    (D : U1SlabData)
    (event : ChargeLabelling → Bool)
    (state : ChargeLabelling) :
    (0 : Q') ≤
      (if event state
        then D.physicalTerm state else 0) := by
  cases hevent : event state
  · exact Q'.le_refl' 0
  · exact D.physicalTerm_nonnegative state

theorem canonicalU1SlabEventNumerator_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (event : ChargeLabelling → Bool) :
    (0 : Q') ≤
      canonicalU1SlabEventNumerator
        w hw half K event := by
  unfold canonicalU1SlabEventNumerator
  exact listQSum_nonnegative_local _
    (eventPhysicalTerm_nonnegative
      (canonicalU1Slab w hw half K) event)
    (canonicalU1Slab w hw half K).states

theorem canonicalU1SlabNewEventMass_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K L : Nat)
    (event : ChargeLabelling → Bool) :
    (0 : Q') ≤
      canonicalU1SlabNewEventMass
        w hw half K L event := by
  unfold canonicalU1SlabNewEventMass
  exact listQSum_nonnegative_local _
    (eventPhysicalTerm_nonnegative
      (canonicalU1Slab w hw half L) event)
    (newChargeSector w hw half K L)

theorem canonicalU1SlabEventNumerator_le_partition
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (event : ChargeLabelling → Bool) :
    canonicalU1SlabEventNumerator
        w hw half K event ≤
      (canonicalU1Slab w hw half K).partition := by
  unfold canonicalU1SlabEventNumerator
    U1SlabData.partition
  apply listQSum_mono_local
  intro state _
  cases hevent : event state
  · exact (canonicalU1Slab
      w hw half K).physicalTerm_nonnegative state
  · exact Q'.le_refl' _

theorem canonicalU1SlabNewEventMass_le_newChargeSectorMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K L : Nat)
    (event : ChargeLabelling → Bool) :
    canonicalU1SlabNewEventMass
        w hw half K L event ≤
      newChargeSectorMass w hw half K L := by
  unfold canonicalU1SlabNewEventMass
    newChargeSectorMass
  apply listQSum_mono_local
  intro state _
  cases hevent : event state
  · exact (canonicalU1Slab
      w hw half L).physicalTerm_nonnegative state
  · exact Q'.le_refl' _

theorem canonicalU1SlabEventNumerator_decomposition
    (w : Q') (hw : (0 : Q') ≤ w)
    (half : Nat) {K L : Nat} (hKL : K ≤ L)
    (event : ChargeLabelling → Bool) :
    canonicalU1SlabEventNumerator
        w hw half L event ≈
      canonicalU1SlabEventNumerator
          w hw half K event +
        canonicalU1SlabNewEventMass
          w hw half K L event := by
  let large := canonicalU1Slab w hw half L
  let small := canonicalU1Slab w hw half K
  let eventTerm : ChargeLabelling → Q' :=
    fun state =>
      if event state
        then large.physicalTerm state else 0
  have hsplit :=
    listQSum_filter_partition
      eventTerm (oldChargeWindow half K)
      large.states
  have holdCarrier :
      large.states.filter (oldChargeWindow half K) =
        small.states :=
    canonicalU1Slab_states_filter
      w hw half hKL
  have hold :
      listQSum eventTerm
          (large.states.filter
            (oldChargeWindow half K)) ≈
        canonicalU1SlabEventNumerator
          w hw half K event := by
    rw [holdCarrier]
    unfold canonicalU1SlabEventNumerator
    apply listQSum_congr
    intro state
    cases hevent : event state
    · simp only [eventTerm, hevent,
        Bool.false_eq_true, ↓reduceIte]
      exact Q'.eqv_refl 0
    · simp only [eventTerm, hevent, ↓reduceIte]
      exact Q'.eqv_of_eq
        (canonicalU1Slab_physicalTerm_stable
          w hw half K L state)
  have hnew :
      listQSum eventTerm
          (large.states.filter
            (fun state =>
              !(oldChargeWindow half K state))) ≈
        canonicalU1SlabNewEventMass
          w hw half K L event := by
    unfold canonicalU1SlabNewEventMass
      newChargeSector
    exact Q'.eqv_refl _
  unfold canonicalU1SlabEventNumerator
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr' hold hnew)

/-! ## 4. Outer-cutoff-uniform normalized event tail -/

theorem canonicalU1SlabEventProbability_outerCutoff_abs_le_newMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (half : Nat) {K L : Nat} (hKL : K ≤ L)
    (event : ChargeLabelling → Bool) :
    absQ
        (canonicalU1SlabEventProbability
            w hw half K event +
          -canonicalU1SlabEventProbability
            w hw half L event) ≤
      newChargeSectorMass w hw half K L := by
  let a :=
    canonicalU1SlabEventNumerator
      w hw half K event
  let b :=
    canonicalU1SlabNewEventMass
      w hw half K L event
  let d :=
    (canonicalU1Slab w hw half K).partition
  let n :=
    newChargeSectorMass w hw half K L
  let A :=
    canonicalU1SlabEventNumerator
      w hw half L event
  let D :=
    (canonicalU1Slab w hw half L).partition
  have ha :=
    canonicalU1SlabEventNumerator_nonnegative
      w hw half K event
  have hb :=
    canonicalU1SlabNewEventMass_nonnegative
      w hw half K L event
  have hn :=
    newChargeSectorMass_nonnegative
      w hw half K L
  have hd1 :=
    (canonicalU1Slab
      w hw half K).partition_one_le
  have had :=
    canonicalU1SlabEventNumerator_le_partition
      w hw half K event
  have hbn :=
    canonicalU1SlabNewEventMass_le_newChargeSectorMass
      w hw half K L event
  have hbase :=
    nested_normalized_event_abs_le_newMass
      ha hb hn hd1 had hbn
  have hA :
      A ≈ a + b :=
    canonicalU1SlabEventNumerator_decomposition
      w hw half hKL event
  have hD :
      D ≈ d + n :=
    canonicalU1Slab_partition_decomposition
      w hw half hKL
  unfold canonicalU1SlabEventProbability
  dsimp only [a, b, d, n, A, D] at hbase hA hD
  dsimp only [a, b, d, n, A, D]
  -- Normalize the larger numerator and denominator to the exact nested form.
  have hlarge :
      Q'.divPos A D
          (canonicalU1Slab w hw half L).partition_pos ≈
        Q'.divPos (a + b) (d + n)
          (positive_of_one_le_local
            (one_le_add_nonnegative_local hd1 hn)) := by
    apply Q'.eqv_of_le_le
    · apply Q'.le_divPos_of_mul_le
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (Q'.divPos A D
              (canonicalU1Slab
                w hw half L).partition_pos)
            (d + n) D (Q'.eqv_symm hD))
          (Q'.eqv_trans _ _ _
            (Q'.divPos_mul_eqv A D
              (canonicalU1Slab
                w hw half L).partition_pos)
            hA))
    · apply Q'.le_divPos_of_mul_le
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (Q'.divPos (a + b) (d + n)
              (positive_of_one_le_local
                (one_le_add_nonnegative_local hd1 hn)))
            D (d + n) hD)
          (Q'.eqv_trans _ _ _
            (Q'.divPos_mul_eqv (a + b) (d + n)
              (positive_of_one_le_local
                (one_le_add_nonnegative_local hd1 hn)))
            (Q'.eqv_symm hA)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (YMGap.Continuum.ContinuumYMStack.absQ_eqv_congr
        (Q'.add_eqv_congr_left
          (Q'.divPos a d
            (canonicalU1Slab
              w hw half K).partition_pos)
          _
          (-(Q'.divPos (a + b) (d + n)
            (positive_of_one_le_local
              (one_le_add_nonnegative_local hd1 hn))))
          (Q'.neg_eqv_congr _ _ hlarge)))) hbase

theorem canonicalU1SlabEventProbability_outerCutoff_abs_le_tensorEnvelope
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) {K L : Nat} (hKL : K ≤ L)
    (event : ChargeLabelling → Bool) :
    absQ
        (canonicalU1SlabEventProbability
            w (Q'.le_of_lt hw0) half K event +
          -canonicalU1SlabEventProbability
            w (Q'.le_of_lt hw0) half L event) ≤
      signedChargeTensorTailEnvelope w K
        (slabPhysicalFaceEdges
          (centralExtent half)).length := by
  exact Q'.le_trans' _ _ _
    (canonicalU1SlabEventProbability_outerCutoff_abs_le_newMass
      w (Q'.le_of_lt hw0) half hKL event)
    (newChargeSectorMass_le_tensorEnvelope
      hw0 hw1 half hKL)

/-! ## 5. Explicit normalized-event Cauchy modulus -/

/-- The tensor cutoff is also a direct modulus for every Boolean event of
the normalized canonical slab law.  The retained cutoff `K` may be followed
by any larger outer cutoff `L`; the bound is independent of `L`. -/
theorem canonicalU1SlabEventProbability_outerCutoff_abs_le_of_cutoff
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    (half : Nat) {K L : Nat} (hKL : K ≤ L)
    (hK :
      signedChargeTensorTailCutoff w ε
          (slabPhysicalFaceEdges
            (centralExtent half)).length ≤ K)
    (event : ChargeLabelling → Bool) :
    absQ
        (canonicalU1SlabEventProbability
            w (Q'.le_of_lt hw0) half K event +
          -canonicalU1SlabEventProbability
            w (Q'.le_of_lt hw0) half L event) ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (canonicalU1SlabEventProbability_outerCutoff_abs_le_tensorEnvelope
      hw0 hw1 half hKL event)
    (signedChargeTensorTailEnvelope_le_of_cutoff
      hw0 hw1 hε
      (slabPhysicalFaceEdges
        (centralExtent half)).length K hK)

#print axioms divPos_sub_divPos_eq_crossDifference
#print axioms nested_divPos_difference_exact
#print axioms nested_normalized_event_abs_le_newMass
#print axioms canonicalU1SlabEventNumerator_decomposition
#print axioms canonicalU1SlabEventProbability_outerCutoff_abs_le_newMass
#print axioms canonicalU1SlabEventProbability_outerCutoff_abs_le_tensorEnvelope
#print axioms canonicalU1SlabEventProbability_outerCutoff_abs_le_of_cutoff

end YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
