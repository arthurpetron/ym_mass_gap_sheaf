/-
# Arbitrary-nome interacting SU(2) outer-cutoff tolerance

The link-incidence estimate which produces twelve powers of `(spin+1)` is
coupling-independent.  Combining it with the generic identity

  coeffW w spin * (spin+1)^12 ≈ tailTerm w 13 spin

extends the physical pointwise domination and finite-Fubini cutoff-increment
bound from the fixed strong-coupling anchor to every rational nome
`0 < w < 1`.

The executable schedule from `SU2PhysicalOuterCutoffNomeTolerance` then makes
the actual interacting increment, and consequently the change of every
normalized Boolean event, smaller than an arbitrary positive rational
tolerance, uniformly in every later outer cutoff containing the retained
window.

This remains a fixed-finite-volume theorem for each supplied `w`.  It is not
uniform as `w` approaches one and supplies no spacing or continuum limit.

## Axiom gate

No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, choice,
functional extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
import YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
import YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw

namespace YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDependentIncidenceProductBound
open YMGap.Continuum.Z4SpinSummedFaceActivityBound

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic degree-thirteen physical pointwise domination -/

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_four_regroup_local
    (A B C D : Q') :
    (A * B) * (C * D) ≈ (A * C) * (B * D) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D
      (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

private theorem ofNat_mul_eqv_local
    (left right : Nat) :
    Q'.ofNat left * Q'.ofNat right ≈
      Q'.ofNat (left * right) := by
  show (Q'.ofNat left * Q'.ofNat right).num *
      ((Q'.ofNat (left * right)).den : Int) =
    (Q'.ofNat (left * right)).num *
      ((Q'.ofNat left * Q'.ofNat right).den : Int)
  rw [Q'.mul_den_cast]
  show ((Int.ofNat left) * (Int.ofNat right)) * 1 =
    (Int.ofNat (left * right)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  omega

private theorem eliminateLinks_nonnegative_local
    (value : Nat → Q')
    (hvalue : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat,
      (0 : Q') ≤ eliminateLinks value edges
  | [] => Q'.zero_le_one
  | edge :: rest =>
      Q'.mul_nonneg _ _
        (hvalue edge)
        (eliminateLinks_nonnegative_local
          value hvalue rest)

private theorem eliminateLinks_congr_eqv_local
    (left right : Nat → Q') :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → left edge ≈ right edge) →
      eliminateLinks left edges ≈
        eliminateLinks right edges
  | [], _ => Q'.eqv_refl 1
  | edge :: rest, hagree =>
      qmul_congr_local
        (hagree edge List.mem_cons_self)
        (eliminateLinks_congr_eqv_local
          left right rest
          (fun item hitem =>
            hagree item
              (List.mem_cons_of_mem edge hitem)))

private theorem eliminateLinks_pair_natProduct_eqv_local
    (value : Nat → Q') (charge : Nat → Nat) :
    ∀ edges : List Nat,
      eliminateLinks value edges *
          Q'.ofNat (natListProduct (edges.map charge)) ≈
        eliminateLinks
          (fun edge =>
            value edge * Q'.ofNat (charge edge))
          edges
  | [] => by
      change ((1 : Q') * Q'.ofNat 1).eqv 1
      decide
  | edge :: rest => by
      simp only [eliminateLinks, List.map_cons,
        natListProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (value edge * eliminateLinks value rest)
          _ _
          (Q'.eqv_symm
            (ofNat_mul_eqv_local
              (charge edge)
              (natListProduct
                (rest.map charge))))) ?_
      refine Q'.eqv_trans _ _ _
        (mul_four_regroup_local
          (value edge)
          (eliminateLinks value rest)
          (Q'.ofNat (charge edge))
          (Q'.ofNat
            (natListProduct (rest.map charge)))) ?_
      exact Q'.mul_eqv_congr_left
        (value edge * Q'.ofNat (charge edge))
        _ _
        (eliminateLinks_pair_natProduct_eqv_local
          value charge rest)

/-- The full four-dimensional link-incidence product is bounded by the
degree-thirteen face product at every nonnegative nome.  No strong-coupling
upper bound is used. -/
theorem physicalTerm_le_degreeThirteenFaceProduct
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical :
      physical ∈ boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalTerm w K n physical ≤
      eliminateLinks
        (fun edge =>
          tailTerm w physicalFacePolynomialDegree
            (physical edge))
        (List.range (plaquetteEdgeCount n)) := by
  have hfaceEq :=
    parametricKPhysicalFaceFactor_eq_coeffWProduct
      (w := w) hphysical
  have hface0 :
      (0 : Q') ≤
        parametricKPhysicalFaceFactor
          w K n physical := by
    rw [hfaceEq]
    exact eliminateLinks_nonnegative_local _
      (fun edge =>
        coeffW_nonneg hw0 (physical edge))
      _
  have hlink :=
    explicitLinkMultiplicityProduct_le_faceTwelfthSpinProduct
      K n physical
  have hmul :=
    Q'.mul_le_mul_of_nonneg_left
      _ _ _ hlink hface0
  unfold parametricKPhysicalTerm
  rw [hfaceEq]
  rw [hfaceEq,
    boxFaceTwelfthSpinProduct_eq_rangeProduct]
    at hmul
  refine Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (eliminateLinks_pair_natProduct_eqv_local
      (fun edge => coeffW w (physical edge))
      (fun edge => (physical edge + 1) ^ 12)
      (List.range (plaquetteEdgeCount n))) ?_
  apply eliminateLinks_congr_eqv_local
  intro edge _
  simpa [physicalFacePolynomialDegree] using
    (coeffW_mul_twelfth_eqv_decoratedActivity
      w (physical edge))

/-! ## 2. Generic finite-Fubini lift to the interacting increment -/

private theorem listQSum_mono_local {A : Type}
    (left right : A → Q') :
    ∀ source : List A,
      (∀ item, item ∈ source →
        left item ≤ right item) →
      listQSum left source ≤ listQSum right source
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local left right tail
          (fun item hitem =>
            hle item
              (List.mem_cons_of_mem head hitem)))

private theorem listQSum_congr_local {A : Type}
    (left right : A → Q') :
    ∀ source : List A,
      (∀ item, left item ≈ right item) →
      listQSum left source ≈ listQSum right source
  | [], _ => Q'.eqv_refl 0
  | head :: tail, heq =>
      Q'.add_eqv_congr'
        (heq head)
        (listQSum_congr_local
          left right tail heq)

private theorem listQSum_mask_eq_filter_local
    {A : Type} (weight : A → Q')
    (event : A → Bool) :
    ∀ source : List A,
      listQSum
          (fun item =>
            if event item then weight item else 0)
          source ≈
        listQSum weight (source.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head
      · simp only [List.filter_cons, hevent,
          Bool.false_eq_true, ↓reduceIte, listQSum]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.eqv_refl 0)
            (listQSum_mask_eq_filter_local
              weight event tail))
          (Q'.eqv_of_eq (Q'.zero_add' _))
      · simp only [List.filter_cons, hevent,
          ↓reduceIte, listQSum]
        exact Q'.add_eqv_congr'
          (Q'.eqv_refl (weight head))
          (listQSum_mask_eq_filter_local
            weight event tail)

/-- The actual interacting new-label sector is bounded by the literal
degree-thirteen outside-face mass for every nonnegative nome. -/
theorem physicalCutoffIncrement_le_outsideFaceMass
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    {M K n : Nat} :
    parametricKCutoffIncrement w M K n ≤
      boundedSU2PhysicalOutsideFaceMass
        w M K
        (List.range (plaquetteEdgeCount n)) := by
  unfold parametricKCutoffIncrement
  have hterm :
      listQSum
          (parametricKPhysicalTerm w K n)
          ((boundedEdgeLabellings K
            (List.range (plaquetteEdgeCount n))).filter
              (fun state =>
                !(labelWithinB M
                  (List.range
                    (plaquetteEdgeCount n)) state))) ≤
        listQSum
          (su2PhysicalFaceProduct w
            (List.range (plaquetteEdgeCount n)))
          ((boundedEdgeLabellings K
            (List.range (plaquetteEdgeCount n))).filter
              (fun state =>
                !(labelWithinB M
                  (List.range
                    (plaquetteEdgeCount n)) state))) := by
    apply listQSum_mono_local
    intro state hstate
    exact physicalTerm_le_degreeThirteenFaceProduct
      hw0 (List.mem_filter.mp hstate).1
  refine Q'.le_trans' _ _ _ hterm ?_
  have hmask :
      boundedSU2PhysicalOutsideFaceMass
          w M K
          (List.range (plaquetteEdgeCount n)) ≈
        listQSum
          (su2PhysicalFaceProduct w
            (List.range (plaquetteEdgeCount n)))
          ((boundedEdgeLabellings K
            (List.range (plaquetteEdgeCount n))).filter
              (fun state =>
                !(labelWithinB M
                  (List.range
                    (plaquetteEdgeCount n)) state))) := by
    unfold boundedSU2PhysicalOutsideFaceMass
    refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          if !(labelWithinB M
              (List.range (plaquetteEdgeCount n)) state)
            then su2PhysicalFaceProduct w
              (List.range (plaquetteEdgeCount n)) state
            else 0)
        (boundedEdgeLabellings K
          (List.range (plaquetteEdgeCount n)))) _
      (listQSum_congr_local
        (fun state =>
          if labelWithinB M
              (List.range (plaquetteEdgeCount n)) state
            then 0
            else su2PhysicalFaceProduct w
              (List.range (plaquetteEdgeCount n)) state)
        (fun state =>
          if !(labelWithinB M
              (List.range (plaquetteEdgeCount n)) state)
            then su2PhysicalFaceProduct w
              (List.range (plaquetteEdgeCount n)) state
            else 0)
        (boundedEdgeLabellings K
          (List.range (plaquetteEdgeCount n)))
        (fun state => by
          cases hwindow :
              labelWithinB M
                (List.range
                  (plaquetteEdgeCount n)) state
          · simp [hwindow]
            exact Q'.eqv_refl _
          · simp [hwindow]
            exact Q'.eqv_refl _)) ?_
    exact listQSum_mask_eq_filter_local
      (su2PhysicalFaceProduct w
        (List.range (plaquetteEdgeCount n)))
      (fun state =>
        !(labelWithinB M
          (List.range (plaquetteEdgeCount n)) state))
      (boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount n)))
  exact Q'.ge_of_eqv hmask

private theorem range_nodup_local :
    ∀ N : Nat, (List.range N).Nodup
  | 0 => List.nodup_nil
  | N + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨range_nodup_local N,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq :=
        List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl N)
        (List.mem_range.mp hleft)

/-- The genuine interacting cutoff increment obeys the arbitrary-nome
executable total-tolerance schedule, uniformly in every later cutoff. -/
theorem physicalNomeCutoffIncrement_le_tolerance
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat) {ε : Q'} (hε : (0 : Q') < ε)
    {K : Nat}
    (hK :
      physicalNomeTensorToleranceRetainedCutoff
          w (plaquetteEdgeCount volume) ε ≤ K) :
    parametricKCutoffIncrement
        w
        (physicalNomeTensorToleranceRetainedCutoff
          w (plaquetteEdgeCount volume) ε)
        K volume ≤
      ε := by
  let retained :=
    physicalNomeTensorToleranceRetainedCutoff
      w (plaquetteEdgeCount volume) ε
  refine Q'.le_trans' _ _ _
    (physicalCutoffIncrement_le_outsideFaceMass
      (Q'.le_of_lt hw0)
      (M := retained) (K := K) (n := volume)) ?_
  have hK' :
      physicalNomeTensorToleranceRetainedCutoff
          w
          (List.range
            (plaquetteEdgeCount volume)).length
          ε ≤ K := by
    simpa using hK
  dsimp only [retained]
  simpa using
    (boundedSU2PhysicalOutsideFaceMass_le_tolerance
      hw0 hw1
      (List.range (plaquetteEdgeCount volume))
      (range_nodup_local _)
      hε hK')

/-! ## 3. Generic nested normalized Boolean events -/

/-- Exact normalized probability of a Boolean predicate of the physical face
labelling at one finite cutoff and arbitrary nonnegative nome. -/
def physicalNomeCutoffEventProbability
    (w : Q') (hw0 : (0 : Q') ≤ w)
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) : Q' :=
  Q'.divPos
    (parametricKEventNumerator
      w cutoff volume event)
    (parametricKPhysicalPartition
      w cutoff volume)
    (couplingKPhysicalPartition_pos
      hw0 cutoff volume)

theorem physicalNomeCutoffEventProbability_abs_le_increment
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    {M K volume : Nat} (hMK : M ≤ K)
    (event : EdgeLabelling → Bool) :
    absQ
        (physicalNomeCutoffEventProbability
            w hw0 M volume event +
          -physicalNomeCutoffEventProbability
            w hw0 K volume event) ≤
      parametricKCutoffIncrement w M K volume := by
  let a :=
    parametricKEventNumerator w M volume event
  let b :=
    parametricKEventCutoffIncrement
      w M K volume event
  let d :=
    parametricKPhysicalPartition w M volume
  let n :=
    parametricKCutoffIncrement w M K volume
  let A :=
    parametricKEventNumerator w K volume event
  let D :=
    parametricKPhysicalPartition w K volume
  have ha : (0 : Q') ≤ a := by
    dsimp only [a]
    exact parametricKEventNumerator_nonnegative
      hw0 M volume event
  have hb : (0 : Q') ≤ b := by
    dsimp only [b]
    exact parametricKEventCutoffIncrement_nonnegative
      hw0 M K volume event
  have hn : (0 : Q') ≤ n := by
    dsimp only [n]
    exact parametricKCutoffIncrement_nonnegative
      hw0 M K volume
  have hd1 : (1 : Q') ≤ d := by
    dsimp only [d]
    exact couplingKPhysicalPartition_one_le
      hw0 M volume
  have had : a ≤ d := by
    dsimp only [a, d]
    exact parametricKEventNumerator_le_partition
      hw0 M volume event
  have hbn : b ≤ n := by
    dsimp only [b, n]
    exact
      parametricKEventCutoffIncrement_le_partitionIncrement
        hw0 M K volume event
  have hbase :=
    nested_normalized_event_abs_le_newMass
      ha hb hn hd1 had hbn
  have hd :
      (0 : Q') < d :=
    YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
      (by decide) hd1
  have hdn :
      (0 : Q') < d + n :=
    YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
      (by decide)
      (Q'.le_trans' _ _ _ hd1
        (Q'.add_le_self_of_nonneg d n hn))
  have hbaseExplicit :
      absQ
          (Q'.divPos a d hd +
            -(Q'.divPos
              (a + b) (d + n) hdn)) ≤
        n := by
    simpa only using hbase
  have hA : A ≈ a + b := by
    dsimp only [A, a, b]
    exact
      parametricKEventNumerator_eq_base_add_increment
        (w := w) hMK
  have hD : D ≈ d + n := by
    dsimp only [D, d, n]
    exact
      parametricKPhysicalPartition_eq_base_add_increment
        (w := w) hMK
  have hDactual :
      (0 : Q') < D := by
    dsimp only [D]
    exact couplingKPhysicalPartition_pos
      hw0 K volume
  have hlarge :
      Q'.divPos A D hDactual ≈
        Q'.divPos (a + b) (d + n) hdn := by
    apply Q'.eqv_of_le_le
    · apply Q'.le_divPos_of_mul_le
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (Q'.divPos A D hDactual)
            (d + n) D
            (Q'.eqv_symm hD))
          (Q'.eqv_trans _ _ _
            (Q'.divPos_mul_eqv
              A D hDactual)
            hA))
    · apply Q'.le_divPos_of_mul_le
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (Q'.divPos
              (a + b) (d + n) hdn)
            D (d + n) hD)
          (Q'.eqv_trans _ _ _
            (Q'.divPos_mul_eqv
              (a + b) (d + n) hdn)
            (Q'.eqv_symm hA)))
  unfold physicalNomeCutoffEventProbability
  dsimp only [a, b, d, n, A, D]
    at hbaseExplicit hlarge
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (YMGap.Continuum.ContinuumYMStack.absQ_eqv_congr
        (Q'.add_eqv_congr_left
          (Q'.divPos
            (parametricKEventNumerator
              w M volume event)
            (parametricKPhysicalPartition
              w M volume)
            (couplingKPhysicalPartition_pos
              hw0 M volume))
          _
          (-(Q'.divPos
            (parametricKEventNumerator
                w M volume event +
              parametricKEventCutoffIncrement
                w M K volume event)
            (parametricKPhysicalPartition
                w M volume +
              parametricKCutoffIncrement
                w M K volume)
            hdn))
          (Q'.neg_eqv_congr _ _ hlarge))))
    hbaseExplicit

/-- Arbitrary-nome normalized Boolean-event stability at the executable
retained cutoff, uniform in every later cutoff containing it. -/
theorem physicalNomeCutoffEventProbability_abs_le_tolerance
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat) {ε : Q'} (hε : (0 : Q') < ε)
    {K : Nat}
    (hK :
      physicalNomeTensorToleranceRetainedCutoff
          w (plaquetteEdgeCount volume) ε ≤ K)
    (event : EdgeLabelling → Bool) :
    absQ
        (physicalNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            (physicalNomeTensorToleranceRetainedCutoff
              w (plaquetteEdgeCount volume) ε)
            volume event +
          -physicalNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            K volume event) ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (physicalNomeCutoffEventProbability_abs_le_increment
      (Q'.le_of_lt hw0) hK event)
    (physicalNomeCutoffIncrement_le_tolerance
      hw0 hw1 volume hε hK)

/-! ## Axiom audit -/

#print axioms physicalTerm_le_degreeThirteenFaceProduct
#print axioms physicalCutoffIncrement_le_outsideFaceMass
#print axioms physicalNomeCutoffIncrement_le_tolerance
#print axioms physicalNomeCutoffEventProbability_abs_le_increment
#print axioms physicalNomeCutoffEventProbability_abs_le_tolerance

end YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance
