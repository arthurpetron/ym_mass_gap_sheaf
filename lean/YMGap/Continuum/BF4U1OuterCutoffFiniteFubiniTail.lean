/-
# Finite Fubini bridge for the outer-cutoff-uniform U(1) tail

This module identifies the recursive free tensor masses with the literal
function-valued `boundedEdgeLabellings` carrier on a noduplicated face list.
It then drops the exact zero/one U(1) Haar factors and bounds the canonical
new-charge sector by the outer-cutoff-independent recursive tensor envelope.
-/

import YMGap.Continuum.BF4U1OuterCutoffNesting
import YMGap.Continuum.BF4U1OuterCutoffUniformTensorTail
import YMGap.Continuum.BF4U1ExponentGramCutoffTailBridge

namespace YMGap.Continuum.BF4U1OuterCutoffFiniteFubiniTail

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4U1ExponentGramCutoffTailBridge
open YMGap.Continuum.BF4U1OuterCutoffNesting
open YMGap.Continuum.BF4U1OuterCutoffUniformTensorTail
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.AbelianFusionCLT
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.U1SignedChargeHeatTail
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem fsum_eq_finSum_local
    (f : Nat → Q') :
    ∀ length,
      YMGap.Continuum.BondMovingStep.fsum f length =
        finSum f length
  | 0 => rfl
  | length + 1 => by
      change
        YMGap.Continuum.BondMovingStep.fsum f length +
            f length =
          finSum f length + f length
      rw [fsum_eq_finSum_local f length]

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
      · simp only [List.filter_cons, hevent, Bool.false_eq_true,
          ↓reduceIte, listQSum]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.eqv_refl 0)
            (listQSum_mask_eq_filter_local
              weight event tail))
          (Q'.eqv_of_eq
            (Q'.zero_add' _))
      · simp only [List.filter_cons, hevent, ↓reduceIte, listQSum]
        exact Q'.add_eqv_congr'
          (Q'.eqv_refl (weight head))
          (listQSum_mask_eq_filter_local
            weight event tail)

/-! ## 1. Literal free Cartesian heat masses -/

def u1FaceHeatProduct
    (w : Q') (faces : List Nat)
    (state : ChargeLabelling) : Q' :=
  listQProduct
    (fun id =>
      signedChargeHeatWeight w (state id))
    faces

def boundedU1FaceHeatMass
    (w : Q') (K : Nat)
    (faces : List Nat) : Q' :=
  listQSum
    (u1FaceHeatProduct w faces)
    (boundedEdgeLabellings (2 * K) faces)

/-- The cutoff test used below, stated directly on an arbitrary face list. -/
def chargeWithinFaces
    (M : Nat) (faces : List Nat)
    (state : ChargeLabelling) : Bool :=
  chargeWithinOn M state faces

def boundedU1FaceOutsideHeatMass
    (w : Q') (M K : Nat)
    (faces : List Nat) : Q' :=
  listQSum
    (fun state =>
      if chargeWithinFaces M faces state
        then 0
        else u1FaceHeatProduct w faces state)
    (boundedEdgeLabellings (2 * K) faces)

private theorem setEdgeLabel_on_self
    (state : ChargeLabelling)
    (edge spin : Nat) :
    setEdgeLabel state edge spin edge = spin := by
  simp [setEdgeLabel]

private theorem setEdgeLabel_off
    (state : ChargeLabelling)
    {edge id spin : Nat} (hne : id ≠ edge) :
    setEdgeLabel state edge spin id =
      state id := by
  simp [setEdgeLabel, hne]

private theorem listQProduct_setEdgeLabel_fresh
    (w : Q') (state : ChargeLabelling)
    (edge spin : Nat) :
    ∀ rest : List Nat, edge ∉ rest →
      listQProduct
          (fun id =>
            signedChargeHeatWeight w
              (setEdgeLabel state edge spin id))
          rest =
        listQProduct
          (fun id =>
            signedChargeHeatWeight w (state id))
          rest
  | [], _ => rfl
  | id :: tail, hfresh => by
      have hne : id ≠ edge := by
        intro heq
        subst id
        exact hfresh List.mem_cons_self
      have htail : edge ∉ tail := by
        intro hmem
        exact hfresh
          (List.mem_cons_of_mem id hmem)
      simp only [listQProduct]
      rw [setEdgeLabel_off state hne,
        listQProduct_setEdgeLabel_fresh
          w state edge spin tail htail]

private theorem u1FaceHeatProduct_setEdgeLabel
    (w : Q') (state : ChargeLabelling)
    (edge spin : Nat) (rest : List Nat)
    (hfresh : edge ∉ rest) :
    u1FaceHeatProduct w (edge :: rest)
        (setEdgeLabel state edge spin) =
      signedChargeHeatWeight w spin *
        u1FaceHeatProduct w rest state := by
  unfold u1FaceHeatProduct
  simp only [listQProduct]
  rw [setEdgeLabel_on_self,
    listQProduct_setEdgeLabel_fresh
      w state edge spin rest hfresh]

private theorem chargeWithinOn_setEdgeLabel_fresh
    (M : Nat) (state : ChargeLabelling)
    (edge spin : Nat) :
    ∀ rest : List Nat, edge ∉ rest →
      chargeWithinOn M
          (setEdgeLabel state edge spin) rest =
        chargeWithinOn M state rest
  | [], _ => rfl
  | id :: tail, hfresh => by
      have hne : id ≠ edge := by
        intro heq
        subst id
        exact hfresh List.mem_cons_self
      have htail : edge ∉ tail := by
        intro hmem
        exact hfresh
          (List.mem_cons_of_mem id hmem)
      simp only [chargeWithinOn]
      rw [setEdgeLabel_off state hne,
        chargeWithinOn_setEdgeLabel_fresh
          M state edge spin tail htail]

private theorem chargeWithinFaces_setEdgeLabel
    (M : Nat) (state : ChargeLabelling)
    (edge spin : Nat) (rest : List Nat)
    (hfresh : edge ∉ rest) :
    chargeWithinFaces M (edge :: rest)
        (setEdgeLabel state edge spin) =
      (decide (chargeMagnitude spin ≤ M) &&
        chargeWithinFaces M rest state) := by
  unfold chargeWithinFaces
  simp only [chargeWithinOn]
  rw [setEdgeLabel_on_self,
    chargeWithinOn_setEdgeLabel_fresh
      M state edge spin rest hfresh]

/-! ## 2. Exact free-mass Fubini factorization -/

theorem boundedU1FaceHeatMass_eq_tensorMass
    (w : Q') (K : Nat) :
    ∀ faces : List Nat, faces.Nodup →
      boundedU1FaceHeatMass w K faces ≈
        signedChargeTensorMass w K faces.length
  | [], _ => by
      unfold boundedU1FaceHeatMass
        u1FaceHeatProduct
        boundedEdgeLabellings
        signedChargeTensorMass
      exact Q'.eqv_of_eq (Q'.zero_add' 1)
  | edge :: rest, hnodup => by
      have hfresh : edge ∉ rest :=
        (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have ih :=
        boundedU1FaceHeatMass_eq_tensorMass
          w K rest hrestNodup
      unfold boundedU1FaceHeatMass
      change
        listQSum
            (u1FaceHeatProduct w (edge :: rest))
            (boundedEdgeLabellings (2 * K) (edge :: rest)) ≈
          symmetricLabelPartial w K *
            signedChargeTensorMass w K rest.length
      refine Q'.eqv_trans _ _ _
        (listQSum_bounded_cons
          (2 * K) edge rest
          (u1FaceHeatProduct w (edge :: rest))) ?_
      rw [fsum_eq_finSum_local]
      refine Q'.eqv_trans _
        (finSum
          (fun spin =>
            signedChargeHeatWeight w spin *
              boundedU1FaceHeatMass w K rest)
        (2 * K + 1)) _ ?_ ?_
      · apply finSum_eqv_congr
        intro spin
        refine Q'.eqv_trans _ _ _
          (listQSum_congr
            (fun state =>
              Q'.eqv_of_eq
                (u1FaceHeatProduct_setEdgeLabel
                  w state edge spin rest hfresh))
            (boundedEdgeLabellings (2 * K) rest)) ?_
        exact listQSum_mul_left
          (signedChargeHeatWeight w spin)
          (u1FaceHeatProduct w rest)
          (boundedEdgeLabellings (2 * K) rest)
      · have hfactor :
            finSum
                (fun spin =>
                  signedChargeHeatWeight w spin *
                    boundedU1FaceHeatMass w K rest)
                (2 * K + 1) ≈
              symmetricLabelPartial w K *
                boundedU1FaceHeatMass w K rest := by
          simpa only [symmetricLabelPartial] using
            Q'.eqv_symm
              (RationalTail.finSum_mul_const
                (signedChargeHeatWeight w)
                (boundedU1FaceHeatMass w K rest)
                (2 * K + 1))
        have hmul :
            symmetricLabelPartial w K *
                boundedU1FaceHeatMass w K rest ≈
              symmetricLabelPartial w K *
                signedChargeTensorMass w K rest.length :=
          Q'.mul_eqv_congr_left _ _ _ ih
        exact Q'.eqv_trans _ _ _ hfactor hmul

#print axioms boundedU1FaceHeatMass_eq_tensorMass

/-! ## 3. One-coordinate window decomposition -/

private theorem add_nonnegative_local {a b : Q'}
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a + b := by
  have h := Q'.add_le_add ha hb
  rw [Q'.zero_add'] at h
  exact h

private theorem finSum_split_local
    (f : Nat → Q') (N : Nat) :
    ∀ L : Nat,
      finSum f (N + L) ≈
        finSum f N +
          finSum (fun offset => f (N + offset)) L
  | 0 => by
      rw [Nat.add_zero, finSum_zero, Q'.add_zero']
      exact Q'.eqv_refl _
  | L + 1 => by
      have ih := finSum_split_local f N L
      show
        finSum f (N + L) + f (N + L) ≈
          finSum f N +
            (finSum (fun offset => f (N + offset)) L +
              f (N + L))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih)
        (Q'.add_assoc_eqv _ _ _)

private theorem finSum_nonnegative_local
    (f : Nat → Q')
    (hf : ∀ index, (0 : Q') ≤ f index) :
    ∀ length, (0 : Q') ≤ finSum f length
  | 0 => Q'.le_refl' 0
  | length + 1 =>
      add_nonnegative_local
        (finSum_nonnegative_local f hf length)
        (hf length)

private theorem finSum_mono_local
    (lower upper : Nat → Q')
    (hpointwise : ∀ index, lower index ≤ upper index) :
    ∀ length,
      finSum lower length ≤ finSum upper length
  | 0 => Q'.le_refl' 0
  | length + 1 =>
      Q'.add_le_add
        (finSum_mono_local lower upper hpointwise length)
        (hpointwise length)

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
  | head :: tail, hpointwise =>
      Q'.add_le_add
        (hpointwise head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hmem =>
            hpointwise item
              (List.mem_cons_of_mem head hmem)))

private theorem signedChargeHeatWeight_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (label : Nat) :
    (0 : Q') ≤ signedChargeHeatWeight w label := by
  unfold signedChargeHeatWeight
  exact abelCoeff_nonneg
    (Q'.le_of_lt hw0) _

private theorem u1FaceHeatProduct_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (state : ChargeLabelling) :
    ∀ faces : List Nat,
      (0 : Q') ≤
        u1FaceHeatProduct w faces state
  | [] => Q'.zero_le_one
  | edge :: rest =>
      Q'.mul_nonneg _ _
        (signedChargeHeatWeight_nonnegative
          hw0 (state edge))
        (u1FaceHeatProduct_nonnegative
          hw0 state rest)

private theorem boundedU1FaceHeatMass_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (K : Nat) (faces : List Nat) :
    (0 : Q') ≤
      boundedU1FaceHeatMass w K faces := by
  unfold boundedU1FaceHeatMass
  exact listQSum_nonnegative_local _
    (fun state =>
      u1FaceHeatProduct_nonnegative
        hw0 state faces)
    (boundedEdgeLabellings (2 * K) faces)

private theorem boundedU1FaceOutsideHeatMass_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (M K : Nat) (faces : List Nat) :
    (0 : Q') ≤
      boundedU1FaceOutsideHeatMass
        w M K faces := by
  unfold boundedU1FaceOutsideHeatMass
  apply listQSum_nonnegative_local
  intro state
  cases hwindow :
      chargeWithinFaces M faces state
  · exact u1FaceHeatProduct_nonnegative
      hw0 state faces
  · exact Q'.le_refl' 0

/-- One-label heat weight masked to the strict outer shell. -/
def signedChargeBadWeight
    (w : Q') (M label : Nat) : Q' :=
  if decide (M < chargeMagnitude label)
    then signedChargeHeatWeight w label
    else 0

private theorem signedChargeBadWeight_prefix_zero
    (w : Q') (M label : Nat)
    (hlabel : label < 2 * M + 1) :
    signedChargeBadWeight w M label = 0 := by
  have hmag :
      chargeMagnitude label ≤ M :=
    chargeMagnitude_le_of_label_lt hlabel
  unfold signedChargeBadWeight
  simp [Nat.not_lt.mpr hmag]

private theorem signedChargeBadWeight_tail
    (w : Q') (M offset : Nat) :
    signedChargeBadWeight w M
        (2 * M + 1 + offset) =
      signedChargeHeatWeight w
        (2 * M + 1 + offset) := by
  have hmag :
      M <
        chargeMagnitude
          (2 * M + 1 + offset) := by
    unfold chargeMagnitude
    omega
  unfold signedChargeBadWeight
  simp [hmag]

theorem signedChargeBadWeight_finSum_eq_outerShell
    (w : Q') {M K : Nat} (hMK : M ≤ K) :
    finSum (signedChargeBadWeight w M)
        (2 * K + 1) ≈
      signedChargeOuterShellMass w M K := by
  have hlength :
      2 * K + 1 =
        (2 * M + 1) + 2 * (K - M) := by
    omega
  rw [hlength]
  refine Q'.eqv_trans _ _ _
    (finSum_split_local
      (signedChargeBadWeight w M)
      (2 * M + 1) (2 * (K - M))) ?_
  have hprefix :
      finSum (signedChargeBadWeight w M)
          (2 * M + 1) ≈ 0 := by
    refine Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr_lt
        (signedChargeBadWeight w M)
        (fun _ => (0 : Q'))
        (2 * M + 1)
        (fun label hlabel =>
          Q'.eqv_of_eq
            (signedChargeBadWeight_prefix_zero
              w M label hlabel))) ?_
    exact Q'.eqv_of_eq
      (finSum_zero_seq (2 * M + 1))
  have htail :
      finSum
          (fun offset =>
            signedChargeBadWeight w M
              (2 * M + 1 + offset))
          (2 * (K - M)) ≈
        signedChargeOuterShellMass w M K := by
    unfold signedChargeOuterShellMass
    exact RationalTail.finSum_eqv_congr _ _
      (fun offset =>
        Q'.eqv_of_eq
          (signedChargeBadWeight_tail
            w M offset))
      (2 * (K - M))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hprefix htail) ?_
  exact Q'.eqv_of_eq
    (Q'.zero_add'
      (signedChargeOuterShellMass w M K))

#print axioms signedChargeBadWeight_finSum_eq_outerShell

/-! ## 4. Boolean union event versus the recursive union mass -/

private theorem conditionedOutsideSum_eq_good
    (w : Q') (M K edge spin : Nat)
    (rest : List Nat) (hfresh : edge ∉ rest)
    (hgood : chargeMagnitude spin ≤ M) :
    listQSum
        (fun state =>
          if chargeWithinFaces M (edge :: rest)
              (setEdgeLabel state edge spin)
            then 0
            else
              u1FaceHeatProduct w (edge :: rest)
                (setEdgeLabel state edge spin))
        (boundedEdgeLabellings (2 * K) rest) ≈
      signedChargeHeatWeight w spin *
        boundedU1FaceOutsideHeatMass
          w M K rest := by
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        signedChargeHeatWeight w spin *
          (if chargeWithinFaces M rest state
            then 0
            else u1FaceHeatProduct w rest state))
      (boundedEdgeLabellings (2 * K) rest)) _
    (listQSum_congr
      (fun state => by
        rw [chargeWithinFaces_setEdgeLabel
          M state edge spin rest hfresh,
          u1FaceHeatProduct_setEdgeLabel
            w state edge spin rest hfresh]
        cases hrest :
            chargeWithinFaces M rest state
        · simp [hgood]
          exact Q'.eqv_refl _
        · simp [hgood]
          exact Q'.eqv_symm
            (Q'.mul_zero_eqv
              (signedChargeHeatWeight w spin)))
      (boundedEdgeLabellings (2 * K) rest)) ?_
  unfold boundedU1FaceOutsideHeatMass
  exact listQSum_mul_left
    (signedChargeHeatWeight w spin)
    (fun state =>
      if chargeWithinFaces M rest state
        then 0
        else u1FaceHeatProduct w rest state)
    (boundedEdgeLabellings (2 * K) rest)

private theorem conditionedOutsideSum_eq_bad
    (w : Q') (M K edge spin : Nat)
    (rest : List Nat) (hfresh : edge ∉ rest)
    (hbad : ¬ chargeMagnitude spin ≤ M) :
    listQSum
        (fun state =>
          if chargeWithinFaces M (edge :: rest)
              (setEdgeLabel state edge spin)
            then 0
            else
              u1FaceHeatProduct w (edge :: rest)
                (setEdgeLabel state edge spin))
        (boundedEdgeLabellings (2 * K) rest) ≈
      signedChargeHeatWeight w spin *
        boundedU1FaceHeatMass w K rest := by
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        signedChargeHeatWeight w spin *
          u1FaceHeatProduct w rest state)
      (boundedEdgeLabellings (2 * K) rest)) _
    (listQSum_congr
      (fun state => by
        rw [chargeWithinFaces_setEdgeLabel
          M state edge spin rest hfresh,
          u1FaceHeatProduct_setEdgeLabel
            w state edge spin rest hfresh]
        cases hrest :
            chargeWithinFaces M rest state
        · simp [hbad]
          exact Q'.eqv_refl _
        · simp [hbad]
          exact Q'.eqv_refl _)
      (boundedEdgeLabellings (2 * K) rest)) ?_
  unfold boundedU1FaceHeatMass
  exact listQSum_mul_left
    (signedChargeHeatWeight w spin)
    (u1FaceHeatProduct w rest)
    (boundedEdgeLabellings (2 * K) rest)

private theorem conditionedOutsideSum_le_unionTerm
    {w : Q'} (hw0 : (0 : Q') < w)
    (M K edge spin : Nat)
    (rest : List Nat) (hfresh : edge ∉ rest) :
    listQSum
        (fun state =>
          if chargeWithinFaces M (edge :: rest)
              (setEdgeLabel state edge spin)
            then 0
            else
              u1FaceHeatProduct w (edge :: rest)
                (setEdgeLabel state edge spin))
        (boundedEdgeLabellings (2 * K) rest) ≤
      signedChargeBadWeight w M spin *
          boundedU1FaceHeatMass w K rest +
        signedChargeHeatWeight w spin *
          boundedU1FaceOutsideHeatMass
            w M K rest := by
  by_cases hgood :
      chargeMagnitude spin ≤ M
  · have hleft :=
      conditionedOutsideSum_eq_good
        w M K edge spin rest hfresh hgood
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv hleft) ?_
    have hbadWeight :
        signedChargeBadWeight w M spin = 0 := by
      unfold signedChargeBadWeight
      simp [Nat.not_lt.mpr hgood]
    rw [hbadWeight]
    let tailMass :=
      signedChargeHeatWeight w spin *
        boundedU1FaceOutsideHeatMass
          w M K rest
    have hzero :
        (0 : Q') *
              boundedU1FaceHeatMass w K rest +
            tailMass ≈
          tailMass := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.zero_mul_eqv
            (boundedU1FaceHeatMass w K rest))
          (Q'.eqv_refl tailMass)) ?_
      exact Q'.eqv_of_eq
        (Q'.zero_add' tailMass)
    exact Q'.le_of_eqv
      (Q'.eqv_symm hzero)
  · have hleft :=
      conditionedOutsideSum_eq_bad
        w M K edge spin rest hfresh hgood
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv hleft) ?_
    have hbadWeight :
        signedChargeBadWeight w M spin =
          signedChargeHeatWeight w spin := by
      unfold signedChargeBadWeight
      simp [Nat.lt_of_not_ge hgood]
    rw [hbadWeight]
    exact Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _
        (signedChargeHeatWeight_nonnegative
          hw0 spin)
        (boundedU1FaceOutsideHeatMass_nonnegative
          hw0 M K rest))

theorem boundedU1FaceOutsideHeatMass_le_unionMass
    {w : Q'} (hw0 : (0 : Q') < w)
    {M K : Nat} (hMK : M ≤ K) :
    ∀ faces : List Nat, faces.Nodup →
      boundedU1FaceOutsideHeatMass
          w M K faces ≤
        signedChargeTensorOutsideUnionMass
          w M K faces.length
  | [], _ => by
      unfold boundedU1FaceOutsideHeatMass
        boundedEdgeLabellings
        chargeWithinFaces chargeWithinOn
        u1FaceHeatProduct
        signedChargeTensorOutsideUnionMass
      exact Q'.le_refl' 0
  | edge :: rest, hnodup => by
      have hfresh : edge ∉ rest :=
        (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have ih :=
        boundedU1FaceOutsideHeatMass_le_unionMass
          hw0 hMK rest hrestNodup
      unfold boundedU1FaceOutsideHeatMass
      have hfubini :=
        listQSum_bounded_cons
          (2 * K) edge rest
          (fun state =>
            if chargeWithinFaces M (edge :: rest) state
              then 0
              else u1FaceHeatProduct
                w (edge :: rest) state)
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv hfubini) ?_
      rw [fsum_eq_finSum_local]
      let totalRest :=
        boundedU1FaceHeatMass w K rest
      let outsideRest :=
        boundedU1FaceOutsideHeatMass
          w M K rest
      let unionTerm := fun spin =>
        signedChargeBadWeight w M spin *
            totalRest +
          signedChargeHeatWeight w spin *
            outsideRest
      refine Q'.le_trans' _
        (finSum unionTerm (2 * K + 1))
        _
        (finSum_mono_local _ _ (fun spin =>
          conditionedOutsideSum_le_unionTerm
            hw0 M K edge spin rest hfresh)
          (2 * K + 1)) ?_
      have hsplit :
          finSum unionTerm (2 * K + 1) ≈
            finSum
                (fun spin =>
                  signedChargeBadWeight w M spin *
                    totalRest)
                (2 * K + 1) +
              finSum
                (fun spin =>
                  signedChargeHeatWeight w spin *
                    outsideRest)
                (2 * K + 1) := by
        exact RationalTail.finSum_add _ _
          (2 * K + 1)
      have hbadFactor :
          finSum
                (fun spin =>
                  signedChargeBadWeight w M spin *
                    totalRest)
                (2 * K + 1) ≈
            signedChargeOuterShellMass w M K *
              totalRest := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (RationalTail.finSum_mul_const
              (signedChargeBadWeight w M)
              totalRest (2 * K + 1))) ?_
        exact Q'.mul_eqv_congr_right _ _ _
          (signedChargeBadWeight_finSum_eq_outerShell
            w hMK)
      have htotalFactor :
          finSum
                (fun spin =>
                  signedChargeHeatWeight w spin *
                    outsideRest)
                (2 * K + 1) ≈
            symmetricLabelPartial w K *
              outsideRest := by
        simpa only [symmetricLabelPartial] using
          Q'.eqv_symm
            (RationalTail.finSum_mul_const
              (signedChargeHeatWeight w)
              outsideRest (2 * K + 1))
      have hregroup :
          finSum unionTerm (2 * K + 1) ≈
            signedChargeOuterShellMass w M K *
                totalRest +
              symmetricLabelPartial w K *
                outsideRest :=
        Q'.eqv_trans _ _ _ hsplit
          (Q'.add_eqv_congr'
            hbadFactor htotalFactor)
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv hregroup) ?_
      change
        signedChargeOuterShellMass w M K *
              boundedU1FaceHeatMass w K rest +
            symmetricLabelPartial w K *
              boundedU1FaceOutsideHeatMass w M K rest ≤
          signedChargeOuterShellMass w M K *
              signedChargeTensorMass w K rest.length +
            symmetricLabelPartial w K *
              signedChargeTensorOutsideUnionMass
                w M K rest.length
      apply Q'.add_le_add
      · exact Q'.le_of_eqv
          (Q'.mul_eqv_congr_left _ _ _
            (boundedU1FaceHeatMass_eq_tensorMass
              w K rest hrestNodup))
      · exact Q'.mul_le_mul_of_nonneg_left
          _ _ _
          ih
          (symmetricLabelPartial_nonnegative
            hw0 K)

#print axioms boundedU1FaceOutsideHeatMass_le_unionMass

/-! ## 5. Canonical physical slab: drop the Haar constraints -/

private theorem labelWithinB_even_eq_chargeWithinFaces
    (M : Nat) (state : ChargeLabelling) :
    ∀ faces : List Nat,
      labelWithinB (2 * M) faces state =
        chargeWithinFaces M faces state
  | [] => rfl
  | edge :: rest => by
      have ih :=
        labelWithinB_even_eq_chargeWithinFaces
          M state rest
      by_cases hlabel :
          state edge < 2 * M + 1
      · have hmag :
            chargeMagnitude (state edge) ≤ M :=
          chargeMagnitude_le_of_label_lt hlabel
        simp [labelWithinB, chargeWithinFaces,
          chargeWithinOn, hlabel, hmag, ih]
      · have hmag :
            ¬ chargeMagnitude (state edge) ≤ M := by
          intro hle
          unfold chargeMagnitude at hle
          omega
        simp [labelWithinB, chargeWithinFaces,
          chargeWithinOn, hlabel, hmag, ih]

theorem oldChargeWindow_eq_chargeWithinFaces
    (half M : Nat) (state : ChargeLabelling) :
    oldChargeWindow half M state =
      chargeWithinFaces M
        (slabPhysicalFaceEdges
          (centralExtent half)) state := by
  unfold oldChargeWindow
  exact labelWithinB_even_eq_chargeWithinFaces
    M state
      (slabPhysicalFaceEdges
        (centralExtent half))

private theorem rangeNodupLocal :
    ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨rangeNodupLocal n,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq :=
        List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl n)
        (List.mem_range.mp hleft)

private theorem slabPhysicalFaceEdges_nodup_local
    (extent : Nat) :
    (slabPhysicalFaceEdges extent).Nodup := by
  unfold slabPhysicalFaceEdges
  exact rangeNodupLocal _

private theorem canonicalPhysicalTerm_le_faceHeat
    {w : Q'} (hw0 : (0 : Q') < w)
    (half L : Nat) (state : ChargeLabelling) :
    (canonicalU1Slab w (Q'.le_of_lt hw0)
        half L).physicalTerm state ≤
      u1FaceHeatProduct w
        (slabPhysicalFaceEdges
          (centralExtent half)) state := by
  let D :=
    canonicalU1Slab w (Q'.le_of_lt hw0)
      half L
  have hface0 :
      (0 : Q') ≤ D.faceFactor state := by
    unfold U1SlabData.faceFactor
    exact u1FaceHeatProduct_nonnegative
      hw0 state D.faceEdges
  have hhaar :
      D.haarFactor state ≤ (1 : Q') :=
    u1HaarFactor_le_one D state
  have hdrop :
      D.physicalTerm state ≤
        D.faceFactor state * (1 : Q') := by
    unfold U1SlabData.physicalTerm
    exact Q'.mul_le_mul_of_nonneg_left
      _ _ _ hhaar hface0
  have hfaceEq :
      D.faceFactor state =
        u1FaceHeatProduct w
          (slabPhysicalFaceEdges
            (centralExtent half)) state := by
    unfold D canonicalU1Slab
      U1SlabData.faceFactor
      U1SlabData.faceEdges
      U1SlabData.carrierData
      SlabPhysicalData.faceEdges
      u1FaceHeatProduct
      signedChargeHeatWeight
    rfl
  refine Q'.le_trans' _ _ _ hdrop ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.mul_one_eqv (D.faceFactor state))
      (Q'.eqv_of_eq hfaceEq))

theorem newChargeSectorMass_le_outsideHeatMass
    {w : Q'} (hw0 : (0 : Q') < w)
    (half K L : Nat) :
    newChargeSectorMass w (Q'.le_of_lt hw0)
        half K L ≤
      boundedU1FaceOutsideHeatMass w K L
        (slabPhysicalFaceEdges
          (centralExtent half)) := by
  let faces :=
    slabPhysicalFaceEdges (centralExtent half)
  let source :=
    boundedEdgeLabellings (2 * L) faces
  have hsource :
      newChargeSector w (Q'.le_of_lt hw0)
          half K L =
        source.filter
          (fun state =>
            !(chargeWithinFaces K faces state)) := by
    unfold newChargeSector source faces
    rw [canonicalU1Slab_states]
    apply congrArg
      (fun event =>
        (boundedEdgeLabellings (2 * L)
          (slabPhysicalFaceEdges
            (centralExtent half))).filter event)
    funext state
    rw [oldChargeWindow_eq_chargeWithinFaces]
  unfold newChargeSectorMass
  rw [hsource]
  have hdrop :
      listQSum
          (canonicalU1Slab w (Q'.le_of_lt hw0)
            half L).physicalTerm
          (source.filter
            (fun state =>
              !(chargeWithinFaces K faces state))) ≤
        listQSum
          (u1FaceHeatProduct w faces)
          (source.filter
            (fun state =>
              !(chargeWithinFaces K faces state))) := by
    apply listQSum_mono_local
    intro state _
    exact canonicalPhysicalTerm_le_faceHeat
      hw0 half L state
  refine Q'.le_trans' _ _ _ hdrop ?_
  have hfilter :
      boundedU1FaceOutsideHeatMass
          w K L faces ≈
        listQSum
          (u1FaceHeatProduct w faces)
          (source.filter
            (fun state =>
              !(chargeWithinFaces K faces state))) := by
    unfold boundedU1FaceOutsideHeatMass source
    refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          if !(chargeWithinFaces K faces state)
            then u1FaceHeatProduct w faces state
            else 0)
        (boundedEdgeLabellings (2 * L) faces)) _
      (listQSum_congr
        (fun state => by
          cases hwindow :
              chargeWithinFaces K faces state
          · simp
            exact Q'.eqv_refl _
          · simp
            exact Q'.eqv_refl _)
        (boundedEdgeLabellings
          (2 * L) faces)) ?_
    exact listQSum_mask_eq_filter_local
      (u1FaceHeatProduct w faces)
      (fun state =>
        !(chargeWithinFaces K faces state))
      (boundedEdgeLabellings (2 * L) faces)
  exact Q'.ge_of_eqv hfilter

theorem newChargeSectorMass_le_tensorEnvelope
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) {K L : Nat} (hKL : K ≤ L) :
    newChargeSectorMass w (Q'.le_of_lt hw0)
        half K L ≤
      signedChargeTensorTailEnvelope w K
        (slabPhysicalFaceEdges
          (centralExtent half)).length := by
  refine Q'.le_trans' _ _ _
    (newChargeSectorMass_le_outsideHeatMass
      hw0 half K L) ?_
  refine Q'.le_trans' _ _ _
    (boundedU1FaceOutsideHeatMass_le_unionMass
      hw0 hKL
      (slabPhysicalFaceEdges
        (centralExtent half))
      (slabPhysicalFaceEdges_nodup_local _)) ?_
  exact signedChargeTensorOutsideUnionMass_le_envelope
    hw0 hw1 hKL
      (slabPhysicalFaceEdges
        (centralExtent half)).length

theorem canonicalU1Slab_partition_increment_tail
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) {K L : Nat} (hKL : K ≤ L) :
    (canonicalU1Slab w (Q'.le_of_lt hw0)
        half L).partition ≤
      (canonicalU1Slab w (Q'.le_of_lt hw0)
          half K).partition +
        signedChargeTensorTailEnvelope w K
          (slabPhysicalFaceEdges
            (centralExtent half)).length := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (canonicalU1Slab_partition_decomposition
        w (Q'.le_of_lt hw0) half hKL)) ?_
  exact Q'.add_le_add_left _ _ _
    (newChargeSectorMass_le_tensorEnvelope
      hw0 hw1 half hKL)

#print axioms oldChargeWindow_eq_chargeWithinFaces
#print axioms newChargeSectorMass_le_outsideHeatMass
#print axioms newChargeSectorMass_le_tensorEnvelope
#print axioms canonicalU1Slab_partition_increment_tail

end YMGap.Continuum.BF4U1OuterCutoffFiniteFubiniTail
