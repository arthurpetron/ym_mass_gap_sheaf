/-
# Finite Fubini bridge for the physical SU(2) degree-thirteen tail

The incidence estimate for the literal four-dimensional spin-foam term
produces one factor

  (spin + 1)^13 * w^(spin * (spin + 2))

per physical face.  `SU2PhysicalOuterCutoffTensorTail` proves a uniform
outer-cutoff bound for the corresponding recursive tensor mass.  This file
identifies that tensor with the literal `boundedEdgeLabellings` Cartesian
carrier and compares the Boolean new-label sector with its recursive union
envelope.

At the strong-coupling anchor this closes the finite-Fubini step from the
actual interacting cutoff increment to the outer-cutoff-independent scalar
envelope.  Haar/fusion multiplicities have not been discarded heuristically:
their complete incidence product is consumed by
`anchorPhysicalTerm_le_degreeThirteenFaceProduct`.

## Axiom gate

Finite `List`, `Nat`, and `Q'` recursion only.  No `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup

namespace YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem fsum_eq_finSum_local
    (f : Nat → Q') :
    ∀ length,
      fsum f length = finSum f length
  | 0 => rfl
  | length + 1 => by
      change fsum f length + f length =
        finSum f length + f length
      rw [fsum_eq_finSum_local f length]

private theorem add_nonnegative_local {a b : Q'}
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a + b := by
  have h := Q'.add_le_add ha hb
  rw [Q'.zero_add'] at h
  exact h

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

private theorem listQSum_mul_left_local
    {A : Type} (a : Q') (weight : A → Q') :
    ∀ source : List A,
      listQSum (fun item => a * weight item) source ≈
        a * listQSum weight source
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | head :: tail => by
      change
        a * weight head +
            listQSum (fun item => a * weight item) tail ≈
          a * (weight head + listQSum weight tail)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_mul_left_local a weight tail))
        (Q'.eqv_symm
          (Q'.mul_add_eqv a _ _))

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
          (Q'.eqv_of_eq (Q'.zero_add' _))
      · simp only [List.filter_cons, hevent, ↓reduceIte, listQSum]
        exact Q'.add_eqv_congr'
          (Q'.eqv_refl (weight head))
          (listQSum_mask_eq_filter_local
            weight event tail)

/-! ## 1. Literal degree-thirteen Cartesian face masses -/

def su2PhysicalFaceProduct
    (w : Q') (faces : List Nat)
    (state : EdgeLabelling) : Q' :=
  eliminateLinks
    (fun face =>
      tailTerm w physicalFacePolynomialDegree
        (state face))
    faces

def boundedSU2PhysicalFaceMass
    (w : Q') (K : Nat)
    (faces : List Nat) : Q' :=
  listQSum
    (su2PhysicalFaceProduct w faces)
    (boundedEdgeLabellings K faces)

def boundedSU2PhysicalOutsideFaceMass
    (w : Q') (M K : Nat)
    (faces : List Nat) : Q' :=
  listQSum
    (fun state =>
      if labelWithinB M faces state
        then 0
        else su2PhysicalFaceProduct w faces state)
    (boundedEdgeLabellings K faces)

private theorem setEdgeLabel_on_self
    (state : EdgeLabelling)
    (edge spin : Nat) :
    setEdgeLabel state edge spin edge = spin := by
  simp [setEdgeLabel]

private theorem setEdgeLabel_off
    (state : EdgeLabelling)
    {edge face spin : Nat} (hne : face ≠ edge) :
    setEdgeLabel state edge spin face =
      state face := by
  simp [setEdgeLabel, hne]

private theorem eliminateLinks_setEdgeLabel_fresh
    (w : Q') (state : EdgeLabelling)
    (edge spin : Nat) :
    ∀ rest : List Nat, edge ∉ rest →
      eliminateLinks
          (fun face =>
            tailTerm w physicalFacePolynomialDegree
              (setEdgeLabel state edge spin face))
          rest =
        eliminateLinks
          (fun face =>
            tailTerm w physicalFacePolynomialDegree
              (state face))
          rest
  | [], _ => rfl
  | face :: tail, hfresh => by
      have hne : face ≠ edge := by
        intro heq
        subst face
        exact hfresh List.mem_cons_self
      have htail : edge ∉ tail := by
        intro hmem
        exact hfresh
          (List.mem_cons_of_mem face hmem)
      simp only [eliminateLinks]
      rw [setEdgeLabel_off state hne,
        eliminateLinks_setEdgeLabel_fresh
          w state edge spin tail htail]

private theorem su2PhysicalFaceProduct_setEdgeLabel
    (w : Q') (state : EdgeLabelling)
    (edge spin : Nat) (rest : List Nat)
    (hfresh : edge ∉ rest) :
    su2PhysicalFaceProduct w (edge :: rest)
        (setEdgeLabel state edge spin) =
      tailTerm w physicalFacePolynomialDegree spin *
        su2PhysicalFaceProduct w rest state := by
  unfold su2PhysicalFaceProduct
  simp only [eliminateLinks]
  rw [setEdgeLabel_on_self,
    eliminateLinks_setEdgeLabel_fresh
      w state edge spin rest hfresh]

private theorem labelWithinB_setEdgeLabel_fresh_local
    (M : Nat) (state : EdgeLabelling)
    (edge spin : Nat) :
    ∀ rest : List Nat, edge ∉ rest →
      labelWithinB M rest
          (setEdgeLabel state edge spin) =
        labelWithinB M rest state
  | [], _ => rfl
  | face :: tail, hfresh => by
      have hne : face ≠ edge := by
        intro heq
        subst face
        exact hfresh List.mem_cons_self
      have htail : edge ∉ tail := by
        intro hmem
        exact hfresh
          (List.mem_cons_of_mem face hmem)
      simp only [labelWithinB]
      rw [setEdgeLabel_off state hne,
        labelWithinB_setEdgeLabel_fresh_local
          M state edge spin tail htail]

private theorem labelWithinB_setEdgeLabel_local
    (M : Nat) (state : EdgeLabelling)
    (edge spin : Nat) (rest : List Nat)
    (hfresh : edge ∉ rest) :
    labelWithinB M (edge :: rest)
        (setEdgeLabel state edge spin) =
      (decide (spin < M + 1) &&
        labelWithinB M rest state) := by
  simp only [labelWithinB]
  rw [setEdgeLabel_on_self,
    labelWithinB_setEdgeLabel_fresh_local
      M state edge spin rest hfresh]

theorem boundedSU2PhysicalFaceMass_eq_tensorMass
    (w : Q') (K : Nat) :
    ∀ faces : List Nat, faces.Nodup →
      boundedSU2PhysicalFaceMass w K faces ≈
        su2PhysicalTensorMass w K faces.length
  | [], _ => by
      unfold boundedSU2PhysicalFaceMass
        su2PhysicalFaceProduct
        boundedEdgeLabellings
        su2PhysicalTensorMass
      exact Q'.eqv_of_eq (Q'.zero_add' 1)
  | edge :: rest, hnodup => by
      have hfresh : edge ∉ rest :=
        (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have ih :=
        boundedSU2PhysicalFaceMass_eq_tensorMass
          w K rest hrestNodup
      unfold boundedSU2PhysicalFaceMass
      change
        listQSum
            (su2PhysicalFaceProduct w (edge :: rest))
            (boundedEdgeLabellings K (edge :: rest)) ≈
          su2PhysicalLabelPartial w K *
            su2PhysicalTensorMass w K rest.length
      refine Q'.eqv_trans _ _ _
        (listQSum_bounded_cons K edge rest
          (su2PhysicalFaceProduct w (edge :: rest))) ?_
      rw [fsum_eq_finSum_local]
      refine Q'.eqv_trans _
        (finSum
          (fun spin =>
            tailTerm w physicalFacePolynomialDegree spin *
              boundedSU2PhysicalFaceMass w K rest)
          (K + 1)) _ ?_ ?_
      · apply finSum_eqv_congr
        intro spin
        refine Q'.eqv_trans _ _ _
          (listQSum_congr
            (fun state =>
              Q'.eqv_of_eq
                (su2PhysicalFaceProduct_setEdgeLabel
                  w state edge spin rest hfresh))
            (boundedEdgeLabellings K rest)) ?_
        exact listQSum_mul_left_local
          (tailTerm w physicalFacePolynomialDegree spin)
          (su2PhysicalFaceProduct w rest)
          (boundedEdgeLabellings K rest)
      · have hfactor :
            finSum
                (fun spin =>
                  tailTerm w physicalFacePolynomialDegree spin *
                    boundedSU2PhysicalFaceMass w K rest)
                (K + 1) ≈
              su2PhysicalLabelPartial w K *
                boundedSU2PhysicalFaceMass w K rest := by
          simpa only [su2PhysicalLabelPartial] using
            Q'.eqv_symm
              (RationalTail.finSum_mul_const
                (tailTerm w physicalFacePolynomialDegree)
                (boundedSU2PhysicalFaceMass w K rest)
                (K + 1))
        exact Q'.eqv_trans _ _ _ hfactor
          (Q'.mul_eqv_congr_left _ _ _ ih)

/-! ## 2. One-coordinate strict outer shell -/

def su2PhysicalBadWeight
    (w : Q') (M spin : Nat) : Q' :=
  if decide (M < spin)
    then tailTerm w physicalFacePolynomialDegree spin
    else 0

private theorem su2PhysicalBadWeight_prefix_zero
    (w : Q') (M spin : Nat)
    (hspin : spin < M + 1) :
    su2PhysicalBadWeight w M spin = 0 := by
  have hle : spin ≤ M := by omega
  unfold su2PhysicalBadWeight
  simp [Nat.not_lt.mpr hle]

private theorem su2PhysicalBadWeight_tail
    (w : Q') (M offset : Nat) :
    su2PhysicalBadWeight w M
        (M + 1 + offset) =
      tailTerm w physicalFacePolynomialDegree
        (M + 1 + offset) := by
  have hgt : M < M + 1 + offset := by omega
  unfold su2PhysicalBadWeight
  simp [hgt]

theorem su2PhysicalBadWeight_finSum_eq_outerShell
    (w : Q') {M K : Nat} (hMK : M ≤ K) :
    finSum (su2PhysicalBadWeight w M)
        (K + 1) ≈
      su2PhysicalOuterShellMass w M K := by
  have hlength :
      K + 1 = (M + 1) + (K - M) := by
    omega
  rw [hlength]
  refine Q'.eqv_trans _ _ _
    (finSum_split_local
      (su2PhysicalBadWeight w M)
      (M + 1) (K - M)) ?_
  have hprefix :
      finSum (su2PhysicalBadWeight w M)
          (M + 1) ≈ 0 := by
    refine Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr_lt
        (su2PhysicalBadWeight w M)
        (fun _ => (0 : Q'))
        (M + 1)
        (fun spin hspin =>
          Q'.eqv_of_eq
            (su2PhysicalBadWeight_prefix_zero
              w M spin hspin))) ?_
    exact Q'.eqv_of_eq
      (finSum_zero_seq (M + 1))
  have htail :
      finSum
          (fun offset =>
            su2PhysicalBadWeight w M
              (M + 1 + offset))
          (K - M) ≈
        su2PhysicalOuterShellMass w M K := by
    unfold su2PhysicalOuterShellMass tailWindow
    exact RationalTail.finSum_eqv_congr _ _
      (fun offset =>
        Q'.eqv_of_eq
          (su2PhysicalBadWeight_tail
            w M offset))
      (K - M)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hprefix htail) ?_
  exact Q'.eqv_of_eq
    (Q'.zero_add'
      (su2PhysicalOuterShellMass w M K))

/-! ## 3. Boolean union event versus the recursive union mass -/

private theorem su2PhysicalFaceProduct_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (state : EdgeLabelling) :
    ∀ faces : List Nat,
      (0 : Q') ≤
        su2PhysicalFaceProduct w faces state
  | [] => Q'.zero_le_one
  | face :: rest =>
      Q'.mul_nonneg _ _
        (tailTerm_nonneg
          (Q'.le_of_lt hw0)
          physicalFacePolynomialDegree
          (state face))
        (su2PhysicalFaceProduct_nonnegative
          hw0 state rest)

private theorem boundedSU2PhysicalFaceMass_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (K : Nat) (faces : List Nat) :
    (0 : Q') ≤
      boundedSU2PhysicalFaceMass w K faces := by
  unfold boundedSU2PhysicalFaceMass
  exact listQSum_nonnegative_local _
    (fun state =>
      su2PhysicalFaceProduct_nonnegative
        hw0 state faces)
    (boundedEdgeLabellings K faces)

private theorem boundedSU2PhysicalOutsideFaceMass_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (M K : Nat) (faces : List Nat) :
    (0 : Q') ≤
      boundedSU2PhysicalOutsideFaceMass
        w M K faces := by
  unfold boundedSU2PhysicalOutsideFaceMass
  apply listQSum_nonnegative_local
  intro state
  cases hwindow : labelWithinB M faces state
  · exact su2PhysicalFaceProduct_nonnegative
      hw0 state faces
  · exact Q'.le_refl' 0

private theorem conditionedOutsideSum_eq_good
    (w : Q') (M K edge spin : Nat)
    (rest : List Nat) (hfresh : edge ∉ rest)
    (hgood : spin ≤ M) :
    listQSum
        (fun state =>
          if labelWithinB M (edge :: rest)
              (setEdgeLabel state edge spin)
            then 0
            else
              su2PhysicalFaceProduct w (edge :: rest)
                (setEdgeLabel state edge spin))
        (boundedEdgeLabellings K rest) ≈
      tailTerm w physicalFacePolynomialDegree spin *
        boundedSU2PhysicalOutsideFaceMass
          w M K rest := by
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        tailTerm w physicalFacePolynomialDegree spin *
          (if labelWithinB M rest state
            then 0
            else su2PhysicalFaceProduct w rest state))
      (boundedEdgeLabellings K rest)) _
    (listQSum_congr
      (fun state => by
        rw [labelWithinB_setEdgeLabel_local
          M state edge spin rest hfresh,
          su2PhysicalFaceProduct_setEdgeLabel
            w state edge spin rest hfresh]
        cases hrest : labelWithinB M rest state
        · simp [Nat.lt_succ_iff.mpr hgood]
          exact Q'.eqv_refl _
        · simp [Nat.lt_succ_iff.mpr hgood]
          exact Q'.eqv_symm
            (Q'.mul_zero_eqv
              (tailTerm w physicalFacePolynomialDegree spin)))
      (boundedEdgeLabellings K rest)) ?_
  unfold boundedSU2PhysicalOutsideFaceMass
  exact listQSum_mul_left_local
    (tailTerm w physicalFacePolynomialDegree spin)
    (fun state =>
      if labelWithinB M rest state
        then 0
        else su2PhysicalFaceProduct w rest state)
    (boundedEdgeLabellings K rest)

private theorem conditionedOutsideSum_eq_bad
    (w : Q') (M K edge spin : Nat)
    (rest : List Nat) (hfresh : edge ∉ rest)
    (hbad : ¬ spin ≤ M) :
    listQSum
        (fun state =>
          if labelWithinB M (edge :: rest)
              (setEdgeLabel state edge spin)
            then 0
            else
              su2PhysicalFaceProduct w (edge :: rest)
                (setEdgeLabel state edge spin))
        (boundedEdgeLabellings K rest) ≈
      tailTerm w physicalFacePolynomialDegree spin *
        boundedSU2PhysicalFaceMass w K rest := by
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        tailTerm w physicalFacePolynomialDegree spin *
          su2PhysicalFaceProduct w rest state)
      (boundedEdgeLabellings K rest)) _
    (listQSum_congr
      (fun state => by
        rw [labelWithinB_setEdgeLabel_local
          M state edge spin rest hfresh,
          su2PhysicalFaceProduct_setEdgeLabel
            w state edge spin rest hfresh]
        have hlarge : ¬ spin < M + 1 := by
          omega
        cases hrest : labelWithinB M rest state
        · simp [hlarge]
          exact Q'.eqv_refl _
        · simp [hlarge]
          exact Q'.eqv_refl _)
      (boundedEdgeLabellings K rest)) ?_
  unfold boundedSU2PhysicalFaceMass
  exact listQSum_mul_left_local
    (tailTerm w physicalFacePolynomialDegree spin)
    (su2PhysicalFaceProduct w rest)
    (boundedEdgeLabellings K rest)

private theorem conditionedOutsideSum_le_unionTerm
    {w : Q'} (hw0 : (0 : Q') < w)
    (M K edge spin : Nat)
    (rest : List Nat) (hfresh : edge ∉ rest) :
    listQSum
        (fun state =>
          if labelWithinB M (edge :: rest)
              (setEdgeLabel state edge spin)
            then 0
            else
              su2PhysicalFaceProduct w (edge :: rest)
                (setEdgeLabel state edge spin))
        (boundedEdgeLabellings K rest) ≤
      su2PhysicalBadWeight w M spin *
          boundedSU2PhysicalFaceMass w K rest +
        tailTerm w physicalFacePolynomialDegree spin *
          boundedSU2PhysicalOutsideFaceMass
            w M K rest := by
  by_cases hgood : spin ≤ M
  · have hleft :=
      conditionedOutsideSum_eq_good
        w M K edge spin rest hfresh hgood
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv hleft) ?_
    have hbadWeight :
        su2PhysicalBadWeight w M spin = 0 := by
      unfold su2PhysicalBadWeight
      simp [Nat.not_lt.mpr hgood]
    rw [hbadWeight]
    let tailMass :=
      tailTerm w physicalFacePolynomialDegree spin *
        boundedSU2PhysicalOutsideFaceMass
          w M K rest
    have hzero :
        (0 : Q') *
              boundedSU2PhysicalFaceMass w K rest +
            tailMass ≈
          tailMass := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.zero_mul_eqv
            (boundedSU2PhysicalFaceMass w K rest))
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
        su2PhysicalBadWeight w M spin =
          tailTerm w physicalFacePolynomialDegree spin := by
      unfold su2PhysicalBadWeight
      simp [Nat.lt_of_not_ge hgood]
    rw [hbadWeight]
    exact Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _
        (tailTerm_nonneg
          (Q'.le_of_lt hw0)
          physicalFacePolynomialDegree spin)
        (boundedSU2PhysicalOutsideFaceMass_nonnegative
          hw0 M K rest))

theorem boundedSU2PhysicalOutsideFaceMass_le_unionMass
    {w : Q'} (hw0 : (0 : Q') < w)
    {M K : Nat} (hMK : M ≤ K) :
    ∀ faces : List Nat, faces.Nodup →
      boundedSU2PhysicalOutsideFaceMass
          w M K faces ≤
        su2PhysicalTensorOutsideUnionMass
          w M K faces.length
  | [], _ => by
      unfold boundedSU2PhysicalOutsideFaceMass
        boundedEdgeLabellings labelWithinB
        su2PhysicalFaceProduct
        su2PhysicalTensorOutsideUnionMass
      exact Q'.le_refl' 0
  | edge :: rest, hnodup => by
      have hfresh : edge ∉ rest :=
        (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have ih :=
        boundedSU2PhysicalOutsideFaceMass_le_unionMass
          hw0 hMK rest hrestNodup
      unfold boundedSU2PhysicalOutsideFaceMass
      have hfubini :=
        listQSum_bounded_cons K edge rest
          (fun state =>
            if labelWithinB M (edge :: rest) state
              then 0
              else su2PhysicalFaceProduct
                w (edge :: rest) state)
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv hfubini) ?_
      rw [fsum_eq_finSum_local]
      let totalRest :=
        boundedSU2PhysicalFaceMass w K rest
      let outsideRest :=
        boundedSU2PhysicalOutsideFaceMass
          w M K rest
      let unionTerm := fun spin =>
        su2PhysicalBadWeight w M spin *
            totalRest +
          tailTerm w physicalFacePolynomialDegree spin *
            outsideRest
      refine Q'.le_trans' _
        (finSum unionTerm (K + 1))
        _
        (finSum_mono_local _ _ (fun spin =>
          conditionedOutsideSum_le_unionTerm
            hw0 M K edge spin rest hfresh)
          (K + 1)) ?_
      have hsplit :
          finSum unionTerm (K + 1) ≈
            finSum
                (fun spin =>
                  su2PhysicalBadWeight w M spin *
                    totalRest)
                (K + 1) +
              finSum
                (fun spin =>
                  tailTerm w physicalFacePolynomialDegree spin *
                    outsideRest)
                (K + 1) := by
        exact RationalTail.finSum_add _ _ (K + 1)
      have hbadFactor :
          finSum
                (fun spin =>
                  su2PhysicalBadWeight w M spin *
                    totalRest)
                (K + 1) ≈
            su2PhysicalOuterShellMass w M K *
              totalRest := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (RationalTail.finSum_mul_const
              (su2PhysicalBadWeight w M)
              totalRest (K + 1))) ?_
        exact Q'.mul_eqv_congr_right _ _ _
          (su2PhysicalBadWeight_finSum_eq_outerShell
            w hMK)
      have htotalFactor :
          finSum
                (fun spin =>
                  tailTerm w physicalFacePolynomialDegree spin *
                    outsideRest)
                (K + 1) ≈
            su2PhysicalLabelPartial w K *
              outsideRest := by
        simpa only [su2PhysicalLabelPartial] using
          Q'.eqv_symm
            (RationalTail.finSum_mul_const
              (tailTerm w physicalFacePolynomialDegree)
              outsideRest (K + 1))
      have hregroup :
          finSum unionTerm (K + 1) ≈
            su2PhysicalOuterShellMass w M K *
                totalRest +
              su2PhysicalLabelPartial w K *
                outsideRest :=
        Q'.eqv_trans _ _ _ hsplit
          (Q'.add_eqv_congr'
            hbadFactor htotalFactor)
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv hregroup) ?_
      change
        su2PhysicalOuterShellMass w M K *
              boundedSU2PhysicalFaceMass w K rest +
            su2PhysicalLabelPartial w K *
              boundedSU2PhysicalOutsideFaceMass w M K rest ≤
          su2PhysicalOuterShellMass w M K *
              su2PhysicalTensorMass w K rest.length +
            su2PhysicalLabelPartial w K *
              su2PhysicalTensorOutsideUnionMass
                w M K rest.length
      apply Q'.add_le_add
      · exact Q'.le_of_eqv
          (Q'.mul_eqv_congr_left _ _ _
            (boundedSU2PhysicalFaceMass_eq_tensorMass
              w K rest hrestNodup))
      · exact Q'.mul_le_mul_of_nonneg_left
          _ _ _ ih
          (su2PhysicalLabelPartial_nonnegative
            hw0 K)

/-! ## 4. Literal interacting anchor increment -/

theorem anchorCutoffIncrement_le_outsideFaceMass
    {M K n : Nat} :
    parametricKCutoffIncrement anchorCoupling
        M K n ≤
      boundedSU2PhysicalOutsideFaceMass
        anchorCoupling M K
        (List.range (plaquetteEdgeCount n)) := by
  unfold parametricKCutoffIncrement
  have hterm :
      listQSum
          (parametricKPhysicalTerm anchorCoupling K n)
          ((boundedEdgeLabellings K
            (List.range (plaquetteEdgeCount n))).filter
              (fun state =>
                !(labelWithinB M
                  (List.range (plaquetteEdgeCount n)) state))) ≤
        listQSum
          (su2PhysicalFaceProduct anchorCoupling
            (List.range (plaquetteEdgeCount n)))
          ((boundedEdgeLabellings K
            (List.range (plaquetteEdgeCount n))).filter
              (fun state =>
                !(labelWithinB M
                  (List.range (plaquetteEdgeCount n)) state))) := by
    apply listQSum_mono_local
    intro state hstate
    exact anchorPhysicalTerm_le_degreeThirteenFaceProduct
      (List.mem_filter.mp hstate).1
  refine Q'.le_trans' _ _ _ hterm ?_
  have hmask :
      boundedSU2PhysicalOutsideFaceMass
          anchorCoupling M K
          (List.range (plaquetteEdgeCount n)) ≈
        listQSum
          (su2PhysicalFaceProduct anchorCoupling
            (List.range (plaquetteEdgeCount n)))
          ((boundedEdgeLabellings K
            (List.range (plaquetteEdgeCount n))).filter
              (fun state =>
                !(labelWithinB M
                  (List.range (plaquetteEdgeCount n)) state))) := by
    unfold boundedSU2PhysicalOutsideFaceMass
    refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          if !(labelWithinB M
              (List.range (plaquetteEdgeCount n)) state)
            then su2PhysicalFaceProduct anchorCoupling
              (List.range (plaquetteEdgeCount n)) state
            else 0)
        (boundedEdgeLabellings K
          (List.range (plaquetteEdgeCount n)))) _
      (listQSum_congr
        (fun state => by
          cases hwindow :
              labelWithinB M
                (List.range (plaquetteEdgeCount n)) state
          · simp
            exact Q'.eqv_refl _
          · simp
            exact Q'.eqv_refl _)
        (boundedEdgeLabellings K
          (List.range (plaquetteEdgeCount n)))) ?_
    exact listQSum_mask_eq_filter_local
      (su2PhysicalFaceProduct anchorCoupling
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
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl N)
        (List.mem_range.mp hleft)

/-- The literal interacting anchor increment is bounded by the
outer-cutoff-independent degree-thirteen tensor envelope. -/
theorem anchorCutoffIncrement_le_tensorEnvelope
    (S precision : Nat) {M K n : Nat}
    (hMK : M ≤ K)
    (hcutBase :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow anchorCoupling (2 * S + 3) ≤
        HalfPow.half)
    (hheadBase :
      tailTerm anchorCoupling
          physicalFacePolynomialDegree S ≤
        dyad 1)
    (hcutTail :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow anchorCoupling
            (2 * (M + 1) + 3) ≤
        HalfPow.half)
    (hheadTail :
      tailTerm anchorCoupling
          physicalFacePolynomialDegree (M + 1) ≤
        dyad (precision + 1)) :
    parametricKCutoffIncrement anchorCoupling
        M K n ≤
      su2PhysicalTensorTailEnvelope
        anchorCoupling S M precision
        (plaquetteEdgeCount n) := by
  refine Q'.le_trans' _ _ _
    (anchorCutoffIncrement_le_outsideFaceMass
      (M := M) (K := K) (n := n)) ?_
  refine Q'.le_trans' _ _ _
    (boundedSU2PhysicalOutsideFaceMass_le_unionMass
      (w := anchorCoupling) (by decide) hMK
      (List.range (plaquetteEdgeCount n))
      (range_nodup_local _)) ?_
  simpa using
    (su2PhysicalTensorOutsideUnionMass_le_envelope
      (w := anchorCoupling) (by decide) (by decide)
      S precision (M := M) (K := K)
      hcutBase hheadBase hcutTail hheadTail
      (plaquetteEdgeCount n))

#print axioms boundedSU2PhysicalFaceMass_eq_tensorMass
#print axioms su2PhysicalBadWeight_finSum_eq_outerShell
#print axioms boundedSU2PhysicalOutsideFaceMass_le_unionMass
#print axioms anchorCutoffIncrement_le_outsideFaceMass
#print axioms anchorCutoffIncrement_le_tensorEnvelope

end YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
