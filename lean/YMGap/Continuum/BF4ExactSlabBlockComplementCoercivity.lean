/-
# Original all-state patch-complement coercivity

The actual block conditional is the groundspace projection of the actual
patch generator. Its complement obeys a positive collar-dependent Poincare
bound on EVERY vector of the original completion. Exterior-dependent ground
states remain in the kernel. Only the comparison argument uses independent
Haar projections; the resulting energy uses the original singleton updates.

The explicit coefficient is blockLower/blockUpper. It is independent of
ambient extent and late heat cutoff for fixed nome and patch size, but loses
exponentially with patch size. This supplies a baseline for energy-relative,
kernel-preserving approximation, NOT a useful scaling-family estimate or an
OS/physical Hamiltonian gap.
-/

import YMGap.Continuum.BF4ExactSlabBlockFixedSpace
import YMGap.Continuum.GNSProjectionDistanceMinimum
import YMGap.Continuum.SU2QuaternionWeightedHaarFamilyVariance

namespace YMGap.Continuum.BF4ExactSlabBlockComplementCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockCompletionComparison
open YMGap.Continuum.BF4ExactSlabBlockReferenceProjection
open YMGap.Continuum.BF4ExactSlabBlockSingletonProjection
open YMGap.Continuum.BF4ExactSlabBlockFixedSpace
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.SU2QuaternionWeightedHaarFamilyCompletion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem sumOn_map {A B : Type} (xs : List A) (f : A → B) (g : B → RC) :
    sumOn (xs.map f) g = sumOn xs (fun a => g (f a)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [List.map_cons, sumOn, ih]

private theorem scale_eqv {a b : Q'} (h : Q'.eqv a b) (x : RC) :
    RCscale a x = RCscale b x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_eqv_congr_right _ _ (X.approx n) h))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)
  (tests : List (PhysicalLink extent))

local notation "S" => testLinks extent tests
local notation "hS" => testLinks_valid extent tests
local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => backgroundData hw0 hw1 K extent hK S
local notation "W" => background w K extent S
local notation "HC" => background_certificate hw0 hw1 K extent hK S
local notation "J" => toBackground hw0 hw1 K extent hK S hS
local notation "P" => BF4ExactSlabConditionalSweep.projections hw0 hw1 K extent hK
local notation "R" => SU2QuaternionWeightedHaarFamilyVariance.projections blocks W HC

/-- A listed physical link, with the actual independent-background witness. -/
def backgroundIndex (i : { j : PhysicalLink extent // j ∈ tests }) :
    SU2QuaternionWeightedHaarFamilyVariance.ValidSlot blocks W :=
  ⟨(boundaryCompleteSlabLinks extent).idxOf i.val.val,
    List.idxOf_lt_length_of_mem i.val.property,
    background_independent_on_support w K extent S i.val.property
      (List.mem_map.mpr ⟨i.val, i.property, rfl⟩)⟩

/-- Preserve every occurrence; neither exterior coordinates nor repeated
patch entries are removed. -/
def backgroundTests : List (SU2QuaternionWeightedHaarFamilyVariance.ValidSlot blocks W) :=
  tests.attach.map (backgroundIndex (w := w) K extent tests)

theorem backgroundTests_slots :
    (backgroundTests (w := w) K extent tests).map Subtype.val = slots extent S := by
  calc
    (backgroundTests (w := w) K extent tests).map Subtype.val =
        tests.attach.map (fun i => (backgroundIndex (w := w) K extent tests i).val) :=
      List.map_map
    _ = tests.map (fun i => (boundaryCompleteSlabLinks extent).idxOf i.val) := by
      change tests.attach.map ((fun i : PhysicalLink extent =>
        (boundaryCompleteSlabLinks extent).idxOf i.val) ∘ Subtype.val) = _
      rw [← List.map_map, List.attach_map_subtype_val]
    _ = slots extent S := by
      simp only [slots, testLinks, List.map_map]
      rfl

/-- Only the comparison projection is independent Haar. The vector subtracted
on the right is the actual original-action conditional output. -/
theorem background_singleton_energy_le
    (i : { j : PhysicalLink extent // j ∈ tests }) (x : GNSCompletionSpace F) :
    RCle (RCscale (blockLower w (S).length)
      (normSq ((R).residual (backgroundIndex (w := w) K extent tests i) (J x))))
      (normSq ((P).residual i.val x)) := by
  have hi : i.val.val ∈ S := List.mem_map.mpr ⟨i.val, i.property, rfl⟩
  have hfix : (R).op (backgroundIndex (w := w) K extent tests i)
      (J ((P).op i.val x)) = J ((P).op i.val x) := by
    have h := reference_conditional hw0 hw1 K extent hK S [i.val.val] hS
      (fun j hj => (List.mem_singleton.mp hj) ▸ hi) x
    rw [conditionalProjection_singleton hw0 hw1 K extent hK i.val.val i.val.property] at h
    have hp := background_reference_singleton hw0 hw1 K extent hK S hS
      i.val.val hi ((P).op i.val x)
    exact hp.symm.trans (congrArg J h)
  have hmin := (R).residual_distance_minimum
    (backgroundIndex (w := w) K extent tests i) (J x) (J ((P).op i.val x)) hfix
  have hscaled := RCscale_mono
    (Q'.le_of_lt (blockLower_positive hw0 hw1 (S).length)) hmin
  have hnorm := (completed_form_bounds hw0 hw1 K extent hK S hS
    ((P).residual i.val x)).1
  change RCle (RCscale (blockLower w (S).length)
    (normSq (J ((F).cSub x ((P).op i.val x))))) _ at hnorm
  rw [toBackground_sub] at hnorm
  exact RCle_trans hscaled hnorm

/-- Sum of the independent reference residuals is controlled by the existing
original patch energy, on the same completed input. -/
theorem background_energy_le (x : GNSCompletionSpace F) :
    RCle (RCscale (blockLower w (S).length)
      ((R).finalEnergy (backgroundTests (w := w) K extent tests) (J x)))
      ((P).finalEnergy tests x) := by
  have h := sumOn_mono tests.attach _ _
    (fun i _ => background_singleton_energy_le hw0 hw1 K extent hK tests i x)
  rw [sumOn_scale] at h
  have he : sumOn tests.attach (fun i => normSq ((P).residual i.val x)) =
      (P).finalEnergy tests x := by
    rw [← sumOn_map tests.attach Subtype.val (fun i => normSq ((P).residual i x)),
      List.attach_map_subtype_val]
    rfl
  rw [he] at h
  simpa only [finalEnergy, backgroundTests, sumOn_map] using h

private def blockFamily : Family F Unit where
  op _ := BF4ExactSlabBlockConditionalProjection.conditionalProjection hw0 hw1 K extent hK S hS
  adjoint _ := BF4ExactSlabBlockConditionalProjection.conditionalProjection_selfAdjoint
    hw0 hw1 K extent hK S hS
  idem _ := BF4ExactSlabBlockConditionalProjection.conditionalProjection_idempotent
    hw0 hw1 K extent hK S hS

local notation "C" => BF4ExactSlabBlockConditionalProjection.conditionalProjection
  hw0 hw1 K extent hK S hS
local notation "Q" => reference hw0 hw1 K extent hK S S hS (fun _ h => h)

/-- Division-free all-state Poincare bound for the ACTUAL patch groundspace.
No locality or global-vacuum centering is assumed for x. -/
theorem block_complement_coercivity_mul (x : GNSCompletionSpace F) :
    RCle (RCscale (blockLower w (S).length) (normSq ((F).cSub x (C x))))
      (RCscale (blockUpper w (S).length) ((P).finalEnergy tests x)) := by
  have hmin := (blockFamily hw0 hw1 K extent hK tests).residual_distance_minimum
    () x (Q x) (conditional_reference hw0 hw1 K extent hK S S hS (fun _ h => h) x)
  have hnorm := (completed_form_bounds hw0 hw1 K extent hK S hS
    ((F).cSub x (Q x))).2
  rw [toBackground_sub, background_reference] at hnorm
  have hvar := SU2QuaternionWeightedHaarFamilyVariance.family_variance_le_energy
    blocks W HC (backgroundTests (w := w) K extent tests) (J x)
  simp only [backgroundTests_slots] at hvar
  have hU : (0 : Q') ≤ blockUpper w (S).length :=
    Q'.le_of_lt (blockUpper_positive hw0 (S).length)
  have hL : (0 : Q') ≤ blockLower w (S).length :=
    Q'.le_of_lt (blockLower_positive hw0 hw1 (S).length)
  have hv := RCle_trans hmin (RCle_trans hnorm (RCscale_mono hU hvar))
  have hvL := RCscale_mono hL hv
  have heU := RCscale_mono hU (background_energy_le hw0 hw1 K extent hK tests x)
  rw [RCscale_RCscale] at hvL heU
  rw [scale_eqv (Q'.mul_comm_eqv (blockLower w (S).length) (blockUpper w (S).length))] at hvL
  exact RCle_trans hvL heU

/-- A positive rational baseline; dependence on nome and patch size is data. -/
def blockCoercivity (size : Nat) : Q' :=
  Q'.recipPos (blockUpper w size) (blockUpper_positive hw0 size) * blockLower w size

include hw1 in
theorem blockCoercivity_positive (size : Nat) :
    (0 : Q') < blockCoercivity hw0 size :=
  Q'.mul_pos (Q'.recipPos_pos _ _) (blockLower_positive hw0 hw1 size)

private theorem one_le_pow_local_cap {a : Q'} (ha : (1 : Q') ≤ a) :
    ∀ n : Nat, (1 : Q') ≤ a^n
  | 0 => Q'.le_refl' _
  | n + 1 => by
      rw [Q'.pow_succ]
      have hmul := Q'.mul_le_mul_of_nonneg_left _ _ a
        (one_le_pow_local_cap ha n) (Q'.le_trans' _ _ _ Q'.zero_le_one ha)
      exact Q'.le_trans' _ _ _ ha
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv a)) hmul)

/-- The patch Poincare coefficient never exceeds one. -/
theorem blockCoercivity_le_one (hw1 : w < (1 : Q')) (size : Nat) :
    blockCoercivity hw0 size ≤ (1 : Q') := by
  have hfloor_pos := localFloor_positive hw0 hw1
  have hfloor0 : (0 : Q') ≤ localFloor w := Q'.le_of_lt hfloor_pos
  have hfloor1 : localFloor w ≤ (1 : Q') := by
    unfold localFloor
    exact Q'.min_le_right
  have hlow : blockLower w size ≤ (1 : Q') :=
    HKPos.pow_le_one hfloor0 hfloor1 (6 * size)
  have hupper : (1 : Q') ≤ blockUpper w size := by
    unfold blockUpper
    exact one_le_pow_local_cap (one_le_localCap hw0) (6 * size)
  have hupper_pos := blockUpper_positive hw0 size
  have hrecip : Q'.recipPos (blockUpper w size) hupper_pos ≤ (1 : Q') := by
    apply Q'.le_of_mul_le_mul_left (c := blockUpper w size) _ hupper_pos
    have heq : Q'.eqv
        (blockUpper w size * Q'.recipPos (blockUpper w size) hupper_pos) 1 :=
      Q'.mul_recipPos_eqv _ _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
      (Q'.le_trans' _ _ _ hupper
        (Q'.ge_of_eqv (Q'.mul_one_eqv (blockUpper w size))))
  unfold blockCoercivity
  have hprod := Q'.mul_le_mul_of_nonneg_right
    (Q'.recipPos (blockUpper w size) hupper_pos) 1 (blockLower w size)
    hrecip (Q'.le_of_lt (blockLower_positive hw0 hw1 size))
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (blockLower w size))) hlow)

/-- The same patch coefficient on every completed vector, with its exact
original block residual and original singleton energy. -/
theorem block_complement_coercivity (x : GNSCompletionSpace F) :
    RCle (RCscale (blockCoercivity hw0 tests.length) (normSq ((F).cSub x (C x))))
      ((P).finalEnergy tests x) := by
  have h := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos
      (blockUpper w (S).length) (blockUpper_positive hw0 (S).length)))
    (block_complement_coercivity_mul hw0 hw1 K extent hK tests x)
  rw [RCscale_RCscale, RCscale_RCscale] at h
  have hc : Q'.eqv
      (Q'.recipPos (blockUpper w (S).length) (blockUpper_positive hw0 (S).length) *
        blockUpper w (S).length) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  rw [scale_eqv hc, RCscale_one] at h
  simpa only [blockCoercivity, testLinks, List.length_map] using h

#print axioms backgroundIndex
#print axioms backgroundTests
#print axioms backgroundTests_slots
#print axioms background_singleton_energy_le
#print axioms background_energy_le
#print axioms block_complement_coercivity_mul
#print axioms blockCoercivity
#print axioms blockCoercivity_positive
#print axioms blockCoercivity_le_one
#print axioms block_complement_coercivity

end YMGap.Continuum.BF4ExactSlabBlockComplementCoercivity
