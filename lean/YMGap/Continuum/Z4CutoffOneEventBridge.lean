/-
# Exact cutoff-one bridge for finite-box events

The cutoff-cofinal event measure is stated on physical face labellings, while
the existing strong-coupling thermodynamic construction is stated on corrected
canonical polymer families.  This module supplies the exact interface.

A physical labelling is sent to its excited-face support, then to the canonical
connected-component family, and finally to the ambient polymer order.  At
physical cutoff one, the support/labelling bijection reindexes every lifted
event numerator into the corrected polymer event numerator.  The result holds
for an arbitrary Boolean predicate on families and preserves the actual
normalization, so the two cutoff-one probabilities agree exactly up to `Q'.eqv`.
-/

import YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
import YMGap.Continuum.Z4ParametricCutoffEventCofinal

namespace YMGap.Continuum.Z4CutoffOneEventBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical lift from spin labellings to polymer families -/

def physicalCanonicalAmbientFamily (n : Nat)
    (physical : EdgeLabelling) : List (List Nat) :=
  ambientOrderedFamily n
    (canonicalSurfaceFamily n (excitedPlaquetteIds n physical))

def cutoffOneLiftedFamilyEvent (n : Nat)
    (event : List (List Nat) → Bool) : EdgeLabelling → Bool :=
  fun physical => event (physicalCanonicalAmbientFamily n physical)

theorem physicalCanonicalAmbientFamily_componentLabel
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    physicalCanonicalAmbientFamily n (componentLabel support) =
      ambientOrderedFamily n (canonicalSurfaceFamily n support) := by
  unfold physicalCanonicalAmbientFamily
  rw [excitedPlaquetteIds_componentLabel_eq_support hsupport]

theorem componentLabel_mem_explicitPhysicalLabellings_one
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    componentLabel support ∈ explicitPhysicalLabellings 1 n := by
  rw [explicitPhysicalLabellings_one_eq_supportIndicators]
  exact List.mem_map.mpr ⟨support, hsupport, rfl⟩

theorem canonicalSurfaceFamily_mem_connectedGas
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    canonicalSurfaceFamily n support ∈ canonicalConnectedSurfaceGas n := by
  unfold canonicalConnectedSurfaceGas
  exact List.mem_map.mpr ⟨support, hsupport, rfl⟩

theorem parametricKPhysicalTerm_one_componentLabel_eqv_ambientActivity
    (w : Q') {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    parametricKPhysicalTerm w 1 n (componentLabel support) ≈
      canonicalSurfaceFamilyActivity w n
        (ambientOrderedFamily n (canonicalSurfaceFamily n support)) := by
  have hphysical := componentLabel_mem_explicitPhysicalLabellings_one hsupport
  have hfactor :=
    parametricLocalizedSpinFoamWeight_surfaceComponent_factor
      (w := w) hphysical
  have hcomponentActivity :
      parametricLocalizedWeightProduct w n
          (surfaceComponentLabels n (componentLabel support)) =
        canonicalSurfaceFamilyActivity w n
          (canonicalSurfaceFamily n support) := by
    rw [← canonicalSurfaceFamily_labels_eq n support]
    exact parametricLocalizedWeightProduct_componentLabels w n
      (canonicalSurfaceFamily n support)
  have hordered := gasFamilyActivity_eqv_ambientOrdered
    w (canonicalSurfaceFamily_mem_connectedGas hsupport)
  exact Q'.eqv_trans _
    (parametricLocalizedSpinFoamWeight w n (componentLabel support)) _
    (parametricKPhysicalTerm_one_eqv_localized w n
      (componentLabel support))
    (Q'.eqv_trans _
      (parametricLocalizedWeightProduct w n
        (surfaceComponentLabels n (componentLabel support))) _
      hfactor
      (Q'.eqv_trans _
        (canonicalSurfaceFamilyActivity w n
          (canonicalSurfaceFamily n support)) _
        (Q'.eqv_of_eq hcomponentActivity) hordered))

theorem parametricKEventTerm_one_componentLabel_eqv_ambientMask
    (w : Q') (n : Nat) (event : List (List Nat) → Bool)
    {support : List Nat} (hsupport : support ∈ cutoffOneFaceSupports n) :
    parametricKEventTerm w 1 n
        (cutoffOneLiftedFamilyEvent n event) (componentLabel support) ≈
      if event (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      then canonicalSurfaceFamilyActivity w n
        (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      else 0 := by
  unfold parametricKEventTerm cutoffOneLiftedFamilyEvent
  rw [physicalCanonicalAmbientFamily_componentLabel hsupport]
  by_cases hevent :
      event (ambientOrderedFamily n (canonicalSurfaceFamily n support)) = true
  · rw [if_pos hevent, if_pos hevent]
    exact parametricKPhysicalTerm_one_componentLabel_eqv_ambientActivity
      w hsupport
  · rw [if_neg hevent, if_neg hevent]
    exact Q'.eqv_refl 0

/-! ## 2. Exact reindexing of arbitrary event numerators -/

def cutoffOneAmbientMaskedEventNumerator (w : Q') (n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (fun family => if event family
      then canonicalSurfaceFamilyActivity w n family else 0)
    (ambientOrderedExactGas n)

private theorem listQSum_map_eqv_local {A B : Type}
    (f : A → Q') (g : B → Q') (reindex : A → B) :
    ∀ xs : List A,
      (∀ item, item ∈ xs → f item ≈ g (reindex item)) →
      listQSum f xs ≈ listQSum g (xs.map reindex)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, h => by
      change f head + listQSum f tail ≈
        g (reindex head) + listQSum g (tail.map reindex)
      exact Q'.add_eqv_congr'
        (h head List.mem_cons_self)
        (listQSum_map_eqv_local f g reindex tail
          (fun item hitem =>
            h item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_map_local {A B : Type}
    (f : B → Q') (reindex : A → B) : ∀ xs : List A,
    listQSum f (xs.map reindex) =
      listQSum (fun item => f (reindex item)) xs
  | [] => rfl
  | _ :: tail => congrArg (fun rest => f (reindex _) + rest)
      (listQSum_map_local f reindex tail)

theorem parametricKEventNumerator_one_eqv_ambientMasked
    (w : Q') (n : Nat) (event : List (List Nat) → Bool) :
    parametricKEventNumerator w 1 n
        (cutoffOneLiftedFamilyEvent n event) ≈
      cutoffOneAmbientMaskedEventNumerator w n event := by
  unfold parametricKEventNumerator
  change
    listQSum
        (parametricKEventTerm w 1 n
          (cutoffOneLiftedFamilyEvent n event))
        (explicitPhysicalLabellings 1 n) ≈
      cutoffOneAmbientMaskedEventNumerator w n event
  rw [explicitPhysicalLabellings_one_eq_supportIndicators]
  unfold cutoffOneAmbientMaskedEventNumerator ambientOrderedExactGas
    canonicalConnectedSurfaceGas
  rw [List.map_map]
  rw [listQSum_map_local]
  apply listQSum_map_eqv_local
  intro support hsupport
  exact parametricKEventTerm_one_componentLabel_eqv_ambientMask
    w n event hsupport

private theorem listQSum_mask_eq_filter_local {A : Type}
    (weight : A → Q') (event : A → Bool) : ∀ xs : List A,
    listQSum (fun item => if event item then weight item else 0) xs ≈
      listQSum weight (xs.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head with
      | false =>
          simp only [hevent, Bool.false_eq_true, if_false,
            List.filter_cons, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum weight (tail.filter event)) _
            (Q'.add_eqv_congr' (Q'.eqv_refl 0)
              (listQSum_mask_eq_filter_local weight event tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [hevent, if_true, List.filter_cons, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_mask_eq_filter_local weight event tail)

theorem cutoffOneAmbientMaskedEventNumerator_eqv_anchor
    (n : Nat) (event : List (List Nat) → Bool) :
    cutoffOneAmbientMaskedEventNumerator anchorCoupling n event ≈
      anchorEventNumerator n event := by
  let masked : List (List Nat) → Q' := fun family =>
    if event family
    then canonicalSurfaceFamilyActivity anchorCoupling n family else 0
  have hperm :
      listQSum masked (ambientOrderedExactGas n) ≈
        listQSum masked (canonicalCompatibleAmbientFamilies n) :=
    listQSum_perm masked (ambientOrderedExactGas_perm_compatibleFamilies n)
  have hfilter := listQSum_mask_eq_filter_local
    (canonicalSurfaceFamilyActivity anchorCoupling n) event
    (canonicalCompatibleAmbientFamilies n)
  unfold cutoffOneAmbientMaskedEventNumerator anchorEventNumerator
  dsimp only [masked] at hperm
  exact Q'.eqv_trans _ _ _ hperm hfilter

/-- Every arbitrary corrected-polymer event numerator is literally the
cutoff-one numerator of its canonical physical-labelling lift. -/
theorem anchorParametricKEventNumerator_one_eqv_anchorEventNumerator
    (n : Nat) (event : List (List Nat) → Bool) :
    parametricKEventNumerator anchorCoupling 1 n
        (cutoffOneLiftedFamilyEvent n event) ≈
      anchorEventNumerator n event := by
  exact Q'.eqv_trans _
    (cutoffOneAmbientMaskedEventNumerator anchorCoupling n event) _
    (parametricKEventNumerator_one_eqv_ambientMasked
      anchorCoupling n event)
    (cutoffOneAmbientMaskedEventNumerator_eqv_anchor n event)

/-! ## 3. The actual cutoff-one normalizations agree -/

def anchorParametricCutoffOneLiftedEventProbability
    (n : Nat) (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (parametricKEventNumerator anchorCoupling 1 n
      (cutoffOneLiftedFamilyEvent n event))
    (parametricKPhysicalPartition anchorCoupling 1 n)
    (anchorParametricPartition_pos (K := 1) (by decide) n)

private theorem divPos_eqv_divPos_of_cross_local {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : (c * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q
      (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (c * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  apply Q'.mul_left_cancel_of_pos hq
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv q (Q'.divPos p q hq)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv p q hq) ?_
  refine Q'.eqv_trans _ _ _ hcancel ?_
  exact Q'.mul_comm_eqv c q

private theorem divPos_eqv_congr_local {p p' q q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hp : p ≈ p') (hden : q ≈ q') :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  apply divPos_eqv_divPos_of_cross_local hq hq'
  exact Q'.eqv_trans _ (p' * q') _
    (Q'.mul_eqv_congr_right _ _ _ hp)
    (Q'.mul_eqv_congr_left p' _ _ (Q'.eqv_symm hden))

theorem anchorParametricPartition_one_eqv_anchorCanonicalPartition
    (n : Nat) :
    parametricKPhysicalPartition anchorCoupling 1 n ≈
      anchorCanonicalPartition n := by
  exact Q'.eqv_trans _
    (parametricLocalizedSpinFoamPartition anchorCoupling n) _
    (parametricKPhysicalPartition_one_eqv_localized anchorCoupling n)
    (Q'.eqv_symm
      (anchorCanonicalPartition_eqv_localizedSpinFoam n))

theorem anchorParametricCutoffOneLiftedEventProbability_eqv_anchor
    (n : Nat) (event : List (List Nat) → Bool) :
    anchorParametricCutoffOneLiftedEventProbability n event ≈
      anchorEventProbability n event := by
  unfold anchorParametricCutoffOneLiftedEventProbability
    anchorEventProbability
  exact divPos_eqv_congr_local
    (anchorParametricPartition_pos (K := 1) (by decide) n)
    (anchorCanonicalPartition_pos n)
    (anchorParametricKEventNumerator_one_eqv_anchorEventNumerator n event)
    (anchorParametricPartition_one_eqv_anchorCanonicalPartition n)

end YMGap.Continuum.Z4CutoffOneEventBridge

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CutoffOneEventBridge.parametricKPhysicalTerm_one_componentLabel_eqv_ambientActivity
#print axioms YMGap.Continuum.Z4CutoffOneEventBridge.parametricKEventNumerator_one_eqv_ambientMasked
#print axioms YMGap.Continuum.Z4CutoffOneEventBridge.anchorParametricKEventNumerator_one_eqv_anchorEventNumerator
#print axioms YMGap.Continuum.Z4CutoffOneEventBridge.anchorParametricCutoffOneLiftedEventProbability_eqv_anchor
