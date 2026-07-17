/-
# Global assembly of fixed-link incidence trajectories

Each fixed link now has an explicit finite list of compatible internal channel
assignments, but the choices are heterogeneous because different links meet
different fixed face-ID lists.  This file proves finite product Fubini for such
heterogeneous choices and assembles one global incidence-trajectory state over
the literal fixed-link list.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedWordTrajectoryFubini

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedWordTrajectoryFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem qMulCongrLocal {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Heterogeneous finite choices -/

def zeroChoiceOn {A B : Type} (fallback : B) : A → B :=
  fun _ => fallback

def setChoiceOn {A B : Type} [DecidableEq A]
    (choice : A → B) (key : A) (value : B) : A → B :=
  fun item => if item = key then value else choice item

def heterogeneousChoices {A B : Type} [DecidableEq A]
    (fallback : B) (options : A → List B) :
    List A → List (A → B)
  | [] => [zeroChoiceOn fallback]
  | key :: rest =>
      (options key).flatMap (fun value =>
        (heterogeneousChoices fallback options rest).map
          (fun choice => setChoiceOn choice key value))

theorem heterogeneousChoices_sound
    {A B : Type} [DecidableEq A]
    (fallback : B) (options : A → List B) :
    ∀ (keys : List A) (choice : A → B), keys.Nodup →
      choice ∈ heterogeneousChoices fallback options keys →
      ∀ key : A, key ∈ keys → choice key ∈ options key
  | [], _, _, _, key, hkey => False.elim (List.not_mem_nil hkey)
  | head :: rest, choice, hnodup, hchoice, key, hkey => by
      have hparts := List.nodup_cons.mp hnodup
      obtain ⟨selected, hselected, hselectedBlock⟩ :=
        List.mem_flatMap.mp hchoice
      obtain ⟨tailChoice, htailChoice, heq⟩ :=
        List.mem_map.mp hselectedBlock
      rw [← heq]
      by_cases hsame : key = head
      · subst key
        rw [show setChoiceOn tailChoice head selected head = selected by
          simp [setChoiceOn]]
        exact hselected
      · rw [show setChoiceOn tailChoice head selected key =
            tailChoice key by simp [setChoiceOn, hsame]]
        have hrest : key ∈ rest := by
          rcases List.mem_cons.mp hkey with heqKey | htail
          · exact False.elim (hsame heqKey)
          · exact htail
        exact heterogeneousChoices_sound fallback options rest tailChoice
          hparts.2 htailChoice key hrest

private theorem listQSum_heterogeneousChoices_cons
    {A B : Type} [DecidableEq A]
    (fallback : B) (options : A → List B)
    (key : A) (rest : List A) (value : (A → B) → Q') :
    listQSum value
        (heterogeneousChoices fallback options (key :: rest)) ≈
      listQSum (fun selected =>
        listQSum (fun choice =>
          value (setChoiceOn choice key selected))
          (heterogeneousChoices fallback options rest))
        (options key) := by
  change listQSum value
      ((options key).flatMap (fun selected =>
        (heterogeneousChoices fallback options rest).map
          (fun choice => setChoiceOn choice key selected))) ≈ _
  refine Q'.eqv_trans _ _ _ (listQSum_flatMap _ _ _) ?_
  apply listQSum_congr
  intro selected
  exact Q'.eqv_of_eq
    (listQSum_map value
      (fun choice => setChoiceOn choice key selected)
      (heterogeneousChoices fallback options rest))

/-- Heterogeneous product Fubini: the available finite choices may depend on
the key, while `Nodup` prevents two keys from overwriting one coordinate. -/
theorem heterogeneousChoices_product_fubini
    {A B : Type} [DecidableEq A]
    (fallback : B) (options : A → List B)
    (factor : A → B → Q') :
    ∀ keys : List A, keys.Nodup →
      listQSum (fun choice =>
        listQProduct (fun key => factor key (choice key)) keys)
        (heterogeneousChoices fallback options keys) ≈
      listQProduct
        (fun key => listQSum (factor key) (options key)) keys
  | [], _ => by
      change (1 : Q') + 0 ≈ 1
      exact q_add_zero_eqv 1
  | key :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      let fullValue : (A → B) → Q' := fun choice =>
        listQProduct (fun item => factor item (choice item))
          (key :: rest)
      let tailValue : (A → B) → Q' := fun choice =>
        listQProduct (fun item => factor item (choice item)) rest
      have hexpand := listQSum_heterogeneousChoices_cons
        fallback options key rest fullValue
      have hinner : ∀ selected,
          listQSum (fun choice =>
              fullValue (setChoiceOn choice key selected))
            (heterogeneousChoices fallback options rest) ≈
            factor key selected *
              listQSum tailValue
                (heterogeneousChoices fallback options rest) := by
        intro selected
        have hpoint : ∀ choice,
            fullValue (setChoiceOn choice key selected) ≈
              factor key selected * tailValue choice := by
          intro choice
          unfold fullValue tailValue
          simp only [listQProduct]
          apply qMulCongrLocal
          · simp [setChoiceOn]
            exact Q'.eqv_refl _
          · apply listQProduct_congr_eqv
            intro item hitem
            have hne : item ≠ key := by
              intro heq
              exact hparts.1 (heq ▸ hitem)
            simp [setChoiceOn, hne]
            exact Q'.eqv_refl _
        refine Q'.eqv_trans _ _ _
          (listQSum_congr hpoint
            (heterogeneousChoices fallback options rest)) ?_
        exact listQSum_mul_left (factor key selected) tailValue
          (heterogeneousChoices fallback options rest)
      refine Q'.eqv_trans _ _ _ hexpand ?_
      refine Q'.eqv_trans _ _ _
        (listQSum_congr hinner (options key)) ?_
      refine Q'.eqv_trans _ _ _
        (listQSum_mul_right (factor key)
          (listQSum tailValue
            (heterogeneousChoices fallback options rest))
          (options key)) ?_
      simp only [listQProduct]
      exact Q'.mul_eqv_congr_left
        (listQSum (factor key) (options key)) _ _
        (heterogeneousChoices_product_fubini
          fallback options factor rest hparts.2)

/-! ## 2. Concrete global incidence-trajectory state -/

abbrev FixedIncidenceTrajectoryState := Z4Link → Nat → Nat

def adjacentEvenFixedLinkTrajectoryOptions
    (K radius : Nat) (link : Z4Link) : List (Nat → Nat) :=
  boundedLabellingsOn (linkAuxiliaryCutoff K)
    (adjacentEvenIncidentFixedFaceIds radius link)

def adjacentEvenFixedIncidenceTrajectoryStates
    (K radius : Nat) : List FixedIncidenceTrajectoryState :=
  heterogeneousChoices (zeroLabellingOn : Nat → Nat)
    (adjacentEvenFixedLinkTrajectoryOptions K radius)
    (adjacentEvenFixedLinks radius)

def adjacentEvenFixedIncidenceTrajectoryFactor
    (radius : Nat) (physical : Nat → Nat)
    (source target : Z4Link → Nat)
    (link : Z4Link) (channel : Nat → Nat) : Q' :=
  Q'.ofNat (fixedIdTrajectoryMultiplicity physical channel
    (source link) (target link)
    (adjacentEvenIncidentFixedFaceIds radius link))

/-- One global sum over all compatible per-link internal channel trajectories,
with every literal fixed link included exactly once. -/
def adjacentEvenGlobalFixedIncidenceTrajectoryKernel
    (K radius : Nat) (physical : Nat → Nat)
    (source target : Z4Link → Nat) : Q' :=
  listQSum (fun trajectory =>
    listQProduct (fun link =>
      adjacentEvenFixedIncidenceTrajectoryFactor radius physical
        source target link (trajectory link))
      (adjacentEvenFixedLinks radius))
    (adjacentEvenFixedIncidenceTrajectoryStates K radius)

/-- The global incidence-trajectory sum is exactly the product of the literal
multi-fixed transition matrix elements on all fixed links. -/
theorem adjacentEvenGlobalFixedIncidenceTrajectoryKernel_eqv_transitionProduct
    (K radius : Nat) (physical : Nat → Nat)
    (source target : Z4Link → Nat) :
    adjacentEvenGlobalFixedIncidenceTrajectoryKernel
        K radius physical source target ≈
      listQProduct (fun link =>
        Q'.ofNat (fusionWalkMultiplicity (linkAuxiliaryCutoff K)
          (source link) (target link)
          (adjacentEvenIncidentFixedSpins radius physical link)))
        (adjacentEvenFixedLinks radius) := by
  unfold adjacentEvenGlobalFixedIncidenceTrajectoryKernel
    adjacentEvenFixedIncidenceTrajectoryStates
    adjacentEvenFixedIncidenceTrajectoryFactor
    adjacentEvenFixedLinkTrajectoryOptions
  refine Q'.eqv_trans _ _ _
    (heterogeneousChoices_product_fubini
      (zeroLabellingOn : Nat → Nat)
      (fun link => boundedLabellingsOn (linkAuxiliaryCutoff K)
        (adjacentEvenIncidentFixedFaceIds radius link))
      (fun link channel =>
        Q'.ofNat (fixedIdTrajectoryMultiplicity physical channel
          (source link) (target link)
          (adjacentEvenIncidentFixedFaceIds radius link)))
      (adjacentEvenFixedLinks radius)
      (adjacentEvenFixedLinks_nodup radius)) ?_
  apply listQProduct_congr_eqv
  intro link _
  exact Q'.eqv_symm
    (ofNat_adjacentEvenFixedWordTransition_eqv_trajectorySum
      K radius (source link) (target link) physical link)

#print axioms heterogeneousChoices_product_fubini
#print axioms heterogeneousChoices_sound
#print axioms adjacentEvenGlobalFixedIncidenceTrajectoryKernel_eqv_transitionProduct

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
