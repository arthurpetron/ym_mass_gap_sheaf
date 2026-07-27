/-
# Reflection-equivariance and CP preservation of the BF4 U(1) block

The direct U(1) BF4 block sums the four signed fine charges over each
nondegenerate dyadic face fibre.  The corrected affine fine extent makes
those fibres reflection-equivariant.  Spatial charges are preserved and
time-oriented charges reverse sign, exactly matching
`reflectChargeLabel`.

This module first proves literal commutation of `u1BlockState` with the
orientation-correct fine and coarse slab reflections.  It then uses that
commutation to transport reflection-positive fine-law quadratics through the
deterministic supported-Dirac pushforward.

## Axiom gate

Finite lists, integers, and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, custom axiom, noncomputable declaration, or placeholder.
-/

import YMGap.Continuum.BF4U1ExponentGramPositivity
import YMGap.Continuum.Z4DyadicSlabReflectionParityKernel

namespace YMGap.Continuum.BF4U1BlockReflectionCP

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
open YMGap.Continuum.BF4U1ExponentGramPositivity
open YMGap.Continuum.BF4U1ReflectionCovariance
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.BF4U1TwistedPhysicalReindex
open YMGap.Continuum.BF4U1TwistedReflectionGram
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Signed charge reading through reflection -/

theorem slabCharge_reflectU1_inside
    (extent : Nat) (physical : ChargeLabelling)
    {plaquette : Z4Plaq}
    (hplaquette :
      plaquette ∈ boundaryCompleteSlabPlaquettes extent) :
    decodeCharge
        (slabSpinAtPlaquette extent
          (reflectU1SlabLabelling extent physical) plaquette) =
      plaquetteReflectionSign plaquette.2 *
        decodeCharge
          (slabSpinAtPlaquette extent physical
            (timeReflectPlaquette extent plaquette)) := by
  have hreflected :=
    timeReflectPlaquette_mem_boundaryCompleteSlab hplaquette
  rw [slabSpinAtPlaquette_eq_of_mem hplaquette,
    slabSpinAtPlaquette_eq_of_mem hreflected]
  have hindex :
      listIndexOf plaquette
          (boundaryCompleteSlabPlaquettes extent) ∈
        slabPhysicalFaceEdges extent := by
    unfold slabPhysicalFaceEdges
    exact List.mem_range.mpr
      (listIndexOf_lt_of_mem plaquette
        (boundaryCompleteSlabPlaquettes extent) hplaquette)
  rw [reflectU1SlabLabelling_on_physical hindex]
  unfold slabFaceReflectId
  have hlookup :
      slabPlaquetteAt extent
          (listIndexOf plaquette
            (boundaryCompleteSlabPlaquettes extent)) =
        plaquette := by
    unfold slabPlaquetteAt
    exact getD_listIndexOf_of_mem fallbackPlaquette plaquette
      (boundaryCompleteSlabPlaquettes extent) hplaquette
  rw [hlookup, decodeCharge_reflectChargeLabel]

/-! ## 2. Finite signed-sum reindexing -/

private theorem listChargeSum_congr_on
    (left right : Z4Plaq → Int) :
    ∀ plaquettes : List Z4Plaq,
      (∀ plaquette, plaquette ∈ plaquettes →
        left plaquette = right plaquette) →
      listChargeSum left plaquettes =
        listChargeSum right plaquettes
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [listChargeSum]
      rw [hagree head List.mem_cons_self,
        listChargeSum_congr_on left right tail
          (fun plaquette hplaquette =>
            hagree plaquette
              (List.mem_cons_of_mem head hplaquette))]

private theorem listChargeSum_map
    (charge : Z4Plaq → Int) (f : Z4Plaq → Z4Plaq) :
    ∀ plaquettes : List Z4Plaq,
      listChargeSum charge (plaquettes.map f) =
        listChargeSum (fun plaquette => charge (f plaquette))
          plaquettes
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listChargeSum]
      rw [listChargeSum_map charge f tail]

private theorem listChargeSum_perm
    (charge : Z4Plaq → Int)
    {left right : List Z4Plaq}
    (hperm : left.Perm right) :
    listChargeSum charge left =
      listChargeSum charge right := by
  induction hperm with
  | nil => rfl
  | cons head _ ih =>
      simp only [listChargeSum]
      rw [ih]
  | swap first second tail =>
      simp only [listChargeSum]
      exact Int.add_left_comm _ _ _
  | trans _ _ ihLeft ihRight =>
      exact ihLeft.trans ihRight

private theorem listChargeSum_mul_left
    (sign : Int) (charge : Z4Plaq → Int) :
    ∀ plaquettes : List Z4Plaq,
      listChargeSum (fun plaquette => sign * charge plaquette)
          plaquettes =
        sign * listChargeSum charge plaquettes
  | [] => by simp [listChargeSum]
  | head :: tail => by
      simp only [listChargeSum]
      rw [listChargeSum_mul_left sign charge tail,
        Int.mul_add]

/-- The signed four-face charge sum intertwines reflection with the
orientation sign of the coarse plaquette. -/
theorem dyadicFaceChargeSum_reflection
    (extent : Nat) (fineState : ChargeLabelling)
    (coarsePlaquette : Z4Plaq)
    (hcoarse : coarsePlaquette ∈
      boundaryCompleteSlabPlaquettes extent) :
    dyadicFaceChargeSum (dyadicSlabFineExtent extent)
        (reflectU1SlabLabelling
          (dyadicSlabFineExtent extent) fineState)
        coarsePlaquette =
      plaquetteReflectionSign coarsePlaquette.2 *
        dyadicFaceChargeSum (dyadicSlabFineExtent extent)
          fineState
          (timeReflectPlaquette extent coarsePlaquette) := by
  have hadmissible :=
    (mem_boundaryCompleteSlabPlaquettes
      extent coarsePlaquette).mp hcoarse |>.2
  let fibre := dyadicFacePreimages coarsePlaquette
  let reflectedCharge : Z4Plaq → Int := fun finePlaquette =>
    decodeCharge
      (slabSpinAtPlaquette (dyadicSlabFineExtent extent)
        (reflectU1SlabLabelling
          (dyadicSlabFineExtent extent) fineState)
        finePlaquette)
  let targetCharge : Z4Plaq → Int := fun finePlaquette =>
    decodeCharge
      (slabSpinAtPlaquette (dyadicSlabFineExtent extent)
        fineState
        (timeReflectPlaquette
          (dyadicSlabFineExtent extent) finePlaquette))
  let originalCharge : Z4Plaq → Int := fun finePlaquette =>
    decodeCharge
      (slabSpinAtPlaquette (dyadicSlabFineExtent extent)
        fineState finePlaquette)
  unfold dyadicFaceChargeSum
  calc
    listChargeSum reflectedCharge fibre =
        listChargeSum
          (fun finePlaquette =>
            plaquetteReflectionSign coarsePlaquette.2 *
              targetCharge finePlaquette)
          fibre := by
      apply listChargeSum_congr_on
      intro finePlaquette hpreimage
      have hfine :=
        dyadicFacePreimage_mem_boundaryCompleteFineSlab
          hcoarse hpreimage
      unfold reflectedCharge targetCharge
      have hreflect :=
        slabCharge_reflectU1_inside
          (dyadicSlabFineExtent extent) fineState hfine
      have hplane : finePlaquette.2 = coarsePlaquette.2 := by
        unfold fibre at hpreimage
        obtain ⟨⟨a,b,c,d⟩, plane⟩ := coarsePlaquette
        cases plane <;>
          simp only [dyadicFacePreimages, List.mem_cons,
            List.not_mem_nil, or_false] at hpreimage <;>
          rcases hpreimage with h | h | h | h <;>
          subst finePlaquette <;> rfl
      simpa [hplane] using hreflect
    _ = plaquetteReflectionSign coarsePlaquette.2 *
        listChargeSum targetCharge fibre :=
      listChargeSum_mul_left _ _ _
    _ = plaquetteReflectionSign coarsePlaquette.2 *
        listChargeSum originalCharge
          (fibre.map
            (timeReflectPlaquette
              (dyadicSlabFineExtent extent))) := by
      rw [listChargeSum_map]
    _ = plaquetteReflectionSign coarsePlaquette.2 *
        listChargeSum originalCharge
          (dyadicFacePreimages
            (timeReflectPlaquette extent coarsePlaquette)) := by
      rw [listChargeSum_perm originalCharge
        (timeReflect_dyadicFacePreimages_perm
          extent coarsePlaquette hadmissible)]

theorem encodeCharge_reflection
    (plane : Z4Plane) (charge : Int) :
    encodeCharge
        (plaquetteReflectionSign plane * charge) =
      reflectChargeLabel plane (encodeCharge charge) := by
  cases plane <;>
    simp [plaquetteReflectionSign, reflectChargeLabel,
      negateChargeLabel, decodeCharge_encodeCharge]

/-! ## 3. The deterministic block intertwines slab reflection -/

theorem u1BlockState_reflection
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff : Nat)
    {fineState : ChargeLabelling}
    (hfine :
      fineState ∈
        (fineU1Data G g hg fineChargeCutoff).states) :
    u1BlockState G fineChargeCutoff
        (reflectU1SlabLabelling
          (centralExtent G.fineHalf) fineState) =
      reflectU1SlabLabelling
        (centralExtent G.coarseHalf)
        (u1BlockState G fineChargeCutoff fineState) := by
  have hreflectedFine :
      reflectU1SlabLabelling
          (centralExtent G.fineHalf) fineState ∈
        (fineU1Data G g hg fineChargeCutoff).states := by
    exact reflectU1SlabLabelling_mem_bounded hfine
  funext id
  by_cases hid :
      id ∈ slabPhysicalFaceEdges
        (centralExtent G.coarseHalf)
  · have hreflectedId := slabFaceReflectId_physical hid
    rw [u1BlockState_eq_direct_on_physical
        G g hg fineChargeCutoff hreflectedFine hid,
      reflectU1SlabLabelling_on_physical hid,
      u1BlockState_eq_direct_on_physical
        G g hg fineChargeCutoff hfine hreflectedId]
    have hcoarse :
        slabPlaquetteAt (centralExtent G.coarseHalf) id ∈
          boundaryCompleteSlabPlaquettes
            (centralExtent G.coarseHalf) :=
      slabPlaquetteAt_mem hid
    have hsum :=
      dyadicFaceChargeSum_reflection
        (centralExtent G.coarseHalf) fineState
        (slabPlaquetteAt
          (centralExtent G.coarseHalf) id) hcoarse
    rw [← G.extent_relation] at hsum
    rw [hsum, encodeCharge_reflection,
      slabPlaquetteAt_slabFaceReflectId hid]
  · unfold u1BlockState
    rw [if_neg hid]
    simp [reflectU1SlabLabelling, hid]

/-! ## 4. Half-space locality of the block -/

private theorem temporalHalfSide_lower_time_lt
    {half time : Nat}
    (hside : temporalHalfSide half time = .lower) :
    time < half := by
  unfold temporalHalfSide at hside
  by_cases hlt : time < half
  · exact hlt
  · rw [if_neg hlt] at hside
    by_cases heq : time = half
    · rw [if_pos heq] at hside
      cases hside
    · rw [if_neg heq] at hside
      cases hside

private theorem spatialHalfSide_lower_time_le
    {half time : Nat}
    (hside : spatialHalfSide half time = .lower) :
    time ≤ half := by
  unfold spatialHalfSide at hside
  by_cases hle : time ≤ half
  · exact hle
  · rw [if_neg hle] at hside
    cases hside

theorem dyadicFacePreimage_lower
    {half : Nat} {coarsePlaquette finePlaquette : Z4Plaq}
    (hcoarse :
      plaquetteHalfSide half coarsePlaquette = .lower)
    (hpreimage :
      finePlaquette ∈ dyadicFacePreimages coarsePlaquette) :
    plaquetteHalfSide (2 * half + 1) finePlaquette = .lower := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := coarsePlaquette
  cases plane with
  | p01 =>
      have hd : d ≤ half := by
        apply spatialHalfSide_lower_time_le
        exact hcoarse
      simp only [dyadicFacePreimages, List.mem_cons,
        List.not_mem_nil, or_false] at hpreimage
      rcases hpreimage with h | h | h | h <;>
        subst finePlaquette <;>
        simp only [plaquetteHalfSide] <;>
        unfold spatialHalfSide <;>
        rw [if_pos (by omega)]
  | p02 =>
      have hd : d ≤ half := by
        apply spatialHalfSide_lower_time_le
        exact hcoarse
      simp only [dyadicFacePreimages, List.mem_cons,
        List.not_mem_nil, or_false] at hpreimage
      rcases hpreimage with h | h | h | h <;>
        subst finePlaquette <;>
        simp only [plaquetteHalfSide] <;>
        unfold spatialHalfSide <;>
        rw [if_pos (by omega)]
  | p03 =>
      have hd : d < half := by
        apply temporalHalfSide_lower_time_lt
        exact hcoarse
      simp only [dyadicFacePreimages, List.mem_cons,
        List.not_mem_nil, or_false] at hpreimage
      rcases hpreimage with h | h | h | h <;>
        subst finePlaquette <;>
        simp only [plaquetteHalfSide] <;>
        unfold temporalHalfSide <;>
        rw [if_pos (by omega)]
  | p12 =>
      have hd : d ≤ half := by
        apply spatialHalfSide_lower_time_le
        exact hcoarse
      simp only [dyadicFacePreimages, List.mem_cons,
        List.not_mem_nil, or_false] at hpreimage
      rcases hpreimage with h | h | h | h <;>
        subst finePlaquette <;>
        simp only [plaquetteHalfSide] <;>
        unfold spatialHalfSide <;>
        rw [if_pos (by omega)]
  | p13 =>
      have hd : d < half := by
        apply temporalHalfSide_lower_time_lt
        exact hcoarse
      simp only [dyadicFacePreimages, List.mem_cons,
        List.not_mem_nil, or_false] at hpreimage
      rcases hpreimage with h | h | h | h <;>
        subst finePlaquette <;>
        simp only [plaquetteHalfSide] <;>
        unfold temporalHalfSide <;>
        rw [if_pos (by omega)]
  | p23 =>
      have hd : d < half := by
        apply temporalHalfSide_lower_time_lt
        exact hcoarse
      simp only [dyadicFacePreimages, List.mem_cons,
        List.not_mem_nil, or_false] at hpreimage
      rcases hpreimage with h | h | h | h <;>
        subst finePlaquette <;>
        simp only [plaquetteHalfSide] <;>
        unfold temporalHalfSide <;>
        rw [if_pos (by omega)]

theorem slabSpinAtPlaquette_lowerRestriction
    (half : Nat) (state : ChargeLabelling)
    {plaquette : Z4Plaq}
    (hplaquette :
      plaquette ∈ boundaryCompleteSlabPlaquettes
        (centralExtent half))
    (hlower :
      plaquetteHalfSide half plaquette = .lower) :
    slabSpinAtPlaquette (centralExtent half)
        (centralLowerRestriction half state) plaquette =
      slabSpinAtPlaquette (centralExtent half)
        state plaquette := by
  rw [slabSpinAtPlaquette_eq_of_mem hplaquette,
    slabSpinAtPlaquette_eq_of_mem hplaquette]
  have hindex :
      listIndexOf plaquette
          (boundaryCompleteSlabPlaquettes
            (centralExtent half)) ∈
        slabPhysicalFaceEdges (centralExtent half) := by
    unfold slabPhysicalFaceEdges
    exact List.mem_range.mpr
      (listIndexOf_lt_of_mem plaquette
        (boundaryCompleteSlabPlaquettes
          (centralExtent half)) hplaquette)
  have hlookup :
      slabPlaquetteAt (centralExtent half)
          (listIndexOf plaquette
            (boundaryCompleteSlabPlaquettes
              (centralExtent half))) =
        plaquette := by
    unfold slabPlaquetteAt
    exact getD_listIndexOf_of_mem fallbackPlaquette plaquette
      (boundaryCompleteSlabPlaquettes
        (centralExtent half)) hplaquette
  have hlowerId :
      listIndexOf plaquette
          (boundaryCompleteSlabPlaquettes
            (centralExtent half)) ∈
        centralLowerFaceIds half := by
    apply mem_centralLowerFaceIds.mpr
    exact ⟨hindex, by rw [hlookup]; exact hlower⟩
  simp [centralLowerRestriction, hlowerId]

theorem dyadicFaceChargeSum_lowerRestriction
    (G : CutoffOneGeometry) (state : ChargeLabelling)
    (coarsePlaquette : Z4Plaq)
    (hcoarseMem :
      coarsePlaquette ∈ boundaryCompleteSlabPlaquettes
        (centralExtent G.coarseHalf))
    (hcoarseLower :
      plaquetteHalfSide G.coarseHalf coarsePlaquette = .lower) :
    dyadicFaceChargeSum (centralExtent G.fineHalf)
        (centralLowerRestriction G.fineHalf state)
        coarsePlaquette =
      dyadicFaceChargeSum (centralExtent G.fineHalf)
        state coarsePlaquette := by
  unfold dyadicFaceChargeSum
  apply listChargeSum_congr_on
  intro finePlaquette hpreimage
  have hfineMem :
      finePlaquette ∈ boundaryCompleteSlabPlaquettes
        (centralExtent G.fineHalf) := by
    have hmem :=
      dyadicFacePreimage_mem_boundaryCompleteFineSlab
        hcoarseMem hpreimage
    rwa [← G.extent_relation] at hmem
  have hfineLower :
      plaquetteHalfSide G.fineHalf finePlaquette = .lower := by
    unfold CutoffOneGeometry.fineHalf
    exact dyadicFacePreimage_lower
      hcoarseLower hpreimage
  rw [slabSpinAtPlaquette_lowerRestriction
    G.fineHalf state hfineMem hfineLower]

/-- Coarse lower labels depend only on the fine lower restriction. -/
theorem centralLowerRestriction_u1BlockState
    (G : CutoffOneGeometry) (fineChargeCutoff : Nat)
    (state : ChargeLabelling) :
    centralLowerRestriction G.coarseHalf
        (u1BlockState G fineChargeCutoff state) =
      centralLowerRestriction G.coarseHalf
        (u1BlockState G fineChargeCutoff
          (centralLowerRestriction G.fineHalf state)) := by
  funext id
  by_cases hid : id ∈ centralLowerFaceIds G.coarseHalf
  · have hparts := mem_centralLowerFaceIds.mp hid
    simp only [centralLowerRestriction, if_pos hid]
    unfold u1BlockState
    rw [if_pos hparts.1, if_pos hparts.1]
    congr 1
    exact (dyadicFaceChargeSum_lowerRestriction G state
      (slabPlaquetteAt
        (centralExtent G.coarseHalf) id)
      (slabPlaquetteAt_mem hparts.1) hparts.2).symm
  · simp [centralLowerRestriction, hid]

theorem u1ReflectedUpperRestriction_eq_lower_reflection
    (half : Nat) (state : ChargeLabelling) :
    u1ReflectedUpperRestriction half state =
      centralLowerRestriction half
        (reflectU1SlabLabelling
          (centralExtent half) state) := by
  funext id
  by_cases hid : id ∈ centralLowerFaceIds half
  · have hparts := mem_centralLowerFaceIds.mp hid
    simp only [u1ReflectedUpperRestriction,
      centralLowerRestriction, if_pos hid]
    rw [reflectU1SlabLabelling_on_physical hparts.1]
  · simp [u1ReflectedUpperRestriction,
      centralLowerRestriction, hid]

/-- Coarse reflected-upper labels depend only on the fine
orientation-correct reflected-upper restriction. -/
theorem u1ReflectedUpperRestriction_u1BlockState
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff : Nat)
    {state : ChargeLabelling}
    (hstate :
      state ∈ (fineU1Data G g hg fineChargeCutoff).states) :
    centralLowerRestriction G.coarseHalf
        (u1BlockState G fineChargeCutoff
          (u1ReflectedUpperRestriction G.fineHalf state)) =
      u1ReflectedUpperRestriction G.coarseHalf
        (u1BlockState G fineChargeCutoff state) := by
  rw [u1ReflectedUpperRestriction_eq_lower_reflection]
  rw [← centralLowerRestriction_u1BlockState
    G fineChargeCutoff
    (reflectU1SlabLabelling
      (centralExtent G.fineHalf) state)]
  rw [u1BlockState_reflection
    G g hg fineChargeCutoff hstate]
  rw [u1ReflectedUpperRestriction_eq_lower_reflection]

/-! ## 5. Global charge conjugation and the pulled half observable -/

theorem slabCharge_conjugate_inside
    (extent : Nat) (state : ChargeLabelling)
    {plaquette : Z4Plaq}
    (hplaquette :
      plaquette ∈ boundaryCompleteSlabPlaquettes extent) :
    decodeCharge
        (slabSpinAtPlaquette extent
          (conjugateChargeLabelling state) plaquette) =
      -decodeCharge
        (slabSpinAtPlaquette extent state plaquette) := by
  rw [slabSpinAtPlaquette_eq_of_mem hplaquette,
    slabSpinAtPlaquette_eq_of_mem hplaquette]
  unfold conjugateChargeLabelling
  exact decodeCharge_negateChargeLabel _

private theorem listChargeSum_neg
    (charge : Z4Plaq → Int) :
    ∀ plaquettes : List Z4Plaq,
      listChargeSum (fun plaquette => -charge plaquette)
          plaquettes =
        -listChargeSum charge plaquettes
  | [] => rfl
  | head :: tail => by
      simp only [listChargeSum]
      rw [listChargeSum_neg charge tail, Int.neg_add]

theorem dyadicFaceChargeSum_conjugate
    (G : CutoffOneGeometry) (state : ChargeLabelling)
    (coarsePlaquette : Z4Plaq)
    (hcoarse :
      coarsePlaquette ∈ boundaryCompleteSlabPlaquettes
        (centralExtent G.coarseHalf)) :
    dyadicFaceChargeSum (centralExtent G.fineHalf)
        (conjugateChargeLabelling state) coarsePlaquette =
      -dyadicFaceChargeSum (centralExtent G.fineHalf)
        state coarsePlaquette := by
  unfold dyadicFaceChargeSum
  refine Eq.trans ?_
    (listChargeSum_neg
      (fun finePlaquette =>
        decodeCharge
          (slabSpinAtPlaquette (centralExtent G.fineHalf)
            state finePlaquette))
      (dyadicFacePreimages coarsePlaquette))
  apply listChargeSum_congr_on
  intro finePlaquette hpreimage
  have hfine :
      finePlaquette ∈ boundaryCompleteSlabPlaquettes
        (centralExtent G.fineHalf) := by
    have hmem :=
      dyadicFacePreimage_mem_boundaryCompleteFineSlab
        hcoarse hpreimage
    rwa [← G.extent_relation] at hmem
  exact slabCharge_conjugate_inside
    (centralExtent G.fineHalf) state hfine

theorem conjugateChargeLabelling_mem_states
    (D : U1SlabData) {state : ChargeLabelling}
    (hstate : state ∈ D.states) :
    conjugateChargeLabelling state ∈ D.states := by
  have hsound := boundedEdgeLabellings_sound
    (2 * D.chargeCutoff)
    (slabPhysicalFaceEdges D.extent) state hstate
  apply boundedEdgeLabellings_complete
  · intro id hid
    unfold conjugateChargeLabelling
    simpa [reflectChargeLabel] using
      (reflectChargeLabel_lt_cutoff
        (plane := Z4Plane.p03)
        (hsound.1 id hid))
  · intro id hid
    unfold conjugateChargeLabelling
    rw [hsound.2 id hid]
    rfl

theorem u1BlockState_conjugate
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff : Nat)
    {state : ChargeLabelling}
    (hstate :
      state ∈ (fineU1Data G g hg fineChargeCutoff).states) :
    u1BlockState G fineChargeCutoff
        (conjugateChargeLabelling state) =
      conjugateChargeLabelling
        (u1BlockState G fineChargeCutoff state) := by
  have hconjugate :
      conjugateChargeLabelling state ∈
        (fineU1Data G g hg fineChargeCutoff).states :=
    conjugateChargeLabelling_mem_states _ hstate
  funext id
  by_cases hid :
      id ∈ slabPhysicalFaceEdges
        (centralExtent G.coarseHalf)
  · rw [u1BlockState_eq_direct_on_physical
        G g hg fineChargeCutoff hconjugate hid,
      dyadicFaceChargeSum_conjugate G state
      (slabPlaquetteAt
        (centralExtent G.coarseHalf) id)
      (slabPlaquetteAt_mem hid)]
    unfold conjugateChargeLabelling
    rw [u1BlockState_eq_direct_on_physical
      G g hg fineChargeCutoff hstate hid]
    unfold negateChargeLabel
    rw [decodeCharge_encodeCharge]
  · have hleft :
        u1BlockState G fineChargeCutoff
            (conjugateChargeLabelling state) id = 0 := by
      unfold u1BlockState
      rw [if_neg hid]
    rw [hleft]
    unfold conjugateChargeLabelling
    have hright :
        u1BlockState G fineChargeCutoff state id = 0 := by
      unfold u1BlockState
      rw [if_neg hid]
    rw [hright]
    rfl

theorem centralLowerRestriction_conjugate
    (half : Nat) (state : ChargeLabelling) :
    centralLowerRestriction half
        (conjugateChargeLabelling state) =
      conjugateChargeLabelling
        (centralLowerRestriction half state) := by
  funext id
  by_cases hid : id ∈ centralLowerFaceIds half
  · simp only [centralLowerRestriction,
      conjugateChargeLabelling, if_pos hid]
  · simp only [centralLowerRestriction,
      conjugateChargeLabelling, if_neg hid]
    rfl

theorem halfState_mem_fullStates
    (D : U1SlabData) {state : ChargeLabelling}
    (hstate : state ∈ u1HalfStates D) :
    state ∈ D.states := by
  have hsound := boundedEdgeLabellings_sound
    (2 * D.chargeCutoff)
    (centralLowerFaceIds D.half) state hstate
  apply boundedEdgeLabellings_complete
  · intro id hid
    by_cases hlower : id ∈ centralLowerFaceIds D.half
    · exact hsound.1 id hlower
    · rw [hsound.2 id hlower]
      omega
  · intro id hid
    apply hsound.2 id
    intro hlower
    exact hid (mem_centralLowerFaceIds.mp hlower).1

def u1BlockPullbackCoefficient
    (G : CutoffOneGeometry) (fineChargeCutoff : Nat)
    (coefficient : ChargeLabelling → Q')
    (fineHalfState : ChargeLabelling) : Q' :=
  coefficient
    (centralLowerRestriction G.coarseHalf
      (u1BlockState G fineChargeCutoff fineHalfState))

theorem u1BlockPullbackCoefficient_even
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coefficient : ChargeLabelling → Q')
    (heven :
      ChargeConjugationEvenOn
        (coarseU1Data G candidate hcandidate fineChargeCutoff)
        coefficient) :
    ChargeConjugationEvenOn
      (fineU1Data G g hg fineChargeCutoff)
      (u1BlockPullbackCoefficient
        G fineChargeCutoff coefficient) := by
  intro state hstate
  have hfull :
      state ∈
        (fineU1Data G g hg fineChargeCutoff).states :=
    halfState_mem_fullStates _ hstate
  have hblocked :
      u1BlockState G fineChargeCutoff state ∈
        (coarseU1Data G candidate hcandidate
          fineChargeCutoff).states :=
    u1BlockState_mem_coarse
      G candidate hcandidate fineChargeCutoff state
  have hlower :
      centralLowerRestriction G.coarseHalf
          (u1BlockState G fineChargeCutoff state) ∈
        u1HalfStates
          (coarseU1Data G candidate hcandidate
            fineChargeCutoff) := by
    exact centralLowerRestriction_mem hblocked
  unfold u1BlockPullbackCoefficient
  rw [u1BlockState_conjugate
    G g hg fineChargeCutoff hfull,
    centralLowerRestriction_conjugate]
  exact heven _ hlower

/-! ## 6. Deterministic CP pushforward -/

private theorem rearrange_observable_mass_kernel
    (observable mass kernel : Q') :
    observable * (mass * kernel) ≈
      mass * (observable * kernel) := by
  show (observable * (mass * kernel)).num *
      (((mass * (observable * kernel)).den) : Int) =
    (mass * (observable * kernel)).num *
      (((observable * (mass * kernel)).den) : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

theorem u1BlockKernel_weighted_row
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (observable : ChargeLabelling → Q')
    (fineState : ChargeLabelling) :
    listQSum
        (fun coarseState =>
          observable coarseState *
            u1BlockKernel G candidate hcandidate
              fineChargeCutoff fineState coarseState)
        (coarseU1Data G candidate hcandidate
          fineChargeCutoff).states ≈
      observable
        (u1BlockState G fineChargeCutoff fineState) := by
  let coarse :=
    coarseU1Data G candidate hcandidate fineChargeCutoff
  let selected :=
    u1BlockState G fineChargeCutoff fineState
  have hselected : selected ∈ coarse.states :=
    u1BlockState_mem_coarse
      G candidate hcandidate fineChargeCutoff fineState
  refine Q'.eqv_trans _
    (listQSum
      (fun coarseState =>
        observable selected *
          u1BlockKernel G candidate hcandidate
            fineChargeCutoff fineState coarseState)
      coarse.states) _ ?_ ?_
  · apply listQSum_congr_on
    intro coarseState hcoarse
    unfold u1BlockKernel
    change observable coarseState *
        supportedDirac coarse.faceEdges selected coarseState ≈
      observable selected *
        supportedDirac coarse.faceEdges selected coarseState
    unfold supportedDirac
    by_cases heq :
        supportedLabellingEqB coarse.faceEdges
          coarseState selected = true
    · rw [if_pos heq]
      have hsame : coarseState = selected := by
        exact (supportedLabellingEqB_true_iff
          hcoarse hselected).mp heq
      subst coarseState
      exact Q'.eqv_refl _
    · have hfalse :
          supportedLabellingEqB coarse.faceEdges
            coarseState selected = false :=
        Bool.eq_false_iff.mpr heq
      rw [if_neg heq]
      exact Q'.eqv_trans _ 0 _
        (Q'.mul_zero_eqv _)
        (Q'.eqv_symm (Q'.mul_zero_eqv _))
  · refine Q'.eqv_trans _
      (observable selected *
        listQSum
          (u1BlockKernel G candidate hcandidate
            fineChargeCutoff fineState)
          coarse.states) _
      (listQSum_mul_left
        (observable selected)
        (u1BlockKernel G candidate hcandidate
          fineChargeCutoff fineState)
        coarse.states) ?_
    exact Q'.eqv_trans _ _
      (observable selected)
      (Q'.mul_eqv_congr_left _ _ _
        (u1BlockKernel_row_normalized
          G candidate hcandidate
          fineChargeCutoff fineState))
      (Q'.mul_one_eqv _)

def u1BlockedObservableExpectation
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (observable : ChargeLabelling → Q') : Q' :=
  listQSum
    (fun coarseState =>
      observable coarseState *
        u1BlockedMass G g hg candidate hcandidate
          fineChargeCutoff coarseState)
    (coarseU1Data G candidate hcandidate
      fineChargeCutoff).states

/-- Exact deterministic pushforward identity for every rational observable
on the coarse signed-charge carrier. -/
theorem u1BlockedObservableExpectation_eq_pullback
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (observable : ChargeLabelling → Q') :
    u1BlockedObservableExpectation G g hg candidate hcandidate
        fineChargeCutoff observable ≈
      listQSum
        (fun fineState =>
          (fineU1Data G g hg fineChargeCutoff).normalizedMass
              fineState *
            observable
              (u1BlockState G fineChargeCutoff fineState))
        (fineU1Data G g hg fineChargeCutoff).states := by
  let fine := fineU1Data G g hg fineChargeCutoff
  let coarse :=
    coarseU1Data G candidate hcandidate fineChargeCutoff
  refine Q'.eqv_trans _
    (listQSum
      (fun coarseState =>
        listQSum
          (fun fineState =>
            observable coarseState *
              (fine.normalizedMass fineState *
                u1BlockKernel G candidate hcandidate
                  fineChargeCutoff fineState coarseState))
          fine.states)
      coarse.states) _ ?_ ?_
  · unfold u1BlockedObservableExpectation u1BlockedMass
    apply listQSum_congr_on
    intro coarseState _
    exact Q'.eqv_symm
      (listQSum_mul_left
        (observable coarseState)
        (fun fineState =>
          fine.normalizedMass fineState *
            u1BlockKernel G candidate hcandidate
              fineChargeCutoff fineState coarseState)
        fine.states)
  · refine Q'.eqv_trans _
      (listQSum
        (fun fineState =>
          listQSum
            (fun coarseState =>
              observable coarseState *
                (fine.normalizedMass fineState *
                  u1BlockKernel G candidate hcandidate
                    fineChargeCutoff fineState coarseState))
            coarse.states)
        fine.states) _
      (listQSum_swap
        (fun fineState coarseState =>
          observable coarseState *
            (fine.normalizedMass fineState *
              u1BlockKernel G candidate hcandidate
                fineChargeCutoff fineState coarseState))
        fine.states coarse.states) ?_
    apply listQSum_congr_on
    intro fineState _
    refine Q'.eqv_trans _
      (listQSum
        (fun coarseState =>
          fine.normalizedMass fineState *
            (observable coarseState *
              u1BlockKernel G candidate hcandidate
                fineChargeCutoff fineState coarseState))
        coarse.states) _ ?_ ?_
    · apply listQSum_congr_on
      intro coarseState _
      exact rearrange_observable_mass_kernel _ _ _
    · refine Q'.eqv_trans _
        (fine.normalizedMass fineState *
          listQSum
            (fun coarseState =>
              observable coarseState *
                u1BlockKernel G candidate hcandidate
                  fineChargeCutoff fineState coarseState)
            coarse.states) _
        (listQSum_mul_left
          (fine.normalizedMass fineState)
          (fun coarseState =>
            observable coarseState *
              u1BlockKernel G candidate hcandidate
                fineChargeCutoff fineState coarseState)
          coarse.states) ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (u1BlockKernel_weighted_row
          G candidate hcandidate fineChargeCutoff
          observable fineState)

/-- The orientation-correct OS quadratic of the actual blocked U(1) law. -/
def u1BlockedFullReflectionQuadratic
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coefficient : ChargeLabelling → Q') : Q' :=
  listQSum
    (fun coarseState =>
      (coefficient
          (centralLowerRestriction G.coarseHalf coarseState) *
        coefficient
          (u1ReflectedUpperRestriction
            G.coarseHalf coarseState)) *
      u1BlockedMass G g hg candidate hcandidate
        fineChargeCutoff coarseState)
    (coarseU1Data G candidate hcandidate
      fineChargeCutoff).states

private theorem u1BlockPullbackCoefficient_lower
    (G : CutoffOneGeometry) (fineChargeCutoff : Nat)
    (coefficient : ChargeLabelling → Q')
    (fineState : ChargeLabelling) :
    u1BlockPullbackCoefficient G fineChargeCutoff coefficient
        (centralLowerRestriction G.fineHalf fineState) =
      coefficient
        (centralLowerRestriction G.coarseHalf
          (u1BlockState G fineChargeCutoff fineState)) := by
  unfold u1BlockPullbackCoefficient
  rw [← centralLowerRestriction_u1BlockState
    G fineChargeCutoff fineState]

private theorem u1BlockPullbackCoefficient_upper
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff : Nat)
    (coefficient : ChargeLabelling → Q')
    {fineState : ChargeLabelling}
    (hfine :
      fineState ∈ (fineU1Data G g hg fineChargeCutoff).states) :
    u1BlockPullbackCoefficient G fineChargeCutoff coefficient
        (u1ReflectedUpperRestriction G.fineHalf fineState) =
      coefficient
        (u1ReflectedUpperRestriction G.coarseHalf
          (u1BlockState G fineChargeCutoff fineState)) := by
  unfold u1BlockPullbackCoefficient
  rw [u1ReflectedUpperRestriction_u1BlockState
    G g hg fineChargeCutoff hfine]

/-- The blocked OS quadratic is exactly the fine normalized OS quadratic of
the block-pulled half observable. -/
theorem u1BlockedFullReflectionQuadratic_eq_finePullback
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coefficient : ChargeLabelling → Q') :
    u1BlockedFullReflectionQuadratic
        G g hg candidate hcandidate fineChargeCutoff coefficient ≈
      u1FullNormalizedMassReflectionQuadratic
        (fineU1Data G g hg fineChargeCutoff)
        (u1BlockPullbackCoefficient
          G fineChargeCutoff coefficient) := by
  let coarseObservable : ChargeLabelling → Q' :=
    fun coarseState =>
      coefficient
          (centralLowerRestriction G.coarseHalf coarseState) *
        coefficient
          (u1ReflectedUpperRestriction
            G.coarseHalf coarseState)
  refine Q'.eqv_trans _
    (listQSum
      (fun fineState =>
        (fineU1Data G g hg fineChargeCutoff).normalizedMass
            fineState *
          coarseObservable
            (u1BlockState G fineChargeCutoff fineState))
      (fineU1Data G g hg fineChargeCutoff).states) _ ?_ ?_
  · exact u1BlockedObservableExpectation_eq_pullback
      G g hg candidate hcandidate fineChargeCutoff
        coarseObservable
  · unfold u1FullNormalizedMassReflectionQuadratic
    apply listQSum_congr_on
    intro fineState hfine
    unfold coarseObservable
    change
      (fineU1Data G g hg fineChargeCutoff).normalizedMass fineState *
          (coefficient
              (centralLowerRestriction G.coarseHalf
                (u1BlockState G fineChargeCutoff fineState)) *
            coefficient
              (u1ReflectedUpperRestriction G.coarseHalf
                (u1BlockState G fineChargeCutoff fineState))) ≈
        (u1BlockPullbackCoefficient G fineChargeCutoff coefficient
              (centralLowerRestriction G.fineHalf fineState) *
            u1BlockPullbackCoefficient G fineChargeCutoff coefficient
              (u1ReflectedUpperRestriction G.fineHalf fineState)) *
          (fineU1Data G g hg fineChargeCutoff).normalizedMass fineState
    rw [u1BlockPullbackCoefficient_lower,
      u1BlockPullbackCoefficient_upper
        G g hg fineChargeCutoff coefficient hfine]
    exact Q'.mul_comm_eqv _ _

/-- CP-order preservation: deterministic BF4 blocking sends the fine
reflection-positive U(1) law to a reflection-positive blocked law on every
charge-conjugation-even coarse observable. -/
theorem u1BlockedFullReflectionQuadratic_nonnegative
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coefficient : ChargeLabelling → Q')
    (heven :
      ChargeConjugationEvenOn
        (coarseU1Data G candidate hcandidate fineChargeCutoff)
        coefficient) :
    (0 : Q') ≤
      u1BlockedFullReflectionQuadratic
        G g hg candidate hcandidate
          fineChargeCutoff coefficient := by
  have hfine :
      (0 : Q') ≤
        u1FullNormalizedMassReflectionQuadratic
          (fineU1Data G g hg fineChargeCutoff)
          (u1BlockPullbackCoefficient
            G fineChargeCutoff coefficient) :=
    u1FullNormalizedMassReflectionQuadratic_nonnegative
      (fineU1Data G g hg fineChargeCutoff)
      (u1BlockPullbackCoefficient
        G fineChargeCutoff coefficient)
      (u1BlockPullbackCoefficient_even
        G g hg candidate hcandidate
          fineChargeCutoff coefficient heven)
  exact Q'.le_trans' _ _ _ hfine
    (Q'.ge_of_eqv
      (u1BlockedFullReflectionQuadratic_eq_finePullback
        G g hg candidate hcandidate
          fineChargeCutoff coefficient))

/-! ## 6. The actual blocked exponent packet -/

/-- The orientation-correct quadratic of a finite packet of heat-exponent
coordinates against the actual BF4 pushed-forward U(1) law. -/
def u1BlockedExponentPacketQuadratic
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coefficients : List (Nat × Q')) : Q' :=
  u1BlockedFullReflectionQuadratic
    G g hg candidate hcandidate fineChargeCutoff
    (u1ExponentLinearCoefficient
      G.coarseHalf coefficients)

/-- Every finite exponent packet of the actual blocked U(1) law is positive.
This is the finite-carrier CP-order statement required by the
same-carrier discriminator. -/
theorem u1BlockedExponentPacketQuadratic_nonnegative
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coefficients : List (Nat × Q')) :
    (0 : Q') ≤
      u1BlockedExponentPacketQuadratic
        G g hg candidate hcandidate
          fineChargeCutoff coefficients := by
  exact u1BlockedFullReflectionQuadratic_nonnegative
    G g hg candidate hcandidate fineChargeCutoff
    (u1ExponentLinearCoefficient
      G.coarseHalf coefficients)
    (u1ExponentLinearCoefficient_even
      (coarseU1Data G candidate hcandidate
        fineChargeCutoff)
      coefficients)

/-- The diagonal entry already used by the SU(2)/U(1) same-carrier
discriminator is exactly the orientation-correct blocked-law quadratic. -/
theorem u1BlockedExponentGramEntry_diagonal_eq_full
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff exponent : Nat) :
    u1BlockedExponentGramEntry
        G g hg candidate hcandidate fineChargeCutoff
        { leftExponent := exponent,
          rightExponent := exponent } ≈
      u1BlockedFullReflectionQuadratic
        G g hg candidate hcandidate fineChargeCutoff
        (u1ExponentCoefficient G.coarseHalf exponent) := by
  unfold u1BlockedExponentGramEntry u1ExponentGramEntry
    reflectedLawBilinear u1BlockedFullReflectionQuadratic
  apply listQSum_congr_on
  intro coarseState _
  rw [u1ExponentCoefficient_reflectedRestrictions]
  exact Q'.eqv_refl _

/-- Consequently, every actual blocked diagonal exponent-Gram coordinate is
nonnegative, with no auxiliary carrier and no assumed reflection axiom. -/
theorem u1BlockedExponentGramEntry_diagonal_nonnegative
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff exponent : Nat) :
    (0 : Q') ≤
      u1BlockedExponentGramEntry
        G g hg candidate hcandidate fineChargeCutoff
        { leftExponent := exponent,
          rightExponent := exponent } := by
  have hpositive :
      (0 : Q') ≤
        u1BlockedFullReflectionQuadratic
          G g hg candidate hcandidate fineChargeCutoff
          (u1ExponentCoefficient
            G.coarseHalf exponent) :=
    u1BlockedFullReflectionQuadratic_nonnegative
      G g hg candidate hcandidate fineChargeCutoff
      (u1ExponentCoefficient G.coarseHalf exponent)
      (u1ExponentCoefficient_even
        (coarseU1Data G candidate hcandidate
          fineChargeCutoff)
        exponent)
  exact Q'.le_trans' _ _ _ hpositive
    (Q'.ge_of_eqv
      (u1BlockedExponentGramEntry_diagonal_eq_full
        G g hg candidate hcandidate
          fineChargeCutoff exponent))

end YMGap.Continuum.BF4U1BlockReflectionCP

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.slabCharge_reflectU1_inside
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.dyadicFaceChargeSum_reflection
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.encodeCharge_reflection
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1BlockState_reflection
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.dyadicFacePreimage_lower
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.dyadicFaceChargeSum_lowerRestriction
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.centralLowerRestriction_u1BlockState
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1ReflectedUpperRestriction_u1BlockState
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.dyadicFaceChargeSum_conjugate
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1BlockState_conjugate
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1BlockPullbackCoefficient_even
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1BlockKernel_weighted_row
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1BlockedObservableExpectation_eq_pullback
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1BlockedFullReflectionQuadratic_eq_finePullback
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1BlockedFullReflectionQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1BlockedExponentPacketQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1BlockedExponentGramEntry_diagonal_eq_full
#print axioms YMGap.Continuum.BF4U1BlockReflectionCP.u1BlockedExponentGramEntry_diagonal_nonnegative
