/-
# Literal width inclusion does not descend to the physical bond completion

At EVERY positive width, a literal boundary plaquette minus its one-step
advance is bond-null and its SAME included source is not bond-null after
ANY strict padding.
This uses each width's ORIGINAL action and OWN centering; no equality of
means across widths is assumed. Consequently no function between those
physical bond completions can preserve the literal inclusion of EVERY dense
source, even without linearity, continuity or time-intertwining assumptions.

The obstruction concerns full literal inclusion from the inclusive fringe.
It does not rule out controlled bulk comparisons, larger-width estimates,
approximate comparison maps or thermodynamic/continuum constructions.
-/

import YMGap.Continuum.BF4WilsonAllNomeCenteringPin
import YMGap.Continuum.BF4WilsonAllNomeFringeTimeKernel
import YMGap.Continuum.BF4WilsonAllNomeBondOSTime
import YMGap.Continuum.BF4WilsonAllNomeDyadicDenseNaturality

namespace YMGap.Continuum.BF4WilsonAllNomeWidthInclusionObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq Z4Link edgesOf dirsOf addE)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
  (spatialFaces spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
  (FullyActive StrictSliceLink active_index_iff spatial_face_link_mem)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
  (uniformFloor uniformFloor_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
  (inclusion inclusion_zero inclusion_difference inclusion_advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDenseNaturality (inclusion_loopState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection
open YMGap.Continuum.BF4WilsonAllNomeCenteringPin (centeredPart_embed)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
  (plaquetteExcitation plaquetteExcitation_response_floor)
open YMGap.Continuum.BF4WilsonAllNomeFringeTimeKernel
  (inactive_face_time_one_zero)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (image)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
  (root_zero root_zero_iff_time_zero)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "E" => embed hw0 hw1
local notation "Z" => completedZero hw0 hw1 width

private theorem sub_zero_iff (x y : V) :
    completedSub hw0 hw1 x y = Z ↔ x = y := by
  constructor
  · intro h
    have hh := congrArg (fun z => completedAdd hw0 hw1 z y) h
    change completedAdd hw0 hw1 (completedSub hw0 hw1 x y) y =
      completedAdd hw0 hw1 Z y at hh
    unfold completedSub at hh
    rw [completedAdd_assoc, completedNeg_add, completedAdd_zero,
      completedZero_add] at hh
    exact hh
  · intro h
    rw [h, completedSub_self]

private theorem projection_time_fixed (n : Nat) (x : V) :
    T n (unitProjection hw0 hw1 x) = unitProjection hw0 hw1 x := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [completedInner_time_balance, unitProjection_pairing,
    ← completedInner_time_balance hw0 hw1 n (unitState hw0 hw1 width) y,
    completedUnit_fixed, unitProjection_pairing]

/-- The actual completed bond source is zero exactly at the original
one-step kernel, not at the ambient nullspace. -/
theorem source_eq_zero_iff_time_kernel (x : IntrinsicExpression width) :
    ofSource hw0 hw1 x = ofSource hw0 hw1 (zero width) ↔ T 1 (E x) = Z := by
  have hz : (image hw0 hw1 (zero width)).val = Z := by
    change root hw0 hw1 1 Z = Z
    exact root_zero hw0 hw1 1
  constructor
  · intro h
    have hh := congrArg (bondValue hw0 hw1) h
    rw [bondValue_ofSource, bondValue_ofSource, hz] at hh
    exact (root_zero_iff_time_zero hw0 hw1 1 (E x)).mp hh
  · intro h
    apply bondValue_injective hw0 hw1
    rw [bondValue_ofSource, bondValue_ofSource, hz]
    exact (root_zero_iff_time_zero hw0 hw1 1 (E x)).mpr h

/-- A literal rational source; no width-specific mean occurs in its syntax. -/
def timeDefect (x : IntrinsicExpression width) : IntrinsicExpression width :=
  difference x (advance 1 x)

theorem embed_timeDefect (x : IntrinsicExpression width) :
    E (timeDefect x) = completedSub hw0 hw1 (E x) (T 1 (E x)) := by
  have h := completedSub_embed hw0 hw1 x (advance 1 x)
  rw [← completedTime_embed] at h
  exact h.symm

/-- Strict completed contraction identifies the nullity of this rational
defect with annihilation of the source's OWN centered one-step image. -/
theorem timeDefect_source_zero_iff (x : IntrinsicExpression width) :
    ofSource hw0 hw1 (timeDefect x) = ofSource hw0 hw1 (zero width) ↔
      T 1 (centeredVector hw0 hw1 x) = Z := by
  rw [source_eq_zero_iff_time_kernel, embed_timeDefect, completedTime_sub,
    sub_zero_iff]
  constructor
  · intro hraw
    let c := centeredPart hw0 hw1 (E x)
    have hc : T 1 c = T 1 (T 1 c) := by
      have h := congrArg (centeredPart hw0 hw1) hraw
      simpa only [centeredPart_time] using h
    let y : VacuumComplement hw0 hw1 (width := width) :=
      ⟨T 1 c, completedTime_preserves_vacuumComplement hw0 hw1 1 c
        (centeredPart_orthogonal hw0 hw1 (E x))⟩
    have hfix : T 1 y.val = y.val := hc.symm
    have htwo : T 2 y.val = y.val := by
      rw [show (2 : Nat) = 1+1 from rfl, completedTime_add, hfix, hfix]
    have hz := BF4WilsonAllNomeGeometry.vacuumComplement_twoStep_fixed_eq_zero
      hw0 hw1 width y htwo
    change T 1 (centeredPart hw0 hw1 (E x)) = Z at hz
    rwa [centeredPart_embed] at hz
  · intro h
    have hc : centeredPart hw0 hw1 (T 1 (E x)) = Z := by
      rw [centeredPart_time, centeredPart_embed]
      exact h
    have hp : T 1 (E x) = unitProjection hw0 hw1 (T 1 (E x)) :=
      (sub_zero_iff hw0 hw1 _ _).mp hc
    exact ((congrArg (T 1) hp).trans
      ((projection_time_fixed hw0 hw1 1 (T 1 (E x))).trans hp.symm)).symm

/-- An explicit retained face with one far edge on the inclusive fringe. -/
def boundaryFace (n : Nat) : Z4Plaq := ((0,n,0,0), .p01)

theorem boundaryFace_mem (n : Nat) : boundaryFace n ∈ spatialFaces (n+1) :=
  (spatialFaces_mem_iff (n+1) (boundaryFace n)).mpr
    ⟨Nat.zero_lt_succ _, Nat.lt_succ_self _, Nat.zero_lt_succ _, rfl,
      by
        change ClusterCount4DProgress.Dir4.x1 ≠ ClusterCount4DProgress.Dir4.x3
        decide⟩

/-- The far x0 edge has y=n+1 and is therefore NOT a transmitted link.
No growing idxOf or active-block enumeration is evaluated. -/
theorem boundaryFace_not_fully_active (n : Nat) :
    ¬ FullyActive (n+1) (boundaryFace n) := by
  intro h
  let link : Z4Link := ((0,n+1,0,0), .x0)
  have hl : link ∈ edgesOf (boundaryFace n) := by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hs := (active_index_iff (n+1) link
    (spatial_face_link_mem (boundaryFace_mem n) hl)).mp (h link hl)
  exact Nat.lt_irrefl (n+1) hs.2.2.1

def boundarySource (n : Nat) : IntrinsicExpression (n+1) :=
  loopState (plaquetteLoop (boundaryFace n) (boundaryFace_mem n))

/-- At EVERY positive literal width this explicit rational defect is null. -/
theorem boundary_timeDefect_source_zero (n : Nat) :
    ofSource hw0 hw1 (timeDefect (boundarySource n)) =
      ofSource hw0 hw1 (zero (n+1)) :=
  (timeDefect_source_zero_iff hw0 hw1 (boundarySource n)).mpr
    (inactive_face_time_one_zero hw0 hw1 (n+1) (boundaryFace n)
      (boundaryFace_mem n) (boundaryFace_not_fully_active n))

/-- For any fully active face, the SAME rational defect is physically
nonnull, by the existing positive original response floor. -/
theorem active_plaquette_timeDefect_source_ne_zero
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) (ha : FullyActive width face) :
    ofSource hw0 hw1 (timeDefect (loopState (plaquetteLoop face hf))) ≠
      ofSource hw0 hw1 (zero width) := by
  intro h
  have hz := (timeDefect_source_zero_iff hw0 hw1
    (loopState (plaquetteLoop face hf))).mp h
  have hfloor := plaquetteExcitation_response_floor hw0 hw1 width face hf ha
  change RCle (Quotient.mk crealSetoid (ofQ' (uniformFloor hw0 width)))
    (completedInner hw0 hw1 (centeredVector hw0 hw1 (loopState (plaquetteLoop face hf)))
      (T 1 (centeredVector hw0 hw1 (loopState (plaquetteLoop face hf))))) at hfloor
  rw [hz, completedInner_zero_right] at hfloor
  have hbad : uniformFloor hw0 width ≤ (0 : Q') :=
    GNSQuotient.GNSData.RCofQ'_le_reflect hfloor
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (uniformFloor_positive hw0 hw1 width) hbad)

/-- Literal inclusion retains the actual ordered face at its unchanged
spatial position. It asserts no equality of interacting expectations. -/
theorem inclusion_plaquetteSource {base larger : Nat} (h : base ≤ larger)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    inclusion h (loopState (plaquetteLoop face hf)) =
      loopState (plaquetteLoop face (spatialFaces_mono h hf)) := by
  rw [inclusion_loopState]
  rfl

/-- Every strict enlargement turns the exhibited narrow null source into
a nonnull source of the ORIGINAL larger-width physical bond completion. -/
theorem included_boundary_timeDefect_source_ne_zero (n larger : Nat)
    (h : n+1 < larger) :
    ofSource hw0 hw1 (inclusion (Nat.le_of_lt h) (timeDefect (boundarySource n))) ≠
      ofSource hw0 hw1 (zero larger) := by
  rw [timeDefect, inclusion_difference, inclusion_advance,
    boundarySource, inclusion_plaquetteSource]
  exact active_plaquette_timeDefect_source_ne_zero hw0 hw1 (boundaryFace n)
    (spatialFaces_mono (Nat.le_of_lt h) (boundaryFace_mem n))
    (plaquette_active_after_padding h (boundaryFace n) (boundaryFace_mem n))

/-- No map on the ORIGINAL physical bond completions descends the full
literal dense inclusion from ANY positive width to ANY strictly larger one.
There are NO linearity, continuity, mean-matching or time-intertwining laws. -/
theorem no_completed_literal_inclusion (n larger : Nat) (h : n+1 < larger)
    (F : BondCompletion hw0 hw1 (width := n+1) →
      BondCompletion hw0 hw1 (width := larger))
    (hF : ∀ x : IntrinsicExpression (n+1),
      F (ofSource hw0 hw1 x) = ofSource hw0 hw1 (inclusion (Nat.le_of_lt h) x)) :
    False := by
  have heq := congrArg F (boundary_timeDefect_source_zero hw0 hw1 n)
  rw [hF, hF, inclusion_zero] at heq
  exact included_boundary_timeDefect_source_ne_zero hw0 hw1 n larger h heq

#print axioms source_eq_zero_iff_time_kernel
#print axioms timeDefect
#print axioms embed_timeDefect
#print axioms timeDefect_source_zero_iff
#print axioms boundaryFace
#print axioms boundaryFace_mem
#print axioms boundaryFace_not_fully_active
#print axioms boundarySource
#print axioms boundary_timeDefect_source_zero
#print axioms active_plaquette_timeDefect_source_ne_zero
#print axioms inclusion_plaquetteSource
#print axioms included_boundary_timeDefect_source_ne_zero
#print axioms no_completed_literal_inclusion

end YMGap.Continuum.BF4WilsonAllNomeWidthInclusionObstruction
