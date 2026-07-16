/-
# Reflection-equivariant cellular parity blocking on the corrected Z4 slab

The boundary-complete slab has maximum vertex time `extent`.  A dyadic fine
slab compatible with this convention has maximum time `2 * extent + 1`, not
`2 * extent`: each coarse time layer has two fine representatives and the
half-time reflection exchanges those representatives.  At that affine extent
the four nondegenerate fine-face fibres are permuted by reflection, so their
F2 XOR is exactly equivariant.

This file turns that geometry into a source-dependent, positive, exactly
row-normalized deterministic kernel on canonical coarse support lists.  Every
coarse output bit depends only on its four explicit fine-face preimages, and
the whole kernel intertwines the fine and coarse slab reflections.  These are
finite configuration-geometric statements only; no interacting Yang--Mills
weight pushforward or coupling-flow estimate is asserted.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.Z4DyadicModTwoCellularKernel
import YMGap.Continuum.Z4HalfTimeReflectionGeometry

namespace YMGap.Continuum.Z4DyadicSlabReflectionParityKernel

set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The affine fine-slab extent and reflected face fibres -/

/-- Maximum fine vertex time compatible with a coarse slab of maximum time
`extent`.  The terminal `+ 1` is forced by boundary-complete reflection. -/
def dyadicSlabFineExtent (extent : Nat) : Nat :=
  2 * extent + 1

private theorem swapTwoByTwo {A : Type}
    (first second third fourth : A) :
    [third, fourth, first, second].Perm
      [first, second, third, fourth] := by
  change ([third, fourth] ++ [first, second]).Perm
    ([first, second] ++ [third, fourth])
  exact List.perm_append_comm

/-- Reflection permutes the four nondegenerate fine faces above a coarse
face.  Spatial faces exchange their two fine time layers; time-oriented
faces retain their unique odd fine base time. -/
theorem timeReflect_dyadicFacePreimages_perm
    (extent : Nat) (coarsePlaquette : Z4Plaq)
    (hadmissible : plaquetteTimeAdmissible extent coarsePlaquette) :
    ((dyadicFacePreimages coarsePlaquette).map
        (timeReflectPlaquette (dyadicSlabFineExtent extent))).Perm
      (dyadicFacePreimages
        (timeReflectPlaquette extent coarsePlaquette)) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarsePlaquette
  cases plane with
  | p01 =>
      have hd : d ≤ extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have heven : 2 * extent + 1 - 2 * d = 2 * (extent - d) + 1 := by
        omega
      have hodd : 2 * extent + 1 - (2 * d + 1) = 2 * (extent - d) := by
        omega
      simpa [dyadicSlabFineExtent, dyadicFacePreimages,
        timeReflectPlaquette, heven, hodd] using
        (swapTwoByTwo
          (((2*a+1, 2*b+1, 2*c, 2*(extent-d)), .p01) : Z4Plaq)
          (((2*a+1, 2*b+1, 2*c+1, 2*(extent-d)), .p01) : Z4Plaq)
          (((2*a+1, 2*b+1, 2*c, 2*(extent-d)+1), .p01) : Z4Plaq)
          (((2*a+1, 2*b+1, 2*c+1, 2*(extent-d)+1), .p01) : Z4Plaq))
  | p02 =>
      have hd : d ≤ extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have heven : 2 * extent + 1 - 2 * d = 2 * (extent - d) + 1 := by
        omega
      have hodd : 2 * extent + 1 - (2 * d + 1) = 2 * (extent - d) := by
        omega
      simpa [dyadicSlabFineExtent, dyadicFacePreimages,
        timeReflectPlaquette, heven, hodd] using
        (swapTwoByTwo
          (((2*a+1, 2*b, 2*c+1, 2*(extent-d)), .p02) : Z4Plaq)
          (((2*a+1, 2*b+1, 2*c+1, 2*(extent-d)), .p02) : Z4Plaq)
          (((2*a+1, 2*b, 2*c+1, 2*(extent-d)+1), .p02) : Z4Plaq)
          (((2*a+1, 2*b+1, 2*c+1, 2*(extent-d)+1), .p02) : Z4Plaq))
  | p03 =>
      have hd : d < extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have htime :
          2 * extent + 1 - (2 * d + 1 + 1) =
            2 * (extent - (d + 1)) + 1 := by
        omega
      simp [dyadicSlabFineExtent, dyadicFacePreimages,
        timeReflectPlaquette, htime]
  | p12 =>
      have hd : d ≤ extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have heven : 2 * extent + 1 - 2 * d = 2 * (extent - d) + 1 := by
        omega
      have hodd : 2 * extent + 1 - (2 * d + 1) = 2 * (extent - d) := by
        omega
      simpa [dyadicSlabFineExtent, dyadicFacePreimages,
        timeReflectPlaquette, heven, hodd] using
        (swapTwoByTwo
          (((2*a, 2*b+1, 2*c+1, 2*(extent-d)), .p12) : Z4Plaq)
          (((2*a+1, 2*b+1, 2*c+1, 2*(extent-d)), .p12) : Z4Plaq)
          (((2*a, 2*b+1, 2*c+1, 2*(extent-d)+1), .p12) : Z4Plaq)
          (((2*a+1, 2*b+1, 2*c+1, 2*(extent-d)+1), .p12) : Z4Plaq))
  | p13 =>
      have hd : d < extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have htime :
          2 * extent + 1 - (2 * d + 1 + 1) =
            2 * (extent - (d + 1)) + 1 := by
        omega
      simp [dyadicSlabFineExtent, dyadicFacePreimages,
        timeReflectPlaquette, htime]
  | p23 =>
      have hd : d < extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have htime :
          2 * extent + 1 - (2 * d + 1 + 1) =
            2 * (extent - (d + 1)) + 1 := by
        omega
      simp [dyadicSlabFineExtent, dyadicFacePreimages,
        timeReflectPlaquette, htime]

/-- Every explicit fine face above a corrected-slab coarse face belongs to
the affine fine slab.  Thus no hidden face outside the declared finite
geometry enters the local XOR. -/
theorem dyadicFacePreimage_mem_boundaryCompleteFineSlab
    {extent : Nat} {coarsePlaquette finePlaquette : Z4Plaq}
    (hcoarse : coarsePlaquette ∈
      boundaryCompleteSlabPlaquettes extent)
    (hpreimage : finePlaquette ∈
      dyadicFacePreimages coarsePlaquette) :
    finePlaquette ∈
      boundaryCompleteSlabPlaquettes (dyadicSlabFineExtent extent) := by
  have hparts :=
    (mem_boundaryCompleteSlabPlaquettes extent coarsePlaquette).mp hcoarse
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarsePlaquette
  cases plane <;>
    simp only [dyadicFacePreimages, List.mem_cons, List.not_mem_nil,
      or_false] at hpreimage <;>
    rcases hpreimage with h | h | h | h <;>
    subst finePlaquette <;>
    simp only [mem_boxPlaquettes] at hparts <;>
    simp only [plaquetteTimeAdmissible] at hparts <;>
    apply (mem_boundaryCompleteSlabPlaquettes
      (dyadicSlabFineExtent extent) _).mpr <;>
    exact ⟨by
      simp only [mem_boxPlaquettes, dyadicSlabFineExtent]
      exact ⟨by omega, by omega, by omega, by omega⟩,
      by
        simp only [dyadicSlabFineExtent, plaquetteTimeAdmissible]
        omega⟩

/-! ## 2. Exact coefficient-level reflection commutation -/

def reflectSlabFaceCoefficient
    (extent : Nat) (coefficient : Z4Plaq → Bool) : Z4Plaq → Bool :=
  fun plaquette => coefficient (timeReflectPlaquette extent plaquette)

private theorem xorList_map {A B : Type}
    (coefficient : B → Bool) (f : A → B) :
    ∀ entries : List A,
      xorList coefficient (entries.map f) =
        xorList (fun entry => coefficient (f entry)) entries
  | [] => rfl
  | head :: tail => by
      simp only [List.map, xorList]
      rw [xorList_map coefficient f tail]

private theorem xorList_perm {A : Type} (coefficient : A → Bool)
    {first second : List A} (hperm : first.Perm second) :
    xorList coefficient first = xorList coefficient second := by
  induction hperm with
  | nil => rfl
  | cons head hperm ih =>
      simp only [xorList]
      rw [ih]
  | swap first second tail =>
      simp only [xorList]
      exact Bool.xor_left_comm _ _ _
  | trans _ _ ihFirst ihSecond =>
      exact ihFirst.trans ihSecond

/-- Cellular face parity commutes pointwise with corrected-slab reflection.
This is the exact local intertwining identity required by the kernel below. -/
theorem dyadicFacePushforward_reflection
    (extent : Nat) (fineCoefficient : Z4Plaq → Bool)
    (coarsePlaquette : Z4Plaq)
    (hadmissible : plaquetteTimeAdmissible extent coarsePlaquette) :
    dyadicFacePushforward
        (reflectSlabFaceCoefficient (dyadicSlabFineExtent extent)
          fineCoefficient)
        coarsePlaquette =
      dyadicFacePushforward fineCoefficient
        (timeReflectPlaquette extent coarsePlaquette) := by
  unfold dyadicFacePushforward reflectSlabFaceCoefficient
  rw [← xorList_map fineCoefficient
    (timeReflectPlaquette (dyadicSlabFineExtent extent))
    (dyadicFacePreimages coarsePlaquette)]
  exact xorList_perm fineCoefficient
    (timeReflect_dyadicFacePreimages_perm
      extent coarsePlaquette hadmissible)

/-! ## 3. Canonical slab supports and their reflection -/

def dyadicSlabSupportStateSpace (extent : Nat) :
    List (List Z4Plaq) :=
  sublists (boundaryCompleteSlabPlaquettes extent)

theorem dyadicSlabSupportStateSpace_nodup (extent : Nat) :
    (dyadicSlabSupportStateSpace extent).Nodup := by
  unfold dyadicSlabSupportStateSpace
  exact sublists_nodup
    (boundaryCompleteSlabPlaquettes extent)
    (boundaryCompleteSlabPlaquettes_nodup extent)

/-- The canonical coarse support obtained by retaining precisely the true
local parity coefficients in corrected-slab order. -/
def dyadicSlabParitySupport (extent : Nat)
    (fineCoefficient : Z4Plaq → Bool) : List Z4Plaq :=
  (boundaryCompleteSlabPlaquettes extent).filter
    (dyadicFacePushforward fineCoefficient)

theorem dyadicSlabParitySupport_mem_stateSpace
    (extent : Nat) (fineCoefficient : Z4Plaq → Bool) :
    dyadicSlabParitySupport extent fineCoefficient ∈
      dyadicSlabSupportStateSpace extent := by
  unfold dyadicSlabParitySupport dyadicSlabSupportStateSpace
  exact filter_mem_sublists _ _

theorem mem_dyadicSlabParitySupport_iff
    (extent : Nat) (fineCoefficient : Z4Plaq → Bool)
    (coarsePlaquette : Z4Plaq) :
    coarsePlaquette ∈ dyadicSlabParitySupport extent fineCoefficient ↔
      coarsePlaquette ∈ boundaryCompleteSlabPlaquettes extent ∧
        dyadicFacePushforward fineCoefficient coarsePlaquette = true := by
  simp [dyadicSlabParitySupport]

/-- Canonical reflection of a coarse support.  Filtering the fixed slab list
removes order artifacts from reflecting a list pointwise. -/
def reflectCanonicalSlabSupport
    (extent : Nat) (support : List Z4Plaq) : List Z4Plaq :=
  (boundaryCompleteSlabPlaquettes extent).filter
    (reflectSlabFaceCoefficient extent (supportCoefficient support))

theorem reflectCanonicalSlabSupport_mem_stateSpace
    (extent : Nat) (support : List Z4Plaq) :
    reflectCanonicalSlabSupport extent support ∈
      dyadicSlabSupportStateSpace extent := by
  unfold reflectCanonicalSlabSupport dyadicSlabSupportStateSpace
  exact filter_mem_sublists _ _

theorem mem_reflectCanonicalSlabSupport_iff
    (extent : Nat) (support : List Z4Plaq) (plaquette : Z4Plaq) :
    plaquette ∈ reflectCanonicalSlabSupport extent support ↔
      plaquette ∈ boundaryCompleteSlabPlaquettes extent ∧
        timeReflectPlaquette extent plaquette ∈ support := by
  simp [reflectCanonicalSlabSupport, reflectSlabFaceCoefficient,
    supportCoefficient]

/-- Canonical slab reflection is an involution on the enumerated support
state space. -/
theorem reflectCanonicalSlabSupport_involutive
    {extent : Nat} {support : List Z4Plaq}
    (hstate : support ∈ dyadicSlabSupportStateSpace extent) :
    reflectCanonicalSlabSupport extent
        (reflectCanonicalSlabSupport extent support) = support := by
  apply sublists_eq_of_mem_iff
    (boundaryCompleteSlabPlaquettes extent)
    (reflectCanonicalSlabSupport extent
      (reflectCanonicalSlabSupport extent support))
    support
    (boundaryCompleteSlabPlaquettes_nodup extent)
    (reflectCanonicalSlabSupport_mem_stateSpace extent _)
    hstate
  intro plaquette
  constructor
  · intro hmem
    have hfirst :=
      (mem_reflectCanonicalSlabSupport_iff extent
        (reflectCanonicalSlabSupport extent support) plaquette).mp hmem
    have hreflected :=
      (mem_reflectCanonicalSlabSupport_iff extent support
        (timeReflectPlaquette extent plaquette)).mp hfirst.2
    have hadmissible :=
      ((mem_boundaryCompleteSlabPlaquettes extent plaquette).mp
        hfirst.1).2
    simpa [timeReflectPlaquette_involutive extent plaquette hadmissible]
      using hreflected.2
  · intro hmem
    have hslab : plaquette ∈ boundaryCompleteSlabPlaquettes extent :=
      mem_of_mem_sublists
        (boundaryCompleteSlabPlaquettes extent) support hstate
        plaquette hmem
    apply (mem_reflectCanonicalSlabSupport_iff extent
      (reflectCanonicalSlabSupport extent support) plaquette).mpr
    refine ⟨hslab, ?_⟩
    apply (mem_reflectCanonicalSlabSupport_iff extent support
      (timeReflectPlaquette extent plaquette)).mpr
    refine ⟨timeReflectPlaquette_mem_boundaryCompleteSlab hslab, ?_⟩
    have hadmissible :=
      ((mem_boundaryCompleteSlabPlaquettes extent plaquette).mp hslab).2
    simpa [timeReflectPlaquette_involutive extent plaquette hadmissible]
      using hmem

/-- Exact equivariance of the complete canonical output support. -/
theorem dyadicSlabParitySupport_reflection
    (extent : Nat) (fineCoefficient : Z4Plaq → Bool) :
    dyadicSlabParitySupport extent
        (reflectSlabFaceCoefficient (dyadicSlabFineExtent extent)
          fineCoefficient) =
      reflectCanonicalSlabSupport extent
        (dyadicSlabParitySupport extent fineCoefficient) := by
  apply sublists_eq_of_mem_iff
    (boundaryCompleteSlabPlaquettes extent)
    (dyadicSlabParitySupport extent
      (reflectSlabFaceCoefficient (dyadicSlabFineExtent extent)
        fineCoefficient))
    (reflectCanonicalSlabSupport extent
      (dyadicSlabParitySupport extent fineCoefficient))
    (boundaryCompleteSlabPlaquettes_nodup extent)
    (dyadicSlabParitySupport_mem_stateSpace extent _)
    (reflectCanonicalSlabSupport_mem_stateSpace extent _)
  intro coarsePlaquette
  constructor
  · intro hmem
    have hparts := (mem_dyadicSlabParitySupport_iff extent
      (reflectSlabFaceCoefficient (dyadicSlabFineExtent extent)
        fineCoefficient) coarsePlaquette).mp hmem
    apply (mem_reflectCanonicalSlabSupport_iff extent
      (dyadicSlabParitySupport extent fineCoefficient)
      coarsePlaquette).mpr
    refine ⟨hparts.1, ?_⟩
    apply (mem_dyadicSlabParitySupport_iff extent fineCoefficient
      (timeReflectPlaquette extent coarsePlaquette)).mpr
    refine ⟨timeReflectPlaquette_mem_boundaryCompleteSlab hparts.1, ?_⟩
    rw [← dyadicFacePushforward_reflection extent fineCoefficient
      coarsePlaquette
      ((mem_boundaryCompleteSlabPlaquettes extent coarsePlaquette).mp
        hparts.1).2]
    exact hparts.2
  · intro hmem
    have hparts := (mem_reflectCanonicalSlabSupport_iff extent
      (dyadicSlabParitySupport extent fineCoefficient)
      coarsePlaquette).mp hmem
    have himage := (mem_dyadicSlabParitySupport_iff extent fineCoefficient
      (timeReflectPlaquette extent coarsePlaquette)).mp hparts.2
    apply (mem_dyadicSlabParitySupport_iff extent
      (reflectSlabFaceCoefficient (dyadicSlabFineExtent extent)
        fineCoefficient) coarsePlaquette).mpr
    refine ⟨hparts.1, ?_⟩
    rw [dyadicFacePushforward_reflection extent fineCoefficient
      coarsePlaquette
      ((mem_boundaryCompleteSlabPlaquettes extent coarsePlaquette).mp
        hparts.1).2]
    exact himage.2

/-! ## 4. Positive normalized local kernel and reflection intertwining -/

def dyadicSlabParityKernel (extent : Nat)
    (fineCoefficient : Z4Plaq → Bool)
    (coarseSupport : List Z4Plaq) : Q' :=
  deterministicKernel (dyadicSlabParitySupport extent)
    fineCoefficient coarseSupport

theorem dyadicSlabParityKernel_nonnegative
    (extent : Nat) (fineCoefficient : Z4Plaq → Bool)
    (coarseSupport : List Z4Plaq) :
    (0 : Q') ≤
      dyadicSlabParityKernel extent fineCoefficient coarseSupport := by
  exact deterministicKernel_nonnegative
    (dyadicSlabParitySupport extent) fineCoefficient coarseSupport

theorem dyadicSlabParityKernel_row_normalized
    (extent : Nat) (fineCoefficient : Z4Plaq → Bool) :
    listQSum (dyadicSlabParityKernel extent fineCoefficient)
        (dyadicSlabSupportStateSpace extent) ≈ 1 := by
  exact deterministicKernel_row_normalized
    (dyadicSlabParitySupport extent) fineCoefficient
    (dyadicSlabSupportStateSpace extent)
    (dyadicSlabSupportStateSpace_nodup extent)
    (dyadicSlabParitySupport_mem_stateSpace extent fineCoefficient)

/-- Membership of a single coarse output face uses only its four explicit
fine preimages. -/
theorem dyadicSlabParitySupport_membership_local
    (extent : Nat) (first second : Z4Plaq → Bool)
    (coarsePlaquette : Z4Plaq)
    (hlocal : ∀ finePlaquette,
      finePlaquette ∈ dyadicFacePreimages coarsePlaquette →
        first finePlaquette = second finePlaquette) :
    coarsePlaquette ∈ dyadicSlabParitySupport extent first ↔
      coarsePlaquette ∈ dyadicSlabParitySupport extent second := by
  constructor <;> intro hmem
  · have hparts :=
      (mem_dyadicSlabParitySupport_iff extent first coarsePlaquette).mp hmem
    apply (mem_dyadicSlabParitySupport_iff extent second
      coarsePlaquette).mpr
    exact ⟨hparts.1, by
      rw [← dyadicFacePushforward_local first second
        coarsePlaquette hlocal]
      exact hparts.2⟩
  · have hparts :=
      (mem_dyadicSlabParitySupport_iff extent second coarsePlaquette).mp hmem
    apply (mem_dyadicSlabParitySupport_iff extent first
      coarsePlaquette).mpr
    exact ⟨hparts.1, by
      rw [dyadicFacePushforward_local first second
        coarsePlaquette hlocal]
      exact hparts.2⟩

/-- The deterministic parity kernel exactly intertwines corrected-slab
reflection on every canonical target state. -/
theorem dyadicSlabParityKernel_reflection_equivariant
    (extent : Nat) (fineCoefficient : Z4Plaq → Bool)
    (coarseSupport : List Z4Plaq)
    (hcoarse : coarseSupport ∈ dyadicSlabSupportStateSpace extent) :
    dyadicSlabParityKernel extent
        (reflectSlabFaceCoefficient (dyadicSlabFineExtent extent)
          fineCoefficient)
        (reflectCanonicalSlabSupport extent coarseSupport) =
      dyadicSlabParityKernel extent fineCoefficient coarseSupport := by
  unfold dyadicSlabParityKernel
  unfold deterministicKernel
  rw [dyadicSlabParitySupport_reflection extent fineCoefficient]
  by_cases himage :
      coarseSupport = dyadicSlabParitySupport extent fineCoefficient
  · subst coarseSupport
    simp
  · have hreflectedNe :
        reflectCanonicalSlabSupport extent coarseSupport ≠
          reflectCanonicalSlabSupport extent
            (dyadicSlabParitySupport extent fineCoefficient) := by
      intro hreflected
      have htwice := congrArg (reflectCanonicalSlabSupport extent) hreflected
      rw [reflectCanonicalSlabSupport_involutive hcoarse,
        reflectCanonicalSlabSupport_involutive
          (dyadicSlabParitySupport_mem_stateSpace extent fineCoefficient)]
        at htwice
      exact himage htwice
    simp [himage, hreflectedNe]

/-! ## 5. Fence for the naive even fine extent -/

def bottomDyadicSlabWitness : Z4Plaq :=
  ((0, 0, 0, 0), .p01)

/-- With fine extent `2` over coarse extent `1`, reflection does not permute
the dyadic fibre: a reflected child remains at time `1`, while the reflected
coarse fibre occupies times `2` and `3`.  This concrete fence explains the
affine `2 * extent + 1` convention above. -/
theorem evenFineExtent_reflection_fibre_obstruction :
    ¬ ((dyadicFacePreimages bottomDyadicSlabWitness).map
        (timeReflectPlaquette 2)).Perm
      (dyadicFacePreimages
        (timeReflectPlaquette 1 bottomDyadicSlabWitness)) := by
  intro hperm
  let witness : Z4Plaq := ((1, 1, 0, 1), .p01)
  have hwitnessLeft : witness ∈
      (dyadicFacePreimages bottomDyadicSlabWitness).map
        (timeReflectPlaquette 2) := by
    simp [witness, bottomDyadicSlabWitness, dyadicFacePreimages,
      timeReflectPlaquette]
  have hwitnessRight : witness ∈ dyadicFacePreimages
      (timeReflectPlaquette 1 bottomDyadicSlabWitness) :=
    (List.Perm.mem_iff hperm).mp hwitnessLeft
  simp [witness, bottomDyadicSlabWitness, dyadicFacePreimages,
    timeReflectPlaquette] at hwitnessRight

/-! ## Axiom audit -/

#print axioms timeReflect_dyadicFacePreimages_perm
#print axioms dyadicFacePreimage_mem_boundaryCompleteFineSlab
#print axioms dyadicFacePushforward_reflection
#print axioms dyadicSlabSupportStateSpace_nodup
#print axioms dyadicSlabParitySupport_mem_stateSpace
#print axioms reflectCanonicalSlabSupport_involutive
#print axioms dyadicSlabParitySupport_reflection
#print axioms dyadicSlabParityKernel_nonnegative
#print axioms dyadicSlabParityKernel_row_normalized
#print axioms dyadicSlabParitySupport_membership_local
#print axioms dyadicSlabParityKernel_reflection_equivariant
#print axioms evenFineExtent_reflection_fibre_obstruction

end YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
