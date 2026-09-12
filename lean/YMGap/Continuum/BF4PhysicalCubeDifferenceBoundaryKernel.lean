/-
# An explicit positive OS weight for every cube-to-mate move

The difference boundary is an actual bounded production boundary, not a new
dynamics. Its complete physical summand equals an explicit product of heat
coefficients, with all lower, reflected upper, and fixed link multiplicities
equal to one. The product is strictly positive for w > 0 and lies below the
original raw reflected kernel. It depends on w and the six source labels;
no state-uniform transition floor, congestion bound, or spectral gap is claimed.

In particular every bounded cube-supported state is in the genuine positive
half-state carrier. Common parity is not required for that larger carrier.
-/

import YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity

namespace YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity
open YMGap.Continuum.BF4PhysicalHalfCubeSupport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def halfHeat (w : Q') (state : EdgeLabelling) : Q' :=
  eliminateLinks (fun face => coeffW w (state face)) (centralLowerFaceIds 0)

def boundaryHeat (w : Q') (boundary : EdgeLabelling) : Q' :=
  eliminateLinks (fun face => coeffW w (boundary face)) (centralFixedFaceIds 0)

/-- Explicit heat-only lower bound, independent of the cutoff once the source
and mate fit it. This is state-dependent data, not a uniform minorization. -/
def differencePhysicalWeight (w : Q') (state : EdgeLabelling) : Q' :=
  boundaryHeat w (cubeDifferenceBoundary state) *
    (halfHeat w state * halfHeat w (centralLowerCubeEvenInwardMatePhysical state))

private theorem product_congr (left right : Nat → Q') :
    ∀ ids : List Nat, (∀ face, face ∈ ids → left face = right face) →
      eliminateLinks left ids = eliminateLinks right ids
  | [], _ => rfl
  | face :: ids, h => by
      simp only [eliminateLinks, h face List.mem_cons_self,
        product_congr left right ids (fun f hf => h f (List.mem_cons_of_mem face hf))]

private theorem natProduct_one {A : Type} (value : A → Nat) :
    ∀ items : List A, (∀ item, item ∈ items → value item = 1) →
      natListProduct value items = 1
  | [], _ => rfl
  | item :: items, h => by
      simp only [natListProduct, h item List.mem_cons_self,
        natProduct_one value items (fun i hi => h i (List.mem_cons_of_mem item hi)), Nat.one_mul]

private theorem product_pos (value : Nat → Q') (h : ∀ face, (0 : Q') < value face) :
    ∀ ids : List Nat, (0 : Q') < eliminateLinks value ids
  | [] => by change (0 : Q') < 1; decide
  | face :: ids => Q'.mul_pos (h face) (product_pos value h ids)

private theorem qmul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem faceFactor_eq_heat (w : Q') (K : Nat)
    (physical state : EdgeLabelling) (ids : List Nat)
    (hb : ∀ face, state face ≤ K)
    (heq : ∀ face, face ∈ ids → physical face = state face) :
    slabFaceFactorOn w K physical ids =
      eliminateLinks (fun face => coeffW w (state face)) ids := by
  apply product_congr
  intro face hf
  rw [heq face hf, coeffAt_heatKernelPacket (Nat.lt_succ_of_le (hb face))]

theorem halfAmplitude_eq_heat_of_multiplicity_one (w : Q') (K : Nat)
    (state boundary : EdgeLabelling) (hb : ∀ face, state face ≤ K)
    (hm : ∀ link, link ∈ centralLowerLinks 0 → slabExplicitLinkMultiplicity K 1
      (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling) link = 1) :
    centralHalfAmplitude w K 0 state boundary ≈ halfHeat w state := by
  have hprod := natProduct_one _ (centralLowerLinks 0) hm
  unfold centralHalfAmplitude centralLowerFactor slabLinkMultiplicityProductOn
  change slabFaceFactorOn w K _ (centralLowerFaceIds 0) * Q'.ofNat
    (natListProduct (slabExplicitLinkMultiplicity K 1
      (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling)) (centralLowerLinks 0)) ≈ _
  rw [hprod, faceFactor_eq_heat w K _ state _ hb (fun _ hf => assembled_lower state boundary hf)]
  exact Q'.mul_one_eqv _

theorem boundaryWeight_eq_heat_of_multiplicity_one (w : Q') (K : Nat)
    (boundary : EdgeLabelling) (hb : ∀ face, boundary face ≤ K)
    (hm : ∀ link, link ∈ centralFixedLinks 0 → slabExplicitLinkMultiplicity K 1
      (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary zeroEdgeLabelling) link = 1) :
    centralBoundaryWeight w K 0 boundary ≈ boundaryHeat w boundary := by
  have hprod := natProduct_one _ (centralFixedLinks 0) hm
  unfold centralBoundaryWeight centralFixedWeight slabLinkMultiplicityProductOn
  change slabFaceFactorOn w K _ (centralFixedFaceIds 0) * Q'.ofNat
    (natListProduct (slabExplicitLinkMultiplicity K 1
      (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary zeroEdgeLabelling)) (centralFixedLinks 0)) ≈ _
  rw [hprod, faceFactor_eq_heat w K _ boundary _ hb
    (fun _ hf => assembled_fixed zeroEdgeLabelling boundary hf)]
  exact Q'.mul_one_eqv _

theorem cubeSupported_mem_halfStates (K : Nat) (state : EdgeLabelling)
    (hb : ∀ face, state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    state ∈ centralHalfStates K 0 := by
  apply boundedEdgeLabellings_complete
  · intro face _; exact Nat.lt_succ_of_le (hb face)
  · intro face hf
    exact hz face (fun hc => hf (centralLowerCubeFaceIds_subset_lower face hc))

theorem cubeMate_mem_halfStates (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    centralLowerCubeEvenInwardMatePhysical state ∈ centralHalfStates K 0 := by
  apply cubeSupported_mem_halfStates K _ (cubeMate_bounded K hK state hb)
  intro face hf
  rw [centralLowerCubeEvenInwardMatePhysical_off_cube state hf, hz face hf]

/-- The chosen complete production summand has no remaining multiplicity debt. -/
theorem differencePhysicalTerm_eq_weight (w : Q') (K : Nat) (hK : 1 ≤ K)
    (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    slabParametricKPhysicalTerm w K 1 (assembleReflectedSlabLabelling 0 state
      (cubeDifferenceBoundary state) (centralLowerCubeEvenInwardMatePhysical state)) ≈
      differencePhysicalWeight w state := by
  have hbound := cubeSupported_bounded K state hb hz
  refine Q'.eqv_trans _ _ _ (centralPhysicalTerm_eq_gram_integrand w
    (cubeSupported_mem_halfStates K state hbound hz)
    (cubeDifferenceBoundary_mem K state hb) (cubeMate_mem_halfStates K hK state hbound hz)) ?_
  apply qmul_congr
  · exact boundaryWeight_eq_heat_of_multiplicity_one w K _
      (cubeDifferenceBoundary_bounded K state hb) (difference_fixed_multiplicity_one K state hb)
  · apply qmul_congr
    · exact halfAmplitude_eq_heat_of_multiplicity_one w K _ _ hbound
        (difference_source_multiplicity_one K state hb hz)
    · exact halfAmplitude_eq_heat_of_multiplicity_one w K _ _ (cubeMate_bounded K hK state hbound)
        (difference_mate_multiplicity_one K hK state hb hz)

theorem differencePhysicalWeight_pos {w : Q'} (hw : (0 : Q') < w) (state : EdgeLabelling) :
    (0 : Q') < differencePhysicalWeight w state :=
  Q'.mul_pos (product_pos _ (fun _ => coeffW_pos hw _) _)
    (Q'.mul_pos (product_pos _ (fun _ => coeffW_pos hw _) _)
      (product_pos _ (fun _ => coeffW_pos hw _) _))

private theorem sum_nonnegative {A : Type} (value : A → Q')
    (hv : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | item :: items => Q'.zero_le_add _ _ (hv item) (sum_nonnegative value hv items)

private theorem member_le_sum {A : Type} (value : A → Q')
    (hv : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items → value item ≤ listQSum value items
  | [], _, h => False.elim (List.not_mem_nil h)
  | head :: tail, item, h => by
      rcases List.mem_cons.mp h with heq | ht
      · subst item
        exact Q'.add_le_self_of_nonneg _ _ (sum_nonnegative value hv tail)
      · have hmono := Q'.add_le_add_right (0 : Q') (value head) (listQSum value tail) (hv head)
        rw [Q'.zero_add'] at hmono
        exact Q'.le_trans' _ _ _ (member_le_sum value hv tail ht) hmono

theorem differencePhysicalWeight_le_kernel {w : Q'} (hw : (0 : Q') ≤ w)
    (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    differencePhysicalWeight w state ≤ centralPhysicalReflectedKernel w K 0 state
      (centralLowerCubeEvenInwardMatePhysical state) := by
  have hmember := member_le_sum
    (fun boundary => slabParametricKPhysicalTerm w K 1 (assembleReflectedSlabLabelling 0 state
      boundary (centralLowerCubeEvenInwardMatePhysical state)))
    (fun _ => slabParametricKPhysicalTerm_nonnegative hw K 1 _)
    (centralBoundaryChannels K 0) (cubeDifferenceBoundary_mem K state hb)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (differencePhysicalTerm_eq_weight w K hK state hb hz))
    hmember

theorem difference_kernel_pos {w : Q'} (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    (0 : Q') < centralPhysicalReflectedKernel w K 0 state
      (centralLowerCubeEvenInwardMatePhysical state) :=
  Q'.pos_of_lt_of_le (differencePhysicalWeight_pos hw state)
    (differencePhysicalWeight_le_kernel (Q'.le_of_lt hw) K hK state hb hz)

/-- Every cube-supported bounded label assignment belongs to the actual
positive half-state carrier, including its non-vacuum parity components. -/
theorem cubeSupported_mem_positiveHalfStates {w : Q'} (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    state ∈ centralPositiveHalfStates w (Q'.le_of_lt hw) K 0 := by
  have hbound := cubeSupported_bounded K state hb hz
  apply mem_centralPositiveHalfStates_iff.mpr
  refine ⟨cubeSupported_mem_halfStates K state hbound hz, ?_⟩
  have hp : (0 : Q') < centralNormalizedPhysicalReflectedKernel w (Q'.le_of_lt hw) K 0
      state (centralLowerCubeEvenInwardMatePhysical state) := by
    unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
    exact Q'.mul_pos (difference_kernel_pos hw K hK state hb hz) (Q'.recipPos_pos _ _)
  have hmember := member_le_sum
    (centralNormalizedPhysicalReflectedKernel w (Q'.le_of_lt hw) K 0 state)
    (fun target => centralNormalizedPhysicalReflectedKernel_nonnegative (Q'.le_of_lt hw) K 0 state target)
    (centralHalfStates K 0) (cubeMate_mem_halfStates K hK state hbound hz)
  exact Q'.pos_of_lt_of_le hp hmember

end YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel

#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel.differencePhysicalWeight
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel.halfAmplitude_eq_heat_of_multiplicity_one
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel.boundaryWeight_eq_heat_of_multiplicity_one
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel.cubeSupported_mem_halfStates
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel.cubeMate_mem_halfStates
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel.differencePhysicalTerm_eq_weight
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel.differencePhysicalWeight_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel.differencePhysicalWeight_le_kernel
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel.difference_kernel_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel.cubeSupported_mem_positiveHalfStates
