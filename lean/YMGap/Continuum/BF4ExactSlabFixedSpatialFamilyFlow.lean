/-
# Finite-family signed flow on the actual slab, including fringe coordinates

Instantiate the finite-family positive recurrence with every active heat
factor and a unit factor for each inactive retained coordinate. Unit factors
leave the ORIGINAL kinetic polynomial unchanged. No fictitious heatAt is
inserted at the fringe. All tests enter through their original slice jumps.

The shared RHS energy is energy(T^n1,f), with the exact factor 2 from the
jump identity. No cardinality prefactor is introduced. The signed cost is
still an explicit original-edge integral, not a proved uniform marginal
variance budget. Complete decomposition and cross-limit control remain open.
-/

import YMGap.Continuum.QuaternionHaarFiniteFamilyDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity energy energy_identity)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound (headFloor_le_oneThirtySecond)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (heatAt)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (heatAt_floorCertificate)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarFiniteFamilyDual

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks kineticWeight

/-- All retained coordinates without an active kinetic heat factor. -/
def fringeBlocks (width : Nat) : List Nat :=
  (List.range (N width)).filter (fun i => decide (i ∉ activeBlocks width))

theorem fringeBlocks_mem_iff (width i : Nat) :
    i ∈ fringeBlocks width ↔ i < N width ∧ i ∉ activeBlocks width := by
  constructor
  · intro hi
    exact ⟨List.mem_range.mp (List.mem_filter.mp hi).1,
      of_decide_eq_true (List.mem_filter.mp hi).2⟩
  · intro hi
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hi.1, decide_eq_true hi.2⟩

/-- Every retained coordinate belongs to exactly one of the two lists.
This is coordinate coverage, not a decomposition of centered observables. -/
theorem retained_coordinate_partition (width i : Nat) (hi : i < N width) :
    (i ∈ activeBlocks width ∨ i ∈ fringeBlocks width) ∧
      ¬ (i ∈ activeBlocks width ∧ i ∈ fringeBlocks width) := by
  constructor
  · by_cases ha : i ∈ activeBlocks width
    · exact Or.inl ha
    · exact Or.inr ((fringeBlocks_mem_iff width i).mpr ⟨hi,ha⟩)
  · intro h
    exact ((fringeBlocks_mem_iff width i).mp h.2).2 h.1

theorem fringeBlocks_lt (width i : Nat) (hi : i ∈ fringeBlocks width) : i < N width :=
  List.mem_range.mp (List.mem_filter.mp hi).1

/-- Heat factors on active links; unit factors, not fictitious heat kernels,
on every remaining retained coordinate. -/
def family (w : Q') (K width : Nat) (tests : Nat → RatPoly) : List (RatPoly × RatPoly) :=
  (activeBlocks width).map (fun i => (heatAt i (N width+i) w K, jump (N width) (tests i))) ++
  (fringeBlocks width).map (fun i => (polyOne, jump (N width) (tests i)))

private theorem product_append (ps qs : List (RatPoly × RatPoly)) :
    RatPolyCoeffEqv (product (ps++qs)) (polyMul (product ps) (product qs)) := by
  induction ps with
  | nil => exact (RatPolyCoeffEqv.one_mul _).symm
  | cons p ps ih =>
      exact (ih.mul_left p.1).trans (RatPolyCoeffEqv.mul_assoc _ _ _).symm

private theorem unit_product (n : Nat) (tests : Nat → RatPoly) (ids : List Nat) :
    RatPolyCoeffEqv (product (ids.map (fun i => (polyOne,jump n (tests i))))) polyOne := by
  induction ids with
  | nil => exact .refl _
  | cons i ids ih => exact (ih.mul_left polyOne).trans (RatPolyCoeffEqv.one_mul _)

private theorem heat_product (n : Nat) (w : Q') (K : Nat) (tests : Nat → RatPoly) (ids : List Nat) :
    product (ids.map (fun i => (heatAt i (n+i) w K,jump n (tests i)))) = productHeat n w K ids := by
  induction ids with
  | nil => rfl
  | cons i ids ih => change polyMul _ (product _) = polyMul _ (productHeat n w K ids); rw [ih]

/-- Adding the complete fringe family changes no original kinetic factor. -/
theorem family_product_pin (w : Q') (K width : Nat) (tests : Nat → RatPoly) :
    RatPolyCoeffEqv (product (family w K width tests)) (kineticWeight w K width) := by
  unfold family
  refine (product_append _ _).trans ?_
  rw [heat_product, kineticWeight_eq_indexedProduct]
  exact ((unit_product (N width) tests (fringeBlocks width)).mul_left _).trans
    (RatPolyCoeffEqv.mul_one _)

private theorem cap_neg (c : Q') : RatPolyCoeffEqv (polyNeg (cap c)) (cap (-c)) := by
  intro weight
  change (-(c*1))*weight []+0 ≈ ((-c)*1)*weight []+0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c 1))) (Q'.eqv_refl _)

private def unitFloorCertificate {n : Nat} {h : Q'} (hh : h ≤ (1 : Q')) :
    Certificate n (polyAdd polyOne (polyNeg (cap h))) :=
  .ofCoeff (((RatPolyCoeffEqv.one_smul polyOne).symm.add (cap_neg h)).trans (cap_add 1 (-h)))
    (Certificate.constant n (1 + -h) (Q'.sub_nonneg_of_le hh))

-- Select certificate DATA by finite decidable search, never by eliminating
-- the Prop-level existential in List.mem_map into Type.
private def mappedCertificates {n : Nat} {h : Q'} (f : Nat → RatPoly × RatPoly) :
    (ids : List Nat) →
    (∀ i, i ∈ ids → Certificate n (polyAdd (f i).1 (polyNeg (cap h)))) →
    ∀ p, p ∈ ids.map f → Certificate n (polyAdd p.1 (polyNeg (cap h)))
  | [], _, _, hp => False.elim (List.not_mem_nil hp)
  | i::ids, C, p, hp =>
      if he : p = f i then he ▸ C i List.mem_cons_self
      else mappedCertificates f ids (fun j hj => C j (List.mem_cons_of_mem i hj)) p
        ((List.mem_cons.mp hp).resolve_left he)

/-- Both active and fringe factor floors are supplied by existing certificates. -/
def familyFloorCertificates {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (tests : Nat → RatPoly) :
    ∀ p, p ∈ family w K width tests →
      Certificate (N width+N width) (polyAdd p.1 (polyNeg (cap (headFloor w)))) := by
  intro p hp
  let active := (activeBlocks width).map
    (fun i => (heatAt i (N width+i) w K, jump (N width) (tests i)))
  if ha : p ∈ active then
    exact mappedCertificates _ (activeBlocks width) (fun i hi => by
      have hi' := activeBlocks_lt width i hi
      exact heatAt_floorCertificate (show i<N width+N width by omega)
        (show N width+i<N width+N width by omega) hw0 hw1 K hK) p ha
  else
    exact mappedCertificates _ (fringeBlocks width) (fun _ _ =>
      unitFloorCertificate (Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide)))
      p ((List.mem_append.mp hp).resolve_left ha)

theorem family_tests_supported (w : Q') (K width : Nat) (tests : Nat → RatPoly)
    (ht : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (tests i)) :
    ∀ p, p ∈ family w K width tests → SupportedQuaternionBlocks (N width+N width) p.2 := by
  intro p hp
  rcases List.mem_append.mp hp with ha | hf
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact jump_supported (ht i (activeBlocks_lt width i hi))
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hf
    exact jump_supported (ht i (fringeBlocks_lt width i hi))

/-- Both full endpoint weights, before inserting the kinetic family. -/
def endpointWeight (w : Q') (K width n : Nat) : RatPoly :=
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  polyMul a (liftBoundary (N width) a)

/-- Original-edge flow pairing; its tests have not been replaced by normalized inverses. -/
def flowPair (w : Q') (K width n : Nat) (tests : Nat → RatPoly) (f : RatPoly) : Q' :=
  quaternionHaar (N width+N width) (polyMul (endpointWeight w K width n)
    (polyMul (flow (family w K width tests)) (jump (N width) f)))

/-- Explicit signed family cost, including active--fringe and fringe--fringe terms. -/
def signedCost (w : Q') (K width n : Nat) (tests : Nat → RatPoly) : Q' :=
  quaternionHaar (N width+N width) (polyMul (endpointWeight w K width n)
    (cost (headFloor w) (family w K width tests)))

/-- ONE original temporal energy budget for all retained coordinate tests.
No cardinality prefactor. The RHS signed cost still needs a controlled
marginal-norm comparison; this theorem does not supply a global gap. -/
theorem original_family_flow_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n : Nat) (tests : Nat → RatPoly)
    (ht : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (tests i))
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    headFloor w*(flowPair w K width n tests f * flowPair w K width n tests f) ≤
      ((2 : Q')*energy w K width (terminalMessage w K width n) f) * signedCost w K width n tests := by
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  have ha := supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n)
  let A := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (terminalMessage_certificate hw0 hw1 K width hK n)
  have h := finite_family_dual (headFloor_positive hw0 hw1) (family w K width tests)
    (familyFloorCertificates hw0 hw1 K width hK tests) (family_tests_supported w K width tests ht)
    ((certificate_extend (N width) ha A).mul (lift_certificate (N width) A)) (jump_supported hf)
  have hp : RatPolyCoeffEqv
      (polyMul (endpointWeight w K width n)
        (polyMul (product (family w K width tests)) (polyMul (jump (N width) f) (jump (N width) f))))
      (polyMul (edgeDensity w K width (terminalMessage w K width n))
        (polyMul (jump (N width) f) (jump (N width) f))) :=
    (((family_product_pin w K width tests).mul_right _).mul_left _).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.mul (.var 2) (.var 0)) (.var 1)) (.var 3)) (by decide)
        (fun
          | 0 => a | 1 => liftBoundary (N width) a | 2 => kineticWeight w K width
          | _ => polyMul (jump (N width) f) (jump (N width) f)))
  have hj := Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_symm (energy_identity w K width (terminalMessage_supported w K width n) hf))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hj))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.fringeBlocks
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.fringeBlocks_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.retained_coordinate_partition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.fringeBlocks_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.family
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.family_product_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.familyFloorCertificates
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.family_tests_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.endpointWeight
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.flowPair
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.signedCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow.original_family_flow_energy
