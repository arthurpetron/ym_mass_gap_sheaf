/-
# Three-layer conditional contraction on the ORIGINAL all-volume carrier

The literal twelve swept side characters and lower plaquette transmit an
arbitrary retained boundary with coefficient w^36. The retained polynomial
uses the upper four tube links and ALL spectator links. Its support guard
excludes only the twelve integrated links; it is not asserted that the full
interacting background satisfies that guard. Other face/spin selections and
the signed response remainder are still open.
-/

import YMGap.Continuum.BF4ExactSlabTubeCarrierWords

namespace YMGap.Continuum.BF4ExactSlabTubeCarrierContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding
open YMGap.Continuum.BF4ExactSlabTubeCarrierWords
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BondMovingStep (coeffW)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" margin:max => List.length (boundaryCompleteSlabLinks (responseExtent margin))
local notation "P" => plaquette 0 1 2 3

def compactFactors : List RatPoly := compactSlice ⟨0,by decide⟩ :: sideIds.map fun i => compactSide i.1 i.2

def literalFactors (margin : Nat) : List RatPoly :=
  literalSlice margin ⟨0,by decide⟩ :: sideIds.map fun i => literalSide margin i.1 i.2

def bareTransmission : Q' := Q'.mkPos 1 4096 (by decide)

/-- A small factorized certificate: no product of all twelve sides is expanded.
The rational pilot gives 1/16, 1/256, 1/4096; Lean checks the joint contraction. -/
theorem contraction_coefficients :
    RatPolyCoeffEqv (factorProduct (partialFactors 12 compactFactors)) (polySmul bareTransmission P) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem haar_coeff {p q : RatPoly} (h : RatPolyCoeffEqv p q) (blocks : Nat) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  have pin : ∀ r : RatPoly, quaternionHaar blocks r = ratWeightedSum (quaternionHaarMono blocks) r := by
    intro r
    induction r with
    | nil => rfl
    | cons t ts ih => simp only [quaternionHaar, ratWeightedSum, ih]
  rw [pin,pin]
  exact h _

private theorem append_single_coeff (fs : List RatPoly) (p : RatPoly) :
    RatPolyCoeffEqv (factorProduct (fs ++ [p])) (polyMul (factorProduct fs) p) := by
  induction fs with
  | nil => exact RatPolyCoeffEqv.mul_comm p polyOne
  | cons f fs ih =>
    exact (RatPolyCoeffEqv.mul_left f ih).trans (RatPolyCoeffEqv.mul_assoc _ _ _).symm

theorem compact_boundary_haar (blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks+12) (factorProduct (compactFactors ++ [liftBoundary 12 boundary])) ≈
      bareTransmission * quaternionHaar blocks (polyMul P boundary) := by
  have hc := (append_single_coeff (partialFactors 12 compactFactors) boundary).trans
    ((contraction_coefficients.mul_right boundary).trans (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
  exact Q'.eqv_trans _ _ _ (partialFactors_boundary_haar 12 blocks compactFactors boundary)
    (Q'.eqv_trans _ _ _ (haar_coeff hc blocks) (quaternionHaar_polySmul _ _ _))

/-- Product of the twelve ORIGINAL fundamental heat coefficients 2*w^3. -/
def heatCoefficient (w : Q') : Q' := qpow (coeffW w 1) 12

theorem heatCoefficient_pin (w : Q') : heatCoefficient w ≈ 4096 * qpow w 36 :=
  poly_identity_of_normal_eq
    (.pow (.mul (.const 2) (.pow (.var 0) 3)) 12)
    (.mul (.const 4096) (.pow (.var 0) 36)) (by decide) (fun _ => w)

theorem weightedCoefficient_pin (w : Q') : heatCoefficient w * bareTransmission ≈ qpow w 36 := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (heatCoefficient_pin w)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (by decide : bareTransmission * 4096 ≈ (1 : Q'))) (Q'.one_mul_eqv _)

theorem compact_weighted_boundary_haar (w : Q') (blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks+12) (polySmul (heatCoefficient w)
      (factorProduct (compactFactors ++ [liftBoundary 12 boundary]))) ≈
      qpow w 36 * quaternionHaar blocks (polyMul P boundary) := by
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (compact_boundary_haar blocks boundary))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _ (weightedCoefficient_pin w))))

private theorem factors_supported (blocks : Nat) (fs : List RatPoly)
    (h : ∀ p, p ∈ fs → SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (factorProduct fs) := by
  induction fs with
  | nil => exact supported_one blocks
  | cons p ps ih =>
    exact supported_polyMul (h p List.mem_cons_self)
      (ih (fun q hq => h q (List.mem_cons_of_mem p hq)))

private theorem compact_factor_supported : ∀ p, p ∈ compactFactors → SupportedQuaternionBlocks 16 p := by
  have hc : compactFactors.all (fun p => p.all (fun t => decide (t.1.length ≤ 4*16))) = true := by decide +kernel
  intro p hp t ht
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hc p hp) t ht)

private theorem lift_supported (n blocks : Nat) {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks (blocks+n) (liftBoundary n p) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    intro t ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    have h := ih s hs
    change s.1.length + 1 + 1 + 1 + 1 ≤ 4 * (blocks + (n+1))
    omega

private theorem source_supported (margin : Nat) {boundary : RatPoly}
    (hb : SupportedQuaternionBlocks (N margin-12) boundary) :
    SupportedQuaternionBlocks (N margin) (factorProduct (compactFactors ++ [liftBoundary 12 boundary])) := by
  have hn := carrier_size margin
  apply factors_supported
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · intro t ht
    have hs := compact_factor_supported p hp t ht
    omega
  · simp only [List.mem_singleton] at hp
    subst p
    have h := lift_supported 12 (N margin-12) hb
    have he : N margin-12+12 = N margin := by omega
    rw [he] at h
    exact h

def literalBoundary (margin : Nat) (boundary : RatPoly) : RatPoly :=
  (carrierEmbedding margin).polynomial (liftBoundary 12 boundary)

theorem boundary_source_pin (margin : Nat) (boundary : RatPoly) :
    PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial (factorProduct (compactFactors ++ [liftBoundary 12 boundary])))
      (factorProduct (literalFactors margin ++ [literalBoundary margin boundary])) := by
  have go : ∀ ids : List (Fin 3 × Fin 4), PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial (factorProduct
        ((ids.map fun i => compactSide i.1 i.2) ++ [liftBoundary 12 boundary])))
      (factorProduct ((ids.map fun i => literalSide margin i.1 i.2) ++ [literalBoundary margin boundary])) := by
    intro ids
    induction ids with
    | nil =>
      simp only [List.map_nil, List.nil_append, factorProduct, (carrierEmbedding margin).polynomial_mul]
      exact (PaddedPolynomialCoeffEqv.refl _ _).mul (.of_prefix (carrierEmbedding margin).polynomial_one_prefix)
    | cons i ids ih =>
      simp only [List.map_cons, List.cons_append, factorProduct, (carrierEmbedding margin).polynomial_mul]
      exact (side_embedding_pin margin i.1 i.2).mul ih
  simp only [compactFactors, literalFactors, List.cons_append, factorProduct, (carrierEmbedding margin).polynomial_mul]
  exact (slice_embedding_pin margin _).mul (go sideIds)

private theorem target_supported (margin : Nat) (boundary : RatPoly) :
    SupportedQuaternionBlocks (N margin) (factorProduct (literalFactors margin ++ [literalBoundary margin boundary])) := by
  apply factors_supported
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_cons.mp hp with hp | hp
    · subst p
      exact original_character_support _ _ _
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
      exact swept_character_supported _ _ _ _
  · simp only [List.mem_singleton] at hp
    subst p
    exact (carrierEmbedding margin).polynomial_supported _

/-- Exactly the twelve literal selected heat channels on the original slab,
with arbitrary retained upper/spectator data. This is NOT a full-action bound. -/
theorem literal_weighted_boundary_haar (w : Q') (margin : Nat) (boundary : RatPoly)
    (hb : SupportedQuaternionBlocks (N margin-12) boundary) :
    quaternionHaar (N margin) (polySmul (heatCoefficient w)
      (factorProduct (literalFactors margin ++ [literalBoundary margin boundary]))) ≈
      qpow w 36 * quaternionHaar (N margin-12) (polyMul P boundary) := by
  have hp := (boundary_source_pin margin boundary).haar
    ((carrierEmbedding margin).polynomial_supported _) (target_supported margin boundary)
  have he := (carrierEmbedding margin).haar _ (source_supported margin hb)
  have hbare := Q'.eqv_trans _ _ _ (Q'.eqv_symm hp) he
  have hn : N margin-12+12 = N margin := by have h := carrier_size margin; omega
  have hc := compact_weighted_boundary_haar w (N margin-12) boundary
  rw [hn] at hc
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hbare)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polySmul _ _ _)) hc))

end YMGap.Continuum.BF4ExactSlabTubeCarrierContraction

#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.compactFactors
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.literalFactors
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.bareTransmission
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.contraction_coefficients
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.compact_boundary_haar
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.heatCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.heatCoefficient_pin
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.weightedCoefficient_pin
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.compact_weighted_boundary_haar
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.literalBoundary
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.boundary_source_pin
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierContraction.literal_weighted_boundary_haar
