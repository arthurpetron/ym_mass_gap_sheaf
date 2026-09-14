/-
# Original relative heat kernels at arbitrary physical block pairs

Two explicit swaps expose distinct blocks as zero and one. They act on
the entire polynomial carrier. Every packet spin is retained; support and
independence from other blocks are structural, not cutoff computations.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
import YMGap.Continuum.SU2QuaternionFourBlockSelection

namespace YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFourBlockExposure
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

def scalarAt (a b : Nat) : RatPoly :=
  (PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))).scalar

def heatAt (a b : Nat) (w : Q') (K : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
    (characterPolynomial (scalarAt a b) spin)) (List.range (K+1))

theorem heatAt_zero_one (w : Q') (K : Nat) : heatAt 0 1 w K = relativeHeat w K := rfl

def pairSteps {blocks : Nat} (hb : 1 < blocks) (a b : Fin blocks) : List (QuaternionBlockInvolution blocks) :=
  extend (extend [] ⟨0,by omega⟩ a) ⟨1,hb⟩ b

theorem pair_zero {blocks : Nat} (hb : 1 < blocks) (a b : Fin blocks) (hab : a.val ≠ b.val) :
    quaternionBlockSwapChainSource (pairSteps hb a b) 0 = a.val :=
  extend_preserves (extend [] ⟨0,by omega⟩ a) ⟨1,hb⟩ b
    (extend_source [] ⟨0,by omega⟩ a) (by change (0 : Nat) ≠ 1; decide) hab

theorem pair_one {blocks : Nat} (hb : 1 < blocks) (a b : Fin blocks) :
    quaternionBlockSwapChainSource (pairSteps hb a b) 1 = b.val :=
  extend_source (extend [] ⟨0,by omega⟩ a) ⟨1,hb⟩ b

theorem scalar_exposed {blocks : Nat} (hb : 1 < blocks) (a b : Fin blocks) (hab : a.val ≠ b.val) :
    QuaternionPrefixPolynomialEqv blocks (applyQuaternionBlockSwapChain (pairSteps hb a b) (scalarAt a.val b.val))
      relativeScalar := by
  have hp := (applyQuaternionBlockSwapChain_coordinateVariable_prefix (pairSteps hb a b)
      (by omega) (pair_zero hb a b hab)).mul
    (applyQuaternionBlockSwapChain_coordinateVariable_prefix (pairSteps hb a b) hb (pair_one hb a b)).conj
  rw [← applyQuaternionBlockSwapChainQuaternion_conj, ← applyQuaternionBlockSwapChainQuaternion_mul] at hp
  have hs := hp.scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at hs
  exact hs

private theorem chain_add {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks)) (p q : RatPoly) :
    applyQuaternionBlockSwapChain steps (polyAdd p q) =
      polyAdd (applyQuaternionBlockSwapChain steps p) (applyQuaternionBlockSwapChain steps q) := by
  induction steps generalizing p q with
  | nil => rfl
  | cons s ss ih => simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_add, ih]

private theorem chain_smul {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks)) (c : Q') (p : RatPoly) :
    applyQuaternionBlockSwapChain steps (polySmul c p) = polySmul c (applyQuaternionBlockSwapChain steps p) := by
  induction steps generalizing p with
  | nil => rfl
  | cons s ss ih => simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_smul, ih]

private theorem chain_zero {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks)) :
    applyQuaternionBlockSwapChain steps polyZero = polyZero := by
  induction steps with
  | nil => rfl
  | cons s ss ih => exact ih

theorem heat_exposed {blocks : Nat} (hb : 1 < blocks) (a b : Fin blocks) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) : PaddedPolynomialCoeffEqv blocks
      (applyQuaternionBlockSwapChain (pairSteps hb a b) (heatAt a.val b.val w K)) (relativeHeat w K) := by
  have hc (spin : Nat) : QuaternionPrefixPolynomialEqv blocks
      (applyQuaternionBlockSwapChain (pairSteps hb a b) (characterPolynomial (scalarAt a.val b.val) spin))
      (relativeCharacter spin) :=
    (applyQuaternionBlockSwapChain_character_prefix _ _ _).trans ((scalar_exposed hb a b hab).character spin)
  unfold heatAt relativeHeat
  induction List.range (K+1) with
  | nil => rw [finitePolySum, chain_zero]; exact .refl _ _
  | cons s ss ih =>
    simp only [finitePolySum, chain_add, chain_smul]
    exact ((PaddedPolynomialCoeffEqv.of_prefix (hc s)).smul _).add ih

private theorem chain_components {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks)) (q : PolyQuaternion) :
    applyQuaternionBlockSwapChainQuaternion steps q =
      ⟨applyQuaternionBlockSwapChain steps q.scalar, applyQuaternionBlockSwapChain steps q.iPart,
        applyQuaternionBlockSwapChain steps q.jPart, applyQuaternionBlockSwapChain steps q.kPart⟩ := by
  induction steps generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (reindexPolyQuaternion s q)

theorem coordinate_exposed {blocks target source : Nat} (steps : List (QuaternionBlockInvolution blocks))
    (ht : target < blocks) (hmap : quaternionBlockSwapChainSource steps target = source) (i : Fin 4) :
    QuaternionPrefixPolynomialEqv blocks
      (applyQuaternionBlockSwapChain steps (polyVar (4*source+i.val))) (polyVar (4*target+i.val)) := by
  have h := applyQuaternionBlockSwapChain_coordinateVariable_prefix steps ht hmap
  rw [chain_components] at h
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp only [Fin.ext_iff]; omega
  rcases hi with rfl | rfl | rfl | rfl
  · exact h.scalar
  · exact h.iPart
  · exact h.jPart
  · exact h.kPart

theorem coordinate_supported {blocks block : Nat} (hb : block < blocks) (i : Fin 4) :
    SupportedQuaternionBlocks blocks (polyVar (4*block+i.val)) := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  simp only [varMono, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

private theorem support_add {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (polyAdd p q) := fun t ht => (List.mem_append.mp ht).elim (hp t) (hq t)

private theorem support_smul {blocks : Nat} (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem scalar_supported {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks) :
    SupportedQuaternionBlocks blocks (scalarAt a b) := by
  have ha0 := coordinate_supported ha (0 : Fin 4)
  have ha1 := coordinate_supported ha (1 : Fin 4)
  have ha2 := coordinate_supported ha (2 : Fin 4)
  have ha3 := coordinate_supported ha (3 : Fin 4)
  have hb0 := coordinate_supported hb (0 : Fin 4)
  have hb1 := coordinate_supported hb (1 : Fin 4)
  have hb2 := coordinate_supported hb (2 : Fin 4)
  have hb3 := coordinate_supported hb (3 : Fin 4)
  exact support_add (supported_polyMul ha0 hb0)
    (support_neg (support_add (supported_polyMul ha1 (support_neg hb1))
      (support_add (supported_polyMul ha2 (support_neg hb2)) (supported_polyMul ha3 (support_neg hb3)))))

theorem character_supported {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    ∀ spin, SupportedQuaternionBlocks blocks (characterPolynomial p spin)
  | 0 => QuaternionHaarSquareCertificate.supported_one blocks
  | 1 => support_smul 2 hp
  | s+2 => support_add (supported_polyMul (support_smul 2 hp) (character_supported hp (s+1)))
      (support_smul (-1) (character_supported hp s))

theorem heat_supported {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks) (w : Q') (K : Nat) :
    SupportedQuaternionBlocks blocks (heatAt a b w K) := by
  unfold heatAt
  induction List.range (K+1) with
  | nil => intro t ht; exact False.elim (List.not_mem_nil ht)
  | cons s ss ih => exact support_add (support_smul _ (character_supported (scalar_supported ha hb) s)) ih

theorem scalar_independent (slot a b : Nat) (ha : slot ≠ a) (hb : slot ≠ b) :
    HasQuaternionBlockDegree slot 0 (scalarAt a b) := by
  have h1 := hasPolyQuaternionBlockDegree_coordinateVariable a slot
  have h2 := hasPolyQuaternionBlockDegree_coordinateVariable b slot
  rw [if_neg ha] at h1
  rw [if_neg hb] at h2
  exact (h1.mul h2.conj).scalar

theorem character_independent {slot : Nat} {p : RatPoly} (hp : HasQuaternionBlockDegree slot 0 p) :
    ∀ spin, HasQuaternionBlockDegree slot 0 (characterPolynomial p spin)
  | 0 => hasQuaternionBlockDegree_one slot
  | 1 => hp.smul 2
  | s+2 => ((hp.smul 2).mul (character_independent hp (s+1))).add ((character_independent hp s).smul (-1))

theorem heat_independent (slot a b : Nat) (ha : slot ≠ a) (hb : slot ≠ b) (w : Q') (K : Nat) :
    HasQuaternionBlockDegree slot 0 (heatAt a b w K) := by
  unfold heatAt
  induction List.range (K+1) with
  | nil => exact hasQuaternionBlockDegree_zero slot 0
  | cons s ss ih => exact ((character_independent (scalar_independent slot a b ha hb) s).smul _).add ih

end YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.scalarAt
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.heatAt
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.heatAt_zero_one
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.pairSteps
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.pair_zero
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.pair_one
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.scalar_exposed
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.heat_exposed
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.coordinate_exposed
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.coordinate_supported
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.scalar_supported
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.character_supported
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.heat_supported
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.scalar_independent
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.character_independent
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry.heat_independent
