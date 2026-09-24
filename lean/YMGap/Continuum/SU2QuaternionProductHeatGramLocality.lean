/-
# Block locality of the computed product-heat Gram channels

Every leaf of a one-link Gram channel uses only that link block.  Cartesian
products therefore use only the selected block list.  This is proved from the
literal polynomial tensor construction; no coefficient-equivalent replacement
or additional channel certificate is introduced.
-/

import YMGap.Continuum.SU2QuaternionProductHeatGramChannels
import YMGap.Continuum.SU2QuaternionHaarFamilyProjection

namespace YMGap.Continuum.SU2QuaternionProductHeatGramLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection

private def ComplexBlockIndependent (block : Nat) (p : ComplexRatPoly) : Prop :=
  QuaternionBlockIndependent block p.1 ∧ QuaternionBlockIndependent block p.2

private def TensorBlockIndependent (block : Nat) :
    (degree : Nat) → PolyTensor degree → Prop
  | 0, x => ComplexBlockIndependent block x
  | degree + 1, x => ∀ bit, TensorBlockIndependent block degree (x bit)

private theorem complex_zero_independent (block : Nat) :
    ComplexBlockIndependent block complexRatPolyZero :=
  ⟨quaternionBlockIndependent_polyZero block,
    quaternionBlockIndependent_polyZero block⟩

private theorem complex_one_independent (block : Nat) :
    ComplexBlockIndependent block complexRatPolyOne :=
  ⟨quaternionBlockIndependent_polyOne block,
    quaternionBlockIndependent_polyZero block⟩

private theorem complex_add_independent {block : Nat} {p q : ComplexRatPoly}
    (hp : ComplexBlockIndependent block p) (hq : ComplexBlockIndependent block q) :
    ComplexBlockIndependent block (complexRatPolyAdd p q) :=
  ⟨quaternionBlockIndependent_polyAdd hp.1 hq.1,
    quaternionBlockIndependent_polyAdd hp.2 hq.2⟩

private theorem complex_mul_independent {block : Nat} {p q : ComplexRatPoly}
    (hp : ComplexBlockIndependent block p) (hq : ComplexBlockIndependent block q) :
    ComplexBlockIndependent block (complexRatPolyMul p q) :=
  ⟨quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polyMul hp.1 hq.1)
      (quaternionBlockIndependent_polyNeg
        (quaternionBlockIndependent_polyMul hp.2 hq.2)),
    quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polyMul hp.1 hq.2)
      (quaternionBlockIndependent_polyMul hp.2 hq.1)⟩

private theorem coordinate_matrix_independent {slot block : Nat} (hne : slot ≠ block) :
    ∀ row column,
      ComplexBlockIndependent block
        (fundamentalMatrixCoefficient
          (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) row column) := by
  intro row column
  have h (component : Nat) (hc : component < 4) :
      QuaternionBlockIndependent block (polyVar (4 * slot + component)) :=
    quaternionBlockIndependent_polyVar_of_distinctBlock hne hc
  cases row <;> cases column
  · exact ⟨by simpa [asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using h 0 (by omega),
      by simpa [asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using h 1 (by omega)⟩
  · exact ⟨by simpa [asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using h 2 (by omega),
      by simpa [asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using h 3 (by omega)⟩
  · exact ⟨quaternionBlockIndependent_polyNeg
      (by simpa [asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using h 2 (by omega)),
      by simpa [asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using h 3 (by omega)⟩
  · exact ⟨by simpa [asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using h 0 (by omega),
      quaternionBlockIndependent_polyNeg
        (by simpa [asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using h 1 (by omega))⟩

private theorem tensor_add_independent (block : Nat) : ∀ {degree} {x y : PolyTensor degree},
    TensorBlockIndependent block degree x → TensorBlockIndependent block degree y →
      TensorBlockIndependent block degree (polyTensorAdd degree x y)
  | 0, _, _, hx, hy => complex_add_independent hx hy
  | _ + 1, _, _, hx, hy => fun bit => tensor_add_independent block (hx bit) (hy bit)

private theorem tensor_scale_independent (block : Nat) {a : ComplexRatPoly}
    (ha : ComplexBlockIndependent block a) : ∀ {degree} {x : PolyTensor degree},
      TensorBlockIndependent block degree x →
        TensorBlockIndependent block degree (polyTensorScale degree a x)
  | 0, _, hx => complex_mul_independent ha hx
  | _ + 1, _, hx => fun bit => tensor_scale_independent block ha (hx bit)

private theorem polyEmbed_independent (block : Nat) {f : Nat → ComplexRatPoly}
    (hf : ∀ j, ComplexBlockIndependent block (f j)) : ∀ degree,
    TensorBlockIndependent block degree (polyEmbed degree f)
  | 0 => hf 0
  | degree + 1 => by
      intro bit
      cases bit
      · exact polyEmbed_independent block hf degree
      · exact polyEmbed_independent block (fun j => hf (j + 1)) degree

private theorem basis_tensor_independent (block k degree : Nat) :
    TensorBlockIndependent block degree (polyEmbed degree (polynomialBasis k)) := by
  apply polyEmbed_independent block
  intro j
  by_cases h : j = k
  · simpa [polynomialBasis, h] using complex_one_independent block
  · simpa [polynomialBasis, h] using complex_zero_independent block

private theorem matrix_action_independent {slot block : Nat} (hne : slot ≠ block) :
    ∀ degree (x : PolyTensor degree), TensorBlockIndependent block degree x →
      TensorBlockIndependent block degree
        (polyMatrixAction degree
          (fundamentalMatrixCoefficient
            (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot))) x)
  | 0, _, hx => hx
  | degree + 1, x, hx => fun row =>
      tensor_add_independent block
        (tensor_scale_independent block (coordinate_matrix_independent hne row false)
          (matrix_action_independent hne degree (x false) (hx false)))
        (tensor_scale_independent block (coordinate_matrix_independent hne row true)
          (matrix_action_independent hne degree (x true) (hx true)))

private theorem polynomialColumn_independent {slot block degree k : Nat}
    (hne : slot ≠ block) :
    TensorBlockIndependent block degree
      (polynomialColumn
        (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree k) := by
  exact matrix_action_independent hne degree _ (basis_tensor_independent block k degree)

private theorem tensorLeaves_independent {block degree : Nat} {x : PolyTensor degree}
    (hx : TensorBlockIndependent block degree x) :
    ∀ p, p ∈ tensorLeaves degree x → QuaternionBlockIndependent block p := by
  induction degree with
  | zero =>
      intro p hp
      simp only [tensorLeaves, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hx.1
      · rcases hp with rfl | hp
        · exact hx.2
        · exact False.elim (List.not_mem_nil hp)
  | succ degree ih =>
      intro p hp
      simp only [tensorLeaves, List.mem_append] at hp
      exact hp.elim (ih (hx false) p) (ih (hx true) p)

/-- A one-link Gram leaf is independent of every distinct block. -/
theorem heatChannels_independent {slot block : Nat} (hne : slot ≠ block)
    (w : Q') (K : Nat) : ∀ c, c ∈ heatChannels slot w K →
      QuaternionBlockIndependent block c.2 := by
  intro c hc
  obtain ⟨degree, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨k, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  exact tensorLeaves_independent (polynomialColumn_independent hne) p hp

/-- Every computed Cartesian product channel is local to its selected list. -/
theorem productChannels_independent (n : Nat) (w : Q') (K : Nat) : ∀ ids block,
    block ∉ ids → ∀ c, c ∈ productChannels n w K ids →
      QuaternionBlockIndependent block c.2
  | [], block, _, c, hc => by
      simp only [productChannels, List.mem_singleton] at hc
      subst c
      exact quaternionBlockIndependent_polyOne block
  | slot :: ids, block, hnot, c, hc => by
      obtain ⟨a, ha, hac⟩ := List.mem_flatMap.mp hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hac
      have hslot : slot ≠ block := by
        intro heq
        subst block
        exact hnot List.mem_cons_self
      exact quaternionBlockIndependent_polyMul
        (heatChannels_independent hslot w K a ha)
        (productChannels_independent n w K ids block
          (fun h => hnot (List.mem_cons_of_mem slot h)) b hb)

/-- Projecting an absent block fixes the literal channel polynomial. -/
theorem project_productChannel_fixed (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (block : Nat) (hnot : block ∉ ids) (c : GramChannel)
    (hc : c ∈ productChannels n w K ids) :
    RatPolyCoeffEqv (project block c.2) c.2 :=
  project_fixed block c.2 (productChannels_independent n w K ids block hnot c hc)

/-- Sequential projection over absent blocks fixes the literal channel. -/
theorem familyProject_productChannel_fixed (n : Nat) (w : Q') (K : Nat)
    (ids absent : List Nat) (hnot : ∀ block, block ∈ absent → block ∉ ids)
    (c : GramChannel) (hc : c ∈ productChannels n w K ids) :
    RatPolyCoeffEqv (familyProject absent c.2) c.2 :=
  familyProject_fixed absent c.2
    (fun block hb => productChannels_independent n w K ids block (hnot block hb) c hc)

end YMGap.Continuum.SU2QuaternionProductHeatGramLocality

#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramLocality.heatChannels_independent
#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramLocality.productChannels_independent
#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramLocality.project_productChannel_fixed
#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramLocality.familyProject_productChannel_fixed
