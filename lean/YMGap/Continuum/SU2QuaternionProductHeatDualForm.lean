/-
# The product-heat kinetic form and sharp Cauchy--Schwarz

The actual selected-link product heat defines a symmetric positive-semidefinite
bilinear form on supported slice polynomials.  Packaging that finite algebraic
form as existing `GNSData` gives sharp Cauchy--Schwarz for arbitrary signed
inputs while retaining every factor inside those inputs.

This is valid for any finite cutoff and any list of valid link indices; no
`Nodup`, strict heat positivity, eigenvector statement, response floor, or
continuum conclusion is asserted.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPositive
import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
import YMGap.Continuum.GNSQuotient

namespace YMGap.Continuum.SU2QuaternionProductHeatDualForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- The bare selected-link kinetic pairing on one supported slice. -/
def kineticPair (blocks : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (f g : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul f (productMap blocks w K ids g))

theorem kineticPair_symm (blocks : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (f g : RatPoly)
    (hf : SupportedQuaternionBlocks blocks f)
    (hg : SupportedQuaternionBlocks blocks g) :
    kineticPair blocks w K ids f g ≈ kineticPair blocks w K ids g f := by
  have hs := kernel_pairing_swap (productHeat_supported blocks w K ids hids) hg hf
    (productHeat_swap blocks w K ids hids)
  exact Q'.eqv_trans _ _ _ (productMap_pairing blocks w K ids g f)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
      (Q'.eqv_trans _ _ _ hs
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
          (Q'.eqv_symm (productMap_pairing blocks w K ids f g)))))

theorem kineticPair_add_left (blocks : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (f g r : RatPoly) :
    kineticPair blocks w K ids (polyAdd f g) r ≈
      kineticPair blocks w K ids f r + kineticPair blocks w K ids g r := by
  unfold kineticPair
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

theorem kineticPair_smul_left (blocks : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (c : Q') (f g : RatPoly) :
    kineticPair blocks w K ids (polySmul c f) g ≈
      c * kineticPair blocks w K ids f g :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c f
      (productMap blocks w K ids g)))
    (quaternionHaar_polySmul blocks c _)

/-- Positivity of the actual product-map diagonal. -/
theorem kineticPair_nonnegative (blocks : Nat) (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (ids : List Nat) (hids : ∀ i, i ∈ ids → i < blocks)
    (f : RatPoly) (hf : SupportedQuaternionBlocks blocks f) :
    (0 : Q') ≤ kineticPair blocks w K ids f f :=
  productMap_nonnegative blocks w hw K ids hids f hf

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem zero_add (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul 0 polyOne) p) p :=
  ((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.refl p)).trans
    (RatPolyCoeffEqv.zero_add p)

private theorem neg_add (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul (-1) p) p) (polySmul 0 polyOne) :=
  (RatPolyCoeffEqv.add_comm _ _).trans
    ((RatPolyCoeffEqv.add_neg_smul p).trans
      (RatPolyCoeffEqv.zero_smul polyOne).symm)

/-- `GNSData` for the product-heat kinetic form on supported polynomials. -/
def kineticGNSData (blocks : Nat) (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (ids : List Nat) (hids : ∀ i, i ∈ ids → i < blocks) : GNSData where
  V := {p : RatPoly // SupportedQuaternionBlocks blocks p}
  veq := fun p q => RatPolyCoeffEqv p.val q.val
  veq_refl := fun _ => RatPolyCoeffEqv.refl _
  veq_symm := fun h => h.symm
  veq_trans := fun h h' => h.trans h'
  zero := ⟨polySmul 0 polyOne, support_smul (supported_one blocks) 0⟩
  add := fun p q => ⟨polyAdd p.val q.val, supported_add p.property q.property⟩
  neg := fun p => ⟨polySmul (-1) p.val, support_smul p.property (-1)⟩
  smul := fun c p => ⟨polySmul c p.val, support_smul p.property c⟩
  add_congr := fun h h' => h.add h'
  neg_congr := fun h => h.smul (-1)
  smul_congr := fun c {_ _} h => h.smul c
  add_assoc := fun _ _ _ => RatPolyCoeffEqv.add_assoc _ _ _
  add_comm := fun _ _ => RatPolyCoeffEqv.add_comm _ _
  zero_add := fun p => zero_add p.val
  neg_add := fun p => neg_add p.val
  B := fun p q => kineticPair blocks w K ids p.val q.val
  B_congr_left := fun q h => haar_of_coeff (h.mul_right (productMap blocks w K ids q.val))
  B_add_left := fun p q r => kineticPair_add_left blocks w K ids p.val q.val r.val
  B_smul_left := fun c p q => kineticPair_smul_left blocks w K ids c p.val q.val
  B_symm := fun p q => kineticPair_symm blocks w K ids hids p.val q.val p.property q.property
  self_nonneg := fun p => kineticPair_nonnegative blocks w hw K ids hids p.val p.property

/-- Sharp Cauchy--Schwarz for arbitrary signed supported inputs under the same
selected-link product heat. -/
theorem kineticPair_cauchySchwarz (blocks : Nat) (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (ids : List Nat) (hids : ∀ i, i ∈ ids → i < blocks)
    (f g : RatPoly) (hf : SupportedQuaternionBlocks blocks f)
    (hg : SupportedQuaternionBlocks blocks g) :
    kineticPair blocks w K ids f g * kineticPair blocks w K ids f g ≤
      kineticPair blocks w K ids f f * kineticPair blocks w K ids g g :=
  (kineticGNSData blocks w hw K ids hids).cauchy_schwarz ⟨f, hf⟩ ⟨g, hg⟩

end YMGap.Continuum.SU2QuaternionProductHeatDualForm

#print axioms YMGap.Continuum.SU2QuaternionProductHeatDualForm.kineticPair
#print axioms YMGap.Continuum.SU2QuaternionProductHeatDualForm.kineticPair_symm
#print axioms YMGap.Continuum.SU2QuaternionProductHeatDualForm.kineticPair_add_left
#print axioms YMGap.Continuum.SU2QuaternionProductHeatDualForm.kineticPair_smul_left
#print axioms YMGap.Continuum.SU2QuaternionProductHeatDualForm.kineticPair_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatDualForm.kineticGNSData
#print axioms YMGap.Continuum.SU2QuaternionProductHeatDualForm.kineticPair_cauchySchwarz
