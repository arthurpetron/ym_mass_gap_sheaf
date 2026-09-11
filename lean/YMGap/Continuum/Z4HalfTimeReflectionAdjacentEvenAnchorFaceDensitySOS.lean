/-
# Finite global face-density SOS from oriented plaquette holonomies

The local anchor-face SOS has already been pulled back to a rational
unit-quaternion gauge field at one physical plaquette.  This leaf takes a
finite list of plaquettes, maps every face to that pullback, and combines the
result with the constructive finite-SOS product.

The corresponding physical density is kept as an explicit right-recursive
product of truncated class values.  In particular, faces sharing a link are
all evaluated on the same gauge field; no independent-face approximation or
premature Haar factorization occurs.

Everything here is symbolic in the supplied face list.  The adjacent-even
fixed-face specialization names the existing list and maps its identifiers to
physical plaquettes without evaluating or materializing the slab.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceDensitySOS

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedRationalSOSProduct
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceWeightDecomposition

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. A symbolic finite face density -/

/-- One gauge-field SOS factor for every plaquette in the supplied finite
list. -/
def anchorFaceDensityFactorList
    (cutoff : Nat) (plaquettes : List Z4Plaq) :
    List (FiniteWeightedRationalSOS RationalUnitQuaternionGaugeField) :=
  plaquettes.map (latticeAnchorFaceHolonomySOS cutoff)

/-- The finite weighted SOS presenting the product of all supplied face
weights. -/
def anchorFaceDensitySOS
    (cutoff : Nat) (plaquettes : List Z4Plaq) :
    FiniteWeightedRationalSOS RationalUnitQuaternionGaugeField :=
  multiplyList (anchorFaceDensityFactorList cutoff plaquettes)

/-- The corresponding right-recursive product of physical truncated class
values.  Every factor reads its holonomy from the same gauge field. -/
def anchorFaceClassValueProduct (cutoff : Nat) :
    List Z4Plaq → RationalUnitQuaternionGaugeField → Q'
  | [], _ => 1
  | plaquette :: tail, field =>
      anchorTruncatedFaceClassValue cutoff
          (latticePlaquetteHolonomy field plaquette).val.r *
        anchorFaceClassValueProduct cutoff tail field

/-! ## 2. Exact evaluation and nonnegativity -/

/-- The abstract `valueList` of the mapped SOS factors is exactly the
recursive physical face product. -/
theorem valueList_anchorFaceDensityFactorList
    (cutoff : Nat) (field : RationalUnitQuaternionGaugeField) :
    ∀ plaquettes : List Z4Plaq,
      valueList (anchorFaceDensityFactorList cutoff plaquettes) field ≈
        anchorFaceClassValueProduct cutoff plaquettes field
  | [] => Q'.eqv_refl 1
  | plaquette :: tail =>
      q_mul_congr
        (value_latticeAnchorFaceHolonomySOS cutoff plaquette field)
        (valueList_anchorFaceDensityFactorList cutoff field tail)

/-- **Exact finite face-density identity.**  The multiplied SOS evaluates to
the recursive product of the truncated class value at every oriented
plaquette holonomy. -/
theorem value_anchorFaceDensitySOS
    (cutoff : Nat) (plaquettes : List Z4Plaq)
    (field : RationalUnitQuaternionGaugeField) :
    value (anchorFaceDensitySOS cutoff plaquettes) field ≈
      anchorFaceClassValueProduct cutoff plaquettes field := by
  exact Q'.eqv_trans _ _ _
    (value_multiplyList
      (anchorFaceDensityFactorList cutoff plaquettes) field)
    (valueList_anchorFaceDensityFactorList cutoff field plaquettes)

/-- Every weight of the symbolic finite density presentation remains
constructively nonnegative. -/
theorem anchorFaceDensitySOS_weight_nonnegative
    (cutoff : Nat) (plaquettes : List Z4Plaq) (term : Nat) :
    (0 : Q') ≤ (anchorFaceDensitySOS cutoff plaquettes).weight term :=
  (anchorFaceDensitySOS cutoff plaquettes).weight_nonnegative term

/-- The multiplied finite SOS is pointwise nonnegative for every rational
unit-quaternion gauge field. -/
theorem anchorFaceDensitySOS_nonnegative
    (cutoff : Nat) (plaquettes : List Z4Plaq)
    (field : RationalUnitQuaternionGaugeField) :
    (0 : Q') ≤ value (anchorFaceDensitySOS cutoff plaquettes) field :=
  value_nonnegative (anchorFaceDensitySOS cutoff plaquettes) field

/-- The recursively written physical density is likewise pointwise
nonnegative. -/
theorem anchorFaceClassValueProduct_nonnegative
    (cutoff : Nat) (field : RationalUnitQuaternionGaugeField) :
    ∀ plaquettes : List Z4Plaq,
      (0 : Q') ≤ anchorFaceClassValueProduct cutoff plaquettes field
  | [] => Q'.zero_le_one
  | plaquette :: tail => by
      exact Q'.mul_nonneg _ _
        (anchorTruncatedFaceClassValue_holonomy_nonnegative cutoff
          (plaquetteOrientedEdgeInput field plaquette))
        (anchorFaceClassValueProduct_nonnegative cutoff field tail)

/-! ## 3. Existing adjacent-even fixed-face specialization -/

/-- The actual adjacent-even fixed faces as physical plaquettes, preserving
the existing duplicate-free identifier order.  This is a symbolic `List.map`;
the slab list is not evaluated here. -/
def adjacentEvenFixedFacePlaquettes (radius : Nat) : List Z4Plaq :=
  (adjacentEvenFixedFaceIds radius).map
    (slabPlaquetteAt (adjacentEvenExtent radius))

/-- The anchor density SOS on the complete current adjacent-even fixed-face
list. -/
def adjacentEvenFixedFaceDensitySOS (cutoff radius : Nat) :
    FiniteWeightedRationalSOS RationalUnitQuaternionGaugeField :=
  anchorFaceDensitySOS cutoff (adjacentEvenFixedFacePlaquettes radius)

/-- The corresponding physical product over the actual fixed-face list. -/
def adjacentEvenFixedFaceClassValueProduct
    (cutoff radius : Nat) (field : RationalUnitQuaternionGaugeField) : Q' :=
  anchorFaceClassValueProduct cutoff
    (adjacentEvenFixedFacePlaquettes radius) field

/-- Exact evaluation on the current adjacent-even fixed-face geometry. -/
theorem value_adjacentEvenFixedFaceDensitySOS
    (cutoff radius : Nat) (field : RationalUnitQuaternionGaugeField) :
    value (adjacentEvenFixedFaceDensitySOS cutoff radius) field ≈
      adjacentEvenFixedFaceClassValueProduct cutoff radius field :=
  value_anchorFaceDensitySOS cutoff
    (adjacentEvenFixedFacePlaquettes radius) field

/-- Pointwise nonnegativity of the fixed-face density SOS. -/
theorem adjacentEvenFixedFaceDensitySOS_nonnegative
    (cutoff radius : Nat) (field : RationalUnitQuaternionGaugeField) :
    (0 : Q') ≤ value
      (adjacentEvenFixedFaceDensitySOS cutoff radius) field :=
  anchorFaceDensitySOS_nonnegative cutoff
    (adjacentEvenFixedFacePlaquettes radius) field

/-- Pointwise nonnegativity of the explicitly recursive fixed-face physical
product. -/
theorem adjacentEvenFixedFaceClassValueProduct_nonnegative
    (cutoff radius : Nat) (field : RationalUnitQuaternionGaugeField) :
    (0 : Q') ≤
      adjacentEvenFixedFaceClassValueProduct cutoff radius field :=
  anchorFaceClassValueProduct_nonnegative cutoff field
    (adjacentEvenFixedFacePlaquettes radius)

#print axioms valueList_anchorFaceDensityFactorList
#print axioms value_anchorFaceDensitySOS
#print axioms anchorFaceDensitySOS_weight_nonnegative
#print axioms anchorFaceDensitySOS_nonnegative
#print axioms anchorFaceClassValueProduct_nonnegative
#print axioms value_adjacentEvenFixedFaceDensitySOS
#print axioms adjacentEvenFixedFaceDensitySOS_nonnegative
#print axioms adjacentEvenFixedFaceClassValueProduct_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceDensitySOS
