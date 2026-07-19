/-
# Oriented plaquette holonomy pullback of the adjacent-even anchor-face SOS

The local anchor-face certificate is a function of one rational unit
quaternion.  This leaf supplies its first genuine lattice-geometric input map.
For the four positive-coordinate links returned by `edgesOf`, in the exact
order

```
  U0 = U(v,a),       U1 = U(v,b),
  U2 = U(v+e_b,a),   U3 = U(v+e_a,b),
```

the positively oriented plaquette boundary word is

```
  U0 * U3 * U2^{-1} * U1^{-1}.
```

All products and inverses use the constructive rational unit-quaternion group.
Consequently the holonomy is unit norm by construction, and the existing
finite weighted SOS can be pulled back without changing its finite carrier or
weights.

This remains an algebraic rational gauge-field layer.  It does not assert a
compact completion, Haar invariance, or the global reflected-slab integral.
The sixteen-coordinate environment below is only the explicit input boundary
for a later polynomial substitution; no duplicate `RatPoly` substitution is
introduced here.
-/

import YMGap.RepTheory.RationalQuaternionUnitNormGroup
import YMGap.Continuum.ClusterCount4DProgress
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceSOS

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedRationalSOSProduct
open YMGap.Continuum.SU2QuaternionOddFaceSOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceSOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceWeightDecomposition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Unit quaternions as anchor inputs -/

/-- Forget the group wrapper while retaining its exact unit-sphere witness in
the association convention expected by `AnchorQuaternionInput`. -/
def unitNormToAnchorQuaternionInput (q : UnitNorm) : AnchorQuaternionInput where
  x := q.val.r
  y1 := q.val.i
  y2 := q.val.j
  y3 := q.val.k
  onSphere := by
    have hnorm :
        (q.val.r * q.val.r + q.val.i * q.val.i) +
            (q.val.j * q.val.j + q.val.k * q.val.k) ≈ (1 : Q') :=
      q.unitNorm
    exact Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv
        (q.val.r * q.val.r + q.val.i * q.val.i)
        (q.val.j * q.val.j) (q.val.k * q.val.k))
      hnorm

@[simp] theorem unitNormToAnchorQuaternionInput_x (q : UnitNorm) :
    (unitNormToAnchorQuaternionInput q).x = q.val.r := rfl

@[simp] theorem unitNormToAnchorQuaternionInput_y1 (q : UnitNorm) :
    (unitNormToAnchorQuaternionInput q).y1 = q.val.i := rfl

@[simp] theorem unitNormToAnchorQuaternionInput_y2 (q : UnitNorm) :
    (unitNormToAnchorQuaternionInput q).y2 = q.val.j := rfl

@[simp] theorem unitNormToAnchorQuaternionInput_y3 (q : UnitNorm) :
    (unitNormToAnchorQuaternionInput q).y3 = q.val.k := rfl

/-! ## 2. The four oriented boundary edges and their holonomy -/

/-- Four positive-coordinate link values in the literal order used by
`ClusterCount4DProgress.edgesOf`.  Boundary orientation is encoded by the
inverse operations in `standardPlaquetteHolonomy`, not by changing this
storage order. -/
structure FourOrientedEdgeInput where
  u0 : UnitNorm
  u1 : UnitNorm
  u2 : UnitNorm
  u3 : UnitNorm

/-- The four edge values as a list, preserving the audited `edgesOf` order. -/
def FourOrientedEdgeInput.toList (input : FourOrientedEdgeInput) : List UnitNorm :=
  [input.u0, input.u1, input.u2, input.u3]

@[simp] theorem FourOrientedEdgeInput.toList_length
    (input : FourOrientedEdgeInput) : input.toList.length = 4 := rfl

/-- The standard positively oriented plaquette word.  The left association is
fixed explicitly so later polynomial substitution has a unique syntax. -/
def standardPlaquetteHolonomy (input : FourOrientedEdgeInput) : UnitNorm :=
  UnitNorm.mul
    (UnitNorm.mul
      (UnitNorm.mul input.u0 input.u3)
      (UnitNorm.inv input.u2))
    (UnitNorm.inv input.u1)

/-- The plaquette holonomy retains the exact raw unit-norm equation. -/
theorem standardPlaquetteHolonomy_isUnitNorm
    (input : FourOrientedEdgeInput) :
    IsUnitNorm (standardPlaquetteHolonomy input).val :=
  (standardPlaquetteHolonomy input).unitNorm

/-- The standard plaquette word as an input to the local anchor-face SOS. -/
def plaquetteHolonomyInput
    (input : FourOrientedEdgeInput) : AnchorQuaternionInput :=
  unitNormToAnchorQuaternionInput (standardPlaquetteHolonomy input)

/-- The holonomy input lies on the rational unit three-sphere. -/
theorem plaquetteHolonomyInput_onSphere (input : FourOrientedEdgeInput) :
    OnUnitQuaternionSphere
      (plaquetteHolonomyInput input).x
      (plaquetteHolonomyInput input).y1
      (plaquetteHolonomyInput input).y2
      (plaquetteHolonomyInput input).y3 :=
  (plaquetteHolonomyInput input).onSphere

/-! ## 3. Exact pullback of the local finite SOS -/

/-- The complete anchor-face SOS pulled back to its four oriented edge
values.  The term count and all weights are definitionally unchanged. -/
def anchorFaceHolonomySOS (cutoff : Nat) :
    FiniteWeightedRationalSOS FourOrientedEdgeInput :=
  pullback plaquetteHolonomyInput (anchorFaceSOS cutoff)

/-- Exact evaluation of the pulled-back SOS at the standard plaquette
holonomy. -/
theorem value_anchorFaceHolonomySOS
    (cutoff : Nat) (input : FourOrientedEdgeInput) :
    value (anchorFaceHolonomySOS cutoff) input ≈
      anchorTruncatedFaceClassValue cutoff
        (standardPlaquetteHolonomy input).val.r := by
  refine Q'.eqv_trans _ _ _
    (value_pullback plaquetteHolonomyInput (anchorFaceSOS cutoff) input) ?_
  simpa only [plaquetteHolonomyInput, unitNormToAnchorQuaternionInput] using
    (Q'.eqv_symm
      (anchorTruncatedFaceClassValue_eqv_anchorFaceSOS cutoff
        (plaquetteHolonomyInput input)))

/-- The pulled-back finite SOS is pointwise nonnegative on every four-edge
input. -/
theorem anchorFaceHolonomySOS_nonnegative
    (cutoff : Nat) (input : FourOrientedEdgeInput) :
    (0 : Q') ≤ value (anchorFaceHolonomySOS cutoff) input :=
  value_nonnegative (anchorFaceHolonomySOS cutoff) input

/-- Equivalently, the physical truncated class value is nonnegative at every
rational plaquette holonomy. -/
theorem anchorTruncatedFaceClassValue_holonomy_nonnegative
    (cutoff : Nat) (input : FourOrientedEdgeInput) :
    (0 : Q') ≤ anchorTruncatedFaceClassValue cutoff
      (standardPlaquetteHolonomy input).val.r := by
  simpa only [plaquetteHolonomyInput, unitNormToAnchorQuaternionInput] using
    (anchorTruncatedFaceClassValue_nonnegative cutoff
      (plaquetteHolonomyInput input))

/-! ## 4. The literal `edgesOf` projection from a lattice gauge field -/

/-- A rational unit-quaternion value on every positive-coordinate lattice
link.  No finite-volume restriction is imposed at this local projection
layer. -/
abbrev RationalUnitQuaternionGaugeField := Z4Link → UnitNorm

/-- Read the four positive-coordinate links of a plaquette in the exact
`edgesOf` order `0,1,2,3`. -/
def plaquetteOrientedEdgeInput
    (field : RationalUnitQuaternionGaugeField) (plaquette : Z4Plaq) :
    FourOrientedEdgeInput :=
  let a := (dirsOf plaquette.2).1
  let b := (dirsOf plaquette.2).2
  ⟨field (plaquette.1, a),
    field (plaquette.1, b),
    field (addE plaquette.1 b, a),
    field (addE plaquette.1 a, b)⟩

/-- The projection above is definitionally the map of a field over the
audited `edgesOf` list. -/
theorem plaquetteOrientedEdgeInput_toList
    (field : RationalUnitQuaternionGaugeField) (plaquette : Z4Plaq) :
    (plaquetteOrientedEdgeInput field plaquette).toList =
      (edgesOf plaquette).map field := rfl

/-- Standard oriented holonomy of a lattice gauge field around one
plaquette. -/
def latticePlaquetteHolonomy
    (field : RationalUnitQuaternionGaugeField) (plaquette : Z4Plaq) : UnitNorm :=
  standardPlaquetteHolonomy (plaquetteOrientedEdgeInput field plaquette)

/-- The corresponding anchor input for one lattice plaquette. -/
def latticePlaquetteHolonomyInput
    (field : RationalUnitQuaternionGaugeField)
    (plaquette : Z4Plaq) : AnchorQuaternionInput :=
  plaquetteHolonomyInput (plaquetteOrientedEdgeInput field plaquette)

/-- The face SOS pulled all the way back to a gauge field at a fixed physical
plaquette. -/
def latticeAnchorFaceHolonomySOS (cutoff : Nat) (plaquette : Z4Plaq) :
    FiniteWeightedRationalSOS RationalUnitQuaternionGaugeField :=
  pullback (fun field => plaquetteOrientedEdgeInput field plaquette)
    (anchorFaceHolonomySOS cutoff)

/-- Exact evaluation of the gauge-field pullback at the physical plaquette
holonomy. -/
theorem value_latticeAnchorFaceHolonomySOS
    (cutoff : Nat) (plaquette : Z4Plaq)
    (field : RationalUnitQuaternionGaugeField) :
    value (latticeAnchorFaceHolonomySOS cutoff plaquette) field ≈
      anchorTruncatedFaceClassValue cutoff
        (latticePlaquetteHolonomy field plaquette).val.r := by
  exact Q'.eqv_trans _ _ _
    (value_pullback
      (fun gaugeField => plaquetteOrientedEdgeInput gaugeField plaquette)
      (anchorFaceHolonomySOS cutoff) field)
    (value_anchorFaceHolonomySOS cutoff
      (plaquetteOrientedEdgeInput field plaquette))

/-- The gauge-field pullback is pointwise nonnegative. -/
theorem latticeAnchorFaceHolonomySOS_nonnegative
    (cutoff : Nat) (plaquette : Z4Plaq)
    (field : RationalUnitQuaternionGaugeField) :
    (0 : Q') ≤ value (latticeAnchorFaceHolonomySOS cutoff plaquette) field :=
  value_nonnegative (latticeAnchorFaceHolonomySOS cutoff plaquette) field

/-! ## 5. Explicit sixteen-coordinate boundary -/

/-- Raw rational coordinates of the four link values, in edge-major order
`(u0.r,u0.i,u0.j,u0.k, ..., u3.r,u3.i,u3.j,u3.k)`. -/
def fourEdgeCoordinateList (input : FourOrientedEdgeInput) : List Q' :=
  [input.u0.val.r, input.u0.val.i, input.u0.val.j, input.u0.val.k,
    input.u1.val.r, input.u1.val.i, input.u1.val.j, input.u1.val.k,
    input.u2.val.r, input.u2.val.i, input.u2.val.j, input.u2.val.k,
    input.u3.val.r, input.u3.val.i, input.u3.val.j, input.u3.val.k]

@[simp] theorem fourEdgeCoordinateList_length
    (input : FourOrientedEdgeInput) :
    (fourEdgeCoordinateList input).length = 16 := rfl

/-- Total sixteen-coordinate environment for later `RatPoly` substitution;
coordinates beyond the four quaternion blocks are sent to zero. -/
def fourEdgeEnvironment
    (input : FourOrientedEdgeInput) (coordinate : Nat) : Q' :=
  (fourEdgeCoordinateList input).getD coordinate 0

@[simp] theorem fourEdgeEnvironment_u0_r (input : FourOrientedEdgeInput) :
    fourEdgeEnvironment input 0 = input.u0.val.r := rfl

@[simp] theorem fourEdgeEnvironment_u0_i (input : FourOrientedEdgeInput) :
    fourEdgeEnvironment input 1 = input.u0.val.i := rfl

@[simp] theorem fourEdgeEnvironment_u0_j (input : FourOrientedEdgeInput) :
    fourEdgeEnvironment input 2 = input.u0.val.j := rfl

@[simp] theorem fourEdgeEnvironment_u0_k (input : FourOrientedEdgeInput) :
    fourEdgeEnvironment input 3 = input.u0.val.k := rfl

@[simp] theorem fourEdgeEnvironment_u1_r (input : FourOrientedEdgeInput) :
    fourEdgeEnvironment input 4 = input.u1.val.r := rfl

@[simp] theorem fourEdgeEnvironment_u2_r (input : FourOrientedEdgeInput) :
    fourEdgeEnvironment input 8 = input.u2.val.r := rfl

@[simp] theorem fourEdgeEnvironment_u3_r (input : FourOrientedEdgeInput) :
    fourEdgeEnvironment input 12 = input.u3.val.r := rfl

@[simp] theorem fourEdgeEnvironment_u3_k (input : FourOrientedEdgeInput) :
    fourEdgeEnvironment input 15 = input.u3.val.k := rfl

#print axioms unitNormToAnchorQuaternionInput
#print axioms standardPlaquetteHolonomy_isUnitNorm
#print axioms plaquetteHolonomyInput_onSphere
#print axioms value_anchorFaceHolonomySOS
#print axioms anchorFaceHolonomySOS_nonnegative
#print axioms plaquetteOrientedEdgeInput_toList
#print axioms value_latticeAnchorFaceHolonomySOS
#print axioms latticeAnchorFaceHolonomySOS_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
