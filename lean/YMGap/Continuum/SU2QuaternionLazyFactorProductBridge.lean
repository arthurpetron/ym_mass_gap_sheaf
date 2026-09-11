/-
# From lazy quaternion factors to one supported Haar polynomial

The global face SOS deliberately stores a selected feature as a list of raw
`RatPoly` factors.  Product-Haar square positivity, by contrast, consumes one
raw polynomial `p` and its square `polyMul p p`.  This leaf supplies the
algebraic bridge between those interfaces without unfolding any concrete
face polynomial.

The factor product is a right-recursive opaque `RatPoly` construction.  Its
evaluation is exactly `evalRatPolyFactors`, and a uniform finite-coordinate
support bound on the list is preserved by the product.  Concatenation is
multiplication up to extensional `RatPolyEqv`; consequently the product of a
lazy packet's two-copy `squareFactors` list is extensionally the raw square of
the one-copy factor product.

The final specialization packages the adjacent-even selected plane half as
one polynomial supported on exactly the active quaternion blocks.  This is
the input shape required by the finite-product Haar square theorem once its
arbitrary block-sector closure is available.  No Haar positivity or
spin/kernel identification is asserted here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
import YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazyEndpointScaleAssembly

namespace YMGap.Continuum.SU2QuaternionLazyFactorProductBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPoly
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
open YMGap.Continuum.SU2QuaternionLazyGlobalSOS
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazyEndpointScaleAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazySectorSplit

local infix:50 " ≈ " => Q'.eqv

/-- Explicit local name for the physical four-dimensional plaquette type.
The qualification prevents collision with unrelated imported plaquette
carriers. -/
abbrev PhysicalZ4Plaq : Type :=
  YMGap.Continuum.ClusterCount4DProgress.Z4Plaq

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Recursive raw product of a lazy factor list -/

/-- Right-recursive raw product of polynomial factors.  This definition is
kept opaque in downstream work: unfolding it on a concrete nontrivial face
family can materialize a very large duplicate-preserving term list. -/
def ratPolyFactorProduct : List RatPoly → RatPoly
  | [] => polyOne
  | polynomial :: factors =>
      polyMul polynomial (ratPolyFactorProduct factors)

/-- The raw recursive product evaluates exactly as the established lazy
factor-list evaluator. -/
theorem eval_ratPolyFactorProduct (rho : Nat → Q') :
    ∀ factors : List RatPoly,
      evalRatPoly rho (ratPolyFactorProduct factors) ≈
        evalRatPolyFactors rho factors
  | [] => evalRatPoly_one rho
  | polynomial :: factors => by
      change
        evalRatPoly rho
            (polyMul polynomial (ratPolyFactorProduct factors)) ≈
          evalRatPoly rho polynomial * evalRatPolyFactors rho factors
      exact Q'.eqv_trans _ _ _
        (evalRatPoly_mul rho polynomial
          (ratPolyFactorProduct factors))
        (Q'.mul_eqv_congr_left
          (evalRatPoly rho polynomial) _ _
          (eval_ratPolyFactorProduct rho factors))

/-- Uniform finite-coordinate support is closed under the recursive raw
factor product. -/
theorem ratPolyFactorProduct_supported
    {coordinateCount : Nat} : ∀ {factors : List RatPoly},
    SupportedRatPolyFactors coordinateCount factors →
      SupportedCoordinates coordinateCount
        (ratPolyFactorProduct factors)
  | [], _ => supportedCoordinates_polyOne coordinateCount
  | polynomial :: factors, hsupport => by
      apply supportedCoordinates_polyMul
      · exact hsupport polynomial List.mem_cons_self
      · apply ratPolyFactorProduct_supported
        intro source hsource
        exact hsupport source
          (List.mem_cons_of_mem polynomial hsource)

/-! ## 2. Concatenation and the two-copy square -/

/-- Concatenating lazy factor lists is raw polynomial multiplication up to
extensional polynomial equality. -/
theorem ratPolyFactorProduct_append_eqv
    (left right : List RatPoly) :
    RatPolyEqv (ratPolyFactorProduct (left ++ right))
      (polyMul (ratPolyFactorProduct left)
        (ratPolyFactorProduct right)) := by
  intro rho
  refine Q'.eqv_trans _ _ _
    (eval_ratPolyFactorProduct rho (left ++ right)) ?_
  refine Q'.eqv_trans _ _ _
    (evalRatPolyFactors_append rho left right) ?_
  refine Q'.eqv_trans _ _ _
    (q_mul_congr
      (Q'.eqv_symm (eval_ratPolyFactorProduct rho left))
      (Q'.eqv_symm (eval_ratPolyFactorProduct rho right))) ?_
  exact Q'.eqv_symm
    (evalRatPoly_mul rho
      (ratPolyFactorProduct left)
      (ratPolyFactorProduct right))

/-- One raw polynomial representing the selected feature of a lazy packet. -/
def lazyFeaturePolynomial
    {Input : Type} {environment : Input → Nat → Q'}
    (packet : LazyRatPolySOSFeatures Input environment)
    (term : Nat) : RatPoly :=
  ratPolyFactorProduct (packet.factors term)

/-- One raw polynomial representing the packet's lazy two-copy square list. -/
def lazySquareFactorPolynomial
    {Input : Type} {environment : Input → Nat → Q'}
    (packet : LazyRatPolySOSFeatures Input environment)
    (term : Nat) : RatPoly :=
  ratPolyFactorProduct (LazyRatPolySOSFeatures.squareFactors packet term)

theorem eval_lazyFeaturePolynomial
    {Input : Type} {environment : Input → Nat → Q'}
    (packet : LazyRatPolySOSFeatures Input environment)
    (term : Nat) (input : Input) :
    evalRatPoly (environment input)
        (lazyFeaturePolynomial packet term) ≈
      packet.data.feature term input := by
  exact Q'.eqv_trans _ _ _
    (eval_ratPolyFactorProduct
      (environment input) (packet.factors term))
    (packet.eval_factors term input)

/-- The raw product of the two-copy lazy square list is extensionally the
ordinary raw square of the one-copy factor product. -/
theorem lazySquareFactorPolynomial_eqv_polyMul
    {Input : Type} {environment : Input → Nat → Q'}
    (packet : LazyRatPolySOSFeatures Input environment)
    (term : Nat) :
    RatPolyEqv (lazySquareFactorPolynomial packet term)
      (polyMul (lazyFeaturePolynomial packet term)
        (lazyFeaturePolynomial packet term)) := by
  exact ratPolyFactorProduct_append_eqv
    (packet.factors term) (packet.factors term)

/-- Support of the selected one-copy packet polynomial. -/
theorem lazyFeaturePolynomial_supported
    {Input : Type} {environment : Input → Nat → Q'}
    {coordinateCount : Nat}
    {packet : LazyRatPolySOSFeatures Input environment}
    (hsupport : LazyPacketSupported coordinateCount packet)
    (term : Nat) :
    SupportedCoordinates coordinateCount
      (lazyFeaturePolynomial packet term) :=
  ratPolyFactorProduct_supported (hsupport term)

/-- Both the two-copy factor product and the direct raw square retain the
same packet coordinate bound. -/
theorem lazySquareFactorPolynomials_supported
    {Input : Type} {environment : Input → Nat → Q'}
    {coordinateCount : Nat}
    {packet : LazyRatPolySOSFeatures Input environment}
    (hsupport : LazyPacketSupported coordinateCount packet)
    (term : Nat) :
    SupportedCoordinates coordinateCount
        (lazySquareFactorPolynomial packet term) ∧
      SupportedCoordinates coordinateCount
        (polyMul (lazyFeaturePolynomial packet term)
          (lazyFeaturePolynomial packet term)) := by
  have hhalf := lazyFeaturePolynomial_supported hsupport term
  constructor
  · apply ratPolyFactorProduct_supported
    exact supportedRatPolyFactors_append
      (hsupport term) (hsupport term)
  · exact supportedCoordinates_polyMul hhalf hhalf

/-! ## 3. Adjacent-even selected plane specialization -/

/-- One raw polynomial for a selected feature on every adjacent-even fixed
face, all expressed in the common deduplicated active-link carrier. -/
def adjacentEvenLazyPlaneHalfPolynomial
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat) : RatPoly :=
  ratPolyFactorProduct
    (adjacentEvenLazyPlaneHalfFactors cutoff radius faceTerm)

/-- Raw product of the corresponding two-copy lazy square-factor list. -/
def adjacentEvenLazyPlaneSquareFactorPolynomial
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat) : RatPoly :=
  ratPolyFactorProduct
    (adjacentEvenFixedFaceSelectedSquareFactors
      cutoff radius faceTerm)

theorem eval_adjacentEvenLazyPlaneHalfPolynomial
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat)
    (rho : Nat → Q') :
    evalRatPoly rho
        (adjacentEvenLazyPlaneHalfPolynomial
          cutoff radius faceTerm) ≈
      adjacentEvenLazyPlaneHalfValue cutoff radius faceTerm rho := by
  exact eval_ratPolyFactorProduct _ _

theorem eval_adjacentEvenLazyPlaneSquareFactorPolynomial
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat)
    (rho : Nat → Q') :
    evalRatPoly rho
        (adjacentEvenLazyPlaneSquareFactorPolynomial
          cutoff radius faceTerm) ≈
      adjacentEvenLazyPlaneHalfValue cutoff radius faceTerm rho *
        adjacentEvenLazyPlaneHalfValue cutoff radius faceTerm rho := by
  exact Q'.eqv_trans _ _ _
    (eval_ratPolyFactorProduct rho
      (adjacentEvenFixedFaceSelectedSquareFactors
        cutoff radius faceTerm))
    (eval_adjacentEvenFixedFaceSelectedSquareFactors
      cutoff radius faceTerm rho)

/-- The production selected factor list has the exact active coordinate
support before its raw product is assembled. -/
theorem adjacentEvenLazyPlaneHalfFactors_supported
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat) :
    SupportedRatPolyFactors
      (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenLazyPlaneHalfFactors cutoff radius faceTerm) := by
  intro polynomial hpolynomial
  unfold adjacentEvenLazyPlaneHalfFactors
    selectedGlobalAnchorFaceFactors at hpolynomial
  rw [List.mem_map] at hpolynomial
  obtain ⟨entry, _, rfl⟩ := hpolynomial
  change
    SupportedCoordinates
      (linkQuaternionCoordinateCount (adjacentEvenActiveLinks radius))
      (globalAnchorFaceFeaturePolynomial cutoff
        (adjacentEvenActiveLinks radius) entry.1 entry.2)
  exact globalAnchorFaceFeaturePolynomial_supported _ _ _ _

theorem adjacentEvenLazyPlaneHalfPolynomial_supported
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat) :
    SupportedCoordinates (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenLazyPlaneHalfPolynomial
        cutoff radius faceTerm) := by
  apply ratPolyFactorProduct_supported
  exact adjacentEvenLazyPlaneHalfFactors_supported cutoff radius faceTerm

/-- The raw one-copy plane polynomial is supported on precisely the first
`activeLinks.length` quaternion blocks, in the finite-product Haar carrier's
native predicate. -/
theorem adjacentEvenLazyPlaneHalfPolynomial_supportedBlocks
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat) :
    SupportedQuaternionBlocks (adjacentEvenActiveLinks radius).length
      (adjacentEvenLazyPlaneHalfPolynomial
        cutoff radius faceTerm) := by
  rw [← supportedCoordinates_four_mul_iff]
  exact adjacentEvenLazyPlaneHalfPolynomial_supported
    cutoff radius faceTerm

/-- Exact bridge requested by finite-product Haar square positivity: the
two-copy lazy factor product is extensionally the raw square of the supported
active-link polynomial. -/
theorem adjacentEvenLazyPlaneSquareFactorPolynomial_eqv_polyMul
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat) :
    RatPolyEqv
      (adjacentEvenLazyPlaneSquareFactorPolynomial
        cutoff radius faceTerm)
      (polyMul
        (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm)
        (adjacentEvenLazyPlaneHalfPolynomial
          cutoff radius faceTerm)) := by
  exact ratPolyFactorProduct_append_eqv
    (adjacentEvenLazyPlaneHalfFactors cutoff radius faceTerm)
    (adjacentEvenLazyPlaneHalfFactors cutoff radius faceTerm)

theorem adjacentEvenLazyPlaneSquarePolynomials_supportedBlocks
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat) :
    SupportedQuaternionBlocks (adjacentEvenActiveLinks radius).length
        (adjacentEvenLazyPlaneSquareFactorPolynomial
          cutoff radius faceTerm) ∧
      SupportedQuaternionBlocks (adjacentEvenActiveLinks radius).length
        (polyMul
          (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm)
          (adjacentEvenLazyPlaneHalfPolynomial
            cutoff radius faceTerm)) := by
  have hhalf := adjacentEvenLazyPlaneHalfFactors_supported
    cutoff radius faceTerm
  constructor
  · rw [← supportedCoordinates_four_mul_iff]
    apply ratPolyFactorProduct_supported
    exact supportedRatPolyFactors_append hhalf hhalf
  · rw [← supportedCoordinates_four_mul_iff]
    exact supportedCoordinates_polyMul
      (adjacentEvenLazyPlaneHalfPolynomial_supported
        cutoff radius faceTerm)
      (adjacentEvenLazyPlaneHalfPolynomial_supported
        cutoff radius faceTerm)

#print axioms eval_ratPolyFactorProduct
#print axioms ratPolyFactorProduct_supported
#print axioms ratPolyFactorProduct_append_eqv
#print axioms lazySquareFactorPolynomial_eqv_polyMul
#print axioms lazySquareFactorPolynomials_supported
#print axioms eval_adjacentEvenLazyPlaneHalfPolynomial
#print axioms adjacentEvenLazyPlaneHalfPolynomial_supportedBlocks
#print axioms adjacentEvenLazyPlaneSquareFactorPolynomial_eqv_polyMul
#print axioms adjacentEvenLazyPlaneSquarePolynomials_supportedBlocks

end YMGap.Continuum.SU2QuaternionLazyFactorProductBridge
