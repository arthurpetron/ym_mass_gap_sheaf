/-
# Lazy shared-link polynomial features for global quaternion SOS products

The global face density is a product of finite weighted sums of squares.  Its
expanded raw `RatPoly` representative is the wrong computational object:
duplicate-preserving polynomial multiplication can grow very rapidly even
though a selected global SOS feature is only a product of one feature from
each face.

This leaf keeps that product lazy.  A feature is represented by a list of raw
polynomial factors together with an exact evaluation theorem.  Multiplying
two packets concatenates their factor lists and delegates all term counts,
packed indices, weights, and nonnegativity witnesses to the existing
`FiniteWeightedRationalSOSProduct.multiply`.  In particular, no cross-face
`polyMul` is constructed anywhere in this file.

The local anchor-face feature polynomial is first pulled to sixteen oriented
edge coordinates and then substituted into the common physical-link carrier.
Every face in a family is evaluated against the same lattice gauge field, so
shared physical links remain shared variables.  Squaring a selected feature
is represented by appending its factor list to itself, which is the symbolic
payload required by later product-Haar integration.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionGlobalFaceRatPoly

namespace YMGap.Continuum.SU2QuaternionLazyGlobalSOS

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedRationalSOSProduct
open YMGap.Continuum.RatPolySubstitution
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceDensitySOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyRatPoly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceSOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

universe u

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Lazy products of raw polynomial factors -/

/-- Evaluate a list of raw polynomials without first multiplying their
duplicate-preserving term lists. -/
def evalRatPolyFactors (rho : Nat → Q') : List RatPoly → Q'
  | [] => 1
  | polynomial :: tail =>
      evalRatPoly rho polynomial * evalRatPolyFactors rho tail

/-- Evaluation of lazy factors turns concatenation into multiplication. -/
theorem evalRatPolyFactors_append (rho : Nat → Q') :
    ∀ left right : List RatPoly,
      evalRatPolyFactors rho (left ++ right) ≈
        evalRatPolyFactors rho left * evalRatPolyFactors rho right
  | [], right =>
      Q'.eqv_symm (Q'.one_mul_eqv (evalRatPolyFactors rho right))
  | polynomial :: tail, right => by
      change
        evalRatPoly rho polynomial *
            evalRatPolyFactors rho (tail ++ right) ≈
          (evalRatPoly rho polynomial * evalRatPolyFactors rho tail) *
            evalRatPolyFactors rho right
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (evalRatPoly rho polynomial) _ _
          (evalRatPolyFactors_append rho tail right)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-! ## 2. Polynomial-factor realizations of finite weighted SOS data -/

/-- A finite weighted rational SOS whose selected feature is represented by
a lazy list of raw polynomial factors in one common environment.

The underlying SOS data is stored verbatim.  Consequently term counts,
weights, and every weight-nonnegativity witness are preserved rather than
reconstructed. -/
structure LazyRatPolySOSFeatures (Input : Type u)
    (environment : Input → Nat → Q') : Type u where
  data : FiniteWeightedRationalSOS Input
  factors : Nat → List RatPoly
  eval_factors : ∀ (term : Nat) (input : Input),
    evalRatPolyFactors (environment input) (factors term) ≈
      data.feature term input

namespace LazyRatPolySOSFeatures

/-- The one-term constant-one SOS has the empty factor product. -/
def one (Input : Type u) (environment : Input → Nat → Q') :
    LazyRatPolySOSFeatures Input environment where
  data := FiniteWeightedRationalSOSProduct.one Input
  factors := fun _ => []
  eval_factors := fun _ _ => Q'.eqv_refl 1

/-- Lazy product of two polynomially realized SOS packets.  The right packet
is the least-significant packed coordinate, exactly as in the underlying
finite weighted SOS product. -/
def multiply {Input : Type u} {environment : Input → Nat → Q'}
    (left right : LazyRatPolySOSFeatures Input environment) :
    LazyRatPolySOSFeatures Input environment where
  data := FiniteWeightedRationalSOSProduct.multiply left.data right.data
  factors := fun packed =>
    left.factors (packed / right.data.termCount) ++
      right.factors (packed % right.data.termCount)
  eval_factors := by
    intro packed input
    exact Q'.eqv_trans _ _ _
      (evalRatPolyFactors_append (environment input)
        (left.factors (packed / right.data.termCount))
        (right.factors (packed % right.data.termCount)))
      (q_mul_congr
        (left.eval_factors (packed / right.data.termCount) input)
        (right.eval_factors (packed % right.data.termCount) input))

/-- Iterated lazy product.  This recursion constructs only packed functions
and factor-list concatenations; it does not enumerate packed terms. -/
def multiplyList {Input : Type u} {environment : Input → Nat → Q'} :
    List (LazyRatPolySOSFeatures Input environment) →
      LazyRatPolySOSFeatures Input environment
  | [] => one Input environment
  | head :: tail => multiply head (multiplyList tail)

/-- The underlying SOS of the lazy list product is exactly the established
finite weighted SOS list product. -/
theorem multiplyList_data
    {Input : Type u} {environment : Input → Nat → Q'} :
    ∀ packets : List (LazyRatPolySOSFeatures Input environment),
      (multiplyList packets).data =
        FiniteWeightedRationalSOSProduct.multiplyList
          (packets.map fun packet => packet.data)
  | [] => rfl
  | head :: tail => by
      change
        FiniteWeightedRationalSOSProduct.multiply head.data
            (multiplyList tail).data =
          FiniteWeightedRationalSOSProduct.multiply head.data
            (FiniteWeightedRationalSOSProduct.multiplyList
              (tail.map fun packet => packet.data))
      exact congrArg
        (FiniteWeightedRationalSOSProduct.multiply head.data)
        (multiplyList_data tail)

/-- Evaluate the weighted square sum represented by a lazy packet without
ever assembling its feature factors into one raw polynomial. -/
def value {Input : Type u} {environment : Input → Nat → Q'}
    (packet : LazyRatPolySOSFeatures Input environment)
    (input : Input) : Q' :=
  finSum (fun term =>
    packet.data.weight term *
      (evalRatPolyFactors (environment input) (packet.factors term) *
        evalRatPolyFactors (environment input) (packet.factors term)))
    packet.data.termCount

/-- Exact shared-input semantics of a lazy packet. -/
theorem value_eqv_dataValue
    {Input : Type u} {environment : Input → Nat → Q'}
    (packet : LazyRatPolySOSFeatures Input environment)
    (input : Input) :
    value packet input ≈
      FiniteWeightedRationalSOSProduct.value packet.data input := by
  unfold value FiniteWeightedRationalSOSProduct.value
  exact finSum_eqv_congr _ _ (fun term =>
    Q'.mul_eqv_congr_left (packet.data.weight term) _ _
      (q_mul_congr
        (packet.eval_factors term input)
        (packet.eval_factors term input))) packet.data.termCount

/-- The square of a selected lazy feature is represented by two copies of
the same factor list, still without raw polynomial multiplication. -/
def squareFactors {Input : Type u} {environment : Input → Nat → Q'}
    (packet : LazyRatPolySOSFeatures Input environment)
    (term : Nat) : List RatPoly :=
  packet.factors term ++ packet.factors term

/-- Exact evaluation of the lazy square-factor list. -/
theorem eval_squareFactors
    {Input : Type u} {environment : Input → Nat → Q'}
    (packet : LazyRatPolySOSFeatures Input environment)
    (term : Nat) (input : Input) :
    evalRatPolyFactors (environment input) (squareFactors packet term) ≈
      packet.data.feature term input * packet.data.feature term input := by
  exact Q'.eqv_trans _ _ _
    (evalRatPolyFactors_append (environment input)
      (packet.factors term) (packet.factors term))
    (q_mul_congr
      (packet.eval_factors term input)
      (packet.eval_factors term input))

end LazyRatPolySOSFeatures

/-! ## 3. One global anchor-face feature packet -/

/-- A selected anchor-face feature pulled from its local sixteen edge
coordinates into the supplied common physical-link carrier. -/
def globalAnchorFaceFeaturePolynomial
    (cutoff : Nat) (links : List Z4Link)
    (plaquette : Z4Plaq) (term : Nat) : RatPoly :=
  substitute (faceToGlobalLinkSubstitution links plaquette)
    (anchorFaceHolonomyFeaturePolynomial cutoff term)

/-- Exact evaluation of one globally coordinated face feature against one
lattice gauge field. -/
theorem eval_globalAnchorFaceFeaturePolynomial
    (cutoff : Nat) (links : List Z4Link)
    (plaquette : Z4Plaq) (term : Nat)
    (field : RationalUnitQuaternionGaugeField)
    (hsupport : ∀ link, link ∈ edgesOf plaquette → link ∈ links) :
    evalRatPoly (globalLinkEnvironment links field)
        (globalAnchorFaceFeaturePolynomial cutoff links plaquette term) ≈
      (latticeAnchorFaceHolonomySOS cutoff plaquette).feature term field := by
  change
    evalRatPoly (globalLinkEnvironment links field)
        (substitute (faceToGlobalLinkSubstitution links plaquette)
          (anchorFaceHolonomyFeaturePolynomial cutoff term)) ≈
      (anchorFaceHolonomySOS cutoff).feature term
        (plaquetteOrientedEdgeInput field plaquette)
  exact Q'.eqv_trans _ _ _
    (eval_substitute
      (faceToGlobalLinkSubstitution links plaquette)
      (anchorFaceHolonomyFeaturePolynomial cutoff term)
      (globalLinkEnvironment links field))
    (Q'.eqv_trans _ _ _
      (evalRatPoly_environment_congr
        (eval_faceToGlobalLinkSubstitution links field plaquette hsupport)
        (anchorFaceHolonomyFeaturePolynomial cutoff term))
      (eval_anchorFaceHolonomyFeaturePolynomial cutoff term
        (plaquetteOrientedEdgeInput field plaquette)))

/-- The lazy one-face packet.  It stores the existing gauge-field SOS
verbatim and represents each selected feature by a singleton polynomial
factor list. -/
def globalAnchorFaceLazyPacket
    (cutoff : Nat) (links : List Z4Link) (plaquette : Z4Plaq)
    (hsupport : ∀ link, link ∈ edgesOf plaquette → link ∈ links) :
    LazyRatPolySOSFeatures RationalUnitQuaternionGaugeField
      (fun field => globalLinkEnvironment links field) where
  data := latticeAnchorFaceHolonomySOS cutoff plaquette
  factors := fun term =>
    [globalAnchorFaceFeaturePolynomial cutoff links plaquette term]
  eval_factors := by
    intro term field
    change
      evalRatPoly (globalLinkEnvironment links field)
          (globalAnchorFaceFeaturePolynomial cutoff links plaquette term) *
          1 ≈
        (latticeAnchorFaceHolonomySOS cutoff plaquette).feature term field
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ 1
        (eval_globalAnchorFaceFeaturePolynomial
          cutoff links plaquette term field hsupport))
      (Q'.mul_one_eqv _)

/-- The one-face packet preserves the anchor SOS term count exactly. -/
theorem globalAnchorFaceLazyPacket_termCount
    (cutoff : Nat) (links : List Z4Link) (plaquette : Z4Plaq)
    (hsupport : ∀ link, link ∈ edgesOf plaquette → link ∈ links) :
    (globalAnchorFaceLazyPacket cutoff links plaquette hsupport).data.termCount =
      (anchorFaceSOS cutoff).termCount := rfl

/-- The one-face packet preserves every anchor SOS weight exactly. -/
theorem globalAnchorFaceLazyPacket_weight
    (cutoff : Nat) (links : List Z4Link) (plaquette : Z4Plaq)
    (hsupport : ∀ link, link ∈ edgesOf plaquette → link ∈ links)
    (term : Nat) :
    (globalAnchorFaceLazyPacket cutoff links plaquette hsupport).data.weight term =
      (anchorFaceSOS cutoff).weight term := rfl

/-! ## 4. Lazy finite face families -/

/-- Build one lazy singleton-feature packet for every plaquette in a finite
family.  The support certificate ensures that all packets use the same global
link environment. -/
def globalAnchorFaceLazyPackets
    (cutoff : Nat) (links : List Z4Link) :
    ∀ plaquettes : List Z4Plaq,
      (∀ plaquette, plaquette ∈ plaquettes →
        ∀ link, link ∈ edgesOf plaquette → link ∈ links) →
      List (LazyRatPolySOSFeatures RationalUnitQuaternionGaugeField
        (fun field => globalLinkEnvironment links field))
  | [], _ => []
  | plaquette :: tail, hsupport =>
      globalAnchorFaceLazyPacket cutoff links plaquette
          (fun link hlink =>
            hsupport plaquette List.mem_cons_self link hlink) ::
        globalAnchorFaceLazyPackets cutoff links tail
          (fun source hsource link hlink =>
            hsupport source (List.mem_cons_of_mem plaquette hsource)
              link hlink)

/-- Forgetting lazy feature realizations recovers the exact mapped list of
gauge-field face SOS factors. -/
theorem globalAnchorFaceLazyPackets_data
    (cutoff : Nat) (links : List Z4Link) :
    ∀ (plaquettes : List Z4Plaq)
      (hsupport : ∀ plaquette, plaquette ∈ plaquettes →
        ∀ link, link ∈ edgesOf plaquette → link ∈ links),
      (globalAnchorFaceLazyPackets cutoff links plaquettes hsupport).map
          (fun packet => packet.data) =
        anchorFaceDensityFactorList cutoff plaquettes
  | [], _ => rfl
  | plaquette :: tail, hsupport => by
      change
        latticeAnchorFaceHolonomySOS cutoff plaquette ::
            (globalAnchorFaceLazyPackets cutoff links tail
              (fun source hsource link hlink =>
                hsupport source
                  (List.mem_cons_of_mem plaquette hsource) link hlink)).map
              (fun packet => packet.data) =
          latticeAnchorFaceHolonomySOS cutoff plaquette ::
            anchorFaceDensityFactorList cutoff tail
      exact congrArg
        (List.cons (latticeAnchorFaceHolonomySOS cutoff plaquette))
        (globalAnchorFaceLazyPackets_data cutoff links tail
          (fun source hsource link hlink =>
            hsupport source
              (List.mem_cons_of_mem plaquette hsource) link hlink))

/-- The complete lazy product packet for a finite family of faces. -/
def globalAnchorFaceLazyDensityPacket
    (cutoff : Nat) (links : List Z4Link) (plaquettes : List Z4Plaq)
    (hsupport : ∀ plaquette, plaquette ∈ plaquettes →
      ∀ link, link ∈ edgesOf plaquette → link ∈ links) :
    LazyRatPolySOSFeatures RationalUnitQuaternionGaugeField
      (fun field => globalLinkEnvironment links field) :=
  LazyRatPolySOSFeatures.multiplyList
    (globalAnchorFaceLazyPackets cutoff links plaquettes hsupport)

/-- The underlying SOS of the lazy family is exactly the existing symbolic
finite face-density SOS. -/
theorem globalAnchorFaceLazyDensityPacket_data
    (cutoff : Nat) (links : List Z4Link) (plaquettes : List Z4Plaq)
    (hsupport : ∀ plaquette, plaquette ∈ plaquettes →
      ∀ link, link ∈ edgesOf plaquette → link ∈ links) :
    (globalAnchorFaceLazyDensityPacket
        cutoff links plaquettes hsupport).data =
      anchorFaceDensitySOS cutoff plaquettes := by
  unfold globalAnchorFaceLazyDensityPacket anchorFaceDensitySOS
  rw [LazyRatPolySOSFeatures.multiplyList_data]
  rw [globalAnchorFaceLazyPackets_data]

/-- Exact shared-field evaluation of the lazy finite face family. -/
theorem value_globalAnchorFaceLazyDensityPacket
    (cutoff : Nat) (links : List Z4Link) (plaquettes : List Z4Plaq)
    (hsupport : ∀ plaquette, plaquette ∈ plaquettes →
      ∀ link, link ∈ edgesOf plaquette → link ∈ links)
    (field : RationalUnitQuaternionGaugeField) :
    LazyRatPolySOSFeatures.value
        (globalAnchorFaceLazyDensityPacket cutoff links plaquettes hsupport)
        field ≈
      anchorFaceClassValueProduct cutoff plaquettes field := by
  exact Q'.eqv_trans _ _ _
    (LazyRatPolySOSFeatures.value_eqv_dataValue
      (globalAnchorFaceLazyDensityPacket cutoff links plaquettes hsupport)
      field)
    (Q'.eqv_trans _ _ _
      (by
        rw [globalAnchorFaceLazyDensityPacket_data]
        exact Q'.eqv_refl _)
      (value_anchorFaceDensitySOS cutoff plaquettes field))

/-! ## 5. Production adjacent-even fixed-face family -/

/-- The lazy product packet on the complete adjacent-even fixed-face family. -/
def adjacentEvenFixedFaceLazyDensityPacket
    (cutoff radius : Nat) :
    LazyRatPolySOSFeatures RationalUnitQuaternionGaugeField
      (fun field => adjacentEvenActiveLinkEnvironment radius field) :=
  globalAnchorFaceLazyDensityPacket cutoff
    (adjacentEvenActiveLinks radius)
    (adjacentEvenFixedFacePlaquettes radius)
    (fun _ hplaquette _ hlink =>
      adjacentEvenFixedFacePlaquette_edge_mem_activeLinks
        hplaquette hlink)

/-- Exact shared-gauge-field evaluation on the production fixed-face list. -/
theorem value_adjacentEvenFixedFaceLazyDensityPacket
    (cutoff radius : Nat) (field : RationalUnitQuaternionGaugeField) :
    LazyRatPolySOSFeatures.value
        (adjacentEvenFixedFaceLazyDensityPacket cutoff radius) field ≈
      adjacentEvenFixedFaceClassValueProduct cutoff radius field := by
  exact value_globalAnchorFaceLazyDensityPacket cutoff
    (adjacentEvenActiveLinks radius)
    (adjacentEvenFixedFacePlaquettes radius)
    (fun _ hplaquette _ hlink =>
      adjacentEvenFixedFacePlaquette_edge_mem_activeLinks
        hplaquette hlink)
    field

#print axioms evalRatPolyFactors_append
#print axioms LazyRatPolySOSFeatures.multiplyList_data
#print axioms LazyRatPolySOSFeatures.value_eqv_dataValue
#print axioms LazyRatPolySOSFeatures.eval_squareFactors
#print axioms eval_globalAnchorFaceFeaturePolynomial
#print axioms globalAnchorFaceLazyPacket_weight
#print axioms globalAnchorFaceLazyPackets_data
#print axioms globalAnchorFaceLazyDensityPacket_data
#print axioms value_globalAnchorFaceLazyDensityPacket
#print axioms value_adjacentEvenFixedFaceLazyDensityPacket

end YMGap.Continuum.SU2QuaternionLazyGlobalSOS
