/-
# Constructive support bounds for shared-link quaternion polynomials

The raw rational-polynomial carrier records a monomial by a finite exponent
list.  This leaf packages the corresponding finite-coordinate support
invariant at an arbitrary coordinate count and proves that it is preserved by
all literal polynomial operations used by substitution.

Applying that calculus to the shared-link base-four codec proves that every
local face coordinate, every substituted anchor-face polynomial, and every
selected lazy anchor-face feature lives in the exact common carrier

    4 * links.length.

The production adjacent-even statements specialize this to
`adjacentEvenActiveCoordinateCount radius`.  Thus later finite-product Haar
and Fubini arguments can consume the lazy face factors without an additional
support hypothesis or an eight-coordinate truncation.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
import YMGap.Continuum.SU2QuaternionLazyGlobalSOS

namespace YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

universe u

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RatPolySubstitution
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPoly
open YMGap.Continuum.SU2QuaternionLazyGlobalSOS
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceDensitySOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyRatPoly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Generic finite-coordinate support calculus -/

/-- Literal support in the first `coordinateCount` coordinates of the raw
finite-list polynomial carrier.  This is intentionally the same convention
as `Supported8` and `SupportedQuaternionBlocks`: even a trailing zero is kept
inside the structural support bound. -/
def SupportedCoordinates
    (coordinateCount : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial → term.1.length ≤ coordinateCount

/-- The generic coordinate predicate agrees definitionally with the
finite-product Haar block predicate at a base-four coordinate count. -/
theorem supportedCoordinates_four_mul_iff
    (blockCount : Nat) (polynomial : RatPoly) :
    SupportedCoordinates (4 * blockCount) polynomial ↔
      SupportedQuaternionBlocks blockCount polynomial :=
  Iff.rfl

theorem supportedCoordinates_polyZero (coordinateCount : Nat) :
    SupportedCoordinates coordinateCount polyZero := by
  intro term hterm
  simp only [polyZero, List.not_mem_nil] at hterm

theorem supportedCoordinates_polyOne (coordinateCount : Nat) :
    SupportedCoordinates coordinateCount polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_singleton] at hterm
  subst term
  simp

theorem supportedCoordinates_polyConst
    (coordinateCount : Nat) (coefficient : Q') :
    SupportedCoordinates coordinateCount (polyConst coefficient) := by
  intro term hterm
  simp only [polyConst, List.mem_singleton] at hterm
  subst term
  simp

theorem supportedCoordinates_polyVar
    {coordinateCount coordinate : Nat} (hcoordinate : coordinate < coordinateCount) :
    SupportedCoordinates coordinateCount (polyVar coordinate) := by
  intro term hterm
  simp only [polyVar, List.mem_singleton] at hterm
  subst term
  simp only [varMono, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

theorem supportedCoordinates_polyAdd
    {coordinateCount : Nat} {left right : RatPoly}
    (hleft : SupportedCoordinates coordinateCount left)
    (hright : SupportedCoordinates coordinateCount right) :
    SupportedCoordinates coordinateCount (polyAdd left right) := by
  intro term hterm
  simp only [polyAdd, List.mem_append] at hterm
  cases hterm with
  | inl hterm => exact hleft term hterm
  | inr hterm => exact hright term hterm

theorem supportedCoordinates_polyNeg
    {coordinateCount : Nat} {polynomial : RatPoly}
    (hsupport : SupportedCoordinates coordinateCount polynomial) :
    SupportedCoordinates coordinateCount (polyNeg polynomial) := by
  intro term hterm
  unfold polyNeg at hterm
  rw [List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  exact hsupport source hsource

theorem supportedCoordinates_polySmul
    (coefficient : Q') {coordinateCount : Nat} {polynomial : RatPoly}
    (hsupport : SupportedCoordinates coordinateCount polynomial) :
    SupportedCoordinates coordinateCount (polySmul coefficient polynomial) := by
  intro term hterm
  unfold polySmul at hterm
  rw [List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  exact hsupport source hsource

/-- Dropping a prefix commutes with zero-padded componentwise monomial
multiplication. -/
theorem monoMul_drop (left right : List Nat) : ∀ coordinateCount : Nat,
    (monoMul left right).drop coordinateCount =
      monoMul (left.drop coordinateCount) (right.drop coordinateCount)
  | 0 => rfl
  | coordinateCount + 1 => by
      cases left <;> cases right <;>
        simp [monoMul, monoMul_drop]
      next tail => cases tail.drop coordinateCount <;> rfl

/-- Componentwise monomial multiplication cannot exceed a common structural
support bound. -/
theorem monoMul_length_le
    {coordinateCount : Nat} {left right : List Nat}
    (hleft : left.length ≤ coordinateCount)
    (hright : right.length ≤ coordinateCount) :
    (monoMul left right).length ≤ coordinateCount := by
  apply List.drop_eq_nil_iff.mp
  rw [monoMul_drop]
  rw [List.drop_eq_nil_of_le hleft, List.drop_eq_nil_of_le hright]
  rfl

/-- Membership inversion for literal raw-polynomial multiplication. -/
theorem mem_polyMul
    {left right : RatPoly} {term : RatTerm}
    (hterm : term ∈ polyMul left right) :
    ∃ leftTerm, leftTerm ∈ left ∧
      ∃ rightTerm, rightTerm ∈ right ∧
        term =
          (monoMul leftTerm.1 rightTerm.1,
            leftTerm.2 * rightTerm.2) := by
  unfold polyMul at hterm
  rw [List.mem_flatMap] at hterm
  obtain ⟨leftTerm, hleftTerm, hterm⟩ := hterm
  rw [List.mem_map] at hterm
  obtain ⟨rightTerm, hrightTerm, rfl⟩ := hterm
  exact ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, rfl⟩

theorem supportedCoordinates_polyMul
    {coordinateCount : Nat} {left right : RatPoly}
    (hleft : SupportedCoordinates coordinateCount left)
    (hright : SupportedCoordinates coordinateCount right) :
    SupportedCoordinates coordinateCount (polyMul left right) := by
  intro term hterm
  obtain ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, rfl⟩ :=
    mem_polyMul hterm
  exact monoMul_length_le
    (hleft leftTerm hleftTerm) (hright rightTerm hrightTerm)

theorem supportedCoordinates_polyPow
    {coordinateCount : Nat} {polynomial : RatPoly}
    (hsupport : SupportedCoordinates coordinateCount polynomial) :
    ∀ exponent : Nat,
      SupportedCoordinates coordinateCount (polyPow polynomial exponent)
  | 0 => supportedCoordinates_polyOne coordinateCount
  | exponent + 1 =>
      supportedCoordinates_polyMul
        (supportedCoordinates_polyPow hsupport exponent) hsupport

/-- Substituting a monomial preserves a common target support bound whenever
every coordinate polynomial obeys that bound.  No support assumption on the
source exponent list is necessary. -/
theorem supportedCoordinates_substituteMonoFrom
    {coordinateCount : Nat} {sigma : Nat → RatPoly}
    (hsigma : ∀ coordinate, SupportedCoordinates coordinateCount (sigma coordinate)) :
    ∀ (start : Nat) (monomial : List Nat),
      SupportedCoordinates coordinateCount
        (substituteMonoFrom sigma start monomial)
  | _, [] => supportedCoordinates_polyOne coordinateCount
  | start, exponent :: tail =>
      supportedCoordinates_polyMul
        (supportedCoordinates_polyPow (hsigma start) exponent)
        (supportedCoordinates_substituteMonoFrom hsigma (start + 1) tail)

theorem supportedCoordinates_substituteMono
    {coordinateCount : Nat} {sigma : Nat → RatPoly}
    (hsigma : ∀ coordinate, SupportedCoordinates coordinateCount (sigma coordinate))
    (monomial : List Nat) :
    SupportedCoordinates coordinateCount (substituteMono sigma monomial) :=
  supportedCoordinates_substituteMonoFrom hsigma 0 monomial

theorem supportedCoordinates_substituteTerm
    {coordinateCount : Nat} {sigma : Nat → RatPoly}
    (hsigma : ∀ coordinate, SupportedCoordinates coordinateCount (sigma coordinate))
    (term : RatTerm) :
    SupportedCoordinates coordinateCount (substituteTerm sigma term) :=
  supportedCoordinates_polySmul term.2
    (supportedCoordinates_substituteMono hsigma term.1)

/-- Arbitrary-variable substitution preserves a uniform target-coordinate
support bound. -/
theorem supportedCoordinates_substitute
    {coordinateCount : Nat} {sigma : Nat → RatPoly}
    (hsigma : ∀ coordinate, SupportedCoordinates coordinateCount (sigma coordinate)) :
    ∀ polynomial : RatPoly,
      SupportedCoordinates coordinateCount (substitute sigma polynomial)
  | [] => supportedCoordinates_polyZero coordinateCount
  | term :: tail =>
      supportedCoordinates_polyAdd
        (supportedCoordinates_substituteTerm hsigma term)
        (supportedCoordinates_substitute hsigma tail)

/-! ## 2. Exact support of the shared-link coordinate map -/

/-- Every total shared-link coordinate polynomial lies in the exact common
base-four carrier.  Invalid components and absent links are literal zero
polynomials. -/
theorem globalLinkCoordinatePolynomial_supported
    (links : List Z4Link) (link : Z4Link) (component : Nat) :
    SupportedCoordinates (linkQuaternionCoordinateCount links)
      (globalLinkCoordinatePolynomial links link component) := by
  unfold globalLinkCoordinatePolynomial
  by_cases hcomponent : component < 4
  · rw [if_pos hcomponent]
    by_cases hlink : link ∈ links
    · rw [if_pos hlink]
      exact supportedCoordinates_polyVar
        (globalLinkCoordinate_lt_count links link component hlink hcomponent)
    · rw [if_neg hlink]
      exact supportedCoordinates_polyZero _
  · rw [if_neg hcomponent]
    exact supportedCoordinates_polyZero _

/-- Every source coordinate in the local-to-global face map lands in the
exact shared-link carrier, including its explicit zero extension. -/
theorem faceToGlobalLinkSubstitution_supported
    (links : List Z4Link) (plaquette : Z4Plaq) (coordinate : Nat) :
    SupportedCoordinates (linkQuaternionCoordinateCount links)
      (faceToGlobalLinkSubstitution links plaquette coordinate) := by
  unfold faceToGlobalLinkSubstitution
  by_cases hcoordinate : coordinate < 16
  · rw [if_pos hcoordinate]
    exact globalLinkCoordinatePolynomial_supported _ _ _
  · rw [if_neg hcoordinate]
    exact supportedCoordinates_polyZero _

/-- The complete substituted face polynomial is confined to the common
shared-link carrier. -/
theorem globalAnchorFacePolynomial_supported
    (cutoff : Nat) (links : List Z4Link) (plaquette : Z4Plaq) :
    SupportedCoordinates (linkQuaternionCoordinateCount links)
      (globalAnchorFacePolynomial cutoff links plaquette) := by
  unfold globalAnchorFacePolynomial
  exact supportedCoordinates_substitute
    (faceToGlobalLinkSubstitution_supported links plaquette)
    (anchorFaceHolonomyWeightedSOSPolynomial cutoff)

/-- Every selected anchor-face SOS feature, at every cutoff and term index,
is confined to the same shared-link carrier. -/
theorem globalAnchorFaceFeaturePolynomial_supported
    (cutoff : Nat) (links : List Z4Link)
    (plaquette : Z4Plaq) (term : Nat) :
    SupportedCoordinates (linkQuaternionCoordinateCount links)
      (globalAnchorFaceFeaturePolynomial cutoff links plaquette term) := by
  unfold globalAnchorFaceFeaturePolynomial
  exact supportedCoordinates_substitute
    (faceToGlobalLinkSubstitution_supported links plaquette)
    (anchorFaceHolonomyFeaturePolynomial cutoff term)

/-! ## 3. Lazy factor-list support -/

/-- Every raw polynomial in a lazy factor list obeys one common coordinate
bound. -/
def SupportedRatPolyFactors
    (coordinateCount : Nat) (factors : List RatPoly) : Prop :=
  ∀ polynomial, polynomial ∈ factors →
    SupportedCoordinates coordinateCount polynomial

theorem supportedRatPolyFactors_nil (coordinateCount : Nat) :
    SupportedRatPolyFactors coordinateCount [] := by
  intro polynomial hpolynomial
  simp only [List.not_mem_nil] at hpolynomial

theorem supportedRatPolyFactors_cons
    {coordinateCount : Nat} {polynomial : RatPoly} {factors : List RatPoly}
    (hpolynomial : SupportedCoordinates coordinateCount polynomial)
    (hfactors : SupportedRatPolyFactors coordinateCount factors) :
    SupportedRatPolyFactors coordinateCount (polynomial :: factors) := by
  intro source hsource
  simp only [List.mem_cons] at hsource
  cases hsource with
  | inl hsource => simpa only [hsource] using hpolynomial
  | inr hsource => exact hfactors source hsource

theorem supportedRatPolyFactors_append
    {coordinateCount : Nat} {left right : List RatPoly}
    (hleft : SupportedRatPolyFactors coordinateCount left)
    (hright : SupportedRatPolyFactors coordinateCount right) :
    SupportedRatPolyFactors coordinateCount (left ++ right) := by
  intro polynomial hpolynomial
  simp only [List.mem_append] at hpolynomial
  cases hpolynomial with
  | inl hpolynomial => exact hleft polynomial hpolynomial
  | inr hpolynomial => exact hright polynomial hpolynomial

/-- Uniform coordinate support for every selected feature-factor list of a
lazy SOS packet. -/
def LazyPacketSupported
    {Input : Type u} {environment : Input → Nat → Q'}
    (coordinateCount : Nat)
    (packet : LazyRatPolySOSFeatures Input environment) : Prop :=
  ∀ term, SupportedRatPolyFactors coordinateCount (packet.factors term)

theorem lazyPacketSupported_one
    (Input : Type u) (environment : Input → Nat → Q')
    (coordinateCount : Nat) :
    LazyPacketSupported coordinateCount
      (LazyRatPolySOSFeatures.one Input environment) := by
  intro term
  exact supportedRatPolyFactors_nil coordinateCount

theorem lazyPacketSupported_multiply
    {Input : Type u} {environment : Input → Nat → Q'}
    {coordinateCount : Nat}
    {left right : LazyRatPolySOSFeatures Input environment}
    (hleft : LazyPacketSupported coordinateCount left)
    (hright : LazyPacketSupported coordinateCount right) :
    LazyPacketSupported coordinateCount
      (LazyRatPolySOSFeatures.multiply left right) := by
  intro packed
  exact supportedRatPolyFactors_append
    (hleft (packed / right.data.termCount))
    (hright (packed % right.data.termCount))

theorem lazyPacketSupported_multiplyList
    {Input : Type u} {environment : Input → Nat → Q'}
    {coordinateCount : Nat} :
    ∀ packets : List (LazyRatPolySOSFeatures Input environment),
      (∀ packet, packet ∈ packets → LazyPacketSupported coordinateCount packet) →
      LazyPacketSupported coordinateCount
        (LazyRatPolySOSFeatures.multiplyList packets)
  | [], _ => lazyPacketSupported_one Input environment coordinateCount
  | head :: tail, hpackets =>
      lazyPacketSupported_multiply
        (hpackets head List.mem_cons_self)
        (lazyPacketSupported_multiplyList tail
          (fun packet hpacket =>
            hpackets packet (List.mem_cons_of_mem head hpacket)))

/-- Every singleton factor of one lazy face packet has the exact common
shared-link support. -/
theorem globalAnchorFaceLazyPacket_supported
    (cutoff : Nat) (links : List Z4Link) (plaquette : Z4Plaq)
    (hsupport : ∀ link, link ∈ edgesOf plaquette → link ∈ links) :
    LazyPacketSupported (linkQuaternionCoordinateCount links)
      (globalAnchorFaceLazyPacket cutoff links plaquette hsupport) := by
  intro term
  apply supportedRatPolyFactors_cons
  · exact globalAnchorFaceFeaturePolynomial_supported
      cutoff links plaquette term
  · exact supportedRatPolyFactors_nil _

theorem globalAnchorFaceLazyPackets_supported
    (cutoff : Nat) (links : List Z4Link) :
    ∀ (plaquettes : List Z4Plaq)
      (hsupport : ∀ plaquette, plaquette ∈ plaquettes →
        ∀ link, link ∈ edgesOf plaquette → link ∈ links)
      (packet : LazyRatPolySOSFeatures RationalUnitQuaternionGaugeField
        (fun field => globalLinkEnvironment links field)),
      packet ∈ globalAnchorFaceLazyPackets cutoff links plaquettes hsupport →
        LazyPacketSupported (linkQuaternionCoordinateCount links) packet
  | [], _, packet, hpacket => by
      simp only [globalAnchorFaceLazyPackets, List.not_mem_nil] at hpacket
  | plaquette :: tail, hsupport, packet, hpacket => by
      simp only [globalAnchorFaceLazyPackets, List.mem_cons] at hpacket
      cases hpacket with
      | inl hpacket =>
          subst packet
          exact globalAnchorFaceLazyPacket_supported cutoff links plaquette
            (fun link hlink =>
              hsupport plaquette List.mem_cons_self link hlink)
      | inr hpacket =>
          exact globalAnchorFaceLazyPackets_supported cutoff links tail
            (fun source hsource link hlink =>
              hsupport source (List.mem_cons_of_mem plaquette hsource)
                link hlink)
            packet hpacket

/-- The full lazy density packet carries the exact common coordinate support
without expanding any product of face polynomials. -/
theorem globalAnchorFaceLazyDensityPacket_supported
    (cutoff : Nat) (links : List Z4Link) (plaquettes : List Z4Plaq)
    (hsupport : ∀ plaquette, plaquette ∈ plaquettes →
      ∀ link, link ∈ edgesOf plaquette → link ∈ links) :
    LazyPacketSupported (linkQuaternionCoordinateCount links)
      (globalAnchorFaceLazyDensityPacket
        cutoff links plaquettes hsupport) := by
  unfold globalAnchorFaceLazyDensityPacket
  apply lazyPacketSupported_multiplyList
  intro packet hpacket
  exact globalAnchorFaceLazyPackets_supported
    cutoff links plaquettes hsupport packet hpacket

/-! ## 4. Production adjacent-even support certificates -/

/-- A selected feature of any adjacent-even fixed face, including an
out-of-range face id or term index, remains in the exact active coordinate
carrier. -/
def adjacentEvenFixedFaceGlobalFeaturePolynomial
    (cutoff radius id term : Nat) : RatPoly :=
  globalAnchorFaceFeaturePolynomial cutoff
    (adjacentEvenActiveLinks radius)
    (slabPlaquetteAt (adjacentEvenExtent radius) id) term

theorem adjacentEvenFixedFaceGlobalFeaturePolynomial_supported
    (cutoff radius id term : Nat) :
    SupportedCoordinates (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenFixedFaceGlobalFeaturePolynomial
        cutoff radius id term) := by
  change
    SupportedCoordinates
      (linkQuaternionCoordinateCount (adjacentEvenActiveLinks radius))
      (globalAnchorFaceFeaturePolynomial cutoff
        (adjacentEvenActiveLinks radius)
        (slabPlaquetteAt (adjacentEvenExtent radius) id) term)
  exact globalAnchorFaceFeaturePolynomial_supported _ _ _ _

/-- The already-exposed full fixed-face polynomial has the same exact active
coordinate support. -/
theorem adjacentEvenFixedFaceGlobalPolynomial_supported
    (cutoff radius id : Nat) :
    SupportedCoordinates (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenFixedFaceGlobalPolynomial cutoff radius id) := by
  change
    SupportedCoordinates
      (linkQuaternionCoordinateCount (adjacentEvenActiveLinks radius))
      (globalAnchorFacePolynomial cutoff
        (adjacentEvenActiveLinks radius)
        (slabPlaquetteAt (adjacentEvenExtent radius) id))
  exact globalAnchorFacePolynomial_supported _ _ _

/-- Every symbolic full-face polynomial factor in the production list obeys
the exact active-coordinate bound. -/
theorem adjacentEvenFixedFaceGlobalPolynomialFactors_supported
    (cutoff radius : Nat) :
    SupportedRatPolyFactors (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenFixedFaceGlobalPolynomialFactors cutoff radius) := by
  intro polynomial hpolynomial
  unfold adjacentEvenFixedFaceGlobalPolynomialFactors at hpolynomial
  rw [List.mem_map] at hpolynomial
  obtain ⟨id, _, rfl⟩ := hpolynomial
  exact adjacentEvenFixedFaceGlobalPolynomial_supported cutoff radius id

/-- Every selected factor list in the complete adjacent-even lazy density
packet is supported in the production active-link carrier. -/
theorem adjacentEvenFixedFaceLazyDensityPacket_supported
    (cutoff radius : Nat) :
    LazyPacketSupported (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenFixedFaceLazyDensityPacket cutoff radius) := by
  change
    LazyPacketSupported
      (linkQuaternionCoordinateCount (adjacentEvenActiveLinks radius))
      (globalAnchorFaceLazyDensityPacket cutoff
        (adjacentEvenActiveLinks radius)
        (adjacentEvenFixedFacePlaquettes radius)
        (fun _ hplaquette _ hlink =>
          adjacentEvenFixedFacePlaquette_edge_mem_activeLinks
            hplaquette hlink))
  exact globalAnchorFaceLazyDensityPacket_supported cutoff
    (adjacentEvenActiveLinks radius)
    (adjacentEvenFixedFacePlaquettes radius)
    (fun _ hplaquette _ hlink =>
      adjacentEvenFixedFacePlaquette_edge_mem_activeLinks hplaquette hlink)

#print axioms supportedCoordinates_substitute
#print axioms globalLinkCoordinatePolynomial_supported
#print axioms faceToGlobalLinkSubstitution_supported
#print axioms globalAnchorFacePolynomial_supported
#print axioms globalAnchorFaceFeaturePolynomial_supported
#print axioms globalAnchorFaceLazyDensityPacket_supported
#print axioms adjacentEvenFixedFaceGlobalFeaturePolynomial_supported
#print axioms adjacentEvenFixedFaceGlobalPolynomialFactors_supported
#print axioms adjacentEvenFixedFaceLazyDensityPacket_supported

end YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
