/-
# Explicit locality and placement-independent bounds for actual Wilson words

The literal ordered word has Haar-unit norm under every spectator insertion:
the existing norm-multiplication identity retains repeated and shared links.
Its scalar square bound therefore gives a constructed interval at arbitrary
spin. The cap depends only on spin, not on word length, carrier size, width,
time offset, coupling or heat cutoff. Signed expression caps retain only the
spins, rational coefficients and algebraic operations.

Locality is a separate syntactic theorem about actual original link lists.
No disjointness follows merely from the interval certificate. These are the
observable inputs to the existing finite box-boundary estimate, not an OS
quotient multiplier bound, full gauge-algebra coverage or continuum result.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality
import YMGap.Continuum.QuaternionHaarCharacterInterval
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.BF4ExactSlabSpatialWilsonControl

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (LinkLocal)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval

local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private structure LocalQuaternion (extent : Nat) (links : List Z4Link) (p : PolyQuaternion) : Prop where
  scalar : LinkLocal extent links p.scalar
  iPart : LinkLocal extent links p.iPart
  jPart : LinkLocal extent links p.jPart
  kPart : LinkLocal extent links p.kPart

private theorem local_one (extent : Nat) (links : List Z4Link) :
    LocalQuaternion extent links PolyQuaternion.one :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _, BlockLocal.zero _ _, BlockLocal.zero _ _⟩

private theorem LocalQuaternion.conj {extent : Nat} {links : List Z4Link} {p : PolyQuaternion}
    (hp : LocalQuaternion extent links p) : LocalQuaternion extent links (PolyQuaternion.conj p) :=
  ⟨hp.scalar, hp.iPart.neg, hp.jPart.neg, hp.kPart.neg⟩

private theorem LocalQuaternion.mul {extent : Nat} {links : List Z4Link} {p q : PolyQuaternion}
    (hp : LocalQuaternion extent links p) (hq : LocalQuaternion extent links q) :
    LocalQuaternion extent links (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply BlockLocal.add | apply BlockLocal.neg | apply BlockLocal.mul

private theorem local_link (extent : Nat) (links : List Z4Link) {link : Z4Link}
    (hl : link ∈ links) : LocalQuaternion extent links (correctedSlabLinkPolynomial extent link) := by
  by_cases hm : link ∈ boundaryCompleteSlabLinks extent
  · have hc (c : Nat) (h : c < 4) : LinkLocal extent links
        (polyVar (4*(boundaryCompleteSlabLinks extent).idxOf link+c)) := by
      apply BlockLocal.coordinate
      rw [show (4*(boundaryCompleteSlabLinks extent).idxOf link+c)/4 =
        (boundaryCompleteSlabLinks extent).idxOf link by omega, correctedSlabLinkAt_idxOf hm]
      exact hl
    rw [correctedSlabLinkPolynomial_of_mem hm]
    exact ⟨hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega)⟩
  · rw [correctedSlabLinkPolynomial_of_not_mem hm]
    exact local_one extent links

private theorem local_oriented (extent : Nat) (links : List Z4Link) (e : OrientedBF4Link)
    (he : e.link ∈ links) : LocalQuaternion extent links (orientedCorrectedSlabLinkPolynomial extent e) := by
  unfold orientedCorrectedSlabLinkPolynomial
  split
  · exact (local_link extent links he).conj
  · exact local_link extent links he

private theorem local_word (extent : Nat) (links : List Z4Link) :
    ∀ edges : List OrientedBF4Link, (∀ e, e ∈ edges → e.link ∈ links) →
    LocalQuaternion extent links (word extent edges)
  | [], _ => local_one extent links
  | e :: es, h => (local_oriented extent links e (h e List.mem_cons_self)).mul
      (local_word extent links es (fun f hf => h f (List.mem_cons_of_mem e hf)))

/-- Locality uses the actual allowed link list, not a polynomial-equivalence shortcut. -/
theorem word_scalar_local (extent : Nat) (links : List Z4Link)
    (edges : List OrientedBF4Link) (hlinks : ∀ e, e ∈ edges → e.link ∈ links) :
    LinkLocal extent links (word extent edges).scalar :=
  (local_word extent links edges hlinks).scalar

theorem character_local (extent : Nat) (links : List Z4Link)
    (edges : List OrientedBF4Link) (hlinks : ∀ e, e ∈ edges → e.link ∈ links) (spin : Nat) :
    LinkLocal extent links (character extent edges spin) :=
  (word_scalar_local extent links edges hlinks).character spin

/-- Ordered norm multiplicativity on the SAME Haar carrier, including shared links. -/
theorem word_unit (extent : Nat) :
    ∀ edges : List OrientedBF4Link,
    (∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent) →
    HaarCarrierEqv (B extent) (polyQuaternionNorm (word extent edges)) polyOne
  | [], _ => RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one
  | e :: es, h => haarNorm_mul (haarNorm_orientedSlabLink e (h e List.mem_cons_self))
      (word_unit extent es (fun f hf => h f (List.mem_cons_of_mem e hf)))

/-- A computed arbitrary-spin interval; no pointwise trace-bound premise is supplied. -/
def character_interval (extent : Nat) (edges : List OrientedBF4Link)
    (hphysical : ∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent) (spin : Nat) :
    Interval (B extent) (character extent edges spin) (2*(16 : Q')^spin) := by
  have hs := word_supported extent edges
  exact characterInterval (SquareBound.scalar (p := word extent edges)
    ⟨hs.scalar, hs.iPart, hs.jPart, hs.kPart⟩ (word_unit extent edges hphysical)) spin

/-- Only spins, signed coefficients and expression operations occur in this cap. -/
def windowCap {width : Nat} : WindowExpression width → Q'
  | .one => 1
  | .loop _ _ spin => 2*(16 : Q')^spin
  | .add e f => windowCap e + windowCap f
  | .mul e f => windowCap e * windowCap f
  | .smul c e => (c*c+1)*windowCap e

theorem windowCap_mapOffsets {width : Nat} (f : Nat → Nat) :
    ∀ e : WindowExpression width, windowCap (mapOffsets f e) = windowCap e
  | .one => rfl
  | .loop _ _ _ => rfl
  | .add e g => by
      change windowCap (mapOffsets f e) + windowCap (mapOffsets f g) = windowCap e + windowCap g
      rw [windowCap_mapOffsets f e, windowCap_mapOffsets f g]
  | .mul e g => by
      change windowCap (mapOffsets f e) * windowCap (mapOffsets f g) = windowCap e * windowCap g
      rw [windowCap_mapOffsets f e, windowCap_mapOffsets f g]
  | .smul c e => by
      change (c*c+1)*windowCap (mapOffsets f e) = (c*c+1)*windowCap e
      rw [windowCap_mapOffsets f e]

theorem windowCap_mirror {width : Nat} (h : Nat) (e : WindowExpression width) :
    windowCap (mirror h e) = windowCap e := windowCap_mapOffsets _ e

private def signed_interval {blocks : Nat} {p : RatPoly} {a : Q'}
    (P : Interval blocks p a) (c : Q') : Interval blocks (polySmul c p) ((c*c+1)*a) :=
  Interval.ofCoeff (supported_smul P.support c) (cap_mul_left c p).symm
    ((Interval.ofSquare (SquareBound.constant blocks c)).mul P)

/-- Both signs are certified on the literal original polynomial with its unchanged cap. -/
def placed_interval {width start L extent : Nat}
    (hw : width ≤ extent) (ht : start+L ≤ extent) :
    (e : WindowExpression width) → Within L e →
    Interval (B extent) (placedPolynomial extent start e) (windowCap e)
  | .one, _ => Interval.one _
  | .loop offset value spin, h =>
      character_interval extent _
        (placeLoop hw (show start+offset ≤ extent by
          have hoffset : offset ≤ L := h
          omega) value).physical spin
  | .add e f, h => (placed_interval hw ht e h.1).add (placed_interval hw ht f h.2)
  | .mul e f, h => (placed_interval hw ht e h.1).mul (placed_interval hw ht f h.2)
  | .smul c e, h => signed_interval (placed_interval hw ht e h) c

/-- The literal finite links of the placed expression; repetitions are harmless. -/
def placedLinks {width : Nat} (start : Nat) : WindowExpression width → List Z4Link
  | .one => []
  | .loop offset value _ => value.edges.map (fun e => timeShiftLink (start+offset) e.link)
  | .add e f => placedLinks start e ++ placedLinks start f
  | .mul e f => placedLinks start e ++ placedLinks start f
  | .smul _ e => placedLinks start e

theorem placed_local {width : Nat} (extent start : Nat) :
    ∀ e : WindowExpression width,
    LinkLocal extent (placedLinks start e) (placedPolynomial extent start e)
  | .one => BlockLocal.one _ _
  | .loop offset value spin => by
      apply character_local
      intro e he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      exact List.mem_map.mpr ⟨f, hf, rfl⟩
  | .add e f => BlockLocal.add
      ((placed_local extent start e).mono (fun _ hl => List.mem_append.mpr (Or.inl hl)))
      ((placed_local extent start f).mono (fun _ hl => List.mem_append.mpr (Or.inr hl)))
  | .mul e f => BlockLocal.mul
      ((placed_local extent start e).mono (fun _ hl => List.mem_append.mpr (Or.inl hl)))
      ((placed_local extent start f).mono (fun _ hl => List.mem_append.mpr (Or.inr hl)))
  | .smul c e => BlockLocal.smul (placed_local extent start e) c

/-- Feed a separately proved containing-box inclusion to the original LinkLocal consumer. -/
theorem placed_local_in {width : Nat} (extent start : Nat) (e : WindowExpression width)
    (links : List Z4Link) (hlinks : ∀ link, link ∈ placedLinks start e → link ∈ links) :
    LinkLocal extent links (placedPolynomial extent start e) :=
  (placed_local extent start e).mono hlinks

end YMGap.Continuum.BF4ExactSlabSpatialWilsonControl

#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.word_scalar_local
#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.character_local
#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.word_unit
#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.character_interval
#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.windowCap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.windowCap_mapOffsets
#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.windowCap_mirror
#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.placed_interval
#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.placedLinks
#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.placed_local
#print axioms YMGap.Continuum.BF4ExactSlabSpatialWilsonControl.placed_local_in
