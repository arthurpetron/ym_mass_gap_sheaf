/-
# Actual all-link vertex Gauss action on physical oriented links

The sum below differentiates the ORIGINAL coordinate polynomials, once per
physical carrier link. Index injectivity and the constructive carrier Nodup
proof isolate the contributing link. Left/right coordinate laws are applied
only AFTER the actual derivatives have been formed. Reverse orientation swaps
the endpoint contributions with their literal signs; no sphere equation,
unit-quaternion hypothesis or differentiation of padded equivalences is used.

The ordered closed-word telescope is a downstream consumer of this endpoint
law. No continuum generator/domain, signed Ward estimate or gap is asserted.
-/

import YMGap.Continuum.SU2QuaternionLeftRightAngularAction
import YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord

namespace YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionLeftRightAngularAction
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.QuaternionHaarAngularCarrier

local notation:max "SlabB" extent:arg => List.length (boundaryCompleteSlabLinks extent)
attribute [local irreducible] boundaryCompleteSlabLinks

/-- Literal contribution of one original carrier link. -/
def linkGauss (extent : Nat) (v : Z4Vertex) (i : Fin 3) (link : Z4Link)
    (p : RatPoly) : RatPoly :=
  polyAdd
    (if v = link.1 then
      polyNeg (frameDerivativeAt false ((boundaryCompleteSlabLinks extent).idxOf link) i p)
     else polyZero)
    (if v = addE link.1 link.2 then
      frameDerivativeAt true ((boundaryCompleteSlabLinks extent).idxOf link) i p
     else polyZero)

/-- The actual finite vertex generator, on the SAME boundary-complete carrier. -/
def vertexGauss (extent : Nat) (v : Z4Vertex) (i : Fin 3) (p : RatPoly) : RatPoly :=
  finitePolySum (fun link => linkGauss extent v i link p) (boundaryCompleteSlabLinks extent)

/-- Componentwise actual derivative, not an assigned symbolic endpoint tangent. -/
def vertexGaussQuaternion (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (q : PolyQuaternion) : PolyQuaternion :=
  ⟨vertexGauss extent v i q.scalar, vertexGauss extent v i q.iPart,
    vertexGauss extent v i q.jPart, vertexGauss extent v i q.kPart⟩

private def addQuaternion (p q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyAdd p.scalar q.scalar, polyAdd p.iPart q.iPart,
    polyAdd p.jPart q.jPart, polyAdd p.kPart q.kPart⟩

private theorem padded_neg {B : Nat} {p q : RatPoly}
    (h : PaddedPolynomialCoeffEqv B p q) :
    PaddedPolynomialCoeffEqv B (polyNeg p) (polyNeg q) :=
  (PaddedPolynomialCoeffEqv.of_coeff (blocks := B) (neg_smul p)).trans
    ((h.smul (-1)).trans (PaddedPolynomialCoeffEqv.of_coeff (neg_smul q).symm))

private theorem padded_add_quaternion {B : Nat} {p p' q q' : PolyQuaternion}
    (hp : PaddedQuaternionCoeffEqv B p p') (hq : PaddedQuaternionCoeffEqv B q q') :
    PaddedQuaternionCoeffEqv B (addQuaternion p q) (addQuaternion p' q') :=
  ⟨PaddedPolynomialCoeffEqv.add hp.scalar hq.scalar,
    PaddedPolynomialCoeffEqv.add hp.iPart hq.iPart,
    PaddedPolynomialCoeffEqv.add hp.jPart hq.jPart,
    PaddedPolynomialCoeffEqv.add hp.kPart hq.kPart⟩

private theorem padded_neg_quaternion {B : Nat} {p q : PolyQuaternion}
    (h : PaddedQuaternionCoeffEqv B p q) :
    PaddedQuaternionCoeffEqv B (negQuaternion p) (negQuaternion q) :=
  ⟨padded_neg h.scalar, padded_neg h.iPart, padded_neg h.jPart, padded_neg h.kPart⟩

private theorem neg_zero : RatPolyCoeffEqv (polyNeg polyZero) polyZero := .refl _

private theorem neg_neg (p : RatPoly) : RatPolyCoeffEqv (polyNeg (polyNeg p)) p :=
  coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0)
    (by decide) (fun _ => p)

private theorem double_neg_quaternion (q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (negQuaternion (negQuaternion q)) q :=
  ⟨neg_neg q.scalar, neg_neg q.iPart, neg_neg q.jPart, neg_neg q.kPart⟩

private theorem add_comm_quaternion (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (addQuaternion p q) (addQuaternion q p) :=
  ⟨RatPolyCoeffEqv.add_comm _ _, RatPolyCoeffEqv.add_comm _ _,
    RatPolyCoeffEqv.add_comm _ _, RatPolyCoeffEqv.add_comm _ _⟩

private theorem sum_zero {B : Nat} (f : Z4Link → RatPoly) :
    ∀ links : List Z4Link,
      (∀ link, link ∈ links → PaddedPolynomialCoeffEqv B (f link) polyZero) →
      PaddedPolynomialCoeffEqv B (finitePolySum f links) polyZero
  | [], _ => .refl _ _
  | link :: links, h =>
      ((h link List.mem_cons_self).add
        (sum_zero f links (fun e he => h e (List.mem_cons_of_mem link he)))).trans
          (.of_coeff (RatPolyCoeffEqv.zero_add polyZero))

/-- A local finite-sum isolation proof; its zero inputs will be produced by
the actual other-coordinate action below, never supplied as source laws. -/
private theorem sum_single {B : Nat} (f : Z4Link → RatPoly) (target : Z4Link) :
    ∀ links : List Z4Link, links.Nodup →
      (∀ link, link ∈ links → link ≠ target →
        PaddedPolynomialCoeffEqv B (f link) polyZero) →
      PaddedPolynomialCoeffEqv B (finitePolySum f links)
        (if target ∈ links then f target else polyZero)
  | [], _, _ => by simp only [List.not_mem_nil, if_false, finitePolySum]; exact .refl _ _
  | link :: links, hn, hz => by
      have htail : links.Nodup := (List.nodup_cons.mp hn).2
      by_cases he : link = target
      · subst link
        have hnot : target ∉ links := (List.nodup_cons.mp hn).1
        have ht := sum_zero f links (fun e hm => hz e (List.mem_cons_of_mem target hm)
          (fun heq => hnot (heq ▸ hm)))
        rw [if_pos List.mem_cons_self]
        exact ((PaddedPolynomialCoeffEqv.refl B (f target)).add ht).trans
          (.of_coeff (RatPolyCoeffEqv.add_zero _))
      · have hh := hz link List.mem_cons_self he
        have ht := sum_single f target links htail
          (fun e hm hne => hz e (List.mem_cons_of_mem link hm) hne)
        have hm : (target ∈ link :: links) ↔ target ∈ links := by
          simp only [List.mem_cons]
          constructor
          · intro h; cases h with
            | inl h => exact False.elim (he h.symm)
            | inr h => exact h
          · intro h; exact Or.inr h
        simpa only [hm, finitePolySum] using
          (hh.add ht).trans (.of_coeff (RatPolyCoeffEqv.zero_add _))

/-- Other physical links genuinely have different actual coordinate indices. -/
private theorem physical_frame_other {extent : Nat} (right : Bool) (i : Fin 3)
    (e : OrientedBF4Link) (he : e.link ∈ boundaryCompleteSlabLinks extent)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent) (hne : link ≠ e.link) :
    PaddedQuaternionCoeffEqv (SlabB extent)
      (quaternionAction right ((boundaryCompleteSlabLinks extent).idxOf link) i
        (orientedCorrectedSlabLinkPolynomial extent e)) zeroQuaternion := by
  have hi : (boundaryCompleteSlabLinks extent).idxOf link ≠
      (boundaryCompleteSlabLinks extent).idxOf e.link :=
    fun h => hne (idxOf_injective_on_members hl he h)
  unfold orientedCorrectedSlabLinkPolynomial
  rw [correctedSlabLinkPolynomial_of_mem he]
  cases hr : e.reverse
  · exact other_coordinate_action right (List.idxOf_lt_length_of_mem hl)
      (List.idxOf_lt_length_of_mem he) hi i
  · exact other_conjugate_coordinate_action right (List.idxOf_lt_length_of_mem hl)
      (List.idxOf_lt_length_of_mem he) hi i

private def localQuaternion (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (link : Z4Link) (q : PolyQuaternion) : PolyQuaternion :=
  addQuaternion
    (if v = link.1 then
      negQuaternion (quaternionAction false ((boundaryCompleteSlabLinks extent).idxOf link) i q)
     else zeroQuaternion)
    (if v = addE link.1 link.2 then
      quaternionAction true ((boundaryCompleteSlabLinks extent).idxOf link) i q
     else zeroQuaternion)

private theorem localQuaternion_components (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (link : Z4Link) (q : PolyQuaternion) :
    localQuaternion extent v i link q =
      ⟨linkGauss extent v i link q.scalar, linkGauss extent v i link q.iPart,
        linkGauss extent v i link q.jPart, linkGauss extent v i link q.kPart⟩ := by
  unfold localQuaternion linkGauss
  split <;> split <;> rfl

private theorem local_other {extent : Nat} (v : Z4Vertex) (i : Fin 3)
    (e : OrientedBF4Link) (he : e.link ∈ boundaryCompleteSlabLinks extent)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent) (hne : link ≠ e.link) :
    PaddedQuaternionCoeffEqv (SlabB extent)
      (localQuaternion extent v i link (orientedCorrectedSlabLinkPolynomial extent e))
      zeroQuaternion := by
  have hL := physical_frame_other false i e he link hl hne
  have hR := physical_frame_other true i e he link hl hne
  have hN : PaddedQuaternionCoeffEqv (SlabB extent) (negQuaternion zeroQuaternion) zeroQuaternion :=
    .of_coeff ⟨neg_zero, neg_zero, neg_zero, neg_zero⟩
  have hZ : PaddedQuaternionCoeffEqv (SlabB extent)
      (addQuaternion zeroQuaternion zeroQuaternion) zeroQuaternion :=
    .of_coeff ⟨RatPolyCoeffEqv.zero_add _, RatPolyCoeffEqv.zero_add _,
      RatPolyCoeffEqv.zero_add _, RatPolyCoeffEqv.zero_add _⟩
  unfold localQuaternion
  split <;> split
  · exact (padded_add_quaternion ((padded_neg_quaternion hL).trans hN) hR).trans hZ
  · exact (padded_add_quaternion ((padded_neg_quaternion hL).trans hN) (.refl _ _)).trans hZ
  · exact (padded_add_quaternion (.refl _ _) hR).trans hZ
  · exact hZ

/-- The actual full-carrier sum isolates the physical oriented occurrence.
Carrier links are summed once; word occurrences are not deduplicated. -/
theorem physical_link_local (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (e : OrientedBF4Link) (he : e.link ∈ boundaryCompleteSlabLinks extent) :
    PaddedQuaternionCoeffEqv (SlabB extent)
      (vertexGaussQuaternion extent v i (orientedCorrectedSlabLinkPolynomial extent e))
      (localQuaternion extent v i e.link (orientedCorrectedSlabLinkPolynomial extent e)) := by
  let q := orientedCorrectedSlabLinkPolynomial extent e
  have h (p : RatPoly)
      (hz : ∀ link, link ∈ boundaryCompleteSlabLinks extent → link ≠ e.link →
        PaddedPolynomialCoeffEqv (SlabB extent) (linkGauss extent v i link p) polyZero) :
      PaddedPolynomialCoeffEqv (SlabB extent) (vertexGauss extent v i p)
        (linkGauss extent v i e.link p) := by
    have hs := sum_single (fun link => linkGauss extent v i link p) e.link
      (boundaryCompleteSlabLinks extent) (boundaryCompleteSlabLinks_nodup extent) hz
    simpa only [vertexGauss, if_pos he] using hs
  have hz := local_other v i e he
  have hz' (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent) (hne : link ≠ e.link) :=
    hz link hl hne
  rw [localQuaternion_components]
  refine ⟨h q.scalar ?_, h q.iPart ?_, h q.jPart ?_, h q.kPart ?_⟩
  · intro link hl hne; have h0 := hz' link hl hne
    rw [localQuaternion_components] at h0; exact h0.scalar
  · intro link hl hne; have h0 := hz' link hl hne
    rw [localQuaternion_components] at h0; exact h0.iPart
  · intro link hl hne; have h0 := hz' link hl hne
    rw [localQuaternion_components] at h0; exact h0.jPart
  · intro link hl hne; have h0 := hz' link hl hne
    rw [localQuaternion_components] at h0; exact h0.kPart

/-- Literal oriented endpoint law, with all reverse signs retained. -/
def endpointQuaternion (v : Z4Vertex) (i : Fin 3) (e : OrientedBF4Link)
    (q : PolyQuaternion) : PolyQuaternion :=
  addQuaternion
    (if v = entryStart e then negQuaternion (PolyQuaternion.mul (imaginaryBasis i) q)
     else zeroQuaternion)
    (if v = entryFinish e then PolyQuaternion.mul q (imaginaryBasis i)
     else zeroQuaternion)

/-- The original Gauss sum acts as minus-left at the ORIENTED start and
plus-right at the ORIENTED finish, without a unit/sphere assumption. -/
theorem oriented_link_endpoint (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (e : OrientedBF4Link) (he : e.link ∈ boundaryCompleteSlabLinks extent) :
    PaddedQuaternionCoeffEqv (SlabB extent)
      (vertexGaussQuaternion extent v i (orientedCorrectedSlabLinkPolynomial extent e))
      (endpointQuaternion v i e (orientedCorrectedSlabLinkPolynomial extent e)) := by
  apply (physical_link_local extent v i e he).trans
  have hb := List.idxOf_lt_length_of_mem he
  unfold localQuaternion endpointQuaternion entryStart entryFinish orientedCorrectedSlabLinkPolynomial
  rw [correctedSlabLinkPolynomial_of_mem he]
  cases hr : e.reverse
  · simp only [Bool.false_eq_true, if_false]
    have hL := coordinate_action false hb i
    have hR := coordinate_action true hb i
    split <;> split
    · exact padded_add_quaternion (padded_neg_quaternion hL) hR
    · exact padded_add_quaternion (padded_neg_quaternion hL) (.refl _ _)
    · exact padded_add_quaternion (.refl _ _) hR
    · exact .refl _ _
  · simp only [if_true]
    have hL := (padded_neg_quaternion (conjugate_coordinate_action false hb i)).trans
      (.of_coeff (double_neg_quaternion _))
    have hR := conjugate_coordinate_action true hb i
    by_cases hs : v = e.link.1 <;> by_cases ht : v = addE e.link.1 e.link.2
    · simp only [if_pos hs, if_pos ht]
      exact (padded_add_quaternion hL hR).trans (.of_coeff (add_comm_quaternion _ _))
    · simp only [if_pos hs, if_neg ht]
      exact (padded_add_quaternion hL (.refl _ _)).trans (.of_coeff (add_comm_quaternion _ _))
    · simp only [if_neg hs, if_pos ht]
      exact (padded_add_quaternion (.refl _ _) hR).trans (.of_coeff (add_comm_quaternion _ _))
    · simp only [if_neg hs, if_neg ht]; exact .refl _ _

end YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord

#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord.linkGauss
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord.vertexGauss
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord.vertexGaussQuaternion
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord.physical_link_local
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord.endpointQuaternion
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord.oriented_link_endpoint
