/-
# Fixed-cutoff block degree of the ORIGINAL spatial action

Every original spatial heat factor has degree at most K in a selected
quaternion block, and has degree zero when its literal face omits that link.
At most six distinct original spatial faces meet a physical link. The
complete original spatial product therefore has degree at most 6*K in every
source block. This is a syntactic finite-cutoff statement only; it gives no
coefficient-size, term-count, runtime, scaling, or margin estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticDegree
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDegree

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Link Z4Plaq edgesOf)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
  (characterPolynomial PolyQuaternion OrientedBF4Link orientedPlaquetteBoundary)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (link orientedLink plaquette spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
  (heatFace_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree (plaquette_degree)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound
  (spatialIncidentFaces spatialIncidentFaces_length_le_six)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
  (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
  (orientedPlaquetteBoundary_link_mem_edgesOf)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
  (independent_of_local)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
  (HasQuaternionBlockDegree HasPolyQuaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionBlockDegreeBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticDegree
  (characterPolynomial_degree_le)

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem exact_degree_le {block d : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree block d p) : DegreeLE block d p :=
  fun term ht => Nat.le_of_eq (hp term ht)

private structure LocalQuaternion (blocks : Nat) (allowed : Nat → Prop)
    (q : PolyQuaternion) : Prop where
  scalar : BlockLocal blocks allowed q.scalar
  iPart : BlockLocal blocks allowed q.iPart
  jPart : BlockLocal blocks allowed q.jPart
  kPart : BlockLocal blocks allowed q.kPart

private theorem local_one (blocks : Nat) (allowed : Nat → Prop) :
    LocalQuaternion blocks allowed PolyQuaternion.one :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _, BlockLocal.zero _ _, BlockLocal.zero _ _⟩

private theorem LocalQuaternion.conj {blocks : Nat} {allowed : Nat → Prop}
    {p : PolyQuaternion} (hp : LocalQuaternion blocks allowed p) :
    LocalQuaternion blocks allowed (PolyQuaternion.conj p) :=
  ⟨hp.scalar, hp.iPart.neg, hp.jPart.neg, hp.kPart.neg⟩

private theorem LocalQuaternion.mul {blocks : Nat} {allowed : Nat → Prop}
    {p q : PolyQuaternion} (hp : LocalQuaternion blocks allowed p)
    (hq : LocalQuaternion blocks allowed q) :
    LocalQuaternion blocks allowed (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply BlockLocal.add | apply BlockLocal.neg | apply BlockLocal.mul

private theorem link_local (width i : Nat) (selected : Z4Link)
    (hselected : selected ∈ baseLinks width →
      (baseLinks width).idxOf selected ≠ i) :
    LocalQuaternion (N width) (fun b => b ≠ i) (link width selected) := by
  by_cases hm : selected ∈ baseLinks width
  · have hc (c : Nat) (h : c < 4) :
        BlockLocal (N width) (fun b => b ≠ i)
          (polyVar (4*(baseLinks width).idxOf selected+c)) := by
      apply BlockLocal.coordinate
      rw [show (4*(baseLinks width).idxOf selected+c)/4 =
        (baseLinks width).idxOf selected by omega]
      exact hselected hm
    rw [link, if_pos hm]
    exact ⟨hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)⟩
  · rw [link, if_neg hm]
    exact local_one _ _

private theorem oriented_local (width i : Nat) (entry : OrientedBF4Link)
    (hentry : entry.link ∈ baseLinks width →
      (baseLinks width).idxOf entry.link ≠ i) :
    LocalQuaternion (N width) (fun b => b ≠ i) (orientedLink width entry) := by
  unfold orientedLink
  split
  · exact (link_local width i entry.link hentry).conj
  · exact link_local width i entry.link hentry

private theorem word_local (width i : Nat) :
    ∀ (word : List OrientedBF4Link),
    (∀ entry, entry ∈ word → entry.link ∈ baseLinks width →
      (baseLinks width).idxOf entry.link ≠ i) →
    ∀ p, LocalQuaternion (N width) (fun b => b ≠ i) p →
      LocalQuaternion (N width) (fun b => b ≠ i)
        (word.foldl (fun q entry => PolyQuaternion.mul q
          (orientedLink width entry)) p)
  | [], _, _, hp => hp
  | entry :: rest, hnot, _, hp =>
      word_local width i rest
        (fun other hmem => hnot other (List.mem_cons_of_mem entry hmem)) _
        (hp.mul (oriented_local width i entry (hnot entry List.mem_cons_self)) )

private theorem plaquette_scalar_independent_index (width : Nat)
    (face : Z4Plaq) (i : Nat) (hi : i < N width)
    (hnot : ∀ selected, selected ∈ edgesOf face →
      selected ∈ baseLinks width →
      (baseLinks width).idxOf selected ≠ i) :
    QuaternionBlockIndependent i (plaquette width face).scalar := by
  have hp := word_local width i (orientedPlaquetteBoundary face)
    (fun entry he => hnot entry.link
      (orientedPlaquetteBoundary_link_mem_edgesOf he))
    PolyQuaternion.one (local_one _ _)
  exact independent_of_local hp.scalar hi (fun h => h rfl)

/-- The actual scalar plaquette word has block degree at most one in every
original spatial block, whether or not that block meets the face. -/
theorem plaquetteScalar_degree (width : Nat) (face : Z4Plaq)
    (i : Nat) (hi : i < N width) (hf : face ∈ spatialFaces width) :
    DegreeLE i 1 (plaquette width face).scalar := by
  let selected : Z4Link := (baseLinks width)[i]
  have hselected : selected ∈ baseLinks width := List.getElem_mem hi
  have hget : (baseLinks width)[(baseLinks width).idxOf selected]'
      (List.idxOf_lt_length_of_mem hselected) = selected :=
    LawfulBEq.eq_of_beq
      (List.findIdx_getElem (w := List.idxOf_lt_length_of_mem hselected))
  have hindex : (baseLinks width).idxOf selected = i :=
    List.getElem?_inj (List.idxOf_lt_length_of_mem hselected)
      (YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.baseLinks_nodup width)
      (by rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hselected),
        List.getElem?_eq_getElem hi]; exact congrArg some hget)
  by_cases hface : selected ∈ edgesOf face
  · have hdegree := exact_degree_le (plaquette_degree width hf hface).scalar
    simpa only [hindex] using hdegree
  · apply (DegreeLE.of_independent ?_).mono (Nat.zero_le 1)
    apply plaquette_scalar_independent_index width face i hi
    intro other hedge hcarrier hidx
    have heq : (baseLinks width).idxOf other =
        (baseLinks width).idxOf selected := hidx.trans hindex.symm
    have hselectedEq := idxOf_injective_on_members hcarrier hselected heq
    subst other
    exact hface hedge

/-- Every character of the actual plaquette scalar has its spin-bounded
degree ceiling in every original spatial block. -/
theorem plaquetteCharacter_degree (width : Nat) (face : Z4Plaq)
    (i : Nat) (hi : i < N width) (hf : face ∈ spatialFaces width)
    (spin : Nat) :
    DegreeLE i spin (characterPolynomial (plaquette width face).scalar spin) :=
  characterPolynomial_degree_le i _
    (plaquetteScalar_degree width face i hi hf) spin

private theorem finitePolySum_degree_le {A : Type} (block d : Nat)
    (f : A → RatPoly) : ∀ xs : List A,
      (∀ x, x ∈ xs → DegreeLE block d (f x)) →
      DegreeLE block d (finitePolySum f xs)
  | [], _ => by
      intro term hterm
      exact False.elim (List.not_mem_nil hterm)
  | x :: xs, h => by
      change DegreeLE block d (polyAdd (f x) (finitePolySum f xs))
      exact (h x List.mem_cons_self).add
        (finitePolySum_degree_le block d f xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem heatFace_degree_le (w : Q') (K width : Nat) (face : Z4Plaq)
    (i : Nat)
    (hi : i < N width) (hf : face ∈ spatialFaces width) :
    DegreeLE i K (heatPrefix w K (plaquette width face).scalar) := by
  unfold heatPrefix
  apply finitePolySum_degree_le
  intro spin hspin
  have hspinLe : spin ≤ K := by
    have h := List.mem_range.mp hspin
    omega
  exact ((plaquetteCharacter_degree width face i hi hf spin).smul
    (coeffW w spin)).mono hspinLe

private theorem incidentFilter_length_cons (selected : Z4Link)
    (face : Z4Plaq) (faces : List Z4Plaq) :
    ((face :: faces).filter fun p => decide (selected ∈ edgesOf p)).length =
      (if selected ∈ edgesOf face then 1 else 0) +
        (faces.filter fun p => decide (selected ∈ edgesOf p)).length := by
  by_cases h : selected ∈ edgesOf face <;> simp [h, Nat.add_comm]

private theorem spatialProduct_link_degree (w : Q') (K width : Nat)
    {selected : Z4Link} (hselected : selected ∈ baseLinks width) :
    ∀ faces : List Z4Plaq,
      (∀ face, face ∈ faces → face ∈ spatialFaces width) →
      DegreeLE ((baseLinks width).idxOf selected)
        (((faces.filter fun face => decide (selected ∈ edgesOf face)).length)*K)
        (polynomialProduct (fun face =>
          heatPrefix w K (plaquette width face).scalar) faces)
  | [], _ => by
      simp only [List.filter_nil, List.length_nil, polynomialProduct]
      simpa using (DegreeLE.one ((baseLinks width).idxOf selected) 0)
  | face :: faces, hfaces => by
      have hface : face ∈ spatialFaces width := hfaces face List.mem_cons_self
      have htail : ∀ f, f ∈ faces → f ∈ spatialFaces width := by
        intro f hf
        exact hfaces f (List.mem_cons_of_mem face hf)
      have htailDegree := spatialProduct_link_degree w K width hselected faces htail
      change DegreeLE ((baseLinks width).idxOf selected)
        (((face :: faces).filter fun p => decide (selected ∈ edgesOf p)).length*K)
        (polyMul (heatPrefix w K (plaquette width face).scalar)
          (polynomialProduct (fun face =>
            heatPrefix w K (plaquette width face).scalar) faces))
      by_cases hincident : selected ∈ edgesOf face
      · have hfactor := heatFace_degree_le w K width face
          ((baseLinks width).idxOf selected) (List.idxOf_lt_length_of_mem hselected) hface
        have hmul := hfactor.mul htailDegree
        simpa only [incidentFilter_length_cons, if_pos hincident,
          Nat.add_mul, Nat.one_mul] using hmul
      · have hindependent := heatFace_independent w K hselected hincident
        have hfactor : DegreeLE ((baseLinks width).idxOf selected) 0
            (heatPrefix w K (plaquette width face).scalar) :=
          DegreeLE.of_independent hindependent
        have hmul := hfactor.mul htailDegree
        simpa only [incidentFilter_length_cons, if_neg hincident,
          Nat.zero_add, Nat.zero_mul] using hmul

/-- The actual original spatial product has degree at most 6*K in the
selected physical link block. Every literal face factor remains in order. -/
theorem spatialWeight_link_degree (w : Q') (K width : Nat)
    {selected : Z4Link} (hselected : selected ∈ baseLinks width) :
    DegreeLE ((baseLinks width).idxOf selected) (6*K)
      (spatialWeight w K width) := by
  unfold spatialWeight
  have h := spatialProduct_link_degree w K width hselected
    (spatialFaces width) (fun _ hf => hf)
  have hcount := spatialIncidentFaces_length_le_six width selected
  exact h.mono (by
    simpa only [spatialIncidentFaces] using Nat.mul_le_mul_right K hcount)

/-- At every original lower physical block, the complete actual spatial
weight has degree at most six times the retained spin cutoff. -/
theorem spatialWeight_degree (w : Q') (K width i : Nat)
    (hi : i < N width) :
    DegreeLE i (6*K) (spatialWeight w K width) := by
  let selected : Z4Link := (baseLinks width)[i]
  have hselected : selected ∈ baseLinks width := List.getElem_mem hi
  have hget : (baseLinks width)[(baseLinks width).idxOf selected]'
      (List.idxOf_lt_length_of_mem hselected) = selected :=
    LawfulBEq.eq_of_beq
      (List.findIdx_getElem (w := List.idxOf_lt_length_of_mem hselected))
  have hindex : (baseLinks width).idxOf selected = i :=
    List.getElem?_inj (List.idxOf_lt_length_of_mem hselected)
      (YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.baseLinks_nodup width)
      (by rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hselected),
        List.getElem?_eq_getElem hi]; exact congrArg some hget)
  simpa only [hindex] using spatialWeight_link_degree w K width hselected

#print axioms plaquetteScalar_degree
#print axioms plaquetteCharacter_degree
#print axioms spatialWeight_link_degree
#print axioms spatialWeight_degree

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDegree
