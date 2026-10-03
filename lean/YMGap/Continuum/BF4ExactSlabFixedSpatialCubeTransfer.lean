/-
# The twelve-link cube is an exact tested restriction of the ORIGINAL transfer

At width two the fully active spatial action has exactly six cube faces.
The other twelve active kinetic links point out of this cube. Their full
heat factors integrate to one on cube-supported inputs, with every supported
output insertion retained. This proves the original T1 and TF identities
for the literal bent six-link loop, at EVERY rational nome and finite cutoff.

Equality is in the supported original-Haar quotient, not free polynomial
equality. The original slice carrier is retained. The seven weighted moments
are also proved equal to their cube representatives. No numerical moment
value, character-basis completeness, computed matrix pin, gain sign, cutoff
guard, completed or continuum theorem is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer
import YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
import YMGap.Continuum.SU2QuaternionProductHeatWilsonWord

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary (SliceLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
  (spatialFaces spatialFaces_mem_iff spatialFaces_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt activeBlocks_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_mem_iff fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
  (polynomialProduct polynomialProduct_perm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation (QuaternionSupported)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra (degree_zero_independent)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt word_independent)
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported character_independent)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)
open YMGap.Continuum.CayleyPruferInjection (nodup_map_of_injOn)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks activeBlocks activeSpatialWeight

/-- Cube faces in the pilot's order: (x,y), (x,z), (y,z), then the
opposite parallel face in each case. The plaquette words remain original. -/
def cubeFaces : List Z4Plaq :=
  [((0,0,0,0),.p01), ((0,0,1,0),.p01),
   ((0,0,0,0),.p02), ((0,1,0,0),.p02),
   ((0,0,0,0),.p12), ((1,0,0,0),.p12)]

/-- Twelve positively oriented links, in the pilot's vertex-major order
with x,y,z encoded by bits 1,2,4. -/
def cubeLinks : List Z4Link :=
  [((0,0,0,0),.x0), ((0,0,0,0),.x1), ((0,0,0,0),.x2),
   ((1,0,0,0),.x1), ((1,0,0,0),.x2),
   ((0,1,0,0),.x0), ((0,1,0,0),.x2), ((1,1,0,0),.x2),
   ((0,0,1,0),.x0), ((0,0,1,0),.x1),
   ((1,0,1,0),.x1), ((0,1,1,0),.x0)]

private theorem cubeLinks_strict (link : Z4Link) (hl : link ∈ cubeLinks) :
    StrictSliceLink 2 link := by
  simp only [cubeLinks, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem cubeLinks_in_carrier (link : Z4Link) (hl : link ∈ cubeLinks) :
    link ∈ baseLinks 2 := (baseLinks_mem_iff 2 link).mpr (cubeLinks_strict link hl).1

private theorem cubeFaces_edges (face : Z4Plaq) (hf : face ∈ cubeFaces)
    (link : Z4Link) (hl : link ∈ edgesOf face) : link ∈ cubeLinks := by
  simp only [cubeFaces, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil, or_false] at hl
  all_goals rcases hl with rfl | rfl | rfl | rfl
  all_goals decide

private theorem cubeFaces_spatial (face : Z4Plaq) (hf : face ∈ cubeFaces) :
    face ∈ spatialFaces 2 := by
  apply (spatialFaces_mem_iff 2 face).mpr
  simp only [cubeFaces, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem far_coordinate_zero {n : Nat} (h : n+1 < 2) : n = 0 :=
  Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (Nat.le_of_lt_succ h))

/-- Actual fully active faces, not a proposed replacement action. -/
theorem activeSpatialFaces_two_mem_iff (face : Z4Plaq) :
    face ∈ activeSpatialFaces 2 ↔ face ∈ cubeFaces := by
  constructor
  · intro hf
    have hs := (List.mem_filter.mp hf).1
    have hfull : FullyActive 2 face := of_decide_eq_true (List.mem_filter.mp hf).2
    have onA : (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1) ∈ edgesOf face :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have onB : (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2) ∈ edgesOf face :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have farA := (active_index_iff 2 (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
      (spatial_face_link_mem hs onA)).mp (hfull _ onA)
    have farB := (active_index_iff 2 (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
      (spatial_face_link_mem hs onB)).mp (hfull _ onB)
    obtain ⟨hx,hy,hz,ht,hd⟩ := (spatialFaces_mem_iff 2 face).mp hs
    rcases face with ⟨⟨x,y,z,t⟩,plane⟩
    change t = 0 at ht
    cases plane with
    | p01 =>
        simp only [StrictSliceLink, SliceLink, dirsOf, addE] at farA farB
        have hx0 : x = 0 := far_coordinate_zero farB.2.1
        have hy0 : y = 0 := far_coordinate_zero farA.2.2.1
        have hz01 : z = 0 ∨ z = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hz)
        subst x; subst y; subst t
        rcases hz01 with rfl | rfl
        all_goals decide
    | p02 =>
        simp only [StrictSliceLink, SliceLink, dirsOf, addE] at farA farB
        have hx0 : x = 0 := far_coordinate_zero farB.2.1
        have hz0 : z = 0 := far_coordinate_zero farA.2.2.2
        have hy01 : y = 0 ∨ y = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hy)
        subst x; subst z; subst t
        rcases hy01 with rfl | rfl
        all_goals decide
    | p12 =>
        simp only [StrictSliceLink, SliceLink, dirsOf, addE] at farA farB
        have hy0 : y = 0 := far_coordinate_zero farB.2.2.1
        have hz0 : z = 0 := far_coordinate_zero farA.2.2.2
        have hx01 : x = 0 ∨ x = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hx)
        subst y; subst z; subst t
        rcases hx01 with rfl | rfl
        all_goals decide
    | p03 => exact False.elim (hd rfl)
    | p13 => exact False.elim (hd rfl)
    | p23 => exact False.elim (hd rfl)
  · intro hf
    apply List.mem_filter.mpr
    refine ⟨cubeFaces_spatial face hf, decide_eq_true ?_⟩
    intro link hl
    have hc := cubeFaces_edges face hf link hl
    exact (active_index_iff 2 link (cubeLinks_in_carrier link hc)).mpr (cubeLinks_strict link hc)

theorem activeSpatialFaces_two_perm : (activeSpatialFaces 2).Perm cubeFaces :=
  Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff _ _
    (List.filter_sublist.nodup (spatialFaces_nodup 2)) (by decide)
    activeSpatialFaces_two_mem_iff

/-- The actual six retained factors, without any change to their source words. -/
def cubeWeight (w : Q') (K : Nat) : RatPoly :=
  polynomialProduct (fun face => heatPrefix w K (plaquette 2 face).scalar) cubeFaces

theorem activeSpatialWeight_cube (w : Q') (K : Nat) :
    RatPolyCoeffEqv (activeSpatialWeight w K 2) (cubeWeight w K) := by
  unfold activeSpatialWeight cubeWeight
  exact polynomialProduct_perm _ activeSpatialFaces_two_perm

def cubeIndices : List Nat := cubeLinks.map (baseLinks 2).idxOf

theorem cubeIndices_active (i : Nat) (hi : i ∈ cubeIndices) : i ∈ activeBlocks 2 := by
  obtain ⟨link,hl,rfl⟩ := List.mem_map.mp hi
  exact (active_index_iff 2 link (cubeLinks_in_carrier link hl)).mpr (cubeLinks_strict link hl)

theorem cubeIndices_nodup : cubeIndices.Nodup :=
  nodup_map_of_injOn _ _ (by decide : cubeLinks.Nodup)
    (fun a ha b hb he => BF4ExactSlabTemporalGaugeLedger.idxOf_injective_on_members
      (cubeLinks_in_carrier a ha) (cubeLinks_in_carrier b hb) he)

theorem cubeIndices_length : cubeIndices.length = 12 := by
  rw [cubeIndices, List.length_map]
  rfl

/-- These are original active factors which do not touch any retained face. -/
def outgoingIndices : List Nat :=
  (activeBlocks 2).filter (fun i => !decide (i ∈ cubeIndices))

theorem outgoing_core_perm : (outgoingIndices ++ cubeIndices).Perm (activeBlocks 2) := by
  let kept := (activeBlocks 2).filter (fun i => decide (i ∈ cubeIndices))
  have hk : kept.Perm cubeIndices :=
    Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff _ _
      (List.filter_sublist.nodup (activeBlocks_nodup 2)) cubeIndices_nodup (fun i => by
        constructor
        · intro hi
          exact of_decide_eq_true (List.mem_filter.mp hi).2
        · intro hi
          exact List.mem_filter.mpr ⟨cubeIndices_active i hi, decide_eq_true hi⟩)
  have hp : (kept ++ outgoingIndices).Perm (activeBlocks 2) :=
    List.filter_append_perm (fun i => decide (i ∈ cubeIndices)) (activeBlocks 2)
  exact ((hk.symm.append_left outgoingIndices).trans List.perm_append_comm).trans hp

theorem activeSpatialWeight_cube_independent (w : Q') (K i : Nat)
    (hi : i < N) (hnot : i ∉ cubeIndices) :
    QuaternionBlockIndependent i (activeSpatialWeight w K 2) := by
  unfold activeSpatialWeight
  apply heatProduct_independent_index w K 2 (activeSpatialFaces 2) i hi
  intro face hf link hl _ he
  have hc := cubeFaces_edges face ((activeSpatialFaces_two_mem_iff face).mp hf) link hl
  exact hnot (he ▸ List.mem_map.mpr ⟨link,hc,rfl⟩)

/-- Original slice map with its exact six-face action and twelve kinetic links. -/
def cubeTransfer (w : Q') (K : Nat) (f : RatPoly) : RatPoly :=
  productMap N w K cubeIndices (polyMul (cubeWeight w K) f)

/-- All retained output tests are allowed; the input's cube locality is the
only extra guard. No nome, positivity, or cutoff lower bound is needed. -/
theorem original_transfer_cube (w : Q') (K : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks N f)
    (hi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i f) :
    SupportedHaarEqv N (transferStep w K 2 f) (cubeTransfer w K f) := by
  have hfr : ∀ i, i ∈ fringeBlocks 2 → QuaternionBlockIndependent i f := fun i h =>
    hi i (fringeBlocks_lt 2 i h) (fun hc => ((fringeBlocks_mem_iff 2 i).mp h).2
      (cubeIndices_active i hc))
  have hsupport := supported_polyMul (activeSpatialWeight_supported w K 2) hf
  have hdrop := productMap_drop_independent_prefix N w K cubeIndices outgoingIndices
    (outgoing_core_perm.nodup_iff.mpr (activeBlocks_nodup 2))
    (fun i h => activeBlocks_lt 2 i (outgoing_core_perm.mem_iff.mp h)) _ hsupport
    (fun i h => by
      have ha := (List.mem_filter.mp h).1
      have hn : i ∉ cubeIndices := by
        intro hc
        have hfalse := (List.mem_filter.mp h).2
        rw [decide_eq_true hc] at hfalse
        contradiction
      exact quaternionBlockIndependent_polyMul
        (activeSpatialWeight_cube_independent w K i (activeBlocks_lt 2 i ha) hn)
        (hi i (activeBlocks_lt 2 i ha) hn))
  have hperm : RatPolyCoeffEqv
      (activeTransfer w K 2 f)
      (productMap N w K (outgoingIndices ++ cubeIndices) (polyMul (activeSpatialWeight w K 2) f)) :=
    SU2QuaternionHeadChainComposition.partialHaarHeads_congr N
      ((polynomialProduct_perm _ outgoing_core_perm.symm).mul_right _)
  have hweight := productMap_congr N w K cubeIndices ((activeSpatialWeight_cube w K).mul_right f)
  have horiginal : SupportedHaarEqv N (transferStep w K 2 f) (activeTransfer w K 2 f) :=
    fun p hp => original_transfer_haar_active w K 2 hf hfr hp
  exact horiginal.trans
    ((SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hperm)).trans
      (hdrop.trans (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hweight))))

/-- Literal bent path 0->2->3->1->5->4->0 in the pilot's cube encoding.
The inverse orientations are retained, not replaced by a face trace product. -/
def bentEdges : List OrientedBF4Link :=
  [⟨((0,0,0,0),.x1),false⟩, ⟨((0,1,0,0),.x0),false⟩,
   ⟨((1,0,0,0),.x1),true⟩, ⟨((1,0,0,0),.x2),false⟩,
   ⟨((0,0,1,0),.x0),true⟩, ⟨((0,0,0,0),.x2),true⟩]

def bentObservable : RatPoly :=
  characterPolynomial (wordAt (fun e => (baseLinks 2).idxOf e.link) bentEdges).scalar 1

private theorem bentEdges_core (e : OrientedBF4Link) (he : e ∈ bentEdges) : e.link ∈ cubeLinks := by
  simp only [bentEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem word_supported (n : Nat) (block : OrientedBF4Link → Nat) :
    ∀ es, (∀ e, e ∈ es → block e < n) → QuaternionSupported n (wordAt block es)
  | [], _ => ⟨supported_one n, (fun _ h => False.elim (List.not_mem_nil h)),
      (fun _ h => False.elim (List.not_mem_nil h)), (fun _ h => False.elim (List.not_mem_nil h))⟩
  | e::es, h => by
      have hc : QuaternionSupported n (orientedCoordinateQuaternion (block e) e.reverse) := by
        cases e.reverse
        · exact QuaternionSupported.coordinate (h e List.mem_cons_self)
        · exact (QuaternionSupported.coordinate (h e List.mem_cons_self)).conj
      exact hc.mul (word_supported n block es (fun f hf => h f (List.mem_cons_of_mem e hf)))

theorem bentObservable_supported : SupportedQuaternionBlocks N bentObservable :=
  character_supported (word_supported N (fun e => (baseLinks 2).idxOf e.link) bentEdges
    (fun e he => List.idxOf_lt_length_of_mem (cubeLinks_in_carrier e.link (bentEdges_core e he)))).scalar 1

theorem bentObservable_cube_independent (i : Nat) (_hi : i < N) (hnot : i ∉ cubeIndices) :
    QuaternionBlockIndependent i bentObservable :=
  degree_zero_independent (character_independent
    (word_independent i (fun e => (baseLinks 2).idxOf e.link) bentEdges
      (fun e he h => hnot (h ▸ List.mem_map.mpr ⟨e.link,bentEdges_core e he,rfl⟩))).scalar 1)

/-- The actual original vacuum message U=T1 is pinned to the cube source. -/
theorem original_vacuum_message_cube (w : Q') (K : Nat) :
    SupportedHaarEqv N (transferStep w K 2 polyOne) (cubeTransfer w K polyOne) :=
  original_transfer_cube w K (supported_one N) (fun i _ _ => quaternionBlockIndependent_polyOne i)

/-- The actual original B=TF is pinned for the precise bent-loop insertion. -/
theorem original_bent_message_cube (w : Q') (K : Nat) :
    SupportedHaarEqv N (transferStep w K 2 bentObservable) (cubeTransfer w K bentObservable) :=
  original_transfer_cube w K bentObservable_supported bentObservable_cube_independent

theorem cubeTransfer_supported (w : Q') (K : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks N f) : SupportedQuaternionBlocks N (cubeTransfer w K f) :=
  productMap_supported N w K cubeIndices
    (fun i hi => activeBlocks_lt 2 i (cubeIndices_active i hi))
    (supported_polyMul (heatProduct_supported w K 2 cubeFaces) hf)

/-- Locality belongs to the reduced representative, not necessarily to
the raw original message. It pays subsequent action peeling. -/
theorem cubeTransfer_independent (w : Q') (K i : Nat) (hi : i < N)
    (hnot : i ∉ cubeIndices) {f : RatPoly} (hf : SupportedQuaternionBlocks N f) :
    QuaternionBlockIndependent i (cubeTransfer w K f) :=
  productMap_independent_of_not_mem N w K cubeIndices
    (fun j hj => activeBlocks_lt 2 j (cubeIndices_active j hj)) i hi hnot _
    (supported_polyMul (heatProduct_supported w K 2 cubeFaces) hf)

private theorem weighted_core (w : Q') (K : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks N p)
    (hi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i p) :
    weightedMass w K 2 p ≈ quaternionHaar N (polyMul (cubeWeight w K) p) :=
  Q'.eqv_trans _ _ _
    (spatialWeight_haar_active w K 2 p hp (fun i h => hi i (fringeBlocks_lt 2 i h)
      (fun hc => ((fringeBlocks_mem_iff 2 i).mp h).2 (cubeIndices_active i hc))))
    (QuaternionHaarSquareCertificate.haar_of_coeff ((activeSpatialWeight_cube w K).mul_right p))

private theorem weighted_message (w : Q') (K : Nat) {f p : RatPoly}
    (hf : SupportedQuaternionBlocks N f)
    (hfi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i f)
    (hp : SupportedQuaternionBlocks N p)
    (hpi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i p) :
    weightedMass w K 2 (polyMul p (transferStep w K 2 f)) ≈
      quaternionHaar N (polyMul (cubeWeight w K) (polyMul p (cubeTransfer w K f))) := by
  have h := (SupportedHaarEqv.refl N p).mul (original_transfer_cube w K hf hfi)
    (transferStep_supported w K 2 hf) hp
  exact Q'.eqv_trans _ _ _ (h (spatialWeight w K 2) (spatialWeight_supported w K 2))
    (weighted_core w K (supported_polyMul hp (cubeTransfer_supported w K hf))
      (fun i hi hn => quaternionBlockIndependent_polyMul (hpi i hi hn)
        (cubeTransfer_independent w K i hi hn hf)))

private theorem weighted_message_pair (w : Q') (K : Nat) {f g p : RatPoly}
    (hf : SupportedQuaternionBlocks N f)
    (hfi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i f)
    (hg : SupportedQuaternionBlocks N g)
    (hgi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i g)
    (hp : SupportedQuaternionBlocks N p)
    (hpi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i p) :
    weightedMass w K 2 (polyMul p (polyMul (transferStep w K 2 f) (transferStep w K 2 g))) ≈
      quaternionHaar N (polyMul (cubeWeight w K)
        (polyMul p (polyMul (cubeTransfer w K f) (cubeTransfer w K g)))) := by
  have hpair := (original_transfer_cube w K hf hfi).mul (original_transfer_cube w K hg hgi)
    (transferStep_supported w K 2 hg) (cubeTransfer_supported w K hf)
  have h := (SupportedHaarEqv.refl N p).mul hpair
    (supported_polyMul (transferStep_supported w K 2 hf) (transferStep_supported w K 2 hg)) hp
  exact Q'.eqv_trans _ _ _ (h (spatialWeight w K 2) (spatialWeight_supported w K 2))
    (weighted_core w K
      (supported_polyMul hp (supported_polyMul (cubeTransfer_supported w K hf) (cubeTransfer_supported w K hg)))
      (fun i hi hn => quaternionBlockIndependent_polyMul (hpi i hi hn)
        (quaternionBlockIndependent_polyMul (cubeTransfer_independent w K i hi hn hf)
          (cubeTransfer_independent w K i hi hn hg))))

/-- Seven ORIGINAL raw moments, in the order Z, N, BB, UB, UU, UFB, UFU.
Z and UU are distinct partition horizons, not a common normalization. -/
def originalBentMoments (w : Q') (K : Nat) : List Q' :=
  let U := transferStep w K 2 polyOne
  let B := transferStep w K 2 bentObservable
  let ell := weightedMass w K 2
  [ell (polyMul polyOne U), ell (polyMul bentObservable U),
   ell (polyMul polyOne (polyMul B B)), ell (polyMul polyOne (polyMul U B)),
   ell (polyMul polyOne (polyMul U U)), ell (polyMul bentObservable (polyMul U B)),
   ell (polyMul bentObservable (polyMul U U))]

/-- The same seven moments of the exact cube representatives on the SAME
original carrier. Their numerical values are not supplied in this module. -/
def cubeBentMoments (w : Q') (K : Nat) : List Q' :=
  let U := cubeTransfer w K polyOne
  let B := cubeTransfer w K bentObservable
  let ell := fun p => quaternionHaar N (polyMul (cubeWeight w K) p)
  [ell (polyMul polyOne U), ell (polyMul bentObservable U),
   ell (polyMul polyOne (polyMul B B)), ell (polyMul polyOne (polyMul U B)),
   ell (polyMul polyOne (polyMul U U)), ell (polyMul bentObservable (polyMul U B)),
   ell (polyMul bentObservable (polyMul U U))]

/-- Literal seven-moment source identification, retaining OWN centering data
and the complete original spatial weight until tested substitution is paid. -/
theorem original_seven_bent_moments_cube (w : Q') (K : Nat) :
    (originalBentMoments w K).getD 0 0 ≈ (cubeBentMoments w K).getD 0 0 ∧
    (originalBentMoments w K).getD 1 0 ≈ (cubeBentMoments w K).getD 1 0 ∧
    (originalBentMoments w K).getD 2 0 ≈ (cubeBentMoments w K).getD 2 0 ∧
    (originalBentMoments w K).getD 3 0 ≈ (cubeBentMoments w K).getD 3 0 ∧
    (originalBentMoments w K).getD 4 0 ≈ (cubeBentMoments w K).getD 4 0 ∧
    (originalBentMoments w K).getD 5 0 ≈ (cubeBentMoments w K).getD 5 0 ∧
    (originalBentMoments w K).getD 6 0 ≈ (cubeBentMoments w K).getD 6 0 := by
  have hone : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i polyOne :=
    fun i _ _ => quaternionBlockIndependent_polyOne i
  have hs := supported_one N
  have hb := bentObservable_supported
  have hi := bentObservable_cube_independent
  exact ⟨weighted_message w K hs hone hs hone, weighted_message w K hs hone hb hi,
    weighted_message_pair w K hb hi hb hi hs hone, weighted_message_pair w K hs hone hb hi hs hone,
    weighted_message_pair w K hs hone hs hone hs hone, weighted_message_pair w K hs hone hb hi hb hi,
    weighted_message_pair w K hs hone hs hone hb hi⟩

#print axioms cubeLinks_strict
#print axioms cubeFaces_edges
#print axioms cubeFaces_spatial
#print axioms active_index_iff
#print axioms spatial_face_link_mem
#print axioms spatialFaces_mem_iff
#print axioms activeSpatialFaces

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.activeSpatialFaces_two_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.cubeLinks_in_carrier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.activeSpatialFaces_two_perm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.activeSpatialWeight_cube
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.cubeIndices_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.cubeIndices_active
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.cubeIndices_length
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.outgoing_core_perm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.activeSpatialWeight_cube_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.original_transfer_cube
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.bentObservable_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.bentObservable_cube_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.original_vacuum_message_cube
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.original_bent_message_cube
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.cubeTransfer_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.cubeTransfer_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.original_seven_bent_moments_cube
