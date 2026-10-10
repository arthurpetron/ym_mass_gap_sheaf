/-
# Exact bare Gram of ORIGINAL signed spatial plaquette families

Distinct canonical faces have an exclusive original link, so their literal
fundamental characters are orthogonal in the complete fixed-slice Haar law.
The ordered formula retains every repeated occurrence and signed coefficient.
For a Nodup family the norm is exactly the coefficient-square sum. In
particular the padded ALL-spatial-face unit family has norm equal to its
literal face count, positive at every positive base width.

Consumer: family_variance_bare_floor and the raw-source cap share the SAME
predecessorMass square. This supplies the missing computed bare norm for a
general-family omitted cutoff. It is not an interacting Gram identity,
warmed-source estimate, completed norm, scaling survival or physical gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
import YMGap.Continuum.Z4DistinctPlaquetteIntersection
import YMGap.Continuum.QuaternionHaarGammaFiniteSum
import YMGap.Continuum.QuaternionHaarFamilySquare
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
  (spatialFaces spatialFaces_mem_iff spatialFaces_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
  (face_link_mem_base character_haar_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
  (characterFace_independent_index)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
  (plaquette_supported plaquette_square_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.Z4DistinctPlaquetteIntersection (two_boundary_links_determine_face)
open YMGap.Continuum.QuaternionHaarGammaFiniteSum (finitePolySum_mul_pair)
open YMGap.Continuum.QuaternionHaarFamilySquare (qListSum_congr)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n

attribute [local irreducible] baseLinks plaquette

private def faceChar (width : Nat) (p : Z4Plaq) : RatPoly :=
  characterPolynomial (plaquette width p).scalar 1

/- An explicit decidable choice between two distinct initial edges suffices;
no enumeration, quotient representative or classical choice is involved. -/
private theorem exclusive_edge (p q : Z4Plaq) (hne : p ≠ q) :
    ∃ l : Z4Link, l ∈ edgesOf p ∧ l ∉ edgesOf q := by
  let a : Z4Link := (p.1, (dirsOf p.2).1)
  let b : Z4Link := (p.1, (dirsOf p.2).2)
  have ha : a ∈ edgesOf p := List.mem_cons_self
  have hb : b ∈ edgesOf p := by
    exact List.mem_cons_of_mem a List.mem_cons_self
  have hab : a ≠ b := fun h => dirsOf_ne p.2 (congrArg Prod.snd h)
  exact if haq : a ∈ edgesOf q then
    ⟨b, hb, fun hbq => hne (two_boundary_links_determine_face p q a b ha hb hab haq hbq)⟩
  else ⟨a, ha, haq⟩

/-- The actual original fundamental face Gram is the geometric Kronecker
delta, including adjacent faces sharing one link. Not an interacting pin. -/
theorem plaquette_pair_haar (width : Nat) (p q : Z4Plaq)
    (hp : p ∈ spatialFaces width) (hq : q ∈ spatialFaces width) :
    H (N width) (polyMul (characterPolynomial (plaquette width p).scalar 1)
      (characterPolynomial (plaquette width q).scalar 1)) ≈
      if p = q then (1 : Q') else 0 := by
  exact if he : p = q then by
    subst q
    simpa only [faceChar, if_pos rfl] using plaquette_square_one width p hp
  else by
    obtain ⟨l, hlp, hlq⟩ := exclusive_edge p q he
    have hl : l ∈ baseLinks width := face_link_mem_base hp hlp
    have hi := characterFace_independent_index width q ((baseLinks width).idxOf l) 1
      (List.idxOf_lt_length_of_mem hl) (fun m hm hmPhysical hindex =>
        hlq ((idxOf_injective_on_members hmPhysical hl hindex) ▸ hm))
    have hz := character_haar_zero hp l hlp 1 (by decide)
      (faceChar width q) (plaquette_supported width q) hi
    simpa only [faceChar, if_neg he] using hz

private theorem haar_finite_sum {A : Type} (n : Nat) (f : A → RatPoly) :
    ∀ xs : List A, H n (finitePolySum f xs) ≈
      qListSum (xs.map (fun a => H n (f a)))
  | [] => Q'.eqv_refl 0
  | _::xs => Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_finite_sum n f xs))

private theorem weighted_pair_haar (width : Nat) (c : Z4Plaq → Q')
    (p q : Z4Plaq) (hp : p ∈ spatialFaces width) (hq : q ∈ spatialFaces width) :
    H (N width) (polyMul (polySmul (c p) (faceChar width p))
      (polySmul (c q) (faceChar width q))) ≈
      if p = q then c p*c q else 0 := by
  have hc : RatPolyCoeffEqv
      (polyMul (polySmul (c p) (faceChar width p)) (polySmul (c q) (faceChar width q)))
      (polySmul (c p*c q) (polyMul (faceChar width p) (faceChar width q))) :=
    (RatPolyCoeffEqv.polyMul_smul_left (c p) _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right (c q) _ _).smul (c p)).trans
        (RatPolyCoeffEqv.smul_assoc (c p) (c q) _))
  have hs := Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N width) hc)
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) (c p*c q) _)
      (Q'.mul_eqv_congr_left (c p*c q) _ _ (plaquette_pair_haar width p q hp hq)))
  exact if he : p = q then by
    have hs' : H (N width) (polyMul (polySmul (c p) (faceChar width p))
        (polySmul (c q) (faceChar width q))) ≈ (c p*c q)*1 := by
      simpa only [if_pos he] using hs
    simpa only [if_pos he] using Q'.eqv_trans _ _ _ hs' (Q'.mul_one_eqv (c p*c q))
  else by
    have hs' : H (N width) (polyMul (polySmul (c p) (faceChar width p))
        (polySmul (c q) (faceChar width q))) ≈ (c p*c q)*0 := by
      simpa only [if_neg he] using hs
    simpa only [if_neg he] using Q'.eqv_trans _ _ _ hs' (Q'.mul_zero_eqv (c p*c q))

/-- Ordered geometric multiplicities, not merely positional diagonal terms.
For example two equal unit faces contribute four, not two. -/
def bareCoefficientGram (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  qListSum (qs.map (fun p =>
    qListSum (qs.map (fun q => if p = q then c p*c q else 0))))

/-- Exact bare norm for arbitrary signed coefficients and repeated physical
face occurrences, on the original full fixed-slice carrier. -/
theorem family_square_ordered_gram (width : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    H (N width) (polyMul (spatialSpan width c qs) (spatialSpan width c qs)) ≈
      bareCoefficientGram c qs := by
  let f : Z4Plaq → RatPoly := fun p => polySmul (c p) (faceChar width p)
  have he := haar_of_coeff (blocks := N width) (finitePolySum_mul_pair f f qs qs)
  have ho := haar_finite_sum (N width)
    (fun p => finitePolySum (fun q => polyMul (f p) (f q)) qs) qs
  have hi : ∀ p, p ∈ qs → H (N width)
      (finitePolySum (fun q => polyMul (f p) (f q)) qs) ≈
      qListSum (qs.map (fun q => if p = q then c p*c q else 0)) := by
    intro p hp
    exact Q'.eqv_trans _ _ _ (haar_finite_sum (N width) _ qs)
      (qListSum_congr qs _ _ (fun q hq => weighted_pair_haar width c p q (hqs p hp) (hqs q hq)))
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _ ho (qListSum_congr qs _ _ hi))

private theorem delta_sum_absent (c : Z4Plaq → Q') (p : Z4Plaq) :
    ∀ qs : List Z4Plaq, p ∉ qs →
      qListSum (qs.map (fun q => if p = q then c p*c q else 0)) ≈ 0
  | [], _ => Q'.eqv_refl _
  | q::qs, hn => by
    have he : p ≠ q := fun h => hn (List.mem_cons.mpr (Or.inl h))
    have ht : p ∉ qs := fun h => hn (List.mem_cons_of_mem q h)
    change (if p = q then c p*c q else 0) +
      qListSum (qs.map (fun q => if p = q then c p*c q else 0)) ≈ 0
    rw [if_neg he]
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (delta_sum_absent c p qs ht))
      (by decide : (0 : Q')+0 ≈ 0)

private theorem delta_sum_present (c : Z4Plaq → Q') (p : Z4Plaq) :
    ∀ qs : List Z4Plaq, qs.Nodup → p ∈ qs →
      qListSum (qs.map (fun q => if p = q then c p*c q else 0)) ≈ c p*c p
  | [], _, hp => False.elim (List.not_mem_nil hp)
  | q::qs, hn, hp => by
    have hnd := List.nodup_cons.mp hn
    exact if he : p = q then by
      subst q
      change (if p = p then c p*c p else 0) +
        qListSum (qs.map (fun q => if p = q then c p*c q else 0)) ≈ c p*c p
      rw [if_pos rfl]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (delta_sum_absent c p qs hnd.1))
        (QPoly.q_add_zero_eqv _)
    else by
      have ht : p ∈ qs := (List.mem_cons.mp hp).resolve_left he
      change (if p = q then c p*c q else 0) +
        qListSum (qs.map (fun q => if p = q then c p*c q else 0)) ≈ c p*c p
      rw [if_neg he]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (delta_sum_present c p qs hnd.2 ht))
        (QPoly.q_zero_add_eqv _)

/-- Distinct physical faces are an exact bare-Haar orthonormal family.
No nonzero coefficient or coefficient-sign premise is supplied. -/
theorem family_square_nodup (width : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    H (N width) (polyMul (spatialSpan width c qs) (spatialSpan width c qs)) ≈
      qListSum (qs.map (fun p => c p*c p)) :=
  Q'.eqv_trans _ _ _ (family_square_ordered_gram width c qs hqs)
    (qListSum_congr qs _ _ (fun p hp => delta_sum_present c p qs hn hp))

private theorem unit_square_sum : ∀ qs : List Z4Plaq,
    qListSum (qs.map (fun _ => (1 : Q')*(1 : Q'))) ≈ Q'.ofNat qs.length
  | [] => Q'.eqv_symm Q'.ofNat_zero_eqv
  | _::qs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (by decide : (1 : Q')*1 ≈ 1) (unit_square_sum qs))
      (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (Q'.ofNat_add_eqv qs.length 1).symm)

/-- ALL original spatial faces of the smaller base, embedded in the SAME
padded carrier, have an explicitly evaluated bare norm. -/
theorem padded_all_faces_square (base width : Nat) (hwidth : base ≤ width) :
    let f := spatialSpan width (fun _ => (1 : Q')) (spatialFaces base)
    H (N width) (polyMul f f) ≈ Q'.ofNat (spatialFaces base).length :=
  Q'.eqv_trans _ _ _
    (family_square_nodup width (fun _ => (1 : Q')) (spatialFaces base)
      (spatialFaces_nodup base) (fun _ hp => spatialFaces_mono hwidth hp))
    (unit_square_sum (spatialFaces base))

/-- Concrete nonzero bare norm for the unit ALL-face family used before
temporal smoothing on the AF trajectory; no interacting/survival claim. -/
theorem padded_all_faces_square_positive (base width : Nat)
    (hbase : 0 < base) (hwidth : base ≤ width) :
    let f := spatialSpan width (fun _ => (1 : Q')) (spatialFaces base)
    (0 : Q') < H (N width) (polyMul f f) := by
  have hp : ((0,0,0,0), Z4Plane.p01) ∈ spatialFaces base :=
    (spatialFaces_mem_iff base _).mpr ⟨hbase, hbase, hbase, rfl, by decide⟩
  have hl : 0 < (spatialFaces base).length :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hp)
  have hlen : (spatialFaces base).length = ((spatialFaces base).length-1)+1 := by omega
  have hpositive : (0 : Q') < Q'.ofNat (spatialFaces base).length := by
    rw [hlen]
    exact Q'.ofNat_succ_pos _
  exact Q'.pos_of_lt_of_le hpositive
    (Q'.ge_of_eqv (padded_all_faces_square base width hwidth))

#print axioms plaquette_pair_haar
#print axioms bareCoefficientGram
#print axioms family_square_ordered_gram
#print axioms family_square_nodup
#print axioms padded_all_faces_square
#print axioms padded_all_faces_square_positive

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareGram
