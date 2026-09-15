/-
# Local spin selection with the ENTIRE detached heat background retained

The actual faces touching one original exposed link form a computed collar
of at most six faces. Keep its cutoff B fixed, but allow arbitrary individual
cutoffs on every detached face. A selected character above the degree of
p times that collar has exactly zero original full-Haar integral. The
threshold never inspects the detached cutoffs. Shared other links remain.

This is a finite exact selection identity at arbitrary rational nomes.
The collar cutoff B and insertion still enter the threshold. No original
OS-norm approximation, bulk/volume limit, transfer range, or Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
import YMGap.Continuum.BF4ExactSlabCollarDegreeBound

namespace YMGap.Continuum.BF4ExactSlabLocalBulkSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- ORIGINAL ordered plaquette heat factors, with individual physical profiles. -/
def profileHeat (w : Nat → Q') (cutoff : Nat → Nat) (extent : Nat) (ids : List Nat) : RatPoly :=
  polynomialProduct (fun id => faceHeatPolynomial (w id) (cutoff id) extent id) ids

theorem profileHeat_supported (w : Nat → Q') (cutoff : Nat → Nat) (extent : Nat) :
    ∀ ids : List Nat, SupportedQuaternionBlocks (blocks extent) (profileHeat w cutoff extent ids)
  | [] => supported_one _
  | id::ids => supported_polyMul (heatFace_supported (w id) (cutoff id) extent id)
      (profileHeat_supported w cutoff extent ids)

theorem profileHeat_local (w : Nat → Q') (cutoff : Nat → Nat) (extent : Nat) (ids : List Nat) :
    LinkLocal extent (faceLinks extent ids) (profileHeat w cutoff extent ids) :=
  BlockLocal.fold _ ids (fun id hi => (heatFace_local (w id) (cutoff id) extent id).mono
    (fun _ hl => List.mem_flatMap.mpr ⟨id,hi,hl⟩))

def nearIds (extent : Nat) (face : Z4Plaq) (ambient : List Nat) : List Nat :=
  collarIds extent [faceLinkA face] [] ambient

def farIds (extent : Nat) (face : Z4Plaq) (ambient : List Nat) : List Nat :=
  detachedIds extent [faceLinkA face] [] ambient

theorem nearIds_length_le (extent : Nat) (face : Z4Plaq) (ambient : List Nat)
    (hn : ambient.Nodup) (hphys : ∀ id,id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    (nearIds extent face ambient).length ≤ 6 := by
  simpa only [List.length_cons,List.length_nil,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
    collarIds_length_le extent [faceLinkA face] [] ambient hn hphys

/-- A bound on touching cutoffs does not restrict any detached cutoff. -/
def localCutoff (extent : Nat) (face : Z4Plaq) (B : Nat) (farCutoff : Nat → Nat) (id : Nat) : Nat :=
  if detachedTest extent [faceLinkA face] [] id then farCutoff id else B

def nearHeat (w : Nat → Q') (B extent : Nat) (face : Z4Plaq) (ambient : List Nat) : RatPoly :=
  profileHeat w (fun _ => B) extent (nearIds extent face ambient)

def farHeat (w : Nat → Q') (farCutoff : Nat → Nat) (extent : Nat) (face : Z4Plaq) (ambient : List Nat) : RatPoly :=
  profileHeat w farCutoff extent (farIds extent face ambient)

/-- Exact factorization by incidence, not factorization of the Haar integral. -/
theorem localHeat_pin (w : Nat → Q') (B : Nat) (farCutoff : Nat → Nat)
    (extent : Nat) (face : Z4Plaq) (ambient : List Nat) :
    RatPolyCoeffEqv (profileHeat w (localCutoff extent face B farCutoff) extent ambient)
      (polyMul (nearHeat w B extent face ambient) (farHeat w farCutoff extent face ambient)) := by
  have hn : profileHeat w (localCutoff extent face B farCutoff) extent (nearIds extent face ambient) =
      nearHeat w B extent face ambient := by
    apply polynomialProduct_congr
    intro id hi
    have h : detachedTest extent [faceLinkA face] [] id = false := by
      simpa only [Bool.not_eq_true'] using (List.mem_filter.mp hi).2
    simp only [localCutoff,h,Bool.false_eq_true,if_false]
  have hf : profileHeat w (localCutoff extent face B farCutoff) extent (farIds extent face ambient) =
      farHeat w farCutoff extent face ambient := by
    apply polynomialProduct_congr
    intro id hi
    simp only [localCutoff,(List.mem_filter.mp hi).2,if_true]
  have h := (polynomialProduct_perm (fun id => faceHeatPolynomial (w id)
    (localCutoff extent face B farCutoff id) extent id)
    (region_partition extent [faceLinkA face] [] ambient).symm).trans (polynomialProduct_append _ _ _)
  change RatPolyCoeffEqv _ (polyMul (profileHeat _ _ extent (nearIds extent face ambient))
    (profileHeat _ _ extent (farIds extent face ambient))) at h
  rw [hn,hf] at h
  exact h

theorem farHeat_degree_zero {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (w : Nat → Q')
    (farCutoff : Nat → Nat) (ambient : List Nat) :
    HasQuaternionBlockDegree (blockA hf).val 0 (farHeat w farCutoff extent face ambient) := by
  have hd := detached_disjoint extent [faceLinkA face] [] ambient
  have hn : faceLinkA face ∉ faceLinks extent (farIds extent face ambient) :=
    fun h => hd _ (by simp [faceLinks]) h
  have hlocal := profileHeat_local w farCutoff extent (farIds extent face ambient)
  have hm := List.idxOf_lt_length_of_mem
    (show faceLinkA face ∈ boundaryCompleteSlabLinks extent from
      (mem_boundaryCompleteSlabLinks_iff extent _).mpr ⟨face,hf,by simp [faceLinkA,edgesOf]⟩)
  have hp : correctedSlabLinkAt extent (blockA hf).val = faceLinkA face :=
    correctedSlabLinkAt_idxOf ((mem_boundaryCompleteSlabLinks_iff extent _).mpr
      ⟨face,hf,by simp [faceLinkA,edgesOf]⟩)
  intro t ht
  have hz := hlocal t ht (blockA hf).val hm (fun h => hn (hp ▸ h))
  unfold quaternionBlockDegree
  rw [show 4*(blockA hf).val = 4*(blockA hf).val+0 by omega,
    hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide)]

/-- Computed solely from the insertion and the touching B-cutoff collar. -/
def localDegree {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (w : Nat → Q')
    (B : Nat) (ambient : List Nat) (p : RatPoly) : Nat :=
  selectedFaceBound hf (polyMul p (nearHeat w B extent face ambient))

/-- Every detached original interaction remains, with an arbitrary individual cutoff. -/
theorem local_character_zero {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (w : Nat → Q')
    (B : Nat) (farCutoff : Nat → Nat) (ambient : List Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) (spin : Nat)
    (hs : localDegree hf w B ambient p < spin) :
    quaternionHaar (blocks extent) (polyMul
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin)
      (polyMul p (profileHeat w (localCutoff extent face B farCutoff) extent ambient))) ≈ 0 := by
  have he := ((localHeat_pin w B farCutoff extent face ambient).mul_left p).trans
    (RatPolyCoeffEqv.mul_assoc p (nearHeat w B extent face ambient)
      (farHeat w farCutoff extent face ambient)).symm
  exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ (he.mul_left _))
    (original_character_product_zero hf spin _ _
      (supported_polyMul hp (profileHeat_supported w (fun _ => B) extent _))
      (profileHeat_supported w farCutoff extent _) (farHeat_degree_zero hf w farCutoff ambient) hs)

end YMGap.Continuum.BF4ExactSlabLocalBulkSelection

#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.profileHeat
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.profileHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.profileHeat_local
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.nearIds
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.farIds
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.nearIds_length_le
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.localCutoff
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.nearHeat
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.farHeat
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.localHeat_pin
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.farHeat_degree_zero
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.localDegree
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkSelection.local_character_zero
