/-
# A singly occupied link kills the ORIGINAL full signed integrand

Extract one actual physical face without losing any other factor. At the
selected link every other incident face has spin zero, so independence of
the retained product is proved from its labels. Positive-spin Haar selection
then applies to the original full moment, at arbitrary slab extent.
-/

import YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
import YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm

namespace YMGap.Continuum.BF4ExactSlabSingletonOccupiedLink

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

theorem faceProduct_link_zero (extent : Nat) (state : EdgeLabelling) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) : ∀ faces : List Z4Plaq,
    (∀ f, f ∈ faces → link ∈ edgesOf f → state ((boundaryCompleteSlabPlaquettes extent).idxOf f) = 0) →
    HasQuaternionBlockDegree ((boundaryCompleteSlabLinks extent).idxOf link) 0 (faceProduct extent state faces)
  | [], _ => hasQuaternionBlockDegree_one _
  | f::fs, h => by
    have hf : HasQuaternionBlockDegree ((boundaryCompleteSlabLinks extent).idxOf link) 0
        (correctedSlabPlaquetteSpinFactor extent state f) := by
      by_cases he : state ((boundaryCompleteSlabPlaquettes extent).idxOf f) = 0
      · unfold correctedSlabPlaquetteSpinFactor
        rw [he]
        exact hasQuaternionBlockDegree_one _
      · exact linkLocal_degree_zero ((face_scalar_local extent f).character _) link hl
          (fun hh => he (h f List.mem_cons_self hh))
    exact hf.mul (faceProduct_link_zero extent state link hl fs (fun g hg => h g (List.mem_cons_of_mem f hg)))

/-- The independence guard is discharged from all remaining ORIGINAL face labels. -/
theorem original_insert_singleton_zero (extent : Nat) (state : EdgeLabelling) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (face : Z4Plaq) (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face)
    (hs : 0 < state ((boundaryCompleteSlabPlaquettes extent).idxOf face))
    (hd : HasQuaternionBlockDegree ((boundaryCompleteSlabLinks extent).idxOf link) 0 p)
    (only : ∀ f, f ∈ boundaryCompleteSlabPlaquettes extent → f ≠ face → link ∈ edgesOf f →
      state ((boundaryCompleteSlabPlaquettes extent).idxOf f) = 0) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul p (exactCorrectedSlabSpinNetworkIntegrand extent state)) ≈ 0 := by
  obtain ⟨before,after,he⟩ := List.append_of_mem hf
  have perm : (boundaryCompleteSlabPlaquettes extent).Perm (face::(before++after)) := by
    rw [he]
    exact List.perm_middle
  have hn := (List.nodup_cons.mp (perm.nodup (boundaryCompleteSlabPlaquettes_nodup extent))).1
  have ho : ∀ f, f ∈ before++after → link ∈ edgesOf f → state ((boundaryCompleteSlabPlaquettes extent).idxOf f) = 0 :=
    fun f hm => only f (perm.mem_iff.mpr (List.mem_cons_of_mem face hm)) (fun h => hn (h ▸ hm))
  have hlink := (mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face,hf,hl⟩
  refine Q'.eqv_trans _ _ _ (quaternionHaar_factorFold_perm _ (correctedSlabPlaquetteSpinFactor extent state) perm p) ?_
  change quaternionHaar _ (polyMul p (polyMul _ _)) ≈ 0
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc _ _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _
    ((RatPolyCoeffEqv.mul_comm p (correctedSlabPlaquetteSpinFactor extent state face)).mul_right
      (faceProduct extent state (before++after)))) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_assoc _ _ _ _) ?_
  exact original_character_link_zero hf link hl _ hs _
    (supported_polyMul hp (correctedSlabSpinNetworkFaces_support extent state (before++after)))
    (hd.mul (faceProduct_link_zero extent state link hlink _ ho))

/-- Explicit finite positive-spin incidence, not parity incidence. -/
def incidentOccupied (extent : Nat) (state : EdgeLabelling) (link : Z4Link) : List Z4Plaq :=
  (boundaryCompleteSlabPlaquettes extent).filter
    (fun f => decide (link ∈ edgesOf f ∧ 0 < state ((boundaryCompleteSlabPlaquettes extent).idxOf f)))

theorem incident_singleton_zero (extent : Nat) (state : EdgeLabelling) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (link : Z4Link) (face : Z4Plaq) (h : incidentOccupied extent state link = [face])
    (hd : HasQuaternionBlockDegree ((boundaryCompleteSlabLinks extent).idxOf link) 0 p) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul p (exactCorrectedSlabSpinNetworkIntegrand extent state)) ≈ 0 := by
  have hm : face ∈ incidentOccupied extent state link := by rw [h]; exact List.mem_singleton_self face
  have hf := List.mem_filter.mp hm
  have hs := of_decide_eq_true hf.2
  apply original_insert_singleton_zero extent state p hp face hf.1 link hs.1 hs.2 hd
  intro f hphys hne hlink
  by_cases hz : state ((boundaryCompleteSlabPlaquettes extent).idxOf f) = 0
  · exact hz
  · have hm : f ∈ incidentOccupied extent state link := List.mem_filter.mpr
      ⟨hphys,decide_eq_true ⟨hlink,by omega⟩⟩
    rw [h] at hm
    exact False.elim (hne (List.mem_singleton.mp hm))

end YMGap.Continuum.BF4ExactSlabSingletonOccupiedLink

#print axioms YMGap.Continuum.BF4ExactSlabSingletonOccupiedLink.faceProduct_link_zero
#print axioms YMGap.Continuum.BF4ExactSlabSingletonOccupiedLink.original_insert_singleton_zero
#print axioms YMGap.Continuum.BF4ExactSlabSingletonOccupiedLink.incidentOccupied
#print axioms YMGap.Continuum.BF4ExactSlabSingletonOccupiedLink.incident_singleton_zero
