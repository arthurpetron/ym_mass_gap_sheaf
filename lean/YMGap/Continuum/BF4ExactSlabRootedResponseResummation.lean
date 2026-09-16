/-
# Exact spectator resummation for the ORIGINAL three-mark response

Root the actual face-link graph at both probe supports AND the inserted
face. Group the finite response coefficients by their computed rooted
core. All detached spectator selections sum to their actual partition
FOURTH power, with signs retained. The three mark-separation tests then
discard zero core coefficients. No absolute spectator majorant is used.

The original cleared response equals this computed sum at every rational
nome and finite cutoff. At positive subunit nomes and sufficiently late
cutoff, each resummed term has an explicit collar-local normalization cost.
A supplied estimate on the same signed sum feeds the existing cutoff-limit
covariance consumer. Spatial decay with useful coupling dependence is NOT
proved here; neither are physical transfer or continuum claims.
-/

import YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization
import YMGap.Continuum.BF4ExactSlabRootedFunctionalResummation
import YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion
import YMGap.Continuum.BF4ExactSlabResponseCollarNormalization

namespace YMGap.Continuum.BF4ExactSlabRootedResponseResummation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRootedFamilyResummation
open YMGap.Continuum.BF4ExactSlabRootedFunctionalResummation
open YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization
open YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabResponseCollarNormalization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-- All three marked supports form the root; the inserted face is not a spectator. -/
def markedLinks (extent id : Nat) (left right : List Z4Link) : List Z4Link :=
  (left++right)++edgesOf (slabPlaquetteAt extent id)

/-- Existing canonical rooted cores, with the proved three-mark zero cases removed. -/
def responseAnchors (extent id : Nat) (left right : List Z4Link) (ambient : List Nat) : List (List Nat) :=
  (rootedAnchors extent (markedLinks extent id left right) ambient).filter
    (responseKeep extent id left right)

/-- The signed resummed response; each detached factor is the actual Z^4. -/
def rootedResponse (w : Q') (K extent id : Nat) (p q : RatPoly)
    (left right : List Z4Link) (ambient : List Nat) : Q' :=
  listQSum (fun anchor => responseCoefficient w K extent id p q anchor *
    partitionFourth w K extent (detachedIds extent (markedLinks extent id left right) anchor ambient))
    (responseAnchors extent id left right ambient)

/-- Same response, computed cores, exact detached partition factors. The
duplicate-free premise is on the ambient enumeration, not on a supplied
cluster expansion or a guessed family of contributing components. -/
theorem response_resummed_filtered (w : Q') (K extent : Nat) (p q : RatPoly)
    (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (hn : ambient.Nodup) (id : Nat) :
    response w K extent ambient id p q ≈ rootedResponse w K extent id p q left right ambient := by
  let links := markedLinks extent id left right
  have hlp : LinkLocal extent links p := hl.mono
    (fun _ h => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h))))
  have hlq : LinkLocal extent links q := hr.mono
    (fun _ h => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))))
  have hf : ∀ link, link ∈ edgesOf (slabPlaquetteAt extent id) → link ∈ links :=
    fun _ h => List.mem_append.mpr (Or.inr h)
  have he := rooted_functional_resummed_expansion extent links
    (fun ids => response w K extent ids id p q) (partitionFourth w K extent)
    (fun h => response_perm w K extent h id p q)
    (fun a b hd => response_spectator_factorizes w K extent p q links hp hq hlp hlq a b id hf hd)
    ambient hn
  exact Q'.eqv_trans _ _ _ he
    (sum_filter_zero _ (responseKeep extent id left right) _ (fun anchor _ hk =>
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (responseCoefficient_zero_of_discard w K extent p q left right hp hq hl hr anchor id hk))
        (QPoly.q_zero_mul _)))

/-- The actual resummed term, normalized against the original two endpoint
partitions, costs only the explicit nome-, marked-support- and core-size-dependent
collar factor. This is not a smallness or spatial-decay estimate on the coefficient. -/
theorem rooted_response_term_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (id : Nat)
    (hid : id ∈ slabPhysicalFaceEdges extent) (p q : RatPoly)
    (left right : List Z4Link) (anchor ambient : List Nat) (hn : ambient.Nodup)
    (ha : ∀ j, j ∈ ambient → j ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (responseCoefficient w K extent id p q anchor *
      partitionFourth w K extent (detachedIds extent (markedLinks extent id left right) anchor ambient)) ≤
      (Q'.abs (responseCoefficient w K extent id p q anchor) *
        collarCost w hw0 hw1 (collarCount (markedLinks extent id left right) anchor)) *
      responseDenominator w K extent ambient id := by
  have hz : (0 : Q') ≤ partitionFourth w K extent
      (detachedIds extent (markedLinks extent id left right) anchor ambient) :=
    Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _) (SumOfSquares.q_mul_self_nonneg _)
  have h := Q'.mul_le_mul_of_nonneg_left _ _ _
    (detached_fourth_bound_bounded_count hw0 hw1 K extent hK
      (markedLinks extent id left right) anchor ambient hn ha id hid)
    (Q'.abs_nonneg (responseCoefficient w K extent id p q anchor))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.abs_mul_nonneg_right _ hz))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))

/-- A SUPPLIED bound on the resummed SIGNED expression controls the SAME
original covariance difference, retaining both endpoint partitions until
normalization. This theorem does not supply spatial decay of rooted cores. -/
theorem covariance_response_bound_of_rooted (w : Q')
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat)
    (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent)
    (p q : RatPoly) (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (b : Q') (K0 : Nat)
    (h : ∀ K, K0 ≤ K → Q'.abs (rootedResponse w K extent id p q left right ids) ≤
      b*responseDenominator w K extent ids id) :
    CReal.leEv (CReal.abs (CReal.sub
      (covariance w hw0 hw1 extent (ids++[id])
        (fun j hj => by
          rcases List.mem_append.mp hj with hj | hj
          · exact hi j hj
          · have he := List.mem_singleton.mp hj
            subst j
            exact hid) p q)
      (covariance w hw0 hw1 extent ids hi p q))) (CReal.ofQ' b) :=
  covariance_response_bound_eventually w hw0 hw1 extent ids hi id hid p q b K0
    (fun K hK => Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr
        (response_resummed_filtered w K extent p q left right hp hq hl hr ids hn id)))
      (h K hK))

end YMGap.Continuum.BF4ExactSlabRootedResponseResummation

#print axioms YMGap.Continuum.BF4ExactSlabRootedResponseResummation.markedLinks
#print axioms YMGap.Continuum.BF4ExactSlabRootedResponseResummation.responseAnchors
#print axioms YMGap.Continuum.BF4ExactSlabRootedResponseResummation.rootedResponse
#print axioms YMGap.Continuum.BF4ExactSlabRootedResponseResummation.response_resummed_filtered
#print axioms YMGap.Continuum.BF4ExactSlabRootedResponseResummation.rooted_response_term_bound
#print axioms YMGap.Continuum.BF4ExactSlabRootedResponseResummation.covariance_response_bound_of_rooted
