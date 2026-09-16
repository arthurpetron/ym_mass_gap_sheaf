/-
# Exact response cancellation when one original probe is separated

An explicit link separator of the OLD selected action isolates one probe
from the other probe AND the inserted physical face. Place that face on
the latter side of the actual partition: both original connected numerators
vanish by disjoint Haar factorization. The exact response identity therefore
vanishes with both endpoint partition squares retained.

All rational nomes and cutoffs are allowed. The inserted identifier need
not be absent from the old list. These are signed finite identities, not
coefficient bounds, spectator resummation, spatial decay, or a gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
import YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion

namespace YMGap.Continuum.BF4ExactSlabResponseProbeSeparation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

private theorem connected_comm (w : Q') (K extent : Nat) (ids : List Nat) (p q : RatPoly) :
    connectedNumerator w K extent ids p q ≈ connectedNumerator w K extent ids q p :=
  Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff
      ((RatPolyCoeffEqv.mul_comm p q).mul_right
        (polynomialProduct (faceHeatPolynomial w K extent) ids))))
    (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv _ _))

private theorem response_zero_of_endpoint_zeros (w : Q') (K extent : Nat) (ids : List Nat)
    (id : Nat) (p q : RatPoly)
    (hold : connectedNumerator w K extent ids p q ≈ 0)
    (hnew : connectedNumerator w K extent (ids++[id]) p q ≈ 0) :
    response w K extent ids id p q ≈ 0 := by
  have hz (a b : Q') (h : a ≈ 0) : a*b ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (QPoly.q_zero_mul b)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (response_identity w K extent ids id p q))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hz _ _ hnew)
      (Q'.neg_eqv_congr _ _ (hz _ _ hold))) (by decide : (0 : Q') + -0 ≈ 0))

private theorem separated_endpoint_zeros (w : Q') (K extent : Nat) (p q : RatPoly)
    (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ids : List Nat) (id : Nat)
    (S : Separator extent left (right ++ edgesOf (slabPlaquetteAt extent id)) ids) :
    connectedNumerator w K extent ids p q ≈ 0 ∧
      connectedNumerator w K extent (ids++[id]) p q ≈ 0 := by
  let oldSeparator : Separator extent left right ids :=
    { cut := S.cut
      disjoint := by
        intro link hleft hright
        apply S.disjoint link hleft
        rcases List.mem_append.mp hright with h | h
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))
        · exact List.mem_append.mpr (Or.inr h) }
  have hold := numerator_zero_of_separator w K extent p q left right hp hq hl hr ids oldSeparator
  have hdisjoint : LinksDisjoint (left ++ faceLinks extent (cutLeft ids S.cut))
      (right ++ faceLinks extent (cutRight ids S.cut ++ [id])) := by
    intro link hleft hright
    apply S.disjoint link hleft
    rcases List.mem_append.mp hright with hright | hfaces
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hright)))
    · obtain ⟨face, hface, hedge⟩ := List.mem_flatMap.mp hfaces
      rcases List.mem_append.mp hface with holdFace | hnewFace
      · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨face, holdFace, hedge⟩))
      · have heq : face = id := List.mem_singleton.mp hnewFace
        subst face
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hedge)))
  have hperm : (cutLeft ids S.cut ++ (cutRight ids S.cut ++ [id])).Perm (ids++[id]) := by
    simpa only [List.append_assoc] using (cut_partition ids S.cut).append_right [id]
  have hnew := Q'.eqv_trans _ _ _ (connectedNumerator_perm w K extent hperm.symm p q)
    (connectedNumerator_zero w K extent (cutLeft ids S.cut) (cutRight ids S.cut ++ [id])
      left right hdisjoint p q hp hq hl hr)
  exact ⟨hold, hnew⟩

/-- Isolating the left probe from the right probe and inserted face kills
the signed ORIGINAL response, at both endpoint actions simultaneously. -/
theorem response_zero_of_left_separator (w : Q') (K extent : Nat) (p q : RatPoly)
    (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ids : List Nat) (id : Nat)
    (S : Separator extent left (right ++ edgesOf (slabPlaquetteAt extent id)) ids) :
    response w K extent ids id p q ≈ 0 := by
  have h := separated_endpoint_zeros w K extent p q left right hp hq hl hr ids id S
  exact response_zero_of_endpoint_zeros w K extent ids id p q h.1 h.2

/-- The symmetric probe-separation case uses the same original moments. -/
theorem response_zero_of_right_separator (w : Q') (K extent : Nat) (p q : RatPoly)
    (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ids : List Nat) (id : Nat)
    (S : Separator extent right (left ++ edgesOf (slabPlaquetteAt extent id)) ids) :
    response w K extent ids id p q ≈ 0 := by
  have h := separated_endpoint_zeros w K extent q p right left hq hp hr hl ids id S
  exact response_zero_of_endpoint_zeros w K extent ids id p q
    (Q'.eqv_trans _ _ _ (connected_comm w K extent ids p q) h.1)
    (Q'.eqv_trans _ _ _ (connected_comm w K extent (ids++[id]) p q) h.2)

end YMGap.Continuum.BF4ExactSlabResponseProbeSeparation

#print axioms YMGap.Continuum.BF4ExactSlabResponseProbeSeparation.response_zero_of_left_separator
#print axioms YMGap.Continuum.BF4ExactSlabResponseProbeSeparation.response_zero_of_right_separator
