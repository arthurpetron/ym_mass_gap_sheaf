/-
# Rooted resummation for the heterogeneous original connected numerator

The rooted-family algebra is independent of the face nomes.  This file
instantiates the existing rooted functional resummation with the actual
heterogeneous connected numerator and its spectator partition square, then
applies the existing two-probe separator filter.
-/

import YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion
import YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
import YMGap.Continuum.BF4ExactSlabRootedFunctionalResummation

namespace YMGap.Continuum.BF4ExactSlabHeterogeneousRootedResummation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabRootedFamilyResummation
open YMGap.Continuum.BF4ExactSlabRootedFunctionalResummation
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

local infix:50 " ≈ " => Q'.eqv

private theorem coefficient_zero_of_discard
    (w : Nat → Q') (K : Nat → Nat) (extent : Nat)
    (p q : RatPoly) (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ids : List Nat) (hk : keep extent left right ids = false) :
    connectedCoefficient w K extent p q ids ≈ 0 := by
  cases he : findSeparator extent left right ids with
  | none =>
      simp only [keep, he, Option.isNone] at hk
      cases hk
  | some S =>
      exact coefficient_zero_of_separator w K extent p q left right hp hq hl hr ids S

theorem connectedNumerator_connecting_expansion
    (w : Nat → Q') (K : Nat → Nat) (extent : Nat)
    (p q : RatPoly) (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (hn : ambient.Nodup) :
    connectedNumerator w K extent ambient p q ≈
      listQSum (fun ids => connectedCoefficient w K extent p q ids *
        partitionSquare w K extent (detachedIds extent (left ++ right) ids ambient))
        (connectingAnchors extent left right ambient) := by
  have hroot := rooted_functional_resummed_expansion
    (extent := extent) (links := left ++ right)
    (F := fun ids => connectedNumerator w K extent ids p q)
    (G := partitionSquare w K extent)
    (fun {xs} {ys} h => connectedNumerator_perm w K extent h p q)
    (fun a b hd => numerator_spectator_factorizes w K extent p q (left ++ right)
      hp hq (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
      (hr.mono (fun _ h => List.mem_append.mpr (Or.inr h))) a b hd)
    ambient hn
  refine Q'.eqv_trans _ _ _ hroot ?_
  unfold connectingAnchors
  exact sum_filter_zero _ (keep extent left right) _ (fun ids _ hk =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (coefficient_zero_of_discard w K extent p q left right hp hq hl hr ids hk))
      (QPoly.q_zero_mul _))

end YMGap.Continuum.BF4ExactSlabHeterogeneousRootedResummation

#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousRootedResummation.connectedNumerator_connecting_expansion
