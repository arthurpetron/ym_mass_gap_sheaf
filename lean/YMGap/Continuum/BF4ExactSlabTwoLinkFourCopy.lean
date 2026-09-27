/-
# Original two-link signed four-copy identity

Instantiate the generic four-copy covariance identity on two distinct physical
links of the original slab action. The original face product is retained:
left-only and right-only factors are replicated in their own coordinates,
shared faces remain inside the crossed determinant, and neither faces occur
once as the exterior insertion. This is an exact identity, not an angle or
positivity estimate.
-/

import YMGap.Continuum.BF4ExactSlabSharedFaceGeometry
import YMGap.Continuum.BF4ExactSlabLocalSupportComparison
import YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
import YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
import YMGap.Continuum.SU2QuaternionSharedFactorDeterminant

namespace YMGap.Continuum.BF4ExactSlabTwoLinkFourCopy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSharedFaceGeometry
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionFourCopyCovariance
open YMGap.Continuum.SU2QuaternionSharedFactorDeterminant

local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

def leftOnlyHeat (w : Q') (K extent : Nat) (left right : Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (leftOnlyIds extent left right)

def rightOnlyHeat (w : Q') (K extent : Nat) (left right : Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (rightOnlyIds extent left right)

def neitherHeat (w : Q') (K extent : Nat) (left right : Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (neitherIds extent left right)

/-- The selected-coordinate interaction: both one-link factors and all shared
faces. Only its crossed determinant will be integrated in the four-copy form. -/
def interactionWeight (w : Q') (K extent : Nat) (left right : Z4Link) : RatPoly :=
  polyMul (polyMul (leftOnlyHeat w K extent left right)
    (rightOnlyHeat w K extent left right)) (sharedHeat w K extent left right)

private theorem faceLocal_independent {extent : Nat} {links : List Z4Link}
    {p : RatPoly} (hp : LinkLocal extent links p) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hnot : link ∉ links) :
    QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf link) p := by
  apply independent_of_local hp (List.idxOf_lt_length_of_mem hl)
  intro hm
  apply hnot
  rw [correctedSlabLinkAt_idxOf hl] at hm
  exact hm

theorem leftOnly_independent_right (w : Q') (K extent : Nat)
    (left right : Z4Link) (hright : right ∈ boundaryCompleteSlabLinks extent) :
    QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf right)
      (leftOnlyHeat w K extent left right) := by
  apply faceLocal_independent (leftOnly_heat_local w K extent left right) hright
  intro hm
  have hmem := (List.mem_filter.mp hm).1
  exact right_not_mem_leftOnly extent left right hmem

theorem rightOnly_independent_left (w : Q') (K extent : Nat)
    (left right : Z4Link) (hleft : left ∈ boundaryCompleteSlabLinks extent) :
    QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf left)
      (rightOnlyHeat w K extent left right) := by
  apply faceLocal_independent (rightOnly_heat_local w K extent left right) hleft
  intro hm
  have hmem := (List.mem_filter.mp hm).1
  exact left_not_mem_rightOnly extent left right hmem

theorem neither_independent_left (w : Q') (K extent : Nat)
    (left right : Z4Link) (hleft : left ∈ boundaryCompleteSlabLinks extent) :
    QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf left)
      (neitherHeat w K extent left right) := by
  apply faceLocal_independent (neither_heat_local w K extent left right) hleft
  intro hm
  exact (links_not_mem_neither extent left right).1 (List.mem_filter.mp hm).1

theorem neither_independent_right (w : Q') (K extent : Nat)
    (left right : Z4Link) (hright : right ∈ boundaryCompleteSlabLinks extent) :
    QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf right)
      (neitherHeat w K extent left right) := by
  apply faceLocal_independent (neither_heat_local w K extent left right) hright
  intro hm
  exact (links_not_mem_neither extent left right).2 (List.mem_filter.mp hm).1

theorem full_factor_pin (w : Q') (K extent : Nat) (left right : Z4Link) :
    RatPolyCoeffEqv (fullWeight w K extent)
      (polyMul (neitherHeat w K extent left right)
        (interactionWeight w K extent left right)) := by
  have hfull := heatProduct_shared_partition w K extent left right
  have hret := retainedHeat_partition w K extent left right
  have hgroup : RatPolyCoeffEqv (fullWeight w K extent)
      (polyMul (sharedHeat w K extent left right)
        (polyMul (leftOnlyHeat w K extent left right)
          (polyMul (rightOnlyHeat w K extent left right)
            (neitherHeat w K extent left right)))) := by
    exact hfull.trans ((RatPolyCoeffEqv.refl _).mul hret)
  exact hgroup.trans (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
    (.mul (.var 3) (.mul (.mul (.var 1) (.var 2)) (.var 0))) (by decide)
    (fun | 0 => sharedHeat w K extent left right
         | 1 => leftOnlyHeat w K extent left right
         | 2 => rightOnlyHeat w K extent left right
         | _ => neitherHeat w K extent left right))

private theorem singleton_disjoint {a b : Nat} (h : a ≠ b) :
    ∀ i, i ∈ [a] → i ∉ [b] :=
  fun _ hi hj => h ((List.mem_singleton.mp hi).symm.trans (List.mem_singleton.mp hj))

private theorem pair_nodup {a b : Nat} (h : a ≠ b) : ([a] ++ [b]).Nodup := by
  simp [h]

private theorem singleton_property {P : Nat → Prop} {a : Nat} (h : P a) :
    ∀ i, i ∈ [a] → P i :=
  fun _ hi => Eq.mpr (congrArg P (List.mem_singleton.mp hi)) h

private theorem pair_property {P : Nat → Prop} {a b : Nat} (ha : P a) (hb : P b) :
    ∀ i, i ∈ [a]++[b] → P i := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact singleton_property ha i h
  · exact singleton_property hb i h

theorem interaction_cross_determinant_pin (w : Q') (K extent : Nat)
    (left right : Z4Link)
    (hleft : left ∈ boundaryCompleteSlabLinks extent)
    (hright : right ∈ boundaryCompleteSlabLinks extent) (hlinks : left ≠ right) :
    HaarCarrierEqv ((blocks extent) + (blocks extent))
      (crossDeterminant (blocks extent) [ (boundaryCompleteSlabLinks extent).idxOf left ]
        [ (boundaryCompleteSlabLinks extent).idxOf right ]
        (interactionWeight w K extent left right))
      (polyMul
        (polyMul
          (polyMul (leftOnlyHeat w K extent left right)
            (replica (blocks extent) [ (boundaryCompleteSlabLinks extent).idxOf left ]
              (leftOnlyHeat w K extent left right)))
          (polyMul (rightOnlyHeat w K extent left right)
            (replica (blocks extent) [ (boundaryCompleteSlabLinks extent).idxOf right ]
              (rightOnlyHeat w K extent left right))))
        (crossDeterminant (blocks extent)
          [ (boundaryCompleteSlabLinks extent).idxOf left ]
          [ (boundaryCompleteSlabLinks extent).idxOf right ]
          (sharedHeat w K extent left right))) := by
  unfold interactionWeight
  have hne : (boundaryCompleteSlabLinks extent).idxOf left ≠
      (boundaryCompleteSlabLinks extent).idxOf right := by
    intro hidx
    exact hlinks (idxOf_injective_on_members hleft hright hidx)
  have ht := shared_factor_determinant (blocks extent)
    [ (boundaryCompleteSlabLinks extent).idxOf left ]
    [ (boundaryCompleteSlabLinks extent).idxOf right ]
    (singleton_disjoint hne)
    (leftOnlyHeat w K extent left right) (rightOnlyHeat w K extent left right)
    (sharedHeat w K extent left right)
    (heatProduct_supported w K extent (leftOnlyIds extent left right))
    (heatProduct_supported w K extent (rightOnlyIds extent left right))
    (singleton_property (leftOnly_independent_right w K extent left right hright))
    (singleton_property (rightOnly_independent_left w K extent left right hleft))
  exact ht

theorem original_four_copy_identity (w : Q') (K extent : Nat)
    (left right : Z4Link)
    (hleft : left ∈ boundaryCompleteSlabLinks extent)
    (hright : right ∈ boundaryCompleteSlabLinks extent) (hlinks : left ≠ right)
    (f g : RatPoly)
    (hf : SupportedQuaternionBlocks (blocks extent) f)
    (hg : SupportedQuaternionBlocks (blocks extent) g)
    (hfB : QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf right) f)
    (hgA : QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf left) g) :
    quaternionHaar ((blocks extent) + (blocks extent))
        (polyMul (neitherHeat w K extent left right)
          (fourEnergy (blocks extent)
            [ (boundaryCompleteSlabLinks extent).idxOf left ]
            [ (boundaryCompleteSlabLinks extent).idxOf right ]
            (interactionWeight w K extent left right) f g)) ≈
      quaternionHaar (blocks extent)
        (polyMul (neitherHeat w K extent left right)
          (polyAdd
            (polyAdd
              (covarianceNumerator
                ([ (boundaryCompleteSlabLinks extent).idxOf left ] ++
                  [ (boundaryCompleteSlabLinks extent).idxOf right ])
                (interactionWeight w K extent left right) f g)
              (covarianceNumerator
                ([ (boundaryCompleteSlabLinks extent).idxOf left ] ++
                  [ (boundaryCompleteSlabLinks extent).idxOf right ])
                (interactionWeight w K extent left right) f g))
            (polyAdd
              (covarianceNumerator
                ([ (boundaryCompleteSlabLinks extent).idxOf left ] ++
                  [ (boundaryCompleteSlabLinks extent).idxOf right ])
                (interactionWeight w K extent left right) f g)
              (covarianceNumerator
                ([ (boundaryCompleteSlabLinks extent).idxOf left ] ++
                  [ (boundaryCompleteSlabLinks extent).idxOf right ])
                (interactionWeight w K extent left right) f g)))) := by
  unfold interactionWeight
  have hne : (boundaryCompleteSlabLinks extent).idxOf left ≠
      (boundaryCompleteSlabLinks extent).idxOf right := by
    intro hidx
    exact hlinks (idxOf_injective_on_members hleft hright hidx)
  have hA : ([ (boundaryCompleteSlabLinks extent).idxOf left ] ++
      [ (boundaryCompleteSlabLinks extent).idxOf right ]).Nodup := by
    exact pair_nodup hne
  have hids : ∀ i,
      i ∈ ([ (boundaryCompleteSlabLinks extent).idxOf left ] ++
        [ (boundaryCompleteSlabLinks extent).idxOf right ]) → i < blocks extent := by
    exact pair_property (List.idxOf_lt_length_of_mem hleft) (List.idxOf_lt_length_of_mem hright)
  exact four_copy_identity (blocks extent)
    [ (boundaryCompleteSlabLinks extent).idxOf left ]
    [ (boundaryCompleteSlabLinks extent).idxOf right ]
    (singleton_disjoint hne)
    (interactionWeight w K extent left right) f g
    (neitherHeat w K extent left right)
    (supported_polyMul
      (supported_polyMul
        (heatProduct_supported w K extent (leftOnlyIds extent left right))
        (heatProduct_supported w K extent (rightOnlyIds extent left right)))
      (sharedHeat_supported w K extent left right))
    hf hg (heatProduct_supported w K extent (neitherIds extent left right))
    (singleton_property hfB) (singleton_property hgA)
    (pair_property (neither_independent_left w K extent left right hleft)
      (neither_independent_right w K extent left right hright))
    hA hids

/-- Concrete shared-heat form: one-block heat is replicated, the original
neither-face heat is inserted once, and only the shared heat is crossed. -/
theorem original_shared_four_copy_identity (w : Q') (K extent : Nat)
    (left right : Z4Link)
    (hleft : left ∈ boundaryCompleteSlabLinks extent)
    (hright : right ∈ boundaryCompleteSlabLinks extent) (hlinks : left ≠ right)
    (f g : RatPoly)
    (hf : SupportedQuaternionBlocks (blocks extent) f)
    (hg : SupportedQuaternionBlocks (blocks extent) g)
    (hfB : QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf right) f)
    (hgA : QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf left) g) :
    let n := blocks extent;
    let A := [(boundaryCompleteSlabLinks extent).idxOf left];
    let B := [(boundaryCompleteSlabLinks extent).idxOf right];
    let N := covarianceNumerator (A++B) (interactionWeight w K extent left right) f g;
    quaternionHaar (n+n) (polyMul (neitherHeat w K extent left right)
      (weightedFourEnergy n A B (leftOnlyHeat w K extent left right)
        (rightOnlyHeat w K extent left right) (sharedHeat w K extent left right) f g)) ≈
      quaternionHaar n (polyMul (neitherHeat w K extent left right)
        (polyAdd (polyAdd N N) (polyAdd N N))) := by
  have hne : (boundaryCompleteSlabLinks extent).idxOf left ≠
      (boundaryCompleteSlabLinks extent).idxOf right :=
    fun hidx => hlinks (idxOf_injective_on_members hleft hright hidx)
  exact weighted_four_copy_identity (blocks extent)
    [(boundaryCompleteSlabLinks extent).idxOf left]
    [(boundaryCompleteSlabLinks extent).idxOf right] (singleton_disjoint hne)
    (leftOnlyHeat w K extent left right) (rightOnlyHeat w K extent left right)
    (sharedHeat w K extent left right) f g (neitherHeat w K extent left right)
    (heatProduct_supported w K extent (leftOnlyIds extent left right))
    (heatProduct_supported w K extent (rightOnlyIds extent left right))
    (sharedHeat_supported w K extent left right) hf hg
    (heatProduct_supported w K extent (neitherIds extent left right))
    (singleton_property (leftOnly_independent_right w K extent left right hright))
    (singleton_property (rightOnly_independent_left w K extent left right hleft))
    (singleton_property hfB) (singleton_property hgA)
    (pair_property (neither_independent_left w K extent left right hleft)
      (neither_independent_right w K extent left right hright))
    (pair_nodup hne)
    (pair_property (List.idxOf_lt_length_of_mem hleft) (List.idxOf_lt_length_of_mem hright))

#print axioms leftOnly_independent_right
#print axioms rightOnly_independent_left
#print axioms neither_independent_left
#print axioms neither_independent_right
#print axioms full_factor_pin
#print axioms interaction_cross_determinant_pin
#print axioms original_four_copy_identity
#print axioms original_shared_four_copy_identity

end YMGap.Continuum.BF4ExactSlabTwoLinkFourCopy
