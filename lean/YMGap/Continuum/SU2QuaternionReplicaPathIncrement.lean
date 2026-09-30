/-
# One-coordinate form of a replica-prefix path increment

Exchanging the already-swapped prefix of the two copies converts the next
path increment into replacement of just its next quaternion block.  The
weighted Haar identity is an exact change of variables for an arbitrary
supported doubled-carrier polynomial; it does not compare interacting
weights or choose an order of physical links.
-/

import YMGap.Continuum.SU2QuaternionReplicaPathTelescope
import YMGap.Continuum.SU2QuaternionDisjointPartialSwap

namespace YMGap.Continuum.SU2QuaternionReplicaPathIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionDisjointPartialSwap
open YMGap.Continuum.SU2QuaternionReplicaPathTelescope
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- The literal adjacent increment in the first-copy block order. -/
def prefixIncrement (n j : Nat) (f : RatPoly) : RatPoly :=
  difference (replicaPrefix n (j+1) f) (replicaPrefix n j f)

/-- Replacement of just block `j` by its second-copy coordinate. -/
def singleBlockDifference (n j : Nat) (f : RatPoly) : RatPoly :=
  difference (reindexQuaternionPolynomial (swap n [j]) f) f

theorem prefixIncrement_supported (n j : Nat) (f : RatPoly) :
    SupportedQuaternionBlocks (n+n) (prefixIncrement n j f) :=
  difference_supported (replicaPrefix_supported n (j+1) f)
    (replicaPrefix_supported n j f)

/-- Swapping the existing prefix cancels it from both adjacent path
observables.  Reindexing pads monomials, hence the carrier equivalence. -/
theorem prefix_increment_transport (n j : Nat) (f : RatPoly)
    (hj : j < n) (hf : SupportedQuaternionBlocks n f) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n (List.range j))
        (prefixIncrement n j f))
      (singleBlockDifference n j f) := by
  have hdisj : ∀ i, i ∈ List.range j → i ∉ [j] := by
    intro i hi hij
    have hi' := List.mem_range.mp hi
    have hij' := List.mem_singleton.mp hij
    omega
  have hfirst : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n (List.range j))
        (replicaPrefix n (j+1) f))
      (reindexQuaternionPolynomial (swap n [j]) f) := by
    simpa only [replicaPrefix, List.range_succ] using
      (reindex_comp_cancel n (List.range j) [j] hdisj f)
  have hf2 : SupportedQuaternionBlocks (n+n) f := by
    intro term hterm
    exact Nat.le_trans (hf term hterm) (Nat.mul_le_mul_left 4 (by omega))
  have hsecond : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n (List.range j))
        (replicaPrefix n j f)) f := by
    simpa only [replicaPrefix] using
      (reindex_twice_carrier n (List.range j) f hf2)
  change HaarCarrierEqv (n+n)
    (reindexQuaternionPolynomial (swap n (List.range j))
      (difference (replicaPrefix n (j+1) f) (replicaPrefix n j f)))
    (difference (reindexQuaternionPolynomial (swap n [j]) f) f)
  simp only [difference, reindexQuaternionPolynomial_add,
    reindexQuaternionPolynomial_neg]
  exact HaarCarrierEqv.add hfirst (HaarCarrierEqv.neg hsecond)

theorem prefix_increment_square_transport (n j : Nat) (f : RatPoly)
    (hj : j < n) (hf : SupportedQuaternionBlocks n f) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n (List.range j))
        (polyMul (prefixIncrement n j f) (prefixIncrement n j f)))
      (polyMul (singleBlockDifference n j f)
        (singleBlockDifference n j f)) := by
  rw [reindexQuaternionPolynomial_mul]
  exact HaarCarrierEqv.mul
    (prefix_increment_transport n j f hj hf)
    (prefix_increment_transport n j f hj hf)

/-- An exact full-pair change of variables.  The weight after the swap is
explicitly reindexed; this theorem does not bound it by the original weight. -/
theorem weighted_prefix_increment_change (n j : Nat) (f W : RatPoly)
    (hj : j < n) (hf : SupportedQuaternionBlocks n f)
    (hW : SupportedQuaternionBlocks (n+n) W) :
    quaternionHaar (n+n)
      (polyMul W (polyMul (prefixIncrement n j f) (prefixIncrement n j f))) ≈
    quaternionHaar (n+n)
      (polyMul (reindexQuaternionPolynomial (swap n (List.range j)) W)
        (polyMul (singleBlockDifference n j f)
          (singleBlockDifference n j f))) := by
  let s := swap n (List.range j)
  let d := prefixIncrement n j f
  have hd : SupportedQuaternionBlocks (n+n) d := prefixIncrement_supported n j f
  have hchange := quaternionHaar_reindex s
    (polyMul W (polyMul d d))
    (supported_polyMul hW (supported_polyMul hd hd))
  rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul] at hchange
  have hcarrier : HaarCarrierEqv (n+n)
      (polyMul (reindexQuaternionPolynomial s W)
        (polyMul (reindexQuaternionPolynomial s d)
          (reindexQuaternionPolynomial s d)))
      (polyMul (reindexQuaternionPolynomial s W)
        (polyMul (singleBlockDifference n j f)
          (singleBlockDifference n j f))) :=
    HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.mul
        (prefix_increment_transport n j f hj hf)
        (prefix_increment_transport n j f hj hf))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hchange) (haar_of_carrier hcarrier)

#print axioms prefixIncrement
#print axioms singleBlockDifference
#print axioms prefixIncrement_supported
#print axioms prefix_increment_transport
#print axioms prefix_increment_square_transport
#print axioms weighted_prefix_increment_change

end YMGap.Continuum.SU2QuaternionReplicaPathIncrement
