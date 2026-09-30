/-
# Two exterior copies with one shared quaternion block

On the doubled original carrier, exchange every block except a selected
lower/upper pair. The selected lower block is the common variable for two
local factors whose exterior coordinates lie in different copies. These are
coordinate identities only; no conditional-density comparison is asserted.
-/

import YMGap.Continuum.SU2QuaternionPartialSliceSwap
import YMGap.Continuum.SU2QuaternionSelectedProjectionReindex

namespace YMGap.Continuum.SU2QuaternionSharedBlockExteriorSwap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionSelectedProjectionReindex

/-- Exactly the first-copy exterior blocks relative to `j`. -/
def exteriorIds (n j : Nat) : List Nat :=
  (List.range n).filter (fun k => decide (k ≠ j))

theorem mem_exteriorIds (n j k : Nat) :
    k ∈ exteriorIds n j ↔ k < n ∧ k ≠ j := by
  simp [exteriorIds]

/-- Exchange the two exteriors while retaining both selected blocks. -/
def exteriorSwap (n j : Nat) : QuaternionBlockInvolution (n+n) :=
  swap n (exteriorIds n j)

theorem exteriorSwap_lower_fixed (n j : Nat) (hj : j < n) :
    (exteriorSwap n j).map j = j := by
  rw [exteriorSwap, swap_lower n _ j hj]
  simp [mem_exteriorIds]

theorem exteriorSwap_upper_fixed (n j : Nat) (hj : j < n) :
    (exteriorSwap n j).map (n+j) = n+j := by
  rw [exteriorSwap, swap_upper n _ j hj]
  simp [mem_exteriorIds]

theorem exteriorSwap_lower_moves (n j k : Nat) (hk : k < n) (hne : k ≠ j) :
    (exteriorSwap n j).map k = n+k := by
  rw [exteriorSwap, swap_lower n _ k hk]
  simp [mem_exteriorIds, hk, hne]

theorem exteriorSwap_upper_moves (n j k : Nat) (hk : k < n) (hne : k ≠ j) :
    (exteriorSwap n j).map (n+k) = k := by
  rw [exteriorSwap, swap_upper n _ k hk]
  simp [mem_exteriorIds, hk, hne]

/-- In-place Haar integration commutes with the exterior exchange because
the integrated selected block itself does not move. -/
theorem reindex_project_commutes (n j : Nat) (hj : j < n) (p : RatPoly) :
    RatPolyCoeffEqv
      (reindexQuaternionPolynomial (exteriorSwap n j)
        (integrateQuaternionBlock j p))
      (integrateQuaternionBlock j
        (reindexQuaternionPolynomial (exteriorSwap n j) p)) := by
  have hslot : j < n+n := Nat.lt_of_lt_of_le hj (Nat.le_add_right n n)
  simpa only [exteriorSwap_lower_fixed n j hj] using
    (reindex_integrateQuaternionBlock (exteriorSwap n j) j hslot p)

/-- A polynomial independent of the retained block moves wholly to the
second copy. This is Haar-carrier equality under arbitrary insertion, not
literal list equality. -/
theorem normalizer_transport_to_lift (n j : Nat) (hj : j < n) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p)
    (hind : QuaternionBlockIndependent j p) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (exteriorSwap n j) p)
      (liftBoundary n p) := by
  apply reindex_to_lift n (exteriorIds n j) p hp
  intro k hk hnot
  by_cases h : k = j
  · subst k
    exact hind
  · exact False.elim (hnot ((mem_exteriorIds n j k).mpr ⟨hk, h⟩))

#print axioms exteriorIds
#print axioms mem_exteriorIds
#print axioms exteriorSwap
#print axioms exteriorSwap_lower_fixed
#print axioms exteriorSwap_upper_fixed
#print axioms exteriorSwap_lower_moves
#print axioms exteriorSwap_upper_moves
#print axioms reindex_project_commutes
#print axioms normalizer_transport_to_lift

end YMGap.Continuum.SU2QuaternionSharedBlockExteriorSwap
