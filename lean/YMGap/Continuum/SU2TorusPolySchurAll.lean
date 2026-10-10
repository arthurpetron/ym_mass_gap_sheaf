/-
All-spin Schur pairing for the constructed two-link polynomial Haar.

The off-diagonal identity integrates the head-harmonic solid representatives
with the second physical quaternion retained. The diagonal identity uses the
already proved norm of the same ordinary relative character. The resulting
character means remove the spin-two cutoff from the existing polynomial
partition calculation. This is not a full torus Gibbs measure, an interacting
transfer identity, or compact-group Haar on all functions.
-/

import YMGap.Continuum.SU2TorusPolyGibbs
import YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir
import YMGap.Continuum.SU2QuaternionRelativeCharacterNorm

namespace YMGap.Continuum.SU2TorusPolySchurAll

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir
open YMGap.Continuum.SU2QuaternionRelativeCharacterNorm
open YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2TorusPolyGibbs
open YMGap.Continuum.SU2PolyLinkHaar

local infix:50 " ≈ " => Q'.eqv

/-- Different spin labels are orthogonal under the ORIGINAL two-link Haar.
The carrier pins replace both ordinary characters by solid harmonics before
the exact head integration; the remaining physical link is never fixed. -/
theorem relativeCharacter_pair_zero {s t : Nat} (hne : s ≠ t) :
    quaternionHaar 2 (polyMul (relativeCharacter s) (relativeCharacter t)) ≈ 0 := by
  have hcarrier : QuaternionHaarCarrierEqv 2
      (polyMul (relativeCharacter s) (relativeCharacter t))
      (polyMul (relativeSolid s) (relativeSolid t)) :=
    ((solid_character_pin 2 (by decide) s).symm.mul_right (relativeCharacter t)).trans
      ((solid_character_pin 2 (by decide) t).symm.mul_left (relativeSolid s))
  have hpartial : RatPolyCoeffEqv
      (partialHaarHead (polyMul (relativeSolid s) (relativeSolid t))) polyZero :=
    relativeSolid_harmonic_offDiagonal
      (relativeSolid_blockDegree t) (relativeSolid_harmonic t) hne
  exact Q'.eqv_trans _ _ _ (haar_of_carrier hcarrier)
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (quaternionHaar_partialHaarHead 1 _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff hpartial)
        (Q'.eqv_refl 0)))

/-- Every two-link relative-character pair has its exact Kronecker value. -/
theorem relativeCharacter_pairing_all (s t : Nat) :
    quaternionHaar 2 (polyMul (relativeCharacter s) (relativeCharacter t)) ≈
      (if s = t then 1 else 0) := by
  by_cases h : s = t
  · subst t
    rw [if_pos rfl]
    exact relativeCharacter_square_norm s
  · rw [if_neg h]
    exact relativeCharacter_pair_zero h

/-- The constructed two-link polynomial Haar satisfies Schur at every spin. -/
theorem polySchur_all (J : Nat) : PolySchurUpTo quaternionPolyLinkHaar2 J :=
  fun s t _ _ => relativeCharacter_pairing_all s t

/-- Pairing against the trivial character gives every character mean. -/
theorem polyCharMean_all (J : Nat) : PolyCharMeanUpTo quaternionPolyLinkHaar2 J := by
  intro s _
  have hp := relativeCharacter_pairing_all s 0
  change quaternionHaar 2 (polyMul (relativeCharacter s) polyOne) ≈
    (if s = 0 then 1 else 0) at hp
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_polyMul_one_right 2 (relativeCharacter s))) hp

/-- Arbitrary signed coefficients and every cutoff, including zero: the
ORIGINAL two-link partition of the character sum is its trivial coefficient. -/
theorem partition_constructed_all (c : Nat → Q') (J : Nat) :
    (partitionPoly quaternionPolyLinkHaar2 c J).eqv (c 0) :=
  partitionPoly_eqv_c0 quaternionPolyLinkHaar2 c J (polyCharMean_all J)

#print axioms relativeCharacter_pair_zero
#print axioms relativeCharacter_pairing_all
#print axioms polySchur_all
#print axioms polyCharMean_all
#print axioms partition_constructed_all

end YMGap.Continuum.SU2TorusPolySchurAll
