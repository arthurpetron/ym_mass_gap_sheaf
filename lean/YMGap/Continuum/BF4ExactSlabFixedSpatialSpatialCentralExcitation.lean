/-
# A nonzero original plaquette vector in the spatial unit complement

The original fundamental character of the canonical spatial plaquette is
centered by the explicit spatial-mean approximation stream. Its completed
self-pairing is the SAME spatial connected variance. The local six-face
star bound therefore gives a positive nome-dependent floor independent
of the positive base size, after all three existing regulator limits.

The vector belongs to the actual spatial unit complement and is acted on
by its actual physical-time semigroup. This supplies a nonzero witness for
the proved common small-nome two-step form bound, not a continuum particle,
metric-completeness theorem, unrestricted-coupling gap or mass calibration.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredPairing
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCentralExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredStream
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate spatialCenteredFace_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Positive base size supplies a specific original spatial plaquette. -/
theorem origin_physical {base : Nat} (hb : 0<base) : originFace ∈ spatialFaces base := by
  apply (spatialFaces_mem_iff base originFace).mpr
  exact ⟨hb, hb, hb, rfl, by decide⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "x" => faceSpan base originFace (origin_physical hb)
local notation "B" => completedInner hw0 hw1 base hsmall hd hs hb

/-- Explicitly constructed, unit-orthogonal original plaquette vector. -/
def centralExcitation : UnitComplement hw0 hw1 base hsmall hd hs hb :=
  ⟨centeredVector hw0 hw1 base hsmall hd hs hb x,
    centeredVector_orthogonal hw0 hw1 base hsmall hd hs hb x⟩

/-- The norm representative retains its existing spatial scalar modulus. -/
def excitationNorm : CReal := spatialCenteredMoment hw0 hw1 base hsmall hd hs hb 0 x x

def excitationNormCauchy : QCauchy (excitationNorm hw0 hw1 base hsmall hd hs hb).approx :=
  spatialCenteredMomentCauchy hw0 hw1 base hsmall hd hs hb 0 x x

theorem centralExcitation_norm_pin :
    B (centralExcitation hw0 hw1 base hsmall hd hs hb).val
      (centralExcitation hw0 hw1 base hsmall hd hs hb).val =
      Quotient.mk crealSetoid (excitationNorm hw0 hw1 base hsmall hd hs hb) :=
  centeredVector_pairing hw0 hw1 base hsmall hd hs hb x x

theorem centralExcitation_orthogonal :
    B (centralExcitation hw0 hw1 base hsmall hd hs hb).val
      (spatialCompletedUnit hw0 hw1 base hsmall hd hs hb) = RCzero :=
  (centralExcitation hw0 hw1 base hsmall hd hs hb).property

/-- A common positive local-star floor for an actual completed vector.
The constant depends on the nome, not the base size or removed regulators. -/
theorem centralExcitation_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio w)))
      (B (centralExcitation hw0 hw1 base hsmall hd hs hb).val
        (centralExcitation hw0 hw1 base hsmall hd hs hb).val) := by
  rw [centralExcitation_norm_pin]
  exact spatialCenteredFace_floor hw0 hw1 base hsmall hd hs hb originFace (origin_physical hb)

theorem centralExcitation_ne_zero :
    (centralExcitation hw0 hw1 base hsmall hd hs hb).val ≠
      spatialEmbedSpan hw0 hw1 base hsmall hd hs hb (zero base) := by
  intro hz
  have h := centralExcitation_norm_floor hw0 hw1 base hsmall hd hs hb
  rw [hz, spatialCompletedZero_norm] at h
  have hle : starRatio w ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (starRatio_positive hw0 hw1) hle)

/-- The same vector and same time map realize the original spatial connected
correlation at every fixed discrete physical lag. -/
theorem centralExcitation_correlator_pin (n : Nat) :
    B (centralExcitation hw0 hw1 base hsmall hd hs hb).val
      (spatialCompletedTime hw0 hw1 base hsmall hd hs hb n
        (centralExcitation hw0 hw1 base hsmall hd hs hb).val) =
      Quotient.mk crealSetoid (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x x) :=
  centeredVector_time_pairing hw0 hw1 base hsmall hd hs hb n x x

theorem centralExcitation_twoStep_bound :
    RCle (B (centralExcitation hw0 hw1 base hsmall hd hs hb).val
      (spatialCompletedTime hw0 hw1 base hsmall hd hs hb 2
        (centralExcitation hw0 hw1 base hsmall hd hs hb).val))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd)))
        (B (centralExcitation hw0 hw1 base hsmall hd hs hb).val
          (centralExcitation hw0 hw1 base hsmall hd hs hb).val)) :=
  unitComplement_twoStep_form_gap hw0 hw1 base hsmall hd hs hb
    (centralExcitation hw0 hw1 base hsmall hd hs hb)

#print axioms origin_physical
#print axioms centralExcitation
#print axioms excitationNorm
#print axioms excitationNormCauchy
#print axioms centralExcitation_norm_pin
#print axioms centralExcitation_orthogonal
#print axioms centralExcitation_norm_floor
#print axioms centralExcitation_ne_zero
#print axioms centralExcitation_correlator_pin
#print axioms centralExcitation_twoStep_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCentralExcitation
