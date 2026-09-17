/-
# A nonzero unit-orthogonal vector on the actual Wilson completion

Center the actual original plaquette using its own mean approximation
stream. Its completed squared norm is the SAME intrinsic-form variance,
so the original local-star floor proves that this vector is nonzero.
The norm representative and its QCauchy modulus are returned explicitly.

The final concrete certificate discharges all guards at the existing nome
1/1024 and source base one. This is a fixed-spacing SU(2) lattice witness,
not a continuum excitation or an extension of the old transfer bound.
No physical-time/vacuum identification on the enlarged carrier is assumed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCentralExcitation
import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
import YMGap.Continuum.BF4ExactSlabSummableCoreRate

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

section General

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base) (face : Z4Plaq) (hf : face ∈ spatialFaces base)

local notation "p" => plaquette face hf
local notation "B" => completedInner hw0 hw1 hsmall hd hs hb

def excitation : Completion hw0 hw1 hsmall hd hs hb :=
  centeredVector hw0 hw1 hsmall hd hs hb p

theorem excitation_orthogonal :
    B (excitation hw0 hw1 hsmall hd hs hb face hf)
      (embed hw0 hw1 hsmall hd hs hb (unit base)) = RCzero :=
  centeredVector_orthogonal hw0 hw1 hsmall hd hs hb p

/-- The representative is the actual completed self-pairing limit. -/
def excitationNorm : CReal :=
  representativeInner hw0 hw1 hsmall hd hs hb
    (centeredStream hw0 hw1 hsmall hd hs hb p) (centeredStream hw0 hw1 hsmall hd hs hb p)

def excitationNormCauchy : QCauchy (excitationNorm hw0 hw1 hsmall hd hs hb face hf).approx :=
  representativeInnerCauchy hw0 hw1 hsmall hd hs hb
    (centeredStream hw0 hw1 hsmall hd hs hb p) (centeredStream hw0 hw1 hsmall hd hs hb p)

theorem excitation_norm_pin :
    B (excitation hw0 hw1 hsmall hd hs hb face hf) (excitation hw0 hw1 hsmall hd hs hb face hf) =
      Quotient.mk crealSetoid (excitationNorm hw0 hw1 hsmall hd hs hb face hf) := rfl

theorem excitationNorm_variance :
    Equiv (excitationNorm hw0 hw1 hsmall hd hs hb face hf)
      (sub (intrinsicForm hw0 hw1 hsmall hd hs hb p p)
        (mul (intrinsicForm hw0 hw1 hsmall hd hs hb p (unit base))
          (intrinsicForm hw0 hw1 hsmall hd hs hb p (unit base)))) :=
  centered_pair_representative hw0 hw1 hsmall hd hs hb p p

theorem excitationNorm_floor :
    leEv (ofQ' (starRatio w)) (excitationNorm hw0 hw1 hsmall hd hs hb face hf) :=
  leEv_trans (form_variance_floor hw0 hw1 hsmall hd hs hb face hf)
    (leEv_of_equiv (excitationNorm_variance hw0 hw1 hsmall hd hs hb face hf).symm)

theorem excitation_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio w)))
      (B (excitation hw0 hw1 hsmall hd hs hb face hf) (excitation hw0 hw1 hsmall hd hs hb face hf)) := by
  rw [excitation_norm_pin]
  exact excitationNorm_floor hw0 hw1 hsmall hd hs hb face hf

theorem excitation_ne_zero :
    excitation hw0 hw1 hsmall hd hs hb face hf ≠ completedZero hw0 hw1 hsmall hd hs hb := by
  intro hz
  have h := excitation_norm_floor hw0 hw1 hsmall hd hs hb face hf
  rw [hz, completedZero_inner_zero] at h
  have hle : starRatio w ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (starRatio_positive hw0 hw1) hle)

/-- A witnessing vector, not a Prop-level existence claim. -/
def excitationCertificate :
    {v : Completion hw0 hw1 hsmall hd hs hb //
      B v (embed hw0 hw1 hsmall hd hs hb (unit base)) = RCzero ∧
      RCle (Quotient.mk crealSetoid (ofQ' (starRatio w))) (B v v) ∧
      v ≠ completedZero hw0 hw1 hsmall hd hs hb} :=
  ⟨excitation hw0 hw1 hsmall hd hs hb face hf,
    excitation_orthogonal hw0 hw1 hsmall hd hs hb face hf,
    excitation_norm_floor hw0 hw1 hsmall hd hs hb face hf,
    excitation_ne_zero hw0 hw1 hsmall hd hs hb face hf⟩

end General

open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCentralExcitation (origin_physical)

local notation "hs0" => And.left existingNome_guards
local notation "hd0" => And.right existingNome_guards
local notation "he0" => And.right existingNome_entropyRate
local notation "B0" => completedInner nome_pos nome_lt_one hs0 hd0 he0 (base := 1) (by decide)

/-- All original analytic, base and face guards are discharged here. -/
def concreteCertificate :
    {v : Completion nome_pos nome_lt_one hs0 hd0 he0 (base := 1) (by decide) //
      B0 v (embed nome_pos nome_lt_one hs0 hd0 he0 (by decide) (unit 1)) = RCzero ∧
      RCle (Quotient.mk crealSetoid (ofQ' (starRatio nome))) (B0 v v) ∧
      v ≠ completedZero nome_pos nome_lt_one hs0 hd0 he0 (by decide)} :=
  excitationCertificate nome_pos nome_lt_one hs0 hd0 he0 (by decide)
    originFace (origin_physical (by decide))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.excitation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.excitation_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.excitationNorm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.excitationNormCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.excitation_norm_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.excitationNorm_variance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.excitationNorm_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.excitation_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.excitation_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.excitationCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation.concreteCertificate
