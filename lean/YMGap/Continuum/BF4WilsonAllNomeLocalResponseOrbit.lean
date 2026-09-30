/-
# Width-independent all-time survival of the ORIGINAL plaquette

The actual local spectator floor c(w)>0 controls the one-step response of
the same literal Wilson plaquette. Its universal squared-norm cap four
gives rho(w)=c(w)/4 as a Rayleigh lower bound. Positivity of every actual
time power propagates this LOWER bound to every integer lag.

The source, time operator and centered norm stay on the existing all-nome
Wilson completion. The absolute floor starRatio(w)*rho(w)^n has no width
argument, with active links supplied by strict padding. No identification
between widths, upper decay, scaling family, finite physical mass or
continuum survival is asserted. Inactive fringe states are not discarded.
-/

import YMGap.Continuum.BF4WilsonAllNomeResponseLower
import YMGap.Continuum.BF4WilsonAllNomeLocalConnectedFloor
import YMGap.Continuum.BF4WilsonAllNomePlaquetteUniformCapResponse

namespace YMGap.Continuum.BF4WilsonAllNomeLocalResponseOrbit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy (originalJointLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalResponse
  (localResponseFloor localResponseFloor_positive)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState pairing_lag)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity (lagMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteVariance (literal_mean_pin)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteUniformCapResponse (plaquette_norm_le_four)
open YMGap.Continuum.BF4WilsonAllNomeResponseLower
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- Explicit lower response rate. No width, heat cutoff or time argument. -/
def localRayleighFloor : Q' := localResponseFloor hw0 hw1 * Q'.mkPos 1 4 (by decide)

theorem localRayleighFloor_positive : (0 : Q') < localRayleighFloor hw0 hw1 :=
  Q'.mul_pos (localResponseFloor_positive hw0 hw1) (by decide)

theorem localRayleighFloor_pow_positive : ∀ n : Nat,
    (0 : Q') < (localRayleighFloor hw0 hw1)^n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (localRayleighFloor_positive hw0 hw1)
      (localRayleighFloor_pow_positive n)

private theorem rational_scale (a b : Q') : RCscale a (Rq b) = Rq (a*b) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul a b).symm

private theorem localRayleighFloor_cap :
    RCscale (localRayleighFloor hw0 hw1) (Rq 4) = Rq (localResponseFloor hw0 hw1) := by
  rw [rational_scale]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (by decide : Q'.eqv (Q'.mkPos 1 4 (by decide) * 4) 1))
      (Q'.mul_one_eqv _))

variable (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "loop" => plaquetteLoop face hf
local notation "x" => loopState loop
local notation "F" => intrinsicForm hw0 hw1
local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "rho" => localRayleighFloor hw0 hw1

/-- The nome-only local response is on the LITERAL Wilson carrier. Only
equal original scalar moments are transported, not a map between carriers. -/
theorem plaquette_local_response_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (Rq (localResponseFloor hw0 hw1)) (B v (T 1 v)) := by
  rw [plaquetteExcitation_correlator_pin]
  let M := originalJointLimit hw0 hw1 0 (.loop 0 loop 1) (Nat.le_refl 0)
  have hlag := pairing_lag hw0 hw1 loop 1
  have hm : Equiv (F x (unit width)) M := literal_mean_pin hw0 hw1 width face hf
  have hm' : Equiv (F (unit width) x) M :=
    (intrinsicForm_symm hw0 hw1 (unit width) x).trans hm
  have hcenter : Equiv (centeredTimeMoment hw0 hw1 1 x x)
      (sub (lagMoment hw0 hw1 loop 1) (mul M M)) := by
    unfold centeredTimeMoment
    exact equiv_sub hlag
      ((Pivot2.mul_congr_left hm).trans (Pivot2.mul_congr_right hm'))
  exact leEv_trans
    (BF4WilsonAllNomeLocalConnectedFloor.connected_response_floor
      hw0 hw1 width face hf hactive) (leEv_of_equiv hcenter.symm)

theorem plaquette_local_rayleigh_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (RCscale rho (B v v)) (B v (T 1 v)) := by
  have h := RCscale_mono (Q'.le_of_lt (localRayleighFloor_positive hw0 hw1))
    (plaquette_norm_le_four hw0 hw1 width face hf)
  rw [localRayleighFloor_cap] at h
  exact RCle_trans h (plaquette_local_response_floor hw0 hw1 width face hf hactive)

/-- Every integer lag of the same state; the coefficient is independent of
width. This is a LOWER survival estimate, not an upper gap estimate. -/
theorem plaquette_response_geometric_lower
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (n : Nat) :
    RCle (RCscale (rho^n) (B v v)) (B v (T n v)) :=
  response_geometric_lower hw0 hw1 v rho
    (Q'.le_of_lt (localRayleighFloor_positive hw0 hw1))
    (plaquette_local_rayleigh_floor hw0 hw1 width face hf hactive) n

/-- A fully supplied rational lower bound with no width in the constant. -/
theorem plaquette_response_absolute_lower
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (n : Nat) :
    RCle (Rq (rho^n * starRatio w)) (B v (T n v)) := by
  have h := RCscale_mono (Q'.le_of_lt (localRayleighFloor_pow_positive hw0 hw1 n))
    (plaquetteExcitation_norm_floor hw0 hw1 width face hf)
  rw [rational_scale] at h
  exact RCle_trans h (plaquette_response_geometric_lower hw0 hw1 width face hf hactive n)

/-- Actual positive-time images retain a positive norm at every finite lag. -/
theorem plaquette_time_norm_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (n : Nat) :
    RCle (Rq (rho^(n+n) * starRatio w)) (B (T n v) (T n v)) := by
  rw [completedInner_time_balance, ← completedTime_add]
  exact plaquette_response_absolute_lower hw0 hw1 width face hf hactive (n+n)

theorem plaquette_time_ne_zero
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (n : Nat) : T n v ≠ completedZero hw0 hw1 width := by
  intro hz
  have h := plaquette_time_norm_floor hw0 hw1 width face hf hactive n
  rw [hz, completedInner_zero_left] at h
  have hle : rho^(n+n)*starRatio w ≤ (0 : Q') :=
    GNSQuotient.GNSData.RCofQ'_le_reflect h
  have hp := Q'.mul_pos (localRayleighFloor_pow_positive hw0 hw1 (n+n))
    (starRatio_positive hw0 hw1)
  exact (by decide : ¬ (0 : Q') < (0 : Q')) (Q'.pos_of_lt_of_le hp hle)

omit hf
/-- Strict padding produces activity for the actual base face at every
larger width. Separate carriers are retained; no width map is postulated. -/
theorem padded_plaquette_response_absolute_lower {base width : Nat}
    (hwidth : base < width) (face : Z4Plaq) (hf : face ∈ spatialFaces base) (n : Nat) :
    let z := (plaquetteExcitation hw0 hw1 width face
      (spatialFaces_mono (Nat.le_of_lt hwidth) hf)).val
    RCle (Rq (rho^n * starRatio w)) (B z (T n z)) :=
  plaquette_response_absolute_lower hw0 hw1 width face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
    (plaquette_active_after_padding hwidth face hf) n

#print axioms localRayleighFloor
#print axioms localRayleighFloor_positive
#print axioms localRayleighFloor_pow_positive
#print axioms plaquette_local_response_floor
#print axioms plaquette_local_rayleigh_floor
#print axioms plaquette_response_geometric_lower
#print axioms plaquette_response_absolute_lower
#print axioms plaquette_time_norm_floor
#print axioms plaquette_time_ne_zero
#print axioms padded_plaquette_response_absolute_lower

end YMGap.Continuum.BF4WilsonAllNomeLocalResponseOrbit
