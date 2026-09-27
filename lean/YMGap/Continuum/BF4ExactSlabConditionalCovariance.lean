/-
# Original normalized covariance is the actual conditional-sweep pairing

At cutoff headCutoff(w)+stage, subtract the computed ORIGINAL finite
expectation from each supported polynomial. Their original unnormalized
GNS pairing, scaled by the existing reciprocal partition, is exactly the
existing connected covariance. No new completion or unit normalization by
an unconstructed square root is used.

Centering preserves literal link support. The checked eight-layer cone
therefore pins this SAME normalized covariance to an iterated sweep pairing
until cone/test contact. Stage (heat cutoff) and rounds (conditional sweep
count) are separate parameters. No physical-time interpretation is made.

OPEN: a useful strict contraction on these actual centered states. Global
mean zero below is NOT an identification with the common-fixed complement.
Neither normalized spatial decay nor a continuum/OS mass gap is proved.
-/

import YMGap.Continuum.BF4ExactSlabEightLayerCone
import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse

namespace YMGap.Continuum.BF4ExactSlabConditionalCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem chain {a b c : Q'} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ hab hbc

private theorem cancel_center (a r z : Q') (h : r*z ≈ 1) : a+(-(a*r))*z ≈ 0 := by
  have he : a+(-(a*r))*z ≈ a+(-a)*(r*z) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.neg (.mul (.var 0) (.var 1))) (.var 2)))
      (.add (.var 0) (.mul (.neg (.var 0)) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => a | 1 => r | _ => z)
  exact chain he (chain (Q'.add_eqv_congr_left _ _ _
    (chain (Q'.mul_eqv_congr_left _ _ _ h) (Q'.mul_one_eqv _)))
      (Q'.add_neg_self_eqv a))

private theorem normalize_center (a b ab r : Q') :
    r*(ab+(-(a*r))*b) ≈ ab*r + -((a*r)*(b*r)) :=
  poly_identity_of_normal_eq
    (.mul (.var 3) (.add (.var 2) (.mul (.neg (.mul (.var 0) (.var 3))) (.var 1))))
    (.add (.mul (.var 2) (.var 3))
      (.neg (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 3)))))
    (by decide) (fun | 0 => a | 1 => b | 2 => ab | _ => r)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)
local notation "F" => fullData hw0 hw1 K extent hK
local notation "N" => (fun p => numerator w (List.length (boundaryCompleteSlabLinks extent)) extent ids p K)
local notation "Z" => partitionSample w extent ids stage
local notation "P" => projections hw0 hw1 K extent hK

/-- The EXISTING reciprocal of the full original finite partition. -/
def inversePartition : Q' := reciprocalTerm w hw0 hw1 extent ids physical stage

local notation "r" => inversePartition hw0 hw1 extent stage

theorem inversePartition_cancel : r*Z ≈ 1 :=
  chain (Q'.mul_comm_eqv _ _)
    (Q'.mul_recipPos_eqv _ (Q'.pos_of_lt_of_le
      (partitionFloor_pos hw0 hw1 ids)
      (partitionSample_floor w hw0 hw1 extent ids physical stage)))

/-- The unscaled constant polynomial: its squared norm is Z, not one. -/
def unit : (F).V := ⟨polyOne, supported_one _⟩

def mean (p : (F).V) : Q' := finiteValue w hw0 hw1 extent ids physical p.val stage

/-- Explicit original-polynomial centering with the actual finite mean. -/
def centered (p : (F).V) : (F).V :=
  (F).add p ((F).smul (-(mean hw0 hw1 extent stage p)) (unit hw0 hw1 extent stage))

local notation "U" => unit hw0 hw1 extent stage
local notation "C" p => centered hw0 hw1 extent stage p

theorem pair_numerator (p q : (F).V) : (F).B p q ≈ N (polyMul p.val q.val) :=
  Q'.eqv_refl _

theorem pair_unit (p : (F).V) : (F).B p U ≈ N p.val :=
  haar_of_coeff ((RatPolyCoeffEqv.mul_one p.val).mul_right
    (polynomialProduct (faceHeatPolynomial w K extent) ids))

theorem unit_pair (p : (F).V) : (F).B U p ≈ N p.val :=
  chain ((F).B_symm U p) (pair_unit hw0 hw1 extent stage p)

theorem unit_norm : (F).B U U ≈ Z :=
  chain (pair_unit hw0 hw1 extent stage U)
    (haar_of_coeff (RatPolyCoeffEqv.one_mul
      (polynomialProduct (faceHeatPolynomial w K extent) ids)))

theorem centered_pair_left (p q : (F).V) :
    (F).B (C p) q ≈ N (polyMul p.val q.val)+(-(N p.val*r))*N q.val := by
  exact chain ((F).B_add_left p ((F).smul (-(mean hw0 hw1 extent stage p)) U) q)
    (Q'.add_eqv_congr' (pair_numerator hw0 hw1 extent stage p q)
      (chain ((F).B_smul_left _ U q)
        (Q'.mul_eqv_congr_left _ _ _ (unit_pair hw0 hw1 extent stage q))))

/-- Actual global mean zero, without identifying all joint fixed vectors. -/
theorem centered_unit (p : (F).V) : (F).B (C p) U ≈ 0 := by
  have he : (F).B (C p) U ≈ N p.val+(-(N p.val*r))*Z :=
    chain ((F).B_add_left p ((F).smul (-(mean hw0 hw1 extent stage p)) U) U)
      (Q'.add_eqv_congr' (pair_unit hw0 hw1 extent stage p)
        (chain ((F).B_smul_left _ U U)
          (Q'.mul_eqv_congr_left _ _ _ (unit_norm hw0 hw1 extent stage))))
  exact chain he (cancel_center _ _ _ (inversePartition_cancel hw0 hw1 extent stage))

theorem centered_pair_right (p q : (F).V) : (F).B (C p) (C q) ≈ (F).B (C p) q := by
  exact chain ((F).B_add_right (C p) q ((F).smul (-(mean hw0 hw1 extent stage q)) U))
    (chain (Q'.add_eqv_congr_left _ _ _
      (chain ((F).B_smul_right _ (C p) U)
        (chain (Q'.mul_eqv_congr_left _ _ _ (centered_unit hw0 hw1 extent stage p))
          (Q'.mul_zero_eqv _)))) (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- Exact finite covariance, with the ORIGINAL reciprocal partition and
both actual centered states. No comparison constant or floor remains. -/
theorem normalized_centered_pair (p q : (F).V) :
    r*(F).B (C p) (C q) ≈ finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage :=
  chain (Q'.mul_eqv_congr_left _ _ _
    (chain (centered_pair_right hw0 hw1 extent stage p q)
      (centered_pair_left hw0 hw1 extent stage p q))) (normalize_center _ _ _ _)

theorem centered_local (support : List Z4Link) (p : (F).V)
    (hp : LinkLocal extent support p.val) : LinkLocal extent support (C p).val :=
  hp.add ((BlockLocal.one _ _).smul _)

/-- The covariance pin lives on the EXISTING completed carrier. -/
theorem completed_covariance (p q : (F).V) :
    rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage) =
      RCscale r ((F).cinnerCompl (embedV F (C p)) (embedV F (C q))) := by
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.eqv_symm (normalized_centered_pair hw0 hw1 extent stage p q))

theorem completed_centered_unit (p : (F).V) :
    (F).cinnerCompl (embedV F (C p)) (embedV F U) = RCzero := by
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv
    (fun _ => centered_unit hw0 hw1 extent stage p)

/-- Global centering is preserved by arbitrary lists of actual color
layers. This remains weaker than membership in the joint-fixed complement. -/
theorem sweep_centered_unit (cs : List Z4LinkEightColor.Color) (p : (F).V) :
    (F).cinnerCompl (runLayers hw0 hw1 K extent hK cs (embedV F (C p)))
      (embedV F U) = RCzero := by
  have hu := localized_embed hw0 hw1 K extent hK [] U (BlockLocal.one _ _)
  change (F).cinnerCompl ((P).sweep (cs.flatMap (layer extent)) (embedV F (C p)))
    (embedV F U) = _
  rw [(P).sweep_pair_fixed _ _ _ (fun i _ => hu i (List.not_mem_nil)),
    completed_centered_unit]

/-- The SAME original normalized connected covariance is an iterated
conditional-sweep pairing before cone/test contact. Stage and rounds are
independent; no heat-cutoff limit is re-labelled as physical time. -/
theorem covariance_as_sweep_pairing (rounds : Nat) (support testSupport : List Z4Link)
    (p q : (F).V) (hp : LinkLocal extent support p.val)
    (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent (8*rounds) support) testSupport) :
    rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage) =
      RCscale r ((F).cinnerCompl
        (runLayers hw0 hw1 K extent hK (cycles rounds) (embedV F (C p)))
        (embedV F (C q))) := by
  rw [cycles_pairing hw0 hw1 K extent hK rounds support testSupport
    (embedV F (C p)) (embedV F (C q))
    (localized_embed hw0 hw1 K extent hK support (C p)
      (centered_local hw0 hw1 extent stage support p hp))
    (localized_embed hw0 hw1 K extent hK testSupport (C q)
      (centered_local hw0 hw1 extent stage testSupport q hq)) hsep]
  exact completed_covariance hw0 hw1 extent stage p q

#print axioms inversePartition_cancel
#print axioms pair_numerator
#print axioms pair_unit
#print axioms unit_norm
#print axioms centered_unit
#print axioms normalized_centered_pair
#print axioms centered_local
#print axioms completed_covariance
#print axioms completed_centered_unit
#print axioms sweep_centered_unit
#print axioms covariance_as_sweep_pairing

end YMGap.Continuum.BF4ExactSlabConditionalCovariance
