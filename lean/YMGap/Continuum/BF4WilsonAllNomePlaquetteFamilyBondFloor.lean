/-
# Whole signed-family response on the original completed bond carrier

The finite interior-family band and the ACTUAL identity Var=Energy+Bond
give Bond >= rho*Var at every positive terminal depth and late cutoff.
The constructed variance and transfer limits transport this inequality to
the SAME completed physical bond covariance. The existing ambient family
floor then supplies a positive coefficient-square floor for distinct faces.

The fraction depends only on strict nome and family-list size, not spatial
width, cutoff or terminal depth. It can deteriorate under changing coupling
or growing families. This is fixed-nome completed nontriviality, NOT a
surviving continuum excitation, physical mass floor or continuum QFT.
-/

import YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance
import YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement
import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws
import YMGap.Continuum.FCLimitContinuity

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (RatPolyCoeffEqv)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws (middleRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (normalizedEnergy oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (familyResponseFraction familyResponseFraction_positive padded_family_energy_band)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity
  (varianceFloor varianceFloor_positive)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
  (familyExpression family_within familyState)
open YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement
  (source_family_shift finite_family_increment_pin)
open YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit
  (finiteEnergy finite_increment_pin)
open YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit
  (finiteVariance finiteVariance_budget_pin varianceCauchy varianceLimit
    varianceLimit_completed_pin)
open YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit
  (singleSlice finiteScalar transferCauchy transferLimit transferLimit_completed_pin)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance
  (familyExcitation familyExcitation_norm_floor)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay (connected)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)

local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] familyExpression finiteEnergy finiteVariance finiteScalar
  normalizedEnergy oddMass middleRatio varianceCauchy varianceLimit transferCauchy transferLimit
  energy terminalMessage weightedMass spatialSpan sourcePolynomial oddVariance

private theorem half_double (a : Q') : HalfPow.half*((2 : Q')*a) ≈ a :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ a (by decide : HalfPow.half*(2 : Q') ≈ 1))
      (Q'.one_mul_eqv a))

private theorem cancel_two {a b : Q'} (h : (2 : Q')*a ≈ (2 : Q')*b) : a ≈ b :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (half_double a))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left HalfPow.half _ _ h) (half_double b))

private theorem oddVariance_congr {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) :
    oddVariance hw0 hw1 K width hK n f ≈ oddVariance hw0 hw1 K width hK n g := by
  have hm := middleRatio_congr hw0 hw1 K width hK (n+1) n h
  unfold oddVariance
  exact Q'.add_eqv_congr' (middleRatio_congr hw0 hw1 K width hK (n+1) n (h.mul h))
    (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hm) (Q'.mul_eqv_congr_left _ _ _ hm)))

private theorem normalize_ceiling {E V Z a : Q'} (hZ : (0 : Q') < Z)
    (hE : E ≤ a*(Z*V)) : E*Q'.recipPos Z hZ ≤ a*V := by
  let r := Q'.recipPos Z hZ
  have h := Q'.mul_le_mul_of_nonneg_right E (a*(Z*V)) r hE
    (Q'.le_of_lt (Q'.recipPos_pos Z hZ))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
      (fun | 0 => a | 1 => Z | 2 => V | _ => r))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
      (Q'.mul_one_eqv _))))

private theorem retained_fraction {E V B r : Q'}
    (hV : V ≈ E+B) (hE : E ≤ (1-r)*V) : r*V ≤ B := by
  have h1 : V ≤ (1-r)*V+B := Q'.le_trans' _ _ _ (Q'.le_of_eqv hV)
    (Q'.add_le_add_right _ _ B hE)
  have h2 := Q'.add_le_add_right _ _ (-((1-r)*V)) h1
  have hleft : r*V ≈ V + -((1-r)*V) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.var 1))
      (.add (.var 1) (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))))
      (by decide) (fun | 0 => r | _ => V)
  have hright : ((1-r)*V+B) + -((1-r)*V) ≈ B :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => (1-r)*V | _ => B)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hright))

private theorem scaled_stream_converges (r : Q') (f : Nat → Q') (c : QCauchy f) :
    ConvergesTo (fun n => ofQ' (r*f n)) (mul (ofQ' r) (ofQ'CauchySeq f c)) :=
  TrigAddCReal.convergesTo_congr_seq
    (fun n => (CRealAlg.ofQ'_mul r (f n)).symm)
    (convergesTo_const_mul (ofQ' r) (convergesTo_ofQ'CauchySeq f c))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {base width : Nat} (hwidth : base < width) (qs : List Z4Plaq)
  (c : Z4Plaq → Q') (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)

local notation "wideFaces" =>
  (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
local notation "e" => familyExpression width qs c wideFaces
local notation "he" => family_within width qs c wideFaces
local notation "x" => familyState width qs c wideFaces
local notation "rho" => familyResponseFraction hw0 hw1 qs.length

/-- The literal family's original finite energy is the SAME spatialSpan energy. -/
theorem finite_family_energy_pin (k t : Nat) :
    finiteEnergy hw0 hw1 e k t ≈ normalizedEnergy hw0 hw1 (headCutoff w+k) width
      (Nat.le_add_right _ _) t (spatialSpan width c qs) :=
  cancel_two (Q'.eqv_trans _ _ _
    (Q'.eqv_symm (finite_increment_pin hw0 hw1 e he k t))
    (finite_family_increment_pin hw0 hw1 width qs c wideFaces k t))

/-- All coefficients and the original moving center survive source transport. -/
theorem finite_family_variance_pin (k t : Nat) :
    finiteVariance hw0 hw1 e k t ≈ oddVariance hw0 hw1 (headCutoff w+k) width
      (Nat.le_add_right _ _) t (spatialSpan width c qs) := by
  have h := source_family_shift width qs c wideFaces 0
  simp only [shift_zero, Nat.zero_mul, liftBoundary] at h
  unfold finiteVariance
  exact oddVariance_congr hw0 hw1 _ width (Nat.le_add_right _ _) t h

/-- Width/cutoff/depth-independent fraction at fixed nome and family size.
Positive depth and one retained heat mode are explicit guards. -/
theorem finite_family_energy_band (k n : Nat) (hk : 1 ≤ k) :
    finiteEnergy hw0 hw1 e k (n+1) ≤ (1-rho)*finiteVariance hw0 hw1 e k (n+1) := by
  have hK1 : 1 ≤ headCutoff w+k := Nat.le_trans hk (Nat.le_add_left _ _)
  have hband := padded_family_energy_band hw0 hw1 (headCutoff w+k)
    (Nat.le_add_right _ _) hK1 hwidth n qs hqs c
  have hnorm : normalizedEnergy hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _)
      (n+1) (spatialSpan width c qs) ≤ (1-rho)*oddVariance hw0 hw1
        (headCutoff w+k) width (Nat.le_add_right _ _) (n+1) (spatialSpan width c qs) := by
    unfold normalizedEnergy
    exact normalize_ceiling
      (oddMass_positive hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) (n+1)) hband
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (finite_family_energy_pin hw0 hw1 hwidth qs c hqs k (n+1)))
    (Q'.le_trans' _ _ _ hnorm (Q'.ge_of_eqv
      (Q'.mul_eqv_congr_left (1-rho) _ _ (finite_family_variance_pin hw0 hw1 hwidth qs c hqs k (n+1)))))

/-- A fraction of the SAME interacting variance is retained by actual transfer. -/
theorem finite_family_bond_fraction (k n : Nat) (hk : 1 ≤ k) :
    rho*finiteVariance hw0 hw1 e k (n+1) ≤ finiteScalar hw0 hw1 e k (n+1) :=
  retained_fraction (finiteVariance_budget_pin hw0 hw1 e he k (n+1))
    (finite_family_energy_band hw0 hw1 hwidth qs c hqs k n hk)

/-- One-sided passage of the actual finite estimate through constructed limits.
The ambient norm on the left is NOT identified with the bond norm on the right. -/
theorem completed_family_bond_fraction :
    RCle (RCscale rho (completedInner hw0 hw1 (centeredVector hw0 hw1 x)
      (centeredVector hw0 hw1 x)))
      (connected hw0 hw1 0 (ofSource hw0 hw1 x) (ofSource hw0 hw1 x)) := by
  have hv : ConvergesTo (fun s => ofQ' (rho*finiteVariance hw0 hw1 e s s))
      (mul (ofQ' rho) (varianceLimit hw0 hw1 e he)) := by
    unfold varianceLimit
    exact scaled_stream_converges rho _ (varianceCauchy hw0 hw1 e he)
  have hb : ConvergesTo (fun s => ofQ' (finiteScalar hw0 hw1 e s s))
      (transferLimit hw0 hw1 e he) := by
    unfold transferLimit
    exact convergesTo_ofQ'CauchySeq _ (transferCauchy hw0 hw1 e he)
  have hlim := leEv_of_ofQ'_limit_le hv hb (fun epsilon hp =>
    ⟨1, fun s hs => by
      have h := finite_family_bond_fraction hw0 hw1 hwidth qs c hqs s (s-1) hs
      rw [Nat.sub_add_cancel hs] at h
      exact Q'.le_trans' _ _ _ h (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hp))⟩)
  have hRC : RCle (RCscale rho (Quotient.mk crealSetoid (varianceLimit hw0 hw1 e he)))
      (Quotient.mk crealSetoid (transferLimit hw0 hw1 e he)) := hlim
  rw [varianceLimit_completed_pin, transferLimit_completed_pin] at hRC
  simpa only [singleSlice, familyState] using hRC

private theorem scale_rational (r v : Q') :
    RCscale r (Quotient.mk crealSetoid (ofQ' v)) =
      Quotient.mk crealSetoid (ofQ' (r*v)) :=
  Quotient.sound (CRealAlg.ofQ'_mul r v).symm

/-- A concrete positive coefficient-square floor on the ORIGINAL physical bond
covariance. Only nome and family-list size enter the coefficient. -/
theorem family_bond_floor (hn : qs.Nodup) :
    RCle (Quotient.mk crealSetoid
      (ofQ' (rho*(varianceFloor w hw0*listQSum (fun p => c p*c p) qs))))
      (connected hw0 hw1 0 (ofSource hw0 hw1 x) (ofSource hw0 hw1 x)) := by
  have h := RCscale_mono (Q'.le_of_lt (familyResponseFraction_positive hw0 hw1 qs.length))
    (familyExcitation_norm_floor hw0 hw1 width qs c wideFaces hn)
  rw [scale_rational] at h
  exact RCle_trans h (completed_family_bond_fraction hw0 hw1 hwidth qs c hqs)

/-- Positive coefficient budget excludes a zero completed physical response.
This asserts fixed-nome nontriviality, not survival under physical scaling. -/
theorem family_bond_ne_zero (hn : qs.Nodup)
    (hc : (0 : Q') < listQSum (fun p => c p*c p) qs) :
    connected hw0 hw1 0 (ofSource hw0 hw1 x) (ofSource hw0 hw1 x) ≠ RCzero := by
  intro hz
  have h := family_bond_floor hw0 hw1 hwidth qs c hqs hn
  rw [hz] at h
  have hle : rho*(varianceFloor w hw0*listQSum (fun p => c p*c p) qs) ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon hp
    obtain ⟨N, hN⟩ := h epsilon hp
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le
      (Q'.mul_pos (familyResponseFraction_positive hw0 hw1 qs.length)
        (Q'.mul_pos (varianceFloor_positive hw0 hw1) hc)) hle)

#print axioms finite_family_energy_pin
#print axioms finite_family_variance_pin
#print axioms finite_family_energy_band
#print axioms finite_family_bond_fraction
#print axioms completed_family_bond_fraction
#print axioms family_bond_floor
#print axioms family_bond_ne_zero

end YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor
