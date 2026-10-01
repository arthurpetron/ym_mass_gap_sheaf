/-
# Positive spectator mass is not uniformly retained by independent heat

The SAME source is inserted at both ends of each actual one-link SU(2)
heat kernel, with nome 1/2 and cutoff 3. Ordered pairs of quaternion blocks
are independent copies, not a replacement scalar model. Their exact bare
square and heat pairing are (17/16)^m and (4097/4096)^m. A computed exponent
refutes every nonnegative extent-independent retention constant.

This rules out promoting positivity and selected-link independence alone
to a width-free spectator L2/heat comparison. These sources are NOT pinned
to the four-dimensional terminal recursion; no actual terminal estimate,
scaling trajectory, continuum limit or mass-gap claim is refuted here.
-/

import YMGap.Continuum.SU2QuaternionSourceDefectSignFence
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Constructive.RatNat

namespace YMGap.Continuum.SU2QuaternionSpectatorHeatRetentionFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (partialHaarHeads_supported_constant)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarKernelBound (haar_liftBoundary)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence (half)
open YMGap.Continuum.SU2QuaternionSourceDefectSignFence
  (sourcePlus sourcePlus_supported sourcePlusCertificate sourceMass plusMass_value)
open YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate
  (heatAt_half_three_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv

/-- Place independent copies on successive literal pairs (0,1),(2,3),.... -/
def pairProduct (p : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | m+1 => polyMul p (liftBoundary 2 (pairProduct p m))

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p := by
  intro t ht
  exact Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 hle)

theorem pairProduct_supported {p : RatPoly} (hp : SupportedQuaternionBlocks 2 p) :
    ∀ m, SupportedQuaternionBlocks (2*m) (pairProduct p m)
  | 0 => supported_one _
  | m+1 => by
      have ht := lift_supported (pairProduct_supported hp m) 2
      simpa only [Nat.mul_succ] using supported_polyMul
        (support_mono hp (by omega : 2 ≤ 2*m+2)) ht

/-- Explicit polynomial positivity is preserved, including all insertions. -/
def pairProductCertificate {p : RatPoly} (hp : SupportedQuaternionBlocks 2 p)
    (P : Certificate 2 p) : ∀ m, Certificate (2*m) (pairProduct p m)
  | 0 => .one _
  | m+1 => by
      have hhead := certificate_extend (2*m) hp P
      have htail := lift_certificate 2 (pairProductCertificate hp P m)
      have hh : Certificate (2*m+2) p := by
        simpa only [Nat.add_comm 2 (2*m)] using hhead
      simpa only [Nat.mul_succ] using hh.mul htail

/-- Tensorization keeps both copies of a source in the actual integrand. -/
theorem pairProduct_mul (p q : RatPoly) : ∀ m,
    RatPolyCoeffEqv (pairProduct (polyMul p q) m)
      (polyMul (pairProduct p m) (pairProduct q m))
  | 0 => (RatPolyCoeffEqv.one_mul polyOne).symm
  | m+1 => by
      change RatPolyCoeffEqv
        (polyMul (polyMul p q) (liftBoundary 2 (pairProduct (polyMul p q) m)))
        (polyMul (polyMul p (liftBoundary 2 (pairProduct p m)))
          (polyMul q (liftBoundary 2 (pairProduct q m))))
      refine (RatPolyCoeffEqv.mul_left _ (lift_coeff 2 (pairProduct_mul p q m))).trans ?_
      rw [lift_product]
      exact RatPolyCoeffEqv.mul_four_swap _ _ _ _

/-- Exact ordered Fubini, with no norm comparison assumption. -/
theorem haar_pairProduct {p : RatPoly} (hp : SupportedQuaternionBlocks 2 p) :
    ∀ m, quaternionHaar (2*m) (pairProduct p m) ≈ (quaternionHaar 2 p)^m
  | 0 => by
      change quaternionHaar 0 polyOne ≈ (1 : Q')
      decide
  | m+1 => by
      have h := head_pairing (2*m) 2 p (pairProduct p m)
      have hc := (partialHaarHeads_supported_constant 2 hp).mul_right (pairProduct p m)
      have hr := Q'.eqv_trans _ _ _ (haar_of_coeff hc)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left _ _))
          (quaternionHaar_polySmul (2*m) _ _))
      have hi : (quaternionHaar 2 p)*quaternionHaar (2*m) (pairProduct p m) ≈
          (quaternionHaar 2 p)*(quaternionHaar 2 p)^m :=
        Q'.mul_eqv_congr_left _ _ _ (haar_pairProduct hp m)
      simpa only [pairProduct, Nat.mul_succ, Q'.pow_succ] using
        Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _ hr hi)

def sourceSeed : RatPoly := sourcePlus
def upperSourceSeed : RatPoly := liftBoundary 1 sourceSeed
def heatSeed : RatPoly := heatAt 0 1 half 3
def pairingSeed : RatPoly := polyMul heatSeed (polyMul sourceSeed upperSourceSeed)

theorem sourceSeed_supported : SupportedQuaternionBlocks 2 sourceSeed :=
  support_mono sourcePlus_supported (by decide)

theorem upperSourceSeed_supported : SupportedQuaternionBlocks 2 upperSourceSeed :=
  lift_supported sourcePlus_supported 1

theorem heatSeed_supported : SupportedQuaternionBlocks 2 heatSeed :=
  heat_supported (by decide) (by decide) half 3

theorem pairingSeed_supported : SupportedQuaternionBlocks 2 pairingSeed :=
  supported_polyMul heatSeed_supported
    (supported_polyMul sourceSeed_supported upperSourceSeed_supported)

def sourceSeedCertificate : Certificate 2 sourceSeed :=
  certificate_extend 1 sourcePlus_supported sourcePlusCertificate

def pairingSeedCertificate : Certificate 2 pairingSeed :=
  heatAt_half_three_certificate.mul
    (sourceSeedCertificate.mul (lift_certificate 1 sourcePlusCertificate))

def bareFactor : Q' := Q'.mkPos 17 16 (by decide)
def heatFactor : Q' := Q'.mkPos 4097 4096 (by decide)
def ratio : Q' := Q'.mkPos 4352 4097 (by decide)

set_option maxRecDepth 100000 in
theorem sourceSeed_square_value :
    quaternionHaar 2 (polyMul sourceSeed sourceSeed) ≈ bareFactor := by decide

/-- The seed denominator is precisely the existing one-link q*P(q) mass. -/
theorem pairingSeed_mass_pin : quaternionHaar 2 pairingSeed ≈ sourceMass sourcePlus := by
  have hk : RatPolyCoeffEqv (productHeat 1 half 3 [0]) heatSeed :=
    RatPolyCoeffEqv.mul_one _
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (hk.mul_right (polyMul sourceSeed upperSourceSeed)).symm)
    (Q'.eqv_symm (productMap_pairing 1 half 3 [0] sourcePlus sourcePlus))

theorem pairingSeed_value : quaternionHaar 2 pairingSeed ≈ heatFactor :=
  Q'.eqv_trans _ _ _ pairingSeed_mass_pin plusMass_value

def spectator (m : Nat) : RatPoly := pairProduct sourceSeed m
def upperSpectator (m : Nat) : RatPoly := pairProduct upperSourceSeed m
def pairedHeat (m : Nat) : RatPoly := pairProduct heatSeed m

def bareMass (m : Nat) : Q' :=
  quaternionHaar (2*m) (polyMul (spectator m) (spectator m))

/-- The literal heat product and SAME spectator at both endpoints. Blocks
are interleaved pairs; no four-dimensional terminal identification is asserted. -/
def pairedMass (m : Nat) : Q' := quaternionHaar (2*m)
  (polyMul (pairedHeat m) (polyMul (spectator m) (upperSpectator m)))

def spectatorCertificate (m : Nat) : Certificate (2*m) (spectator m) :=
  pairProductCertificate sourceSeed_supported sourceSeedCertificate m

def pairedDensityCertificate (m : Nat) : Certificate (2*m)
    (polyMul (pairedHeat m) (polyMul (spectator m) (upperSpectator m))) :=
  .ofCoeff ((pairProduct_mul heatSeed (polyMul sourceSeed upperSourceSeed) m).trans
    ((RatPolyCoeffEqv.refl _).mul (pairProduct_mul sourceSeed upperSourceSeed m))).symm
    (pairProductCertificate pairingSeed_supported pairingSeedCertificate m)

theorem bareMass_value (m : Nat) : bareMass m ≈ bareFactor^m :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (pairProduct_mul sourceSeed sourceSeed m).symm)
    (Q'.eqv_trans _ _ _
      (haar_pairProduct (supported_polyMul sourceSeed_supported sourceSeed_supported) m)
      (ClusteringImpliesGap.pow_eqv_congr _ _ sourceSeed_square_value m))

theorem pairedMass_value (m : Nat) : pairedMass m ≈ heatFactor^m :=
  Q'.eqv_trans _ _ _ (haar_of_coeff
    ((pairProduct_mul heatSeed (polyMul sourceSeed upperSourceSeed) m).trans
      ((RatPolyCoeffEqv.refl _).mul (pairProduct_mul sourceSeed upperSourceSeed m))).symm)
    (Q'.eqv_trans _ _ _ (haar_pairProduct pairingSeed_supported m)
      (ClusteringImpliesGap.pow_eqv_congr _ _ pairingSeed_value m))

theorem pairedMass_positive (m : Nat) : (0 : Q') < pairedMass m :=
  ClusteringImpliesGap.lt_of_lt_of_le
    (ClusteringImpliesGap.pow_pos (by decide : (0 : Q') < heatFactor) m)
    (Q'.ge_of_eqv (pairedMass_value m))

/-- Every fixed selected footprint is genuinely disjoint from this source. -/
def outsideSpectator (footprint m : Nat) : RatPoly :=
  liftBoundary footprint (spectator m)

theorem outsideSpectator_independent (footprint m i : Nat) (hi : i < footprint) :
    QuaternionBlockIndependent i (outsideSpectator footprint m) :=
  lift_lower_independent footprint (spectator m) i hi

def outsideSpectatorCertificate (footprint m : Nat) :
    Certificate (2*m+footprint) (outsideSpectator footprint m) :=
  lift_certificate footprint (spectatorCertificate m)

def outsideBareMass (footprint m : Nat) : Q' := quaternionHaar (2*m+footprint)
  (polyMul (outsideSpectator footprint m) (outsideSpectator footprint m))

def outsidePairedMass (footprint m : Nat) : Q' := quaternionHaar (2*m+footprint)
  (polyMul (liftBoundary footprint (pairedHeat m))
    (polyMul (outsideSpectator footprint m) (liftBoundary footprint (upperSpectator m))))

theorem outsideBareMass_pin (footprint m : Nat) : outsideBareMass footprint m ≈ bareMass m := by
  unfold outsideBareMass outsideSpectator
  rw [← lift_product]
  exact haar_liftBoundary footprint (2*m) _

theorem outsidePairedMass_pin (footprint m : Nat) : outsidePairedMass footprint m ≈ pairedMass m := by
  unfold outsidePairedMass outsideSpectator
  rw [← lift_product, ← lift_product]
  exact haar_liftBoundary footprint (2*m) _

private theorem one_pow (m : Nat) : ((1 : Q')^m) ≈ 1 := by
  induction m with
  | zero => exact Q'.eqv_refl _
  | succ m ih => exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ih

/-- Computed extent: there is no erased existential choice of a large volume. -/
def escapeExponent (C : Q') : Nat := 17*C.num.toNat+1

theorem ratio_escapes (C : Q') (hC : (0 : Q') ≤ C) : C < ratio^(escapeExponent C) := by
  let n := C.num.toNat
  let d : Q' := Q'.mkPos 255 4097 (by decide)
  have hg := ClusteringImpliesGap.pow_ge_linear 1 d (by decide) (by decide) (17*n)
  have hlinear : (Q'.ofNat (17*n+1)) * (d*((1 : Q')^(17*n))) ≈
      (Q'.ofNat (17*n+1))*d :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (one_pow _)))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv d))
  have hbase : (1 : Q')+d ≈ ratio := by decide
  have hb : (Q'.ofNat (17*n+1))*d ≤ ratio^(17*n+1) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hlinear)
      (Q'.le_trans' _ _ _ hg
        (Q'.le_of_eqv (ClusteringImpliesGap.pow_eqv_congr _ _ hbase _)))
  have hn : Q'.ofNat n < (Q'.ofNat (17*n+1))*d := by
    show (Q'.ofNat n).num * (((Q'.ofNat (17*n+1))*d).den : Int) <
      ((Q'.ofNat (17*n+1))*d).num * ((Q'.ofNat n).den : Int)
    rw [Q'.mul_den_cast]
    change (n : Int)*(1*4097) < ((((17*n+1 : Nat) : Int)*255)*1)
    simp only [Int.natCast_add, Int.natCast_mul,
      Int.one_mul, Int.mul_one]
    omega
  exact ClusteringImpliesGap.lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (RatNat.le_ofNat_toNat C hC) hn) hb

private theorem factors_power (m : Nat) : bareFactor^m ≈ ratio^m*heatFactor^m := by
  induction m with
  | zero => exact Q'.eqv_symm (Q'.one_mul_eqv 1)
  | succ m ih =>
      have hbase : bareFactor ≈ ratio*heatFactor := by decide
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ih)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hbase)
          (poly_identity_of_normal_eq
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
            (by decide) (fun
              | 0 => ratio
              | 1 => heatFactor
              | 2 => ratio^m
              | _ => heatFactor^m)))

theorem retention_failure (C : Q') (hC : (0 : Q') ≤ C) :
    C*pairedMass (escapeExponent C) < bareMass (escapeExponent C) := by
  let m := escapeExponent C
  have h := ClusteringImpliesGap.mul_lt_mul_of_pos_right
    (ClusteringImpliesGap.pow_pos (by decide : (0 : Q') < heatFactor) m)
    (ratio_escapes C hC)
  have hl : C*pairedMass m ≈ C*heatFactor^m :=
    Q'.mul_eqv_congr_left _ _ _ (pairedMass_value m)
  have hr : bareMass m ≈ ratio^m*heatFactor^m :=
    Q'.eqv_trans _ _ _ (bareMass_value m) (factors_power m)
  exact Q'.lt_of_le_of_lt (Q'.le_of_eqv hl)
    (ClusteringImpliesGap.lt_of_lt_of_le h (Q'.ge_of_eqv hr))

def retentionCounterexample (C : Q') (hC : (0 : Q') ≤ C) :
    Σ' m : Nat, C*pairedMass m < bareMass m :=
  ⟨escapeExponent C, retention_failure C hC⟩

theorem no_uniform_heat_retention (C : Q') (hC : (0 : Q') ≤ C) :
    ¬ (∀ m, bareMass m ≤ C*pairedMass m) := by
  intro h
  exact (Int.not_le.mpr (retention_failure C hC)) (h (escapeExponent C))

/-- Adding independence from ANY fixed footprint does not repair retention. -/
theorem outside_retention_failure (footprint : Nat) (C : Q') (hC : (0 : Q') ≤ C) :
    C*outsidePairedMass footprint (escapeExponent C) < outsideBareMass footprint (escapeExponent C) :=
  Q'.lt_of_le_of_lt (Q'.le_of_eqv
    (Q'.mul_eqv_congr_left _ _ _ (outsidePairedMass_pin footprint _)))
    (ClusteringImpliesGap.lt_of_lt_of_le (retention_failure C hC)
      (Q'.ge_of_eqv (outsideBareMass_pin footprint _)))

#print axioms pairProduct
#print axioms pairProduct_supported
#print axioms pairProductCertificate
#print axioms pairProduct_mul
#print axioms haar_pairProduct
#print axioms sourceSeedCertificate
#print axioms pairingSeedCertificate
#print axioms sourceSeed_square_value
#print axioms pairingSeed_mass_pin
#print axioms pairingSeed_value
#print axioms spectatorCertificate
#print axioms pairedDensityCertificate
#print axioms bareMass_value
#print axioms pairedMass_value
#print axioms pairedMass_positive
#print axioms outsideSpectator_independent
#print axioms outsideSpectatorCertificate
#print axioms outsideBareMass_pin
#print axioms outsidePairedMass_pin
#print axioms escapeExponent
#print axioms ratio_escapes
#print axioms retention_failure
#print axioms retentionCounterexample
#print axioms no_uniform_heat_retention
#print axioms outside_retention_failure

end YMGap.Continuum.SU2QuaternionSpectatorHeatRetentionFence
