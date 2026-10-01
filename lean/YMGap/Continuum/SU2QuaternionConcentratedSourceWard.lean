/-
# A concentrated nonnegative one-link source and its exact angular geometry

The source below is a power of the sum of the three imaginary-coordinate
squares.  On the unit-quaternion Haar carrier this sum is exactly
`1 - χ₁²/4`.  This is a one-link Haar statement, not an interacting-heat or
four-dimensional terminal-source estimate.
-/

import YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
import YMGap.Continuum.SU2QuaternionSecondOrderCancellation
import YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence
import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
import YMGap.Continuum.SU2QuaternionChannelCasimirLocality
import YMGap.Continuum.QuaternionHaarLinearAngularEnergy
import YMGap.Constructive.ExpGeomBound

namespace YMGap.Continuum.SU2QuaternionConcentratedSourceWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_coordinate)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (coordinate_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation (ratPolyPow)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation (casimir_pair_gamma)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence
  (fundamental fundamental_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private def quarter : Q' := Q'.mkPos 1 4 (by decide)

private def coordinateSquare (i : Nat) : RatPoly :=
  polyMul (polyVar i) (polyVar i)

/-- Sum of the three imaginary-coordinate squares on the original one-link
quaternion carrier. -/
def radial : RatPoly :=
  polyAdd (coordinateSquare 1)
    (polyAdd (coordinateSquare 2) (coordinateSquare 3))

/-- The concentrated source.  Its Haar-carrier value is
`(1 - fundamental²/4)^N`. -/
def source (N : Nat) : RatPoly := ratPolyPow radial N

theorem radial_supported : SupportedQuaternionBlocks 1 radial := by
  have h (i : Fin 4) : SupportedQuaternionBlocks 1 (polyVar i.val) := by
    simpa only [Nat.mul_zero, Nat.zero_add] using
      (coordinate_supported (by decide : 0 < 1) i)
  exact supported_add (supported_polyMul (h 1) (h 1))
    (supported_add (supported_polyMul (h 2) (h 2))
      (supported_polyMul (h 3) (h 3)))

theorem source_supported : ∀ N : Nat, SupportedQuaternionBlocks 1 (source N)
  | 0 => supported_one 1
  | N+1 => supported_polyMul (source_supported N) radial_supported

/-- Positivity is carried by finite square certificates, not assumed. -/
def radialCertificate : Certificate 1 radial := by
  have h (i : Fin 4) : SupportedQuaternionBlocks 1 (polyVar i.val) := by
    simpa only [Nat.mul_zero, Nat.zero_add] using
      (coordinate_supported (by decide : 0 < 1) i)
  exact .add (.square (polyVar 1) (h 1))
    (.add (.square (polyVar 2) (h 2))
      (.square (polyVar 3) (h 3)))

def sourceCertificate : ∀ N : Nat, Certificate 1 (source N)
  | 0 => .one 1
  | N+1 => (sourceCertificate N).mul radialCertificate

/-- The same source square used by the Ward moment and angular energy. -/
def sourceSquareCertificate (N : Nat) :
    Certificate 1 (polyMul (source N) (source N)) :=
  .square (source N) (source_supported N)

/-- The imaginary-square presentation equals `1 - χ₁²/4` under every
one-link Haar insertion. -/
theorem radial_carrier :
    HaarCarrierEqv 1
      (polyAdd radial (polySmul quarter (polyMul fundamental fundamental)))
      polyOne := by
  have hcoeff : RatPolyCoeffEqv
      (polyAdd radial (polySmul quarter (polyMul fundamental fundamental)))
      (polyQuaternionNorm (PolyQuaternion.coordinateVariable 0)) :=
    RatPolyCoeffEqv.of_canon_termwise (by decide)
  exact (RatPolyCoeffEqv.haarCarrier hcoeff).trans
    (haarNorm_coordinate (by decide : 0 < 1))

/-- Fixed one-link Casimir on the SAME arbitrary-insertion Haar carrier.
Raw monomial keys may be padded by angular differentiation; no false raw
coefficient equality is asserted. -/
theorem fundamental_casimir :
    HaarCarrierEqv 1
      (activeCasimirPolynomial [0] fundamental)
      (polySmul 3 fundamental) := by
  have hd : HasQuaternionBlockDegree 0 1 fundamental := by
    intro t ht
    simp only [fundamental, characterPolynomial, PolyQuaternion.coordinateVariable,
      Nat.mul_zero, polySmul, polyVar, List.map_cons, List.map_nil,
      List.mem_singleton] at ht
    subst t
    decide
  have hhead : HaarCarrierEqv 1 (blockAngularLaplacian 0 fundamental)
      (polySmul (-3) fundamental) :=
    (RatPolyCoeffEqv.haarCarrier (blockAngularLaplacian_eq_six 0 fundamental)).trans (by
      simpa only [angularLaplacian, six, blockAngularDerivative,
        Nat.mul_zero, Nat.zero_add] using
        (linear_angularLaplacian (by decide : 0 < 1) fundamental hd))
  have hlist : RatPolyCoeffEqv (activeCasimirPolynomial [0] fundamental)
      (polyNeg (blockAngularLaplacian 0 fundamental)) :=
    RatPolyCoeffEqv.add_zero _
  exact (RatPolyCoeffEqv.haarCarrier hlist).trans
    ((HaarCarrierEqv.neg hhead).trans (RatPolyCoeffEqv.haarCarrier
      ((neg_smul (polySmul (-3) fundamental)).trans
        ((RatPolyCoeffEqv.smul_assoc (-1) (-3) fundamental).trans
          (RatPolyCoeffEqv.smul_coefficient (by decide) fundamental)))))

/-- Its carré du champ is four times the imaginary-coordinate square. -/
theorem fundamental_gamma :
    RatPolyCoeffEqv
      (activeGamma [0] fundamental fundamental)
      (polySmul 4 radial) :=
  RatPolyCoeffEqv.of_canon_termwise (by decide)

/-- The radial square is an exact angular eigenfunction for the mixed
fundamental derivative, before using the sphere quotient. -/
theorem fundamental_radial_gamma :
    RatPolyCoeffEqv
      (activeGamma [0] fundamental radial)
      (polySmul (-2) (polyMul fundamental radial)) :=
  RatPolyCoeffEqv.of_canon_termwise (by decide)

/-- Exact polynomial power rule for the concentrated source.  The coefficient
`-2N` arises before any Haar integration or source normalization. -/
theorem fundamental_source_gamma : ∀ N : Nat,
    RatPolyCoeffEqv
      (activeGamma [0] fundamental (source N))
      (polySmul ((-2 : Q') * Q'.ofNat N)
        (polyMul fundamental (source N)))
  | 0 => RatPolyCoeffEqv.of_canon_termwise (by decide)
  | N+1 => by
      let q := source N
      let c : Q' := (-2) * Q'.ofNat N
      let X := polyMul fundamental (polyMul q radial)
      have hfirst : RatPolyCoeffEqv
          (polyMul (activeGamma [0] fundamental q) radial)
          (polySmul c X) :=
        ((fundamental_source_gamma N).mul_right radial).trans
          ((RatPolyCoeffEqv.polyMul_smul_left c (polyMul fundamental q) radial).trans
            ((RatPolyCoeffEqv.mul_assoc fundamental q radial).smul c))
      have hsecond : RatPolyCoeffEqv
          (polyMul q (activeGamma [0] fundamental radial))
          (polySmul (-2) X) :=
        (fundamental_radial_gamma.mul_left q).trans
          ((RatPolyCoeffEqv.polyMul_smul_right (-2) q
            (polyMul fundamental radial)).trans
              ((((RatPolyCoeffEqv.mul_assoc q fundamental radial).symm.trans
                ((RatPolyCoeffEqv.mul_comm q fundamental).mul_right radial)).trans
                  (RatPolyCoeffEqv.mul_assoc fundamental q radial)).smul (-2)))
      have hscale : c + (-2) ≈ (-2 : Q') * Q'.ofNat (N+1) :=
        Q'.eqv_symm (YMGap.Constructive.mul_ofNat_succ_eqv (-2) N)
      change RatPolyCoeffEqv
        (activeGamma [0] fundamental (polyMul q radial))
        (polySmul ((-2 : Q') * Q'.ofNat (N+1)) X)
      exact (activeGamma_mul_right [0] fundamental q radial).trans
        ((hfirst.add hsecond).trans
          ((RatPolyCoeffEqv.add_smul_same c (-2) X).trans
            (RatPolyCoeffEqv.smul_coefficient hscale X)))

/-- The square of the source has mixed angular derivative `-4N f q_N²`.
All cross terms of the actual polynomial square are retained. -/
theorem fundamental_sourceSquare_gamma (N : Nat) :
    RatPolyCoeffEqv
      (activeGamma [0] fundamental (polyMul (source N) (source N)))
      (polySmul ((-4 : Q') * Q'.ofNat N)
        (polyMul fundamental (polyMul (source N) (source N)))) := by
  let q := source N
  let c : Q' := (-2) * Q'.ofNat N
  let X := polyMul fundamental (polyMul q q)
  have hleft : RatPolyCoeffEqv
      (polyMul (activeGamma [0] fundamental q) q)
      (polySmul c X) :=
    ((fundamental_source_gamma N).mul_right q).trans
      ((RatPolyCoeffEqv.polyMul_smul_left c (polyMul fundamental q) q).trans
        ((RatPolyCoeffEqv.mul_assoc fundamental q q).smul c))
  have hright : RatPolyCoeffEqv
      (polyMul q (activeGamma [0] fundamental q))
      (polySmul c X) :=
    ((fundamental_source_gamma N).mul_left q).trans
      ((RatPolyCoeffEqv.polyMul_smul_right c q (polyMul fundamental q)).trans
        ((((RatPolyCoeffEqv.mul_assoc q fundamental q).symm.trans
          ((RatPolyCoeffEqv.mul_comm q fundamental).mul_right q)).trans
            (RatPolyCoeffEqv.mul_assoc fundamental q q)).smul c))
  have hscale : c + c ≈ (-4 : Q') * Q'.ofNat N :=
    poly_identity_of_normal_eq
      (.add (.mul (.const (-2)) (.var 0))
        (.mul (.const (-2)) (.var 0)))
      (.mul (.const (-4)) (.var 0))
      (by decide) (fun _ => Q'.ofNat N)
  exact (activeGamma_mul_right [0] fundamental q q).trans
    ((hleft.add hright).trans
      ((RatPolyCoeffEqv.add_smul_same c c X).trans
        (RatPolyCoeffEqv.smul_coefficient hscale X)))

def mass (N : Nat) : Q' :=
  H 1 (polyMul (source N) (source N))

def secondMoment (N : Nat) : Q' :=
  H 1 (polyMul (polyMul (source N) (source N))
    (polyMul fundamental fundamental))

def radialMoment (N : Nat) : Q' :=
  H 1 (polyMul (polyMul (source N) (source N)) radial)

/-- The carrier radius gives the exact relationship between the radial and
fundamental-square moments of the SAME source square. -/
theorem sphere_moment (N : Nat) :
    radialMoment N + quarter * secondMoment N ≈ mass N := by
  let W := polyMul (source N) (source N)
  have hd : H 1 (polyMul W
      (polyAdd radial (polySmul quarter (polyMul fundamental fundamental)))) ≈
      radialMoment N + quarter * secondMoment N :=
    Q'.eqv_trans _ _ _ (haar_of_coeff
      (RatPolyCoeffEqv.mul_add_right W radial
        (polySmul quarter (polyMul fundamental fundamental))))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (haar_of_coeff
            (RatPolyCoeffEqv.polyMul_smul_right quarter W
              (polyMul fundamental fundamental)))
            (quaternionHaar_polySmul 1 quarter _))))
  have hc := radial_carrier W
  have hone : H 1 (polyMul W polyOne) ≈ mass N :=
    quaternionHaar_polyMul_one_right 1 W
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hd)
    (Q'.eqv_trans _ _ _ hc hone)

/-- The signed Ward relation before eliminating the radial moment. -/
theorem ward_relation (N : Nat) :
    (3 : Q') * secondMoment N ≈
      ((-4 : Q') * Q'.ofNat N) * secondMoment N +
        4 * radialMoment N := by
  let q := source N
  let W := polyMul q q
  let c : Q' := (-4) * Q'.ofNat N
  have hleft : RatPolyCoeffEqv
      (polyMul (polyMul W fundamental)
        (polySmul 3 fundamental))
      (polySmul 3 (polyMul W (polyMul fundamental fundamental))) :=
      (RatPolyCoeffEqv.polyMul_smul_right 3
        (polyMul W fundamental) fundamental).trans
        ((RatPolyCoeffEqv.mul_assoc W fundamental fundamental).smul 3)
  have hfirst : RatPolyCoeffEqv
      (polyMul (activeGamma [0] fundamental W) fundamental)
      (polySmul c (polyMul W (polyMul fundamental fundamental))) :=
    ((fundamental_sourceSquare_gamma N).mul_right fundamental).trans
      ((RatPolyCoeffEqv.polyMul_smul_left c
        (polyMul fundamental W) fundamental).trans
        ((((RatPolyCoeffEqv.mul_comm fundamental W).mul_right fundamental).trans
          (RatPolyCoeffEqv.mul_assoc W fundamental fundamental)).smul c))
  have hsecond : RatPolyCoeffEqv
      (polyMul W (activeGamma [0] fundamental fundamental))
      (polySmul 4 (polyMul W radial)) :=
    (fundamental_gamma.mul_left W).trans
      (RatPolyCoeffEqv.polyMul_smul_right 4 W radial)
  have hright : RatPolyCoeffEqv
      (activeGamma [0] (polyMul W fundamental) fundamental)
      (polyAdd
        (polySmul c (polyMul W (polyMul fundamental fundamental)))
        (polySmul 4 (polyMul W radial))) :=
    (activeGamma_symm [0] (polyMul W fundamental) fundamental).trans
      ((activeGamma_mul_right [0] fundamental W fundamental).trans
        (hfirst.add hsecond))
  have hibp := casimir_pair_gamma 1 [0]
    (by intro i hi; have hzero : i = 0 := List.mem_singleton.mp hi
        subst i; decide)
    (polyMul W fundamental) fundamental
  have hl : H 1 (polyMul (polyMul W fundamental)
      (activeCasimirPolynomial [0] fundamental)) ≈
      3 * secondMoment N :=
    Q'.eqv_trans _ _ _ (fundamental_casimir (polyMul W fundamental))
      (Q'.eqv_trans _ _ _ (haar_of_coeff hleft)
        (quaternionHaar_polySmul 1 3 _))
  have hr : H 1 (activeGamma [0] (polyMul W fundamental) fundamental) ≈
      c * secondMoment N + 4 * radialMoment N :=
    Q'.eqv_trans _ _ _ (haar_of_coeff hright)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
        (Q'.add_eqv_congr'
          (quaternionHaar_polySmul 1 c _)
          (quaternionHaar_polySmul 1 4 _)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hl)
    (Q'.eqv_trans _ _ _ hibp hr)

private theorem ward_four_radial (N : Nat) (J R : Q')
    (hward : (3 : Q') * J ≈
      ((-4 : Q') * Q'.ofNat N) * J + 4 * R) :
    (4 : Q') * R ≈ (4 * Q'.ofNat N + 3) * J := by
  let n := Q'.ofNat N
  have hplus := Q'.add_eqv_congr' hward
    (Q'.eqv_refl (((4 : Q') * n) * J))
  have hleft : ((4 : Q') * n + 3) * J ≈
      3 * J + (4 * n) * J :=
    poly_identity_of_normal_eq
      (.mul (.add (.mul (.const 4) (.var 0)) (.const 3)) (.var 1))
      (.add (.mul (.const 3) (.var 1))
        (.mul (.mul (.const 4) (.var 0)) (.var 1)))
      (by decide) (fun | 0 => n | _ => J)
  have hright :
      (((-4 : Q') * n) * J + 4 * R) + (4 * n) * J ≈ 4 * R :=
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.mul (.const (-4)) (.var 0)) (.var 1))
          (.mul (.const 4) (.var 2)))
        (.mul (.mul (.const 4) (.var 0)) (.var 1)))
      (.mul (.const 4) (.var 2))
      (by decide) (fun | 0 => n | 1 => J | _ => R)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hplus hright))

private theorem ward_scalar (N : Nat) (Z J R : Q')
    (hsphere : R + quarter * J ≈ Z)
    (hward : (3 : Q') * J ≈
      ((-4 : Q') * Q'.ofNat N) * J + 4 * R) :
    Z ≈ Q'.ofNat (N+1) * J := by
  let n := Q'.ofNat N
  have hquarter : (4 : Q') * quarter ≈ 1 := by decide
  have hterm : (4 : Q') * (quarter * J) ≈ J :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 4 quarter J))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (4 * quarter) 1 J hquarter)
        (Q'.one_mul_eqv J))
  have hfourSphere : (4 : Q') * Z ≈ 4 * R + J := by
    have hscaled := Q'.mul_eqv_congr_left 4 _ _ hsphere
    have hsplit : (4 : Q') * (R + quarter * J) ≈ 4 * R + J :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv 4 R (quarter * J))
        (Q'.add_eqv_congr' (Q'.eqv_refl _) hterm)
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hscaled) hsplit
  have hfourWard : (4 : Q') * R ≈ (4 * n + 3) * J :=
    ward_four_radial N J R hward
  have hlast : ((4 : Q') * n + 3) * J + J ≈
      4 * ((n + 1) * J) :=
    poly_identity_of_normal_eq
      (.add (.mul (.add (.mul (.const 4) (.var 0)) (.const 3)) (.var 1))
        (.var 1))
      (.mul (.const 4) (.mul (.add (.var 0) (.const 1)) (.var 1)))
      (by decide) (fun | 0 => n | _ => J)
  have hnat : n + 1 ≈ Q'.ofNat (N+1) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left n (1 : Q') (Q'.ofNat 1) (by decide))
      (Q'.eqv_symm (Q'.ofNat_add_eqv N 1))
  have hfour : (4 : Q') * Z ≈ 4 * (Q'.ofNat (N+1) * J) :=
    Q'.eqv_trans _ _ _ hfourSphere
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hfourWard (Q'.eqv_refl J))
        (Q'.eqv_trans _ _ _ hlast
          (Q'.mul_eqv_congr_left 4 _ _
            (Q'.mul_eqv_congr_right (n+1) (Q'.ofNat (N+1)) J hnat))))
  exact Q'.mul_left_cancel_of_pos (by decide : (0 : Q') < 4) hfour

/-- Exact one-link Ward moment for the square of the positive concentrated
source.  No finite-nome interacting mean occurs in this statement. -/
theorem sourceSquare_moment (N : Nat) :
    mass N ≈ Q'.ofNat (N+1) * secondMoment N :=
  ward_scalar N (mass N) (secondMoment N) (radialMoment N)
    (sphere_moment N) (ward_relation N)

/-- Exact one-link angular coefficient of the same positive source square.
The factor `4N+3` is a rational Haar identity, not a finite-nome
interacting-energy bound. -/
theorem sourceSquare_angular (N : Nat) :
    weightedAngularEnergy 0 (source N) fundamental ≈
      ((4 : Q') * Q'.ofNat N + 3) * secondMoment N := by
  let W := polyMul (source N) (source N)
  have hfixed : RatPolyCoeffEqv
      (blockAngularSquare 0 fundamental)
      (polySmul 4 radial) :=
    RatPolyCoeffEqv.of_canon_termwise (by decide)
  have hone : weightedAngularEnergy 0 (source N) fundamental ≈
      H 1 (polyMul W (blockAngularSquare 0 fundamental)) := by
    change (0 : Q') + H 1 (polyMul W
      (blockAngularSquare 0 fundamental)) ≈ _
    exact QPoly.q_zero_add_eqv _
  have hgamma : H 1 (polyMul W (blockAngularSquare 0 fundamental)) ≈
      4 * radialMoment N :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (hfixed.mul_left W))
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right 4 W radial))
        (quaternionHaar_polySmul 1 4 _))
  exact Q'.eqv_trans _ _ _ hone
    (Q'.eqv_trans _ _ _ hgamma
      (ward_four_radial N (secondMoment N) (radialMoment N)
        (ward_relation N)))

end YMGap.Continuum.SU2QuaternionConcentratedSourceWard

#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.radial_supported
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.source_supported
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.radialCertificate
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.sourceCertificate
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.sourceSquareCertificate
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.radial_carrier
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.fundamental_casimir
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.fundamental_gamma
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.fundamental_radial_gamma
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.fundamental_source_gamma
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.fundamental_sourceSquare_gamma
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.sphere_moment
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.ward_relation
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.sourceSquare_moment
#print axioms YMGap.Continuum.SU2QuaternionConcentratedSourceWard.sourceSquare_angular
