/-
# Strict one-link moments of the concentrated radial source

The strict mass and zero first moment below follow from exact Haar Ward
identities.  They are not finite-nome interacting-source assertions.
-/

import YMGap.Continuum.SU2QuaternionConcentratedSourceWard

namespace YMGap.Continuum.SU2QuaternionConcentratedSourceMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation (ratPolyPow)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation (casimir_pair_gamma)
open YMGap.Continuum.SU2QuaternionConcentratedSourceWard
open YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence (fundamental)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QPolyHaarPositiveSubstitution (haar_one)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- Haar mass of a single radial power, prior to squaring the source. -/
def radialMass (k : Nat) : Q' := H 1 (source k)

/-- Its fundamental-character second moment. -/
def radialSecond (k : Nat) : Q' :=
  H 1 (polyMul (source k) (polyMul fundamental fundamental))

/-- The carrier sphere equation for any radial power. -/
theorem radial_sphere (k : Nat) :
    radialMass (k+1) + quarter * radialSecond k ≈ radialMass k := by
  let W := source k
  have hd : H 1 (polyMul W
      (polyAdd radial (polySmul quarter (polyMul fundamental fundamental)))) ≈
      radialMass (k+1) + quarter * radialSecond k := by
    have hsplit := RatPolyCoeffEqv.mul_add_right W radial
      (polySmul quarter (polyMul fundamental fundamental))
    have hfirst : H 1 (polyMul W radial) ≈ radialMass (k+1) :=
      Q'.eqv_refl _
    have hsecond : H 1 (polyMul W
        (polySmul quarter (polyMul fundamental fundamental))) ≈
        quarter * radialSecond k :=
      Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right quarter W
          (polyMul fundamental fundamental)))
        (quaternionHaar_polySmul 1 quarter _)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hsplit)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
        (Q'.add_eqv_congr' hfirst hsecond))
  have hc := radial_carrier W
  have hone : H 1 (polyMul W polyOne) ≈ radialMass k :=
    quaternionHaar_polyMul_one_right 1 W
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hd)
    (Q'.eqv_trans _ _ _ hc hone)

/-- One Ward step for a single radial power.  The square-source identity in
the preceding module is its even-exponent specialization. -/
theorem radial_ward (k : Nat) :
    (3 : Q') * radialSecond k ≈
      ((-2 : Q') * Q'.ofNat k) * radialSecond k +
        4 * radialMass (k+1) := by
  let W := source k
  let c : Q' := (-2) * Q'.ofNat k
  have hfirst : RatPolyCoeffEqv
      (polyMul (activeGamma [0] fundamental W) fundamental)
      (polySmul c (polyMul W (polyMul fundamental fundamental))) :=
    ((fundamental_source_gamma k).mul_right fundamental).trans
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
  have hactive : ∀ i, i ∈ [0] → i < 1 := by
    intro i hi
    have hzero : i = 0 := List.mem_singleton.mp hi
    subst i
    decide
  have hibp := casimir_pair_gamma 1 [0] hactive
    (polyMul W fundamental) fundamental
  have hl : H 1 (polyMul (polyMul W fundamental)
      (activeCasimirPolynomial [0] fundamental)) ≈
      3 * radialSecond k := by
    have hc := fundamental_casimir (polyMul W fundamental)
    have hreorder : RatPolyCoeffEqv
        (polyMul (polyMul W fundamental) (polySmul 3 fundamental))
        (polySmul 3 (polyMul W (polyMul fundamental fundamental))) :=
      (RatPolyCoeffEqv.polyMul_smul_right 3
        (polyMul W fundamental) fundamental).trans
        ((RatPolyCoeffEqv.mul_assoc W fundamental fundamental).smul 3)
    exact Q'.eqv_trans _ _ _ hc
      (Q'.eqv_trans _ _ _ (haar_of_coeff hreorder)
        (quaternionHaar_polySmul 1 3 _))
  have hr : H 1 (activeGamma [0] (polyMul W fundamental) fundamental) ≈
      c * radialSecond k + 4 * radialMass (k+1) := by
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hright)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
        (Q'.add_eqv_congr'
          (quaternionHaar_polySmul 1 c _)
          (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 1 4 _)
            (Q'.mul_eqv_congr_left 4 _ _ (Q'.eqv_refl _)))))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hl)
    (Q'.eqv_trans _ _ _ hibp hr)

private theorem pos_of_eqv {a b : Q'}
    (ha : (0 : Q') < a) (hab : a ≈ b) : (0 : Q') < b := by
  have haNum : (0 : Int) < a.num := Q'.num_pos_of_pos ha
  have heq : a.num * (b.den : Int) = b.num * (a.den : Int) := hab
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have had : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have hprod : 0 < b.num * (a.den : Int) := by
    rw [← heq]
    exact Int.mul_pos haNum hbd
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hb
  have hcontra : b.num * (a.den : Int) ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hb (Int.le_of_lt had)
  exact (Int.not_lt_of_ge hcontra) hprod

private theorem right_pos_of_mul_pos {a b : Q'}
    (ha : (0 : Q') < a) (hab : (0 : Q') < a * b) :
    (0 : Q') < b := by
  have hprod : 0 < a.num * b.num := Q'.num_pos_of_pos hab
  have haNum : 0 ≤ a.num := Int.le_of_lt (Q'.num_pos_of_pos ha)
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hb
  have hcontra : a.num * b.num ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos haNum hb
  exact (Int.not_lt_of_ge hcontra) hprod

private theorem linear_pos (k : Nat) (constant : Q')
    (hc : (0 : Q') < constant) :
    (0 : Q') < (2 : Q') * Q'.ofNat k + constant := by
  have hnonneg : (0 : Q') ≤ (2 : Q') * Q'.ofNat k :=
    Q'.mul_nonneg 2 (Q'.ofNat k) (by decide)
      (YMGap.Constructive.ofNat_nonneg k)
  exact pos_of_eqv (Q'.pos_add_nonneg hc hnonneg)
    (Q'.add_comm_eqv constant (2 * Q'.ofNat k))

private theorem radial_scalar_step (k : Nat) (Z J R : Q')
    (hsphere : R + quarter * J ≈ Z)
    (hward : (3 : Q') * J ≈
      ((-2 : Q') * Q'.ofNat k) * J + 4 * R) :
    ((2 : Q') * Q'.ofNat k + 4) * R ≈
      ((2 : Q') * Q'.ofNat k + 3) * Z := by
  let n := Q'.ofNat k
  let A : Q' := 2 * n + 3
  let B : Q' := 2 * n + 4
  have hquarter : (4 : Q') * quarter ≈ 1 := by decide
  have hterm : (4 : Q') * (quarter * J) ≈ J :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 4 quarter J))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (4 * quarter) 1 J hquarter)
        (Q'.one_mul_eqv J))
  have h4sphere : (4 : Q') * Z ≈ 4 * R + J := by
    have hscaled := Q'.mul_eqv_congr_left 4 _ _ hsphere
    have hsplit : (4 : Q') * (R + quarter * J) ≈ 4 * R + J :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv 4 R (quarter * J))
        (Q'.add_eqv_congr' (Q'.eqv_refl _) hterm)
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hscaled) hsplit
  have hplus := Q'.add_eqv_congr' hward
    (Q'.eqv_refl (((2 : Q') * n) * J))
  have h4ward : (4 : Q') * R ≈ A * J := by
    have hleft : A * J ≈ 3 * J + (2 * n) * J :=
      poly_identity_of_normal_eq
        (.mul (.add (.mul (.const 2) (.var 0)) (.const 3)) (.var 1))
        (.add (.mul (.const 3) (.var 1))
          (.mul (.mul (.const 2) (.var 0)) (.var 1)))
        (by decide) (fun | 0 => n | _ => J)
    have hright :
        (((-2 : Q') * n) * J + 4 * R) + (2 * n) * J ≈ 4 * R :=
      poly_identity_of_normal_eq
        (.add
          (.add (.mul (.mul (.const (-2)) (.var 0)) (.var 1))
            (.mul (.const 4) (.var 2)))
          (.mul (.mul (.const 2) (.var 0)) (.var 1)))
        (.mul (.const 4) (.var 2))
        (by decide) (fun | 0 => n | 1 => J | _ => R)
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hleft
      (Q'.eqv_trans _ _ _ hplus hright))
  have h4Z : (4 : Q') * Z ≈ B * J := by
    have hlast : A * J + J ≈ B * J :=
      poly_identity_of_normal_eq
        (.add
          (.mul (.add (.mul (.const 2) (.var 0)) (.const 3)) (.var 1))
          (.var 1))
        (.mul (.add (.mul (.const 2) (.var 0)) (.const 4)) (.var 1))
        (by decide) (fun | 0 => n | _ => J)
    exact Q'.eqv_trans _ _ _ h4sphere
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' h4ward (Q'.eqv_refl J)) hlast)
  have hleft : (4 : Q') * (B * R) ≈ B * (4 * R) :=
    poly_identity_of_normal_eq
      (.mul (.const 4) (.mul (.var 0) (.var 1)))
      (.mul (.var 0) (.mul (.const 4) (.var 1)))
      (by decide) (fun | 0 => B | _ => R)
  have hmiddle : B * (A * J) ≈ A * (B * J) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => B | 1 => A | _ => J)
  have hright : A * (4 * Z) ≈ (4 : Q') * (A * Z) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.const 4) (.var 1)))
      (.mul (.const 4) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => A | _ => Z)
  have hscaled : (4 : Q') * (B * R) ≈ 4 * (A * Z) :=
    Q'.eqv_trans _ _ _ hleft
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left B _ _ h4ward)
        (Q'.eqv_trans _ _ _ hmiddle
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left A _ _ (Q'.eqv_symm h4Z)) hright)))
  exact Q'.mul_left_cancel_of_pos (by decide : (0 : Q') < 4) hscaled

/-- Exact ratio recurrence; both rational coefficients are positive. -/
theorem radialMass_step (k : Nat) :
    ((2 : Q') * Q'.ofNat k + 4) * radialMass (k+1) ≈
      ((2 : Q') * Q'.ofNat k + 3) * radialMass k :=
  radial_scalar_step k (radialMass k) (radialSecond k)
    (radialMass (k+1)) (radial_sphere k) (radial_ward k)

/-- Strict positivity comes from the Ward recurrence and normalized Haar
mass at exponent zero, without expanding high-degree monomials. -/
theorem radialMass_pos : ∀ k : Nat, (0 : Q') < radialMass k
  | 0 => by
      have h : radialMass 0 ≈ (1 : Q') := by
        change H 1 polyOne ≈ (1 : Q')
        exact haar_one 1
      exact pos_of_eqv (by decide : (0 : Q') < 1) (Q'.eqv_symm h)
  | k+1 => by
      let A : Q' := 2 * Q'.ofNat k + 3
      let B : Q' := 2 * Q'.ofNat k + 4
      have hA : (0 : Q') < A := linear_pos k 3 (by decide)
      have hB : (0 : Q') < B := linear_pos k 4 (by decide)
      have hright : (0 : Q') < A * radialMass k :=
        Q'.mul_pos hA (radialMass_pos k)
      have hleft : (0 : Q') < B * radialMass (k+1) :=
        pos_of_eqv hright (Q'.eqv_symm (radialMass_step k))
      exact right_pos_of_mul_pos hB hleft

private theorem source_coeffPow : ∀ k : Nat,
    source k = coeffPolyPow radial k
  | 0 => rfl
  | k+1 => by
      change polyMul (source k) radial =
        polyMul (coeffPolyPow radial k) radial
      rw [source_coeffPow k]

/-- Exact coefficient power-add law, with no sphere reduction. -/
theorem source_power_add (a b : Nat) :
    RatPolyCoeffEqv (polyMul (source a) (source b))
      (source (a+b)) := by
  rw [source_coeffPow a, source_coeffPow b, source_coeffPow (a+b)]
  exact (coeffPolyPow_add radial a b).symm

/-- The Haar mass of the actual source square is a radial power mass. -/
theorem mass_eq_radialMass (N : Nat) :
    mass N ≈ radialMass (N+N) :=
  haar_of_coeff (source_power_add N N)

theorem mass_pos (N : Nat) : (0 : Q') < mass N :=
  pos_of_eqv (radialMass_pos (N+N))
    (Q'.eqv_symm (mass_eq_radialMass N))

/-- The second moment used by the exact angular Ward law is strictly
positive; there is no hidden nondegeneracy hypothesis. -/
theorem secondMoment_pos (N : Nat) : (0 : Q') < secondMoment N := by
  have hfactor : (0 : Q') < Q'.ofNat (N+1) := Q'.ofNat_succ_pos N
  have hprod : (0 : Q') < Q'.ofNat (N+1) * secondMoment N :=
    pos_of_eqv (mass_pos N) (sourceSquare_moment N)
  exact right_pos_of_mul_pos hfactor hprod

/-- The source is radial and its original one-link Haar first moment
against the fundamental character vanishes by Ward, without a parity
expansion. -/
def firstMoment (N : Nat) : Q' :=
  H 1 (polyMul (polyMul (source N) (source N)) fundamental)

theorem firstMoment_zero (N : Nat) : firstMoment N ≈ 0 := by
  let W := polyMul (source N) (source N)
  let c : Q' := (-4) * Q'.ofNat N
  let M := firstMoment N
  have hactive : ∀ i, i ∈ [0] → i < 1 := by
    intro i hi
    have hzero : i = 0 := List.mem_singleton.mp hi
    subst i
    decide
  have hibp := casimir_pair_gamma 1 [0] hactive W fundamental
  have hl : H 1 (polyMul W (activeCasimirPolynomial [0] fundamental)) ≈
      3 * M := by
    exact Q'.eqv_trans _ _ _ (fundamental_casimir W)
      (Q'.eqv_trans _ _ _
        (haar_of_coeff
          (RatPolyCoeffEqv.polyMul_smul_right 3 W fundamental))
        (quaternionHaar_polySmul 1 3 _))
  have hgamma : RatPolyCoeffEqv
      (activeGamma [0] W fundamental)
      (polySmul c (polyMul W fundamental)) :=
    (activeGamma_symm [0] W fundamental).trans
      ((fundamental_sourceSquare_gamma N).trans
        ((RatPolyCoeffEqv.mul_comm fundamental W).smul c))
  have hr : H 1 (activeGamma [0] W fundamental) ≈ c * M :=
    Q'.eqv_trans _ _ _ (haar_of_coeff hgamma)
      (quaternionHaar_polySmul 1 c _)
  have hward : (3 : Q') * M ≈ c * M :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hl)
      (Q'.eqv_trans _ _ _ hibp hr)
  let n := Q'.ofNat N
  have hplus := Q'.add_eqv_congr' hward
    (Q'.eqv_refl (((4 : Q') * n) * M))
  have hleft : ((4 : Q') * n + 3) * M ≈
      3 * M + (4 * n) * M :=
    poly_identity_of_normal_eq
      (.mul (.add (.mul (.const 4) (.var 0)) (.const 3)) (.var 1))
      (.add (.mul (.const 3) (.var 1))
        (.mul (.mul (.const 4) (.var 0)) (.var 1)))
      (by decide) (fun | 0 => n | _ => M)
  have hright :
      (((-4 : Q') * n) * M + (4 * n) * M) ≈ 0 :=
    poly_identity_of_normal_eq
      (.add
        (.mul (.mul (.const (-4)) (.var 0)) (.var 1))
        (.mul (.mul (.const 4) (.var 0)) (.var 1)))
      (.const 0)
      (by decide) (fun | 0 => n | _ => M)
  have hzero : ((4 : Q') * n + 3) * M ≈ 0 :=
    Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _ hplus hright)
  have hcoefficient : (0 : Q') < (4 : Q') * n + 3 := by
    have hn : (0 : Q') ≤ n := YMGap.Constructive.ofNat_nonneg N
    have h4n : (0 : Q') ≤ (4 : Q') * n :=
      Q'.mul_nonneg 4 n (by decide) hn
    exact pos_of_eqv (Q'.pos_add_nonneg
      (by decide : (0 : Q') < 3) h4n)
      (Q'.add_comm_eqv 3 (4*n))
  exact Q'.mul_eqv_zero_of_pos hcoefficient hzero

#print axioms radialMass_step
#print axioms radialMass_pos
#print axioms source_power_add
#print axioms mass_pos
#print axioms secondMoment_pos
#print axioms firstMoment_zero

end YMGap.Continuum.SU2QuaternionConcentratedSourceMoments
