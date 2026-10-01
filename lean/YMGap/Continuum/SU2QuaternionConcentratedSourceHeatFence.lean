/-
# No source-independent weak-step cost bound from nonnegativity alone

For each nonnegative rational C, construct a one-link source and an actual
nome 0<w<1 at which E > C*(1-w)*H[(q*f^2)*P(q)], for EVERY cutoff above
the original sufficient-cutoff guard. The source has a finite nonnegativity
certificate and a strictly positive Haar second moment. The finite-step
energy and moment are the ORIGINAL product-heat expressions, not their
zero-step endpoints.

These sources are not identified with the four-dimensional terminal
recursion. This excludes only a generic nonnegativity-only calibration;
it does not refute an actual terminal-source estimate or Yang--Mills.
-/

import YMGap.Continuum.SU2QuaternionConcentratedSourceMoments
import YMGap.Continuum.SU2QuaternionProductHeatSourceMomentLimit
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Constructive.RatNat

namespace YMGap.Continuum.SU2QuaternionConcentratedSourceHeatFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionConcentratedSourceWard
open YMGap.Continuum.SU2QuaternionConcentratedSourceMoments (secondMoment_pos)
open YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence
  (fundamental fundamental_supported)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatSourceSlope
open YMGap.Continuum.SU2QuaternionProductHeatSourceMomentLimit
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.ClusteringImpliesGap

local infix:50 " ≈ " => Q'.eqv

private def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The exponent is computed directly from the requested rational bound. -/
def escapeExponent (C : Q') : Nat := C.num.toNat

theorem escapeExponent_coefficient (C : Q') (hC : (0 : Q') ≤ C) :
    (2 : Q')*C < 4*Q'.ofNat (escapeExponent C)+2 := by
  have hle := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
    (RatNat.le_ofNat_toNat C hC) (by decide)
  have hstrict : (2 : Q')*Q'.ofNat (escapeExponent C) <
      4*Q'.ofNat (escapeExponent C)+2 := by
    show ((2 : Q')*Q'.ofNat (escapeExponent C)).num *
        (((4 : Q')*Q'.ofNat (escapeExponent C)+2).den : Int) <
      ((4 : Q')*Q'.ofNat (escapeExponent C)+2).num *
        (((2 : Q')*Q'.ofNat (escapeExponent C)).den : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.add_num_cast,
      Q'.add_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast]
    change (2 : Int)*(escapeExponent C : Int)*1 <
      (4*(escapeExponent C : Int)*1+2*1)*1
    omega
  exact Q'.lt_of_le_of_lt hle hstrict

theorem zeroStep_square_pin (N : Nat) :
    zeroStepMoment 0 (source N) (polyMul fundamental fundamental) ≈
      secondMoment N := by
  let q := source N
  let p := polyMul fundamental fundamental
  exact haar_of_coeff
    ((RatPolyCoeffEqv.mul_assoc q p q).trans
      (((RatPolyCoeffEqv.mul_comm p q).mul_left q).trans
        (RatPolyCoeffEqv.mul_assoc q q p).symm))

/-- Both actual fixed-source radii and a positive-nome cap are retained. -/
def step (N : Nat) : Q' :=
  Q'.min' half
    (Q'.min' (slopeRadius 0 (source N) fundamental (secondMoment N))
      (momentRadius 0 (source N) (polyMul fundamental fundamental) (secondMoment N)))

private theorem min_positive {a b : Q'} (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) : (0 : Q') < Q'.min' a b := by
  unfold Q'.min'
  by_cases h : a ≤ b
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb

theorem step_positive (N : Nat) : (0 : Q') < step N :=
  min_positive (by decide : (0 : Q') < half)
    (min_positive (slopeRadius_positive 0 _ _ _ (secondMoment_pos N))
      (momentRadius_positive 0 _ _ _ (secondMoment_pos N)))

def nome (N : Nat) : Q' := (1 : Q')-step N

theorem nome_positive (N : Nat) : (0 : Q') < nome N :=
  sub_pos_of_lt (Q'.lt_of_le_of_lt
    (Q'.min_le_left : step N ≤ half) (by decide : half < (1 : Q')))

theorem nome_lt_one (N : Nat) : nome N < (1 : Q') := by
  have hn : (0 : Int) < (step N).num := Q'.num_pos_of_pos (step_positive N)
  show (nome N).num * ((1 : Q').den : Int) <
    (1 : Q').num * ((nome N).den : Int)
  change (((1 : Q') + -(step N)).num) * 1 <
    1 * (((1 : Q') + -(step N)).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den,
    Int.mul_one, Int.one_mul]
  simp only [show (1 : Q').num = 1 by rfl,
    show ((1 : Q').den : Int) = 1 by rfl,
    show (-(step N)).num = -((step N).num) by rfl,
    Int.one_mul, Int.mul_one]
  omega

theorem nome_step_pin (N : Nat) : (1 : Q')-nome N ≈ step N :=
  poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
    (.var 0) (by decide) (fun _ => step N)

/-- Original finite-step obstruction, not just an endpoint ratio. -/
theorem energy_gt_same_secondMoment (C : Q') (hC : (0 : Q') ≤ C)
    (K : Nat) (hK : sufficientCutoff (nome (escapeExponent C)) ≤ K) :
    C*((1 : Q')-nome (escapeExponent C))*
        sourceMoment 1 (nome (escapeExponent C)) K [0] (source (escapeExponent C))
          (polyMul fundamental fundamental) <
      sourceEnergy 1 (nome (escapeExponent C)) K [0]
        (source (escapeExponent C)) fundamental := by
  let N := escapeExponent C
  let w := nome N
  let h := (1 : Q')-w
  let J := secondMoment N
  let A := weightedAngularEnergy 0 (source N) fundamental
  let B := sourceMoment 1 w K [0] (source N) (polyMul fundamental fundamental)
  let E := sourceEnergy 1 w K [0] (source N) fundamental
  have hw0 : (0 : Q') ≤ w := Q'.le_of_lt (nome_positive N)
  have hw1 : w < (1 : Q') := nome_lt_one N
  have hh : (0 : Q') < h := sub_pos_of_lt hw1
  have hJ : (0 : Q') < J := secondMoment_pos N
  have hstep : h ≤ step N := Q'.le_of_eqv (nome_step_pin N)
  have hs : h ≤ slopeRadius 0 (source N) fundamental J :=
    Q'.le_trans' _ _ _ hstep
      (Q'.le_trans' _ _ _ Q'.min_le_right Q'.min_le_left)
  have hm : h ≤ momentRadius 0 (source N) (polyMul fundamental fundamental) J :=
    Q'.le_trans' _ _ _ hstep
      (Q'.le_trans' _ _ _ Q'.min_le_right Q'.min_le_right)
  have hlow := (sourceEnergy_slope_interval 0 hw0 hw1 K hK
    (source N) fundamental (source_supported N) fundamental_supported J hs).1
  have hupp := ((momentCertificate 0 (source N) (polyMul fundamental fundamental)
    (source_supported N) J hJ).2.2 w hw0 hw1 hm K hK).2
  have hB : B ≤ (2 : Q')*J := Q'.le_trans' _ _ _ hupp
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (zeroStep_square_pin N) (Q'.eqv_refl J))
      (poly_identity_of_normal_eq (.add (.var 0) (.var 0))
        (.mul (.const 2) (.var 0)) (by decide) (fun _ => J))))
  have hcoeff : A-J ≈ ((4 : Q')*Q'.ofNat N+2)*J :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (sourceSquare_angular N) (Q'.eqv_refl (-J)))
      (poly_identity_of_normal_eq
        (.add (.mul (.add (.mul (.const 4) (.var 0)) (.const 3)) (.var 1))
          (.neg (.var 1)))
        (.mul (.add (.mul (.const 4) (.var 0)) (.const 2)) (.var 1))
        (by decide) (fun | 0 => Q'.ofNat N | _ => J))
  have hL : ((4 : Q')*Q'.ofNat N+2)*(h*J) ≤ E :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2)))
          (by decide) (fun | 0 => (4 : Q')*Q'.ofNat N+2 | 1 => h | _ => J))
        (Q'.mul_eqv_congr_left h _ _ (Q'.eqv_symm hcoeff)))) hlow
  have hU : (C*h)*B ≤ (2*C)*(h*J) := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (C*h) hB
      (Q'.mul_nonneg _ _ hC (Q'.le_of_lt hh)))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.const 2) (.var 2)))
      (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => C | 1 => h | _ => J)))
  have hstrict := mul_lt_mul_of_pos_right (Q'.mul_pos hh hJ)
    (escapeExponent_coefficient C hC)
  exact Q'.lt_of_le_of_lt hU (lt_of_lt_of_le hstrict hL)

/-- Actual source exponent and nome returned as data; every guarded cutoff
works. Positivity is produced above, not an unsupplied certificate field. -/
def obstruction (C : Q') (hC : (0 : Q') ≤ C) :
    Σ' N : Nat, Σ' w : Q', ((0 : Q') < w) ×' (w < (1 : Q')) ×'
      (∀ K : Nat, sufficientCutoff w ≤ K →
        C*((1 : Q')-w)*sourceMoment 1 w K [0] (source N)
            (polyMul fundamental fundamental) <
          sourceEnergy 1 w K [0] (source N) fundamental) :=
  ⟨escapeExponent C,nome (escapeExponent C),nome_positive _,nome_lt_one _,
    fun K hK => energy_gt_same_secondMoment C hC K hK⟩

#print axioms escapeExponent
#print axioms escapeExponent_coefficient
#print axioms zeroStep_square_pin
#print axioms step_positive
#print axioms nome_positive
#print axioms nome_lt_one
#print axioms nome_step_pin
#print axioms energy_gt_same_secondMoment
#print axioms obstruction

end YMGap.Continuum.SU2QuaternionConcentratedSourceHeatFence
