/-
# Actual even normalization at every small-nome cube terminal depth

The ORIGINAL radius-two even partition equals the shared cube action
integral of the next terminal square. The constructed action interval and
relative Haar terminal shape bound it by twice the CURRENT Haar amplitude
square, at every guarded cutoff and depth. The Haar amplitude, odd
partition and even partition remain distinct. No gain floor, changing-family
response or continuum claim is inferred from this finite normalization leg.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalEvenBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap (smallNome)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (cubeWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean
  (original_terminal_pair_weighted_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSharpHeatFloor
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
  (evenPartition evenPartition_middle_pin)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (quaternionBlockIndependent_polyOne)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local notation "N" => List.length (baseLinks 2)
local notation:max "H" p:arg => quaternionHaar N p
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks cubeWeight cubeTerminal terminalMessage

private theorem action_mass_pin (K : Nat) (g : RatPoly) :
    H (polyMul (cubeWeight smallNome K) g) ≈ H g +
      H (polyMul g (polyAdd (cubeWeight smallNome K) (polyNeg polyOne))) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N)
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.var 1))
      (.add (.var 1) (.mul (.var 1) (.add (.var 0) (.neg (.const 1)))))
      (by decide) (fun
        | 0 => cubeWeight smallNome K
        | _ => g))) (quaternionHaar_append N _ _)

/-- The next ACTUAL Haar mass is at most the sharp action factor times
the current mass. No interacting partition is substituted for either mass. -/
theorem cubeTerminal_mass_upper (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    H (cubeTerminal K (n+1)) ≤ (1+actionDeviation)*H (cubeTerminal K n) := by
  let a := H (cubeTerminal K n)
  let e := H (polyMul (cubeTerminal K n)
    (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)))
  have he : e ≤ actionDeviation*a := Q'.le_trans' _ _ _ (Q'.le_abs_self e)
    ((sharpCubeRemainder K hK).weighted_haar_bound (cubeTerminal_certificate K hhead n))
  have hr : a+actionDeviation*a ≈ (1+actionDeviation)*a :=
    poly_identity_of_normal_eq (.add (.var 0) (.mul (.var 1) (.var 0)))
      (.mul (.add (.const 1) (.var 1)) (.var 0)) (by decide) (fun
        | 0 => a
        | _ => actionDeviation)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (cubeTerminal_mean_pin K n) (action_mass_pin K (cubeTerminal K n))))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left a _ _ he) (Q'.le_of_eqv hr))

private theorem center_shifted (p : RatPoly) (a : Q') :
    RatPolyCoeffEqv (polyAdd p (polyNeg (cap a))) (shifted p a) := by
  unfold shifted cap
  exact ((RatPolyCoeffEqv.one_smul p).symm.add
    ((neg_smul (polySmul a polyOne)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) a polyOne).trans
        (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _
          (Q'.neg_mul_eqv 1 a) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))) polyOne))))

/-- The actual uncentered terminal square retains its positive Haar mass
and the checked relative centered-square radius. -/
theorem cubeTerminal_square_bound (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    H (polyMul (cubeTerminal K n) (cubeTerminal K n)) ≤
      (1+terminalRadius*terminalRadius)*
        (H (cubeTerminal K n)*H (cubeTerminal K n)) := by
  let g := cubeTerminal K n
  let a := H g
  let d := polyAdd g (polyNeg (cap a))
  have hpin : H (polyMul d d) ≈ H (polyMul g g)-a*a :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N)
      ((center_shifted g a).mul (center_shifted g a)))
      (bare_mean_pin (cubeTerminal_supported K n))
  have he : H (polyMul d d)+a*a ≈ H (polyMul g g) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hpin)
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
        (by decide) (fun
          | 0 => H (polyMul g g)
          | _ => a*a))
  have hr : (terminalRadius*terminalRadius)*(a*a)+a*a ≈
      (1+terminalRadius*terminalRadius)*(a*a) :=
    poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 1)) (.var 1))
      (.mul (.add (.const 1) (.var 0)) (.var 1)) (by decide) (fun
        | 0 => terminalRadius*terminalRadius
        | _ => a*a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (a*a) (cubeTerminal_variance_bound K hK hhead n))
      (Q'.le_of_eqv hr))

/-- Exact ORIGINAL even denominator, with both next-terminal factors and
the same spatial cube action retained. This algebra needs no cutoff guard. -/
theorem evenPartition_cube_pin (K n : Nat) :
    evenPartition smallNome K 2 n ≈
      H (polyMul (cubeWeight smallNome K)
        (polyMul (cubeTerminal K (n+1)) (cubeTerminal K (n+1)))) := by
  have hm := evenPartition_middle_pin smallNome K 2 n
  rw [terminalMessage_next smallNome K 2 n] at hm
  have hp := original_terminal_pair_weighted_pin K (n+1) (n+1) (supported_one N)
    (fun i _ _ => quaternionBlockIndependent_polyOne i)
  exact Q'.eqv_trans _ _ _ hm
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (weightedMass_congr smallNome K 2
      ((RatPolyCoeffEqv.mul_one _).mul (RatPolyCoeffEqv.refl _))))
      (Q'.eqv_trans _ _ _ hp (haar_of_coeff (blocks := N)
        ((RatPolyCoeffEqv.refl _).mul
          ((RatPolyCoeffEqv.mul_one _).mul (RatPolyCoeffEqv.refl _))))))

private theorem action_square_upper (K : Nat) (hK : 1 ≤ K) {g : RatPoly}
    (hg : SupportedQuaternionBlocks N g) :
    H (polyMul (cubeWeight smallNome K) (polyMul g g)) ≤
      (1+actionDeviation)*H (polyMul g g) := by
  let a := H (polyMul g g)
  let e := H (polyMul (polyMul g g)
    (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)))
  have he : e ≤ actionDeviation*a := Q'.le_trans' _ _ _ (Q'.le_abs_self e)
    ((sharpCubeRemainder K hK).weighted_haar_bound (Certificate.square g hg))
  have hr : a+actionDeviation*a ≈ (1+actionDeviation)*a :=
    poly_identity_of_normal_eq (.add (.var 0) (.mul (.var 1) (.var 0)))
      (.mul (.add (.const 1) (.var 1)) (.var 0)) (by decide) (fun
        | 0 => a
        | _ => actionDeviation)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (action_mass_pin K (polyMul g g)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left a _ _ he) (Q'.le_of_eqv hr))

/-- The ACTUAL original even partition is bounded by twice the current
terminal Haar amplitude square, uniformly in guarded cutoff and depth. -/
theorem evenPartition_le_terminal_mass_square (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    evenPartition smallNome K 2 n ≤
      2*(H (cubeTerminal K n)*H (cubeTerminal K n)) := by
  let a := H (cubeTerminal K n)
  let b := H (cubeTerminal K (n+1))
  have ha : (0 : Q') ≤ a := Q'.le_of_lt (cubeTerminal_mass_positive K hK hhead n)
  have hb : (0 : Q') ≤ b := Q'.le_of_lt (cubeTerminal_mass_positive K hK hhead (n+1))
  have hba : b ≤ (1+actionDeviation)*a := cubeTerminal_mass_upper K hK hhead n
  have hup : (0 : Q') ≤ (1+actionDeviation)*a :=
    Q'.mul_nonneg _ _ (by decide) ha
  have hbb : b*b ≤ ((1+actionDeviation)*a)*((1+actionDeviation)*a) :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hba hb)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hba hup)
  have hbound : evenPartition smallNome K 2 n ≤
      (1+actionDeviation)*((1+terminalRadius*terminalRadius)*
        (((1+actionDeviation)*a)*((1+actionDeviation)*a))) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (evenPartition_cube_pin K n))
      (Q'.le_trans' _ _ _ (action_square_upper K hK (cubeTerminal_supported K (n+1)))
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (Q'.le_trans' _ _ _ (cubeTerminal_square_bound K hK hhead (n+1))
            (Q'.mul_le_mul_of_nonneg_left _ _ _ hbb (by decide))) (by decide)))
  have he : (1+actionDeviation)*((1+terminalRadius*terminalRadius)*
        (((1+actionDeviation)*a)*((1+actionDeviation)*a))) ≈
      ((1+actionDeviation)*((1+actionDeviation)*(1+actionDeviation))*
        (1+terminalRadius*terminalRadius))*(a*a) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1)
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2)))))
      (.mul (.mul (.mul (.var 0) (.mul (.var 0) (.var 0))) (.var 1))
        (.mul (.var 2) (.var 2))) (by decide) (fun
          | 0 => 1+actionDeviation
          | 1 => 1+terminalRadius*terminalRadius
          | _ => a)
  have hc : (1+actionDeviation)*((1+actionDeviation)*(1+actionDeviation))*
      (1+terminalRadius*terminalRadius) ≤ (2 : Q') := by decide
  exact Q'.le_trans' _ _ _ hbound (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hc (SumOfSquares.q_mul_self_nonneg a)))

#print axioms cubeTerminal_mass_upper
#print axioms cubeTerminal_square_bound
#print axioms evenPartition_cube_pin
#print axioms evenPartition_le_terminal_mass_square

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalEvenBudget
