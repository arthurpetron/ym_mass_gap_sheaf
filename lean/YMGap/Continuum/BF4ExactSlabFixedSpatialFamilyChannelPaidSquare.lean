/-
# An actual variance-relative payment in the original channel energy

The retained negative observable square is paid against the ORIGINAL
interacting variance, using the constructed local source band.  The payment
is positive at each fixed nome and finite family size; no useful lower bound
on a changing scaling family is asserted.  The signed curvature and computed
cubic/omitted-mode error remain on the right-hand side, unpaid.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSquareCredit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPaidSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound
  (channelFirstOrderVarianceConstant)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare
  (familyChannelCurvature familyChannelObservableSquare familyChannelErrorBudget
    padded_family_energy_le_retainedChannelVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSquareCredit
  (channelObservableSquareVarianceCredit channelObservableSquareVarianceCredit_positive
    family_channel_observableSquare_variance_credit
    channelObservableSquareLinearVarianceCredit channelObservableSquareLinearVarianceCredit_positive
    family_channel_observableSquare_linear_variance_credit)

local infix:50 " ≈ " => Q'.eqv

/-- The computed payment uses only the nome and literal family size.  It
does not claim uniform positivity as the nome or family size changes. -/
def channelSquareEnergyVariancePayment {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) : Q' :=
  (48*(HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))) *
    channelObservableSquareVarianceCredit hw0 hw1 size

theorem channelSquareEnergyVariancePayment_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size : Nat) :
    (0 : Q') < channelSquareEnergyVariancePayment hw0 hw1 size := by
  have hh : (0 : Q') < (1 : Q')-w := HKPos.one_sub_pos hw1
  exact Q'.mul_pos
    (Q'.mul_pos (by decide) (Q'.mul_pos (by decide) (Q'.mul_pos hh hh)))
    (channelObservableSquareVarianceCredit_positive hw0 hw1 size)

attribute [local irreducible] energy terminalMessage spatialSpan oddMass oddVariance
  channelFirstOrderVarianceConstant familyChannelCurvature
  familyChannelObservableSquare familyChannelErrorBudget
  channelObservableSquareVarianceCredit

/-- The original full energy pays a strictly positive, constructed
variance coefficient.  Neither curvature nor the error is discarded or
assumed controlled.  The source, action, own center and interacting variance
are unchanged; this is not a scaling-uniform or physical gap estimate. -/
theorem padded_family_energy_paid_channel_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    let V := oddMass w K width (n+1) *
      oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width coeff qs)
    energy w K width (terminalMessage w K width (n+1)) (spatialSpan width coeff qs) +
      channelSquareEnergyVariancePayment hw0 hw1 qs.length*V ≤
      (h+t)*(channelFirstOrderVarianceConstant hw0 hw1 qs.length*V) +
        (t*(-familyChannelCurvature w K width (n+1) coeff qs) +
          familyChannelErrorBudget w K width (n+1) coeff qs) := by
  dsimp only
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let V := oddMass w K width (n+1) *
    oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width coeff qs)
  let C := channelFirstOrderVarianceConstant hw0 hw1 qs.length
  let rho := channelObservableSquareVarianceCredit hw0 hw1 qs.length
  let curv := familyChannelCurvature w K width (n+1) coeff qs
  let sq := familyChannelObservableSquare w K width (n+1) coeff qs
  let err := familyChannelErrorBudget w K width (n+1) coeff qs
  have hh0 : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have ht0 : (0 : Q') ≤ t := Q'.mul_nonneg _ _ HalfPow.half_nonneg
    (Q'.mul_nonneg _ _ hh0 hh0)
  have hpayment := Q'.mul_le_mul_of_nonneg_left _ _ (48*t)
    (family_channel_observableSquare_variance_credit hw0 hw1 K hK hwidth
      n coeff qs hqs)
    (Q'.mul_nonneg _ _ (by decide) ht0)
  have hcancel :
      ((h+t)*(C*V)+(t*(-curv-48*sq)+err))+(48*t)*(rho*V) ≤
      ((h+t)*(C*V)+(t*(-curv-48*sq)+err))+(48*t)*sq :=
    Q'.add_le_add_left _ _ _ hpayment
  have hshape :
      ((h+t)*(C*V)+(t*(-curv-48*sq)+err))+(48*t)*sq ≈
        (h+t)*(C*V)+(t*(-curv)+err) :=
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.add (.mul (.var 1)
            (.add (.neg (.var 4)) (.neg (.mul (.const 48) (.var 5))))) (.var 6)))
        (.mul (.mul (.const 48) (.var 1)) (.var 5)))
      (.add (.mul (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.add (.mul (.var 1) (.neg (.var 4))) (.var 6)))
      (by decide)
      (fun | 0 => h | 1 => t | 2 => C | 3 => V | 4 => curv | 5 => sq | _ => err)
  have hE := Q'.add_le_add_right _ _ ((48*t)*(rho*V))
    (padded_family_energy_le_retainedChannelVariance hw0 hw1 K hK hwidth
      n coeff qs hqs)
  have hleft :
      channelSquareEnergyVariancePayment hw0 hw1 qs.length*V ≈
        (48*t)*(rho*V) := Q'.mul_assoc_eqv (48*t) rho V
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) hleft))
    (Q'.le_trans' _ _ _ hE
      (Q'.le_trans' _ _ _ hcancel (Q'.le_of_eqv hshape)))

/-- The sharper payment retains one actual source factor and uses l/u,
not (l/u)^2. It is still a nome- and footprint-dependent scalar. -/
def channelSquareLinearEnergyVariancePayment {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) : Q' :=
  (48*(HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))) *
    channelObservableSquareLinearVarianceCredit hw0 hw1 size

theorem channelSquareLinearEnergyVariancePayment_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size : Nat) :
    (0 : Q') < channelSquareLinearEnergyVariancePayment hw0 hw1 size := by
  have hh : (0 : Q') < (1 : Q')-w := HKPos.one_sub_pos hw1
  exact Q'.mul_pos
    (Q'.mul_pos (by decide) (Q'.mul_pos (by decide) (Q'.mul_pos hh hh)))
    (channelObservableSquareLinearVarianceCredit_positive hw0 hw1 size)

attribute [local irreducible] channelObservableSquareLinearVarianceCredit

/-- The linear credit reaches the COMPLETE original energy consumer. The
signed curvature, full error and leading coefficient are all unchanged;
their useful comparison on a justified scaling family remains open. -/
theorem padded_family_energy_paid_channel_square_linear {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    let V := oddMass w K width (n+1) *
      oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width coeff qs)
    energy w K width (terminalMessage w K width (n+1)) (spatialSpan width coeff qs) +
      channelSquareLinearEnergyVariancePayment hw0 hw1 qs.length*V ≤
      (h+t)*(channelFirstOrderVarianceConstant hw0 hw1 qs.length*V) +
        (t*(-familyChannelCurvature w K width (n+1) coeff qs) +
          familyChannelErrorBudget w K width (n+1) coeff qs) := by
  dsimp only
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let V := oddMass w K width (n+1) *
    oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width coeff qs)
  let C := channelFirstOrderVarianceConstant hw0 hw1 qs.length
  let rho := channelObservableSquareLinearVarianceCredit hw0 hw1 qs.length
  let curv := familyChannelCurvature w K width (n+1) coeff qs
  let sq := familyChannelObservableSquare w K width (n+1) coeff qs
  let err := familyChannelErrorBudget w K width (n+1) coeff qs
  have hh0 : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have ht0 : (0 : Q') ≤ t := Q'.mul_nonneg _ _ HalfPow.half_nonneg
    (Q'.mul_nonneg _ _ hh0 hh0)
  have hpayment := Q'.mul_le_mul_of_nonneg_left _ _ (48*t)
    (family_channel_observableSquare_linear_variance_credit hw0 hw1 K hK hwidth
      n coeff qs hqs)
    (Q'.mul_nonneg _ _ (by decide) ht0)
  have hcancel :
      ((h+t)*(C*V)+(t*(-curv-48*sq)+err))+(48*t)*(rho*V) ≤
      ((h+t)*(C*V)+(t*(-curv-48*sq)+err))+(48*t)*sq :=
    Q'.add_le_add_left _ _ _ hpayment
  have hshape :
      ((h+t)*(C*V)+(t*(-curv-48*sq)+err))+(48*t)*sq ≈
        (h+t)*(C*V)+(t*(-curv)+err) :=
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.add (.mul (.var 1)
            (.add (.neg (.var 4)) (.neg (.mul (.const 48) (.var 5))))) (.var 6)))
        (.mul (.mul (.const 48) (.var 1)) (.var 5)))
      (.add (.mul (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.add (.mul (.var 1) (.neg (.var 4))) (.var 6)))
      (by decide)
      (fun | 0 => h | 1 => t | 2 => C | 3 => V | 4 => curv | 5 => sq | _ => err)
  have hE := Q'.add_le_add_right _ _ ((48*t)*(rho*V))
    (padded_family_energy_le_retainedChannelVariance hw0 hw1 K hK hwidth
      n coeff qs hqs)
  have hleft :
      channelSquareLinearEnergyVariancePayment hw0 hw1 qs.length*V ≈
        (48*t)*(rho*V) := Q'.mul_assoc_eqv (48*t) rho V
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) hleft))
    (Q'.le_trans' _ _ _ hE
      (Q'.le_trans' _ _ _ hcancel (Q'.le_of_eqv hshape)))

#print axioms channelSquareEnergyVariancePayment
#print axioms channelSquareEnergyVariancePayment_positive
#print axioms padded_family_energy_paid_channel_square
#print axioms channelSquareLinearEnergyVariancePayment
#print axioms channelSquareLinearEnergyVariancePayment_positive
#print axioms padded_family_energy_paid_channel_square_linear

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPaidSquare
