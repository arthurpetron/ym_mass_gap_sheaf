/-
# The original signed multiplication cost is a difference of window drops

The half-smoothed source uses the ACTUAL odd mean at depth n. That SAME
rational center is retained in the comparison windows at depth n+t; it is
never replaced by their own mean. Both original chronological partitions
remain in the normalizer. The raw comparison pays two original geometric
boundary errors, at n and n+t, without estimating the remaining signed
two-point difference. All assertions are finite at fixed nome and width.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighWindow
import YMGap.Continuum.FCLimitContinuity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSignedMultiplicationWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalPair_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
  (endpoint_mean_lags_commonTail middleRatio_interval_bounds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference
  (rawPair centeredPair centered_lag_difference_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
  (signedMultiplicationCost signedMultiplicationCost_difference clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighWindow
  (clearedRayleighCost_window_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep iterateStep_supported)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass baseLinks spatialWeight kineticWeight terminalMessage

def originalPartitionProduct (w : Q') (K width n t : Nat) : Q' :=
  let A := terminalMessage w K width (n+t)
  weightedMass w K width (polyMul A A) *
    weightedMass w K width (polyMul A (transferStep w K width A))

theorem originalPartitionProduct_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) :
    (0 : Q') < originalPartitionProduct w K width n t := by
  unfold originalPartitionProduct
  dsimp only
  rw [terminalMessage_next]
  exact Q'.mul_pos
    (terminalPair_positive hw0 hw1 K width hK (n+t) (n+t))
    (terminalPair_positive hw0 hw1 K width hK (n+t) (n+t+1))

/-- Literal signed block cost divided by its TWO constructed original masses. -/
def normalizedSignedMultiplicationCost {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (f : RatPoly) : Q' :=
  let c := middleRatio hw0 hw1 K width hK (n+1) n f
  let psi := shifted f c
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  signedMultiplicationCost w K width A b psi *
    Q'.recipPos (originalPartitionProduct w K width n t)
      (originalPartitionProduct_positive hw0 hw1 K width hK n t)

attribute [local irreducible] normalizedSignedMultiplicationCost middleRatio

/-- Exact original source difference. In the second pair of windows, c is
still the depth-n OWN mean, not a depth-(n+t) mean. -/
theorem original_signed_window_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let c := middleRatio hw0 hw1 K width hK (n+1) n f
    normalizedSignedMultiplicationCost hw0 hw1 K width hK n t f ≈
      (centeredPair hw0 hw1 K width hK n (2*t) f c +
        -(centeredPair hw0 hw1 K width hK n (2*t+1) f c)) +
      -(centeredPair hw0 hw1 K width hK (n+t) 0 f c +
        -(centeredPair hw0 hw1 K width hK (n+t) 1 f c)) := by
  let c := middleRatio hw0 hw1 K width hK (n+1) n f
  let psi := shifted f c
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let M := originalPartitionProduct w K width n t
  let d0 := centeredPair hw0 hw1 K width hK n (2*t) f c +
    -(centeredPair hw0 hw1 K width hK n (2*t+1) f c)
  let d1 := centeredPair hw0 hw1 K width hK (n+t) 0 f c +
    -(centeredPair hw0 hw1 K width hK (n+t) 1 f c)
  have hp := shifted_supported hf c
  have hb : SupportedQuaternionBlocks (N width) b :=
    iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) t
      (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hu := supported_polyMul (terminalMessage_supported w K width (n+t)) hp
  have h0 : clearedRayleighCost w K width A b ≈ M*d0 :=
    clearedRayleighCost_window_pin hw0 hw1 K width hK n t hp
  have h1 : clearedRayleighCost w K width A (polyMul A psi) ≈ M*d1 := by
    simpa only [Nat.add_zero, Nat.mul_zero, Nat.zero_add, originalBlockTransfer, iterateStep]
      using clearedRayleighCost_window_pin hw0 hw1 K width hK (n+t) 0 hp
  have hs : signedMultiplicationCost w K width A b psi ≈ M*(d0 + -d1) :=
    Q'.eqv_trans _ _ _ (signedMultiplicationCost_difference w K width hb hu)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' h0 (Q'.neg_eqv_congr _ _ h1))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
          (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide)
          (fun | 0 => M | 1 => d0 | _ => d1)))
  let r := Q'.recipPos M (originalPartitionProduct_positive hw0 hw1 K width hK n t)
  unfold normalizedSignedMultiplicationCost
  change signedMultiplicationCost w K width A b psi * r ≈ d0 + -d1
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hs)
    (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => M | 1 => d0 + -d1 | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_recipPos_eqv M (originalPartitionProduct_positive hw0 hw1 K width hK n t)))
        (Q'.mul_one_eqv _)))

/-- Any supplied bounded center is allowed; this is needed when a mean
computed at depth n is retained in windows at depth n+t. -/
theorem centered_lag_raw_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L J : Nat)
    {f : RatPoly} {C : Q'} (I : Interval (N width) f C) (c : Q')
    (hc : -C ≤ c ∧ c ≤ C) :
    let x := centeredPair hw0 hw1 K width hK n L f c +
      -(centeredPair hw0 hw1 K width hK n J f c)
    let y := rawPair hw0 hw1 K width hK n L f + -(rawPair hw0 hw1 K width hK n J f)
    let e := mixRate hw0 hw1 width ^ n * ((C+C)*(C+C))
    x ≤ y+e ∧ y ≤ x+e := by
  let u := c+c
  let vL := windowRatio hw0 hw1 K width hK n L n f
  let vJ := windowRatio hw0 hw1 K width hK n J n f
  let B := C+C
  let d := mixRate hw0 hw1 width ^ n * B
  have hB := Q'.zero_le_add C C I.nonnegative I.nonnegative
  have hd := Q'.mul_nonneg _ _
    (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) n) hB
  have hu : -B ≤ u ∧ u ≤ B :=
    ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_add_eqv C C))
      (Q'.add_le_add hc.1 hc.1), Q'.add_le_add hc.2 hc.2⟩
  have hm := endpoint_mean_lags_commonTail hw0 hw1 K width hK n L J I
  have hforward := Q'.mul_close_of_two_sided u vJ vL B d hB hd hu.1 hu.2 hm.2 hm.1
  have hreverse := Q'.mul_close_of_two_sided u vL vJ B d hB hd hu.1 hu.2 hm.1 hm.2
  let y := rawPair hw0 hw1 K width hK n L f + -(rawPair hw0 hw1 K width hK n J f)
  let x := centeredPair hw0 hw1 K width hK n L f c +
    -(centeredPair hw0 hw1 K width hK n J f c)
  have hp : x ≈ y + (u*vJ + -(u*vL)) := Q'.eqv_trans _ _ _
    (centered_lag_difference_pin hw0 hw1 K width hK n L J I.support c)
    (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.var 1) (.add (.var 2) (.neg (.var 3))))))
      (.add (.var 0) (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 1) (.var 2)))))
      (by decide) (fun | 0 => y | 1 => u | 2 => vL | _ => vJ))
  have hr : y ≈ x + (u*vL + -(u*vJ)) := Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (u*vL + -(u*vJ)) hp)
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.var 2) (.neg (.var 1)))) (.var 0) (by decide)
      (fun | 0 => y | 1 => u*vJ | _ => u*vL)))
  have he : B*d ≈ mixRate hw0 hw1 width ^ n * ((C+C)*(C+C)) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 0)))
      (.mul (.var 1) (.mul (.var 0) (.var 0))) (by decide)
      (fun | 0 => B | _ => mixRate hw0 hw1 width ^ n)
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) (Q'.le_trans' _ _ _
      (Q'.add_le_add_left y _ _ (Q'.sub_le_of_le_add hforward))
      (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) he))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hr) (Q'.le_trans' _ _ _
      (Q'.add_le_add_left x _ _ (Q'.sub_le_of_le_add hreverse))
      (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) he)))⟩

private theorem subtract_bounds {x y u v e d : Q'}
    (h : x ≤ y+e ∧ y ≤ x+e) (k : u ≤ v+d ∧ v ≤ u+d) :
    x + -u ≤ (y + -v)+(e+d) ∧ y + -v ≤ (x + -u)+(e+d) := by
  have forward := Q'.add_le_add (Q'.sub_le_of_le_add h.1) (Q'.sub_le_of_le_add k.2)
  have reverse := Q'.add_le_add (Q'.sub_le_of_le_add h.2) (Q'.sub_le_of_le_add k.1)
  have regroup (a b c d : Q') : (a + -b) + (c + -d) ≈ (a + -d) + -(b + -c) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3))))
      (.add (.add (.var 0) (.neg (.var 3))) (.neg (.add (.var 1) (.neg (.var 2)))))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)
  exact ⟨Q'.le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (regroup x y v u)) forward),
    Q'.le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (regroup y x u v)) reverse)⟩

/-- BOTH raw orders for the actual signed source, paying the two boundary
depths but making no estimate of the remaining raw drop difference. -/
theorem original_signed_raw_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat)
    {f : RatPoly} {C : Q'} (I : Interval (N width) f C) :
    let raw := (rawPair hw0 hw1 K width hK n (2*t) f +
      -(rawPair hw0 hw1 K width hK n (2*t+1) f)) +
      -(rawPair hw0 hw1 K width hK (n+t) 0 f + -(rawPair hw0 hw1 K width hK (n+t) 1 f))
    let error := mixRate hw0 hw1 width ^ n * ((C+C)*(C+C)) +
      mixRate hw0 hw1 width ^ (n+t) * ((C+C)*(C+C))
    normalizedSignedMultiplicationCost hw0 hw1 K width hK n t f ≤ raw+error ∧
      raw ≤ normalizedSignedMultiplicationCost hw0 hw1 K width hK n t f + error := by
  let c := middleRatio hw0 hw1 K width hK (n+1) n f
  have hc := middleRatio_interval_bounds hw0 hw1 K width hK (n+1) n I
  have h := subtract_bounds
    (centered_lag_raw_bounds hw0 hw1 K width hK n (2*t) (2*t+1) I c hc)
    (centered_lag_raw_bounds hw0 hw1 K width hK (n+t) 0 1 I c hc)
  have hp := original_signed_window_pin hw0 hw1 K width hK n t I.support
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h.1,
    Q'.le_trans' _ _ _ h.2
      (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_symm hp) (Q'.eqv_refl _)))⟩

#print axioms originalPartitionProduct_positive
#print axioms normalizedSignedMultiplicationCost
#print axioms original_signed_window_pin
#print axioms centered_lag_raw_bounds
#print axioms original_signed_raw_bounds

end YMGap.Continuum.BF4ExactSlabFixedSpatialSignedMultiplicationWindow
