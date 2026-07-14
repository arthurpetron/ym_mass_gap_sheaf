/-
# Unsquared ordered F coefficient on the zero-first-leg family

When the first tensor factor has degree zero, the left-associated and
ordered-right coordinate functionals are literally the same projected
binary transvectant.  Applying this equality to the reconstructed left
coordinate unit proves that the raw ordered F coefficient is exactly one.
-/

import YMGap.Continuum.SU2OrderedRacahZeroLegKernel

namespace YMGap.Continuum.SU2OrderedRacahZeroLegRawF

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantClosedBinaryGram
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2OrderedFixedOutputFKernel
open YMGap.Continuum.SU2OrderedRacahMultiplicityFence
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahZeroLegFamily
open YMGap.Continuum.SU2OrderedRacahZeroLegKernel
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## The degree-zero projected coordinate -/

theorem transvect_zero_left_project (n : Nat) (x : BForm2)
    (s : Nat) (hs : s ≤ n) :
    transvect 0 n 0 (rectProject 0 n x) s ≈ x 0 s := by
  unfold transvect OmegaK diag
  have hsum :
      finSum (fun i => rectProject 0 n x i (s - i)) (s + 1) ≈
        finSum (fun i => if i = 0 then x 0 s else 0) (s + 1) := by
    apply finSum_eqv_congr
    intro i
    by_cases hi : i = 0
    · subst i
      simp only [if_pos, Nat.sub_zero]
      exact rectProject_apply_physical 0 n x 0 s (by omega) hs
    · rw [if_neg hi]
      exact rectProject_zero_outside 0 n x i (s - i)
        (Or.inl (Nat.pos_of_ne_zero hi))
  exact Q'.eqv_trans _ _ _ hsum
    (finSum_onehot_value (x 0 s) (s + 1) 0 (by omega))

theorem firstPairOutput_zero_left (b : Nat) (x : TriForm)
    (j l : Nat) (hj : j ≤ b) :
    firstPairOutput 0 b x 0 j l ≈ x 0 j l := by
  simpa only [firstPairOutput, triSlice] using
    transvect_zero_left_project b (triSlice x l) j hj

/-! ## Equality of the two nested coordinate functionals -/

theorem zero_family_coordinate_functionals (b c p : Nat)
    (hp : p ≤ min b c) (x : TriForm) :
    leftNestedCoordinates 0 b c x
        (fixedLeftNestedChannel (zeroLeftFamily b c p hp) 0 (by omega)) ≈
      directRightNestedCoordinates 0 b c x
        (fixedRightNestedChannel (zeroRightFamily b c p hp) 0 (by omega)) := by
  let innerL : PhysicalCGChannel (0 + b - 2 * 0) c :=
    { k := p
      k_le := by simpa only [Nat.mul_zero, Nat.sub_zero, Nat.zero_add] using hp
      s := 0
      s_le := by omega }
  have hfirst : PhysicalRectangleEqv (0 + b - 2 * 0) c
      (firstPairOutput 0 b x 0) (rightTriSlice x 0) := by
    intro j l hj hl
    exact firstPairOutput_zero_left b x j l (by omega)
  have hleft := globalTransvectCoordinates_congr (0 + b - 2 * 0) c
    (firstPairOutput 0 b x 0) (rightTriSlice x 0) hfirst innerL
  have hright := transvect_zero_left_project (b + c - 2 * p)
    (lastPairOutput b c x p) 0 (by omega)
  refine Q'.eqv_trans _
    (globalTransvectCoordinates (0 + b - 2 * 0) c
      (rightTriSlice x 0) innerL) _ ?_ ?_
  · unfold leftNestedCoordinates fixedLeftNestedChannel zeroLeftFamily
    simpa only [innerL] using hleft
  · exact Q'.eqv_symm (by
      simpa only [directRightNestedCoordinates, fixedRightNestedChannel,
        zeroRightFamily, lastPairOutput, innerL, globalTransvectCoordinates,
        Nat.mul_zero, Nat.sub_zero, Nat.zero_add] using hright)

/-! ## The unsquared all-label unit entry -/

/-- **The raw ordered F coefficient is exactly one on every physical
zero-first-leg channel.** -/
theorem zero_family_fixedOrderedFCoefficient_eq_one (b c p : Nat)
    (hp : p ≤ min b c) :
    fixedOrderedFCoefficient (zeroLeftFamily b c p hp)
        (zeroRightFamily b c p hp) ≈ 1 := by
  let qL := zeroLeftFamily b c p hp
  let qR := zeroRightFamily b c p hp
  let x := leftNestedReconstruct 0 b c (fixedLeftCoordinateDelta qL)
  have hF := fixedOrderedFCoefficient_eq_directCoordinate qL qR
  have hfun := zero_family_coordinate_functionals b c p hp x
  have hleft := leftNestedCoordinates_reconstruct 0 b c
    (fixedLeftCoordinateDelta qL)
    (fixedLeftNestedChannel qL 0 (by omega))
  refine Q'.eqv_trans _ _ _ hF ?_
  refine Q'.eqv_trans _
    (leftNestedCoordinates 0 b c x
      (fixedLeftNestedChannel qL 0 (by omega))) _ (Q'.eqv_symm hfun) ?_
  exact Q'.eqv_trans _ _ _ hleft (by
    unfold fixedLeftCoordinateDelta fixedLeftNestedChannel qL
    rw [if_pos]
    · exact Q'.eqv_refl 1
    · exact ⟨rfl, rfl, rfl⟩)

/-! ## Closed normalization interfaces on the whole family -/

theorem zero_family_collapsedCrossFNormalization (b c p : Nat)
    (hp : p ≤ min b c) :
    CollapsedCrossFNormalizationAt (zeroLeftFamily b c p hp)
      (zeroRightFamily b c p hp) := by
  unfold CollapsedCrossFNormalizationAt
  have he := (zero_family_intermediates b c p hp).1
  rw [he]
  let W := Q'.ofNat (b + c - 2 * p + 1) * binaryRowFactorialProduct b c p
  have hC := zero_family_collapsedCross_closed b c p hp
  have hL := (zero_family_closed_factorial_normalization b c p hp).2.1
  have hF := zero_family_fixedOrderedFCoefficient_eq_one b c p hp
  have hprod :
      triLeftChannelWeight 0 b c (b + c - 2 * p) b *
          fixedOrderedFCoefficient (zeroLeftFamily b c p hp)
            (zeroRightFamily b c p hp) ≈ W := by
    refine Q'.eqv_trans _ (W *
      fixedOrderedFCoefficient (zeroLeftFamily b c p hp)
        (zeroRightFamily b c p hp)) _
      (Q'.mul_eqv_congr_right _ _ _ hL) ?_
    exact Q'.eqv_trans _ (W * 1) _
      (Q'.mul_eqv_congr_left W _ _ hF) (Q'.mul_one_eqv W)
  exact Q'.eqv_trans _ W _ hC (Q'.eqv_symm hprod)

theorem zero_family_gramWeightedRacahBridge (b c p : Nat)
    (hp : p ≤ min b c) :
    GramWeightedRacahBridgeAt (zeroLeftFamily b c p hp)
      (zeroRightFamily b c p hp) := by
  unfold GramWeightedRacahBridgeAt
  have he := (zero_family_intermediates b c p hp).1
  have hf := (zero_family_intermediates b c p hp).2
  rw [he, hf]
  let W := Q'.ofNat (b + c - 2 * p + 1) * binaryRowFactorialProduct b c p
  have hL := (zero_family_closed_factorial_normalization b c p hp).2.1
  have hR := (zero_family_closed_factorial_normalization b c p hp).2.2
  have hP := zero_leg_racahKernel_eq_one b c p hp
  have hF := zero_family_fixedOrderedFCoefficient_eq_one b c p hp
  have hleft :
      triRightChannelWeight 0 b c (b + c - 2 * p) (b + c - 2 * p) *
          racahKernel6 0 b c (zeroLegD b c p) b (zeroLegD b c p) ≈ W := by
    refine Q'.eqv_trans _ (W *
      racahKernel6 0 b c (zeroLegD b c p) b (zeroLegD b c p)) _
      (Q'.mul_eqv_congr_right _ _ _ hR) ?_
    exact Q'.eqv_trans _ (W * 1) _
      (Q'.mul_eqv_congr_left W _ _ hP) (Q'.mul_one_eqv W)
  have hFsquare :
      fixedOrderedFCoefficient (zeroLeftFamily b c p hp)
          (zeroRightFamily b c p hp) *
        fixedOrderedFCoefficient (zeroLeftFamily b c p hp)
          (zeroRightFamily b c p hp) ≈ 1 := by
    refine Q'.eqv_trans _
      (1 * fixedOrderedFCoefficient (zeroLeftFamily b c p hp)
        (zeroRightFamily b c p hp)) _
      (Q'.mul_eqv_congr_right _ _ _ hF) ?_
    exact Q'.eqv_trans _ (1 * 1) _
      (Q'.mul_eqv_congr_left 1 _ _ hF) (Q'.one_mul_eqv 1)
  have hright :
      triLeftChannelWeight 0 b c (b + c - 2 * p) b *
        (fixedOrderedFCoefficient (zeroLeftFamily b c p hp)
            (zeroRightFamily b c p hp) *
          fixedOrderedFCoefficient (zeroLeftFamily b c p hp)
            (zeroRightFamily b c p hp)) ≈ W := by
    refine Q'.eqv_trans _ (W *
      (fixedOrderedFCoefficient (zeroLeftFamily b c p hp)
          (zeroRightFamily b c p hp) *
        fixedOrderedFCoefficient (zeroLeftFamily b c p hp)
          (zeroRightFamily b c p hp))) _
      (Q'.mul_eqv_congr_right _ _ _ hL) ?_
    exact Q'.eqv_trans _ (W * 1) _
      (Q'.mul_eqv_congr_left W _ _ hFsquare) (Q'.mul_one_eqv W)
  exact Q'.eqv_trans _ W _ hleft (Q'.eqv_symm hright)

end YMGap.Continuum.SU2OrderedRacahZeroLegRawF

#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegRawF.transvect_zero_left_project
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegRawF.firstPairOutput_zero_left
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegRawF.zero_family_coordinate_functionals
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegRawF.zero_family_fixedOrderedFCoefficient_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegRawF.zero_family_collapsedCrossFNormalization
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegRawF.zero_family_gramWeightedRacahBridge
