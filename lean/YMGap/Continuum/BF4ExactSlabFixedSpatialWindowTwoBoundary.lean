/-
# Both boundaries recede from the same observed window

Apply the positive terminal bracket to the actual window input. Its residual
has a nonnegative (possibly zero) partition, so the checked ratio estimate
cancels normalization without a growing-volume partition floor. Combining
this left estimate with right-boundary forgetting gives a rectangular bound
q^s * 2C*(kappa+1) when all four distances are at least s+1.

The window, action, cutoff and normalization are fixed throughout each
comparison. The constants are explicit and independent of late cutoff and
boundary lengths; they depend on nome and spatial width. This supplies the
time-limit estimate, not window consistency, ambient-lattice identification,
spatial/continuum control or a physical OS/Hamiltonian gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInputComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInputComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

/-- The input partition for a terminal message is exactly the old window
partition, with all m+L+n transfer factors retained. -/
theorem inputPartition_terminal (w : Q') (K width L n m : Nat) :
    inputPartition w K width L n (terminalMessage w K width m) =
      weightedMass w K width
        (polyMul (terminalMessage w K width (m+L)) (terminalMessage w K width n)) := by
  unfold inputPartition terminalMessage
  rw [← iterateStep_add]

theorem inputPartition_terminal_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n m : Nat) :
    (0 : Q') < inputPartition w K width L n (terminalMessage w K width m) := by
  rw [inputPartition_terminal]
  exact terminalPair_positive hw0 hw1 K width hK (m+L) n

/-- No new normalized state is introduced by the boundary-input argument. -/
theorem windowRatio_input_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) (p : RatPoly)
    (hZ : (0 : Q') < inputPartition w K width L n (terminalMessage w K width m)) :
    windowRatio hw0 hw1 K width hK m L n p ≈
      inputNumerator w K width L n (terminalMessage w K width m) p * Q'.recipPos _ hZ := by
  simp only [inputPartition_terminal] at hZ ⊢
  exact Q'.eqv_refl _

private theorem terminal_window_difference {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n s r t : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) :
    Q'.abs (windowRatio hw0 hw1 K width hK (s+1+r) L n p +
      -windowRatio hw0 hw1 K width hK (s+1+t) L n p) ≤
        (c+c)*comparisonEta hw0 hw1 width s := by
  have hX := inputPartition_terminal_positive hw0 hw1 K width hK L n (s+1+r)
  have hY := inputPartition_terminal_positive hw0 hw1 K width hK L n (s+1+t)
  have h := inputRatio_bracket_bound hw0 hw1 K width hK L n
    (terminalMessage_supported w K width (s+1+r))
    (terminalMessage_supported w K width (s+1+t))
    (terminalMessage_certificate hw0 hw1 K width hK (s+1+t)) I
    (terminalComparison hw0 hw1 K width hK s r t)
    (terminalComparison_lower_positive hw0 hw1 K width hK s r t)
    (comparisonEta_nonnegative hw0 hw1 width s)
    (terminalComparison_relative_width hw0 hw1 K width hK s r t) hX hY
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr'
      (windowRatio_input_pin hw0 hw1 K width hK (s+1+r) L n p hX)
      (Q'.neg_eqv_congr _ _ (windowRatio_input_pin hw0 hw1 K width hK (s+1+t) L n p hY))))) h

private theorem orders_of_abs (x y e : Q') (h : Q'.abs (x + -y) ≤ e) :
    x ≤ y+e ∧ y ≤ x+e := by
  have hx : (x + -y) + y ≈ x := poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
    (fun | 0 => x | _ => y)
  have hy : -(x + -y) + x ≈ y := poly_identity_of_normal_eq
    (.add (.neg (.add (.var 0) (.neg (.var 1)))) (.var 0)) (.var 1) (by decide)
    (fun | 0 => x | _ => y)
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv hx)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ y (Q'.le_trans' _ _ _ (Q'.le_abs_self _) h))
      (Q'.le_of_eqv (Q'.add_comm_eqv e y))),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hy)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ x (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) h))
        (Q'.le_of_eqv (Q'.add_comm_eqv e x)))⟩

/-- The left distance can vary independently while the complete observed
window and right message are held fixed. -/
theorem windowRatio_left_commonTail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n s m i : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) (hm : s+1 ≤ m) (hi : s+1 ≤ i) :
    windowRatio hw0 hw1 K width hK m L n p ≤ windowRatio hw0 hw1 K width hK i L n p +
        (c+c)*comparisonEta hw0 hw1 width s ∧
      windowRatio hw0 hw1 K width hK i L n p ≤ windowRatio hw0 hw1 K width hK m L n p +
        (c+c)*comparisonEta hw0 hw1 width s := by
  have h := terminal_window_difference hw0 hw1 K width hK L n s (m-(s+1)) (i-(s+1)) I
  have hem : s+1+(m-(s+1)) = m := by omega
  have hei : s+1+(i-(s+1)) = i := by omega
  rw [hem, hei] at h
  exact orders_of_abs _ _ _ h

/-- Computed two-sided error coefficient, deliberately allowing the coarse
kappa=(cap/floor)^2 used by the terminal comparison. -/
def windowTimeCap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (c : Q') : Q' := (c+c)*(comparisonKappa hw0 hw1 width + 1)

theorem windowTimeCap_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) {c : Q'} (hc : (0 : Q') ≤ c) :
    (0 : Q') ≤ windowTimeCap hw0 hw1 width c :=
  Q'.mul_nonneg _ _
    (Q'.le_trans' _ _ _ hc (Q'.add_le_self_of_nonneg c c hc))
    (Q'.le_trans' _ _ _ (comparisonKappa_nonnegative hw0 hw1 width)
      (Q'.add_le_self_of_nonneg _ 1 (by decide)))

private theorem two_hops (x y z a b e : Q')
    (hxy : x ≤ y+a ∧ y ≤ x+a) (hyz : y ≤ z+b ∧ z ≤ y+b) (he : a+b ≈ e) :
    x ≤ z+e ∧ z ≤ x+e := by
  have hx : (z+b)+a ≈ z+e := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 2)) (.var 1))
      (.add (.var 0) (.add (.var 1) (.var 2))) (by decide)
      (fun | 0 => z | 1 => a | _ => b))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) he)
  have hz : (x+a)+b ≈ x+e := Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv x a b) (Q'.add_eqv_congr' (Q'.eqv_refl _) he)
  exact ⟨Q'.le_trans' _ _ _ hxy.1
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ a hyz.1) (Q'.le_of_eqv hx)),
    Q'.le_trans' _ _ _ hyz.2
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ b hxy.2) (Q'.le_of_eqv hz))⟩

/-- Rectangular time-tail comparison for a fixed supported observed window.
Neither boundary distance, nor late cutoff, appears in the error coefficient. -/
theorem windowRatio_commonTail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L s m n i j : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c)
    (hm : s+1 ≤ m) (hn : s+1 ≤ n) (hi : s+1 ≤ i) (hj : s+1 ≤ j) :
    windowRatio hw0 hw1 K width hK m L n p ≤ windowRatio hw0 hw1 K width hK i L j p +
        mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width c ∧
      windowRatio hw0 hw1 K width hK i L j p ≤ windowRatio hw0 hw1 K width hK m L n p +
        mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width c := by
  apply two_hops _ (windowRatio hw0 hw1 K width hK i L n p) _ _ _ _
    (windowRatio_left_commonTail hw0 hw1 K width hK L n s m i I hm hi)
    (windowRatio_right_commonTail hw0 hw1 K width hK i L s n j I (by omega) (by omega))
  exact poly_identity_of_normal_eq
    (.add (.mul (.add (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
      (.mul (.var 2) (.add (.var 0) (.var 0))))
    (.mul (.var 2) (.mul (.add (.var 0) (.var 0)) (.add (.var 1) (.const 1)))) (by decide)
    (fun | 0 => c | 1 => comparisonKappa hw0 hw1 width | _ => mixRate hw0 hw1 width ^ s)

/-- Every supported polynomial obtains the estimate with its computed cap. -/
theorem polynomialWindow_commonTail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L s m n i j : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p)
    (hm : s+1 ≤ m) (hn : s+1 ≤ n) (hi : s+1 ≤ i) (hj : s+1 ≤ j) :
    windowRatio hw0 hw1 K width hK m L n p ≤ windowRatio hw0 hw1 K width hK i L j p +
        mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width (polynomialCap p) ∧
      windowRatio hw0 hw1 K width hK i L j p ≤ windowRatio hw0 hw1 K width hK m L n p +
        mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width (polynomialCap p) :=
  windowRatio_commonTail hw0 hw1 K width hK L s m n i j
    (polynomialInterval ((L+1)*(N width)) p hp) hm hn hi hj

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary.inputPartition_terminal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary.inputPartition_terminal_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary.windowRatio_input_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary.windowRatio_left_commonTail
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary.windowTimeCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary.windowTimeCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary.windowRatio_commonTail
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary.polynomialWindow_commonTail
