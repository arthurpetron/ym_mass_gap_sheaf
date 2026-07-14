/-
# Removing physical projection from supported transvectants

The off-rectangle leakage fence requires projection for arbitrary coefficient
functions.  For a genuinely bidegree-supported tensor, however, projection is
pointwise equivalent to the original tensor.  Moreover every admissible
transvectant of such a tensor vanishes above its physical output degree.
-/

import YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
import YMGap.Continuum.SU2TransvectantBinaryGramInvariant

namespace YMGap.Continuum.SU2ProjectedRawSupportedBridge

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2TransvectantBinaryGramInvariant
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates

local infix:50 " ≈ " => Q'.eqv

/-- An admissible transvectant of a physically supported tensor vanishes
above degree `m+n-2k`. -/
theorem transvect_zero_above_degree (m n k : Nat) (c : BForm2)
    (hm : k ≤ m) (hn : k ≤ n) (hc : BidegreeSupported m n c)
    (s : Nat) (hs : m + n - 2 * k < s) :
    transvect m n k c s ≈ 0 := by
  have hsupp := omegaK_supported k m n c hm hn hc
  unfold transvect diag
  apply finSum_zero_on
  intro a ha
  apply hsupp a (s - a)
  have has : a ≤ s := Nat.lt_succ_iff.mp ha
  by_cases hleft : m - k < a
  · exact Or.inl hleft
  · right
    omega

/-- A supported tensor is already the zero-outside representative selected
by rectangle projection. -/
theorem bidegreeSupported_eqv_rectProject (m n : Nat) (c : BForm2)
    (hc : BidegreeSupported m n c) :
    BForm2Eqv c (rectProject m n c) := by
  intro i j
  by_cases hi : i ≤ m
  · by_cases hj : j ≤ n
    · exact Q'.eqv_symm (rectProject_apply_physical m n c i j hi hj)
    · exact Q'.eqv_trans _ 0 _ (hc i j (Or.inr (by omega)))
        (Q'.eqv_symm
          (rectProject_zero_outside m n c i j (Or.inr (by omega))))
  · exact Q'.eqv_trans _ 0 _ (hc i j (Or.inl (by omega)))
      (Q'.eqv_symm
        (rectProject_zero_outside m n c i j (Or.inl (by omega))))

/-- Projected actual coordinates equal raw transvectants on any genuinely
supported physical tensor. -/
theorem globalTransvectCoordinates_eq_raw_of_supported
    (m n : Nat) (c : BForm2) (hc : BidegreeSupported m n c)
    (q : PhysicalCGChannel m n) :
    globalTransvectCoordinates m n c q ≈ transvect m n q.k c q.s := by
  have hcongr := transvect_congr m n q.k
    (fun i j => Q'.eqv_symm
      (bidegreeSupported_eqv_rectProject m n c hc i j)) q.s
  simpa only [globalTransvectCoordinates] using hcongr

end YMGap.Continuum.SU2ProjectedRawSupportedBridge

#print axioms YMGap.Continuum.SU2ProjectedRawSupportedBridge.transvect_zero_above_degree
#print axioms YMGap.Continuum.SU2ProjectedRawSupportedBridge.bidegreeSupported_eqv_rectProject
#print axioms YMGap.Continuum.SU2ProjectedRawSupportedBridge.globalTransvectCoordinates_eq_raw_of_supported
