/-
# Higher-height finite-difference fence for the Omega correction

On the total shell, the outer factorial carrier is evaluated at height
`j + l - p`.  The all-order Hahn adjacent-difference identity does move that
height toward the proved height-one face, but it simultaneously lowers the
outer labels and contraction order.  This file records that exact law, gives
a closed rational counterexample to the tempting same-order replacement, and
packages the coupled label-lowering invariant which is sufficient for a
height induction.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneCoordinateFamily
import YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn

local infix:50 " ≈ " => Q'.eqv

/-- On inner support, the second coordinate of the outer factorial carrier is
exactly the correction height `j + l - q.p`. -/
theorem rightShellFactorialCoefficient_exposes_height
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (i j l : Nat) (hinner : q.p ≤ j + l) :
    rightShellFactorialCoefficient q i j l =
      hahnEntry b c (j + l) q.p j *
        transvectFactorialCoeff a q.intermediate q.r i (j + l - q.p) := by
  unfold rightShellFactorialCoefficient
  rw [if_pos hinner]

/-- The actual outer-height first difference.  Moving height down by one
necessarily changes `(m,n,k)` to `(m-1,n-1,k-1)` on the right-hand side. -/
theorem outerHeightAdjacentDifference_lowers_labels
    (m n k i h : Nat)
    (hkm : k ≤ m) (hkn : k ≤ n) (him : i < m)
    (hh : 0 < h) (hhn : h ≤ n) :
    (transvectFactorialCoeff m n k (i + 1) (h - 1) +
      -(transvectFactorialCoeff m n k i h)) ≈
      Q'.ofNat (k * (m + n - k + 1)) *
        transvectFactorialCoeff (m - 1) (n - 1) (k - 1) i (h - 1) := by
  exact transvectFactorialCoeff_adjacent k m n i h hkm hkn him hh hhn

/-- Kernel-checked fence: even at a fully physical interior point, the
reduced carrier in the adjacent-difference law cannot be replaced by the
same `(m,n,k)` carrier.  Here the true difference and reduced carrier both
vanish, while the proposed same-order right-hand side is nonzero. -/
theorem sameOrderOuterHeightRecurrence_refuted : ¬
    ((transvectFactorialCoeff 3 3 2 2 1 +
      -(transvectFactorialCoeff 3 3 2 1 2)) ≈
      Q'.ofNat (2 * (3 + 3 - 2 + 1)) *
        transvectFactorialCoeff 3 3 2 1 1) := by
  decide

/-- The stronger invariant exposed by the fence.  A residual family must be
closed under the label/order-lowering first difference, not merely known at
heights zero and one for one fixed triple of outer parameters. -/
def CoupledOuterHeightDifference
    (R : Nat → Nat → Nat → Nat → Nat → Q') : Prop :=
  ∀ m n k i h,
    k ≤ m → k ≤ n → i < m → 0 < h → h ≤ n →
    (R m n k (i + 1) (h - 1) + -(R m n k i h)) ≈
      Q'.ofNat (k * (m + n - k + 1)) *
        R (m - 1) (n - 1) (k - 1) i (h - 1)

/-- The factorial Hahn carrier itself satisfies the coupled invariant. -/
theorem transvectFactorialCoeff_coupledOuterHeightDifference :
    CoupledOuterHeightDifference transvectFactorialCoeff := by
  intro m n k i h hkm hkn him hh hhn
  exact outerHeightAdjacentDifference_lowers_labels
    m n k i h hkm hkn him hh hhn

/-- If the lower-label residual vanishes, the coupled first difference moves
one step toward height one without division. -/
theorem coupledOuterHeight_step_toward_one
    (R : Nat → Nat → Nat → Nat → Nat → Q')
    (hR : CoupledOuterHeightDifference R)
    (m n k i h : Nat)
    (hkm : k ≤ m) (hkn : k ≤ n) (him : i < m)
    (hh : 0 < h) (hhn : h ≤ n)
    (hlower : R (m - 1) (n - 1) (k - 1) i (h - 1) ≈ 0) :
    R m n k i h ≈ R m n k (i + 1) (h - 1) := by
  have hdiff := hR m n k i h hkm hkn him hh hhn
  have hrhs :
      Q'.ofNat (k * (m + n - k + 1)) *
          R (m - 1) (n - 1) (k - 1) i (h - 1) ≈ 0 :=
    Q'.eqv_trans _
      (Q'.ofNat (k * (m + n - k + 1)) * 0) _
      (Q'.mul_eqv_congr_left
        (Q'.ofNat (k * (m + n - k + 1))) _ _ hlower)
      (q_mul_zero _)
  exact Q'.eqv_symm (q_eqv_of_sub_zero
    (Q'.eqv_trans _ _ _ hdiff hrhs))

/-- Coupled closure plus vanishing of the reduced family propagates every
positive height to the height-one face on the same total-coordinate shell. -/
theorem coupledOuterHeight_eqv_height_one
    (R : Nat → Nat → Nat → Nat → Nat → Q')
    (hR : CoupledOuterHeightDifference R)
    (m n k i h : Nat)
    (hkm : k ≤ m) (hkn : k ≤ n)
    (hishell : i + h ≤ m) (hh : 0 < h) (hhn : h ≤ n)
    (hlower : ∀ u v,
      R (m - 1) (n - 1) (k - 1) u v ≈ 0) :
    R m n k i h ≈ R m n k (i + h - 1) 1 := by
  induction h generalizing i with
  | zero => omega
  | succ h hInd =>
      by_cases hzero : h = 0
      · subst h
        simpa using Q'.eqv_refl (R m n k i 1)
      · have hhpos : 0 < h := by omega
        have hstep := coupledOuterHeight_step_toward_one R hR
          m n k i (h + 1) hkm hkn (by omega) (by omega) (by omega)
            (hlower i ((h + 1) - 1))
        have htail := hInd (i + 1) (by omega) hhpos (by omega)
        have hidx : (i + 1) + h - 1 = i + (h + 1) - 1 := by omega
        rw [hidx] at htail
        exact Q'.eqv_trans _ _ _ hstep htail

/-- Consequently, a height-one certificate closes all heights once the
coupled reduced-label residual family is also available. -/
theorem coupledOuterHeight_zero_of_height_one_and_lower
    (R : Nat → Nat → Nat → Nat → Nat → Q')
    (hR : CoupledOuterHeightDifference R)
    (m n k i h : Nat)
    (hkm : k ≤ m) (hkn : k ≤ n)
    (hishell : i + h ≤ m) (hh : 0 < h) (hhn : h ≤ n)
    (hheightOne : ∀ u, R m n k u 1 ≈ 0)
    (hlower : ∀ u v,
      R (m - 1) (n - 1) (k - 1) u v ≈ 0) :
    R m n k i h ≈ 0 :=
  Q'.eqv_trans _ _ _
    (coupledOuterHeight_eqv_height_one R hR m n k i h
      hkm hkn hishell hh hhn hlower)
    (hheightOne (i + h - 1))

end YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence

#print axioms YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence.rightShellFactorialCoefficient_exposes_height
#print axioms YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence.outerHeightAdjacentDifference_lowers_labels
#print axioms YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence.sameOrderOuterHeightRecurrence_refuted
#print axioms YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence.transvectFactorialCoeff_coupledOuterHeightDifference
#print axioms YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence.coupledOuterHeight_step_toward_one
#print axioms YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence.coupledOuterHeight_eqv_height_one
#print axioms YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence.coupledOuterHeight_zero_of_height_one_and_lower
