/-
# Ordered-right normalization of the cyclic three-factor chart

The cyclic presentation `(b,c,a)` places the intermediate `(b,c)` output
before `a` in the outer tensor.  The repository's ordered right-associated
convention places `a` first.  Rectangle projection commutes with transposition,
so the uniform transvectant swap theorem gives the exact bridge: ordered raw
coordinates equal the cyclic coordinates times the outer swap phase.
-/

import YMGap.Continuum.SU2TransvectantSwapParity
import YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases

namespace YMGap.Continuum.SU2OrderedRightNormalizationBridge

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantSwapParity
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- Swap the two degree parameters of a physical channel without changing its
contraction order or output coefficient. -/
def transposePhysicalChannel {m n : Nat}
    (q : PhysicalCGChannel m n) : PhysicalCGChannel n m :=
  { k := q.k
    k_le := Nat.le_min.mpr ⟨(Nat.le_min.mp q.k_le).2,
      (Nat.le_min.mp q.k_le).1⟩
    s := q.s
    s_le := by
      have hs := q.s_le
      omega }

/-- Physical rectangle projection commutes pointwise with tensor
transposition. -/
theorem rectProject_transpose (m n : Nat) (x : BForm2) :
    BForm2Eqv (rectProject n m (transpose2 x))
      (transpose2 (rectProject m n x)) := by
  intro i j
  by_cases hi : i ≤ n
  · by_cases hj : j ≤ m
    · exact Q'.eqv_trans _ _ _
        (rectProject_apply_physical n m (transpose2 x) i j hi hj)
        (Q'.eqv_symm
          (rectProject_apply_physical m n x j i hj hi))
    · have hleft := rectProject_zero_outside n m (transpose2 x) i j
          (Or.inr (by omega))
      have hright := rectProject_zero_outside m n x j i
        (Or.inl (by omega))
      exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)
  · have hleft := rectProject_zero_outside n m (transpose2 x) i j
        (Or.inl (by omega))
    have hright := rectProject_zero_outside m n x j i
      (Or.inr (by omega))
    exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)

/-- The fixed ordered right-associated coordinate: first couple `(n,p)`, then
apply the outer transvectant with the original `m` factor first. -/
def orderedRightNestedCoordinates (m n p : Nat) (x : TriForm)
    (q : LeftNestedCGChannel n p m) : Q' :=
  globalTransvectCoordinates m (n + p - 2 * q.k)
    (transpose2 (firstPairOutput n p (rotateTri x) q.k))
    (transposePhysicalChannel q.outer)

/-- **Exact ordered/cyclic chart bridge.** -/
theorem orderedRight_eq_phase_cyclic (m n p : Nat) (x : TriForm)
    (q : LeftNestedCGChannel n p m) :
    orderedRightNestedCoordinates m n p x q ≈
      swapPhase q.outer.k * rightNestedCoordinates m n p x q := by
  let inner := firstPairOutput n p (rotateTri x) q.k
  have hproj := transvect_congr m (n + p - 2 * q.k) q.outer.k
    (rectProject_transpose (n + p - 2 * q.k) m inner) q.outer.s
  have hswap := transvect_transpose (n + p - 2 * q.k) m q.outer.k
    (rectProject (n + p - 2 * q.k) m inner) q.outer.s
  exact Q'.eqv_trans _ _ _
    (by simpa only [orderedRightNestedCoordinates,
      globalTransvectCoordinates, transposePhysicalChannel, inner] using hproj)
    (by simpa only [rightNestedCoordinates, leftNestedCoordinates,
      globalTransvectCoordinates, inner] using hswap)

private theorem neg_mul_neg (x y : Q') : (-x) * (-y) ≈ x * y := by
  exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv x (-y))
    (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv x y))
      (Q'.neg_neg_eqv (x * y)))

/-- The swap phase is its own inverse. -/
theorem swapPhase_mul_self : ∀ k, swapPhase k * swapPhase k ≈ 1
  | 0 => Q'.one_mul_eqv 1
  | k + 1 => by
      exact Q'.eqv_trans _ _ _
        (neg_mul_neg (swapPhase k) (swapPhase k))
        (swapPhase_mul_self k)

/-- The converse chart bridge, using the involutive exact sign. -/
theorem cyclic_eq_phase_orderedRight (m n p : Nat) (x : TriForm)
    (q : LeftNestedCGChannel n p m) :
    rightNestedCoordinates m n p x q ≈
      swapPhase q.outer.k * orderedRightNestedCoordinates m n p x q := by
  have hbridge := orderedRight_eq_phase_cyclic m n p x q
  have hmul := Q'.mul_eqv_congr_left (swapPhase q.outer.k) _ _ hbridge
  have hcollapse :
      swapPhase q.outer.k *
          (swapPhase q.outer.k * rightNestedCoordinates m n p x q) ≈
        rightNestedCoordinates m n p x q := by
    exact Q'.eqv_trans _
      ((swapPhase q.outer.k * swapPhase q.outer.k) *
        rightNestedCoordinates m n p x q) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _
        (1 * rightNestedCoordinates m n p x q) _
        (Q'.mul_eqv_congr_right _ _ _ (swapPhase_mul_self q.outer.k))
        (Q'.one_mul_eqv _))
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hmul hcollapse)

end YMGap.Continuum.SU2OrderedRightNormalizationBridge

#print axioms YMGap.Continuum.SU2OrderedRightNormalizationBridge.rectProject_transpose
#print axioms YMGap.Continuum.SU2OrderedRightNormalizationBridge.orderedRight_eq_phase_cyclic
#print axioms YMGap.Continuum.SU2OrderedRightNormalizationBridge.swapPhase_mul_self
#print axioms YMGap.Continuum.SU2OrderedRightNormalizationBridge.cyclic_eq_phase_orderedRight
