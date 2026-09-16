/-
# A positive variance in the actual spatial scalar limit

The recentered fundamental face character has the same local star-ratio
variance floor in every box, heat stage and boundary-time buffer. Its two
raw moments have the same original selected action and partition. Passing
their actual three-regulator diagonal to the constructed spatial scalars
preserves this positive rational floor.

The limit variance is the second spatial moment minus the square of the
first spatial moment. Multiplication is passed through convergence, not
identified with multiplication of matching canonical approximation indices.
This proves scalar nontriviality at the displayed small nome; it constructs
no spatially completed vector carrier, uniform gap or continuum theory.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance (recenter_faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Spatial translation leaves the literal empty-observable presentation fixed. -/
theorem recenter_unit (base margin : Nat) :
    recenter margin (unit base) = unit (paddedWidth base margin) := Subtype.ext rfl

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (base : Nat) (p : Z4Plaq) (hp : p ∈ spatialFaces base)

local notation "x" => faceSpan base p hp

attribute [local irreducible] chartScalar spatialLimit

/-- All three raw scalars name the SAME finite original chart action and Z. -/
theorem recentered_variance_floor (margin stage t : Nat) :
    starRatio w ≤ recenteredScalar hw0 hw1 base 0 x x margin stage t +
      -(recenteredScalar hw0 hw1 base 0 x (unit base) margin stage t *
        recenteredScalar hw0 hw1 base 0 x (unit base) margin stage t) := by
  unfold recenteredScalar
  rw [recenter_faceSpan base p hp margin, recenter_unit]
  exact BF4ExactSlabFixedSpatialLocalVariance.chart_variance_floor hw0 hw1 _ _ _ stage t

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

/-- The genuine spatial-limit second moment minus the square of its first moment. -/
def spatialVariance : CReal :=
  let mean := spatialLimit hw0 hw1 base 0 x (unit base)
    (Nat.le_refl 0) (Nat.le_refl 0) hsmall hd hs hb
  sub (spatialLimit hw0 hw1 base 0 x x (Nat.le_refl 0) (Nat.le_refl 0)
    hsmall hd hs hb) (mul mean mean)

/-- The common raw variance diagonal converges to these exact spatial scalars. -/
theorem spatialVariance_converges :
    ConvergesTo (fun n => ofQ'
      (recenteredScalar hw0 hw1 base 0 x x n n n +
        -(recenteredScalar hw0 hw1 base 0 x (unit base) n n n *
          recenteredScalar hw0 hw1 base 0 x (unit base) n n n)))
      (spatialVariance hw0 hw1 base p hp hsmall hd hs hb) := by
  have hsecond := spatial_diagonal_converges hw0 hw1 base 0 x x
    (Nat.le_refl 0) (Nat.le_refl 0) hsmall hd hs hb
  have hmean := spatial_diagonal_converges hw0 hw1 base 0 x (unit base)
    (Nat.le_refl 0) (Nat.le_refl 0) hsmall hd hs hb
  have h : ConvergesTo (fun n =>
      add (ofQ' (recenteredScalar hw0 hw1 base 0 x x n n n))
        (neg (mul (ofQ' (recenteredScalar hw0 hw1 base 0 x (unit base) n n n))
          (ofQ' (recenteredScalar hw0 hw1 base 0 x (unit base) n n n)))))
      (spatialVariance hw0 hw1 base p hp hsmall hd hs hb) :=
    TrigAddCReal.convergesTo_add hsecond (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hmean hmean))
  apply TrigAddCReal.convergesTo_congr_seq _ h
  intro n
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- The positive lower bound depends only on w, after all three regulator limits. -/
theorem spatialVariance_floor :
    leEv (ofQ' (starRatio w)) (spatialVariance hw0 hw1 base p hp hsmall hd hs hb) :=
  leEv_of_convergesTo_le (CReal.convergesTo_const (ofQ' (starRatio w)))
    (spatialVariance_converges hw0 hw1 base p hp hsmall hd hs hb)
    (fun n => leEv_ofQ'_of_approx_ge
      (fun _ => recentered_variance_floor hw0 hw1 base p hp n n n))

/-- The spatial scalar limit has a genuinely nonzero fundamental-character variance. -/
theorem spatialVariance_ne_zero :
    ¬ Equiv (spatialVariance hw0 hw1 base p hp hsmall hd hs hb) (ofQ' 0) := by
  intro hz
  have h := leEv_trans (spatialVariance_floor hw0 hw1 base p hp hsmall hd hs hb)
    (leEv_of_equiv hz)
  have hle : starRatio w ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (starRatio_positive hw0 hw1) hle)

#print axioms recenter_unit
#print axioms recentered_variance_floor
#print axioms spatialVariance
#print axioms spatialVariance_converges
#print axioms spatialVariance_floor
#print axioms spatialVariance_ne_zero

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialVariance
