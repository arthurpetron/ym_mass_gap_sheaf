/-
# Supported physical contexts and ambient signed-time contexts are the same

The vacuum pairing of an actual supported product is the ordinary original
signed-time product mean. This exact same-carrier pin, combined with ordinary
square-nullity, identifies the supported time-tested relation with the ambient
all-test relation at any common spatial base.

The reverse implication goes through the existing reflected squared distance
and its null embedding theorem. It never identifies ordinary and reflected
norms, assumes an OS-null ideal, or substitutes another completed carrier.
Canonical scalar/OS realization, scaling, continuum QFT and Clay remain open.
-/

import YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra
import YMGap.Continuum.BF4WilsonSignedTimeContextInclusion

namespace YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression
open YMGap.Continuum.BF4WilsonSignedTimeExpectation
open YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra
open YMGap.Continuum.BF4WilsonSignedTimeContext
open YMGap.Continuum.BF4WilsonSignedTimeCauchySchwarz
open YMGap.Continuum.BF4WilsonSignedTimeContextInclusion
  (context_iff_square_zero mean_difference_mul context_include)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression intrinsicForm unit)
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionProduct
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner completedInner_embedStage)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Literal original source at a witnessed larger spatial base. -/
def sourceAt (x : Stage) {N : Nat} (hx : x.base ≤ N) : Expression N :=
  fromIntrinsic (atBase x hx)

theorem sourceAt_product (x y : Stage) {N : Nat}
    (hx : x.base ≤ N) (hy : y.base ≤ N) :
    sourceAt (productStage x y) (Nat.max_le.mpr ⟨hx,hy⟩) =
      .mul (sourceAt x hx) (sourceAt y hy) := by
  unfold sourceAt
  rw [atBase_product, fromIntrinsic_product]

theorem sourceAt_difference (x y : Stage) {N : Nat}
    (hx : x.base ≤ N) (hy : y.base ≤ N) :
    sourceAt (difference x y) (Nat.max_le.mpr ⟨hx,hy⟩) =
      BF4WilsonSignedTimeContextInclusion.difference (sourceAt x hx) (sourceAt y hy) := by
  unfold sourceAt
  rw [atBase_difference, fromIntrinsic_difference]
  rfl

theorem sourceAt_time (n : Nat) (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    sourceAt (time n x) hx = forward n (sourceAt x hx) := by
  unfold sourceAt
  rw [atBase_time, fromIntrinsic_advance]

theorem sourceAt_trans (x : Stage) {N M : Nat} (hx : x.base ≤ N) (hNM : N ≤ M) :
    sourceAt x (Nat.le_trans hx hNM) =
      BF4WilsonSignedTimeBaseInclusion.inclusion hNM (sourceAt x hx) := by
  unfold sourceAt
  rw [← atBase_trans x hx hNM, fromIntrinsic_inclusion]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

/-- Reflection invariance and the actual unit remove reflection only in the
vacuum mean; they do not identify the two quadratic forms. -/
theorem intrinsicForm_unit_mean {base : Nat} (hb : 0 < base)
    (x : IntrinsicExpression base) :
    Equiv (intrinsicForm hw0 hw1 hsmall hd hs hb x (unit base))
      (mean hw0 hw1 hsmall hd hs hb (fromIntrinsic x)) := by
  have h := (mean_reflected_intrinsic hw0 hw1 hsmall hd hs hb x (unit base)).symm
  rw [fromIntrinsic_unit] at h
  exact h.trans ((mean_mul_one hw0 hw1 hsmall hd hs hb _).trans
    (mean_reflect hw0 hw1 hsmall hd hs hb _))

/-- Vacuum expectation of the same stage, at any witnessed common base. -/
theorem pairing_unit_mean_at (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    Equiv (pairing hw0 hw1 hsmall hd hs x unitStage)
      (mean hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx) (sourceAt x hx)) := by
  have hu : 1 ≤ N := Nat.le_trans (Nat.succ_le_of_lt x.positive) hx
  have h := pairing_at_base hw0 hw1 hsmall hd hs x unitStage N hx hu
  rw [atBase_unit] at h
  exact h.trans (intrinsicForm_unit_mean hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx))

/-- The supported product-vacuum scalar is the ordinary original product
mean at the same base, not a surrogate functional. -/
theorem product_vacuum_mean_at (x y : Stage) {N : Nat}
    (hx : x.base ≤ N) (hy : y.base ≤ N) :
    Equiv (pairing hw0 hw1 hsmall hd hs (productStage x y) unitStage)
      (mean hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
        (.mul (sourceAt x hx) (sourceAt y hy))) := by
  have h := pairing_unit_mean_at hw0 hw1 hsmall hd hs (productStage x y)
    (Nat.max_le.mpr ⟨hx,hy⟩)
  rwa [sourceAt_product] at h

theorem completedProductVacuum_mean_at (x y : Stage) {N : Nat}
    (hx : x.base ≤ N) (hy : y.base ≤ N) :
    completedInner hw0 hw1 hsmall hd hs
        (embedStage hw0 hw1 hsmall hd hs (productStage x y))
        (completedUnit hw0 hw1 hsmall hd hs) =
      Quotient.mk crealSetoid (mean hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le x.positive hx) (.mul (sourceAt x hx) (sourceAt y hy))) := by
  rw [completedUnit, completedInner_embedStage]
  exact Quotient.sound (product_vacuum_mean_at hw0 hw1 hsmall hd hs x y hx hy)

/-- One supported difference test at time zero suffices: after the exact
vacuum pin, ordinary square-nullity handles every ambient signed test. -/
theorem context_of_difference_test {x y : Stage} {N : Nat}
    (hx : x.base ≤ N) (hy : y.base ≤ N)
    (hstate : embedStage hw0 hw1 hsmall hd hs (productStage x (difference x y)) =
      embedStage hw0 hw1 hsmall hd hs (productStage y (difference x y))) :
    ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (sourceAt x hx) (sourceAt y hy) := by
  let hb := Nat.lt_of_lt_of_le x.positive hx
  let a := sourceAt x hx
  let b := sourceAt y hy
  let d := BF4WilsonSignedTimeContextInclusion.difference a b
  have hz : (difference x y).base ≤ N := Nat.max_le.mpr ⟨hx,hy⟩
  have hp := congrArg (fun v => completedInner hw0 hw1 hsmall hd hs v
    (completedUnit hw0 hw1 hsmall hd hs)) hstate
  dsimp only at hp
  rw [completedProductVacuum_mean_at hw0 hw1 hsmall hd hs x (difference x y) hx hz,
    completedProductVacuum_mean_at hw0 hw1 hsmall hd hs y (difference x y) hy hz,
    sourceAt_difference x y hx hy] at hp
  have hm : Equiv (mean hw0 hw1 hsmall hd hs hb (.mul a d))
      (mean hw0 hw1 hsmall hd hs hb (.mul b d)) := Quotient.exact hp
  apply (context_iff_square_zero hw0 hw1 hsmall hd hs hb a b).mpr
  exact (mean_difference_mul hw0 hw1 hsmall hd hs hb a b d).trans
    ((Equiv_add hm (Equiv.refl _)).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        Q'.add_neg_self_eqv ((mean hw0 hw1 hsmall hd hs hb (.mul b d)).approx n))))

theorem context_of_timeContext {x y : Stage} {N : Nat}
    (hx : x.base ≤ N) (hy : y.base ≤ N)
    (h : TimeContextEq hw0 hw1 hsmall hd hs x y) :
    ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (sourceAt x hx) (sourceAt y hy) := by
  apply context_of_difference_test hw0 hw1 hsmall hd hs hx hy
  simpa only [time_zero] using h 0 (difference x y)

/-- Ambient nullity yields zero actual reflected distance, hence equality
inside the SAME already constructed completion. -/
theorem embedStage_eq_of_context {x y : Stage} {N : Nat}
    (hx : x.base ≤ N) (hy : y.base ≤ N)
    (h : ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (sourceAt x hx) (sourceAt y hy)) :
    embedStage hw0 hw1 hsmall hd hs x = embedStage hw0 hw1 hsmall hd hs y := by
  let hb := Nat.lt_of_lt_of_le x.positive hx
  let a := sourceAt x hx
  let b := sourceAt y hy
  let d := BF4WilsonSignedTimeContextInclusion.difference a b
  let delta := BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.difference
    (atBase x hx) (atBase y hy)
  have hz := (context_iff_square_zero hw0 hw1 hsmall hd hs hb a b).mp h
  have hm := mean_radical_zero hw0 hw1 hsmall hd hs hb d (reflect d) hz
  have hr : Equiv (mean hw0 hw1 hsmall hd hs hb (.mul (reflect d) d)) (ofQ' 0) :=
    (context_mean hw0 hw1 hsmall hd hs hb
      (context_mul_comm hw0 hw1 hsmall hd hs hb (reflect d) d)).trans hm
  have hpin := (mean_reflected_intrinsic hw0 hw1 hsmall hd hs hb delta delta).symm
  have hdsource : fromIntrinsic delta = d := fromIntrinsic_difference _ _
  rw [hdsource] at hpin
  apply (unionSeminorm hw0 hw1 hsmall hd hs).embedRep_eq_of_null
  exact (distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy).trans (hpin.trans hr)

attribute [local irreducible] mean sourceAt

/-- Inverse direction retains all forward times and all supported product
tests, using larger-base contextual inclusion before the reflected null pin. -/
theorem timeContext_of_context {x y : Stage} {N : Nat}
    (hx : x.base ≤ N) (hy : y.base ≤ N)
    (h : ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (sourceAt x hx) (sourceAt y hy)) :
    TimeContextEq hw0 hw1 hsmall hd hs x y := by
  intro n z
  let M := max N z.base
  have hNM : N ≤ M := Nat.le_max_left _ _
  have hxM : x.base ≤ M := Nat.le_trans hx hNM
  have hyM : y.base ≤ M := Nat.le_trans hy hNM
  have hzM : z.base ≤ M := Nat.le_max_right _ _
  have hlarge := context_include hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) hNM h
  have hsources : ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hxM)
      (sourceAt x hxM) (sourceAt y hyM) := by
    simpa only [sourceAt_trans x hx hNM, sourceAt_trans y hy hNM] using hlarge
  have htime := context_forward hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hxM) n hsources
  have hproduct := context_mul_right hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hxM) htime (sourceAt z hzM)
  have hfinal : ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hxM)
      (sourceAt (productStage (time n x) z) (Nat.max_le.mpr ⟨hxM,hzM⟩))
      (sourceAt (productStage (time n y) z) (Nat.max_le.mpr ⟨hyM,hzM⟩)) := by
    simpa only [sourceAt_product (time n x) z hxM hzM,
      sourceAt_product (time n y) z hyM hzM,
      sourceAt_time n x hxM, sourceAt_time n y hyM] using hproduct
  exact embedStage_eq_of_context hw0 hw1 hsmall hd hs
    (x := productStage (time n x) z) (y := productStage (time n y) z)
    (Nat.max_le.mpr ⟨hxM,hzM⟩) (Nat.max_le.mpr ⟨hyM,hzM⟩) hfinal

/-- Exact identification of the two actual tested relations, at any common
base; neither implication is supplied as a new analytic hypothesis. -/
theorem timeContext_iff_context (x y : Stage) {N : Nat}
    (hx : x.base ≤ N) (hy : y.base ≤ N) :
    TimeContextEq hw0 hw1 hsmall hd hs x y ↔
      ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
        (sourceAt x hx) (sourceAt y hy) :=
  ⟨context_of_timeContext hw0 hw1 hsmall hd hs hx hy,
    timeContext_of_context hw0 hw1 hsmall hd hs hx hy⟩

/-- For this actual original state, one supported difference test detects
the entire time-tested relation. This is not a generic OS-null ideal claim. -/
theorem timeContext_iff_difference_test (x y : Stage) :
    TimeContextEq hw0 hw1 hsmall hd hs x y ↔
      embedStage hw0 hw1 hsmall hd hs (productStage x (difference x y)) =
        embedStage hw0 hw1 hsmall hd hs (productStage y (difference x y)) := by
  constructor
  · intro h
    simpa only [time_zero] using h 0 (difference x y)
  · intro h
    exact timeContext_of_context hw0 hw1 hsmall hd hs (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      (context_of_difference_test hw0 hw1 hsmall hd hs
        (Nat.le_max_left _ _) (Nat.le_max_right _ _) h)

end YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin

#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.sourceAt
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.sourceAt_product
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.sourceAt_difference
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.sourceAt_time
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.sourceAt_trans
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.intrinsicForm_unit_mean
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.pairing_unit_mean_at
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.product_vacuum_mean_at
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.completedProductVacuum_mean_at
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.context_of_difference_test
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.context_of_timeContext
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.embedStage_eq_of_context
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.timeContext_of_context
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.timeContext_iff_context
#print axioms YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin.timeContext_iff_difference_test
