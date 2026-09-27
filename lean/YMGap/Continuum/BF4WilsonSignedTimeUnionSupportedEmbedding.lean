/-
# The supported Wilson observable quotient embeds into the all-base ambient one

The map uses each actual supported source at its own positive spatial base.
Its relation is precisely the already proved supported/ambient contextual
equivalence at a computed common base. Injectivity does not assume product
congruence on arbitrary OS-null completion classes, and no ambient
surjectivity or canonical reflected OS realization is claimed.
-/

import YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin
import YMGap.Continuum.BF4WilsonSignedTimeUnionObservable
import YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient

namespace YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression (Expression)
open YMGap.Continuum.BF4WilsonSignedTimeExpectation (fromIntrinsic)
open YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra
open YMGap.Continuum.BF4WilsonSignedTimeSupportedJoin
open YMGap.Continuum.BF4WilsonSpatialUnion (Stage atBase unitStage sumStage smulStage time)
open YMGap.Continuum.BF4WilsonSpatialUnionProduct (productStage)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Each original supported stage determines a signed-time stage at exactly
its original positive spatial base. -/
def sourceSupported (x : Stage) : BF4WilsonSignedTimeUnion.Stage :=
  ⟨x.base, x.positive, fromIntrinsic x.value⟩

/-- Source transport to any larger base agrees literally with signed union
transport; no CReal representative is chosen. -/
theorem sourceSupported_at (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    BF4WilsonSignedTimeUnion.atBase (sourceSupported x) hx = sourceAt x hx :=
  (fromIntrinsic_inclusion hx x.value).symm

theorem sourceAt_sum (x y : Stage) {N : Nat}
    (hx : x.base ≤ N) (hy : y.base ≤ N) :
    sourceAt (sumStage x y) (Nat.max_le.mpr ⟨hx,hy⟩) =
      .add (sourceAt x hx) (sourceAt y hy) := by
  unfold sourceAt
  rw [BF4WilsonSpatialUnion.atBase_sum, fromIntrinsic_sum]

theorem sourceAt_smul (s : Q') (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    sourceAt (smulStage s x) hx = .smul s (sourceAt x hx) := by
  unfold sourceAt
  rw [BF4WilsonSpatialUnion.atBase_smul, fromIntrinsic_smul]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

/-- The old supported tested relation is exactly the restriction of the
all-base ordinary contextual relation, not merely a one-way implication. -/
theorem related_iff_timeContext (x y : Stage) :
    BF4WilsonSignedTimeUnion.Related hw0 hw1 hsmall hd hs
      (sourceSupported x) (sourceSupported y) ↔
      BF4WilsonSpatialUnionProduct.TimeContextEq hw0 hw1 hsmall hd hs x y := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  change BF4WilsonSignedTimeContext.ContextEq hw0 hw1 hsmall hd hs
      (Nat.lt_of_lt_of_le x.positive hx)
      (BF4WilsonSignedTimeUnion.atBase (sourceSupported x) hx)
      (BF4WilsonSignedTimeUnion.atBase (sourceSupported y) hy) ↔ _
  rw [sourceSupported_at x hx, sourceSupported_at y hy]
  exact (timeContext_iff_context hw0 hw1 hsmall hd hs x y hx hy).symm

private theorem related_of_at_eq (a b : BF4WilsonSignedTimeUnion.Stage) {N : Nat}
    (ha : a.base ≤ N) (hb : b.base ≤ N)
    (he : BF4WilsonSignedTimeUnion.atBase a ha =
      BF4WilsonSignedTimeUnion.atBase b hb) :
    BF4WilsonSignedTimeUnion.Related hw0 hw1 hsmall hd hs a b := by
  apply (BF4WilsonSignedTimeUnion.related_iff_at hw0 hw1 hsmall hd hs a b ha hb).mpr
  rw [he]
  exact BF4WilsonSignedTimeContext.context_refl hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le a.positive ha) _

private theorem sourceSupported_product_related (x y : Stage) :
    BF4WilsonSignedTimeUnion.Related hw0 hw1 hsmall hd hs
      (sourceSupported (productStage x y))
      (BF4WilsonSignedTimeUnion.mulStage (sourceSupported x) (sourceSupported y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  apply related_of_at_eq hw0 hw1 hsmall hd hs _ _ (Nat.le_refl N) (Nat.le_refl N)
  rw [sourceSupported_at, sourceAt_product x y hx hy,
    BF4WilsonSignedTimeUnion.atBase_mul (sourceSupported x) (sourceSupported y) hx hy,
    sourceSupported_at x hx, sourceSupported_at y hy]

private theorem sourceSupported_sum_related (x y : Stage) :
    BF4WilsonSignedTimeUnion.Related hw0 hw1 hsmall hd hs
      (sourceSupported (sumStage x y))
      (BF4WilsonSignedTimeUnion.addStage (sourceSupported x) (sourceSupported y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  apply related_of_at_eq hw0 hw1 hsmall hd hs _ _ (Nat.le_refl N) (Nat.le_refl N)
  rw [sourceSupported_at, sourceAt_sum x y hx hy,
    BF4WilsonSignedTimeUnion.atBase_add (sourceSupported x) (sourceSupported y) hx hy,
    sourceSupported_at x hx, sourceSupported_at y hy]

private theorem sourceSupported_smul_related (s : Q') (x : Stage) :
    BF4WilsonSignedTimeUnion.Related hw0 hw1 hsmall hd hs
      (sourceSupported (smulStage s x))
      (BF4WilsonSignedTimeUnion.smulStage s (sourceSupported x)) := by
  apply related_of_at_eq hw0 hw1 hsmall hd hs _ _ (Nat.le_refl x.base) (Nat.le_refl x.base)
  rw [sourceSupported_at, sourceAt_smul s x (Nat.le_refl _),
    BF4WilsonSignedTimeUnion.atBase_smul, sourceSupported_at]

private theorem sourceSupported_forward_related (n : Nat) (x : Stage) :
    BF4WilsonSignedTimeUnion.Related hw0 hw1 hsmall hd hs
      (sourceSupported (time n x))
      (BF4WilsonSignedTimeUnion.forwardStage n (sourceSupported x)) := by
  apply related_of_at_eq hw0 hw1 hsmall hd hs _ _ (Nat.le_refl x.base) (Nat.le_refl x.base)
  rw [sourceSupported_at, sourceAt_time n x (Nat.le_refl _),
    BF4WilsonSignedTimeUnion.atBase_forward, sourceSupported_at]

private theorem sourceSupported_unit :
    sourceSupported unitStage = BF4WilsonSignedTimeUnion.unitStage := by
  change (⟨1, _, fromIntrinsic (BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit 1)⟩ :
    BF4WilsonSignedTimeUnion.Stage) = ⟨1, _, .one⟩
  rw [fromIntrinsic_unit]

/-- An injective map of the two actual contextual quotients. -/
def embedding : BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs →
    BF4WilsonSignedTimeUnionObservable.Observable hw0 hw1 hsmall hd hs :=
  Quotient.lift
    (fun x => BF4WilsonSignedTimeUnionObservable.ofStage hw0 hw1 hsmall hd hs
      (sourceSupported x))
    (fun x y h => Quotient.sound
      ((related_iff_timeContext hw0 hw1 hsmall hd hs x y).mpr h))

theorem embedding_injective
    (a b : BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs)
    (hab : embedding hw0 hw1 hsmall hd hs a = embedding hw0 hw1 hsmall hd hs b) :
    a = b := by
  induction a using Quotient.inductionOn with
  | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
      exact Quotient.sound ((related_iff_timeContext hw0 hw1 hsmall hd hs x y).mp
        (Quotient.exact hab))

theorem embedding_one :
    embedding hw0 hw1 hsmall hd hs
      (BF4WilsonSpatialUnionObservableQuotient.one hw0 hw1 hsmall hd hs) =
      BF4WilsonSignedTimeUnionObservable.one hw0 hw1 hsmall hd hs := by
  exact congrArg (BF4WilsonSignedTimeUnionObservable.ofStage hw0 hw1 hsmall hd hs)
    sourceSupported_unit

theorem embedding_mul
    (a b : BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs) :
    embedding hw0 hw1 hsmall hd hs
        (BF4WilsonSpatialUnionObservableQuotient.mul hw0 hw1 hsmall hd hs a b) =
      BF4WilsonSignedTimeUnionObservable.mul hw0 hw1 hsmall hd hs
        (embedding hw0 hw1 hsmall hd hs a) (embedding hw0 hw1 hsmall hd hs b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (sourceSupported_product_related hw0 hw1 hsmall hd hs x y)

theorem embedding_add
    (a b : BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs) :
    embedding hw0 hw1 hsmall hd hs
        (BF4WilsonSpatialUnionObservableQuotient.add hw0 hw1 hsmall hd hs a b) =
      BF4WilsonSignedTimeUnionObservable.add hw0 hw1 hsmall hd hs
        (embedding hw0 hw1 hsmall hd hs a) (embedding hw0 hw1 hsmall hd hs b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (sourceSupported_sum_related hw0 hw1 hsmall hd hs x y)

theorem embedding_smul (s : Q')
    (a : BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs) :
    embedding hw0 hw1 hsmall hd hs
        (BF4WilsonSpatialUnionObservableQuotient.smul hw0 hw1 hsmall hd hs s a) =
      BF4WilsonSignedTimeUnionObservable.smul hw0 hw1 hsmall hd hs s
        (embedding hw0 hw1 hsmall hd hs a) := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (sourceSupported_smul_related hw0 hw1 hsmall hd hs s x)

theorem embedding_forward (n : Nat)
    (a : BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs) :
    embedding hw0 hw1 hsmall hd hs
        (BF4WilsonSpatialUnionObservableQuotient.forward hw0 hw1 hsmall hd hs n a) =
      BF4WilsonSignedTimeUnionObservable.forwardTime hw0 hw1 hsmall hd hs n
        (embedding hw0 hw1 hsmall hd hs a) := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (sourceSupported_forward_related hw0 hw1 hsmall hd hs n x)

/-- The ambient original mean restricts to the existing supported vacuum
mean. This is a pin on the embedded subobject, not a state map into the
physical completion for arbitrary ambient signed expressions. -/
theorem embedding_mean
    (a : BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs) :
    BF4WilsonSignedTimeUnionObservable.meanRC hw0 hw1 hsmall hd hs
        (embedding hw0 hw1 hsmall hd hs a) =
      BF4WilsonSpatialUnionObservableQuotient.vacuumMean hw0 hw1 hsmall hd hs a := by
  refine Quotient.inductionOn a ?_
  intro x
  have hnew := BF4WilsonSignedTimeUnionObservable.meanRC_at hw0 hw1 hsmall hd hs
    (sourceSupported x) (Nat.le_refl x.base)
  rw [sourceSupported_at x (Nat.le_refl _)] at hnew
  exact hnew.trans ((Quotient.sound
    (pairing_unit_mean_at hw0 hw1 hsmall hd hs x (Nat.le_refl _)).symm).trans
      (BF4WilsonSpatialUnionObservableQuotient.vacuumMean_ofStage hw0 hw1 hsmall hd hs x).symm)

local notation "Amean" => BF4WilsonSignedTimeUnionObservable.meanRC hw0 hw1 hsmall hd hs
local notation "Amul" => BF4WilsonSignedTimeUnionObservable.mul hw0 hw1 hsmall hd hs
local notation "Atheta" => BF4WilsonSignedTimeUnionObservable.reflection hw0 hw1 hsmall hd hs
local notation "Atime" => BF4WilsonSignedTimeUnionObservable.forwardTime hw0 hw1 hsmall hd hs
local notation "B" => BF4WilsonSpatialUnionPairingData.completedInner hw0 hw1 hsmall hd hs
local notation "S" => BF4WilsonSpatialUnionObservableQuotient.state hw0 hw1 hsmall hd hs
local notation "j" => embedding hw0 hw1 hsmall hd hs

/-- The reflected ambient mean restricts to the SAME completed physical form
on the supported observable quotient; no new Hilbert carrier is selected. -/
theorem embedding_reflected_mean
    (a b : BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs) :
    Amean (Amul (Atheta (j a)) (j b)) = B (S a) (S b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  have hx := Nat.le_max_left x.base y.base
  have hy := Nat.le_max_right x.base y.base
  have hnew : Amean (Amul
      (Atheta (BF4WilsonSignedTimeUnionObservable.ofStage hw0 hw1 hsmall hd hs (sourceSupported x)))
      (BF4WilsonSignedTimeUnionObservable.ofStage hw0 hw1 hsmall hd hs (sourceSupported y))) =
      Quotient.mk crealSetoid (BF4WilsonSignedTimeExpectation.mean hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le x.positive hx)
        (.mul (BF4WilsonSignedTimeExpression.reflect (sourceAt x hx)) (sourceAt y hy))) := by
    change Quotient.mk crealSetoid (BF4WilsonSignedTimeExpectation.mean hw0 hw1 hsmall hd hs
      (Nat.lt_of_lt_of_le x.positive hx)
      (.mul (BF4WilsonSignedTimeUnion.atBase (BF4WilsonSignedTimeUnion.reflectStage (sourceSupported x)) hx)
        (BF4WilsonSignedTimeUnion.atBase (sourceSupported y) hy))) = _
    rw [BF4WilsonSignedTimeUnion.atBase_reflect (sourceSupported x) hx,
      sourceSupported_at x hx, sourceSupported_at y hy]
  exact hnew.trans (BF4WilsonSignedTimeExpectation.completedInner_as_mean hw0 hw1 hsmall hd hs x y).symm

/-- Reflection positivity is asserted on the embedded supported subalgebra,
not on arbitrary ambient signed-time expressions. -/
theorem embedding_reflection_positive
    (a : BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs) :
    RCnonneg (Amean (Amul (Atheta (j a)) (j a))) := by
  rw [embedding_reflected_mean]
  exact BF4WilsonSpatialUnionPairingData.completedInner_nonnegative hw0 hw1 hsmall hd hs (S a)

/-- All supported quotient correlators use the actual completed transfer and
the global ambient time action, on the same embedded observable. -/
theorem embedding_time_correlator (n : Nat)
    (a b : BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs) :
    Amean (Amul (Atheta (j a)) (Atime n (j b))) =
      B (S a) (BF4WilsonSpatialUnionSeminorm.completedTime hw0 hw1 hsmall hd hs n (S b)) := by
  rw [← embedding_forward, embedding_reflected_mean,
    BF4WilsonSpatialUnionObservableQuotient.state_forward]

end YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding

#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.sourceSupported
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.sourceSupported_at
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.sourceAt_sum
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.sourceAt_smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.related_iff_timeContext
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding_injective
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding_one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding_smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding_mean
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding_reflected_mean
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding_reflection_positive
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding.embedding_time_correlator
