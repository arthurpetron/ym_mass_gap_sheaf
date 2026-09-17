/-
# Equal-time Wilson operators commute on the SAME completed carrier

Two actual time-zero character multipliers have arbitrary source loops,
spins and finite support bases. At one computed common base their original
reflected integrands agree by polynomial reassociation and commutativity.
The existing spatial limits and represented pairing limits preserve that
identity. Separation by the SAME completed pairing then proves operator
commutation on every vector of the existing UnionCompletion.

The product of the two existing bounded symmetric operators is consequently
symmetric in that same RC-valued pairing. No new carrier, scalar conversion,
analytic premise or canonical frontier field is introduced. These are
equal-time observable-algebra laws at fixed spacing and the original
small-nome guards, not continuum spacelike locality or full QFT axioms.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator

namespace YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (chartInsertion chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit (spatialLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws (spatialLimit_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier (multiply chart_multiply)
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (pairingData representativeInner completedInner completedInner_symm)
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator
  (completedInner_multiplier_balance)
open YMGap.Continuum.CRealSeminormPairingCompletion (pairSequence_converges)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

private theorem polynomial_left_comm (a b e : RatPoly) :
    RatPolyCoeffEqv (polyMul a (polyMul b e)) (polyMul b (polyMul a e)) :=
  (RatPolyCoeffEqv.mul_assoc a b e).symm.trans
    (((RatPolyCoeffEqv.mul_comm a b).mul_right e).trans
      (RatPolyCoeffEqv.mul_assoc b a e))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

attribute [local irreducible] chartScalar spatialLimit

/-- The full original action and common partition are unchanged in this identity. -/
theorem form_multiplier_comm {base : Nat} (hb : 0 < base) (H : Nat)
    (L R : SourceLoop base) (i j : Nat) (g e : WindowExpression base)
    (hg : Within H g) (he : Within H e) :
    Equiv (form hw0 hw1 hsmall hd hs hb H g
      (.mul (.loop H L i) (.mul (.loop H R j) e)) hg
      ⟨Nat.le_refl _, ⟨Nat.le_refl _, he⟩⟩)
      (form hw0 hw1 hsmall hd hs hb H g
        (.mul (.loop H R j) (.mul (.loop H L i) e)) hg
        ⟨Nat.le_refl _, ⟨Nat.le_refl _, he⟩⟩) := by
  apply spatialLimit_congr hw0 hw1 hsmall hd hs hb H
    (.mul (mirror H g) (.mul (.loop H L i) (.mul (.loop H R j) e)))
    (.mul (mirror H g) (.mul (.loop H R j) (.mul (.loop H L i) e)))
    ⟨mirror_within H g, within_mono (by omega : H ≤ 2*H)
      (.mul (.loop H L i) (.mul (.loop H R j) e))
      ⟨Nat.le_refl _, ⟨Nat.le_refl _, he⟩⟩⟩
    ⟨mirror_within H g, within_mono (by omega : H ≤ 2*H)
      (.mul (.loop H R j) (.mul (.loop H L i) e))
      ⟨Nat.le_refl _, ⟨Nat.le_refl _, he⟩⟩⟩
  intro r t
  exact RatPolyCoeffEqv.mul_left (chartInsertion r H t (mirror H g))
    (polynomial_left_comm (chartInsertion r H t (.loop H L i))
      (chartInsertion r H t (.loop H R j)) (chartInsertion r H t e))

attribute [local irreducible] form

/-- Every expression retains its actual reflection center; the common chart
is computed from the two input radii. -/
theorem intrinsicForm_multiplier_comm {base : Nat} (hb : 0 < base)
    (L R : SourceLoop base) (i j : Nat) (x y : IntrinsicExpression base) :
    Equiv (intrinsicForm hw0 hw1 hsmall hd hs hb x (multiply L i (multiply R j y)))
      (intrinsicForm hw0 hw1 hsmall hd hs hb x (multiply R j (multiply L i y))) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  have hleft := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x
    (multiply L i (multiply R j y)) H hx hy
  have hright := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x
    (multiply R j (multiply L i y)) H hx hy
  simp only [chart_multiply H L i (multiply R j y) hy,
    chart_multiply H R j y hy] at hleft
  simp only [chart_multiply H R j (multiply L i y) hy,
    chart_multiply H L i y hy] at hright
  exact hleft.trans ((form_multiplier_comm hw0 hw1 hsmall hd hs hb H L R i j
    (chart H x) (chart H y) (chart_within H x hx) (chart_within H y hy)).trans hright.symm)

attribute [local irreducible] pairing intrinsicForm

/-- Loops and states may have different bases. One finite maximum suffices
for each pairing; no common base for an entire Cauchy stream is assumed. -/
theorem pairing_multiplier_comm {leftBase rightBase : Nat}
    (L : SourceLoop leftBase) (R : SourceLoop rightBase) (i j : Nat) (x y : Stage) :
    Equiv (pairing hw0 hw1 hsmall hd hs x (multiplyStage L i (multiplyStage R j y)))
      (pairing hw0 hw1 hsmall hd hs x (multiplyStage R j (multiplyStage L i y))) := by
  let N := max (max leftBase rightBase) (max x.base y.base)
  have hL : leftBase ≤ N := by omega
  have hR : rightBase ≤ N := by omega
  have hx : x.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hRy : (multiplyStage R j y).base ≤ N := Nat.max_le.mpr ⟨hR, hy⟩
  have hLy : (multiplyStage L i y).base ≤ N := Nat.max_le.mpr ⟨hL, hy⟩
  have hleft := pairing_at_base hw0 hw1 hsmall hd hs x
    (multiplyStage L i (multiplyStage R j y)) N hx (Nat.max_le.mpr ⟨hL, hRy⟩)
  have hright := pairing_at_base hw0 hw1 hsmall hd hs x
    (multiplyStage R j (multiplyStage L i y)) N hx (Nat.max_le.mpr ⟨hR, hLy⟩)
  simp only [atBase_multiply L i (multiplyStage R j y) hL hRy,
    atBase_multiply R j y hR hy] at hleft
  simp only [atBase_multiply R j (multiplyStage L i y) hR hLy,
    atBase_multiply L i y hL hy] at hright
  exact hleft.trans ((intrinsicForm_multiplier_comm hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) (loopAt L hL) (loopAt R hR) i j
    (atBase x hx) (atBase y hy)).trans hright.symm)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "I" => representativeInner hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "M" => completedMultiply hw0 hw1 hsmall hd hs
local notation "C" => multiplyCauchy hw0 hw1 hsmall hd hs

theorem representativeInner_multiplier_comm {leftBase rightBase : Nat}
    (L : SourceLoop leftBase) (R : SourceLoop rightBase) (i j : Nat) (X Y : (D).Cauchy) :
    Equiv (I X (C L i (C R j Y))) (I X (C R j (C L i Y))) :=
  Equiv_of_limit_of_equal
    (fun n => pairing_multiplier_comm hw0 hw1 hsmall hd hs L R i j (X.seq n) (Y.seq n))
    (pairSequence_converges PD X (C L i (C R j Y)))
    (pairSequence_converges PD X (C R j (C L i Y)))

theorem completedInner_multiplier_comm {leftBase rightBase : Nat}
    (L : SourceLoop leftBase) (R : SourceLoop rightBase) (i j : Nat) (x y : V) :
    B x (M L i (M R j y)) = B x (M R j (M L i y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound
    (representativeInner_multiplier_comm hw0 hw1 hsmall hd hs L R i j X Y)

/-- Equality of the existing operators on EVERY completed state, proved by
the separating original pairing. This is an equal-time, fixed-spacing law. -/
theorem completedMultiply_comm {leftBase rightBase : Nat}
    (L : SourceLoop leftBase) (R : SourceLoop rightBase) (i j : Nat) (x : V) :
    M L i (M R j x) = M R j (M L i x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_symm hw0 hw1 hsmall hd hs (M L i (M R j x)) test,
    completedInner_symm hw0 hw1 hsmall hd hs (M R j (M L i x)) test]
  exact completedInner_multiplier_comm hw0 hw1 hsmall hd hs L R i j test x

/-- The product is symmetric in the SAME RC-valued form, using the proved
commutation law rather than an assumed observable representation. -/
theorem completedInner_multiplier_product_balance {leftBase rightBase : Nat}
    (L : SourceLoop leftBase) (R : SourceLoop rightBase) (i j : Nat) (x y : V) :
    B (M L i (M R j x)) y = B x (M L i (M R j y)) := by
  rw [completedInner_multiplier_balance, completedInner_multiplier_balance,
    completedMultiply_comm hw0 hw1 hsmall hd hs R L j i y]

#print axioms form_multiplier_comm
#print axioms intrinsicForm_multiplier_comm
#print axioms pairing_multiplier_comm
#print axioms representativeInner_multiplier_comm
#print axioms completedInner_multiplier_comm
#print axioms completedMultiply_comm
#print axioms completedInner_multiplier_product_balance

end YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroCommutation
