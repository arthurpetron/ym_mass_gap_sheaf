/-
# Three-parameter Cauchy control through one computed spatial pivot

A spatial comparison uniform in the two inner indices and an explicit
rectangular modulus at each fixed spatial index yield a Cauchy modulus
for the literal three-index diagonal. Only one row's modulus is used at
each tolerance: the spatial pivot is chosen first by geometric decay.
No modulus uniform over spatial rows and no monotonicity of the supplied
modulus are assumed.

The row limits also converge to this same diagonal limit. Their actual
representatives are the existing QMhat reindexings, whose indices are
at least the displayed approximation index. This is a scalar implication;
the intended chart consumer must supply its same-action spatial bound
and its already constructed fixed-width rectangular data.
-/

import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.GNSHilbertSpace
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.SpatialPivotCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local infix:50 " ≃ " => Q'.eqv

def quarter (epsilon : Q') : Q' := HalfPow.half * (HalfPow.half * epsilon)

theorem quarter_pos {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < quarter epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he)

/-- The harmless extra unit in the exponent also covers a zero decay rate. -/
def pivot (rho A : Q') (M : Nat) (epsilon : Q') : Nat :=
  M + geometricCutoff rho A (quarter epsilon)

/-- Both the spatial pivot and its one selected inner-row modulus. -/
def diagonalModulus (rho A : Q') (M : Nat)
    (jointModulus : Nat → Q' → Nat) (epsilon : Q') : Nat :=
  max (pivot rho A M epsilon) (jointModulus (pivot rho A M epsilon) (quarter epsilon))

theorem pivot_tail {rho A : Q'} (hrho0 : (0 : Q') ≤ rho) (hrho1 : rho < (1 : Q'))
    (hA : (0 : Q') ≤ A) (M : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) :
    A * rho^(pivot rho A M epsilon+1-M) ≤ quarter epsilon := by
  have hn : geometricCutoff rho A (quarter epsilon) ≤ pivot rho A M epsilon+1-M := by
    unfold pivot
    omega
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (geometric_bound hrho0 hrho1 hA (quarter_pos he) _ hn)

private theorem three_quarter_chain (epsilon : Q') (he : (0 : Q') < epsilon)
    (u v x z : Q') (hu : u ≤ v+quarter epsilon)
    (hv : v ≤ x+quarter epsilon) (hx : x ≤ z+quarter epsilon) : u ≤ z+epsilon := by
  let q := quarter epsilon
  have hq : (0 : Q') ≤ q := Q'.le_of_lt (quarter_pos he)
  have h1 := Q'.le_trans' _ _ _ hu (Q'.add_le_add_right _ _ q hv)
  have h2 := Q'.le_trans' _ _ _ h1
    (Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hx))
  have h3 := Q'.le_trans' _ _ _ h2 (Q'.add_le_self_of_nonneg _ q hq)
  have hfour : (((z+q)+q)+q)+q ≃ z+epsilon := by
    have hqq : q+q ≃ HalfPow.half*epsilon := ExpNeg.two_halves (HalfPow.half*epsilon)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ((z+q)+q) q q) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (q+q) (Q'.add_assoc_eqv z q q)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z (q+q) (q+q)) ?_
    exact Q'.add_eqv_congr_left z _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hqq hqq) (ExpNeg.two_halves epsilon))
  exact Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv hfour)

variable (C : Nat → Nat → Nat → Q') (rho A : Q') (M : Nat)
  (jointModulus : Nat → Q' → Nat)
  (hrho0 : (0 : Q') ≤ rho) (hrho1 : rho < (1 : Q')) (hA : (0 : Q') ≤ A)
  (hspatial : ∀ r d k t : Nat,
    Q'.abs (C (r+d) k t + -(C r k t)) ≤ A*rho^(r+1-M))
  (hjoint : ∀ (r : Nat) (epsilon : Q'), (0 : Q') < epsilon → ∀ k t j u : Nat,
    jointModulus r epsilon ≤ k → jointModulus r epsilon ≤ t →
    jointModulus r epsilon ≤ j → jointModulus r epsilon ≤ u →
    C r k t ≤ C r j u+epsilon ∧ C r j u ≤ C r k t+epsilon)

include hrho0 hrho1 hA hspatial hjoint in
/-- Independent late spatial indices and two independent inner coordinates.
The middle comparison takes place only at the computed spatial pivot. -/
theorem rectangle (epsilon : Q') (he : (0 : Q') < epsilon) (r k t s j u : Nat)
    (hr : pivot rho A M epsilon ≤ r) (hs : pivot rho A M epsilon ≤ s)
    (hk : jointModulus (pivot rho A M epsilon) (quarter epsilon) ≤ k)
    (ht : jointModulus (pivot rho A M epsilon) (quarter epsilon) ≤ t)
    (hj : jointModulus (pivot rho A M epsilon) (quarter epsilon) ≤ j)
    (hu : jointModulus (pivot rho A M epsilon) (quarter epsilon) ≤ u) :
    C r k t ≤ C s j u+epsilon ∧ C s j u ≤ C r k t+epsilon := by
  have hnear (v a b : Nat) (hv : pivot rho A M epsilon ≤ v) :
      C v a b ≤ C (pivot rho A M epsilon) a b+quarter epsilon ∧
        C (pivot rho A M epsilon) a b ≤ C v a b+quarter epsilon := by
    have h := hspatial (pivot rho A M epsilon) (v-pivot rho A M epsilon) a b
    rw [Nat.add_sub_of_le hv] at h
    have hb := Q'.le_trans' _ _ _ h (pivot_tail hrho0 hrho1 hA M epsilon he)
    exact ⟨ExpNeg.le_add_of_abs_sub_le hb,
      ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (ExpNeg.abs_sub_comm (C (pivot rho A M epsilon) a b) (C v a b))) hb)⟩
  have hleft := hnear r k t hr
  have hmiddle := hjoint (pivot rho A M epsilon) (quarter epsilon) (quarter_pos he)
    k t j u hk ht hj hu
  have hright := hnear s j u hs
  exact ⟨three_quarter_chain epsilon he _ _ _ _ hleft.1 hmiddle.1 hright.2,
    three_quarter_chain epsilon he _ _ _ _ hright.1 hmiddle.2 hleft.2⟩

/-- Explicit Cauchy data for each fixed spatial row, without geometric inputs. -/
def rowCauchy (r : Nat) : QCauchy (fun n => C r n n) where
  M := jointModulus r
  bound := fun epsilon he i j hi hj => hjoint r epsilon he i i j j hi hi hj hj

/-- Actual Type-level Cauchy data for the unmodified three-index diagonal. -/
def diagonalCauchy : QCauchy (fun n => C n n n) where
  M := diagonalModulus rho A M jointModulus
  bound := fun epsilon he i j hi hj =>
    rectangle C rho A M jointModulus hrho0 hrho1 hA hspatial hjoint epsilon he i i i j j j
      (Nat.le_trans (Nat.le_max_left _ _) hi) (Nat.le_trans (Nat.le_max_left _ _) hj)
      (Nat.le_trans (Nat.le_max_right _ _) hi) (Nat.le_trans (Nat.le_max_right _ _) hi)
      (Nat.le_trans (Nat.le_max_right _ _) hj) (Nat.le_trans (Nat.le_max_right _ _) hj)

def rowLimit (r : Nat) : CReal :=
  ofQ'CauchySeq _ (rowCauchy C jointModulus hjoint r)

def diagonalLimit : CReal :=
  ofQ'CauchySeq _ (diagonalCauchy C rho A M jointModulus hrho0 hrho1 hA hspatial hjoint)

theorem diagonal_converges :
    ConvergesTo (fun n => ofQ' (C n n n))
      (diagonalLimit C rho A M jointModulus hrho0 hrho1 hA hspatial hjoint) :=
  convergesTo_ofQ'CauchySeq _
    (diagonalCauchy C rho A M jointModulus hrho0 hrho1 hA hspatial hjoint)

/-- The same rectangle compares any late raw value with the actual diagonal
representative. No existential row-modulus witness is selected. -/
theorem diagonal_approx (epsilon : Q') (he : (0 : Q') < epsilon) (r k t i : Nat)
    (hr : pivot rho A M epsilon ≤ r)
    (hk : jointModulus (pivot rho A M epsilon) (quarter epsilon) ≤ k)
    (ht : jointModulus (pivot rho A M epsilon) (quarter epsilon) ≤ t)
    (hi : diagonalModulus rho A M jointModulus epsilon ≤ i) :
    C r k t ≤ (diagonalLimit C rho A M jointModulus hrho0 hrho1 hA hspatial hjoint).approx i+epsilon ∧
      (diagonalLimit C rho A M jointModulus hrho0 hrho1 hA hspatial hjoint).approx i ≤ C r k t+epsilon := by
  let c := diagonalCauchy C rho A M jointModulus hrho0 hrho1 hA hspatial hjoint
  let b := QMhat _ c i
  have hbi : i ≤ b := self_le_QMhat _ c i
  have hb : pivot rho A M epsilon ≤ b :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hi) hbi
  have hbrow : jointModulus (pivot rho A M epsilon) (quarter epsilon) ≤ b :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hi) hbi
  exact rectangle C rho A M jointModulus hrho0 hrho1 hA hspatial hjoint
    epsilon he r k t b b b hr hb hk ht hbrow hbrow

/-- Row limits converge to the SAME diagonal scalar. The outer threshold
is the spatial pivot; the inner threshold is the explicit diagonal modulus.
The individual row reindexings may depend arbitrarily on their row. -/
theorem rowLimits_converge :
    ConvergesTo (rowLimit C jointModulus hjoint)
      (diagonalLimit C rho A M jointModulus hrho0 hrho1 hA hspatial hjoint) := by
  intro epsilon he
  refine ⟨pivot rho A M epsilon, fun r hr =>
    ⟨diagonalModulus rho A M jointModulus epsilon, fun i hi => ?_⟩⟩
  let c := rowCauchy C jointModulus hjoint r
  let a := QMhat _ c i
  have hai : i ≤ a := self_le_QMhat _ c i
  have harow : jointModulus (pivot rho A M epsilon) (quarter epsilon) ≤ a :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hi) hai
  exact diagonal_approx C rho A M jointModulus hrho0 hrho1 hA hspatial hjoint
    epsilon he r a a i hr harow harow hi

#print axioms quarter
#print axioms quarter_pos
#print axioms pivot
#print axioms diagonalModulus
#print axioms pivot_tail
#print axioms rectangle
#print axioms rowCauchy
#print axioms diagonalCauchy
#print axioms rowLimit
#print axioms diagonalLimit
#print axioms diagonal_converges
#print axioms diagonal_approx
#print axioms rowLimits_converge

end YMGap.Continuum.SpatialPivotCauchy
