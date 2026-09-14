/-
# Exact SU(2) heat power of a finite original coefficient product

Keep every dimension factor and expose the sum of the ORIGINAL c4
exponents. Each positive spin contributes at least three. Extracting a
known exponent floor uses natural subtraction and never division by w.
These identities hold at every rational nome, including zero; they are
not uniform estimates or assertions about the sign of a Haar coefficient.
-/

import YMGap.Continuum.BondMovingStep
import YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2FiniteHeatPowerFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def casimirSum (state : Nat → Nat) : List Nat → Nat
  | [] => 0
  | id::ids => c4 (state id) + casimirSum state ids

def positiveCount (state : Nat → Nat) (ids : List Nat) : Nat :=
  (ids.filter (fun id => decide (0 < state id))).length

def dimensionProduct (state : Nat → Nat) (ids : List Nat) : Q' :=
  eliminateLinks (fun id => dimQ (state id)) ids

/-- Casimir cost beyond the minimum three per occupied face. -/
def excessSum (state : Nat → Nat) : List Nat → Nat
  | [] => 0
  | id::ids => (c4 (state id) - 3) + excessSum state ids

theorem positive_casimir {spin : Nat} (h : 0 < spin) : 3 ≤ c4 spin := by
  have hm := Nat.mul_le_mul (show 1 ≤ spin by omega) (show 3 ≤ spin+2 by omega)
  simpa only [Nat.one_mul] using hm

theorem three_count_le (state : Nat → Nat) : ∀ ids : List Nat,
    3 * positiveCount state ids ≤ casimirSum state ids
  | [] => Nat.le_refl 0
  | id::ids => by
    have ih := three_count_le state ids
    by_cases hp : 0 < state id
    · have hc := positive_casimir hp
      simp only [positiveCount, List.filter_cons, decide_eq_true hp, ↓reduceIte,
        List.length_cons, casimirSum] at ih ⊢
      omega
    · simp only [positiveCount, List.filter_cons, decide_eq_false hp, Bool.false_eq_true,
        ↓reduceIte, casimirSum] at ih ⊢
      omega

theorem casimir_decomposition (state : Nat → Nat) : ∀ ids : List Nat,
    casimirSum state ids = 3 * positiveCount state ids + excessSum state ids
  | [] => rfl
  | id::ids => by
    have ih := casimir_decomposition state ids
    by_cases hp : 0 < state id
    · have hc := positive_casimir hp
      simp only [casimirSum, positiveCount, excessSum, List.filter_cons,
        decide_eq_true hp, ↓reduceIte, List.length_cons] at ih ⊢
      omega
    · have hz : state id = 0 := by omega
      simp only [casimirSum, positiveCount, excessSum, List.filter_cons,
        hz, c4_zero, Nat.zero_sub, Nat.zero_add] at ih ⊢
      exact ih

theorem zero_excess_small (state : Nat → Nat) : ∀ ids : List Nat,
    excessSum state ids = 0 → ∀ id, id ∈ ids → state id ≤ 1
  | [], _, _, hi => False.elim (List.not_mem_nil hi)
  | head::ids, hz, id, hi => by
    have he : c4 (state head) - 3 = 0 ∧ excessSum state ids = 0 := by
      change (c4 (state head) - 3) + excessSum state ids = 0 at hz
      constructor <;> omega
    rcases List.mem_cons.mp hi with hi | hi
    · subst id
      by_cases hs : state head ≤ 1
      · exact hs
      · have hm := Nat.mul_le_mul (show 2 ≤ state head by omega) (show 4 ≤ state head+2 by omega)
        have hb : 8 ≤ c4 (state head) := hm
        omega
    · exact zero_excess_small state ids he.2 id hi

theorem mul_shuffle (a b c d : Q') : (a*b)*(c*d) ≈ (a*c)*(b*d) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
    (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d)

theorem coefficient_product (w : Q') (state : Nat → Nat) : ∀ ids : List Nat,
    eliminateLinks (fun id => coeffW w (state id)) ids ≈
      dimensionProduct state ids * qpow w (casimirSum state ids)
  | [] => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | id::ids => by
    change (dimQ (state id) * qpow w (c4 (state id))) *
      eliminateLinks (fun id => coeffW w (state id)) ids ≈
      (dimQ (state id) * dimensionProduct state ids) * qpow w (c4 (state id) + casimirSum state ids)
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (coefficient_product w state ids)) ?_
    refine Q'.eqv_trans _ _ _ (mul_shuffle _ _ _ _) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (HeatKernelRGStep.qpow_add w _ _))

/-- Constructive residual power: valid even at zero nome; no inverse is used. -/
theorem extract_floor (w coefficient : Q') (floor power : Nat) (h : floor ≤ power) :
    coefficient * qpow w power ≈ qpow w floor * (coefficient * qpow w (power-floor)) := by
  have he : power = floor + (power-floor) := by omega
  rw [he] at ⊢
  have hs : floor + (power-floor) - floor = power-floor := by omega
  rw [hs]
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (HeatKernelRGStep.qpow_add w _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.mul_assoc_eqv _ _ _

end YMGap.Continuum.SU2FiniteHeatPowerFactorization

#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.casimirSum
#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.positiveCount
#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.dimensionProduct
#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.excessSum
#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.positive_casimir
#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.three_count_le
#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.casimir_decomposition
#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.zero_excess_small
#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.mul_shuffle
#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.coefficient_product
#print axioms YMGap.Continuum.SU2FiniteHeatPowerFactorization.extract_floor
