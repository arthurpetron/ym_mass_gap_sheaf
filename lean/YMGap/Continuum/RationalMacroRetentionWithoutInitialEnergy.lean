/-
# Macroscopic retention need not have a small initial energy

The two literal positive contraction modes have equal weights, slow rate
q_n=1-1/(2(n+1)) and fast rate half. Their response has C0=1 and
C(2s)>=oneEighth*C(s) at s=n+1, while 1-C1>=quarter. Thus for s>=5 no
coefficient covering the initial loss can also obey s*c<=1.

This separates two sufficient analytic routes: a small initial loss is
strictly stronger than macroscopic retention on these explicit scalar
moment data. It is NOT an original BF4 state/action or a physical,
continuum or Yang--Mills counterexample. No spectral theorem is used.
-/

import YMGap.Continuum.RationalTwoModeSurvivalObstruction

namespace YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RationalTwoModeSurvivalObstruction
  (horizon slowRate slowRate_bounds horizon_rate_loss)

local infix:50 " ≈ " => Q'.eqv

def response (n j : Nat) : Q' := half*((slowRate n)^j+half^j)
def macroRetention : Q' := Q'.mkPos 1 8 (by decide)
def initialLossFloor : Q' := Q'.mkPos 1 4 (by decide)

private theorem power_le_one (q : Q') (hq : (0 : Q') ≤ q) (hq1 : q ≤ 1) :
    ∀ j : Nat, q^j ≤ 1
  | 0 => Q'.le_refl' _
  | j+1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ q (power_le_one q hq hq1 j) hq)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv q)) hq1)

private theorem power_positive (q : Q') (hq : (0 : Q') < q) :
    ∀ j : Nat, (0 : Q') < q^j
  | 0 => by change (0 : Q') < (1 : Q'); decide
  | j+1 => Q'.mul_pos hq (power_positive q hq j)

private theorem pow_add (q : Q') (a : Nat) : ∀ b : Nat,
    q^(a+b) ≈ q^a*q^b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv _)
  | b+1 => by
      rw [show a+(b+1)=a+b+1 by omega, Q'.pow_succ, Q'.pow_succ]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ (pow_add q a b))
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => q | 1 => q^a | _ => q^b))

private theorem bernoulli (q : Q') (hq : (0 : Q') ≤ q) (j : Nat) :
    1-Q'.ofNat j*(1-q) ≤ q^j := by
  induction j with
  | zero =>
      exact Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.const 1) (.neg (.mul (.const 0) (.add (.const 1) (.neg (.var 0))))))
        (.const 1) (by decide) (fun _ => q))
  | succ j ih =>
      let m := Q'.ofNat j
      let e := 1-q
      have hm : (0 : Q') ≤ m := Q'.ofNat_nonneg j
      have hdebt : (0 : Q') ≤ m*(e*e) :=
        Q'.mul_nonneg _ _ hm (SumOfSquares.q_mul_self_nonneg e)
      have he : q*(1-m*e) ≈ (1-(m+1)*e)+m*(e*e) :=
        poly_identity_of_normal_eq
          (.mul (.var 0) (.add (.const 1)
            (.neg (.mul (.var 1) (.add (.const 1) (.neg (.var 0)))))))
          (.add (.add (.const 1) (.neg (.mul (.add (.var 1) (.const 1))
            (.add (.const 1) (.neg (.var 0))))))
            (.mul (.var 1) (.mul (.add (.const 1) (.neg (.var 0)))
              (.add (.const 1) (.neg (.var 0))))))
          (by decide) (fun | 0 => q | _ => m)
      have hnat : Q'.ofNat (j+1) ≈ m+1 := Q'.ofNat_add_eqv j 1
      have hleft : 1-Q'.ofNat (j+1)*e ≈ 1-(m+1)*e :=
        Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_right _ _ e hnat))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hdebt)
          (Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
            (Q'.mul_le_mul_of_nonneg_left _ _ q ih hq)))

/-- Unit normalization is exact, with both positive weights equal to half. -/
theorem response_zero (n : Nat) : response n 0 ≈ 1 := by
  change half*(1+1) ≈ (1 : Q')
  decide

theorem response_positive (n j : Nat) : (0 : Q') < response n j := by
  have hslow := power_positive (slowRate n)
    (Q'.pos_of_lt_of_le (by decide : (0 : Q') < half) (slowRate_bounds n).1) j
  exact Q'.mul_pos (by decide : (0 : Q') < half)
    (Q'.pos_of_lt_of_le hslow (Q'.add_le_self_of_nonneg _ _
      (Q'.pow_nonneg half half_nonneg j)))

theorem response_le_one (n j : Nat) : response n j ≤ 1 :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ half
      (Q'.add_le_add
        (power_le_one (slowRate n) (Q'.le_trans' _ _ _ half_nonneg (slowRate_bounds n).1)
          (slowRate_bounds n).2 j)
        (power_le_one half half_nonneg (by decide) j)) half_nonneg)
    (Q'.le_of_eqv (by decide : half*(1+1) ≈ (1 : Q')))

/-- The actual slow rate survives its full growing horizon. -/
theorem slow_horizon_floor (n : Nat) : half ≤ (slowRate n)^(horizon n) := by
  have he : 1-Q'.ofNat (horizon n)*(1-slowRate n) ≈ half :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ _
      (Q'.neg_eqv_congr _ _ (horizon_rate_loss n)))
      (by decide : (1 : Q')-half ≈ half)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (bernoulli (slowRate n) (Q'.le_trans' _ _ _ half_nonneg (slowRate_bounds n).1) _)

/-- Uniform macro retention is constructed, not supplied as an input. -/
theorem response_macro_retention (n : Nat) :
    macroRetention*response n (horizon n) ≤ response n (2*horizon n) := by
  let q := slowRate n
  let s := horizon n
  have hq0 := Q'.le_trans' _ _ _ half_nonneg (slowRate_bounds n).1
  have hs := slow_horizon_floor n
  have hsq : initialLossFloor ≤ q^s*q^s := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide : initialLossFloor ≈ half*half))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ half hs half_nonneg)
      (Q'.mul_le_mul_of_nonneg_left _ _ (q^s) hs (Q'.pow_nonneg q hq0 s)))
  have hpow : q^(2*s) ≈ q^s*q^s := by
    rw [show 2*s=s+s by omega]
    exact pow_add q s s
  have hdouble := Q'.le_trans' _ _ _ hsq (Q'.ge_of_eqv hpow)
  have hfloor : macroRetention ≤ response n (2*s) := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide : macroRetention ≈ half*initialLossFloor))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ half hdouble half_nonneg)
      (Q'.mul_le_mul_of_nonneg_left _ _ half
        (Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg half half_nonneg (2*s))) half_nonneg))
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ macroRetention
      (response_le_one n s) (by decide)) (Q'.le_of_eqv (Q'.mul_one_eqv _))) hfloor

/-- The fast half-weight mode keeps a nonvanishing initial loss. -/
theorem initial_loss_lower (n : Nat) : initialLossFloor ≤ 1-response n 1 := by
  have he : response n 1 ≈ half*(slowRate n+half) :=
    Q'.mul_eqv_congr_left half _ _
      (Q'.add_eqv_congr' (Q'.mul_one_eqv (slowRate n)) (Q'.mul_one_eqv half))
  have hu : response n 1 ≤ Q'.mkPos 3 4 (by decide) := Q'.le_trans' _ _ _
    (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ half
      (Q'.add_le_add_right _ _ half (slowRate_bounds n).2) half_nonneg)
      (Q'.le_of_eqv (by decide : half*(1+half) ≈ Q'.mkPos 3 4 (by decide))))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide : initialLossFloor ≈ (1 : Q')-Q'.mkPos 3 4 (by decide)))
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hu))

/-- Macro retention holds above, but the initial-loss sufficient route
cannot meet its unit horizon budget for any horizon at least five. -/
theorem initial_budget_incompatible (n : Nat) (hn : 5 ≤ horizon n)
    (c : Q') (hc : 1-response n 1 ≤ c*response n 0) :
    ¬ Q'.ofNat (horizon n)*c ≤ 1 := by
  have hcz : c*response n 0 ≈ c := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _ (response_zero n)) (Q'.mul_one_eqv c)
  have hl : initialLossFloor ≤ c := Q'.le_trans' _ _ _ (initial_loss_lower n)
    (Q'.le_trans' _ _ _ hc (Q'.le_of_eqv hcz))
  have hfive : Q'.ofNat 5 ≤ Q'.ofNat (horizon n) := by
    change (5 : Int)*1 ≤ (horizon n : Int)*1
    simpa only [Int.mul_one] using (Int.ofNat_le.mpr hn)
  have hs0 : (0 : Q') ≤ Q'.ofNat (horizon n) := Q'.ofNat_nonneg _
  have hchain : Q'.ofNat 5*initialLossFloor ≤ Q'.ofNat (horizon n)*c :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ initialLossFloor hfive (by decide))
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (horizon n)) hl hs0)
  intro hbudget
  exact (Int.not_lt.mpr (Q'.le_trans' _ _ _ hchain hbudget))
    (by decide : (1 : Q') < Q'.ofNat 5*initialLossFloor)

end YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy

#print axioms YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy.response
#print axioms YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy.macroRetention
#print axioms YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy.initialLossFloor
#print axioms YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy.response_zero
#print axioms YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy.response_positive
#print axioms YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy.response_le_one
#print axioms YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy.slow_horizon_floor
#print axioms YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy.response_macro_retention
#print axioms YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy.initial_loss_lower
#print axioms YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy.initial_budget_incompatible
