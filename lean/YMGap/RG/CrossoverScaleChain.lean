/-
# `scaleChain_crossover_floor`: r49 with an explicit crossover budget (NEW statement next to r49)

**Label: PROVED reduction from explicit OPEN inputs. NOT gap evidence. r49 itself is untouched.**
Non-abelian content sits in `hcross_OPEN` beyond w ≈ 1/8 (the crossover; per the YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved,
the 4D U(1) transition lies between w = 1/8 and w = 1/2, inside the crossover)
and in `hafδ_OPEN`/`hupper_OPEN`/`hschur_OPEN` in the AF regime.

Steps `n < k` obey `δ_n ≤ η_n` (`hcross_OPEN`); steps `n ≥ k` obey the old AF budget
`δ_n ≤ C·afGap(j0+n)²` (`hafδ_OPEN`). The loss the ACTUAL recursion gives is read off the existing
`relativeRate_side_floor` (from `relativeRate_margin_lower`): it is ADDITIVE in the prefix sums, not a
product. With `∑_{n<k} η_n ≤ E` (`hE`) and `afQuadratic_prefix_budget` for the tail,
`finSum δ n ≤ E + C·afA²/(j0+3)` for every `n`, and the floor is
`(1 - s)(s - (E + C·afA²·inv(j0+2))) ≤ 2^n (1 - r_n)`, positive when `E + C·afA²·inv(j0+2) < s < 1`.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).
Convention: repo nome `w` matches the Numerics `t = -4 ln w`; U(1) is confined only for
w ≤ 1/8 and already Coulomb (massless) at w = 1/2 and 0.5145 (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).
-/

import YMGap.RG.SmoothSeededAfNomeSchedule

namespace YMGap.RG.CrossoverScaleChain

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (latticeMarginOf)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afGap_pos afA)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.RelativeDissipationScaleChain
  (SchurDecomposition inv inv_nonneg scaleChain_contraction relativeRate_side_floor
   afQuadratic_prefix_budget)

/-- Crossover part of the defect bound: `η_m` for `m < k`, else `0`. -/
def crossPart (k : Nat) (eta : Nat → Q') (m : Nat) : Q' := if m < k then eta m else 0

/-- AF part of the defect bound: `0` for `m < k`, else `C·afGap(j0+m)²`. -/
def afPart (C : Q') (j0 k : Nat) (m : Nat) : Q' :=
  if m < k then 0 else C * (afGap (j0+m) * afGap (j0+m))

private theorem finSum_le_add {d e a : Nat → Q'} (h : ∀ m, d m ≤ e m + a m) :
    ∀ n, finSum d n ≤ finSum e n + finSum a n
  | 0 => by show (0 : Q') ≤ 0 + 0; decide
  | n+1 => Q'.le_trans' _ _ _ (Q'.add_le_add (finSum_le_add h n) (h n))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
        (fun | 0 => finSum e n | 1 => finSum a n | 2 => e n | _ => a n)))

private theorem afGap_sq_nonneg (C : Q') (hC : (0 : Q') ≤ C) (j : Nat) :
    (0 : Q') ≤ C * (afGap j * afGap j) :=
  Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ (Q'.le_of_lt (afGap_pos j)) (Q'.le_of_lt (afGap_pos j)))

private theorem afPart_le (C : Q') (hC : (0 : Q') ≤ C) (j0 k m : Nat) :
    afPart C j0 k m ≤ C * (afGap (j0+m) * afGap (j0+m)) := by
  unfold afPart
  by_cases h : m < k
  · rw [if_pos h]; exact afGap_sq_nonneg C hC _
  · rw [if_neg h]; exact Q'.le_refl' _

private theorem split_le (C : Q') (j0 k : Nat) (delta eta : Nat → Q')
    (hcross : ∀ n, n < k → delta n ≤ eta n)
    (hafδ : ∀ n, k ≤ n → delta n ≤ C * (afGap (j0+n) * afGap (j0+n))) (m : Nat) :
    delta m ≤ crossPart k eta m + afPart C j0 k m := by
  unfold crossPart afPart
  by_cases h : m < k
  · rw [if_pos h, if_pos h]
    exact Q'.le_trans' _ _ _ (hcross m h) (Q'.ge_of_eqv (QPoly.q_add_zero_eqv _))
  · rw [if_neg h, if_neg h]
    exact Q'.le_trans' _ _ _ (hafδ m (Nat.not_lt.mp h))
      (Q'.ge_of_eqv (poly_identity_of_normal_eq (.add (.const 0) (.var 0)) (.var 0) (by decide)
        (fun _ => C * (afGap (j0+m) * afGap (j0+m)))))

/-- **Prefix budget with a crossover (PROVED):** `finSum δ n ≤ E + C·afA²·inv(j0+2)`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem crossover_prefix_budget (C E : Q') (hC : (0 : Q') ≤ C) (j0 k : Nat) (delta eta : Nat → Q')
    (hcross_OPEN : ∀ n, n < k → delta n ≤ eta n)
    (hafδ_OPEN : ∀ n, k ≤ n → delta n ≤ C * (afGap (j0+n) * afGap (j0+n)))
    (hE : ∀ n, finSum (crossPart k eta) n ≤ E) (n : Nat) :
    finSum delta n ≤ E + C * (afA * afA) * inv (j0+2) :=
  Q'.le_trans' _ _ _ (finSum_le_add (split_le C j0 k delta eta hcross_OPEN hafδ_OPEN) n)
    (Q'.add_le_add (hE n)
      (afQuadratic_prefix_budget C hC j0 (afPart C j0 k) (afPart_le C hC j0 k) n))

/-- **Positivity condition (PROVED, sufficient):** `E + B < s < 1` gives floor `> 0`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem crossover_floor_pos (s Dq : Q') (hs1 : s < (1 : Q')) (hD : Dq < s) :
    (0 : Q') < ((1 : Q') - s) * (s - Dq) :=
  Q'.mul_pos (YMGap.Continuum.HKPos.one_sub_pos hs1)
    (YMGap.Continuum.DefectRecursionPrimary.sub_pos_of_lt hD)

/-- **`scaleChain_crossover_floor` (PROVED from explicit OPEN inputs).** Contraction at every scale
and the floor `(1-s)(s - (E + C·afA²·inv(j0+2))) ≤ 2^n (1 - r_n)`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem scaleChain_crossover_floor (ns : NomeSchedule) (width : Nat → Nat) (j0 k : Nat)
    (seed C E : Q') (delta eta : Nat → Q') (hs0 : (0 : Q') ≤ seed) (hs1 : seed < (1 : Q'))
    (hC : (0 : Q') ≤ C) (hE0 : (0 : Q') ≤ E)
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (hcross_OPEN : ∀ n, n < k → delta n ≤ eta n)
    (hafδ_OPEN : ∀ n, k ≤ n → delta n ≤ C * (afGap (j0+n) * afGap (j0+n)))
    (hE : ∀ n, finSum (crossPart k eta) n ≤ E)
    (hbudget : E + C * (afA * afA) * inv (j0+2) < seed)
    (Phi : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
        (width := width (j0+n+1)) →
      VacuumComplement (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width := width (j0+n)))
    (D : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
        (width := width (j0+n+1)) → RC)
    (hupper_OPEN : ∀ n y, RCle
      (completedInner (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (Phi n y).val (Phi n y).val)
      (completedInner (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) y.val y.val))
    (hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
      (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n+1)) (width (j0+n))
      (delta n) (Phi n) (D n))
    (hseed : WilsonVacuumSqContraction (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0) seed)
    (n : Nat) :
    WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
        (relativeRate seed delta n) ∧
      ((1 : Q') - seed) * (seed - (E + C * (afA * afA) * inv (j0+2))) ≤
        Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate seed delta) n := by
  have hB : (0 : Q') ≤ C * (afA * afA) * inv (j0+2) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ (by decide) (by decide)))
      (inv_nonneg _)
  exact ⟨scaleChain_contraction ns width j0 seed delta hs0 (Q'.le_of_lt hs1) hd0 hd1 Phi D
      hupper_OPEN hschur_OPEN hseed n,
    relativeRate_side_floor seed _ delta hs0 hs1 (Q'.le_trans' _ _ _ hE0
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv E)) (Q'.add_le_add_left E _ _ hB)))
      hbudget hd0 hd1
      (crossover_prefix_budget C E hC j0 k delta eta hcross_OPEN hafδ_OPEN hE) n⟩

end YMGap.RG.CrossoverScaleChain
