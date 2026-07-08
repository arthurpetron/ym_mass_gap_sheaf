/-
Closing the two analytic monotonicity residuals of the finite-volume bounded
Hamiltonian mass gap — the `noSpectrumIn` FLOOR of `FiniteVolumeBoundedH`.

# What this module proves (reconstruction-side D-move)

`BoundedHamiltonianFiniteVol.mkFiniteVolumeBoundedH` reduced the milestone-(a)
bounded-Hamiltonian mass gap to five closed field-groups + ONE reduction: the
`noSpectrumIn` floor `Δ = −log sep ≤ E_i = −log λ_i`, assembled (in
`HamiltonianSpectrumInf`) from TWO named `Type`-level analytic residuals

  * `YOfMonotone`          — the artanh argument `yOf m = (m−1)/(m+1)` is monotone;
  * `ArtanhMonotoneWindow` — the artanh series `Σ y^{2k+1}/(2k+1)` is monotone on
    the window `|y| ≤ 1/3`.

Both are the FINITE, SCALAR, CONSTRUCTIVE operator-theory content the reconstruction
side needs, and both close with tools already on the shelf (`Q'.recipPos`
antitonicity + `CRealLog` odd-power monotonicity).  This module PROVES them:

  * `yOfMonotone_proof : YOfMonotone`
      via `yOf m ≃ 1 − 2·(1/(m+1))` (`yOf_eqv_form`) + `recipPos_antitone`;
  * `artanhMonotoneWindow_proof : ArtanhMonotoneWindow`
      via termwise `y^{2k+1} ≤ y'^{2k+1}` (`odd_pow_mono`, all-sign) ⟹ pointwise
      `partialSum y n ≤ partialSum y' n` ⟹ `leEv`.

`odd_pow_mono` is the genuine new piece: `a ≤ b ⟹ a^{2k+1} ≤ b^{2k+1}` for
ARBITRARY rationals (no sign hypothesis), by a three-way sign split off the two
existing one-sided facts `pow_le_pow_base` (nonneg) and `odd_pow_nonpos`, together
with the odd/even power-of-negation identities proved here.

# The payoff

  * `mkFiniteVolumeBoundedH_uncond` — `mkFiniteVolumeBoundedH` with the `Y` / `A`
    hypotheses ELIMINATED (installed from the proofs above).  The two analytic
    monotonicity residuals no longer gate the floor.
  * `concreteBoundedH` — a NON-VACUOUS inhabitant of `FiniteVolumeBoundedH` over a
    real finite `SpectralModel` (the excited character tower at `w = 9/10`,
    `N = 1`) with a GENUINE located gap `Δ = −log(729/1000) > 0`; the in-window
    certificates hold by decision (`sep = 729/1000 ∈ [2/3,1)`).  Energies are the
    real `−log λ`, not shape/zero witnesses.

# Honest scope (unchanged by this module)

The `noSpectrumIn` floor still carries the per-mode artanh-WINDOW certificates
`hwin` / `win` (`|yOf λ_i| ≤ 1/3`, i.e. `λ_i ≥ 1/2`) as hypotheses — the honest
in-window energy-image scope that the direct artanh construction always had.  What
is closed here is the ANALYTIC monotonicity content (the two residuals), not that
window scope.  The literal bounded operator `H = −log T` remains UNSATISFIABLE over
the spin tower and is NOT forced — the standard mass gap uses the bounded carrier
`T` + located `−log` energies, exactly `FiniteVolumeBoundedH`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`, no
`native_decide`, no custom `axiom`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BoundedHamiltonianFiniteVol

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.WilsonSpectralBridge
open YMGap.Continuum.HamiltonianSpectrumInf
open YMGap.Continuum.BoundedHamiltonianFiniteVol

namespace YMGap.Continuum.BoundedHFiniteVolClosed

/-- `¬ (p ≤ q) ⟹ q ≤ p` (total order of `Q'`; local copy). -/
theorem q_le_of_not_le {p q : Q'} (h : ¬ (p ≤ q)) : q ≤ p := by
  show q.num * (p.den : Int) ≤ p.num * (q.den : Int)
  have h' : ¬ (p.num * (q.den : Int) ≤ q.num * (p.den : Int)) := h
  exact Int.le_of_lt (Int.not_le.mp h')

/-! ## 1. `recipPos` is antitone -/

/-- **`recipPos` antitone.**  `0 < x ≤ y ⟹ recipPos y ≤ recipPos x`.  Directly
from `x ≤ y` (`x.num·y.den ≤ y.num·x.den`) after `recipPos_num`/`recipPos_den`. -/
theorem recipPos_antitone {x y : Q'} (hx : (0 : Q') < x) (hy : (0 : Q') < y)
    (hxy : x ≤ y) : Q'.recipPos y hy ≤ Q'.recipPos x hx := by
  show (Q'.recipPos y hy).num * ((Q'.recipPos x hx).den : Int)
      ≤ (Q'.recipPos x hx).num * ((Q'.recipPos y hy).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_num, Q'.recipPos_den x hx, Q'.recipPos_den y hy]
  have h : x.num * (y.den : Int) ≤ y.num * (x.den : Int) := hxy
  rw [Int.mul_comm (y.den : Int) x.num, Int.mul_comm (x.den : Int) y.num]
  exact h

/-! ## 2. The `yOf` identity `yOf m ≃ 1 − 2·(1/(m+1))` and monotonicity -/

/-- **`yOf m ≃ 1 + −(r + r)`** with `r = 1/(m+1)`.  Since `m − 1 = (m+1) − 2`,
`yOf m = (m−1)·r = (m+1)·r − 2·r ≃ 1 − 2r`. -/
theorem yOf_eqv_form (m : Q') (hm1 : (0 : Q') < m + 1) :
    (yOf m hm1).eqv
      (1 + -(Q'.recipPos (m + 1) hm1 + Q'.recipPos (m + 1) hm1)) := by
  -- Step A: (m + -1) ≃ (m+1) + (-1 + -1)
  have e2 : (1 + (-1 + -1) : Q').eqv (-1 : Q') := by
    have a1 : (1 + (-1 + -1) : Q').eqv ((1 + -1) + -1) :=
      Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) (-1))
    have a2 : (((1 : Q') + -1) + -1).eqv ((0 : Q') + -1) :=
      Q'.add_eqv_congr_right (1 + -1) 0 (-1) (Q'.add_neg_self_eqv 1)
    have a3 : ((0 : Q') + -1) = (-1 : Q') := Q'.zero_add' (-1)
    exact Q'.eqv_trans _ _ _ a1 (a3 ▸ a2)
  have hA : ((m + 1) + (-1 + -1) : Q').eqv (m + -1) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv m 1 (-1 + -1)) ?_
    exact Q'.add_eqv_congr_left m (1 + (-1 + -1)) (-1) e2
  -- Step B: multiply by r
  have hB : ((m + -1) * Q'.recipPos (m + 1) hm1).eqv
      (((m + 1) + (-1 + -1)) * Q'.recipPos (m + 1) hm1) :=
    Q'.mul_eqv_congr_right (m + -1) ((m + 1) + (-1 + -1))
      (Q'.recipPos (m + 1) hm1) (Q'.eqv_symm hA)
  -- Step C: distribute
  have hC : (((m + 1) + (-1 + -1)) * Q'.recipPos (m + 1) hm1).eqv
      ((m + 1) * Q'.recipPos (m + 1) hm1
        + (-1 + -1) * Q'.recipPos (m + 1) hm1) :=
    Q'.add_mul_eqv (m + 1) (-1 + -1) (Q'.recipPos (m + 1) hm1)
  -- Step D: simplify each summand
  have hLeft : ((m + 1) * Q'.recipPos (m + 1) hm1).eqv 1 :=
    Q'.mul_recipPos_eqv (m + 1) hm1
  have hNeg1 : ((-1 : Q') * Q'.recipPos (m + 1) hm1).eqv
      (-(Q'.recipPos (m + 1) hm1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (Q'.recipPos (m + 1) hm1)) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (Q'.recipPos (m + 1) hm1))
  have hRight : ((-1 + -1) * Q'.recipPos (m + 1) hm1).eqv
      (-(Q'.recipPos (m + 1) hm1 + Q'.recipPos (m + 1) hm1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (-1) (-1) (Q'.recipPos (m + 1) hm1)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hNeg1 hNeg1) ?_
    exact Q'.eqv_symm (Q'.neg_add_eqv (Q'.recipPos (m + 1) hm1)
      (Q'.recipPos (m + 1) hm1))
  have hD : ((m + 1) * Q'.recipPos (m + 1) hm1
        + (-1 + -1) * Q'.recipPos (m + 1) hm1).eqv
      (1 + -(Q'.recipPos (m + 1) hm1 + Q'.recipPos (m + 1) hm1)) :=
    Q'.add_eqv_congr' hLeft hRight
  show ((m + -1) * Q'.recipPos (m + 1) hm1).eqv _
  exact Q'.eqv_trans _ _ _ hB (Q'.eqv_trans _ _ _ hC hD)

/-- **`YOfMonotone` — PROVED.**  `a ≤ b ⟹ yOf a ≤ yOf b`, via the identity form and
`recipPos_antitone` on `a+1 ≤ b+1`. -/
def yOfMonotone_proof : YOfMonotone where
  mono := fun a b ha hb hab => by
    have ida := yOf_eqv_form a ha
    have idb := yOf_eqv_form b hb
    have hab1 : a + 1 ≤ b + 1 := Q'.add_le_add_right a b 1 hab
    have hr : Q'.recipPos (b + 1) hb ≤ Q'.recipPos (a + 1) ha :=
      recipPos_antitone ha hb hab1
    have hrr : Q'.recipPos (b + 1) hb + Q'.recipPos (b + 1) hb
             ≤ Q'.recipPos (a + 1) ha + Q'.recipPos (a + 1) ha := Q'.add_le_add hr hr
    have hneg : -(Q'.recipPos (a + 1) ha + Q'.recipPos (a + 1) ha)
              ≤ -(Q'.recipPos (b + 1) hb + Q'.recipPos (b + 1) hb) := Q'.neg_le_neg hrr
    have hmid : (1 : Q') + -(Q'.recipPos (a + 1) ha + Q'.recipPos (a + 1) ha)
              ≤ (1 : Q') + -(Q'.recipPos (b + 1) hb + Q'.recipPos (b + 1) hb) :=
      Q'.add_le_add_left 1 _ _ hneg
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv ida)
      (Q'.le_trans' _ _ _ hmid (Q'.ge_of_eqv idb))

/-! ## 3. Odd-power monotonicity (all signs) -/

/-- `(−a)·(−a) ≃ a·a`. -/
theorem neg_mul_neg_eqv (a : Q') : ((-a) * (-a)).eqv (a * a) := by
  have h1 : ((-a) * (-a)).eqv (-(a * (-a))) := Q'.neg_mul_eqv a (-a)
  have h2 : (a * (-a)).eqv (-(a * a)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv a (-a)) (Q'.neg_mul_eqv a a)
  have h3 : (-(a * (-a))).eqv (-(-(a * a))) := Q'.neg_eqv_congr _ _ h2
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h3 (Q'.neg_neg_eqv (a * a)))

/-- Even power of a negation: `(−a)^{2k} ≃ a^{2k}`. -/
theorem neg_even_pow_eqv (a : Q') : ∀ k, ((-a) ^ (2 * k)).eqv (a ^ (2 * k))
  | 0 => Q'.eqv_refl _
  | k + 1 => by
    have he : 2 * (k + 1) = (2 * k) + 2 := by omega
    rw [he, pow_add_two (-a) (2 * k), pow_add_two a (2 * k)]
    have ih := neg_even_pow_eqv a k
    have s1 : ((-a) * ((-a) * (-a) ^ (2 * k))).eqv (((-a) * (-a)) * (-a) ^ (2 * k)) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv (-a) (-a) ((-a) ^ (2 * k)))
    have t1 : (((-a) * (-a)) * (-a) ^ (2 * k)).eqv (((-a) * (-a)) * a ^ (2 * k)) :=
      Q'.mul_eqv_congr_left ((-a) * (-a)) ((-a) ^ (2 * k)) (a ^ (2 * k)) ih
    have t2 : (((-a) * (-a)) * a ^ (2 * k)).eqv ((a * a) * a ^ (2 * k)) :=
      Q'.mul_eqv_congr_right ((-a) * (-a)) (a * a) (a ^ (2 * k)) (neg_mul_neg_eqv a)
    have s3 : ((a * a) * a ^ (2 * k)).eqv (a * (a * a ^ (2 * k))) :=
      Q'.mul_assoc_eqv a a (a ^ (2 * k))
    exact Q'.eqv_trans _ _ _ s1 (Q'.eqv_trans _ _ _ t1 (Q'.eqv_trans _ _ _ t2 s3))

/-- Odd power of a negation: `(−a)^{2k+1} ≃ −(a^{2k+1})`. -/
theorem neg_odd_pow_eqv (a : Q') (k : Nat) :
    ((-a) ^ (2 * k + 1)).eqv (-(a ^ (2 * k + 1))) := by
  rw [Q'.pow_succ, Q'.pow_succ]
  have c1 : ((-a) * (-a) ^ (2 * k)).eqv ((-a) * a ^ (2 * k)) :=
    Q'.mul_eqv_congr_left (-a) ((-a) ^ (2 * k)) (a ^ (2 * k)) (neg_even_pow_eqv a k)
  exact Q'.eqv_trans _ _ _ c1 (Q'.neg_mul_eqv a (a ^ (2 * k)))

/-- **Odd-power monotonicity (all signs).**  `a ≤ b ⟹ a^{2k+1} ≤ b^{2k+1}` for
ARBITRARY rationals, by a three-way sign split. -/
theorem odd_pow_mono {a b : Q'} (hab : a ≤ b) (k : Nat) :
    a ^ (2 * k + 1) ≤ b ^ (2 * k + 1) := by
  by_cases ha : (0 : Q') ≤ a
  · exact pow_le_pow_base a b ha hab (2 * k + 1)
  · have ha' : a ≤ 0 := q_le_of_not_le ha
    by_cases hb : (0 : Q') ≤ b
    · exact Q'.le_trans' _ _ _ (odd_pow_nonpos a ha' k) (pow_nonneg b hb (2 * k + 1))
    · have hb' : b ≤ 0 := q_le_of_not_le hb
      have h0 : (0 : Q') ≤ -b :=
        Q'.le_trans' _ _ _ (Q'.ge_of_eqv (show ((-(0 : Q')).eqv 0) by decide))
          (Q'.neg_le_neg hb')
      have hnba : -b ≤ -a := Q'.neg_le_neg hab
      have hpow : (-b) ^ (2 * k + 1) ≤ (-a) ^ (2 * k + 1) :=
        pow_le_pow_base (-b) (-a) h0 hnba (2 * k + 1)
      have h' : -(b ^ (2 * k + 1)) ≤ -(a ^ (2 * k + 1)) :=
        Q'.le_trans' _ _ _ (Q'.ge_of_eqv (neg_odd_pow_eqv b k))
          (Q'.le_trans' _ _ _ hpow (Q'.le_of_eqv (neg_odd_pow_eqv a k)))
      have hn := Q'.neg_le_neg h'
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.neg_neg_eqv (a ^ (2 * k + 1))))
        (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.neg_neg_eqv (b ^ (2 * k + 1)))))

/-! ## 4. `ArtanhMonotoneWindow` from termwise / pointwise monotonicity -/

/-- Termwise: `y ≤ y' ⟹ term y k ≤ term y' k`. -/
theorem term_mono {y y' : Q'} (h : y ≤ y') (k : Nat) : term y k ≤ term y' k :=
  Q'.mul_le_mul_of_nonneg_right (y ^ (2 * k + 1)) (y' ^ (2 * k + 1)) (recipOdd k)
    (odd_pow_mono h k) (recipOdd_nonneg k)

/-- Pointwise: `y ≤ y' ⟹ partialSum y n ≤ partialSum y' n`. -/
theorem partialSum_mono {y y' : Q'} (h : y ≤ y') :
    ∀ n, partialSum y n ≤ partialSum y' n
  | 0 => by rw [partialSum_zero, partialSum_zero]; exact Q'.le_refl' 0
  | n + 1 => by
    show partialSum y n + term y n ≤ partialSum y' n + term y' n
    exact Q'.add_le_add (partialSum_mono h n) (term_mono h n)

/-- **`ArtanhMonotoneWindow` — PROVED.**  `y ≤ y' ⟹ leEv (artanh y) (artanh y')`,
directly from pointwise `partialSum` monotonicity (`N = 0`, any `ε > 0`). -/
def artanhMonotoneWindow_proof : ArtanhMonotoneWindow where
  mono := fun y y' _hy _hy' hle => by
    intro ε hε
    refine ⟨0, fun n _ => ?_⟩
    show partialSum y n ≤ partialSum y' n + ε
    exact Q'.le_trans' _ _ _ (partialSum_mono hle n)
      (Q'.add_le_self_of_nonneg (partialSum y' n) ε (Q'.le_of_lt hε))

/-! ## 5. The unconditional finite-volume bounded-H constructor -/

/-- **`mkFiniteVolumeBoundedH_uncond`.**  `mkFiniteVolumeBoundedH` with the two
analytic monotonicity residuals `YOfMonotone` / `ArtanhMonotoneWindow` ELIMINATED
(installed from `yOfMonotone_proof` / `artanhMonotoneWindow_proof`).  The
`noSpectrumIn` floor `Δ ≤ E_i` no longer depends on any unproved monotonicity
input; it is now a theorem of the shelf.  The only remaining hypotheses are the
honest in-window certificates `hwin` / `win` (the energy-image scope). -/
def mkFiniteVolumeBoundedH_uncond {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat)
    (hwin : Q'.abs (yOf (excG op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG op w hw0 hw1 N).gap)) ≤ recipOdd 1)
    (win : ∀ i (hi : i < (excG op w hw0 hw1 N).model.k),
      Q'.abs (yOf ((excG op w hw0 hw1 N).model.lam i)
        (plusOne_pos_of_nonneg ((excG op w hw0 hw1 N).model.lam_nonneg i)))
        ≤ recipOdd 1) :
    FiniteVolumeBoundedH (excG op w hw0 hw1 N) hwin :=
  mkFiniteVolumeBoundedH op w hw0 hw1 N yOfMonotone_proof artanhMonotoneWindow_proof
    hwin win

/-! ## 6. A concrete NON-VACUOUS inhabitant (real finite spectral model)

`w = 9/10`, `N = 1`: the single excited mode has eigenvalue
`λ₀ = qpow (9/10) (c4 1) = (9/10)³ = 729/1000 = sep`, which lies in `[2/3, 1)`, so
the artanh-window certificate `|yOf sep| ≤ 1/3` holds by decision.  The located gap
`Δ = −log(729/1000)` is a genuine positive `CReal`.  Parametric in the transfer
operator `op` (the type is inhabited for every `op`, e.g. `idTransfer`), exactly as
`mkFiniteVolumeBoundedH`'s own non-vacuity is. -/

/-- `w = 9/10`. -/
def wConc : Q' := Q'.mkPos 9 10 (by decide)

theorem wConc_nonneg : (0 : Q') ≤ wConc := by decide
theorem wConc_lt_one : wConc < (1 : Q') := by decide

/-- The concrete separator `sep = (9/10)³ = 729/1000` (closed, no free variables). -/
def sepConc : Q' := heatKernelSep wConc

theorem sepConc_plusOne_pos : (0 : Q') < sepConc + 1 := by decide

/-- The CLOSED in-window certificate for `sep = 729/1000 ∈ [2/3, 1)`.  Proved by
decision on a fully-closed term; transported to the `op`-indexed certificates below
by proof-irrelevance of the positivity argument (the artanh value is independent of
it). -/
theorem concWin_val :
    Q'.abs (yOf sepConc sepConc_plusOne_pos) ≤ recipOdd 1 := by decide

/-- The in-window certificate for the separator (defeq to `concWin_val`: the model
separator reduces to `sepConc`, and the positivity proof is proof-irrelevant). -/
theorem concHwin {D : GNSData} {H : CompleteGNSHilbert D} (op : TransferOperator H) :
    Q'.abs (yOf (excG op wConc wConc_nonneg wConc_lt_one 1).gap.sep
        (sepPlusOne_pos (excG op wConc wConc_nonneg wConc_lt_one 1).gap))
      ≤ recipOdd 1 := concWin_val

/-- The per-mode in-window certificate (only mode `i = 0`, eigenvalue `729/1000`). -/
theorem concWin {D : GNSData} {H : CompleteGNSHilbert D} (op : TransferOperator H) :
    ∀ i (hi : i < (excG op wConc wConc_nonneg wConc_lt_one 1).model.k),
      Q'.abs (yOf ((excG op wConc wConc_nonneg wConc_lt_one 1).model.lam i)
        (plusOne_pos_of_nonneg
          ((excG op wConc wConc_nonneg wConc_lt_one 1).model.lam_nonneg i)))
        ≤ recipOdd 1 := by
  intro i hi
  -- `model.k = 1`, so `i = 0`; the eigenvalue is `qpow (9/10) 3 = 729/1000 = sepConc`.
  have hi0 : i = 0 := Nat.lt_one_iff.mp hi
  subst hi0
  exact concWin_val

/-- **`concreteBoundedH` — a NON-VACUOUS `FiniteVolumeBoundedH`.**  Over the real
finite excited character model at `w = 9/10`, `N = 1`, with a genuine located gap
`Δ = −log(729/1000) > 0`.  All fields discharged (energies are real `−log λ`), no
`Y`/`A` residuals, no shape/zero witness. -/
def concreteBoundedH {D : GNSData} {H : CompleteGNSHilbert D} (op : TransferOperator H) :
    FiniteVolumeBoundedH (excG op wConc wConc_nonneg wConc_lt_one 1) (concHwin op) :=
  mkFiniteVolumeBoundedH_uncond op wConc wConc_nonneg wConc_lt_one 1
    (concHwin op) (concWin op)

/-- **The three milestone-(a) predicates hold NON-VACUOUSLY.**  `H ≥ 0`
(`spectrum_nonneg`), `H ψ_vac = 0` (`vacuum_zero`), `Δ = −log(729/1000) > 0`
(`Δ_pos`) — read straight off the concrete inhabitant. -/
theorem concreteBoundedH_mass_gap {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) :
    (∀ i hi, CReal.leEv CReal.czero ((concreteBoundedH op).energy i hi))
      ∧ CReal.Equiv
          (CReal.neg (logRat (1 : Q') (by decide) yOf_one_window)) CReal.czero
      ∧ CReal.IsPositive (concreteBoundedH op).Δ :=
  boundedH_mass_gap (excG op wConc wConc_nonneg wConc_lt_one 1) (concHwin op)
    (concreteBoundedH op)

end YMGap.Continuum.BoundedHFiniteVolClosed

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BoundedHFiniteVolClosed.recipPos_antitone
#print axioms YMGap.Continuum.BoundedHFiniteVolClosed.yOf_eqv_form
#print axioms YMGap.Continuum.BoundedHFiniteVolClosed.yOfMonotone_proof
#print axioms YMGap.Continuum.BoundedHFiniteVolClosed.odd_pow_mono
#print axioms YMGap.Continuum.BoundedHFiniteVolClosed.artanhMonotoneWindow_proof
#print axioms YMGap.Continuum.BoundedHFiniteVolClosed.mkFiniteVolumeBoundedH_uncond
#print axioms YMGap.Continuum.BoundedHFiniteVolClosed.concreteBoundedH
#print axioms YMGap.Continuum.BoundedHFiniteVolClosed.concreteBoundedH_mass_gap
