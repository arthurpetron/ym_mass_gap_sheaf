/-
Division-free logarithm sandwich over `Q'`, rational truncated `−log` series,
physical-units gap restatement, and the `ρ(a) = 1 − a²` toy upgraded to every
sandwiched `L`.  Status: infrastructure, not gap evidence; U(1)-true.

# Contents

* `LogSandwich L` — for all `0 < ρ ≤ 1`: `1 − ρ ≤ L ρ` and `ρ·L ρ ≤ 1 − ρ`
  (the division-free form of `1 − ρ ≤ L ρ ≤ (1 − ρ)/ρ`).  The real `−log`
  satisfies this classically; NO real logarithm is defined or used here.
  Statements are pointwise in `ρ`, so no `eqv`-congruence of `L` is needed.
* `logSeries x N = Σ_{j=1}^{N} x^j / j`, with `lowerLog N ρ := S_{N+1}(1 − ρ)`
  and `upperLog N ρ := S_{N+1}(x) + x^{N+2}/((N+2)·ρ)` (`x = 1 − ρ`, `1/ρ` via
  `invPos`).  Proved: both satisfy `LogSandwich` (so the interface is inhabited
  axiom-free) and `lowerLog ≤ upperLog`.  The key invariant is
  `ρ·S_{N+1}(x) + x^{N+2}/(N+1) ≤ x` whenever `ρ + x ≃ 1`.  NOT proved (no real
  log exists here): that `lowerLog ≤ −log ρ ≤ upperLog`.  Classically this
  holds via the geometric tail bound.
* `mass_le_log` / `log_le_mass` — `m′·a ≤ 1 − ρ(a)` ⟹ `m′·a ≤ L(ρ(a))`; and
  `1 − ρ(a) ≤ M·a`, `ρ₀ ≤ ρ(a)` ⟹ `ρ₀·L(ρ(a)) ≤ M·a`.
* `rhoToy_log_le` — for every sandwiched `L`, `0 < a ≤ 1/2`, `a ≤ ε·(3/4)`:
  `L(1 − a²) ≤ ε·a`, i.e. `L(ρ(a))/a → 0` with explicit modulus
  `a₀(ε) = min(1/2, 3ε/4)`.  `rhoToy_log_ge` gives the matching `a·a ≤ L(ρ(a))`.
  This closes the `−log ρ / a → 0` caveat of `ClusteringImpliesGapPoly` for
  every `L` in the interface (the true `−log` included, classically).

Axiom gate: `propext` / `Quot.sound` only (checked out of tree).
-/

import YMGap.Continuum.ClusteringImpliesGapPoly

namespace YMGap.Continuum.LogBounds

open YMGap.Constructive
open YMGap.Continuum.ClusteringImpliesGapPoly

/-! ## `Q'` helpers -/

/-- `a ≤ b → 0 ≤ b − a`. -/
theorem sub_nonneg_of_le {a b : Q'} (h : a ≤ b) : (0 : Q') ≤ b - a :=
  (Q'.zero_le_iff_num_nonneg _).mpr (by
    show (0 : Int) ≤ b.num * (a.den : Int) + (-a.num) * (b.den : Int)
    have h' : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := h
    rw [Int.neg_mul, ← Int.sub_eq_add_neg]
    exact Int.sub_nonneg_of_le h')

/-- `(a + b) ≃ c → (c − b) ≃ a`. -/
theorem sub_eqv_of_add_eqv {a b c : Q'} (h : (a + b).eqv c) : (c - b).eqv a :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right c (a + b) (-b) (Q'.eqv_symm h))
    (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (-b))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ 0 (Q'.add_neg_self_eqv b))
        (Q'.eqv_of_eq (Q'.add_zero' a))))

/-- Additive left cancellation for `≤`. -/
theorem le_of_add_le_add_left {a b c : Q'} (h : c + a ≤ c + b) : a ≤ b := by
  have e : ∀ y : Q', ((-c) + (c + y)).eqv y := fun y =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-c) c y))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ 0 y (Q'.neg_add_self_eqv c))
        (Q'.eqv_of_eq (Q'.zero_add' y)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (e a))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left (-c) _ _ h) (Q'.le_of_eqv (e b)))

/-- Right distributivity `(a + b)·c ≃ a·c + b·c`. -/
theorem add_mul_eqv (a b c : Q') : ((a + b) * c).eqv (a * c + b * c) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (a + b) c)
    (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c a b)
      (ClusteringImpliesGap.add_eqv_both (Q'.mul_comm_eqv c a) (Q'.mul_comm_eqv c b)))

/-- `1/(N+2) ≤ 1/(N+1)`. -/
theorem invSucc_succ_le (N : Nat) : Q'.invSucc (N + 1) ≤ Q'.invSucc N := by
  show (Q'.invSucc (N + 1)).num * ((Q'.invSucc N).den : Int)
      ≤ (Q'.invSucc N).num * ((Q'.invSucc (N + 1)).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_num, Q'.invSucc_den, Q'.invSucc_den, Int.one_mul, Int.one_mul]
  exact Int.ofNat_le.mpr (Nat.le_succ _)

/-- Reciprocal of a positive rational, `n/d ↦ d/n` (by cases on the numerator;
`0` for non-positive numerators, which never occur under `0 < q`). -/
def invPos : Q' → Q'
  | ⟨Int.ofNat (k + 1), d⟩ => ⟨((d + 1 : Nat) : Int), k⟩
  | _ => 0

theorem invPos_nonneg : ∀ q : Q', (0 : Q') ≤ invPos q
  | ⟨Int.ofNat (_ + 1), d⟩ =>
      (Q'.zero_le_iff_num_nonneg _).mpr (Int.natCast_nonneg (d + 1))
  | ⟨Int.ofNat 0, _⟩ => Q'.le_refl' 0
  | ⟨Int.negSucc _, _⟩ => Q'.le_refl' 0

theorem mul_invPos : ∀ {q : Q'}, (0 : Q') < q → (q * invPos q).eqv 1
  | ⟨Int.ofNat (k + 1), d⟩, _ => by
      show (Int.ofNat (k + 1) * ((d + 1 : Nat) : Int)) * ((1 : Q').den : Int)
          = (1 : Int) * ((⟨Int.ofNat (k + 1), d⟩ * (⟨((d + 1 : Nat) : Int), k⟩ : Q')).den : Int)
      rw [Q'.mul_den_cast]
      show (Int.ofNat (k + 1) * ((d + 1 : Nat) : Int)) * (1 : Int)
          = (1 : Int) * (((d + 1 : Nat) : Int) * ((k + 1 : Nat) : Int))
      rw [Int.mul_one, Int.one_mul]
      exact Int.mul_comm _ _
  | ⟨Int.ofNat 0, _⟩, hq => absurd (Q'.num_pos_of_pos hq) (Int.lt_irrefl 0)
  | ⟨Int.negSucc m, _⟩, hq =>
      absurd (Q'.num_pos_of_pos hq) (Int.lt_asymm (Int.negSucc_lt_zero m))

/-! ## (1) The abstract sandwich interface -/

/-- `L` lies in the division-free `−log` sandwich `1 − ρ ≤ L ρ ≤ (1 − ρ)/ρ`
on `0 < ρ ≤ 1`. -/
structure LogSandwich (L : Q' → Q') : Prop where
  lower : ∀ ρ : Q', (0 : Q') < ρ → ρ ≤ 1 → 1 - ρ ≤ L ρ
  upper : ∀ ρ : Q', (0 : Q') < ρ → ρ ≤ 1 → ρ * L ρ ≤ 1 - ρ

theorem LogSandwich.nonneg {L : Q' → Q'} (hL : LogSandwich L) (ρ : Q')
    (h0 : (0 : Q') < ρ) (h1 : ρ ≤ 1) : (0 : Q') ≤ L ρ :=
  Q'.le_trans' _ _ _ (sub_nonneg_of_le h1) (hL.lower ρ h0 h1)

/-! ## (2) Rational truncated series -/

/-- `logSeries x N = Σ_{j=1}^{N} x^j / j`. -/
def logSeries (x : Q') : Nat → Q'
  | 0 => 0
  | N + 1 => logSeries x N + x ^ (N + 1) * Q'.invSucc N

theorem logSeries_one_eqv (x : Q') : (logSeries x 1).eqv x := by
  show ((0 : Q') + x ^ 1 * Q'.invSucc 0).eqv x
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (ClusteringImpliesGap.pow_one_eqv x))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ 1 (by decide)) (Q'.mul_one_eqv x)))

/-- Lower bound `x ≤ S_{N+1}(x)` for `x ≥ 0`. -/
theorem logSeries_ge (x : Q') (hx : (0 : Q') ≤ x) : ∀ N : Nat, x ≤ logSeries x (N + 1)
  | 0 => Q'.ge_of_eqv (logSeries_one_eqv x)
  | N + 1 => Q'.le_trans' _ _ _ (logSeries_ge x hx N)
      (Q'.add_le_self_of_nonneg (logSeries x (N + 1)) (x ^ (N + 2) * Q'.invSucc (N + 1))
        (Q'.mul_nonneg _ _ (Q'.pow_nonneg x hx _) (Q'.invSucc_nonneg _)))

/-- **Remainder invariant.**  If `ρ + x ≃ 1` and `x ≥ 0`:
`ρ·S_{N+1}(x) + x^{N+2}/(N+1) ≤ x`. -/
theorem logSeries_rem (ρ x : Q') (hx : (0 : Q') ≤ x) (hsum : (ρ + x).eqv 1) :
    ∀ N : Nat, ρ * logSeries x (N + 1) + x ^ (N + 2) * Q'.invSucc N ≤ x
  | 0 => by
      show ρ * logSeries x 1 + (x * x ^ 1) * Q'.invSucc 0 ≤ x
      have e2 : ((x * x ^ 1) * Q'.invSucc 0).eqv (x * x) :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ (x * x) _
            (Q'.mul_eqv_congr_left x _ x (ClusteringImpliesGap.pow_one_eqv x)))
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (x * x) _ 1 (by decide))
            (Q'.mul_one_eqv _))
      have e : (ρ * logSeries x 1 + (x * x ^ 1) * Q'.invSucc 0).eqv x :=
        Q'.eqv_trans _ _ _
          (ClusteringImpliesGap.add_eqv_both
            (Q'.mul_eqv_congr_left ρ _ _ (logSeries_one_eqv x)) e2)
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (add_mul_eqv ρ x x))
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ 1 x hsum) (Q'.one_mul_eqv x)))
      exact Q'.le_of_eqv e
  | N + 1 => by
      show ρ * (logSeries x (N + 1) + x ^ (N + 2) * Q'.invSucc (N + 1))
          + (x * x ^ (N + 2)) * Q'.invSucc (N + 1) ≤ x
      have inner : (ρ * (x ^ (N + 2) * Q'.invSucc (N + 1))
          + (x * x ^ (N + 2)) * Q'.invSucc (N + 1)).eqv
            (x ^ (N + 2) * Q'.invSucc (N + 1)) :=
        Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv x _ _))
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (add_mul_eqv ρ x _))
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ 1 _ hsum) (Q'.one_mul_eqv _)))
      have e1 := Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv ρ (logSeries x (N + 1))
          (x ^ (N + 2) * Q'.invSucc (N + 1))))
        (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
          (Q'.add_eqv_congr_left (ρ * logSeries x (N + 1)) _ _ inner))
      have s2 := Q'.add_le_add_left (ρ * logSeries x (N + 1)) _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (x ^ (N + 2)) (invSucc_succ_le N)
          (Q'.pow_nonneg x hx _))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
        (Q'.le_trans' _ _ _ s2 (logSeries_rem ρ x hx hsum N))

/-- Rational lower `−log` bound `S_{N+1}(1 − ρ)`. -/
def lowerLog (N : Nat) (ρ : Q') : Q' := logSeries (1 - ρ) (N + 1)

/-- Rational upper form `S_{N+1}(x) + x^{N+2}/((N+2)·ρ)`, `x = 1 − ρ`. -/
def upperLog (N : Nat) (ρ : Q') : Q' :=
  lowerLog N ρ + ((1 - ρ) ^ (N + 2) * Q'.invSucc (N + 1)) * invPos ρ

theorem one_sub_add (ρ : Q') : (ρ + (1 - ρ)).eqv 1 :=
  Q'.eqv_symm (Q'.add_sub_cancel_eqv 1 ρ)

theorem lowerLog_sandwich (N : Nat) : LogSandwich (lowerLog N) where
  lower := fun _ _ h1 => logSeries_ge _ (sub_nonneg_of_le h1) N
  upper := fun ρ _ h1 =>
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (ρ * lowerLog N ρ) ((1 - ρ) ^ (N + 2) * Q'.invSucc N)
        (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (sub_nonneg_of_le h1) _) (Q'.invSucc_nonneg _)))
      (logSeries_rem ρ (1 - ρ) (sub_nonneg_of_le h1) (one_sub_add ρ) N)

theorem upperTail_nonneg (N : Nat) (ρ : Q') (h1 : ρ ≤ 1) :
    (0 : Q') ≤ ((1 - ρ) ^ (N + 2) * Q'.invSucc (N + 1)) * invPos ρ :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (sub_nonneg_of_le h1) _)
    (Q'.invSucc_nonneg _)) (invPos_nonneg ρ)

theorem lowerLog_le_upperLog (N : Nat) (ρ : Q') (h1 : ρ ≤ 1) :
    lowerLog N ρ ≤ upperLog N ρ :=
  Q'.add_le_self_of_nonneg _ _ (upperTail_nonneg N ρ h1)

theorem upperLog_sandwich (N : Nat) : LogSandwich (upperLog N) where
  lower := fun ρ h0 h1 => Q'.le_trans' _ _ _ ((lowerLog_sandwich N).lower ρ h0 h1)
    (lowerLog_le_upperLog N ρ h1)
  upper := fun ρ h0 h1 => by
    let R := (1 - ρ) ^ (N + 2) * Q'.invSucc (N + 1)
    have eR : (ρ * (R * invPos ρ)).eqv R :=
      Q'.eqv_trans _ _ _ (ClusteringImpliesGap.mul_comm_assoc ρ R (invPos ρ))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left R _ 1 (mul_invPos h0)) (Q'.mul_one_eqv R))
    have e1 : (ρ * upperLog N ρ).eqv (ρ * lowerLog N ρ + R) :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv ρ _ _) (Q'.add_eqv_congr_left _ _ _ eR)
    have s2 := Q'.add_le_add_left (ρ * lowerLog N ρ) _ ((1 - ρ) ^ (N + 2) * Q'.invSucc N)
      (Q'.mul_le_mul_of_nonneg_left _ _ ((1 - ρ) ^ (N + 2)) (invSucc_succ_le N)
        (Q'.pow_nonneg _ (sub_nonneg_of_le h1) _))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ s2
      (logSeries_rem ρ (1 - ρ) (sub_nonneg_of_le h1) (one_sub_add ρ) N))

/-! ## (3) Physical-units gap restatement -/

/-- `m′·a ≤ 1 − ρ(a)` ⟹ `m′·a ≤ L(ρ(a))` (i.e. `L(ρ(a))/a ≥ m′`). -/
theorem mass_le_log {L : Q' → Q'} (hL : LogSandwich L) (m a ρ : Q') (_ha : (0 : Q') < a)
    (hρ0 : (0 : Q') < ρ) (hρ1 : ρ ≤ 1) (hm : m * a ≤ 1 - ρ) : m * a ≤ L ρ :=
  Q'.le_trans' _ _ _ hm (hL.lower ρ hρ0 hρ1)

/-- `1 − ρ(a) ≤ M·a`, `0 < ρ₀ ≤ ρ(a)` ⟹ `ρ₀·L(ρ(a)) ≤ M·a` (`L/a ≤ M/ρ₀`). -/
theorem log_le_mass {L : Q' → Q'} (hL : LogSandwich L) (M a ρ ρ0 : Q') (_ha : (0 : Q') < a)
    (hρ0 : (0 : Q') < ρ) (hρ1 : ρ ≤ 1) (_hρ0pos : (0 : Q') < ρ0) (hρ0ρ : ρ0 ≤ ρ)
    (hM : 1 - ρ ≤ M * a) : ρ0 * L ρ ≤ M * a :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right ρ0 ρ (L ρ) hρ0ρ (hL.nonneg ρ hρ0 hρ1))
    (Q'.le_trans' _ _ _ (hL.upper ρ hρ0 hρ1) hM)

/-! ## (4) The `ρ(a) = 1 − a²` toy for every sandwiched `L` -/

def q14 : Q' := Q'.mkPos 1 4 (by decide)
def q34 : Q' := Q'.mkPos 3 4 (by decide)
def q43 : Q' := Q'.mkPos 4 3 (by decide)

theorem one_sub_rhoToy (a : Q') : (1 - rhoToy a).eqv (a * a) :=
  sub_eqv_of_add_eqv (rhoToy_add_sq a)

theorem rhoToy_le_one (a : Q') (ha : (0 : Q') ≤ a) : rhoToy a ≤ 1 :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (rhoToy a) (a * a) (Q'.mul_nonneg a a ha ha))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (rhoToy_add_sq a)))

theorem q34_le_rhoToy (a : Q') (ha : (0 : Q') ≤ a) (ha2 : a ≤ hlf) : q34 ≤ rhoToy a := by
  have hsq : a * a ≤ q14 :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left a hlf a ha2 ha)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right a hlf hlf ha2 (Q'.le_of_lt hlf_pos))
        (Q'.le_of_eqv (by decide)))
  have h1 : q14 + q34 ≤ q14 + rhoToy a :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (by decide : (q14 + q34).eqv 1)
        (Q'.eqv_symm (rhoToy_add_sq a))))
      (Q'.add_le_add_right (a * a) q14 (rhoToy a) hsq)
  exact le_of_add_le_add_left h1

/-- Per-lattice lower bound: `a·a ≤ L(ρ(a))` for every sandwiched `L`. -/
theorem rhoToy_log_ge {L : Q' → Q'} (hL : LogSandwich L) (a : Q') (ha : (0 : Q') < a)
    (ha2 : a ≤ hlf) : a * a ≤ L (rhoToy a) :=
  mass_le_log hL a a (rhoToy a) ha
    (ClusteringImpliesGap.lt_of_lt_of_le (by decide : (0 : Q') < q34)
      (q34_le_rhoToy a (Q'.le_of_lt ha) ha2))
    (rhoToy_le_one a (Q'.le_of_lt ha)) (Q'.ge_of_eqv (one_sub_rhoToy a))

/-- **`L(ρ(a))/a → 0`.**  For every sandwiched `L`, `0 < a ≤ 1/2` and
`a ≤ ε·(3/4)` give `L(1 − a²) ≤ ε·a`. -/
theorem rhoToy_log_le {L : Q' → Q'} (hL : LogSandwich L) (ε a : Q') (ha : (0 : Q') < a)
    (ha2 : a ≤ hlf) (haε : a ≤ ε * q34) : L (rhoToy a) ≤ ε * a := by
  have ha0 := Q'.le_of_lt ha
  have hρ34 := q34_le_rhoToy a ha0 ha2
  have hρ0 : (0 : Q') < rhoToy a :=
    ClusteringImpliesGap.lt_of_lt_of_le (by decide : (0 : Q') < q34) hρ34
  have hM : 1 - rhoToy a ≤ (ε * q34) * a :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_rhoToy a))
      (Q'.mul_le_mul_of_nonneg_right a (ε * q34) a haε ha0)
  have h1 := log_le_mass hL (ε * q34) a (rhoToy a) q34 ha hρ0 (rhoToy_le_one a ha0)
    (by decide) hρ34 hM
  have e2 : ((ε * q34) * a).eqv (q34 * (ε * a)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a (Q'.mul_comm_eqv ε q34))
      (Q'.mul_assoc_eqv q34 ε a)
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ q43 (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv e2))
    (by decide : (0 : Q') ≤ q43)
  have c : ∀ X : Q', (q43 * (q34 * X)).eqv X := fun X =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ 1 X (by decide)) (Q'.one_mul_eqv X))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (c _)) (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (c _)))

end YMGap.Continuum.LogBounds
