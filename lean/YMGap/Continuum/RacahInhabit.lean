/-
**Track racah — inhabiting `SixJRecouplingProgress.RacahProb` by the permutation
surrogate (constructive, axiom-clean).**

`SixJRecouplingProgress` corrected the mislabeled `SixJRecoupling` frontier down
to the doubly-stochastic `RacahProb` datum, but left `RacahProb` itself
UNINHABITED as a named residual — with the lingering worry that, like the buggy
`SixJRecoupling` (proved uninhabited at the `D = 0` truncation), it might be
secretly EMPTY.  This module removes that worry: it exhibits an explicit,
constructive, `#print axioms`-clean inhabitant `racahRP : RacahProb`.

# What is delivered (a genuine inhabitation — NOT a physics closure)

## The witness: the order-preserving constant-shift PERMUTATION kernel.

The two triangle-valid channels are step-2 intervals
  * `E = {e : fusionOK a b e ∧ fusionOK e c d} = [eLo, eHi]`,
  * `F = {f : fusionOK b c f ∧ fusionOK a f d} = [fLo, fHi]`,
with `eLo = max(|a−b|,|c−d|)`, `eHi = min(a+b,c+d)`, `fLo = max(|b−c|,|a−d|)`,
`fHi = min(b+c,a+d)`.  The kernel
  `racahPerm(a,b,c,d;e,f) = 1` iff all four `fusionOK` hold and `e+fLo = f+eLo`
is the 0/1 permutation matrix of the constant shift `f = e + fLo − eLo` on
`E → F`.  We prove it discharges all four `RacahProb` fields.

## The single mathematical crux (★): the invariant-dimension symmetry, PROVED.

`rowStoch`/`colStoch` need the shifted `f∗ = e+fLo−eLo` (resp. `e∗ = f+eLo−fLo`)
to LAND in the opposite channel — i.e. the SU(2) coupling-scheme independence
  `min(a+b,c+d) − max(|a−b|,|c−d|)  =  min(b+c,a+d) − max(|b−c|,|a−d|)`.
Over `Nat` with truncated subtraction this is `star`, proved unconditionally by
`omega` (the min/max/`|·|` are encoded as truncated-subtraction Presburger
terms).  All range, parity, and Kronecker-δ facts then reduce to `omega`, and
the row/column sums collapse through the module's own `finSum_delta_left`.

# Honest verdict (unchanged from `SixJRecouplingProgress` §3)

`racahPerm` is a 0/1 PERMUTATION, not the faithful `dim(e)·dim(f)·{6j}²`.  Because
`E` and `F` are equinumerous, a permutation matrix satisfies row+column
stochasticity automatically; two-sided stochasticity is strictly stronger than
one-sided (`rowStoch_not_imply_colStoch`) yet STILL cannot pin the fractional
Wigner-6j values.  So this INHABITS `RacahProb` (proving it non-empty and
`tetraAmp` concretely instantiable) but does NOT close the physics: a faithful
6j needs strictly more (a pentagon / Biedenharn–Elliott three-kernel relation).
The Clay YM mass gap stays OPEN; this is machinery + an inhabitation, not a
closure.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'` / `Nat` / `Fin` core only.  No `Classical.*`, no `Real`, no
`native_decide` (only `decide`/`omega` on decidable `Nat`/`Q'`/`Bool` facts).  No
`sorry` / `admit` / new `axiom`.  All witnesses are `Type`-level data.
`#print axioms` gated (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.SixJRecouplingProgress

namespace YMGap.Continuum.RacahInhabit

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.MayerTwoPlaquette
open YMGap.Continuum.PartitionBeyondTree
open YMGap.Continuum.SixJRecouplingProgress

set_option maxHeartbeats 4000000

/-! ## 0. Truncated-subtraction encoding of the channel endpoints.

`Nat.max`/`Nat.min` are opaque to core `omega`, so we encode
`|x−y| = (x−y)+(y−x)`, `max p q = q+(p−q)`, `min x y = x−(x−y)` as pure
truncated-subtraction Presburger terms.  Every downstream arithmetic fact is
then discharged by `omega`. -/

/-- `|x − y|` as truncated subtraction (`= Nat.max x y − Nat.min x y`). -/
def absd (x y : Nat) : Nat := (x - y) + (y - x)
/-- `max p q` as truncated subtraction. -/
def maxN (p q : Nat) : Nat := q + (p - q)
/-- `min x y` as truncated subtraction. -/
def minN (x y : Nat) : Nat := x - (x - y)
/-- Left channel lower endpoint `eLo = max(|a−b|,|c−d|)`. -/
def eLo (a b c d : Nat) : Nat := maxN (absd a b) (absd c d)
/-- Left channel upper endpoint `eHi = min(a+b,c+d)`. -/
def eHi (a b c d : Nat) : Nat := minN (a+b) (c+d)
/-- Right channel lower endpoint `fLo = max(|b−c|,|a−d|)`. -/
def fLo (a b c d : Nat) : Nat := maxN (absd b c) (absd a d)
/-- Right channel upper endpoint `fHi = min(b+c,a+d)`. -/
def fHi (a b c d : Nat) : Nat := minN (b+c) (a+d)

/-- `Nat.max x y − Nat.min x y = |x − y|`: the bridge from the `Nat.max/min`
form used in `fusionOK` to the `omega`-friendly truncated-subtraction form. -/
theorem absMinMax (x y : Nat) : Nat.max x y - Nat.min x y = absd x y := by
  show max x y - min x y = absd x y
  unfold absd; rw [Nat.max_def, Nat.min_def]; split <;> omega

/-- `fusionOK` decomposed into pure truncated-subtraction arithmetic. -/
theorem fusionOK_iff' (a b s : Nat) :
    fusionOK a b s = true ↔ (absd a b ≤ s ∧ s ≤ a + b ∧ (a + b + s) % 2 = 0) := by
  rw [fusionOK_iff, absMinMax]

/-- **(★) — the SU(2) invariant-dimension / coupling-scheme symmetry.**
`|E| = eHi − eLo = fHi − fLo = |F|`: the two coupling channels have the same
number of internal states.  Proved unconditionally over `Nat` (truncated
subtraction) by `omega`. -/
theorem star (a b c d : Nat) :
    eHi a b c d - eLo a b c d = fHi a b c d - fLo a b c d := by
  unfold eHi eLo fHi fLo maxN minN absd; omega

/-! ## 1. Left-channel validity: `e ∈ [eLo, eHi]`. -/

/-- A valid `e` lies in `[eLo, eHi]`, and validity forces `a+b+c+d` even. -/
theorem valid_e {a b c d e : Nat}
    (h1 : fusionOK a b e = true) (h2 : fusionOK e c d = true) :
    eLo a b c d ≤ e ∧ e ≤ eHi a b c d ∧ (a + b + c + d) % 2 = 0 := by
  rw [fusionOK_iff'] at h1 h2
  simp only [eLo, eHi, maxN, minN, absd] at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- A valid `f` lies in `[fLo, fHi]`, and validity forces `a+b+c+d` even. -/
theorem valid_f {a b c d f : Nat}
    (h3 : fusionOK b c f = true) (h4 : fusionOK a f d = true) :
    fLo a b c d ≤ f ∧ f ≤ fHi a b c d ∧ (a + b + c + d) % 2 = 0 := by
  rw [fusionOK_iff'] at h3 h4
  simp only [fLo, fHi, maxN, minN, absd] at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## 2. Endpoint bounds (tiny `omega` facts). -/

theorem fLo_ge_bc (a b c d : Nat) : absd b c ≤ fLo a b c d := by simp only [fLo, maxN]; omega
theorem fLo_ge_ad (a b c d : Nat) : absd a d ≤ fLo a b c d := by simp only [fLo, maxN]; omega
theorem fHi_le_bc (a b c d : Nat) : fHi a b c d ≤ b + c := by simp only [fHi, minN]; omega
theorem fHi_le_ad (a b c d : Nat) : fHi a b c d ≤ a + d := by simp only [fHi, minN]; omega
theorem eLo_ge_ab (a b c d : Nat) : absd a b ≤ eLo a b c d := by simp only [eLo, maxN]; omega
theorem eLo_ge_cd (a b c d : Nat) : absd c d ≤ eLo a b c d := by simp only [eLo, maxN]; omega
theorem eHi_le_ab (a b c d : Nat) : eHi a b c d ≤ a + b := by simp only [eHi, minN]; omega
theorem eHi_le_cd (a b c d : Nat) : eHi a b c d ≤ c + d := by simp only [eHi, minN]; omega

/-! ## 3. The shifted image lands in the opposite channel.

`f∗ = e + fLo − eLo` (row) and `e∗ = f + eLo − fLo` (column).  Range and parity
of the image use the crux (★) internally (rediscovered by `omega` from the raw
labels); each `omega` is isolated to keep it tractable. -/

theorem fstar_ge (a b c d e : Nat) (h1 : eLo a b c d ≤ e) :
    fLo a b c d ≤ e + fLo a b c d - eLo a b c d := by omega
theorem fstar_le (a b c d e : Nat)
    (h1 : eLo a b c d ≤ e) (h2 : e ≤ eHi a b c d) :
    e + fLo a b c d - eLo a b c d ≤ fHi a b c d := by
  simp only [eLo, eHi, fLo, fHi, maxN, minN, absd] at *; omega
theorem fstar_par1 (a b c d e : Nat) (h1 : eLo a b c d ≤ e)
    (p1 : (a + b + e) % 2 = 0) (p2 : (e + c + d) % 2 = 0) :
    (b + c + (e + fLo a b c d - eLo a b c d)) % 2 = 0 := by
  simp only [eLo, fLo, maxN, absd] at *; omega
theorem fstar_par2 (a b c d e : Nat) (h1 : eLo a b c d ≤ e)
    (p1 : (a + b + e) % 2 = 0) (p2 : (e + c + d) % 2 = 0) :
    (a + (e + fLo a b c d - eLo a b c d) + d) % 2 = 0 := by
  simp only [eLo, fLo, maxN, absd] at *; omega

theorem estar_ge (a b c d f : Nat) (h1 : fLo a b c d ≤ f) :
    eLo a b c d ≤ f + eLo a b c d - fLo a b c d := by omega
theorem estar_le (a b c d f : Nat) (h1 : fLo a b c d ≤ f) (h2 : f ≤ fHi a b c d) :
    f + eLo a b c d - fLo a b c d ≤ eHi a b c d := by
  simp only [eLo, eHi, fLo, fHi, maxN, minN, absd] at *; omega
theorem estar_par1 (a b c d f : Nat) (h1 : fLo a b c d ≤ f)
    (p1 : (b + c + f) % 2 = 0) (p2 : (a + f + d) % 2 = 0) :
    (a + b + (f + eLo a b c d - fLo a b c d)) % 2 = 0 := by
  simp only [eLo, fLo, maxN, absd] at *; omega
theorem estar_par2 (a b c d f : Nat) (h1 : fLo a b c d ≤ f)
    (p1 : (b + c + f) % 2 = 0) (p2 : (a + f + d) % 2 = 0) :
    ((f + eLo a b c d - fLo a b c d) + c + d) % 2 = 0 := by
  simp only [eLo, fLo, maxN, absd] at *; omega

/-- **The shifted `f∗` is valid in the RIGHT channel.**  Both `fusionOK b c f∗`
and `fusionOK a f∗ d` hold — this is the crux (★) plus parity, assembled from
the isolated bounds above. -/
theorem fstar_valid {a b c d e : Nat}
    (h1 : fusionOK a b e = true) (h2 : fusionOK e c d = true) :
    fusionOK b c (e + fLo a b c d - eLo a b c d) = true
      ∧ fusionOK a (e + fLo a b c d - eLo a b c d) d = true := by
  obtain ⟨he1, he2, _⟩ := valid_e h1 h2
  have hp1 : (a + b + e) % 2 = 0 := ((fusionOK_iff' a b e).mp h1).2.2
  have hp2 : (e + c + d) % 2 = 0 := ((fusionOK_iff' e c d).mp h2).2.2
  have b1 := fLo_ge_bc a b c d; have b2 := fLo_ge_ad a b c d
  have b3 := fHi_le_bc a b c d; have b4 := fHi_le_ad a b c d
  have g1 := fstar_ge a b c d e he1
  have g2 := fstar_le a b c d e he1 he2
  refine ⟨(fusionOK_iff' b c _).mpr ⟨Nat.le_trans b1 g1, Nat.le_trans g2 b3,
            fstar_par1 a b c d e he1 hp1 hp2⟩,
         (fusionOK_iff' a _ d).mpr ⟨?_, ?_, fstar_par2 a b c d e he1 hp1 hp2⟩⟩
  · simp only [absd] at b2 ⊢; omega
  · simp only [absd] at b2 ⊢; omega

/-- **The shifted `e∗` is valid in the LEFT channel** (the column mirror). -/
theorem estar_valid {a b c d f : Nat}
    (h3 : fusionOK b c f = true) (h4 : fusionOK a f d = true) :
    fusionOK a b (f + eLo a b c d - fLo a b c d) = true
      ∧ fusionOK (f + eLo a b c d - fLo a b c d) c d = true := by
  obtain ⟨hf1, hf2, _⟩ := valid_f h3 h4
  have hp1 : (b + c + f) % 2 = 0 := ((fusionOK_iff' b c f).mp h3).2.2
  have hp2 : (a + f + d) % 2 = 0 := ((fusionOK_iff' a f d).mp h4).2.2
  have b1 := eLo_ge_ab a b c d; have b2 := eLo_ge_cd a b c d
  have b3 := eHi_le_ab a b c d; have b4 := eHi_le_cd a b c d
  have g1 := estar_ge a b c d f hf1
  have g2 := estar_le a b c d f hf1 hf2
  refine ⟨(fusionOK_iff' a b _).mpr ⟨Nat.le_trans b1 g1, Nat.le_trans g2 b3,
            estar_par1 a b c d f hf1 hp1 hp2⟩,
         (fusionOK_iff' _ c d).mpr ⟨?_, ?_, estar_par2 a b c d f hf1 hp1 hp2⟩⟩
  · simp only [absd] at b2 ⊢; omega
  · simp only [absd] at b2 ⊢; omega

/-! ## 4. The shift equalities and their Kronecker-δ (off-diagonal) negations. -/

theorem shift_eq {a b c d e : Nat}
    (h1 : fusionOK a b e = true) (h2 : fusionOK e c d = true) :
    e + fLo a b c d = (e + fLo a b c d - eLo a b c d) + eLo a b c d := by
  obtain ⟨he1, _, _⟩ := valid_e h1 h2; omega

theorem off_eq {a b c d e f : Nat}
    (h1 : fusionOK a b e = true) (h2 : fusionOK e c d = true)
    (hf : f ≠ e + fLo a b c d - eLo a b c d) :
    ¬ (e + fLo a b c d = f + eLo a b c d) := by
  obtain ⟨he1, _, _⟩ := valid_e h1 h2; omega

theorem shift_eq_col {a b c d f : Nat}
    (h3 : fusionOK b c f = true) (h4 : fusionOK a f d = true) :
    (f + eLo a b c d - fLo a b c d) + fLo a b c d = f + eLo a b c d := by
  obtain ⟨hf1, _, _⟩ := valid_f h3 h4; omega

theorem off_eq_col {a b c d f g : Nat}
    (h3 : fusionOK b c f = true) (h4 : fusionOK a f d = true)
    (hg : g ≠ f + eLo a b c d - fLo a b c d) :
    ¬ (g + fLo a b c d = f + eLo a b c d) := by
  obtain ⟨hf1, _, _⟩ := valid_f h3 h4; omega

/-! ## 5. `Bool`-equality helpers. -/

theorem beq_true_of_eq {x y : Nat} (h : x = y) : (x == y) = true := by
  subst h; exact decide_eq_true rfl
theorem beq_false_of_ne {x y : Nat} (h : x ≠ y) : (x == y) = false :=
  decide_eq_false h

/-! ## 6. The permutation kernel `racahPerm` and its evaluation. -/

/-- The 0/1 permutation guard: valid on both channels AND on the constant shift
`e + fLo = f + eLo` (i.e. `f = e + fLo − eLo`). -/
def racahGuard (a b c d e f : Nat) : Bool :=
  fusionOK a b e && fusionOK e c d && fusionOK b c f && fusionOK a f d
    && (e + fLo a b c d == f + eLo a b c d)

/-- The permutation kernel `P : (Fin 6 → Rep) → Q'`. -/
def racahPerm (j : Fin 6 → Rep) : Q' :=
  if racahGuard (j 0) (j 1) (j 2) (j 3) (j 4) (j 5) = true then 1 else 0

/-- Evaluation on an `mk6`-assembled label. -/
theorem racahPerm_mk6 (a b c d e f : Rep) :
    racahPerm (mk6 a b c d e f) = if racahGuard a b c d e f = true then 1 else 0 := rfl

theorem racahPerm_nonneg (j : Fin 6 → Rep) : (0 : Q') ≤ racahPerm j := by
  unfold racahPerm
  by_cases hg : racahGuard (j 0) (j 1) (j 2) (j 3) (j 4) (j 5) = true
  · rw [if_pos hg]; decide
  · rw [if_neg hg]; decide

/-- `fusionOK` true ⇒ its `fusionInd` value is `1`. -/
theorem fusionInd_val_one {a b s : Nat} (h : fusionOK a b s = true) : fusionInd a b s = 1 := by
  unfold fusionInd; rw [if_pos h]

/-- If a product of two `fusionInd`s is `≃ 1`, both factors are triangle-valid.
Stated over SIX independent indices so it applies to BOTH the row product
`fusionInd a b e · fusionInd e c d` and the column product
`fusionInd b c f · fusionInd a f d` (whose shared index sits in a different
slot) without triggering divergent unification. -/
theorem fusionInd_prod_one {a b s p q r : Nat}
    (h : (fusionInd a b s * fusionInd p q r).eqv 1) :
    fusionOK a b s = true ∧ fusionOK p q r = true := by
  by_cases h1 : fusionOK a b s = true
  · by_cases h2 : fusionOK p q r = true
    · exact ⟨h1, h2⟩
    · exfalso
      have hz : fusionInd p q r = 0 := by unfold fusionInd; rw [if_neg h2]
      rw [hz] at h
      have h0 : (fusionInd a b s * (0 : Q')).eqv 0 := Q'.mul_zero_eqv _
      exact absurd (Q'.eqv_trans _ _ _ (Q'.eqv_symm h) h0) (by decide)
  · exfalso
    have hz : fusionInd a b s = 0 := by unfold fusionInd; rw [if_neg h1]
    rw [hz] at h
    have h0 : ((0 : Q') * fusionInd p q r).eqv 0 := Q'.zero_mul_eqv _
    exact absurd (Q'.eqv_trans _ _ _ (Q'.eqv_symm h) h0) (by decide)

/-! ## 7. Guard evaluation at the diagonal and off-diagonal. -/

/-- Row diagonal: the guard fires at `f = f∗ = e + fLo − eLo`. -/
theorem guard_diag {a b c d e : Nat}
    (h1 : fusionOK a b e = true) (h2 : fusionOK e c d = true) :
    racahGuard a b c d e (e + fLo a b c d - eLo a b c d) = true := by
  obtain ⟨hbc, hafd⟩ := fstar_valid h1 h2
  have hsh := shift_eq h1 h2
  unfold racahGuard
  rw [h1, h2, hbc, hafd]
  simp only [Bool.true_and, Bool.and_true]
  exact beq_true_of_eq hsh

/-- Row off-diagonal: the guard is silent at every `f ≠ f∗`. -/
theorem guard_off {a b c d e f : Nat}
    (h1 : fusionOK a b e = true) (h2 : fusionOK e c d = true)
    (hf : f ≠ e + fLo a b c d - eLo a b c d) :
    racahGuard a b c d e f = false := by
  have hne := off_eq h1 h2 hf
  unfold racahGuard
  rw [beq_false_of_ne hne]
  simp only [Bool.and_false]

/-- Column diagonal: the guard fires at `e = e∗ = f + eLo − fLo`. -/
theorem guard_diag_col {a b c d f : Nat}
    (h3 : fusionOK b c f = true) (h4 : fusionOK a f d = true) :
    racahGuard a b c d (f + eLo a b c d - fLo a b c d) f = true := by
  obtain ⟨hab, hecd⟩ := estar_valid h3 h4
  have hsh := shift_eq_col h3 h4
  unfold racahGuard
  rw [hab, hecd, h3, h4]
  simp only [Bool.true_and, Bool.and_true]
  exact beq_true_of_eq hsh

/-- Column off-diagonal: the guard is silent at every `e ≠ e∗`. -/
theorem guard_off_col {a b c d f g : Nat}
    (h3 : fusionOK b c f = true) (h4 : fusionOK a f d = true)
    (hg : g ≠ f + eLo a b c d - fLo a b c d) :
    racahGuard a b c d g f = false := by
  have hne := off_eq_col h3 h4 hg
  unfold racahGuard
  rw [beq_false_of_ne hne]
  simp only [Bool.and_false]

/-! ## 8. The row/column sums collapse to `1` (guarded δ-collapse). -/

/-- **Row-stochasticity.**  For a left-valid `e` with `f∗ < D`, the row over `f`
collapses (via `finSum_delta_left`) to the single unit at `f∗`. -/
theorem rowSum_one {D a b c d e : Nat}
    (hD : e + fLo a b c d - eLo a b c d < D)
    (h1 : fusionOK a b e = true) (h2 : fusionOK e c d = true) :
    (finSum (fun f => racahPerm (mk6 a b c d e f)) D).eqv 1 := by
  have hdiag : (racahPerm (mk6 a b c d e (e + fLo a b c d - eLo a b c d))).eqv 1 := by
    rw [racahPerm_mk6, if_pos (guard_diag h1 h2)]; exact Q'.eqv_refl 1
  have hoff : ∀ g, g ≠ e + fLo a b c d - eLo a b c d →
      (racahPerm (mk6 a b c d e g)).eqv 0 := by
    intro g hg
    rw [racahPerm_mk6, if_neg (by rw [guard_off h1 h2 hg]; decide)]
    exact Q'.eqv_refl 0
  have hcollapse := finSum_delta_left
    (fun f => racahPerm (mk6 a b c d e f)) (fun _ => (1 : Q'))
    (e + fLo a b c d - eLo a b c d) hoff hdiag hD
  refine Q'.eqv_trans _ _ _ ?_ hcollapse
  exact finSum_eqv_congr_lt _ _ D (fun f _ => Q'.eqv_symm (Q'.mul_one_eqv _))

/-- **Column-stochasticity.**  For a right-valid `f` with `e∗ < D`, the column
over `e` collapses to the single unit at `e∗`. -/
theorem colSum_one {D a b c d f : Nat}
    (hD : f + eLo a b c d - fLo a b c d < D)
    (h3 : fusionOK b c f = true) (h4 : fusionOK a f d = true) :
    (finSum (fun e => racahPerm (mk6 a b c d e f)) D).eqv 1 := by
  have hdiag : (racahPerm (mk6 a b c d (f + eLo a b c d - fLo a b c d) f)).eqv 1 := by
    rw [racahPerm_mk6, if_pos (guard_diag_col h3 h4)]; exact Q'.eqv_refl 1
  have hoff : ∀ g, g ≠ f + eLo a b c d - fLo a b c d →
      (racahPerm (mk6 a b c d g f)).eqv 0 := by
    intro g hg
    rw [racahPerm_mk6, if_neg (by rw [guard_off_col h3 h4 hg]; decide)]
    exact Q'.eqv_refl 0
  have hcollapse := finSum_delta_left
    (fun e => racahPerm (mk6 a b c d e f)) (fun _ => (1 : Q'))
    (f + eLo a b c d - fLo a b c d) hoff hdiag hD
  refine Q'.eqv_trans _ _ _ ?_ hcollapse
  exact finSum_eqv_congr_lt _ _ D (fun e _ => Q'.eqv_symm (Q'.mul_one_eqv _))

/-! ## 9. The four field obligations, as standalone theorems.

Proving each field as a top-level theorem about `racahPerm` (rather than inline
in the structure instance) keeps the goal free of the self-referential
`racahRP.racahProb` projection during elaboration. -/

/-- Field `support`: `racahPerm`'s support lies on both triangle channels. -/
theorem racahPerm_support (a b c d e f : Rep)
    (hne : ¬ (racahPerm (mk6 a b c d e f)).eqv 0) :
    (fusionInd a b e * fusionInd e c d).eqv 1 ∧
      (fusionInd b c f * fusionInd a f d).eqv 1 := by
  rw [racahPerm_mk6] at hne
  by_cases hg : racahGuard a b c d e f = true
  · have h4 := hg
    unfold racahGuard at h4
    simp only [Bool.and_eq_true] at h4
    obtain ⟨⟨⟨⟨hab, hecd⟩, hbcf⟩, hafd⟩, _⟩ := h4
    refine ⟨?_, ?_⟩
    · rw [fusionInd_val_one hab, fusionInd_val_one hecd]; exact Q'.mul_one_eqv 1
    · rw [fusionInd_val_one hbcf, fusionInd_val_one hafd]; exact Q'.mul_one_eqv 1
  · rw [if_neg hg] at hne; exact absurd (Q'.eqv_refl 0) hne

/-- Field `rowStoch`: guarded row-stochasticity of `racahPerm`. -/
theorem racahPerm_rowStoch (D a b c d e : Rep) (hguard : a + b + c + d < D)
    (hvalid : (fusionInd a b e * fusionInd e c d).eqv 1) :
    (finSum (fun f => racahPerm (mk6 a b c d e f)) D).eqv 1 := by
  obtain ⟨hab, hecd⟩ := fusionInd_prod_one hvalid
  have hlt : e + fLo a b c d - eLo a b c d < D := by
    obtain ⟨he1, he2, _⟩ := valid_e hab hecd
    have hle : e + fLo a b c d - eLo a b c d ≤ b + c :=
      Nat.le_trans (fstar_le a b c d e he1 he2) (fHi_le_bc a b c d)
    exact Nat.lt_of_le_of_lt (Nat.le_trans hle (by omega)) hguard
  exact rowSum_one hlt hab hecd

/-- Field `colStoch`: guarded column-stochasticity of `racahPerm`. -/
theorem racahPerm_colStoch (D a b c d f : Rep) (hguard : a + b + c + d < D)
    (hvalid : (fusionInd b c f * fusionInd a f d).eqv 1) :
    (finSum (fun e => racahPerm (mk6 a b c d e f)) D).eqv 1 := by
  obtain ⟨hbcf, hafd⟩ := fusionInd_prod_one hvalid
  have hlt : f + eLo a b c d - fLo a b c d < D := by
    obtain ⟨hf1, hf2, _⟩ := valid_f hbcf hafd
    have hle : f + eLo a b c d - fLo a b c d ≤ a + b :=
      Nat.le_trans (estar_le a b c d f hf1 hf2) (eHi_le_ab a b c d)
    exact Nat.lt_of_le_of_lt (Nat.le_trans hle (by omega)) hguard
  exact colSum_one hlt hbcf hafd

/-! ## 10. The inhabitant. -/

/-- **`RacahProb` is INHABITED.**  The constant-shift permutation kernel
`racahPerm` discharges all four fields: nonnegativity, two-channel support, and
guarded row+column stochasticity.  This removes the worry that `RacahProb`, like
the buggy `SixJRecoupling`, is secretly empty — it is a genuine, constructive,
axiom-clean witness.  (Honest caveat: `racahPerm` is a 0/1 permutation, not the
faithful `dim·dim·{6j}²`; see the module header.) -/
def racahRP : RacahProb where
  racahProb := racahPerm
  nonneg := racahPerm_nonneg
  support := racahPerm_support
  rowStoch := racahPerm_rowStoch
  colStoch := racahPerm_colStoch

/-- **Corollary: the tetrahedron amplitude is concretely instantiable.**  With
the witness `racahRP`, the `m ≥ 4 → (m = 3 corner) + one contraction` collapse
`tetraAmp` is a genuine, computable, nonnegative `Q'` — no longer resting on an
open datum. -/
theorem tetraAmp_racahRP_nonneg (D : Nat) (a b c d : Rep) :
    (0 : Q') ≤ tetraAmp racahRP D a b c d :=
  tetraAmp_nonneg racahRP D a b c d

/-! ## 10. `#print axioms` gates (permitted: `propext` / `Quot.sound`). -/

#print axioms star
#print axioms fstar_valid
#print axioms estar_valid
#print axioms rowSum_one
#print axioms colSum_one
#print axioms racahRP
#print axioms tetraAmp_racahRP_nonneg

end YMGap.Continuum.RacahInhabit
