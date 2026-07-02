/-
# `ArctanValueIdentity`: the value-identity `sval ≃ sinC(arctan 1/5)`, leg (A) closed

This module carries the honest split of the load-bearing arctan↔trig atom into its
two legs, and **discharges leg (A) in full** (mechanically, below `DiffJTP`),
leaving only leg (B) as a sharply-named Type-level residual.

## The precise target

The atom `ArctanSeriesTrigBridge.ArctanTrigConverges` is inter-derivable (by
`ArctanTrigConvergesProof.atom_iff_valueIdent`) with the pair of value-identities

    Equiv sval (sinCat5 d)   -- sine leg
    Equiv cval (cosCat5 d)   -- cosine leg

where `sval = limCReal pc = Σ pc_j (1/5)^j` (the in-`x` ODE series) and
`sinCat5 d = lim_k sinNN(θ_k)` (the in-angle sine-Taylor series along the arctan
partial sums).  Unfolding, `sval.approx D = series pc xv D`.

## What is genuinely proved here (leg (A): the coefficient-match core)

The combinatorial core of leg (A) is **recurrence uniqueness**: the coupled linear
ODE recurrence

    (n+2)·f_{n+2} + n·f_n ≃ g_{n+1},   (n+2)·g_{n+2} + n·g_n ≃ −f_{n+1},
    (f_0,g_0) ≃ (0,1),   (f_1,g_1) ≃ (1,0)

has a UNIQUE (up to `Q'.eqv`) solution — namely `(pc, qc)`.  Any composed-Taylor /
Bell coefficient sequence `γ` of `sin∘arctan` satisfies exactly this recurrence
(the formal-power-series chain rule + `arctan' = 1/(1+x²)`), so `γ_j ≃ pc_j`.  We
package a solution as the Type-level `CoupledRecSol` and prove:

* `mulCancelLeftPos` — positive multiplicative left-cancellation on `Q'` (via
  `recipPos`), the one missing arithmetic lemma the recurrence uniqueness needs;
* `sol_unique` — the two-step-induction uniqueness `f_n ≃ pc_n ∧ g_n ≃ qc_n`;
* `series_eqv_of_coeff_eqv`, `equiv_of_approx_eqv`, `limCReal_equiv_of_coeff_eqv`
  — the lift of pointwise-`eqv` coefficients to `CReal.Equiv` of the two series
  limits;
* `legA_sine` / `legA_cosine` — **leg (A) fully discharged**: for ANY bounded
  coupled solution `s`, `limCReal s.f ≃ sval` and `limCReal s.g ≃ cval`.

None of this differentiates a convergent `CReal` product; it is strictly below
`DiffJTP`.

## The single named residual (leg (B): the composition tail)

`CompositionTail d s hf hg` carries the sole transcendental residue — the two
double-limit interchanges `limCReal s.f ≃ sinCat5 d`, `limCReal s.g ≃ cosCat5 d`
(the `k`-limit-of-the-angle vs `N`-truncation-of-the-composite identification).
`atom_of_tail` closes the atom from `(A)+(B)` through
`ArctanTrigConvergesProof.ComposedSeriesData` / `atom_of_composed`.

Honest verdict (unchanged from the module audit): closing (A) makes ZERO progress
on the atom — `sinCat5` is DEFINED as `lim_k sinNN(θ_k)`, never as `Σ γ_j x^j` — so
the atom's whole transcendental budget is the tail `CompositionTail`.  It is carried
as Type-level data (never `sorry`, never a custom axiom).  For the maximally-honest
"trivial intermediary" packaging (`Csin := sval`, leg (A) reflexive) we also expose
`ValueIdentityResidual`, which relocates the entire residue onto the value-identity
itself.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, `native_decide`,
`sorry`, or custom `axiom`.  All witnesses are `Type`-level data (Rule 8).
-/

import YMGap.Continuum.ArctanTrigConvergesProof
import YMGap.Continuum.ArctanSeriesTrigBridge
import YMGap.Constructive.QDivArctanSeries
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.ArctanValueIdentity

open YMGap.Constructive
open YMGap.Constructive.QDivArctanSeries
open YMGap.Continuum.TanArctan (series qpow)
open YMGap.Continuum.ArctanSeriesTrigBridge
open YMGap.Continuum.ArctanTrigConvergesProof

/-! ## 0. Small `Q'` glue: additive cancellation and positive multiplicative cancellation -/

/-- `(X + c) + -c ≃ X`. -/
private theorem add_neg_cancel_right (X c : Q') : ((X + c) + -c).eqv X := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv X c (-c)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left X (c + -c) 0 (Q'.add_neg_self_eqv c)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' X)

/-- **Additive cancellation.**  `X + c ≃ Y + e` and `c ≃ e` ⟹ `X ≃ Y`. -/
private theorem addCancelRight {X Y c e : Q'} (h : (X + c).eqv (Y + e))
    (hce : c.eqv e) : X.eqv Y := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (add_neg_cancel_right X c)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (X + c) (Y + e) (-c) h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Y + e) (-c) (-e) (Q'.neg_eqv_congr c e hce)) ?_
  exact add_neg_cancel_right Y e

/-- **Positive multiplicative left-cancellation.**  `d > 0` and `d·a ≃ d·b` ⟹
`a ≃ b`.  Multiply by `recipPos d` and collapse `d·(1/d) ≃ 1`. -/
private theorem mulCancelLeftPos {d a b : Q'} (hd : (0 : Q') < d)
    (h : (d * a).eqv (d * b)) : a.eqv b := by
  have hcollapse : ∀ z : Q', ((d * z) * Q'.recipPos d hd).eqv z := by
    intro z
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (d * z) (z * d) (Q'.recipPos d hd)
        (Q'.mul_comm_eqv d z)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv z d (Q'.recipPos d hd)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left z (d * Q'.recipPos d hd) 1 (Q'.mul_recipPos_eqv d hd)) ?_
    exact Q'.mul_one_eqv z
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (hcollapse a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (d * a) (d * b) (Q'.recipPos d hd) h) ?_
  exact hcollapse b

/-! ## 1. The coupled-recurrence solution carrier (Type-level) -/

/-- **A solution of the arctan-ODE coupled recurrence.**  Any composed-Taylor /
Bell coefficient sequence `(γ, δ)` of `sin∘arctan`, `cos∘arctan` is such a solution:
the recurrences are the formal-power-series form of `(1+x²)γ' = δ`,
`(1+x²)δ' = −γ` with bases `(0,1)`, `(1,0)`.  Carried as `Type`-level data. -/
structure CoupledRecSol : Type where
  /-- The candidate sine coefficients. -/
  f : Nat → Q'
  /-- The candidate cosine coefficients. -/
  g : Nat → Q'
  /-- Base: `f 0 ≃ pc 0 (= 0)`. -/
  f0 : (f 0).eqv (pc 0)
  /-- Base: `g 0 ≃ qc 0 (= 1)`. -/
  g0 : (g 0).eqv (qc 0)
  /-- Base: `f 1 ≃ pc 1 (= 1)`. -/
  f1 : (f 1).eqv (pc 1)
  /-- Base: `g 1 ≃ qc 1 (= 0)`. -/
  g1 : (g 1).eqv (qc 1)
  /-- Sine recurrence: `(n+2)·f_{n+2} + n·f_n ≃ g_{n+1}`. -/
  frec : ∀ n, (Q'.ofNat (n + 2) * f (n + 2) + Q'.ofNat n * f n).eqv (g (n + 1))
  /-- Cosine recurrence: `(n+2)·g_{n+2} + n·g_n ≃ −f_{n+1}`. -/
  grec : ∀ n, (Q'.ofNat (n + 2) * g (n + 2) + Q'.ofNat n * g n).eqv (-(f (n + 1)))

/-- **Recurrence uniqueness (the leg-(A) core).**  The coupled recurrence has a
unique solution up to `eqv`: `f_n ≃ pc_n` and `g_n ≃ qc_n` for all `n`.  Two-step
`Nat` induction: the `(n+2)` step uses `frec`/`grec` against `pc_rec`/`qc_rec`,
additive cancellation of the `n·(·)` term, then positive multiplicative
cancellation of the `(n+2)` factor. -/
theorem sol_unique (s : CoupledRecSol) :
    ∀ n, (s.f n).eqv (pc n) ∧ (s.g n).eqv (qc n) := by
  have paired : ∀ n,
      ((s.f n).eqv (pc n) ∧ (s.g n).eqv (qc n)) ∧
      ((s.f (n + 1)).eqv (pc (n + 1)) ∧ (s.g (n + 1)).eqv (qc (n + 1))) := by
    intro n
    induction n with
    | zero => exact ⟨⟨s.f0, s.g0⟩, ⟨s.f1, s.g1⟩⟩
    | succ k ih =>
      obtain ⟨⟨hfk, hgk⟩, ⟨hfk1, hgk1⟩⟩ := ih
      have hd : (0 : Q') < Q'.ofNat (k + 2) := Q'.ofNat_succ_pos (k + 1)
      refine ⟨⟨hfk1, hgk1⟩, ?_, ?_⟩
      · -- f(k+2) ≃ pc(k+2)
        have hmul : (Q'.ofNat (k + 2) * s.f (k + 2)).eqv
            (Q'.ofNat (k + 2) * pc (k + 2)) := by
          refine addCancelRight ?_
            (Q'.mul_eqv_congr_left (Q'.ofNat k) (s.f k) (pc k) hfk)
          refine Q'.eqv_trans _ _ _ (s.frec k) ?_
          refine Q'.eqv_trans _ _ _ hgk1 ?_
          exact Q'.eqv_symm (pc_rec k)
        exact mulCancelLeftPos hd hmul
      · -- g(k+2) ≃ qc(k+2)
        have hmul : (Q'.ofNat (k + 2) * s.g (k + 2)).eqv
            (Q'.ofNat (k + 2) * qc (k + 2)) := by
          refine addCancelRight ?_
            (Q'.mul_eqv_congr_left (Q'.ofNat k) (s.g k) (qc k) hgk)
          refine Q'.eqv_trans _ _ _ (s.grec k) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.neg_eqv_congr (s.f (k + 1)) (pc (k + 1)) hfk1) ?_
          exact Q'.eqv_symm (qc_rec k)
        exact mulCancelLeftPos hd hmul
  exact fun n => (paired n).1

/-- Sine leg of `sol_unique`. -/
theorem sol_f_eqv_pc (s : CoupledRecSol) (n : Nat) : (s.f n).eqv (pc n) :=
  (sol_unique s n).1
/-- Cosine leg of `sol_unique`. -/
theorem sol_g_eqv_qc (s : CoupledRecSol) (n : Nat) : (s.g n).eqv (qc n) :=
  (sol_unique s n).2

/-! ## 2. Lifting pointwise-`eqv` coefficients to `CReal.Equiv` of the series limits -/

/-- Pointwise-`eqv` coefficients give `eqv` partial sums at every truncation. -/
theorem series_eqv_of_coeff_eqv {a b : Nat → Q'} (h : ∀ j, (a j).eqv (b j)) :
    ∀ N, (series a xv N).eqv (series b xv N)
  | 0 => Q'.eqv_refl _
  | N + 1 => by
    show (series a xv N + a N * qpow xv N).eqv (series b xv N + b N * qpow xv N)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (series a xv N) (series b xv N) (a N * qpow xv N)
        (series_eqv_of_coeff_eqv h N)) ?_
    exact Q'.add_eqv_congr_left (series b xv N) (a N * qpow xv N) (b N * qpow xv N)
      (Q'.mul_eqv_congr_right (a N) (b N) (qpow xv N) (h N))

/-- Pointwise-`eqv` approximations give `CReal.Equiv` (take `N = 0`). -/
theorem equiv_of_approx_eqv {A B : CReal} (h : ∀ n, (A.approx n).eqv (B.approx n)) :
    CReal.Equiv A B := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨?_, ?_⟩⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (h n))
      (Q'.add_le_self_of_nonneg (B.approx n) ε (Q'.le_of_lt hε))
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (h n)))
      (Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε))

/-- **`limCReal` congruence.**  Pointwise-`eqv` coefficients ⟹ the two majorized
series limits are `CReal.Equiv`. -/
theorem limCReal_equiv_of_coeff_eqv {a b : Nat → Q'}
    (ha : ∀ j, Q'.abs (a j) ≤ 1) (hb : ∀ j, Q'.abs (b j) ≤ 1)
    (h : ∀ j, (a j).eqv (b j)) :
    CReal.Equiv (limCReal a ha) (limCReal b hb) :=
  equiv_of_approx_eqv (fun n => series_eqv_of_coeff_eqv h n)

/-! ## 3. Leg (A) discharged: any bounded coupled solution has `limCReal = sval/cval` -/

/-- **Leg (A), sine.**  For any bounded coupled solution, `limCReal s.f ≃ sval`.
`sval = limCReal pc`, `s.f n ≃ pc n` (uniqueness), so `limCReal_equiv` closes it. -/
theorem legA_sine (s : CoupledRecSol) (hf : ∀ j, Q'.abs (s.f j) ≤ 1) :
    CReal.Equiv (limCReal s.f hf) sval :=
  limCReal_equiv_of_coeff_eqv hf coeff_pc_le_one (sol_f_eqv_pc s)

/-- **Leg (A), cosine.**  `limCReal s.g ≃ cval`. -/
theorem legA_cosine (s : CoupledRecSol) (hg : ∀ j, Q'.abs (s.g j) ≤ 1) :
    CReal.Equiv (limCReal s.g hg) cval :=
  limCReal_equiv_of_coeff_eqv hg coeff_qc_le_one (sol_g_eqv_qc s)

/-! ## 4. Leg (B): the single named transcendental residual, and the atom -/

/-- **The composition tail — the sole transcendental residue (leg (B)).**  Carries
the two double-limit interchanges identifying the composed-series limits with the
genuine constructive `sinC`/`cosC` of the arctan angle.  Type-level data. -/
structure CompositionTail (d : At5Modulus) (s : CoupledRecSol)
    (hf : ∀ j, Q'.abs (s.f j) ≤ 1) (hg : ∀ j, Q'.abs (s.g j) ≤ 1) : Type where
  /-- `limCReal s.f ≃ sinC(arctan 1/5)`. -/
  tailSin : CReal.Equiv (limCReal s.f hf) (sinCat5 d)
  /-- `limCReal s.g ≃ cosC(arctan 1/5)`. -/
  tailCos : CReal.Equiv (limCReal s.g hg) (cosCat5 d)

/-- **(A) + (B) assembled into the existing `ComposedSeriesData`.**  Leg (A) supplies
`coeffSin`/`coeffCos` (from `legA_*`, symmetrised); leg (B) supplies the tails. -/
def composedData (d : At5Modulus) (s : CoupledRecSol)
    (hf : ∀ j, Q'.abs (s.f j) ≤ 1) (hg : ∀ j, Q'.abs (s.g j) ≤ 1)
    (t : CompositionTail d s hf hg) : ComposedSeriesData d where
  Csin := limCReal s.f hf
  Ccos := limCReal s.g hg
  coeffSin := CReal.Equiv.symm (legA_sine s hf)
  coeffCos := CReal.Equiv.symm (legA_cosine s hg)
  tailSin := t.tailSin
  tailCos := t.tailCos

/-- **The atom, discharged from a coupled solution + its composition tail.** -/
theorem atom_of_tail (d : At5Modulus) (s : CoupledRecSol)
    (hf : ∀ j, Q'.abs (s.f j) ≤ 1) (hg : ∀ j, Q'.abs (s.g j) ≤ 1)
    (t : CompositionTail d s hf hg) : ArctanTrigConverges :=
  atom_of_composed d (composedData d s hf hg t)

/-! ## 5. The maximally-honest "trivial intermediary" packaging (leg (A) reflexive) -/

/-- **The value-identity residual.**  With the trivial intermediary `Csin := sval`,
leg (A) is reflexive and the ENTIRE residue is the two value-identities
`sval ≃ sinCat5 d`, `cval ≃ cosCat5 d`.  Type-level data. -/
structure ValueIdentityResidual (d : At5Modulus) : Type where
  /-- `sval ≃ sinC(arctan 1/5)`. -/
  sineLeg : CReal.Equiv sval (sinCat5 d)
  /-- `cval ≃ cosC(arctan 1/5)`. -/
  cosineLeg : CReal.Equiv cval (cosCat5 d)

/-- The atom follows from the value-identity residual (transport of the proved
`k`-limit leg). -/
theorem atom_of_valueIdentity (d : At5Modulus) (r : ValueIdentityResidual d) :
    ArctanTrigConverges :=
  valueIdent_to_atom d r.sineLeg r.cosineLeg

/-- Conversely the atom yields the value-identity residual (limit-uniqueness). -/
def valueIdentity_of_atom (d : At5Modulus) (h : ArctanTrigConverges) :
    ValueIdentityResidual d :=
  ⟨(atom_iff_valueIdent d).mp h |>.1, (atom_iff_valueIdent d).mp h |>.2⟩

/-- A composition tail collapses (through leg (A)) to a value-identity residual —
making precise that the two packagings carry the SAME transcendental content. -/
def valueIdentity_of_tail (d : At5Modulus) (s : CoupledRecSol)
    (hf : ∀ j, Q'.abs (s.f j) ≤ 1) (hg : ∀ j, Q'.abs (s.g j) ≤ 1)
    (t : CompositionTail d s hf hg) : ValueIdentityResidual d :=
  ⟨CReal.Equiv.trans (CReal.Equiv.symm (legA_sine s hf)) t.tailSin,
   CReal.Equiv.trans (CReal.Equiv.symm (legA_cosine s hg)) t.tailCos⟩

/-! ## 6. The precise target, restated at the approximation level -/

/-- The in-`x` ODE-series unfolding of the sine target: `sval.approx D = Σ_{j<D} pc_j (1/5)^j`. -/
theorem sval_approx (D : Nat) : sval.approx D = series pc xv D := rfl
/-- The cosine analogue. -/
theorem cval_approx (D : Nat) : cval.approx D = series qc xv D := rfl

end YMGap.Continuum.ArctanValueIdentity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ArctanValueIdentity.mulCancelLeftPos
#print axioms YMGap.Continuum.ArctanValueIdentity.sol_unique
#print axioms YMGap.Continuum.ArctanValueIdentity.series_eqv_of_coeff_eqv
#print axioms YMGap.Continuum.ArctanValueIdentity.equiv_of_approx_eqv
#print axioms YMGap.Continuum.ArctanValueIdentity.limCReal_equiv_of_coeff_eqv
#print axioms YMGap.Continuum.ArctanValueIdentity.legA_sine
#print axioms YMGap.Continuum.ArctanValueIdentity.legA_cosine
#print axioms YMGap.Continuum.ArctanValueIdentity.composedData
#print axioms YMGap.Continuum.ArctanValueIdentity.atom_of_tail
#print axioms YMGap.Continuum.ArctanValueIdentity.atom_of_valueIdentity
#print axioms YMGap.Continuum.ArctanValueIdentity.valueIdentity_of_atom
#print axioms YMGap.Continuum.ArctanValueIdentity.valueIdentity_of_tail
