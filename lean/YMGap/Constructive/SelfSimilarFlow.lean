/-
# The **general-`b`** CReal power law and the self-similar CReal flow

`CRealExp` (§6–§7) built the constructive exponential `expNegCD w d` (`e^{−w}` for a
`CReal` argument `w` with explicit modulus data `d`), the add-law lift
`expNegCD_add` (`e^{−a}·e^{−b} ≈ e^{−(a+b)}`), and the **`b = 1`** self-similar step
`self_similar_two : (e^{−s})² ≈ e^{−(s+s)}`.

This module generalises the exponent from the 2-fold sum `s + s` to the general
`n`-fold sum `scaleN n s = s + s + ⋯ + s` and lands:

  * **`scaleN`** — the `n`-fold CReal sum (`scaleN 0 = czero`,
    `scaleN (n+1) s = add (scaleN n s) s`);
  * **`addData`** — the generic two-summand modulus assembler (generalises
    `addSelfData`; modulus `ε ↦ max (Aᴹ(ε/2)) (Bᴹ(ε/2))`);
  * **`zeroData` / `scaleData`** — the recursively-assembled modulus data for
    `czero` and for `scaleN n s`;
  * **`expNegC_zero`** — `e^{−0} ≈ 1` (`expNegCD czero ≈ cone`);
  * **`expNegCD_powerLaw`** — the **general-`b` power law**
    `(e^{−s})ⁿ ≈ e^{−(n·s)}`, i.e. `cpow (expNegCD s d) n ≈ expNegCD (scaleN n s) …`;
  * **`expNegCD_pointwise_congr`** — `expNegC` respects a POINTWISE `.eqv` of
    exponents (the constructive continuity that the flow descent needs);
  * **`selfSimilarCReal`** — the **CReal self-similar flow law** for arbitrary `b`:
    given a `SelfSimilarTower b` (a CReal exponent tower `w` whose `(b+1)`-fold sum
    descends to the previous level, `scaleN (b+1) (w (k+1)) ≃ w k` pointwise), the
    separators `sep k = e^{−w k}` satisfy `sep k ≈ (sep (k+1))^(b+1)` for every `k` —
    a genuine `CReal` inhabitant of the flow law that the rational `polyFlow`
    provably FAILED (`CodynamicTransmutation.polyFlow_not_selfSimilar`).

# Honest scope

`selfSimilarCReal` is conditional on a `SelfSimilarTower` exactly as the rational
`marginInvariant` is conditional on `selfSimilar`.  The DIFFERENCE — the whole point
of the codynamic recast — is that no rational flow inhabits the law, whereas a
CReal tower is constructively inhabitable (the `(b+1)`-fold sum can be matched to
the previous exponent at every approximation index via exact rational division
`(b+1)·(q/(b+1)) ≃ q`).  Building a CONCRETE tower (the `(b+1)`-th-root exponent
family with its full modulus data) is the remaining construction; it is left as an
honest open construction (an inhabitant of the `Type`-level `SelfSimilarTower`
structure), NOT a `sorry` — every theorem here is fully green and axiom-clean.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the `CRealExp` backbone; moduli are `Type`-level data.  Each
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Constructive.CRealExp
import YMGap.Constructive.CRealAbs

namespace YMGap.Constructive

open YMGap.Constructive
open YMGap.Constructive.CReal

namespace CReal

/-! ## 1. The `n`-fold CReal sum `scaleN` -/

/-- The `n`-fold sum `scaleN n s = s + s + ⋯ + s` (`n` copies), built so that
`scaleN (n+1) s = add (scaleN n s) s` definitionally (top copy on the right). -/
def scaleN : Nat → CReal → CReal
  | 0, _ => CReal.czero
  | (n + 1), s => CReal.add (scaleN n s) s

@[simp] theorem scaleN_zero (s : CReal) : scaleN 0 s = CReal.czero := rfl

@[simp] theorem scaleN_succ (n : Nat) (s : CReal) :
    scaleN (n + 1) s = CReal.add (scaleN n s) s := rfl

/-! ## 2. The generic two-summand modulus assembler `addData` -/

/-- `(a + e) + (b + e) ≃ (a + b) + (e + e)` — the quadruple rearrangement used to
collect the two half-tolerances of `addData`'s Cauchy bound (generalises
`add_pair_rearrange`, which is the `a = b` case). -/
theorem add_quad_rearrange (a b e : Q') :
    ((a + e) + (b + e)).eqv ((a + b) + (e + e)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a e (b + e)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (e + (b + e)) ((b + e) + e)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv e b e))
      (Q'.add_eqv_congr_right _ _ e (Q'.add_comm_eqv e b)))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a ((b + e) + e) (b + (e + e))
    (Q'.add_assoc_eqv b e e)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv a b (e + e))

/-- **The generic two-summand `ExpNegCData` assembler.**  Given modulus data for
both summands `A`, `B` and the pointwise sub-unit bound `(A+B).approx ≤ 1`, produces
modulus data for `add A B`.  The Cauchy modulus is `ε ↦ max (Aᴹ(ε/2)) (Bᴹ(ε/2))`;
the Cauchy bound is the summed half-bounds rearranged by `add_quad_rearrange` +
`half_add_half`; antitonicity is the pointwise `max` of the two antitonicities.
(`addSelfData` is the special case `A = B` with the single-summand modulus.) -/
def addData (A B : CReal) (dA : ExpNegCData A) (dB : ExpNegCData B)
    (hbound : ∀ k, (CReal.add A B).approx k ≤ 1) : ExpNegCData (CReal.add A B) where
  Mw := fun ε => max (dA.Mw (ε * Q'.mkPos 1 2 (by decide)))
                     (dB.Mw (ε * Q'.mkPos 1 2 (by decide)))
  hpos := fun k => Q'.zero_le_add _ _ (dA.hpos k) (dB.hpos k)
  hle1 := hbound
  hMw := fun ε hε m n hm hn => by
    have hε2 : (0 : Q') < ε * Q'.mkPos 1 2 (by decide) := Q'.mul_pos hε (Q'.invSucc_pos 1)
    have hmA : dA.Mw (ε * Q'.mkPos 1 2 (by decide)) ≤ m := Nat.le_trans (Nat.le_max_left _ _) hm
    have hnA : dA.Mw (ε * Q'.mkPos 1 2 (by decide)) ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hmB : dB.Mw (ε * Q'.mkPos 1 2 (by decide)) ≤ m := Nat.le_trans (Nat.le_max_right _ _) hm
    have hnB : dB.Mw (ε * Q'.mkPos 1 2 (by decide)) ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    obtain ⟨hA1, hA2⟩ := dA.hMw (ε * Q'.mkPos 1 2 (by decide)) hε2 m n hmA hnA
    obtain ⟨hB1, hB2⟩ := dB.hMw (ε * Q'.mkPos 1 2 (by decide)) hε2 m n hmB hnB
    refine ⟨?_, ?_⟩
    · show A.approx m + B.approx m ≤ (A.approx n + B.approx n) + ε
      refine Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 hA1 hB1) (Q'.le_of_eqv ?_)
      exact Q'.eqv_trans _ _ _
        (add_quad_rearrange (A.approx n) (B.approx n) (ε * Q'.mkPos 1 2 (by decide)))
        (Q'.add_eqv_congr_left _ _ _ (CReal.half_add_half ε))
    · show A.approx n + B.approx n ≤ (A.approx m + B.approx m) + ε
      refine Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 hA2 hB2) (Q'.le_of_eqv ?_)
      exact Q'.eqv_trans _ _ _
        (add_quad_rearrange (A.approx m) (B.approx m) (ε * Q'.mkPos 1 2 (by decide)))
        (Q'.add_eqv_congr_left _ _ _ (CReal.half_add_half ε))
  hMwmono := fun ε δ hδ hδε => by
    have hδ2 : (0 : Q') < δ * Q'.mkPos 1 2 (by decide) := Q'.mul_pos hδ (Q'.invSucc_pos 1)
    have hle2 : δ * Q'.mkPos 1 2 (by decide) ≤ ε * Q'.mkPos 1 2 (by decide) :=
      Q'.mul_le_mul_of_nonneg_right δ ε _ hδε (Q'.le_of_lt (Q'.invSucc_pos 1))
    exact Nat.max_le.mpr
      ⟨Nat.le_trans (dA.hMwmono _ _ hδ2 hle2) (Nat.le_max_left _ _),
       Nat.le_trans (dB.hMwmono _ _ hδ2 hle2) (Nat.le_max_right _ _)⟩

/-! ## 3. `ExpNegCData` for `czero` and for `scaleN n s` -/

/-- Modulus data for the zero exponent `czero` (every approximation is `0`). -/
def zeroData : ExpNegCData CReal.czero where
  Mw := fun _ => 0
  hpos := fun _ => by show (0 : Q') ≤ (0 : Q'); exact Q'.le_refl' 0
  hle1 := fun _ => by show (0 : Q') ≤ (1 : Q'); decide
  hMw := fun ε hε _ _ _ _ => by
    refine ⟨?_, ?_⟩
    · show (0 : Q') ≤ (0 : Q') + ε
      exact Q'.zero_le_add 0 ε (Q'.le_refl' 0) (Q'.le_of_lt hε)
    · show (0 : Q') ≤ (0 : Q') + ε
      exact Q'.zero_le_add 0 ε (Q'.le_refl' 0) (Q'.le_of_lt hε)
  hMwmono := fun _ _ _ _ => Nat.le_refl 0

/-- From the `(n+1)`-fold sub-unit bound, the `n`-fold bound: `(scaleN n s).approx k
≤ (scaleN n s).approx k + s.approx k = (scaleN (n+1) s).approx k ≤ 1` (drops the
top nonnegative copy). -/
theorem scaleN_succ_bound_pred (s : CReal) (d : ExpNegCData s) (n : Nat)
    (hb : ∀ k, (scaleN (n + 1) s).approx k ≤ 1) :
    ∀ k, (scaleN n s).approx k ≤ 1 := fun k =>
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (d.hpos k)) (hb k)

/-- **Modulus data for `scaleN n s`**, recursively assembled from `s`'s data `d`
via `addData` (top copy each step), given the per-`n` sub-unit bound. -/
def scaleData (s : CReal) (d : ExpNegCData s) :
    (n : Nat) → (∀ k, (scaleN n s).approx k ≤ 1) → ExpNegCData (scaleN n s)
  | 0, _ => zeroData
  | (n + 1), hb =>
      addData (scaleN n s) s (scaleData s d n (scaleN_succ_bound_pred s d n hb)) d hb

/-! ## 4. `e^{−0} ≈ 1` -/

/-- `term 0 (k+1) ≃ 0` (the `(−0)` recurrence factor kills every term past the
leading `1`). -/
theorem term_zero_base_succ (k : Nat) : (ExpNeg.term (0 : Q') (k + 1)).eqv (0 : Q') := by
  rw [ExpNeg.term_succ]
  -- term 0 k · ((−0)·c) ≃ term 0 k · 0 ≃ 0
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (ExpNeg.term 0 k) _ 0 ?_) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 0 _ (by decide : ((-(0 : Q')).eqv 0))) ?_
    exact Q'.zero_mul_eqv _
  · refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (ExpNeg.term 0 k) 0) ?_
    exact Q'.zero_mul_eqv (ExpNeg.term 0 k)

/-- `partialSum 0 (n+1) ≃ 1` — the `e^{−0}` partial sums collapse to `1`. -/
theorem partialSum_zero_base : ∀ n, (ExpNeg.partialSum (0 : Q') (n + 1)).eqv (1 : Q')
  | 0 => by rw [ExpNeg.partialSum_one]; exact Q'.eqv_refl 1
  | (n + 1) => by
      rw [ExpNeg.partialSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ 0 (term_zero_base_succ n)) ?_
      refine Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _) ?_
      exact partialSum_zero_base n

/-- **`e^{−0} ≈ 1`** as a `CReal` `Equiv`: `expNeg 0 ≈ cone` (eventual equality from
`partialSum 0 (n+1) ≃ 1`). -/
theorem expNeg_zero_equiv_cone (h : (0 : Q') ≤ (0 : Q')) :
    CReal.Equiv (ExpNeg.expNeg (0 : Q') h) CReal.cone := by
  intro ε hε
  refine ⟨1, fun n hn => ?_⟩
  -- n ≥ 1 ⇒ n = m+1 ⇒ partialSum 0 n ≃ 1 = cone.approx n
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have heq : (ExpNeg.partialSum (0 : Q') (1 + m)).eqv (1 : Q') := by
    have e : 1 + m = m + 1 := by omega
    rw [e]; exact partialSum_zero_base m
  refine ⟨?_, ?_⟩
  · show ExpNeg.partialSum (0 : Q') (1 + m) ≤ (1 : Q') + ε
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) (Q'.add_le_self_of_nonneg 1 ε (Q'.le_of_lt hε))
  · show (1 : Q') ≤ ExpNeg.partialSum (0 : Q') (1 + m) + ε
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm heq))
      (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))

/-- **`expNegCD czero d0 ≈ cone`** — `e^{−0} = 1` lifted through the completion.
The defining sequence is the constant `expNeg 0`, each term `≈ cone`; the constant
`cone` sequence converges to `cone` (`convergesTo_self`), so the limits agree. -/
theorem expNegC_zero (d0 : ExpNegCData CReal.czero) :
    CReal.Equiv (expNegCD CReal.czero d0) CReal.cone :=
  Equiv_of_limit_of_equal
    (fun k => expNeg_zero_equiv_cone (d0.hpos k))
    (expNegCD_converges CReal.czero d0)
    (convergesTo_self CReal.cone)

/-! ## 5. The general-`b` power law `(e^{−s})ⁿ ≈ e^{−(n·s)}` -/

/-- **THE GENERAL-`b` POWER LAW.**  For every `n` with the `n`-fold sub-unit bound,
the `n`-th CReal power of `e^{−s}` equals `e^{−(n·s)}`:

    cpow (expNegCD s d) n ≈ expNegCD (scaleN n s) (scaleData s d n hb).

Induction on `n`: the base is `e^{−0} = 1` (`expNegC_zero`); the step composes the
inductive hypothesis through `mul_congr_left` with one application of the add-law
`expNegCD_add` (peeling the top copy `scaleN (n+1) s = add (scaleN n s) s`).  This
is the general-`b` generalisation of `self_similar_two` (which is `n = b+1 = 2`). -/
theorem expNegCD_powerLaw (s : CReal) (d : ExpNegCData s) :
    ∀ (n : Nat) (hb : ∀ k, (scaleN n s).approx k ≤ 1),
      CReal.Equiv (cpow (expNegCD s d) n) (expNegCD (scaleN n s) (scaleData s d n hb))
  | 0, _ => (expNegC_zero zeroData).symm
  | (n + 1), hb =>
      have hb' := scaleN_succ_bound_pred s d n hb
      Equiv.trans (mul_congr_left (expNegCD_powerLaw s d n hb'))
        (expNegCD_add (scaleN n s) s (scaleData s d n hb') d (scaleData s d (n + 1) hb))

/-! ## 6. Pointwise congruence of `expNegC` (constructive continuity) -/

/-- **`expNegC` respects a POINTWISE `.eqv` of exponents.**  If `v.approx j ≃
v'.approx j` for every `j`, then `e^{−v} ≈ e^{−v'}`.  The two defining sequences are
termwise `Equiv` (`expNeg_eqv_congr`), and each converges to its `expNegCD`, so the
limits agree (`Equiv_of_limit_of_equal`).  This is the constructive continuity the
self-similar descent consumes (a pointwise — not merely asymptotic — hypothesis,
which is exactly what the exact rational-division tower supplies). -/
theorem expNegCD_pointwise_congr (v v' : CReal) (dv : ExpNegCData v) (dv' : ExpNegCData v')
    (h : ∀ j, (v.approx j).eqv (v'.approx j)) :
    CReal.Equiv (expNegCD v dv) (expNegCD v' dv') :=
  Equiv_of_limit_of_equal
    (fun j => expNeg_eqv_congr (dv.hpos j) (dv'.hpos j) (h j))
    (expNegCD_converges v dv)
    (expNegCD_converges v' dv')

/-! ## 7. The CReal self-similar flow law (arbitrary `b`) -/

/-- **A self-similar CReal exponent tower** (block factor `b`).  `w k` is the
exponent at scale `k`; `dw k` its modulus data; `bnd k` the `(b+1)`-fold sub-unit
bound at level `k+1`; and `div k` the descent: the `(b+1)`-fold sum of the finer
exponent `w (k+1)` agrees with the coarser exponent `w k` at every approximation
index (`scaleN (b+1) (w (k+1)) ≃ w k` pointwise — the exact rational-division
relation `(b+1)·(w_k/(b+1)) ≃ w_k`).  This is the `CReal` carrier of the
`(b+1)`-th-root flow that the rational `polyFlow` could not inhabit. -/
structure SelfSimilarTower (b : Nat) : Type where
  w : Nat → CReal
  dw : ∀ k, ExpNegCData (w k)
  bnd : ∀ k j, (scaleN (b + 1) (w (k + 1))).approx j ≤ 1
  div : ∀ k j, ((scaleN (b + 1) (w (k + 1))).approx j).eqv ((w k).approx j)

/-- The separator flow `sep k = e^{−w k}` of a tower. -/
def sep {b : Nat} (T : SelfSimilarTower b) (k : Nat) : CReal :=
  expNegCD (T.w k) (T.dw k)

/-- **THE CReal SELF-SIMILAR FLOW LAW (arbitrary `b`).**  For a `SelfSimilarTower b`,
the separators satisfy `sep k ≈ (sep (k+1))^(b+1)` at every scale — a genuine
`CReal` inhabitant of the codynamic flow law.  Proof: the power law sends
`(sep (k+1))^(b+1)` to `e^{−(b+1)·w(k+1)}`, and the descent `div k` (through
`expNegCD_pointwise_congr`) identifies that with `e^{−w k} = sep k`.

This is the constructive resolution of `CodynamicTransmutation.selfSimilar`: the
rational `polyFlow` provably FAILS the law (`polyFlow_not_selfSimilar`), but the
`CReal` flow `sep` SATISFIES it — the obstruction (`(b+1)`-th roots are irrational)
dissolves once the exponent tower is constructive. -/
theorem selfSimilarCReal {b : Nat} (T : SelfSimilarTower b) (k : Nat) :
    CReal.Equiv (sep T k) (cpow (sep T (k + 1)) (b + 1)) := by
  have hpow : CReal.Equiv (cpow (sep T (k + 1)) (b + 1))
      (expNegCD (scaleN (b + 1) (T.w (k + 1)))
        (scaleData (T.w (k + 1)) (T.dw (k + 1)) (b + 1) (T.bnd k))) :=
    expNegCD_powerLaw (T.w (k + 1)) (T.dw (k + 1)) (b + 1) (T.bnd k)
  have hcongr : CReal.Equiv
      (expNegCD (scaleN (b + 1) (T.w (k + 1)))
        (scaleData (T.w (k + 1)) (T.dw (k + 1)) (b + 1) (T.bnd k)))
      (sep T k) :=
    expNegCD_pointwise_congr (scaleN (b + 1) (T.w (k + 1))) (T.w k)
      (scaleData (T.w (k + 1)) (T.dw (k + 1)) (b + 1) (T.bnd k)) (T.dw k) (T.div k)
  exact (Equiv.trans hpow hcongr).symm

/-! ## 8. A CONCRETE inhabitant of `SelfSimilarTower b`

The conditional flow law `selfSimilarCReal` is discharged below by exhibiting a
closed, unconditional tower for every `b`.  The construction is the exact
rational-division `(b+1)`-th-root flow:

  * exponents `w 0 = 1/2` (a rational seed in `[0,1]`), `w (k+1) = (1/(b+1))·w k`;
  * each separator `sep k = e^{−w k}` is a genuine **irrational** CReal
    (`expNegCD` of a positive exponent), and the flow `sep k ≈ (sep (k+1))^(b+1)`
    is a non-trivial identity among irrational reals — precisely the law the
    rational `polyFlow` of the separators could not inhabit.

The exponent seed is taken rational because the natural Cauchy modulus `Mexp` of
the irrational seed `e^{−1}` is **not antitone** over the unreduced `Q'`
representation (so it does not directly satisfy the `ExpNegCData.hMwmono` field);
a rational seed makes the modulus trivially antitone while keeping every separator
irrational.  Two reusable assemblers do the work:

  * **`ofQ'Data`** — `ExpNegCData` for a constant rational exponent `q ∈ [0,1]`
    (trivial modulus `0`);
  * **`scaleQData`** — scales any `ExpNegCData u` by a sub-unit rational `c`
    (`0 ≤ c ≤ 1`), producing `ExpNegCData (c·u)` with the SAME modulus (since a
    sub-unit scaling contracts differences: `c·|a−b| ≤ |a−b|`). -/

/-- **`scaleN n u ≃ n · u` pointwise** — the `n`-fold CReal sum is, at every
approximation index, the rational scalar `ofNat n` times `u`. -/
theorem scaleN_approx (n : Nat) (u : CReal) (j : Nat) :
    ((scaleN n u).approx j).eqv (Q'.ofNat n * u.approx j) := by
  induction n with
  | zero =>
      show ((0 : Q')).eqv (Q'.ofNat 0 * u.approx j)
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 (u.approx j) (by decide))
        (Q'.zero_mul_eqv (u.approx j)))
  | succ n ih =>
      show (((scaleN n u).approx j) + u.approx j).eqv (Q'.ofNat (n + 1) * u.approx j)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (u.approx j) ih) ?_
      have hstep : (Q'.ofNat n * u.approx j + u.approx j).eqv
          ((Q'.ofNat n + 1) * u.approx j) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv (u.approx j)))) ?_
        exact Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat n) 1 (u.approx j))
      refine Q'.eqv_trans _ _ _ hstep ?_
      exact Q'.mul_eqv_congr_right (Q'.ofNat n + 1) (Q'.ofNat (n + 1)) (u.approx j)
        (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (Q'.ofNat n) 1) (ExpNeg.one_add_ofNat n))

/-- **`ExpNegCData` for a constant rational exponent** `q` with `0 ≤ q ≤ 1`.  The
sequence is constant (`(ofQ' q).approx k = q`), so the Cauchy modulus is `0`. -/
def ofQ'Data (q : Q') (h0 : (0 : Q') ≤ q) (h1 : q ≤ 1) :
    ExpNegCData (CReal.ofQ' q) where
  Mw := fun _ => 0
  hpos := fun _ => by show (0 : Q') ≤ q; exact h0
  hle1 := fun _ => by show q ≤ 1; exact h1
  hMw := fun ε hε _ _ _ _ => by
    refine ⟨?_, ?_⟩
    · show q ≤ q + ε; exact Q'.add_le_self_of_nonneg q ε (Q'.le_of_lt hε)
    · show q ≤ q + ε; exact Q'.add_le_self_of_nonneg q ε (Q'.le_of_lt hε)
  hMwmono := fun _ _ _ _ => Nat.le_refl 0

/-- **Sub-unit rational scaling of `ExpNegCData`.**  For `0 ≤ c ≤ 1`, scales
`ExpNegCData u` to `ExpNegCData (c·u)` keeping the SAME Cauchy modulus: from
`u_m ≤ u_n + ε` we get `c·u_m ≤ c·u_n + c·ε ≤ c·u_n + ε` (the sub-unit factor
`c ≤ 1` contracts the tolerance, so no modulus inflation is needed). -/
def scaleQData (c : Q') (hc0 : (0 : Q') ≤ c) (hc1 : c ≤ 1)
    (u : CReal) (du : ExpNegCData u) :
    ExpNegCData (CReal.mul (CReal.ofQ' c) u) where
  Mw := du.Mw
  hpos := fun k => by
    show (0 : Q') ≤ c * u.approx k
    exact Q'.mul_nonneg c (u.approx k) hc0 (du.hpos k)
  hle1 := fun k => by
    show c * u.approx k ≤ 1
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left (u.approx k) 1 c (du.hle1 k) hc0) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv c)) hc1
  hMw := fun ε hε m n hm hn => by
    obtain ⟨h1, h2⟩ := du.hMw ε hε m n hm hn
    have hcε : c * ε ≤ ε :=
      Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right c 1 ε hc1 (Q'.le_of_lt hε))
        (Q'.le_of_eqv (Q'.one_mul_eqv ε))
    have key : ∀ a d : Q', a ≤ d + ε → c * a ≤ c * d + ε := by
      intro a d had
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left a (d + ε) c had hc0) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv c d ε)) ?_
      exact Q'.add_le_add_left (c * d) (c * ε) ε hcε
    exact ⟨by show c * u.approx m ≤ c * u.approx n + ε; exact key _ _ h1,
           by show c * u.approx n ≤ c * u.approx m + ε; exact key _ _ h2⟩
  hMwmono := du.hMwmono

/-- `1/(b+1) ≤ 1` (the per-level contraction factor is sub-unit). -/
theorem invSucc_le_one (b : Nat) : Q'.invSucc b ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le (Nat.zero_le b))
    (by decide : Q'.invSucc 0 ≤ (1 : Q'))

/-- The concrete exponent tower: `w 0 = 1/2`, `w (k+1) = (1/(b+1))·w k`. -/
def wTower (b : Nat) : Nat → CReal
  | 0 => CReal.ofQ' (Q'.invSucc 1)
  | (k + 1) => CReal.mul (CReal.ofQ' (Q'.invSucc b)) (wTower b k)

/-- The modulus data for every level of `wTower` (base = `ofQ'Data`, descent =
`scaleQData` with `c = 1/(b+1)`). -/
def dwTower (b : Nat) : (k : Nat) → ExpNegCData (wTower b k)
  | 0 => ofQ'Data (Q'.invSucc 1) (by decide) (by decide)
  | (k + 1) =>
      scaleQData (Q'.invSucc b) (Q'.invSucc_nonneg b) (invSucc_le_one b)
        (wTower b k) (dwTower b k)

/-- **The exact `(b+1)`-fold descent.**  `scaleN (b+1) (w (k+1)) ≃ w k` pointwise:
the `(b+1)`-fold sum of `(1/(b+1))·w k` is `((b+1)·(1/(b+1)))·w k ≃ 1·w k ≃ w k`,
the constructive `(b+1)`-th-root identity (`ofNat (b+1) · invSucc b ≃ 1`). -/
theorem wTower_descent (b k j : Nat) :
    ((scaleN (b + 1) (wTower b (k + 1))).approx j).eqv ((wTower b k).approx j) := by
  refine Q'.eqv_trans _ _ _ (scaleN_approx (b + 1) (wTower b (k + 1)) j) ?_
  show (Q'.ofNat (b + 1) * (Q'.invSucc b * (wTower b k).approx j)).eqv
    ((wTower b k).approx j)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (b + 1)) (Q'.invSucc b)
      ((wTower b k).approx j))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat (b + 1) * Q'.invSucc b) 1
      ((wTower b k).approx j) (Q'.ofNat_succ_mul_invSucc b)) ?_
  exact Q'.one_mul_eqv ((wTower b k).approx j)

/-- The `(b+1)`-fold sub-unit bound at every level (via the descent + `hle1`). -/
theorem wTower_bnd (b k j : Nat) :
    (scaleN (b + 1) (wTower b (k + 1))).approx j ≤ 1 :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (wTower_descent b k j)) ((dwTower b k).hle1 j)

/-- **THE CONCRETE TOWER.**  A closed, unconditional inhabitant of
`SelfSimilarTower b` for every `b` — the exact rational-division `(b+1)`-th-root
flow with irrational separators `e^{−w k}`. -/
def concreteTower (b : Nat) : SelfSimilarTower b where
  w := wTower b
  dw := dwTower b
  bnd := wTower_bnd b
  div := wTower_descent b

/-- **THE CLOSED, UNCONDITIONAL SELF-SIMILAR CReal FLOW.**  For every `b` and every
scale `k`, the concrete separators satisfy `sep k ≈ (sep (k+1))^(b+1)` — the
codynamic flow law discharged with NO open hypothesis.  This inhabits the law the
rational `polyFlow` provably fails (`CodynamicTransmutation.polyFlow_not_selfSimilar`):
the separators `sep (concreteTower b) k = e^{−w k}` are genuine irrational CReals,
and the `(b+1)`-th-root descent is exact at every approximation index. -/
theorem concreteSelfSimilarFlow (b k : Nat) :
    CReal.Equiv (sep (concreteTower b) k)
      (cpow (sep (concreteTower b) (k + 1)) (b + 1)) :=
  selfSimilarCReal (concreteTower b) k

end CReal

end YMGap.Constructive

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.add_quad_rearrange
#print axioms YMGap.Constructive.CReal.addData
#print axioms YMGap.Constructive.CReal.zeroData
#print axioms YMGap.Constructive.CReal.scaleData
#print axioms YMGap.Constructive.CReal.expNeg_zero_equiv_cone
#print axioms YMGap.Constructive.CReal.expNegC_zero
#print axioms YMGap.Constructive.CReal.expNegCD_powerLaw
#print axioms YMGap.Constructive.CReal.expNegCD_pointwise_congr
#print axioms YMGap.Constructive.CReal.selfSimilarCReal
#print axioms YMGap.Constructive.CReal.scaleN_approx
#print axioms YMGap.Constructive.CReal.ofQ'Data
#print axioms YMGap.Constructive.CReal.scaleQData
#print axioms YMGap.Constructive.CReal.wTower_descent
#print axioms YMGap.Constructive.CReal.wTower_bnd
#print axioms YMGap.Constructive.CReal.concreteTower
#print axioms YMGap.Constructive.CReal.concreteSelfSimilarFlow
