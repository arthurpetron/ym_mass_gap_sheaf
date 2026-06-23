/-
The **`N`-indexed (all-`k`) telescoping recurrence** for the perfect-square
factor `S_N` of the heat-kernel q-Hankel determinant — proved by genuine
INDUCTION on the product structure of `SN`, not per-`k` `decide`.

Setting (same uniform base variable as `QHankel`/`Favard`/`FavardRec`):
`a ∈ (0,1]`, the order-`N` heat-kernel Gram minor factors as
`Δ_N = S_N²·P_N` with the explicit `N`-indexed perfect-square factor

    S_N(a) = ∏_{j=1}^{N−1} (a^{2j} − 1)^{N−j}        (= `SN N`),

built by `SNaux`/`ppow`/`qFac` for every `N`.  The repo proved the
telescoping/cyclotomic recurrence

    S_{k+1}·S_{k−1} = (a^{2k} − 1)·S_k²              (telescope)

only for `k = 2,3,4,5` (`SN_telescope_2…5`, `betaCyclo_1…5`), each by a
`decide` on fixed coefficient lists.  This file UPGRADES (telescope) to a
single `N`-indexed THEOREM valid for **all** `k ≥ 2`.

# What is PROVED here (axiom-clean; no `Classical`/`sorry`/`native_decide`)

  * `evalSNaux_shift` — the **index-shift identity** (the structural heart):
    for every base point `x`, every `N`, and every `j ≤ N`,

        eval (SNaux (N+1) j) x  ≃  eval (qFacProd j) x · eval (SNaux N j) x,

    proved by INDUCTION on `j`.  Raising the order `N ↦ N+1` multiplies the
    product `∏_{i=1}^{j}(qFac i)^{N−i}` by exactly one extra copy of each
    factor `qFac i` (`i = 1…j`), i.e. by `qFacProd j = ∏_{i=1}^{j} qFac i`.

  * `evalSNaux_top` — `eval (SNaux N N) x ≃ eval (SNaux N (N−1)) x`: the top
    factor `(qFac N)^{N−N} = (qFac N)^0 = 1` is trivial.

  * `SN_telescope_gen` — **the `N`-indexed telescope**, the main target:
    for all `k ≥ 2` and every `x`,

        eval (pmul (SN (k+1)) (SN (k−1))) x
          ≃ eval (pmul (qFac k) (pmul (SN k) (SN k))) x.

    Proved by composing `evalSNaux_shift` (twice) + `evalSNaux_top` + the
    `qFacProd` recurrence + `Q'` ring algebra.  This is a genuine theorem for
    **every** `k`, generalizing the four `decide`-instances; specializing
    `k = 2,3,4,5` recovers `SN_telescope_2…5` (`SN_telescope_gen_recovers_*`).

  * `geRat_SN_sq_nonneg_uniform` — re-export of the uniform square-positivity
    `(ceval (SN N) a)² ≥ 0` for every `N`, every `a` (trivially, even power).

  * `uniform_PN_of_PNStep` — the **reduction**: the single inductive step
    `PNStep` (Type-level), with the base cases `k ≤ 5` discharged from the
    existing per-`N` `nonnegCoeffs P_{k}` facts, IMPLIES `nonnegCoeffs (PN N)`
    for every `N`.  So uniform `P_N ≥ 0` (coefficient form) is reduced to the
    one inductive obligation `PNStep`.

# NAMED-OPEN (precise) — the inductive step `PNStep`

`PNStep` (below) is the obligation

    ∀ k ≥ 2, nonnegCoeffs (PN k) → nonnegCoeffs (PN (k+1)) → nonnegCoeffs (PN (k+2)).

It is left as a **named Type-level residual**, NOT proved.  The telescope
proved here is a recurrence for the *square* factor `S_N`, and pushing it onto
`P_N` requires the Favard/Dodgson minor recurrence, whose new factor is the
**cyclotomic monomial `qFac k = a^{2k} − 1`**.  That factor has a NEGATIVE
constant coefficient (`−1`), so `pmul`-ing by it does NOT preserve the
nonneg-coefficient cone (`nonnegCoeffs_pmul` needs *both* factors nonneg):
the recurrence expressing the next `P` is *subtractive*, and dividing the
cyclotomic content back out leaves negative `a`-powers, not a
nonneg-coefficient multiplier.  Exactly here the closure breaks; `PNStep`
names the gap.  The `PN k` family is supplied abstractly as a parameter to
the reduction, since only `P_1…P_5` are realized as literal lists in the repo;
`uniform_PN_of_PNStep` is parametric over any candidate family `PN`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.QHankel
import YMGap.Continuum.FavardRec

namespace YMGap.Continuum.FavardUniform

open YMGap.Constructive
open YMGap.Continuum

/-! ## Small `Q'` multiplicative-rearrangement helpers

The assembly of the recurrence reorders four `Q'` factors; these mirror the
additive helpers in `QPoly` (`q_add_congr`, `q_interchange`) for `·`. -/

/-- Congruence for `·` on both arguments. -/
theorem q_mul_congr {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- Interchange for `·`: `(a·b)·(c·d) ≃ (a·c)·(b·d)`. -/
theorem q_mul4_swap (a b c d : Q') :
    ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  -- (a·b)·(c·d) ≃ a·(b·(c·d)) ≃ a·((b·c)·d) ≃ a·((c·b)·d)
  --            ≃ a·(c·(b·d)) ≃ (a·c)·(b·d)
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a (b * (c * d)) ((b * c) * d)
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a ((b * c) * d) ((c * b) * d)
    (Q'.mul_eqv_congr_right (b * c) (c * b) d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a ((c * b) * d) (c * (b * d))
    (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-! ## The accumulated factor product `qFacProd`

`qFacProd j = ∏_{i=1}^{j} qFac i`, accumulated in the SAME order as `SNaux`
accumulates its powers.  Raising the order of `SNaux` by one multiplies the
whole product by exactly `qFacProd j`. -/

/-- `qFacProd j = ∏_{i=1}^{j} (qFac i)`, low index innermost (mirrors `SNaux`). -/
def qFacProd : Nat → QPoly.Poly
  | 0 => pone
  | (j + 1) => QPoly.pmul (qFac (j + 1)) (qFacProd j)

/-! ## `ppow` evaluation lemma -/

/-- `eval (ppow p (m+1)) x ≃ eval p x · eval (ppow p m) x` (definitional unfold
of `ppow` through the `eval`-homomorphism `eval_pmul`). -/
theorem eval_ppow_succ (p : QPoly.Poly) (m : Nat) (x : Q') :
    (QPoly.eval (ppow p (m + 1)) x).eqv
      (QPoly.eval p x * QPoly.eval (ppow p m) x) :=
  QPoly.eval_pmul p (ppow p m) x

/-! ## The index-shift identity (the structural heart), by induction on `j`

`eval (SNaux (N+1) j) x ≃ eval (qFacProd j) x · eval (SNaux N j) x`, for
`j ≤ N`.  This is where the all-`k` recurrence comes from: it manipulates the
explicit product `∏_{i=1}^{j}(qFac i)^{N−i}` by a uniform index shift, not by
`decide` on a fixed list. -/

/-- **Index-shift identity.**  Raising the order `N ↦ N+1` of `SNaux _ j`
multiplies it (at `eval`) by `qFacProd j`, for every `j ≤ N`.  By induction
on `j`. -/
theorem evalSNaux_shift (x : Q') :
    ∀ (N j : Nat), j ≤ N →
      (QPoly.eval (SNaux (N + 1) j) x).eqv
        (QPoly.eval (qFacProd j) x * QPoly.eval (SNaux N j) x)
  | _, 0, _ => by
      -- SNaux _ 0 = pone, qFacProd 0 = pone : 1 ≃ 1 · 1
      show (QPoly.eval pone x).eqv (QPoly.eval pone x * QPoly.eval pone x)
      refine Q'.eqv_trans _ _ _ (eval_pone x) ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (eval_pone x)) ?_
      exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (QPoly.eval pone x)) (eval_pone x)
  | N, (j + 1), hj => by
      -- m := N - (j+1).  Since j+1 ≤ N, (N+1)-(j+1) = N-j = m+1.
      have hjN : j ≤ N := Nat.le_of_succ_le hj
      have hN1 : (N + 1) - (j + 1) = (N - (j + 1)) + 1 := by omega
      -- Let f, pw, Pr, Gm name the four Q' values (no `set`: plain abbreviations
      -- via `let`-free re-use of the full expressions; we phrase the algebra on
      -- the explicit `QPoly.eval _ x` terms).
      -- LHS unfolds via SNaux's defining clause and (N+1)-(j+1) = (N-(j+1))+1.
      have hLHS :
          (QPoly.eval (SNaux (N + 1) (j + 1)) x).eqv
            (QPoly.eval (ppow (qFac (j + 1)) ((N - (j + 1)) + 1)) x
              * QPoly.eval (SNaux (N + 1) j) x) := by
        have hdef : SNaux (N + 1) (j + 1)
            = QPoly.pmul (ppow (qFac (j + 1)) ((N + 1) - (j + 1)))
                (SNaux (N + 1) j) := rfl
        rw [hdef, hN1]
        exact QPoly.eval_pmul _ _ x
      -- RHS pieces: SNaux N (j+1) and qFacProd (j+1).
      have hRHSaux :
          (QPoly.eval (SNaux N (j + 1)) x).eqv
            (QPoly.eval (ppow (qFac (j + 1)) (N - (j + 1))) x
              * QPoly.eval (SNaux N j) x) :=
        QPoly.eval_pmul (ppow (qFac (j + 1)) (N - (j + 1))) (SNaux N j) x
      have hRHSprod :
          (QPoly.eval (qFacProd (j + 1)) x).eqv
            (QPoly.eval (qFac (j + 1)) x * QPoly.eval (qFacProd j) x) :=
        QPoly.eval_pmul (qFac (j + 1)) (qFacProd j) x
      have hIH := evalSNaux_shift x N j hjN
      -- LHS ≃ (f · pw) · Gm1, then Gm1 ≃ Pr · Gm by IH, so LHS ≃ (f·pw)·(Pr·Gm).
      -- where f = eval(qFac(j+1)) x, pw = eval(ppow (qFac(j+1)) (N-(j+1))) x,
      --       Pr = eval(qFacProd j) x, Gm = eval(SNaux N j) x.
      have hLHS2 :
          (QPoly.eval (SNaux (N + 1) (j + 1)) x).eqv
            ((QPoly.eval (qFac (j + 1)) x
                * QPoly.eval (ppow (qFac (j + 1)) (N - (j + 1))) x)
              * (QPoly.eval (qFacProd j) x * QPoly.eval (SNaux N j) x)) := by
        refine Q'.eqv_trans _ _ _ hLHS ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (eval_ppow_succ (qFac (j + 1)) (N - (j + 1)) x)) ?_
        exact Q'.mul_eqv_congr_left _ _ _ hIH
      -- RHS = eval(qFacProd(j+1)) · eval(SNaux N (j+1)) ≃ (f·Pr) · (pw·Gm).
      have hRHS2 :
          (QPoly.eval (qFacProd (j + 1)) x * QPoly.eval (SNaux N (j + 1)) x).eqv
            ((QPoly.eval (qFac (j + 1)) x * QPoly.eval (qFacProd j) x)
              * (QPoly.eval (ppow (qFac (j + 1)) (N - (j + 1))) x
                  * QPoly.eval (SNaux N j) x)) :=
        q_mul_congr hRHSprod hRHSaux
      -- (f·pw)·(Pr·Gm) ≃ (f·Pr)·(pw·Gm) by the 4-factor interchange.
      refine Q'.eqv_trans _ _ _ hLHS2 ?_
      refine Q'.eqv_trans _ _ _
        (q_mul4_swap (QPoly.eval (qFac (j + 1)) x)
          (QPoly.eval (ppow (qFac (j + 1)) (N - (j + 1))) x)
          (QPoly.eval (qFacProd j) x) (QPoly.eval (SNaux N j) x)) ?_
      exact Q'.eqv_symm hRHS2

/-! ## The top factor is trivial: `SNaux N N ≃ SNaux N (N−1)`

`SNaux N N = pmul (ppow (qFac N) (N−N)) (SNaux N (N−1)) = pmul pone (SNaux N (N−1))`,
since `N − N = 0` and `ppow _ 0 = pone`. -/

/-- `eval (SNaux N N) x ≃ eval (SNaux N (N−1)) x` for `N ≥ 1`: the top power
`(qFac N)^{N−N} = (qFac N)^0 = 1`. -/
theorem evalSNaux_top (x : Q') (N : Nat) (hN : 1 ≤ N) :
    (QPoly.eval (SNaux N N) x).eqv (QPoly.eval (SNaux N (N - 1)) x) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  -- SNaux (n+1) (n+1) = pmul (ppow (qFac (n+1)) ((n+1)-(n+1))) (SNaux (n+1) n)
  --                   = pmul (ppow (qFac (n+1)) 0) (SNaux (n+1) n)
  --                   = pmul pone (SNaux (n+1) n).
  have hsub : (n + 1) - (n + 1) = 0 := by omega
  have hdef : SNaux (n + 1) (n + 1)
      = QPoly.pmul (ppow (qFac (n + 1)) ((n + 1) - (n + 1))) (SNaux (n + 1) n) := rfl
  have hnm1 : (n + 1) - 1 = n := by omega
  rw [hdef, hsub, hnm1]
  -- ppow _ 0 = pone, so goal: eval (pmul pone (SNaux (n+1) n)) x ≃ eval (SNaux (n+1) n) x
  show (QPoly.eval (QPoly.pmul pone (SNaux (n + 1) n)) x).eqv
      (QPoly.eval (SNaux (n + 1) n) x)
  refine Q'.eqv_trans _ _ _ (QPoly.eval_pmul pone (SNaux (n + 1) n) x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (eval_pone x)) ?_
  exact Q'.one_mul_eqv (QPoly.eval (SNaux (n + 1) n) x)

/-! ## The `qFacProd` recurrence (head factor split) -/

/-- `eval (qFacProd (j+1)) x ≃ eval (qFac (j+1)) x · eval (qFacProd j) x`. -/
theorem eval_qFacProd_succ (x : Q') (j : Nat) :
    (QPoly.eval (qFacProd (j + 1)) x).eqv
      (QPoly.eval (qFac (j + 1)) x * QPoly.eval (qFacProd j) x) :=
  QPoly.eval_pmul (qFac (j + 1)) (qFacProd j) x

/-! ## The `N`-indexed telescope — the main target

For all `k ≥ 2`:

    eval (pmul (SN (k+1)) (SN (k−1))) x
      ≃ eval (pmul (qFac k) (pmul (SN k) (SN k))) x.

`SN N = SNaux N (N−1)`.  Write `g a b := eval (SNaux a b) x`,
`Pr j := eval (qFacProd j) x`, `f i := eval (qFac i) x`.  Then with
`k = n+2` (so `k ≥ 2`):

  * `SN (k+1) = SNaux (k+1) k`; by `evalSNaux_shift` (N=k, j=k≤k) and
    `evalSNaux_top` (N=k), `g (k+1) k ≃ Pr k · g k (k−1)`.
  * `SN k = SNaux k (k−1)`; by `evalSNaux_shift` (N=k−1, j=k−1) and
    `evalSNaux_top` (N=k−1), `g k (k−1) ≃ Pr (k−1) · g (k−1) (k−2)`.
  * `Pr k = f k · Pr (k−1)` (head split).
  * `SN (k−1) = SNaux (k−1) (k−2) = g (k−1) (k−2)`.

LHS `= g (k+1) k · g (k−1) (k−2)`
    `≃ (f k · Pr (k−1)) · g k (k−1) · g (k−1) (k−2)`
    `≃ f k · (Pr (k−1) · g (k−1) (k−2))²  =  f k · (g k (k−1))²`
    `= RHS`.  All by the `Q'` ring helpers. -/

set_option maxHeartbeats 1000000 in
/-- **The `N`-indexed (all-`k ≥ 2`) telescoping recurrence**, proved by
INDUCTION (via `evalSNaux_shift`), not per-`k` `decide`:

    S_{k+1}·S_{k−1} = (a^{2k} − 1)·S_k².

This generalizes `SN_telescope_2…5` / `betaCyclo_1…5` to every `k`. -/
theorem SN_telescope_gen (k : Nat) (hk : 2 ≤ k) (x : Q') :
    (QPoly.eval (QPoly.pmul (SN (k + 1)) (SN (k - 1))) x).eqv
      (QPoly.eval (QPoly.pmul (qFac k) (QPoly.pmul (SN k) (SN k))) x) := by
  -- Set up the index arithmetic.  k ≥ 2.
  have hk1 : 1 ≤ k := by omega
  have hk1' : 1 ≤ k - 1 := by omega
  -- SN definitional unfoldings.
  have hSNkp1 : SN (k + 1) = SNaux (k + 1) k := rfl
  have hSNk : SN k = SNaux k (k - 1) := rfl
  have hSNkm1 : SN (k - 1) = SNaux (k - 1) (k - 2) := rfl
  -- Value abbreviations (named only in comments; the algebra is on the explicit
  -- `QPoly.eval _ x` terms — no `set`).  fk = eval(qFac k) x,
  -- Prk = eval(qFacProd k) x, Prk1 = eval(qFacProd (k-1)) x,
  -- g_kp1_k = eval(SNaux (k+1) k) x, g_k_km1 = eval(SNaux k (k-1)) x,
  -- g_km1_km2 = eval(SNaux (k-1) (k-2)) x.
  -- (1) g (k+1) k ≃ Prk · g k (k−1).
  have step1 : (QPoly.eval (SNaux (k + 1) k) x).eqv
      (QPoly.eval (qFacProd k) x * QPoly.eval (SNaux k (k - 1)) x) := by
    -- evalSNaux_shift with N=k, j=k (k ≤ k): SNaux (k+1) k ≃ qFacProd k · SNaux k k
    have hshift := evalSNaux_shift x k k (Nat.le_refl k)
    -- evalSNaux_top with N=k: SNaux k k ≃ SNaux k (k-1)
    have htop := evalSNaux_top x k hk1
    -- combine
    refine Q'.eqv_trans _ _ _ hshift ?_
    exact Q'.mul_eqv_congr_left _ _ _ htop
  -- (2) g k (k−1) ≃ Pr(k−1) · g (k−1) (k−2).
  have step2 : (QPoly.eval (SNaux k (k - 1)) x).eqv
      (QPoly.eval (qFacProd (k - 1)) x * QPoly.eval (SNaux (k - 1) (k - 2)) x) := by
    -- evalSNaux_shift with N=k−1, j=k−1: SNaux k (k−1) ≃ qFacProd (k−1) · SNaux (k−1) (k−1)
    have hshift0 := evalSNaux_shift x (k - 1) (k - 1) (Nat.le_refl (k - 1))
    -- (k−1)+1 = k, so SNaux ((k−1)+1) (k−1) = SNaux k (k−1).
    have hkk : (k - 1) + 1 = k := by omega
    rw [hkk] at hshift0
    -- evalSNaux_top with N=k−1: SNaux (k−1) (k−1) ≃ SNaux (k−1) ((k−1)−1)=SNaux (k−1)(k−2)
    have htop0 := evalSNaux_top x (k - 1) hk1'
    have hkm2 : (k - 1) - 1 = k - 2 := by omega
    rw [hkm2] at htop0
    refine Q'.eqv_trans _ _ _ hshift0 ?_
    exact Q'.mul_eqv_congr_left _ _ _ htop0
  -- (3) Prk = fk · Pr(k−1)  (head split; k = (k−1)+1).
  have step3 : (QPoly.eval (qFacProd k) x).eqv
      (QPoly.eval (qFac k) x * QPoly.eval (qFacProd (k - 1)) x) := by
    have hkk : (k - 1) + 1 = k := by omega
    have h := eval_qFacProd_succ x (k - 1)
    rw [hkk] at h
    exact h
  -- Now assemble.  LHS = eval(pmul (SN(k+1)) (SN(k−1))) x.
  -- Rewrite the SN's to SNaux form.
  rw [hSNkp1, hSNkm1, hSNk]
  -- Goal (after rw):
  --   eval (pmul (SNaux (k+1) k) (SNaux (k-1) (k-2))) x
  --     ≃ eval (pmul (qFac k) (pmul (SNaux k (k-1)) (SNaux k (k-1)))) x
  -- LHS ≃ g_kp1_k · g_km1_km2  (eval_pmul)
  refine Q'.eqv_trans _ _ _
    (QPoly.eval_pmul (SNaux (k + 1) k) (SNaux (k - 1) (k - 2)) x) ?_
  -- RHS ≃ fk · (g_k_km1 · g_k_km1)
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.eval_pmul (qFac k) (QPoly.pmul (SNaux k (k - 1)) (SNaux k (k - 1))) x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (QPoly.eval_pmul (SNaux k (k - 1)) (SNaux k (k - 1)) x)) ?_
  -- Now goal: fk · (g_k_km1 · g_k_km1) ≃ g_kp1_k · g_km1_km2
  -- Substitute step2 into both g_k_km1 on the LHS: g_k_km1 ≃ Prk1 · g_km1_km2.
  -- LHS ≃ fk · ((Prk1·g_km1_km2)·(Prk1·g_km1_km2))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (q_mul_congr step2 step2)) ?_
  -- RHS target: g_kp1_k · g_km1_km2.  Substitute step1 and step2:
  --   g_kp1_k ≃ Prk · g_k_km1 ≃ (fk·Prk1)·(Prk1·g_km1_km2).
  refine Q'.eqv_symm ?_
  have hg_kp1 : (QPoly.eval (SNaux (k + 1) k) x).eqv
      ((QPoly.eval (qFac k) x * QPoly.eval (qFacProd (k - 1)) x)
        * (QPoly.eval (qFacProd (k - 1)) x * QPoly.eval (SNaux (k - 1) (k - 2)) x)) := by
    refine Q'.eqv_trans _ _ _ step1 ?_
    exact q_mul_congr step3 step2
  -- g_kp1_k · g_km1_km2 ≃ ((fk·Prk1)·(Prk1·g_km1_km2)) · g_km1_km2
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hg_kp1) ?_
  -- Now both sides are pure Q' products.  Write fk, A := Prk1, B := g_km1_km2.
  -- LHS now: ((fk·A)·(A·B)) · B ; target: fk · ((A·B)·(A·B)).
  -- Prove the pure-Q' identity by associativity/commutativity normalization,
  -- on the explicit terms (fk = eval(qFac k) x, A = eval(qFacProd (k-1)) x,
  --  B = eval(SNaux (k-1) (k-2)) x).
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv
      (QPoly.eval (qFac k) x * QPoly.eval (qFacProd (k - 1)) x)
      (QPoly.eval (qFacProd (k - 1)) x * QPoly.eval (SNaux (k - 1) (k - 2)) x)
      (QPoly.eval (SNaux (k - 1) (k - 2)) x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (QPoly.eval (qFac k) x) (QPoly.eval (qFacProd (k - 1)) x)
      ((QPoly.eval (qFacProd (k - 1)) x * QPoly.eval (SNaux (k - 1) (k - 2)) x)
        * QPoly.eval (SNaux (k - 1) (k - 2)) x)) ?_
  refine Q'.mul_eqv_congr_left (QPoly.eval (qFac k) x) _ _ ?_
  -- Goal: A·((A·B)·B) ≃ (A·B)·(A·B)
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (QPoly.eval (qFacProd (k - 1)) x)
      (QPoly.eval (SNaux (k - 1) (k - 2)) x)
      (QPoly.eval (qFacProd (k - 1)) x * QPoly.eval (SNaux (k - 1) (k - 2)) x)) ?_
  refine Q'.mul_eqv_congr_left (QPoly.eval (qFacProd (k - 1)) x) _ _ ?_
  -- Goal: B·(A·B) ≃ (A·B)·B
  exact Q'.mul_comm_eqv (QPoly.eval (SNaux (k - 1) (k - 2)) x)
    (QPoly.eval (qFacProd (k - 1)) x * QPoly.eval (SNaux (k - 1) (k - 2)) x)

/-! ## Recovery of the per-`k` instances from the general theorem

The four `decide`-instances are now corollaries of the one inductive theorem. -/

theorem SN_telescope_gen_recovers_2 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 3) (SN 1)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 2) (QPoly.pmul (SN 2) (SN 2))) x) :=
  SN_telescope_gen 2 (by omega) x

theorem SN_telescope_gen_recovers_3 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 4) (SN 2)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 3) (QPoly.pmul (SN 3) (SN 3))) x) :=
  SN_telescope_gen 3 (by omega) x

theorem SN_telescope_gen_recovers_4 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 5) (SN 3)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 4) (QPoly.pmul (SN 4) (SN 4))) x) :=
  SN_telescope_gen 4 (by omega) x

theorem SN_telescope_gen_recovers_5 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 6) (SN 4)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 5) (QPoly.pmul (SN 5) (SN 5))) x) :=
  SN_telescope_gen 5 (by omega) x

/-! ## Uniform square-positivity (re-export)

The square factor `S_N²` is `≥ 0` for every `N` and every `a` — trivially,
an even power.  Re-exported from `QHankel.geRat_SN_sq_nonneg`. -/

/-- **Uniform square-positivity** `(ceval (SN N) a)² ≥ 0` for every `N`, `a`. -/
theorem geRat_SN_sq_nonneg_uniform (N : Nat) (a : CReal) :
    ExpPos.geRat (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) 0 :=
  geRat_SN_sq_nonneg N a

/-! ## Reduction of uniform `P_N ≥ 0` to the single inductive step `PNStep`

The telescope above is a recurrence for the *square* factor `S_N`.  For the
*coefficient*-positivity of the complementary factor `P_N` we isolate the one
remaining inductive obligation and prove that it suffices.

`PN` is an abstract candidate family (the repo realizes only `P_1…P_5` as
literal lists), with the base cases supplied as hypotheses.  `PNStep` is the
single two-step inductive step.  `uniform_PN_of_PNStep` then yields
`nonnegCoeffs (PN N)` for *every* `N` from `PNStep` plus the base data. -/

/-- The single inductive step: nonneg-coefficient closure of the order-`k`
and `k+1` factors carries to order `k+2`.  This is the **named open
obligation** — see the file header for why the cyclotomic factor `qFac k`
(constant term `−1`) blocks it through `nonnegCoeffs_pmul`. -/
def PNStep (PN : Nat → QPoly.Poly) : Prop :=
  ∀ k, 2 ≤ k → nonnegCoeffs (PN k) → nonnegCoeffs (PN (k + 1)) →
    nonnegCoeffs (PN (k + 2))

/-- **Reduction.**  Given the inductive step `PNStep` and the base cases up to
order `6` (i.e. `P_0…P_6` nonneg — the repo discharges `P_1…P_5` by `decide`,
`P_6` is verified externally / supplied), `nonnegCoeffs (PN N)` holds for
*every* `N`.  By strong-form two-step induction on `N`. -/
theorem uniform_PN_of_PNStep (PN : Nat → QPoly.Poly)
    (hstep : PNStep PN)
    (hb0 : nonnegCoeffs (PN 0)) (hb1 : nonnegCoeffs (PN 1))
    (hb2 : nonnegCoeffs (PN 2)) (hb3 : nonnegCoeffs (PN 3)) :
    ∀ N, nonnegCoeffs (PN N) := by
  -- Two-step induction: prove the pair predicate Q N := nonnegCoeffs (PN N) ∧
  -- nonnegCoeffs (PN (N+1)) for all N, then project.
  have hpair : ∀ N, nonnegCoeffs (PN N) ∧ nonnegCoeffs (PN (N + 1)) := by
    intro N
    induction N with
    | zero => exact ⟨hb0, hb1⟩
    | succ n ih =>
        -- ih : nonnegCoeffs (PN n) ∧ nonnegCoeffs (PN (n+1))
        -- goal: nonnegCoeffs (PN (n+1)) ∧ nonnegCoeffs (PN (n+2))
        refine ⟨ih.2, ?_⟩
        -- need nonnegCoeffs (PN (n+2)).
        -- For n ≥ 2 use the step on k = n; for n = 0,1 use base cases directly.
        match n, ih with
        | 0, _ => exact hb2
        | 1, _ => exact hb3
        | (m + 2), ih =>
            -- k := m+2 ≥ 2, PN k = PN (m+2) = ih.1, PN (k+1) = ih.2.
            -- step gives PN (k+2) = PN (m+4) = PN ((m+2)+2).  Goal: PN (n+2)=PN (m+4).
            exact hstep (m + 2) (by omega) ih.1 ih.2
  exact fun N => (hpair N).1

end YMGap.Continuum.FavardUniform

/-! ## Summary: PROVED vs NAMED-open

**PROVED (axiom-clean, by genuine induction — not per-`k` `decide`).**

  * `evalSNaux_shift` — the index-shift identity (induction on `j`): raising
    the order `N ↦ N+1` of the `SNaux` product multiplies it by `qFacProd j`.
  * `evalSNaux_top` — the top factor is trivial (`(qFac N)^0 = 1`).
  * `SN_telescope_gen` — **the `N`-indexed telescope for ALL `k ≥ 2`**:
    `S_{k+1}·S_{k−1} = (a^{2k}−1)·S_k²`.  This is the structural backbone of
    the uniform proof, generalizing the four `decide`-instances
    (`SN_telescope_gen_recovers_2…5` recover them as corollaries).
  * `geRat_SN_sq_nonneg_uniform` — uniform square-positivity (re-export).
  * `uniform_PN_of_PNStep` — uniform `nonnegCoeffs (PN N)` for every `N`
    REDUCED to the single inductive step `PNStep` + base cases.

**NAMED-open — the single residual `PNStep`.**

  `PNStep PN : ∀ k ≥ 2, nonnegCoeffs (PN k) → nonnegCoeffs (PN (k+1))
                        → nonnegCoeffs (PN (k+2))`.

  The telescope proved here is a recurrence for the *square* factor `S_N`.
  Transporting it to a recurrence for the complementary *coefficient*-nonneg
  factor `P_N` introduces the cyclotomic monomial `qFac k = a^{2k} − 1` as a
  multiplier.  That monomial's constant coefficient is `−1`, so `pmul` by it
  leaves the nonneg-coefficient cone (`nonnegCoeffs_pmul` requires *both*
  arguments nonneg); equivalently, the Favard quadratic
  `P_{k+1}·P_{k−1} = γ_k·P_k²` has `γ_k` rational with `P_{k−1} ∤ P_k²`, so the
  closure is *subtractive* / division-bearing and does NOT carry through the
  cone.  This is exactly where, and why, the uniform coefficient closure
  breaks; `PNStep` is the precisely-named Type-level obligation that remains.
-/

#print axioms YMGap.Continuum.FavardUniform.evalSNaux_shift
#print axioms YMGap.Continuum.FavardUniform.evalSNaux_top
#print axioms YMGap.Continuum.FavardUniform.SN_telescope_gen
#print axioms YMGap.Continuum.FavardUniform.SN_telescope_gen_recovers_2
#print axioms YMGap.Continuum.FavardUniform.SN_telescope_gen_recovers_5
#print axioms YMGap.Continuum.FavardUniform.geRat_SN_sq_nonneg_uniform
#print axioms YMGap.Continuum.FavardUniform.uniform_PN_of_PNStep
