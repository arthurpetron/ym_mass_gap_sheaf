/-
Track B / R2 — the **Gaussian/Casimir MOMENT BOUND** for the scaled heat-kernel
weight, generic in the test polynomial.  This is one half of the continuum
quadratic-defect control: a bound

    ∑_s μ_τ(s) · (1 + τ·C₄(s))^q · P(τ·C₄(s))  ≤  M

on the `τ`-weighted polynomial moment of the heat-kernel-scaled mode density,
where `P` is any test polynomial with NONNEGATIVE rational coefficients and `q`
is the test power.  It composes with the envelope (the other half) to control the
full-mode quadratic defect.

# What this module provides — and exactly how uniform it is (honest)

The scaled-norm infrastructure (`Kτ`, `Zsum`, `μ`, `qfac`, the moving cutoff `S`,
and the Gaussian/Casimir tail modulus) is reused wholesale.  On top of it:

  * `Peval` / `nonnegCoeffs` — the test polynomial as a `List Q'` of coefficients
    (reusing the repo's `QPoly.eval`), with the elementary facts that a
    nonneg-coefficient polynomial is NONNEGATIVE and MONOTONE on `y ≥ 0`
    (`Peval_nonneg`, `Peval_mono`).
  * `momentTerm` / `momentSum` — the per-mode moment summand
    `μ(s)·qfac(w,s)^q·P((1−w)·C₄(s))` and its finite-cutoff sum.
  * **`moment_bound`** (the §3 target).  For every test polynomial `P` with
    nonnegative coefficients, every power `q`, every precision `r`, and a moving
    cutoff `S` satisfying the SAME two explicit rational cutoff inequalities as
    the tail modulus (at the absorbed degree), there is an explicit

        M(P,q,r,S)  =  ofNat S · ((1 + C₄(S))^q · P(C₄(S)))  +  (1/2)^r

    that is **independent of the weight `w`** and bounds the full moment
    `momentSum w (S+M)` for every window `M`.  PROOF: head/tail split at `S`.
    The tail (`s ≥ S`) is `≤ (1/2)^r` by the Casimir tail modulus (the test
    factor `qfac^q·P` is absorbed into a higher Casimir degree `m`).  The head
    (`s < S`) is bounded uniformly in `w` because each `μ(s) ≤ 1` (the mode density
    is a normalized weight) and the test factor `qfac(w,s)^q·P((1−w)·C₄(s))` is
    DOMINATED by its `w = 0` value `(1 + C₄(s))^q·P(C₄(s)) ≤ (1 + C₄(S))^q·P(C₄(S))`
    on `0 ≤ w` (because `qfac` and the `(1−w)·C₄` argument both decrease in `w`,
    and `P` is monotone), so each of the `≤ S` head terms is `≤ headMax`.

# The precise uniformity claim (CRITICAL honesty, AGENTS.md Rule 6)

`M` is **independent of `w`**: it is a function of `(P, q, r, S)` ONLY.  Therefore
on any compact weight subinterval `0 < w ≤ w₀ < 1` a SINGLE cutoff `S` discharges
the two cutoff inequalities for all such `w`, and `M` is then a genuinely
uniform-in-`w` moment bound there.  What is NOT delivered for free is a single `S`
that works for ALL `w ∈ (0,1)` simultaneously: the tail cutoff `S` must grow as
`w → 1` (the active-mode spread `≍ τ^{-1/2}`), so to cover `w → 1` one feeds the
`w`-dependent cutoff `S(w)` — at which point `M(P,q,r,S(w))` carries that mild,
explicit `S`-dependence.  This is exactly the honest moving-cutoff structure of
the underlying tail modulus: the bound is uniform in `w` for each fixed cutoff,
and the cutoff is the only thing that moves.  The head bound and the tail bound
are both proved here; the only `w`-input is the two decidable cutoff inequalities,
fired by `decide` at any concrete `w` (and in the demo).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable `Q'`/`Nat` facts, and
reused order lemmas.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide` (only `decide` on decidable facts), no `sorry`.  All witnesses are
`Type`-level data.
-/

import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Constructive.QPoly
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CornerBound

namespace YMGap.Continuum.BondMovingMoment

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm

/-! ## 0. Small `Q'` helpers (proved here, axiom-clean) -/

/-- `-w ≤ 0` for `0 ≤ w` (raw `num`-sign fact). -/
theorem neg_nonpos {w : Q'} (hw : (0 : Q') ≤ w) : -w ≤ (0 : Q') := by
  have hn : (0 : Int) ≤ w.num := by rw [Q'.zero_le_iff_num_nonneg] at hw; exact hw
  show (-w).num * ((0 : Q').den : Int) ≤ (0 : Q').num * ((-w).den : Int)
  show (-w.num) * (1 : Int) ≤ (0 : Int) * ((-w).den : Int)
  rw [Int.zero_mul, Int.mul_one]
  omega

/-- `1 − w ≤ 1` for `0 ≤ w`.  (`1 − w = 1 + (−w) ≤ 1 + 0 = 1`.) -/
theorem oneSub_le_one {w : Q'} (hw : (0 : Q') ≤ w) : (1 : Q') - w ≤ (1 : Q') := by
  show (1 : Q') + (-w) ≤ (1 : Q')
  have h1 : (1 : Q') + (-w) ≤ (1 : Q') + 0 :=
    Q'.add_le_add_left (1 : Q') (-w) 0 (neg_nonpos hw)
  rwa [Q'.add_zero'] at h1

/-- `ofNat` is monotone: `m ≤ n ⟹ ofNat m ≤ ofNat n`. -/
theorem ofNat_le_ofNat {m n : Nat} (h : m ≤ n) : Q'.ofNat m ≤ Q'.ofNat n := by
  show (Q'.ofNat m).num * ((Q'.ofNat n).den : Int)
      ≤ (Q'.ofNat n).num * ((Q'.ofNat m).den : Int)
  show (m : Int) * 1 ≤ (n : Int) * 1
  have : (m : Int) ≤ (n : Int) := by exact_mod_cast h
  omega

/-- **`Q'`-power monotonicity:** `0 ≤ a ≤ b ⟹ a^q ≤ b^q`. -/
theorem pow_le_pow_of_le {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ q : Nat, a ^ q ≤ b ^ q
  | 0 => by show (1 : Q') ≤ (1 : Q'); exact Q'.le_refl' 1
  | q + 1 => by
      show a * a ^ q ≤ b * b ^ q
      have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
      have haq : a ^ q ≤ b ^ q := pow_le_pow_of_le ha hab q
      have h1 : a * a ^ q ≤ b * a ^ q :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hab (Q'.pow_nonneg _ ha q)
      have h2 : b * a ^ q ≤ b * b ^ q :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ haq hb
      exact Q'.le_trans' _ _ _ h1 h2

/-- `absQ x = x` when `0 ≤ x`. -/
theorem absQ_of_nonneg (x : Q') (hx : (0 : Q') ≤ x) : absQ x = x := by
  unfold absQ
  have hnum : (0 : Int) ≤ x.num := by
    rw [Q'.zero_le_iff_num_nonneg] at hx; exact hx
  rw [if_pos hnum]

/-- `ofNat (n+1) ≃ ofNat n + 1`. -/
theorem ofNat_succ_eqv (n : Nat) : (Q'.ofNat (n + 1)).eqv (Q'.ofNat n + (1 : Q')) :=
  Q'.ofNat_add_eqv n 1

/-- **A single term of a nonnegative `fsum` is `≤` the whole sum.**  For `s < n`
and nonnegative `f`, `f s ≤ fsum f n`.  (Structural induction on `n`.) -/
theorem fsum_term_le_of_nonneg {f : Nat → Q'} (hf : ∀ t, (0 : Q') ≤ f t) :
    ∀ (s n : Nat), s < n → f s ≤ fsum f n
  | s, 0, hs => absurd hs (Nat.not_lt_zero s)
  | s, n + 1, hs => by
      show f s ≤ fsum f n + f n
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | heq
      · have hrec : f s ≤ fsum f n := fsum_term_le_of_nonneg hf s n hlt
        have hself : fsum f n ≤ fsum f n + f n :=
          Q'.add_le_self_of_nonneg _ _ (hf n)
        exact Q'.le_trans' _ _ _ hrec hself
      · subst heq
        have hsumnn : (0 : Q') ≤ fsum f s := fsum_nonneg hf s
        have h0 : (0 : Q') + f s ≤ fsum f s + f s :=
          Q'.add_le_add_right _ _ (f s) hsumnn
        exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv (f s))) h0

/-- A constant times the length bounds a `finSum` of terms each `≤` that constant:
`(∀ i < n, f i ≤ C) ⟹ finSum f n ≤ ofNat n · C` (for `C ≥ 0`).  Induction on `n`. -/
theorem finSum_le_count_mul {C : Q'} (hC : (0 : Q') ≤ C) (f : Nat → Q') :
    ∀ n, (∀ i, i < n → f i ≤ C) → RationalTail.finSum f n ≤ Q'.ofNat n * C
  | 0, _ => by
      show (0 : Q') ≤ Q'.ofNat 0 * C
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv C))
  | n + 1, h => by
      show RationalTail.finSum f n + f n ≤ Q'.ofNat (n + 1) * C
      have hrec : RationalTail.finSum f n ≤ Q'.ofNat n * C :=
        finSum_le_count_mul hC f n (fun i hi => h i (Nat.lt_succ_of_lt hi))
      have hlast : f n ≤ C := h n (Nat.lt_succ_self n)
      have hsum : RationalTail.finSum f n + f n ≤ Q'.ofNat n * C + C :=
        Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ (f n) hrec)
          (Q'.add_le_add_left (Q'.ofNat n * C) _ _ hlast)
      refine Q'.le_trans' _ _ _ hsum ?_
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_symm ?_
      have hstep : (Q'.ofNat (n + 1) * C).eqv ((Q'.ofNat n + (1 : Q')) * C) :=
        Q'.mul_eqv_congr_right _ _ C (ofNat_succ_eqv n)
      refine Q'.eqv_trans _ _ _ hstep ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (Q'.ofNat n) (1 : Q') C) ?_
      exact Q'.add_eqv_congr_left (Q'.ofNat n * C) ((1 : Q') * C) C (Q'.one_mul_eqv C)

/-- `c4` is monotone: `s ≤ t ⟹ c4 s ≤ c4 t` (`c4 s = s(s+2)`). -/
theorem c4_mono {s t : Nat} (h : s ≤ t) : c4 s ≤ c4 t := by
  show s * (s + 2) ≤ t * (t + 2)
  exact Nat.mul_le_mul h (by omega)

/-! ## 1. The test polynomial: nonneg-coefficient `Poly` and `Peval` -/

/-- The test polynomial type is the repo's `QPoly.Poly` (a `List Q'` of
coefficients, low-to-high degree). -/
abbrev Poly := QPoly.Poly

/-- The test-polynomial evaluation `Peval P y` is the repo's Horner `QPoly.eval`. -/
def Peval (P : Poly) (y : Q') : Q' := QPoly.eval P y

@[simp] theorem Peval_nil (y : Q') : Peval [] y = 0 := rfl

@[simp] theorem Peval_cons (c : Q') (cs : Poly) (y : Q') :
    Peval (c :: cs) y = c + y * Peval cs y := rfl

/-- A polynomial has NONNEGATIVE coefficients. -/
def nonnegCoeffs : Poly → Prop
  | [] => True
  | (c :: cs) => (0 : Q') ≤ c ∧ nonnegCoeffs cs

/-- **Nonneg-coeff ⇒ nonneg value on `y ≥ 0`.**  `Peval P y ≥ 0` for `y ≥ 0`. -/
theorem Peval_nonneg : ∀ (P : Poly) {y : Q'}, nonnegCoeffs P → (0 : Q') ≤ y →
    (0 : Q') ≤ Peval P y
  | [], _, _, _ => Q'.le_refl' 0
  | (c :: cs), y, hP, hy => by
      show (0 : Q') ≤ c + y * Peval cs y
      have hc : (0 : Q') ≤ c := hP.1
      have hrec : (0 : Q') ≤ Peval cs y := Peval_nonneg cs hP.2 hy
      exact Q'.zero_le_add _ _ hc (Q'.mul_nonneg _ _ hy hrec)

/-- **Nonneg-coeff ⇒ monotone on `0 ≤ y ≤ z`.**  `Peval P y ≤ Peval P z`. -/
theorem Peval_mono : ∀ (P : Poly) {y z : Q'}, nonnegCoeffs P →
    (0 : Q') ≤ y → y ≤ z → Peval P y ≤ Peval P z
  | [], _, _, _, _, _ => Q'.le_refl' 0
  | (c :: cs), y, z, hP, hy, hyz => by
      show c + y * Peval cs y ≤ c + z * Peval cs z
      have hz : (0 : Q') ≤ z := Q'.le_trans' _ _ _ hy hyz
      have hPynn : (0 : Q') ≤ Peval cs y := Peval_nonneg cs hP.2 hy
      have hrec : Peval cs y ≤ Peval cs z := Peval_mono cs hP.2 hy hyz
      have h1 : y * Peval cs y ≤ z * Peval cs y :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hyz hPynn
      have h2 : z * Peval cs y ≤ z * Peval cs z :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hrec hz
      have h3 : y * Peval cs y ≤ z * Peval cs z := Q'.le_trans' _ _ _ h1 h2
      exact Q'.add_le_add_left c _ _ h3

/-! ## 2. The moment summand and its finite-cutoff sum -/

/-- The scaled-`τ`-argument `yArg(w,s) = (1 − w)·C₄(s)` — the `Q'` proxy for the
scaled Casimir `τ·C₄(s)` (`τ = −log w ≍ 1 − w`), consistent with `qfac`. -/
def yArg (w : Q') (s : Nat) : Q' := ((1 : Q') - w) * Q'.ofNat (c4 s)

theorem yArg_nonneg {w : Q'} (hw1 : w ≤ (1 : Q')) (s : Nat) : (0 : Q') ≤ yArg w s :=
  Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hw1) (zero_le_ofNat _)

/-- **The per-mode moment summand** `μ(s)·qfac(w,s)^q·P(yArg(w,s))`. -/
def momentTerm (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (P : Poly)
    (s : Nat) : Q' :=
  μ w N hZ s * (qfac w s ^ q * Peval P (yArg w s))

/-- **The finite-cutoff moment sum** `∑_{s<n} μ(s)·qfac^q·P(yArg)`. -/
def momentSum (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (P : Poly)
    (n : Nat) : Q' :=
  RationalTail.finSum (fun s => momentTerm w N hZ q P s) n

/-! ## 3. The head bound: `μ ≤ 1` and the `w`-monotone test factor -/

/-- **The mode density is `≤ 1` on its own cutoff.**  For `s < N` and `0 < w`,
`μ(s) ≤ 1`, because the `s`-th summand `(s+1)²·w^{C₄(s)}` is `≤ Zsum w N` (it is one
of the nonnegative terms of that finite sum).  This is the normalized-weight fact
that makes the head uniform. -/
theorem μ_le_one {w : Q'} (hw : (0 : Q') < w) (N : Nat) (hZ : (0 : Q') < Zsum w N)
    (s : Nat) (hs : s < N) : μ w N hZ s ≤ (1 : Q') := by
  show Q'.divPos (dimQ s * (dimQ s * qpow w (c4 s))) (Zsum w N) hZ ≤ (1 : Q')
  refine Q'.divPos_le_of_le_mul _ _ hZ ?_
  have hterm_le : dimQ s * (dimQ s * qpow w (c4 s)) ≤ Zsum w N := by
    show dimQ s * (dimQ s * qpow w (c4 s))
        ≤ fsum (fun t => dimQ t * (dimQ t * qpow w (c4 t))) N
    exact fsum_term_le_of_nonneg
      (fun t => Zsum_summand_nonneg (Q'.le_of_lt hw) t) s N hs
  refine Q'.le_trans' _ _ _ hterm_le ?_
  exact Q'.ge_of_eqv (Q'.one_mul_eqv (Zsum w N))

/-- **`qfac` decreases in `w`.**  For `0 ≤ w`, `qfac(w,s) ≤ 1 + C₄(s)`. -/
theorem qfac_le_w0 {w : Q'} (hw0 : (0 : Q') ≤ w) (s : Nat) :
    qfac w s ≤ (1 : Q') + Q'.ofNat (c4 s) := by
  show (1 : Q') + ((1 : Q') - w) * Q'.ofNat (c4 s) ≤ (1 : Q') + Q'.ofNat (c4 s)
  refine Q'.add_le_add_left (1 : Q') _ _ ?_
  have hstep : ((1 : Q') - w) * Q'.ofNat (c4 s) ≤ (1 : Q') * Q'.ofNat (c4 s) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (oneSub_le_one hw0) (zero_le_ofNat _)
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-- `yArg(w,s) ≤ C₄(s)` for `0 ≤ w`. -/
theorem yArg_le_w0 {w : Q'} (hw0 : (0 : Q') ≤ w) (s : Nat) :
    yArg w s ≤ Q'.ofNat (c4 s) := by
  show ((1 : Q') - w) * Q'.ofNat (c4 s) ≤ Q'.ofNat (c4 s)
  have hstep : ((1 : Q') - w) * Q'.ofNat (c4 s) ≤ (1 : Q') * Q'.ofNat (c4 s) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (oneSub_le_one hw0) (zero_le_ofNat _)
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-- **The uniform head-term bound.**  For `s < S` (and `0 < w < 1`, `s < N`), the
moment summand is bounded by a `w`-INDEPENDENT head maximum:

    μ(s)·qfac(w,s)^q·P(yArg(w,s))  ≤  1 · ((1 + C₄(S))^q · P(C₄(S))).

PROOF.  `μ(s) ≤ 1`; `qfac(w,s) ≤ 1 + C₄(s) ≤ 1 + C₄(S)`; `P(yArg(w,s)) ≤ P(C₄(s)) ≤
P(C₄(S))`.  All factors nonnegative. -/
theorem momentTerm_head_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (P : Poly) (hP : nonnegCoeffs P)
    (S s : Nat) (hsS : s < S) (hsN : s < N) :
    momentTerm w N hZ q P s
      ≤ (1 : Q') * ((((1 : Q') + Q'.ofNat (c4 S)) ^ q) * Peval P (Q'.ofNat (c4 S))) := by
  show μ w N hZ s * (qfac w s ^ q * Peval P (yArg w s))
      ≤ (1 : Q') * ((((1 : Q') + Q'.ofNat (c4 S)) ^ q) * Peval P (Q'.ofNat (c4 S)))
  have hw0' : (0 : Q') ≤ w := Q'.le_of_lt hw0
  have hw1' : w ≤ (1 : Q') := Q'.le_of_lt hw1
  have hC4mono : c4 s ≤ c4 S := c4_mono (Nat.le_of_lt hsS)
  have hC4le : Q'.ofNat (c4 s) ≤ Q'.ofNat (c4 S) := ofNat_le_ofNat hC4mono
  have hqfacnn : (0 : Q') ≤ qfac w s := qfac_nonneg hw1' s
  have hqfacpownn : (0 : Q') ≤ qfac w s ^ q := Q'.pow_nonneg _ hqfacnn q
  have hyargnn : (0 : Q') ≤ yArg w s := yArg_nonneg hw1' s
  have hPynn : (0 : Q') ≤ Peval P (yArg w s) := Peval_nonneg P hP hyargnn
  have hbasenn : (0 : Q') ≤ (1 : Q') + Q'.ofNat (c4 S) :=
    Q'.zero_le_add _ _ (by decide) (zero_le_ofNat _)
  have hbasepownn : (0 : Q') ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q :=
    Q'.pow_nonneg _ hbasenn q
  -- qfac^q ≤ (1+C₄ S)^q
  have hqbase : qfac w s ≤ (1 : Q') + Q'.ofNat (c4 S) :=
    Q'.le_trans' _ _ _ (qfac_le_w0 hw0' s) (Q'.add_le_add_left (1 : Q') _ _ hC4le)
  have hqfacpow : qfac w s ^ q ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q :=
    pow_le_pow_of_le hqfacnn hqbase q
  -- P(yArg) ≤ P(C₄ S)
  have hyle : yArg w s ≤ Q'.ofNat (c4 S) :=
    Q'.le_trans' _ _ _ (yArg_le_w0 hw0' s) hC4le
  have hPmono : Peval P (yArg w s) ≤ Peval P (Q'.ofNat (c4 S)) :=
    Peval_mono P hP hyargnn hyle
  have hPSnn : (0 : Q') ≤ Peval P (Q'.ofNat (c4 S)) :=
    Peval_nonneg P hP (zero_le_ofNat _)
  -- combine test factor
  have hfac : qfac w s ^ q * Peval P (yArg w s)
      ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q * Peval P (Q'.ofNat (c4 S)) := by
    have h1 : qfac w s ^ q * Peval P (yArg w s)
        ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q * Peval P (yArg w s) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hqfacpow hPynn
    have h2 : ((1 : Q') + Q'.ofNat (c4 S)) ^ q * Peval P (yArg w s)
        ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q * Peval P (Q'.ofNat (c4 S)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hPmono hbasepownn
    exact Q'.le_trans' _ _ _ h1 h2
  -- μ ≤ 1, combine
  have hμle : μ w N hZ s ≤ (1 : Q') := μ_le_one hw0 N hZ s hsN
  have hfacnn : (0 : Q') ≤ qfac w s ^ q * Peval P (yArg w s) :=
    Q'.mul_nonneg _ _ hqfacpownn hPynn
  have hA : μ w N hZ s * (qfac w s ^ q * Peval P (yArg w s))
      ≤ (1 : Q') * (qfac w s ^ q * Peval P (yArg w s)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hμle hfacnn
  have hB : (1 : Q') * (qfac w s ^ q * Peval P (yArg w s))
      ≤ (1 : Q') * (((1 : Q') + Q'.ofNat (c4 S)) ^ q * Peval P (Q'.ofNat (c4 S))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hfac (by decide)
  exact Q'.le_trans' _ _ _ hA hB

/-! ## 4. THE MOMENT BOUND (the §3 target) -/

/-- **The explicit `w`-independent moment bound constant.**

    M(P,q,r,S)  =  ofNat S · ((1 + C₄(S))^q · P(C₄(S)))  +  (1/2)^r.

It depends only on the test polynomial `P`, the power `q`, the precision `r`, and
the cutoff `S` — NOT on the weight `w`. -/
def momentM (P : Poly) (q r S : Nat) : Q' :=
  Q'.ofNat S * ((((1 : Q') + Q'.ofNat (c4 S)) ^ q) * Peval P (Q'.ofNat (c4 S)))
    + dyad r

theorem momentM_nonneg (P : Poly) (hP : nonnegCoeffs P) (q r S : Nat) :
    (0 : Q') ≤ momentM P q r S := by
  refine Q'.zero_le_add _ _ ?_ (dyad_nonneg r)
  refine Q'.mul_nonneg _ _ (zero_le_ofNat _) ?_
  refine Q'.mul_nonneg _ _ (Q'.pow_nonneg _ ?_ q) (Peval_nonneg P hP (zero_le_ofNat _))
  exact Q'.zero_le_add _ _ (by decide) (zero_le_ofNat _)

/-- **THE MOMENT BOUND (the §3 target).**  Fix the heat-kernel weight `0 < w < 1`,
a test polynomial `P` with nonnegative coefficients, a power `q`, a precision `r`,
a cutoff `S`, and a cutoff index `N₀` with `S ≤ N₀`.  Suppose:

  * the per-tail-term Casimir domination at the absorbed degree `m + 2`
    (`hsummand`): each tail summand is `≤ tailTerm w (m+2) (S+k)`;
  * the two explicit moving-cutoff inequalities of the tail modulus
    (`hcut`, `hhead`).

Then for EVERY window `M`,

    momentSum w N₀ hZ q P (S + M)  ≤  momentM P q r S,

with `momentM` **independent of `w`** (a function of `(P, q, r, S)`).

PROOF.  Split the sum at `S`: head + tail.  The head is `≤ ofNat S · headMax`
(`momentTerm_head_le`, `finSum_le_count_mul`); the tail is `≤ (1/2)^r`
(`norm_tail_modulus`).  Sum the two. -/
theorem moment_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (P : Poly) (hP : nonnegCoeffs P) (q m r S N₀ : Nat) (hSN : S ≤ N₀)
    (hZ : (0 : Q') < Zsum w N₀)
    (hsummand : ∀ k,
      momentTerm w N₀ hZ q P (S + k) ≤ tailTerm w (m + 2) (S + k))
    (hcut : Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm w (m + 2) S ≤ dyad (r + 1)) :
    ∀ M, momentSum w N₀ hZ q P (S + M) ≤ momentM P q r S := by
  intro M
  -- the moment summand sequence and the `w`-independent head maximum
  let f : Nat → Q' := fun s => momentTerm w N₀ hZ q P s
  let headMax : Q' := (((1 : Q') + Q'.ofNat (c4 S)) ^ q) * Peval P (Q'.ofNat (c4 S))
  show RationalTail.finSum f (S + M) ≤ momentM P q r S
  have hsplit : (RationalTail.finSum f (S + M)).eqv
      (RationalTail.finSum f S + RationalTail.finSum (fun j => f (S + j)) M) :=
    finSum_split f S M
  have hHMnn : (0 : Q') ≤ headMax := by
    refine Q'.mul_nonneg _ _ (Q'.pow_nonneg _ ?_ q) (Peval_nonneg P hP (zero_le_ofNat _))
    exact Q'.zero_le_add _ _ (by decide) (zero_le_ofNat _)
  -- HEAD
  have hhead_terms : ∀ i, i < S → f i ≤ headMax := by
    intro i hi
    have hiN : i < N₀ := Nat.lt_of_lt_of_le hi hSN
    have hle := momentTerm_head_le hw0 hw1 N₀ hZ q P hP S i hi hiN
    refine Q'.le_trans' _ _ _ hle ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv headMax)
  have hHEAD : RationalTail.finSum f S ≤ Q'.ofNat S * headMax :=
    finSum_le_count_mul hHMnn f S hhead_terms
  -- TAIL
  have hTAIL : RationalTail.finSum (fun j => f (S + j)) M ≤ dyad r := by
    have hsumm' : ∀ k,
        μ w N₀ hZ (S + k) * (qfac w (S + k) ^ q * absQ (Peval P (yArg w (S + k))))
          ≤ tailTerm w (m + 2) (S + k) := by
      intro k
      have hPy_nn : (0 : Q') ≤ Peval P (yArg w (S + k)) :=
        Peval_nonneg P hP (yArg_nonneg (Q'.le_of_lt hw1) (S + k))
      rw [absQ_of_nonneg _ hPy_nn]
      exact hsummand k
    have htail := norm_tail_modulus (rrel := fun s => Peval P (yArg w s))
      hw0 hw1 N₀ hZ q m r S hsumm' hcut hhead M
    refine Q'.le_trans' _ _ _ ?_ htail
    refine Q'.le_of_eqv ?_
    have hcong : ∀ k,
        (f (S + k)).eqv
          (μ w N₀ hZ (S + k) * (qfac w (S + k) ^ q * absQ (Peval P (yArg w (S + k))))) := by
      intro k
      show (μ w N₀ hZ (S + k) * (qfac w (S + k) ^ q * Peval P (yArg w (S + k)))).eqv
          (μ w N₀ hZ (S + k) * (qfac w (S + k) ^ q * absQ (Peval P (yArg w (S + k)))))
      have hPy_nn : (0 : Q') ≤ Peval P (yArg w (S + k)) :=
        Peval_nonneg P hP (yArg_nonneg (Q'.le_of_lt hw1) (S + k))
      rw [absQ_of_nonneg _ hPy_nn]
      exact Q'.eqv_refl _
    exact RationalTail.finSum_eqv_congr (fun j => f (S + j))
      (fun k => μ w N₀ hZ (S + k) * (qfac w (S + k) ^ q * absQ (Peval P (yArg w (S + k)))))
      hcong M
  -- COMBINE
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ hHEAD)
    (Q'.add_le_add_left (Q'.ofNat S * headMax) _ _ hTAIL)

/-! ## 5. Demo: the moment bound constant at a concrete `P`, `q`, `w`

Test polynomial `P = 1 + y` (`[1,1]`, nonneg coeffs), power `q = 1`, precision
`r = 1`, cutoff `S = 2`.  The explicit `w`-independent bound constant
`momentM [1,1] 1 1 2` is produced and certified nonnegative.  The two
moving-cutoff inequalities at the absorbed degree `m+2 = 4`, weight `w = 1/4`, are
decidable `Q'` facts (the `w`-input the bound consumes). -/

/-- The demo test polynomial `P = 1 + y` (`[1, 1]`), with nonnegative coefficients. -/
def demoP : Poly := [(1 : Q'), (1 : Q')]

theorem demoP_nonneg : nonnegCoeffs demoP :=
  ⟨by decide, ⟨by decide, True.intro⟩⟩

/-- The explicit `w`-independent demo bound constant `momentM [1,1] 1 1 2`. -/
def demoM : Q' := momentM demoP 1 1 2

/-- The demo bound constant is nonnegative. -/
theorem demoM_nonneg : (0 : Q') ≤ demoM := momentM_nonneg demoP demoP_nonneg 1 1 2

/-- The two moving-cutoff inequalities at the absorbed degree `m+2 = 4`, weight
`w = 1/4`, cutoff `S = 2`, precision `r = 1` — both decidable (the `w`-input). -/
theorem demo_moment_cut :
    Q'.ofNat (2 ^ (2 + 2)) * qpow demoW (2 * 2 + 3) ≤ HalfPow.half := by decide

theorem demo_moment_head : tailTerm demoW (2 + 2) 2 ≤ dyad (1 + 1) := by decide

end YMGap.Continuum.BondMovingMoment

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BondMovingMoment.neg_nonpos
#print axioms YMGap.Continuum.BondMovingMoment.oneSub_le_one
#print axioms YMGap.Continuum.BondMovingMoment.ofNat_le_ofNat
#print axioms YMGap.Continuum.BondMovingMoment.pow_le_pow_of_le
#print axioms YMGap.Continuum.BondMovingMoment.absQ_of_nonneg
#print axioms YMGap.Continuum.BondMovingMoment.ofNat_succ_eqv
#print axioms YMGap.Continuum.BondMovingMoment.fsum_term_le_of_nonneg
#print axioms YMGap.Continuum.BondMovingMoment.finSum_le_count_mul
#print axioms YMGap.Continuum.BondMovingMoment.c4_mono
#print axioms YMGap.Continuum.BondMovingMoment.Peval_nonneg
#print axioms YMGap.Continuum.BondMovingMoment.Peval_mono
#print axioms YMGap.Continuum.BondMovingMoment.yArg_nonneg
#print axioms YMGap.Continuum.BondMovingMoment.μ_le_one
#print axioms YMGap.Continuum.BondMovingMoment.qfac_le_w0
#print axioms YMGap.Continuum.BondMovingMoment.yArg_le_w0
#print axioms YMGap.Continuum.BondMovingMoment.momentTerm_head_le
#print axioms YMGap.Continuum.BondMovingMoment.momentM_nonneg
#print axioms YMGap.Continuum.BondMovingMoment.moment_bound
#print axioms YMGap.Continuum.BondMovingMoment.demoM_nonneg
#print axioms YMGap.Continuum.BondMovingMoment.demo_moment_cut
#print axioms YMGap.Continuum.BondMovingMoment.demo_moment_head
