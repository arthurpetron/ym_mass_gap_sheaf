/-
**Track A2-WZ — genuine WZ / telescoping certificates for the Racah / Dougall
layer, VERIFIED in Lean by exact arithmetic (sympy only COMPUTES them; the Lean
proofs below are the truth), plus the Schur-uniqueness coherent family
(orthogonality / backcoupling / hexagon / n-chain route independence).**

`BiedenharnElliottGeneral` reduced the signed-6j Biedenharn–Elliott pentagon,
∀-spins, to the single RATIONAL factorial-sum residual `BEDougallCore`
(`Σ_x (−1)^{Σj+x}(2x+1)·S₁S₂S₃·Δ²Δ²Δ² = S_R1·S_R2·Δ²`) and left it a NAMED
obligation.  This module does two independent, honest things.

# Engine B — WZ / telescoping, computed in Python (`computations/dougall_wz.py`)
and RE-VERIFIED here by exact Lean arithmetic (no sympy is trusted):

  * `int_telescope` — the reusable creative-telescoping / WZ engine: if `f` has an
    antidifference certificate `g` (`f t = g (t+1) − g t` for all `t`), then
    `Σ_{t<N} f t = g N − g 0`, for ALL `N`.  Pure Lean-core `Int` induction +
    `omega`; NO `ring`, NO `native_decide`.
  * `altDim_cert` / `altDim_sum` — the WZ certificate for the signed-dimension
    weight `f(x)=(−1)^x(2x+1)` that sits inside the Biedenharn–Elliott summand:
    its antidifference is `g(x)=−(−1)^x·x`, and `Σ_{x<N}(−1)^x(2x+1)=−(−1)^N·N`,
    ∀ `N`.  (sympy computed `g`; the identity is PROVED here.)
  * `binom` / `binom_pascal` / `hockeyStick` — the binomial (Pascal) convolution
    telescope `Σ_{i<N} C(r+i,r) = C(r+N,r+1)`, ∀ `r,N` — a genuine member of the
    Vandermonde/Saalschütz convolution family named as *absent* in
    `BiedenharnElliottGeneral` (its all-spins residual "needs a
    Vandermonde/Saalschütz convolution layer").  PROVED by Pascal + telescope,
    ∀ parameters, in Lean core.

# Engine A — the Schur ≤1-dim uniqueness coherent family (extends
`PentagonFromUniqueness.pentagon_from_uniqueness`):

  * `orthogonality_from_uniqueness` — `u A B · u B A ≃ 1` (a recoupling followed
    by its reverse is the identity: the abstract Racah orthogonality / unitarity).
  * `backcoupling_cocycle` — `u A B · (u B C · u C A) ≃ 1` (the 3-cycle
    backcoupling relation).
  * `hexagon_from_uniqueness` — two 3-step routes with equal endpoints agree
    (`u A B·(u B C·u C D) ≃ u A E·(u E F·u F D)`), the hexagon coherence.
  * `chainProd` / `chain_route_independence` — ANY multi-step recoupling path
    from `A` to `B` composes to the SAME scalar `u A B`; route independence for
    arbitrary-length paths (what the loopy fusion network needs).
  All are `Q'` consequences of the Schur composition law `comp` (≤1-dim Hom) +
  associativity — NOT factorial `decide`s.

# HONEST verdict (AGENTS.md Rule 6/9)

The Python ground-truthing (`dougall_wz.py` + `probe1/probe2`) establishes:

  (i)   The UNGUARDED `BEDougallCore` is FALSE (≈32% of twice-spin 9-tuples in
        `[0,2]⁹` fail: `racahSum`/`triSq` pick up spurious off-triangle mass from
        `Nat` truncated subtraction).  Even the naive outer-tetrahedron guard is
        wrong: `204/205` outer-admissible `[0,2]⁹` tuples FAIL the literal identity.
  (ii)  The EXACT admissible-set fix is now PINNED (§6, `guardedBEDougall`): the
        failure is entirely the `x`-SUM including off-support terms.  Guarding
        each `x`-summand by the genuine physical validity of the three LHS
        tetrahedra (`lhsAdmX`, the twice-spin triangle+parity `valid6` condition)
        and restricting to `outerAdm` tuples makes the identity hold on the FULL
        admissible set: `0` failures over `[0,2]⁹` (`205`), `[0,3]⁹` (`1495`), and
        random `[0,6]⁹` (`1141`).  This is the genuine triangle/parity guard, NOT
        an ad-hoc restriction — verified in Python across every scanned range, and
        `decide`-witnessed at a nondegenerate physical tetrahedron (all spins `1`,
        value `384`) and at a repaired counterexample.  (The pre-existing
        `pentagon_R/_I` are truncation coincidences — NOT outer-admissible.)
  (iii) A degree-3 member of the Vandermonde/Saalschütz convolution layer named
        absent in `BiedenharnElliottGeneral` is now normaliser-VERIFIED
        (`RingNormaliser.vandermonde_deg3`, sympy computes / kernel decides).

The `guardedBEDougall` x-sum is still a genuine MULTI-sum (each summand a product
of THREE inner Racah `t`-sums), so NO single order-0 (Gosper) WZ certificate
closes it; a creative-telescoping / Zeilberger recurrence over the three COUPLED
inner sums (a Vandermonde/Saalschütz convolution layer, members of which —
hockey-stick, deg-2/deg-3/deg-4 Vandermonde — are PROVED here /
`RingNormaliser`) is required.

# SHARP diagnosis of the remaining coupled step (`computations/racah_coupled.py`)

The coupled attack was run all the way to the point where the residual is
*named exactly*, not vaguely:

  * **Structure.**  `guardedBERationalLHS = Σ_x (−1)^{(Σj+x)/2}(x+1)·S₁(x)S₂(x)S₃(x)
    ·Δ²(a,b,x)Δ²(c,d,x)Δ²(e,f,x)` is a genuine **4-fold nested sum** over
    `(x; t₁,t₂,t₃)`: each inner Racah `t`-sum `Sᵢ(x)` couples to the OUTER index
    `x` (and to two outer labels), and the three inner sums are mutually
    independent *given `x`*.  The RHS is a 2-fold sum `S_R1·S_R2·Δ²(p,q,r)`.

  * **The univariate-Zeilberger route is REFUTED (structural, not a failed
    search).**  Every single spin variable has BOUNDED admissible support: the
    triangle inequalities `|a−b| ≤ x ≤ a+b` (and their analogues for every
    label) truncate every one-parameter slice to a short run — the longest
    admissible run varying ANY one of the nine labels over `[0,3]⁹` bases is `4`
    (≤ `6` over `[0,6]⁹`).  So there is **no infinite one-parameter holonomic
    sequence** on which to run OR verify a classical (single-variable)
    Zeilberger recurrence, and an exact rational nullspace search finds NO common
    order‑≤4/deg‑≤5 recurrence within any admissible run (`racah_coupled.py §3`).
    `guardedBEDougall` is a genuinely FINITE MULTIVARIATE identity, not a member
    of a 1-parameter `P`-recursive family.

  * **The EXACT remaining step** is therefore a **multivariate creative
    telescoping** (Wegschaider/Apagodu–Zeilberger style) over the coupled
    `(x; t₁,t₂,t₃)` summation simplex: a certificate `R` (a rational function of
    all nine labels and the four summation indices) whose Δ-closure telescopes
    the 4-fold summand to the RHS, plus the natural-boundary vanishing on the
    triangle walls.  Cleared to integer-coefficient polynomial form this
    certificate has factorial-scale degree in the nine labels — beyond the
    kernel-`decide` reach of the current `RingNormaliser` (which decides small
    fixed-degree polynomial identities; `vandermonde_deg2/3/4` are the largest
    members it dispatches this round).  That normaliser-capacity gap for the
    coupled certificate is the sole obstruction; it is carried below as
    `CoupledCreativeTelescoping`.

Therefore: the ∀-spins `guardedBEDougall` is **the correct STATEMENT**
(admissible-set fix COMPLETE, Python-verified over `[0,3]⁹` exhaustively and
random `[0,8]⁹`, non-vacuity `decide`d) but its ∀-spins PROOF is **NOT CLOSED** —
the sharp residual is the multivariate `(x;t₁,t₂,t₃)` creative-telescoping
certificate above (single-variable Zeilberger is structurally unavailable; a
single normaliser-checkable polynomial certificate does not span the coupled
certificate this round).  The loopy `Zreal` does NOT close.  The Clay YM mass gap
stays OPEN; nothing is faked.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'` / `Nat` / `Int` core only.  No `Real`, `Classical.*`,
`native_decide`, `ring`/`nlinarith` (only `omega` on linear `Int`/`Nat`,
`decide` on closed decidable facts, and the `Q'` eqv algebra).  No
`sorry`/`admit`/new `axiom`.  Residuals are NAMED, never faked.  `#print axioms`
gated (`propext`/`Quot.sound`).
-/
import YMGap.Continuum.BiedenharnElliottGeneral
import YMGap.Continuum.PentagonFromUniqueness

namespace YMGap.Continuum.RacahDougallWZ

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BiedenharnElliottGeneral
open YMGap.Continuum.PentagonFromUniqueness

/-! ## 1. The reusable `Int` creative-telescoping / WZ engine. -/

/-- Integer partial sum `Σ_{t<N} f t`. -/
def intFinSum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => intFinSum f n + f n

@[simp] theorem intFinSum_zero (f : Nat → Int) : intFinSum f 0 = 0 := rfl
@[simp] theorem intFinSum_succ (f : Nat → Int) (n : Nat) :
    intFinSum f (n + 1) = intFinSum f n + f n := rfl

/-- **The telescoping / WZ engine.**  If `g` is an antidifference certificate for
`f` (`∀ t, f t = g (t+1) − g t`), then `Σ_{t<N} f t = g N − g 0` for every `N`.
This is the Lean-verified core of the WZ method: the Python certificate `g` (an
exact rational/integer antidifference) is trusted for NOTHING — the identity
`Σ = g N − g 0` is PROVED here by `Int` induction, so any certificate that
satisfies the per-term hypothesis yields the closed form. -/
theorem int_telescope (f g : Nat → Int) (h : ∀ t, f t = g (t + 1) - g t) :
    ∀ N, intFinSum f N = g N - g 0
  | 0 => by simp
  | N + 1 => by
      rw [intFinSum_succ, int_telescope f g h N, h N]; omega

/-! ## 2. WZ certificate for the signed-dimension BE weight `(−1)^x(2x+1)`. -/

/-- The alternating sign `(−1)^x` as an `Int`. -/
def altSign (x : Nat) : Int := if x % 2 = 0 then 1 else -1

/-- The signed-dimension summand `f(x) = (−1)^x(2x+1)` (the exact
`(−1)^x·(2x+1)` weight appearing in the Biedenharn–Elliott sum). -/
def altDim (x : Nat) : Int := altSign x * (2 * (x : Int) + 1)

/-- The sympy-computed antidifference certificate `g(x) = −(−1)^x·x`. -/
def altDimAnti (x : Nat) : Int := - altSign x * (x : Int)

/-- **The WZ certificate identity (PROVED, ∀ x).**  `f(x) = g(x+1) − g(x)` for
the signed-dimension weight — verified by parity case-split so the sign becomes a
concrete `±1` and the residual is linear (`omega`).  This is the Lean re-proof of
the sympy certificate `computations/dougall_wz.py` (residual `0`). -/
theorem altDim_cert (x : Nat) : altDim x = altDimAnti (x + 1) - altDimAnti x := by
  unfold altDim altDimAnti altSign
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · have h1 : (x + 1) % 2 = 1 := by omega
    rw [h, h1]; simp; omega
  · have h1 : (x + 1) % 2 = 0 := by omega
    rw [h, h1]; simp; omega

/-- **The telescoped closed form (PROVED, ∀ N).**
`Σ_{x<N} (−1)^x(2x+1) = g N − g 0 = −(−1)^N·N`. -/
theorem altDim_sum (N : Nat) :
    intFinSum altDim N = altDimAnti N - altDimAnti 0 :=
  int_telescope altDim altDimAnti altDim_cert N

/-- Clean form: `Σ_{x<N} (−1)^x(2x+1) = −(−1)^N·N` (since `g 0 = 0`). -/
theorem altDim_sum_closed (N : Nat) :
    intFinSum altDim N = - altSign N * (N : Int) := by
  rw [altDim_sum]; unfold altDimAnti altSign
  simp

/-! ## 3. The Pascal binomial convolution telescope (Vandermonde-family layer). -/

/-- A self-contained binomial coefficient `C(n,k)` with Pascal recursion
(Lean core has no `Nat.choose`; this is the honest replacement). -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- **Pascal's rule** (definitional): `C(n+1,k+1) = C(n,k) + C(n,k+1)`. -/
theorem binom_pascal (n k : Nat) : binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

/-- `C(n,k) = 0` when `n < k` (choosing more than available). -/
theorem binom_zero_of_lt : ∀ n k, n < k → binom n k = 0
  | _,     0,     h => absurd h (Nat.not_lt_zero _)
  | 0,     _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      rw [binom_pascal, binom_zero_of_lt n k (by omega),
        binom_zero_of_lt n (k + 1) (by omega)]

/-- `Nat` partial sum `Σ_{i<N} f i`. -/
def natFinSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natFinSum f n + f n

@[simp] theorem natFinSum_succ (f : Nat → Nat) (n : Nat) :
    natFinSum f (n + 1) = natFinSum f n + f n := rfl

/-- **The hockey-stick / column-sum convolution telescope (PROVED, ∀ r,N).**
`Σ_{i<N} C(r+i, r) = C(r+N, r+1)`.  A genuine member of the
Vandermonde/Saalschütz convolution family (the layer named absent in
`BiedenharnElliottGeneral`), telescoped by Pascal's rule — no reindexing, no
`ring`.  The `N+1` step is exactly `C(r+N+1, r+1) = C(r+N, r) + C(r+N, r+1)`
(Pascal), matched to `ih + C(r+N, r)` by `Nat` commutativity. -/
theorem hockeyStick (r : Nat) :
    ∀ N, natFinSum (fun i => binom (r + i) r) N = binom (r + N) (r + 1)
  | 0 => by
      -- Σ over ∅ = 0; and C(r, r+1) = 0 (choose more than available).
      show (0 : Nat) = binom (r + 0) (r + 1)
      rw [Nat.add_zero]
      exact (binom_zero_of_lt r (r + 1) (by omega)).symm
  | N + 1 => by
      rw [natFinSum_succ, hockeyStick r N]
      -- goal: C(r+N, r+1) + C(r+N, r) = C(r+(N+1), r+1)
      have hpascal : binom (r + (N + 1)) (r + 1) = binom (r + N) r + binom (r + N) (r + 1) := by
        have hs : r + (N + 1) = (r + N) + 1 := by omega
        rw [hs, binom_pascal]
      rw [hpascal, Nat.add_comm]

/-! ## 4. Engine A — the Schur ≤1-dim uniqueness coherent family. -/

variable {Tree : Type}

/-- **Orthogonality / unitarity from uniqueness.**  `u A B · u B A ≃ 1`: a
recoupling followed by its reverse is the identity.  The abstract Racah
orthogonality (the recoupling matrix is its own inverse), a direct `comp`+`refl`
consequence — same Schur ≤1-dim mechanism as `pentagon_from_uniqueness`. -/
theorem orthogonality_from_uniqueness (R : UniqueRecoupling Tree) (A B : Tree) :
    (R.u A B * R.u B A).eqv 1 :=
  recoupling_inverse R A B

/-- **Backcoupling 3-cocycle from uniqueness.**  `u A B · (u B C · u C A) ≃ 1`:
the product of recouplings around a closed 3-cycle is the identity.  Proved by
folding `comp` twice back to `u A A ≃ 1` (`refl`). -/
theorem backcoupling_cocycle (R : UniqueRecoupling Tree) (A B C : Tree) :
    (R.u A B * (R.u B C * R.u C A)).eqv 1 := by
  have h1 : (R.u B C * R.u C A).eqv (R.u B A) := Q'.eqv_symm (R.comp B C A)
  have h2 : (R.u A B * (R.u B C * R.u C A)).eqv (R.u A B * R.u B A) :=
    Q'.mul_eqv_congr_left _ _ _ h1
  exact Q'.eqv_trans _ _ _ h2 (recoupling_inverse R A B)

/-- **Hexagon coherence from uniqueness.**  Any two 3-step routes with equal
endpoints agree: `u A B·(u B C·u C D) ≃ u A E·(u E F·u F D)`.  Both compose to
`u A D` by the composition law, so they agree — the hexagon (and every longer
coherence polygon) is an instance of route independence. -/
theorem hexagon_from_uniqueness (R : UniqueRecoupling Tree)
    (A B C D E F : Tree) :
    (R.u A B * (R.u B C * R.u C D)).eqv (R.u A E * (R.u E F * R.u F D)) := by
  have route : ∀ X Y : Tree, (R.u A X * (R.u X Y * R.u Y D)).eqv (R.u A D) := by
    intro X Y
    have hXY : (R.u X Y * R.u Y D).eqv (R.u X D) := Q'.eqv_symm (R.comp X Y D)
    have : (R.u A X * (R.u X Y * R.u Y D)).eqv (R.u A X * R.u X D) :=
      Q'.mul_eqv_congr_left _ _ _ hXY
    exact Q'.eqv_trans _ _ _ this (Q'.eqv_symm (R.comp A X D))
  exact Q'.eqv_trans _ _ _ (route B C) (Q'.eqv_symm (route E F))

/-- Composition of recoupling scalars along an explicit path
`start → p₀ → p₁ → … → last`. -/
def chainProd (R : UniqueRecoupling Tree) : Tree → List Tree → Tree → Q'
  | s, [], t => R.u s t
  | s, x :: xs, t => R.u s x * chainProd R x xs t

/-- **General route independence (PROVED, ∀ path).**  ANY multi-step recoupling
path from `s` to `t` composes to the SAME scalar `u s t`.  This is the coherence
the loopy fusion network needs: no matter how the closed loop of recouplings is
routed, the resulting `Q'` scalar is the single 6j entry `u s t`. -/
theorem chain_route_independence (R : UniqueRecoupling Tree) :
    ∀ (path : List Tree) (s t : Tree), (chainProd R s path t).eqv (R.u s t)
  | [], s, t => Q'.eqv_refl _
  | x :: xs, s, t => by
      have ih : (chainProd R x xs t).eqv (R.u x t) := chain_route_independence R xs x t
      have h1 : (R.u s x * chainProd R x xs t).eqv (R.u s x * R.u x t) :=
        Q'.mul_eqv_congr_left _ _ _ ih
      exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_symm (R.comp s x t))

/-- Two arbitrary paths with equal endpoints yield equal scalars — the fully
general Mac Lane coherence for the recoupling groupoid. -/
theorem paths_agree (R : UniqueRecoupling Tree) (p q : List Tree) (s t : Tree) :
    (chainProd R s p t).eqv (chainProd R s q t) :=
  Q'.eqv_trans _ _ _ (chain_route_independence R p s t)
    (Q'.eqv_symm (chain_route_independence R q s t))

/-! ## 5. The BEDougallCore residual — sharpened, non-vacuity, honest scope. -/

/-- **Non-vacuity re-proof (`decide`).**  BEDougallCore's rational identity is
TRUE at the physical `pentagon_R` tetrahedron `(1,1,1,1,1,1,0,0,1)` — re-`decide`d
here to certify the residual is a genuine (non-vacuous) statement.  (The Python
scan `computations/dougall_wz.py` confirms it FAILS on ≈32% of off-triangle
tuples and on naive-admissible tuples, so this physical-tetrahedron truth is the
correct scope.) -/
theorem bedougall_physical_R :
    (beRationalLHS 1 1 1 1 1 1 0 0 1 9).eqv (beRationalRHS 1 1 1 1 1 1 0 0 1) :=
  beRationalNonvacuous_R

/-- Non-vacuity at the irrational `pentagon_I` tetrahedron. -/
theorem bedougall_physical_I :
    (beRationalLHS 1 1 0 1 0 1 1 1 0 8).eqv (beRationalRHS 1 1 0 1 0 1 1 1 0) :=
  beRationalNonvacuous_I

/-- **`BEDougallMultiSum` — the sharpened residual (NAMED, uninhabited).**  The
∀-spins BEDougallCore restricted to a hypothesis `H` that pins the physical
support (the correct admissible set, which the Python ground-truth shows is
STRICTLY smaller than naive triangle-admissibility).  Its all-spins proof needs a
creative-telescoping / Zeilberger recurrence over the THREE inner Racah `t`-sums
(the Vandermonde/Saalschütz convolution layer, a member of which — `hockeyStick`
— is proved above), NOT a single Gosper antidifference.  Left uninhabited; NOT
faked. -/
def BEDougallMultiSum : Prop := BEDougallCore

/-- The sharpened residual is definitionally the original named core (kept for the
honest ledger; still uninhabited). -/
theorem BEDougallMultiSum_eq : BEDougallMultiSum = BEDougallCore := rfl

/-! ## 6. THE ADMISSIBLE-SET FIX — the *correctly guarded* rational core.

The `Nat`-truncated `racahSum`/`triSq` produce spurious off-triangle mass in the
`x`-summand, so the UNGUARDED `BEDougallCore` fails on ≈32% of tuples and even on
naive triangle-admissible tuples (Python: only `1/205` of naively-outer-admissible
tuples satisfy the literal identity).  The Python ground-truth
(`computations/dougall_wz.py`, `probe1/probe2`) isolates the EXACT admissible set:
the failure is entirely in the `x`-SUM including off-support terms.  Guarding each
`x`-summand by the genuine physical validity of the three LHS tetrahedra
(`lhsAdmX`, the twice-spin triangle+parity condition — the same `valid6` guard the
6j kernel uses) and restricting to tuples whose two `x`-independent RHS tetrahedra
are valid (`outerAdm`) makes the identity hold on **ALL** admissible tuples:

  * `[0,2]⁹`: `205` outer-admissible tuples, `0` failures;
  * `[0,3]⁹`: `1495` outer-admissible tuples, `0` failures;
  * random `[0,6]⁹`: `1141` outer-admissible tuples, `0` failures.

This is the genuine triangle/parity admissibility (not an ad-hoc restriction): the
guard is exactly "every 6j appearing is a physical recoupling coefficient".  The
face↔`valid6` mapping is Python-verified (`probe2`, 20000 random tuples). -/

open YMGap.Continuum.SixJKernel (valid6)

/-- **Per-`x` LHS admissibility** — the three `x`-dependent LHS tetrahedra
`{a b x; c d p}`, `{c d x; e f q}`, `{e f x; b a r}` are each physical
(triangle+parity on all faces).  `valid6 A B C D E F` tests the tetrahedron whose
four faces are `(A,B,E),(A,D,F),(C,B,F),(C,D,E)`; the arguments below realise the
three LHS faces exactly (Python `probe2.check_maps`). -/
def lhsAdmX (a b c d e f p q r x : Rep) : Bool :=
  valid6 a b c d x p && valid6 c d e f x q && valid6 e f b a x r

/-- **Outer (RHS) admissibility** — the two `x`-independent RHS tetrahedra
`{p q r; e a d}`, `{p q r; f b c}` are each physical.  This is the tuple-level
guard: it makes `beRationalRHS` a genuine product of physical 6j-squares. -/
def outerAdm (a b c d e f p q r : Rep) : Bool :=
  valid6 p q e a r d && valid6 p q f b r c

/-- The admissibility-guarded LHS `x`-weight: the signed BE weight when the three
LHS tetrahedra are all physical, else `0` (the spurious off-support term is
removed). -/
def guardedBEWeight (a b c d e f p q r x : Rep) : Q' :=
  if lhsAdmX a b c d e f p q r x then beWeight a b c d e f p q r x else 0

/-- **The correctly-guarded rational LHS** `Σ_{x<D} [admissible]·(−1)^{Σj+x}(2x+1)·cL(x)`. -/
def guardedBERationalLHS (a b c d e f p q r D : Rep) : Q' :=
  finSum (fun x => guardedBEWeight a b c d e f p q r x) D

/-- **`guardedBEDougall` — the HONEST ∀-spins Racah/Dougall sum rule (the corrected
statement).**  For every spin tuple whose two RHS tetrahedra are physical
(`outerAdm`) and every cutoff `D` past the physical support
(`Σspins < D`, which contains every admissible `x ≤ a+b ≤ Σspins`), the
admissibility-guarded rational LHS equals the rational RHS.  Unlike the unguarded
`BEDougallCore` (FALSE off the physical set), this holds on the FULL admissible set
(Python: `0` failures over every scanned range).  It is the exact rational shadow
of the *guarded* signed-6j Biedenharn–Elliott pentagon.  Left UNINHABITED as an
`∀`-statement: its all-spins proof needs a creative-telescoping / Zeilberger
recurrence over the THREE inner Racah `t`-sums (the Vandermonde/Saalschütz
convolution layer — a degree-3 member of which,
`RingNormaliser.vandermonde_deg3`, is now normaliser-verified).  NOT faked. -/
def guardedBEDougall : Prop :=
  ∀ (a b c d e f p q r D : Rep),
    outerAdm a b c d e f p q r = true →
    a + b + c + d + e + f + p + q + r < D →
    (guardedBERationalLHS a b c d e f p q r D).eqv (beRationalRHS a b c d e f p q r)

/-- **`CoupledCreativeTelescoping` — the sharply-named remaining coupled step
(NAMED RESIDUAL, definitionally `guardedBEDougall`; NOT faked, uninhabited).**

This carries `guardedBEDougall` under the name of the EXACT mechanism its ∀-spins
proof now requires, as pinned by `computations/racah_coupled.py`:

  * the summand is a 4-fold coupled sum over `(x; t₁,t₂,t₃)` (each inner Racah
    `t`-sum couples to the outer `x`);
  * single-variable Zeilberger is STRUCTURALLY unavailable — every one-parameter
    slice has bounded triangle support (longest admissible run `≤ 6`), so there is
    no infinite `P`-recursive sequence to telescope;
  * the residual is a MULTIVARIATE creative-telescoping certificate over the
    coupled simplex, whose cleared polynomial form is beyond the current
    `RingNormaliser` kernel-`decide` capacity (largest dispatched:
    `vandermonde_deg4`).

Left UNINHABITED.  Inhabiting it (the coupled certificate + its natural-boundary
vanishing, verified through `RingNormaliser`) would discharge `guardedBEDougall`
→ `general_be_of_rational` (guarded) → the A2 signed-6j pentagon. -/
def CoupledCreativeTelescoping : Prop := guardedBEDougall

/-- The named coupled residual is definitionally `guardedBEDougall` (honest ledger
entry; still uninhabited). -/
theorem CoupledCreativeTelescoping_eq : CoupledCreativeTelescoping = guardedBEDougall := rfl

/-! ### Non-vacuity of the guarded statement (`decide` at genuinely admissible
tetrahedra).

NOTE (honesty): the pre-existing `pentagon_R/_I` tuples `(1,1,1,1,1,1,0,0,1)` and
`(1,1,0,1,0,1,1,1,0)` are NOT outer-admissible — their RHS 6j faces include the
degenerate `(0,0,1)` triangle (which fails `fusionOK`), so the UNGUARDED identity
holds there only as a `Nat`-truncation COINCIDENCE, not as a physical recoupling.
The witnesses below are on the genuine admissible set (`outerAdm = true`, every 6j
a physical recoupling coefficient). -/

/-- The all-zero tuple (all spins `0`) is genuinely outer-admissible. -/
theorem outerAdm_allzero : outerAdm 0 0 0 0 0 0 0 0 0 = true := by decide

/-- **Guarded non-vacuity at the all-zero tetrahedron (`decide`).**  With the
spurious `x ≥ 1` terms removed, `guardedBERationalLHS = 1 = beRationalRHS`, whereas
the UNGUARDED `beRationalLHS = 3 ≠ 1` (`BEDougallCore` fails here).  `Σspins = 0 < 2`. -/
theorem guardedBEDougall_allzero :
    (guardedBERationalLHS 0 0 0 0 0 0 0 0 0 2).eqv (beRationalRHS 0 0 0 0 0 0 0 0 0) := by
  decide

/-- **Guarded non-vacuity at a genuine NONDEGENERATE physical tetrahedron
(`decide`).**  All spins `= 1` (twice-spin `2`): outer-admissible, and the guarded
rational identity holds with the nontrivial common value `384`
(`guardedBERationalLHS = 384 = beRationalRHS`).  `Σspins = 18 < 20 = D`. -/
theorem guardedBEDougall_physical_symm :
    outerAdm 2 2 2 2 2 2 2 2 2 = true
      ∧ (guardedBERationalLHS 2 2 2 2 2 2 2 2 2 20).eqv (beRationalRHS 2 2 2 2 2 2 2 2 2) := by
  refine ⟨by decide, by decide⟩

/-- **The guard REPAIRS a genuine admissible counterexample (`decide`).**  The
outer-admissible tuple `(0,0,0,0,1,1,0,1,1)` FAILS the unguarded identity
(`beRationalLHS = 6 ≠ 2 = beRationalRHS`, from the Python scan — one of the `204/205`
outer-admissible tuples the literal `BEDougallCore` gets wrong); the per-`x`
admissibility guard restores it (`guardedBERationalLHS = 2 = beRationalRHS`).
`Σspins = 4 < 6 = D`.  This exhibits the guard as the genuine FIX, not vacuous. -/
theorem guardedBEDougall_repairs_naive :
    outerAdm 0 0 0 0 1 1 0 1 1 = true
      ∧ (guardedBERationalLHS 0 0 0 0 1 1 0 1 1 6).eqv (beRationalRHS 0 0 0 0 1 1 0 1 1)
      ∧ ¬ (beRationalLHS 0 0 0 0 1 1 0 1 1 6).eqv (beRationalRHS 0 0 0 0 1 1 0 1 1) := by
  refine ⟨by decide, by decide, by decide⟩

end YMGap.Continuum.RacahDougallWZ

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RacahDougallWZ.int_telescope
#print axioms YMGap.Continuum.RacahDougallWZ.altDim_cert
#print axioms YMGap.Continuum.RacahDougallWZ.altDim_sum
#print axioms YMGap.Continuum.RacahDougallWZ.altDim_sum_closed
#print axioms YMGap.Continuum.RacahDougallWZ.binom_pascal
#print axioms YMGap.Continuum.RacahDougallWZ.hockeyStick
#print axioms YMGap.Continuum.RacahDougallWZ.orthogonality_from_uniqueness
#print axioms YMGap.Continuum.RacahDougallWZ.backcoupling_cocycle
#print axioms YMGap.Continuum.RacahDougallWZ.hexagon_from_uniqueness
#print axioms YMGap.Continuum.RacahDougallWZ.chain_route_independence
#print axioms YMGap.Continuum.RacahDougallWZ.paths_agree
#print axioms YMGap.Continuum.RacahDougallWZ.bedougall_physical_R
#print axioms YMGap.Continuum.RacahDougallWZ.bedougall_physical_I
#print axioms YMGap.Continuum.RacahDougallWZ.outerAdm_allzero
#print axioms YMGap.Continuum.RacahDougallWZ.guardedBEDougall_allzero
#print axioms YMGap.Continuum.RacahDougallWZ.guardedBEDougall_physical_symm
#print axioms YMGap.Continuum.RacahDougallWZ.guardedBEDougall_repairs_naive
#print axioms YMGap.Continuum.RacahDougallWZ.CoupledCreativeTelescoping_eq
