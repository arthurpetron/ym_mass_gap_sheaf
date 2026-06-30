/-
Constructive **Schur product** and **Hadamard exponential** positivity over
`Q'` matrices — the Mathlib-free transfer of the two positivity tools used by
the external 4D-GFF formalization (Douglas–Hoback–Mei–Nissim, "Formalization of
QFT", arXiv:2603.15770; repository `mrdouglasny/OSforGFF`) to lift covariance
reflection positivity to the generating functional.

# What this module transfers (and from where)

`OSforGFF` proves two classical positivity facts and uses them to push the
Gaussian covariance's reflection positivity up to the generating functional:

  * `General/SchurProduct` — the **Schur product theorem**: the Hadamard
    (entrywise) product of two positive-semidefinite matrices is PSD.
  * `General/HadamardExp` — the **Hadamard exponential**: the entrywise `exp`
    of a PSD matrix is PSD (a convergent sum of Hadamard powers).

Their proofs go through Mathlib's spectral / `Matrix.PosSemidef` API (classical
diagonalization).  THIS module re-establishes BOTH **constructively** and
Mathlib-free, by carrying "PSD" as an EXPLICIT Gram / sum-of-outer-products
**witness** (`GramRep`) rather than via classical spectral extraction:

    a matrix `M` is `GramRep` when `M i j = Σ_{k<r} d_k · (v_k_i · v_k_j)`
    with rational weights `d_k ≥ 0` and rational coordinate vectors `v_k`.

This is precisely the LDLᵀ / weighted-sum-of-squares form already consumed by
`Constructive.SumOfSquares.geRat_sos`.  With PSD carried this way:

  * **Quadratic-form positivity** (`gramPSD_quadForm_nonneg`) is the SOS
    rearrangement `Σ_{ij} c_i c_j Σ_k d_k v_k_i v_k_j = Σ_k d_k (Σ_i c_i v_k_i)²
    ≥ 0` — no spectral theorem.
  * The **Schur product theorem** (`schur_product`) is the Khatri–Rao identity
    `(Σ_k d_k v_k v_kᵀ) ∘ (Σ_l e_l u_l u_lᵀ) = Σ_{k,l} (d_k e_l)
    (v_k∘u_l)(v_k∘u_l)ᵀ` — manifestly a Gram matrix; constructive, exact.
  * The **Hadamard power** (`hadamardPow_gramRep`) is iterated Schur; the
    truncated **Hadamard exponential** `Σ_{n<N} G^{∘n}/n!`
    (`hadamardExpTrunc_gramRep`) is a nonnegatively-scaled direct sum of
    Hadamard powers — each a Gram, the sum a Gram.

# The application to OS2 (honest scope; see the foot of the file)

The audit (`OSAxiomAudit`) flags Schur/Hadamard as the standard route that, in
diagonalized form, this library already uses for OS2
(`ReflectionPositivity.diagReflForm_nonneg`).  The genuine question is whether it
RETIRES the OFF-diagonal character-PRODUCT Gram wall
(`MomentSquarePSD.MomentSquarePos` / the `P_N` wall): `G_{μν} = Σ_c N^c_{μν}
m_c`, the fusion-weighted product form.

The honest finding, **machine-checked here** (`fusion1_not_gramRep`): the SU(2)
fusion-channel matrices `N^c` are NOT individually positive-semidefinite — the
spin-½ channel `N^1` is the path-graph adjacency matrix, with the explicit
negative quadratic form `Q(1,−1) = −2`.  Hence `G = Σ_c m_c N^c` is a
nonnegative combination of NON-PSD matrices, and the Schur/Hadamard machinery
does NOT, by itself, exhibit it as a Gram: the off-diagonal wall genuinely
needs the heat-kernel WEIGHT conspiracy (equivalently pointwise `K_t ≥ 0`),
exactly the analytic input isolated as `MomentSquarePSD.UniformGramSOS`.  So the
wall is **REDUCED and sharpened, not retired**; the DIAGONAL OS2 already proved
(`ReflectionPositivity.reflSchwinger_nonneg`) is the part the algebra closes.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (inherited from the reused `Q'`/`finSum`
algebra).  No `Classical.*`, no `sorryAx`, no `native_decide`, no Mathlib.
-/

import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.SumOfSquares
import YMGap.RG.TonelliFactor
import YMGap.Continuum.ReflectionPositivity
import YMGap.Continuum.OSAxiomAudit
import YMGap.Continuum.GramReduction
import YMGap.Continuum.MomentSquarePSD

namespace YMGap.Continuum.SchurHadamardTransfer

open YMGap.Constructive
open YMGap.Constructive.RationalTail

/-! ## Multiplicative rearrangement atoms (`Q'.eqv`)

`Q'` multiplication is commutative/associative only up to `Q'.eqv`
(cross-multiplication), so the Khatri–Rao bookkeeping needs two explicit
product rearrangements, built from the `mul_assoc_eqv` / `mul_comm_eqv` atoms. -/

/-- `(p·q)·(a·b) ≃ (a·p)·(b·q)` — the 4-factor regrouping behind the Khatri–Rao
identity (pairing each Gram factor's two coordinates). -/
theorem mul4_rearrange (p q a b : Q') :
    ((p * q) * (a * b)).eqv ((a * p) * (b * q)) := by
  have inner : (q * (a * b)).eqv (a * (b * q)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv q a b))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (q * a) (a * q) b (Q'.mul_comm_eqv q a))
        (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a q b)
          (Q'.mul_eqv_congr_left a (q * b) (b * q) (Q'.mul_comm_eqv q b))))
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv p q (a * b))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left p (q * (a * b)) (a * (b * q)) inner)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv p a (b * q)))
        (Q'.mul_eqv_congr_right (p * a) (a * p) (b * q) (Q'.mul_comm_eqv p a))))

/-- `(a·b)·(d·(p·q)) ≃ d·((a·p)·(b·q))` — pull the weight `d` to the front and
regroup the coordinates (the per-term Khatri–Rao identity). -/
theorem mul6_rearrange (a b d p q : Q') :
    ((a * b) * (d * (p * q))).eqv (d * ((a * p) * (b * q))) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (a * b) (d * (p * q)))
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv d (p * q) (a * b))
      (Q'.mul_eqv_congr_left d ((p * q) * (a * b)) ((a * p) * (b * q))
        (mul4_rearrange p q a b)))

/-! ## Constructive PSD-as-Gram over `Q'`

A symmetric `Q'` matrix `M` is positive-semidefinite, *constructively*, when it
is exhibited as an explicit nonnegatively-weighted sum of outer products
(rank-`r` Gram / LDLᵀ form).  Carried as `Type`-level data (AGENTS.md Rule 8),
never a `Prop` `∃`. -/

/-- **Constructive PSD-as-Gram witness.**  Rank `r`, nonnegative rational
weights `d_k`, and rational coordinate vectors `v_k` (`v k i` is the `i`-th
coordinate of the `k`-th vector), with the defining equation
`M i j ≃ Σ_{k<r} d_k · (v_k_i · v_k_j)`.  This is the constructive carrier of
"`M` is PSD" used in place of classical spectral/Cholesky extraction
(cf. `OSforGFF` `Matrix.PosSemidef`). -/
structure GramRep (M : Nat → Nat → Q') where
  /-- Number of outer-product (rank-1) terms. -/
  r : Nat
  /-- Nonnegative weights (the LDLᵀ pivots). -/
  d : Nat → Q'
  /-- Each weight is `≥ 0`. -/
  hd : ∀ k, (0 : Q') ≤ d k
  /-- The coordinate vectors `v_k` (`v k i = (v_k)_i`). -/
  v : Nat → Nat → Q'
  /-- The Gram identity `M i j = Σ_{k<r} d_k · (v_k_i · v_k_j)`. -/
  hM : ∀ i j,
    (M i j).eqv (finSum (fun k => d k * (v k i * v k j)) r)

/-- The Gram quadratic form `Q_N(c) = Σ_{i,j<N} c_i c_j M_{ij}` (the GNS energy
of `c` under `M`). -/
def gramQuadForm (M : Nat → Nat → Q') (c : Nat → Q') (N : Nat) : Q' :=
  finSum (fun i => finSum (fun j => (c i * c j) * M i j) N) N

/-- The linear functional `L_k(c) = Σ_{i<N} c_i v_k_i` whose square the Gram
form decomposes into. -/
def linForm (c v : Nat → Q') (N : Nat) : Q' :=
  finSum (fun i => c i * v i) N

/-! ### The SOS rearrangement

`Σ_{ij} c_i c_j Σ_k d_k v_k_i v_k_j  =  Σ_k d_k (Σ_i c_i v_k_i)²` — proved by
substituting the Gram identity, regrouping each term (`mul6_rearrange`), swapping
the `k`-sum outermost (`finSum_swap`), and collapsing the inner `i,j` sums into
`L_k²` (pulling constants out via `const_mul_finSum` / `finSum_mul_const`). -/

/-- **The SOS identity.**  The Gram quadratic form of a `GramRep` matrix equals
the nonnegatively-weighted sum of squares `Σ_{k<r} d_k · L_k²`, where
`L_k = Σ_{i<N} c_i v_k_i`. -/
theorem gramQuadForm_eq_sos {M : Nat → Nat → Q'} (rep : GramRep M)
    (c : Nat → Q') (N : Nat) :
    (gramQuadForm M c N).eqv
      (finSum (fun k => rep.d k *
        (finSum (fun i => c i * rep.v k i) N * finSum (fun i => c i * rep.v k i) N)) rep.r) := by
  obtain ⟨r, d, _hd, v, hM⟩ := rep
  -- Step h1: substitute the Gram identity and regroup each term to
  --   `U i j k = d_k · ((c_i v_k_i)·(c_j v_k_j))`.
  have h1 : (gramQuadForm M c N).eqv
      (finSum (fun i => finSum (fun j =>
        finSum (fun k => d k * ((c i * v k i) * (c j * v k j))) r) N) N) := by
    refine finSum_eqv_congr _ _ (fun i => ?_) N
    refine finSum_eqv_congr _ _ (fun j => ?_) N
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (c i * c j) (M i j)
        (finSum (fun k => d k * (v k i * v k j)) r) (hM i j)) ?_
    refine Q'.eqv_trans _ _ _
      (const_mul_finSum (fun k => d k * (v k i * v k j)) (c i * c j) r) ?_
    exact finSum_eqv_congr _ _
      (fun k => mul6_rearrange (c i) (c j) (d k) (v k i) (v k j)) r
  -- Step h2: swap `j` and `k` (inner two sums, ranges N and r).
  have h2 : (finSum (fun i => finSum (fun j =>
        finSum (fun k => d k * ((c i * v k i) * (c j * v k j))) r) N) N).eqv
      (finSum (fun i => finSum (fun k =>
        finSum (fun j => d k * ((c i * v k i) * (c j * v k j))) N) r) N) := by
    refine finSum_eqv_congr _ _ (fun i => ?_) N
    exact finSum_swap (fun j k => d k * ((c i * v k i) * (c j * v k j))) N r
  -- Step h3: swap `i` and `k` (outer two sums, ranges N and r).
  have h3 : (finSum (fun i => finSum (fun k =>
        finSum (fun j => d k * ((c i * v k i) * (c j * v k j))) N) r) N).eqv
      (finSum (fun k => finSum (fun i =>
        finSum (fun j => d k * ((c i * v k i) * (c j * v k j))) N) N) r) :=
    finSum_swap
      (fun i k => finSum (fun j => d k * ((c i * v k i) * (c j * v k j))) N) N r
  -- Step h4: per-`k` collapse `Σ_{i<N} Σ_{j<N} U = d_k · (L_k · L_k)`.
  have h4 : ∀ k,
      (finSum (fun i => finSum (fun j => d k * ((c i * v k i) * (c j * v k j))) N) N).eqv
        (d k * (finSum (fun i => c i * v k i) N * finSum (fun i => c i * v k i) N)) := by
    intro k
    -- inner `j`-sum: `Σ_j d_k·((c_i v_k_i)(c_j v_k_j)) = d_k·((c_i v_k_i)·L_k)`
    have step_j : ∀ i,
        (finSum (fun j => d k * ((c i * v k i) * (c j * v k j))) N).eqv
          (d k * ((c i * v k i) * finSum (fun i => c i * v k i) N)) := by
      intro i
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (const_mul_finSum
          (fun j => (c i * v k i) * (c j * v k j)) (d k) N)) ?_
      exact Q'.mul_eqv_congr_left (d k) _ _
        (Q'.eqv_symm (const_mul_finSum (fun j => c j * v k j) (c i * v k i) N))
    -- congruence on the outer `i`-sum, then pull `d_k` out and collapse to `L_k²`.
    refine Q'.eqv_trans _ _ _ (finSum_eqv_congr _ _ step_j N) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (const_mul_finSum
        (fun i => (c i * v k i) * finSum (fun i => c i * v k i) N) (d k) N)) ?_
    exact Q'.mul_eqv_congr_left (d k) _ _
      (Q'.eqv_symm (finSum_mul_const
        (fun i => c i * v k i) (finSum (fun i => c i * v k i) N) N))
  -- assemble
  exact Q'.eqv_trans _ _ _ h1
    (Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _ h3 (finSum_eqv_congr _ _ h4 r)))

/-- **Constructive PSD: the Gram quadratic form is nonnegative.**  For any
`GramRep` matrix `M`, `Σ_{i,j<N} c_i c_j M_{ij} ≥ 0` for every real coefficient
vector `c` — by the SOS identity `= Σ_k d_k L_k² ≥ 0` (each `d_k ≥ 0`,
`L_k² ≥ 0`).  This is the constructive content of "`M` PSD ⟹ positive quadratic
form", with no classical spectral theorem. -/
theorem gramPSD_quadForm_nonneg {M : Nat → Nat → Q'} (rep : GramRep M)
    (c : Nat → Q') (N : Nat) :
    (0 : Q') ≤ gramQuadForm M c N := by
  have hpos : (0 : Q') ≤ finSum (fun k => rep.d k *
      (finSum (fun i => c i * rep.v k i) N * finSum (fun i => c i * rep.v k i) N)) rep.r :=
    YMGap.RG.finSum_nonneg _
      (fun k => Q'.mul_nonneg _ _ (rep.hd k)
        (SumOfSquares.q_mul_self_nonneg _)) rep.r
  exact Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv (Q'.eqv_symm (gramQuadForm_eq_sos rep c N)))

/-! ## `finSum` flattening / product helpers (for the Schur and direct-sum reps)

Two structural identities on `Q'` finite sums beyond `FinSumAlg`:

  * `finSum_mul_finSum` — `(Σ_k a_k)(Σ_l b_l) = Σ_k Σ_l a_k b_l`;
  * `finSum_flatten` — `Σ_{p<s·r} F(p/s)(p%s) = Σ_{k<r} Σ_{l<s} F k l`,
  * `finSum_add_range` — `Σ_{p<a+b} f = Σ_{p<a} f + Σ_{p<b} f(a+·)`.

`finSum_flatten` turns the nested Khatri–Rao double sum into the single rank-`s·r`
Gram sum the `GramRep` structure carries; `finSum_add_range` does the same for the
rank-`r+s` direct sum. -/

/-- `(Σ_{k<r} a_k)·(Σ_{l<s} b_l) ≃ Σ_{k<r} Σ_{l<s} a_k·b_l`. -/
theorem finSum_mul_finSum (a b : Nat → Q') (r s : Nat) :
    ((finSum a r) * (finSum b s)).eqv
      (finSum (fun k => finSum (fun l => a k * b l) s) r) :=
  Q'.eqv_trans _ _ _ (finSum_mul_const a (finSum b s) r)
    (finSum_eqv_congr _ _ (fun k => const_mul_finSum b (a k) s) r)

/-- Bounded congruence: if `f i ≃ g i` for every `i < n`, then the partial sums
agree.  (`finSum_eqv_congr` needs the equality at all indices; this only needs it
on the summed range.) -/
theorem finSum_congr_lt (f g : Nat → Q')
    (n : Nat) (h : ∀ i, i < n → (f i).eqv (g i)) :
    (finSum f n).eqv (finSum g n) := by
  induction n with
  | zero => exact Q'.eqv_refl _
  | succ m ih =>
    have hlt : ∀ i, i < m → (f i).eqv (g i) :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (finSum f m) (finSum g m) (f m) (ih hlt))
      (Q'.add_eqv_congr_left (finSum g m) (f m) (g m) (h m (Nat.lt_succ_self m)))

/-- `Σ_{p<a+b} f = (Σ_{p<a} f) + (Σ_{i<b} f(a+i))` — split a partial sum at `a`. -/
theorem finSum_add_range (f : Nat → Q') (a : Nat) :
    ∀ b, (finSum f (a + b)).eqv (finSum f a + finSum (fun i => f (a + i)) b)
  | 0 => by
      show (finSum f a).eqv (finSum f a + 0)
      rw [Q'.add_zero']; exact Q'.eqv_refl _
  | b + 1 => by
      -- `finSum f (a + (b+1)) = finSum f (a+b) + f (a+b)`
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (finSum f (a + b))
          (finSum f a + finSum (fun i => f (a + i)) b) (f (a + b))
          (finSum_add_range f a b)) ?_
      -- `(Σa + Σb) + f(a+b) ≃ Σa + (Σb + f(a+b))`
      exact Q'.add_assoc_eqv (finSum f a) (finSum (fun i => f (a + i)) b) (f (a + b))

/-- **The flattening identity.**  `Σ_{p<s·r} F(p/s)(p%s) ≃ Σ_{k<r} Σ_{l<s} F k l`
— the reindexing that turns the nested Khatri–Rao sum into a single rank-`s·r`
Gram sum.  Induction on `r`, peeling a length-`s` block and using the Euclidean
identities `(s·r+i)/s = r`, `(s·r+i)%s = i` for `i < s`. -/
theorem finSum_flatten (F : Nat → Nat → Q') (s : Nat) :
    ∀ r, (finSum (fun p => F (p / s) (p % s)) (s * r)).eqv
        (finSum (fun k => finSum (fun l => F k l) s) r)
  | 0 => Q'.eqv_refl _
  | r + 1 => by
      -- `s * (r+1) = s*r + s` (defeq); split the last length-`s` block.
      refine Q'.eqv_trans _ _ _
        (finSum_add_range (fun p => F (p / s) (p % s)) (s * r) s) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (finSum (fun i => F ((s * r + i) / s) ((s * r + i) % s)) s)
          (finSum_flatten F s r)) ?_
      -- the new block `Σ_{i<s} F((s·r+i)/s)((s·r+i)%s) ≃ Σ_{l<s} F r l`
      have hblock : (finSum (fun i => F ((s * r + i) / s) ((s * r + i) % s)) s).eqv
          (finSum (fun l => F r l) s) := by
        refine finSum_congr_lt _ _ s (fun i hi => ?_)
        have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
        have hdiv : (s * r + i) / s = r := by
          rw [Nat.mul_add_div hs, Nat.div_eq_of_lt hi]; omega
        have hmod : (s * r + i) % s = i := by
          rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hi
        rw [hdiv, hmod]; exact Q'.eqv_refl _
      exact Q'.add_eqv_congr_left _ _ _ hblock

/-! ## Two more product rearrangements for Khatri–Rao -/

/-- The interchange law `(a·b)·(c·d) ≃ (a·c)·(b·d)`. -/
theorem mul_interchange (a b c d : Q') :
    ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  have inner : (b * (c * d)).eqv (c * (b * d)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (b * c) (c * b) d (Q'.mul_comm_eqv b c))
        (Q'.mul_assoc_eqv c b d))
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a (b * (c * d)) (c * (b * d)) inner)
      (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))))

/-- The per-term Khatri–Rao identity: `(g·(P·Q))·(h·(p·q)) ≃ (g·h)·((P·p)·(Q·q))`
— the weights `g,h` combine, and the two coordinate pairs interleave. -/
theorem mul6_schur (g P Q h p q : Q') :
    ((g * (P * Q)) * (h * (p * q))).eqv ((g * h) * ((P * p) * (Q * q))) :=
  Q'.eqv_trans _ _ _ (mul_interchange g (P * Q) h (p * q))
    (Q'.mul_eqv_congr_left (g * h) ((P * Q) * (p * q)) ((P * p) * (Q * q))
      (mul_interchange P Q p q))

/-! ## The Schur product theorem (constructive)

**Transfer of `OSforGFF` `General/SchurProduct`** (arXiv:2603.15770): the Hadamard
(entrywise) product of two PSD matrices is PSD.  Constructive, Mathlib-free, via
the explicit Khatri–Rao Gram witness `G∘H = Σ_{k,l} (d_k e_l)(v_k∘u_l)(v_k∘u_l)ᵀ`. -/

/-- **Schur product theorem.**  Given Gram witnesses for `G` and `H`, the
Hadamard (entrywise) product `(G∘H)_{ij} = G_{ij}·H_{ij}` carries the explicit
Gram witness of rank `r_H·r_G` with weights `d^G_{⌊p/r_H⌋}·d^H_{p mod r_H}` and
coordinate vectors `v^G_{⌊p/r_H⌋}∘u^H_{p mod r_H}` (the Khatri–Rao product).  This
is the constructive `General/SchurProduct` of `OSforGFF` (arXiv:2603.15770),
proved without the classical spectral theorem. -/
def schur_product {G H : Nat → Nat → Q'} (repG : GramRep G) (repH : GramRep H) :
    GramRep (fun i j => G i j * H i j) where
  r := repH.r * repG.r
  d := fun p => repG.d (p / repH.r) * repH.d (p % repH.r)
  hd := fun p => Q'.mul_nonneg _ _ (repG.hd _) (repH.hd _)
  v := fun p i => repG.v (p / repH.r) i * repH.v (p % repH.r) i
  hM := by
    intro i j
    -- the two single-matrix Gram representations
    have hGH : (G i j * H i j).eqv
        ((finSum (fun k => repG.d k * (repG.v k i * repG.v k j)) repG.r)
          * (finSum (fun l => repH.d l * (repH.v l i * repH.v l j)) repH.r)) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (G i j) _ (H i j) (repG.hM i j))
        (Q'.mul_eqv_congr_left _ (H i j) _ (repH.hM i j))
    -- expand the product of sums into a nested double sum
    refine Q'.eqv_trans _ _ _ hGH ?_
    refine Q'.eqv_trans _ _ _
      (finSum_mul_finSum
        (fun k => repG.d k * (repG.v k i * repG.v k j))
        (fun l => repH.d l * (repH.v l i * repH.v l j)) repG.r repH.r) ?_
    -- regroup each term to the Khatri–Rao shape `F k l`
    refine Q'.eqv_trans _ _ _
      (finSum_eqv_congr _ _ (fun k => finSum_eqv_congr _ _ (fun l =>
        mul6_schur (repG.d k) (repG.v k i) (repG.v k j)
          (repH.d l) (repH.v l i) (repH.v l j)) repH.r) repG.r) ?_
    -- fold the nested sum back into the single rank-`r_H·r_G` flat sum
    exact Q'.eqv_symm
      (finSum_flatten
        (fun k l => (repG.d k * repH.d l)
          * ((repG.v k i * repH.v l i) * (repG.v k j * repH.v l j))) repH.r repG.r)

/-! ## Base Gram witnesses: all-ones and zero -/

/-- The all-ones matrix `J_{ij} = 1` is a rank-1 Gram (`v_0 = 1`, `d_0 = 1`). -/
def onesGramRep : GramRep (fun _ _ => (1 : Q')) where
  r := 1
  d := fun _ => 1
  hd := fun _ => by decide
  v := fun _ _ => 1
  hM := fun _ _ => by decide

/-- The zero matrix is a rank-0 Gram (empty sum). -/
def zeroGramRep : GramRep (fun _ _ => (0 : Q')) where
  r := 0
  d := fun _ => 0
  hd := fun _ => by decide
  v := fun _ _ => 0
  hM := fun _ _ => Q'.eqv_refl _

/-! ## Nonnegative scaling and direct sum of Gram witnesses -/

/-- A `GramRep` matrix scaled by a nonnegative rational stays a `GramRep`
(absorb the scalar into the weights). -/
def gramRep_smul {M : Nat → Nat → Q'} (q : Q') (hq : (0 : Q') ≤ q)
    (rep : GramRep M) : GramRep (fun i j => q * M i j) where
  r := rep.r
  d := fun k => q * rep.d k
  hd := fun k => Q'.mul_nonneg _ _ hq (rep.hd k)
  v := rep.v
  hM := by
    intro i j
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q (M i j) _ (rep.hM i j)) ?_
    refine Q'.eqv_trans _ _ _
      (const_mul_finSum (fun k => rep.d k * (rep.v k i * rep.v k j)) q rep.r) ?_
    exact finSum_eqv_congr _ _
      (fun k => Q'.eqv_symm (Q'.mul_assoc_eqv q (rep.d k) (rep.v k i * rep.v k j))) rep.r

/-- **Direct sum: the entrywise sum of two `GramRep` matrices is a `GramRep`**
(concatenate the weight/vector families — the first `r_G` indices serve `G`, the
remaining `r_H` serve `H`).  This is the "sum of PSD is PSD" closure. -/
def gramRep_add {G H : Nat → Nat → Q'} (repG : GramRep G) (repH : GramRep H) :
    GramRep (fun i j => G i j + H i j) where
  r := repG.r + repH.r
  d := fun p => if p < repG.r then repG.d p else repH.d (p - repG.r)
  hd := fun p => by
    show (0 : Q') ≤ (if p < repG.r then repG.d p else repH.d (p - repG.r))
    split
    · exact repG.hd p
    · exact repH.hd _
  v := fun p i => if p < repG.r then repG.v p i else repH.v (p - repG.r) i
  hM := by
    intro i j
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (finSum_add_range _ repG.r repH.r) ?_
    -- the first block reproduces `G i j`
    have hGpart :
        (finSum (fun p =>
          (if p < repG.r then repG.d p else repH.d (p - repG.r))
            * ((if p < repG.r then repG.v p i else repH.v (p - repG.r) i)
               * (if p < repG.r then repG.v p j else repH.v (p - repG.r) j))) repG.r).eqv
          (G i j) :=
      Q'.eqv_trans _ _ _
        (finSum_congr_lt _ _ repG.r (fun p hp => by
          simp only [if_pos hp]; exact Q'.eqv_refl _))
        (Q'.eqv_symm (repG.hM i j))
    -- the second block reproduces `H i j`
    have hHpart :
        (finSum (fun t =>
          (if repG.r + t < repG.r then repG.d (repG.r + t)
             else repH.d ((repG.r + t) - repG.r))
            * ((if repG.r + t < repG.r then repG.v (repG.r + t) i
                  else repH.v ((repG.r + t) - repG.r) i)
               * (if repG.r + t < repG.r then repG.v (repG.r + t) j
                    else repH.v ((repG.r + t) - repG.r) j))) repH.r).eqv
          (H i j) :=
      Q'.eqv_trans _ _ _
        (finSum_congr_lt _ _ repH.r (fun t _ => by
          have hnlt : ¬ (repG.r + t < repG.r) := Nat.not_lt.mpr (Nat.le_add_right repG.r t)
          simp only [if_neg hnlt, Nat.add_sub_cancel_left]; exact Q'.eqv_refl _))
        (Q'.eqv_symm (repH.hM i j))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hGpart)
      (Q'.add_eqv_congr_left _ _ _ hHpart)

/-! ## Hadamard powers and the truncated Hadamard exponential

**Transfer of `OSforGFF` `General/HadamardExp`** (arXiv:2603.15770): the entrywise
`exp` of a PSD matrix is PSD.  Constructive version: each Hadamard power is a Gram
(iterated Schur), and the truncated entrywise exponential `Σ_{n<N} G^{∘n}/n!` is a
nonnegatively-scaled direct sum of Gram matrices, hence a Gram. -/

/-- The `n`-th Hadamard (entrywise) power of `M`: `M^{∘0} = J` (all ones),
`M^{∘(n+1)} = M ∘ M^{∘n}`. -/
def hadamardPow (M : Nat → Nat → Q') : Nat → (Nat → Nat → Q')
  | 0 => fun _ _ => 1
  | n + 1 => fun i j => M i j * hadamardPow M n i j

/-- **Hadamard power positivity.**  Every entrywise power of a `GramRep` matrix is
a `GramRep` — iterated Schur product over the all-ones base. -/
def hadamardPow_gramRep {M : Nat → Nat → Q'} (rep : GramRep M) :
    ∀ n, GramRep (hadamardPow M n)
  | 0 => onesGramRep
  | n + 1 => schur_product rep (hadamardPow_gramRep rep n)

/-- Factorial (Lean core here has no `Nat.factorial`). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- `1/n!` as a nonnegative rational coefficient of the entrywise exponential. -/
def invFact (n : Nat) : Q' := Q'.mkPos 1 (fact n) (fact_pos n)

theorem invFact_nonneg (n : Nat) : (0 : Q') ≤ invFact n := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ 1
  decide

/-- The truncated entrywise exponential `(exp_∘ M)^{<N}_{ij} = Σ_{n<N} M^{∘n}_{ij}/n!`. -/
def hadamardExpTrunc (M : Nat → Nat → Q') (N : Nat) : Nat → Nat → Q' :=
  fun i j => finSum (fun n => invFact n * hadamardPow M n i j) N

/-- **Truncated Hadamard exponential positivity.**  Each partial sum
`Σ_{n<N} M^{∘n}/n!` of the entrywise exponential of a `GramRep` matrix is a
`GramRep` — a nonnegatively-scaled (`1/n! ≥ 0`) direct sum of Hadamard powers.
The constructive `General/HadamardExp` (arXiv:2603.15770) at every truncation. -/
def hadamardExpTrunc_gramRep {M : Nat → Nat → Q'} (rep : GramRep M) :
    ∀ N, GramRep (hadamardExpTrunc M N)
  | 0 => zeroGramRep
  | N + 1 =>
      gramRep_add (hadamardExpTrunc_gramRep rep N)
        (gramRep_smul (invFact N) (invFact_nonneg N) (hadamardPow_gramRep rep N))

/-! ## Application to the off-diagonal character-product wall

The off-diagonal OS2 content this could retire is the character-PRODUCT Gram
`G_{μν} = ⟨χ_μ χ_ν⟩_t = Σ_c N^c_{μν} m_c`: a nonnegative (`m_c ≥ 0`) combination
of the SU(2) fusion-channel matrices `N^c`.

**The positive half (`fusionCombo_gramRep`).**  IF every channel matrix `N^c`
were a `GramRep`, then the whole combination would be too — by `gramRep_smul`
(scale by `m_c ≥ 0`) and `gramRep_add` (sum the channels), exactly the
Schur/Hadamard "nonnegative combination of PSD is PSD" closure.  So the algebra
*would* close the off-diagonal wall, were the channels individually PSD.

**The obstruction (`fusion1_not_gramRep`).**  They are NOT.  The spin-½ channel
`N^1` is the path-graph adjacency matrix (`N^1_{μν} = 1 ⟺ |μ−ν| = 1`); its
`2×2` corner has the explicit NEGATIVE quadratic form `Q(1,−1) = −2`, so it is
not positive-semidefinite, hence not a `GramRep`.  This is the machine-checked
reason the Schur/Hadamard route does NOT by itself retire
`MomentSquarePSD.MomentSquarePos` / the `P_N` wall: the off-diagonal PSD must come
from the heat-kernel WEIGHT conspiracy (the `m_c` decay, equivalently pointwise
`K_t ≥ 0`), the analytic input isolated as `MomentSquarePSD.UniformGramSOS`. -/

/-- **Nonnegative combination of Gram channels is a Gram.**  Given channel
matrices `Nc c` each carrying a `GramRep` and nonnegative weights `m c ≥ 0`, the
weighted sum `Σ_{c<C} m_c · Nc c` is a `GramRep`.  This is the abstract closure
(scale + direct sum) behind lifting a fusion decomposition to PSD — the
constructive analogue of the Schur/Hadamard generating-functional lift in
`OSforGFF` (arXiv:2603.15770). -/
def fusionCombo_gramRep (Nc : Nat → Nat → Nat → Q') (m : Nat → Q')
    (hm : ∀ c, (0 : Q') ≤ m c) (reps : ∀ c, GramRep (Nc c)) :
    ∀ C, GramRep (fun i j => finSum (fun c => m c * Nc c i j) C)
  | 0 => zeroGramRep
  | C + 1 =>
      gramRep_add (fusionCombo_gramRep Nc m hm reps C)
        (gramRep_smul (m C) (hm C) (reps C))

/-- The SU(2) spin-½ fusion-channel matrix `N^1_{μν} = 1 ⟺ |μ−ν| = 1` (the
path-graph adjacency matrix). -/
def fusion1 (μ ν : Nat) : Q' :=
  if μ + 1 = ν then 1 else if ν + 1 = μ then 1 else 0

/-- The off-cone test vector `(1, −1, 0, …)`. -/
def fusion1BadVec : Nat → Q' :=
  fun i => if i = 0 then 1 else if i = 1 then (-1 : Q') else 0

/-- The `2×2` corner of `N^1` has a strictly negative quadratic form,
`Q(1,−1) = −2`: the explicit certificate that `N^1` is NOT
positive-semidefinite. -/
theorem fusion1_not_psd :
    ¬ ((0 : Q') ≤ gramQuadForm fusion1 fusion1BadVec 2) := by decide

/-- **The spin-½ fusion channel is not Gram-representable.**  If `N^1` had a
`GramRep`, its quadratic form would be `≥ 0` everywhere
(`gramPSD_quadForm_nonneg`), contradicting `fusion1_not_psd`.  Hence the
Schur/Hadamard machinery cannot, by itself, exhibit the character-PRODUCT Gram as
a Gram: the off-diagonal `MomentSquarePos` / `P_N` wall is NOT retired by the
algebra alone — it needs the heat-kernel weight conspiracy. -/
theorem fusion1_not_gramRep : GramRep fusion1 → False :=
  fun rep => fusion1_not_psd (gramPSD_quadForm_nonneg rep fusion1BadVec 2)

/-- **The off-diagonal reduction (re-exposed).**  The genuine reduction from the
single named residual to all-order off-diagonal positivity is
`MomentSquarePSD.momentSquarePos_of_uniformSOS`: a uniform CReal weighted-SOS
certificate (`UniformGramSOS`, the CReal analogue of this module's `GramRep`
quadratic form) gives `MomentSquarePos`.  By `fusion1_not_gramRep`, that residual
is NOT discharged channel-by-channel via Schur; it remains the sharp analytic
input.  We re-expose the reduction here to record the connection in Lean. -/
theorem offdiagonal_reduction_from_residual (M : GramRed.MomentData)
    (h : MomentSquarePSD.UniformGramSOS M) : GramRed.MomentSquarePos M :=
  MomentSquarePSD.momentSquarePos_of_uniformSOS M h

end YMGap.Continuum.SchurHadamardTransfer

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SchurHadamardTransfer.gramPSD_quadForm_nonneg
#print axioms YMGap.Continuum.SchurHadamardTransfer.gramQuadForm_eq_sos
#print axioms YMGap.Continuum.SchurHadamardTransfer.schur_product
#print axioms YMGap.Continuum.SchurHadamardTransfer.hadamardPow_gramRep
#print axioms YMGap.Continuum.SchurHadamardTransfer.hadamardExpTrunc_gramRep
#print axioms YMGap.Continuum.SchurHadamardTransfer.fusionCombo_gramRep
#print axioms YMGap.Continuum.SchurHadamardTransfer.fusion1_not_gramRep
#print axioms YMGap.Continuum.SchurHadamardTransfer.offdiagonal_reduction_from_residual
