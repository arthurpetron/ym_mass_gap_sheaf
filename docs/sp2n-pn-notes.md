# Sp(2N) / LGV symplectic-character notes on `nonnegCoeffs P_N`

A focused sympy investigation (exact arithmetic throughout, N ≤ 7; methodology
`/tmp/pn_*.py`) of the two headroom routes named in
`continuum-positivity-status.md` §5b: (1) a sign-clean
symplectic-character / non-intersecting-path (LGV) determinant model for
`p_N`, and (2) a Dodgson–Toda induction off the `λ_k` relation.

**Bottom line up front.** Neither route was closed. The Dodgson–Toda relation
is now *exactly* pinned down (`λ_k = (q^k−1)²·P_{k+1}P_{k−1}/P_k²`) but is
**circular** as an induction (β_k contains the unknown `P_{k+1}`). The LGV /
symplectic route gained a genuinely clean reframing — the Gram is a determinant
of a manifestly **nonneg-coefficient** matrix of positive theta-monomials — but
the residual `P_N` is **provably not** a nonnegative combination of the natural
positive atoms (principal Schur / symplectic specializations): an **exact Farkas
certificate** rules this out already at `N = 2`. The remaining kernel is sharpened
below.

All claims below use exact rational/symbolic sympy (no floats for any coefficient
statement). The base data reproduces the Lean ground truth (`P_3` matches
`MomentPositivity.P3` on the nose).

---

## 0. Setup recomputed from scratch (matches Lean)

The Gram is the **SU(2) character (fusion) Gram**, *not* the naive Hankel
`m_{i+j}`:

    G_{ij} = ⟨χ_i χ_j⟩ = Σ_{p=0}^{min(i,j)} m_{|i−j|+2p},     m_s = (s+1)·a^{s(s+2)}.

`Δ_N = det G[0..N−1]`, `S_N = ∏_{j=1}^{N−1}(a^{2j}−1)^{N−j}`,
`P_N = Δ_N/S_N²`, `q = a²`, `p_N(q) = P_N`. Verified N ≤ 7:
`deg_q p_N = N(N²−1)/3`, `p_N(0)=1`, lead `(2N−1)!!`, even powers only, all
coefficients nonnegative. (E.g. `p_3 = 1+4q+12q²+20q³+32q⁴+36q⁵+36q⁶+24q⁷+15q⁸`,
matching `MomentPositivity.P3`.) `P_N` is **irreducible over ℚ** for N ≤ 6 (single
factor, exact `factor_list`); `S_N²` is **sign-mixed** (e.g. `S_3²` has 3 negative
coefficients). So the division `Δ_N/S_N²` genuinely trades a sign-mixed perfect
square against a sign-clean residual — the §5 obstruction in one line.

---

## 1. Explicit Hankel−minus−Toeplitz (symplectic) signature — confirmed

Two exact, uniform-in-N structural identities (verified N ≤ 5):

* **Diagonal increment.** `G_{ij} − G_{i−1,j−1} = m_{i+j}` for all `i,j ≥ 1`.
* **Hankel−Toeplitz form.** With `h_n := Σ_{t=0}^{⌊n/2⌋} m_{n−2t}` (`h_{<0}=0`),

      G_{ij} = h_{i+j} − h_{|i−j|−2}.

This is exactly the Okada / Krattenthaler **symplectic `Sp(2N)` / odd-orthogonal
`SO(2N+1)`** determinantal signature (`det(h_{i+j} − h_{i−j})`-type), confirming
the §5b identification. It is the natural "home" of `P_N`.

---

## 2. The positive lacunary-measure reframing (new, clean)

The single most useful new structural fact. Set `t_r := r·a^{r²}` (`r ≥ 1`); these
are the **differentiated-Jacobi-theta coefficients**, all with **positive**
coefficient `r` and a Gaussian (lacunary) exponent `r²`. Then

    m_s = t_{s+1}/a      (since (s+1)a^{s(s+2)} = (s+1)a^{(s+1)²−1}),

and therefore

    a·G_{ij} = Σ_{p=0}^{min(i,j)} t_{|i−j|+1+2p}.

**Every entry of `a·G` is a nonnegative-coefficient polynomial in `a`** (a finite
sum of positive theta-monomials) — verified N ≤ 5. Consequently

    aᴺ·Δ_N = det(a·G),     a·G = nonneg-coefficient matrix.

So the *entire* sign content of `Δ_N` (and hence of `P_N`) is the **determinantal
sign-cancellation** of a nonneg-coefficient matrix — there is no sign coming from
the entries. This is precisely the structure an LGV / non-intersecting-path
interpretation is built to resolve (Gessel–Viennot turns the signed permutation
expansion into a positive sum over non-crossing path families).

### Why the naive LGV/total-nonnegativity does **not** fire

For LGV to give nonneg coefficients of the *full* determinant directly, `a·G`
would need to be **coefficient-totally-nonnegative** (all minors nonneg-coeff).
It is **not**: exhaustive check of all minors of the 5×5 `a·G` found **226** with
negative coefficients, the smallest being a 2×2:

    det [[a·G_{00}, a·G_{01}],[a·G_{10}, a·G_{11}]]  ⊃  3a¹⁰ − 4a⁸ + a²   (sign-mixed).

The negativity is intrinsic: the Gaussian exponent `r²` in `t_r = r·a^{r²}` makes
`t_{|i−j|+1+2p}` **non-factorizable** across `i, j` (`r² = (|i−j|+1+2p)²` does not
split as `f(i,p)+g(j,p)`), so `a·G` is **not** a Gram `AAᵀ` of nonneg-coeff
factors, and the entries are not a TN/path kernel. This is the theta/Gaussian
obstruction made precise: the symplectic-Hankel positivity theorems (which assume
a TN or positive-measure kernel) do not apply because the underlying "measure"

    μ = Σ_{r≥1} r·δ_{x_r},   x_r = a^{r²}   (positive weights!)

is supported on **lacunary** nodes `a^{r²}`, whose Vandermonde squares
`(a^{r²}−a^{s²})² = a^{2s²}(a^{r²−s²}−1)²` are individually sign-mixed
(`(q^d−1)² = q^{2d} − 2q^d + 1`). Positivity of the *weights* does not rescue
coefficient-positivity of the *Vandermonde-weighted sum*.

(Also confirmed: `S_N = a^{−e}·∏_{0≤i<j≤N−1}(a^{2j}−a^{2i})`, the q-Vandermonde of
the *geometric* nodes `q^i` — the Stieltjes–Wigert / Chern–Simons factor. The two
node systems — geometric `q^i` for `S_N`, lacunary `a^{r²}` for the measure — are
different; that mismatch is the structural reason `P_N` is not a clean character.)

---

## 3. `P_N` is NOT a nonneg combination of principal characters — exact Farkas

The cleanest way a symplectic/Schur model would *prove* coefficient-positivity:
exhibit `P_N` as a **nonnegative** combination of **principal specializations**
`s_μ(1,q,…,q^{N−1})` (or symplectic `sp_μ(q^1,…,q^N)`), each of which is a
manifestly nonneg-coefficient `q`-bracket product (Gaussian binomial / q-Weyl
dimension). This **fails**, and the failure is exact, not numerical:

* **In span, not in the positive cone.** `P_N` *is* in the ℚ-span of the
  principal Schur specs (they span symmetric functions), but every such
  representation has negative coefficients.
* **Exact Farkas certificate (N = 2, 3).** Solving the rational LP
  "`∃ c ≥ 0 : Σ c_μ s_μ(1,…,q^{N−1}) = P_N`" returns **infeasible**, and a
  separating dual vector `y` was found and **verified exactly** (`Aᵀy ≥ 0`
  entrywise, `bᵀy = −1 < 0`) — a rigorous proof of infeasibility, float-free.
* **The N = 2 obstruction in closed form.** Atoms are
  `s_∅ = 1`, `s_{(1)}(1,q) = 1+q`, `s_{(2)}(1,q) = 1+q+q²`. The *unique*
  representation of `P_2 = 1+2q+3q²` is

      P_2 = −1·s_∅ − 1·s_{(1)} + 3·s_{(2)}      (coeffs (−1,−1,3)).

  The atoms are all "rise-then-flat" Gaussians; `P_2`'s **strictly accelerating**
  profile `(1,2,3)` requires `3·s_{(2)}` for the top, then *subtraction* to repair
  the lower coefficients. Tried and also infeasible (float-certified, robust):
  ordinary Schur with `len ≤ N`, `nvars ∈ {N, 2N−1}`; the irreducibility of `P_N`
  is the deep reason — a nonneg combination of **factorable** cyclotomic atoms
  cannot land on an irreducible "generic" target.

**Upshot.** The symplectic-character route in its *positive-combination* form is
dead: `P_N` is not a positive character, nor a positive sum of principal
characters. Any working model must keep the **genuine determinantal cancellation**
(§2) and exhibit a *non-principal* (descent/charge-statistic) LGV path sum — which
this investigation did not find. The column-coefficient closed forms
(`[q¹]P_N = 2(N−1)`, `[q²]P_N=(N+1)(2N−3)`, `[q³]P_N=⅔(2N−1)(N²+2N−9)`, matching
`LGVPositivity.lean`) confirm the `e^{2Nq}` "N independent walkers" envelope
(`[qᵏ]P_N ~ (2N)ᵏ/k!`), consistent with a vicious-walker model, but each closed
form is only valid in its interior regime `N ≳ k` and goes negative outside it —
so it does not assemble into a uniform positive path model either.

---

## 4. Dodgson–Toda fallback: the `λ_k` relation is exact but circular

### The exact relation (corrects §5b's schematic form)

The §5b statement `λ_k = [∏_{j≤k}(a^{2j}−1)]²·P_{k+1}P_{k−1}/P_k²/4` is *not* exact
(the prefactor and the `/4` are wrong). The **exact** relation, with
`λ_k := Δ_{k+1}Δ_{k−1}/Δ_k²` (the Favard `β_k`), is — verified k = 2..5:

    λ_k = (a^{2k} − 1)² · P_{k+1}·P_{k−1} / P_k²            ( = (q^k−1)²·P_{k+1}P_{k−1}/P_k² ).

Derivation: `Δ_N = S_N²P_N` and the telescoping `S_{k+1}²S_{k−1}²/S_k⁴ =
(a^{2k}−1)²` (the only surviving cyclotomic factor — checked by exact
factorization). Clean Toda / log-concavity form:

    P_{k−1}·P_{k+1} = [λ_k / (q^k−1)²] · P_k².

### Why it does not induct

For a self-contained induction "`nonnegCoeffs P_{k−1}, P_k ⟹ nonnegCoeffs
P_{k+1}`", one needs `λ_k` (equivalently the multiplier `λ_k/(q^k−1)²`) as a
**known nonneg-coefficient rational function of `q` alone**, independent of the
unknown `P_{k+1}`. It is **not**: factoring `β_k = Δ_{k+1}Δ_{k−1}/Δ_k²` exactly
shows its numerator literally **contains `P_{k+1}` (and `P_{k+2}`)** —

    β_k = (cyclotomic)² · P_{k+1}·P_{k−1} / P_k²,

so `β_k` has no closed form free of the higher `P`. The relation is an *identity*,
not a *recurrence*: it expresses `λ_k` and `P_{k+1}` in terms of each other.
(Confirmed independently: `P_k²` does **not** divide `P_{k−1}P_{k+1}` for k ≤ 6 —
`P_N` irreducible, so the "ratio is a polynomial" hope fails too.) The only
non-circular content is the trivial `P_{k+1} = (P_{k+1}P_{k−1})/P_{k−1}`, which
assumes what it should prove.

**Verdict on route 2:** dead as a self-contained induction. There is no
`q`-rational multiplier; the Toda relation needs an *external* input (a closed
form or model for one of the `P`'s), which is the very thing we lack.

---

## 5. The live target and the precise remaining kernel

The clean reduced target is unchanged and re-confirmed (N ≤ 7, exact):

    UniformPNDiffNonneg:  D_k := P_k − P_{k−1}  is coefficient-nonneg,

and even the convexity `D²_k := P_k − 2P_{k−1} + P_{k−2} ≥ 0` (coeff) holds N ≤ 7.
Either gives `nonnegCoeffs P_N` by telescoping
(`P_N = P_1 + Σ_{k≥2} D_k`, nonneg sum). But neither `D_k` nor `D²_k` was found to
have a sign-clean determinant/character model: testing `D_k` as a nonneg
combination of `q^j·`Gaussian-binomials is *trivially* feasible (any
nonneg-coeff polynomial is a nonneg combination of monomials), hence
non-explanatory; no *uniform-in-N* positive model emerged.

**Sharpened verdict.** After this pass:

* **Routes closed off:** (a) positive-character / positive-principal-combination
  models — **provably dead** (exact Farkas, §3); (b) Dodgson–Toda induction —
  **provably circular** (§4); (c) naive LGV / coefficient-total-nonnegativity of
  the Gram — **dead** (sign-mixed 2×2 minors, §2).

* **The one surviving sub-route** is the *non-principal* LGV path sum demanded by
  §2: a non-intersecting lattice-path (vicious-walker) family whose generating
  function with a **descent/major-index/charge** statistic equals `p_N`, in which
  the Gessel–Viennot involution resolves the genuine determinantal cancellation of
  the nonneg-coefficient matrix `a·G` (§2) into a positive sum. The `e^{2Nq}`
  walker envelope (§3) and the symplectic Hankel−Toeplitz form (§1) are the two
  concrete handles. This was *not* constructed here; it remains a genuine
  research problem.

* **Precise mathematical kernel.** Find a finite set `Π_N` of non-intersecting
  path families on the symplectic lattice (Hankel−Toeplitz = paths with a
  reflecting wall) and a positive weight `wt(π) = q^{stat(π)}` such that

      p_N(q) = Σ_{π ∈ Π_N} q^{stat(π)},

  i.e. realize `p_N` as the partition function of `N` vicious walkers stepping on
  the lacunary node lattice `{a^{r²}}` with the differentiated-theta drift
  `t_r = r·a^{r²}`, the Vandermonde square `S_N²` cancelling against the
  reflecting-wall reflections. Equivalently (and this is the crux): exhibit the
  Gessel–Viennot sign-reversing involution on the permutation expansion of
  `det(a·G)/(aᴺ S_N²)` that cancels all negative monomials. Coefficient-positivity
  would then be manifest and *uniform in N*; value-positivity (already known via
  the heat kernel being a positive measure) is strictly weaker and not the target.

The Wall-2 (analytic, differentiated–Jacobi-triple-product) route to the same
uniform PSD remains the alternative and is unaffected by these findings.
