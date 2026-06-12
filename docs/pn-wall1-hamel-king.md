# Wall-1: the Hamel–King deformed-denominator / flagged-character test on `nonnegCoeffs P_N`

A focused, exact (sympy, rational/symbolic throughout — no floats for any
coefficient claim) test of the literature-informed route named for this pass:

> **HYPOTHESIS (Hamel–King + Okada).** `S_N²` is the *deformed symplectic Weyl
> denominator* and `P_N` is the *deformed flagged sp(2N) character* (a positive
> King-tableau sum by construction), so that `P_N = Δ_N/S_N²` is manifestly
> nonneg **without** `Δ_N` ever being positive.

Refs targeted: **Hamel–King**, "Symplectic shifted tableaux and deformations of
Weyl's denominator formula for sp(2n)," *J. Algebraic Combin.* **16** (2002)
269–300 (deformed denominator + flagged sp character, Jacobi–Trudi eqs 3.28–3.30,
King-tableau constraint `T_{i,j} ≥ 2i−1`); **Krattenthaler/Fulmek–Krattenthaler**,
"Lattice path proofs for determinantal formulas for symplectic and orthogonal
characters," *JCTA* **77** (1997) 3–50 (symplectic character = N non-intersecting
lattice paths); **Lecouvey**, Kostka–Foulkes / type-`C_n` charge; **Stembridge**,
Adv. Math. **83** (1990) (Pfaffian/√det). Base data reproduces the Lean ground
truth (`P_2 = [1,2,3]`, `P_3` matches `MomentPositivity.P3`, `P_4` matches the
docs; `P_N(1)`, deg `N(N²−1)/3`, lead `(2N−1)!!`, even powers, all-nonneg, N ≤ 6).
Scripts: `/tmp/pn_*.py`.

**Bottom line up front.** The hypothesis in its **principal/geometric** form is
**falsified, exactly and structurally**, by a clean new obstruction (the
*palindrome obstruction*, §2) that subsumes and sharpens the prior Farkas
negative. `S_N` is identified **exactly** as the **type-A** (GL_N) principal
Vandermonde, *not* the type-C symplectic denominator (§1). The genuine
Hamel–King **deformation/flagging escape is the one surviving sub-route** and was
not closed: no flagged sp character at a geometric specialization matched `P_N`
in the tested net (§3). One OEIS hit (§4) gives the box factor a Barnes-`G` /
superfactorial closed form but no new positivity model. Nothing new closes; the
findings are sharp **negatives** plus an **exact identification of `S_N`**.

---

## 0. Setup recomputed from scratch (matches Lean)

`m_s = (s+1)a^{s(s+2)}`, character Gram `G_{ij} = Σ_{p=0}^{min(i,j)} m_{|i−j|+2p}`,
`Δ_N = det G[0..N−1]`, `S_N = ∏_{j=1}^{N−1}(a^{2j}−1)^{N−j}`, `P_N = Δ_N/S_N²`,
`q = a²`, `p_N(q) = P_N`. Reproduced exactly N ≤ 6:
`p_2 = 1+2q+3q²`, `p_3 = 1+4q+12q²+20q³+32q⁴+36q⁵+36q⁶+24q⁷+15q⁸`, …,
`deg p_N = N(N²−1)/3`, `p_N(0)=1`, lead `(2N−1)!!`, only even `a`-powers, all
coefficients ≥ 0, `p_N(1) = N!·∏_{k=1}^{N−1}C(2k+1,k) = 1,6,180,25200,…`.

In the single base variable `q`,

    S_N(q) = ∏_{j=1}^{N−1} (q^j − 1)^{N−j}        (verified Δ_N = S_N²·p_N in q, N ≤ 4)

with `deg S_N = Σ_{j=1}^{N−1}(N−j)j`, `deg S_N² = 2·that`, and
`deg Δ_N = 2 deg S_N + deg p_N`.

---

## 1. `S_N` IS the type-A Vandermonde — NOT the symplectic (type-C) denominator (exact)

The first half of the Hamel–King hypothesis ("`S_N²` is the deformed *symplectic*
Weyl denominator") is **false at the principal/geometric specialization**, and the
correct identification is clean:

> **`S_N(q) = q^{−E(N)} · ∏_{0≤i<j≤N−1} (q^j − q^i)`** — i.e. `S_N` is exactly the
> **type-A (GL_N) principal Vandermonde** on the geometric nodes `x_i = q^i`,
> times a monomial. (Verified N ≤ 5; the ratio
> `[∏_{i<j}(q^j−q^i)]/S_N = q^{E(N)}` is a *pure monomial*, `E(N) = 0,1,4,10,20 =
> Σ_i i(N−1−i)`.)

By contrast the **type-C symplectic Weyl denominator** principal-specialized at
`x_i = q^i` (the bialternant `det(x_j^{n−i} − x_j^{−(n−i)})`) is a *different*
polynomial: it equals `S_N²` times **extra** cyclotomic factors and a monomial,

    sympDenom(q¹,…,q^N) = ±q^{−c}·S_N² · (q²+1)(q²−q+1)(q⁴+…)·…   (N = 2,3,4, exact),

never `S_N²` on the nose. So `S_N²` is the **squared type-A Vandermonde**
(the q-Vandermonde of the *geometric* nodes `q^i` — the Stieltjes–Wigert /
Chern–Simons factor), **not** a symplectic denominator. This matches the prior
`sp2n-pn-notes` §2 remark (geometric nodes for `S_N` vs lacunary nodes `a^{r²}`
for the measure) and now pins it as an exact identity. The "denominator =
symplectic Weyl denominator" leg of Hamel–King is therefore the wrong type.

---

## 2. The PALINDROME OBSTRUCTION — `P_N` is no principal character of any classical type (exact)

The sharpest new result of this pass — a one-line **structural impossibility**
that subsumes the prior Farkas certificate (`sp2n-pn-notes` §3) and extends it
from "no positive *combination*" to "**no single character, even signed, at any
geometric specialization**":

> **Theorem (palindrome obstruction).** Every irreducible character `χ` of a
> classical group `Sp(2n)`, `SO(2n+1)`, `SO(2n)` is invariant under the Weyl
> group, which for types `B, C, D` contains the sign map `x_i ↦ x_i^{−1}`.
> Hence at *any* geometric specialization `x_j = q^{c_j}` the Laurent polynomial
> `χ(q^{c_1},…,q^{c_n})` is invariant under `q ↦ q^{−1}` (up to an overall
> monomial), i.e. its coefficient sequence is **palindromic**. (Type-A `s_λ`
> principal specializations are likewise palindromic, by partition-conjugation /
> reversal.)
>
> But `P_N` is **provably non-palindromic**: `[q⁰]P_N = 1` while `[q^{deg}]P_N =
> (2N−1)!! > 1` (and the low/high tails are wildly asymmetric — N ≤ 5: e.g.
> `(c_0,c_{deg}) = (1,945)`, `(c_1,c_{deg−1}) = (8,3360)` at N = 5).
>
> **Therefore `P_N` is not a single classical character — symplectic, orthogonal
> or general-linear — at any geometric/principal specialization `x_j = q^{c_j}`.**

This is verified directly: principal-specialized `sp(2n)` and `so(2n+1)`
characters (e.g. `sp_{(1,0)}(q,q²) = (q+1)²(q²−q+1)/q²`, palindromic; the so(5)
characters at `x_i=q^i` are all palindromic q-binomial-type products), none of
which is the irreducible, strictly-non-palindromic `p_2 = 1+2q+3q²`.

**Consequence.** The Hamel–King identification "`P_N = principal symplectic
character`" cannot hold. The *only* way the route survives is via the genuine
**Hamel–King deformation / flagging**, which breaks the Weyl symmetry (a flag
truncates the King tableaux asymmetrically) and *can* be non-palindromic. This
is consistent with — and is the precise mechanism behind — the prior memory's
"non-principal (charge/major-index)" verdict.

---

## 3. The flagged / deformed escape — the surviving sub-route, not closed

The lead `(2N−1)!! = ∏_{k=1}^{N−1}(2k+1)` and constant `1` of `P_N` are exactly
the **King symplectic signature**: the King alphabet for the `k`-th nested box is
`{1,1̄,…,k,k̄}` of size `2k`, and with the `T_{i,j} ≥ 2i−1` flag the top (max-area)
path of box `k` is counted with multiplicity `2k+1` (the SO(2k+1)/Sp(2k) flag
symbol). So:

* **Degree match is exact.** `deg p_N = Σ_{k=1}^{N−1}k(k+1) = deg ∏_{k=1}^{N−1}
  [2k+1 choose k]_q` (the nested-box Gaussian-binomial product), reconfirmed
  N ≤ 5. The box geometry `1×2, 2×3, …, (N−1)×N` is pinned.
* **The box product does NOT divide `p_N`.** `∏[2k+1 choose k]_q ∤ p_N`
  (nonzero remainder, N = 2…5) — so `p_N ≠ (box product)·(S_N charge factor)` as
  a *product*; the `N!` must enter as an `S_N` **sum** (charge) that entangles the
  boxes, consistent with `p_N` irreducible. (Reconfirms `pn-wall1-lgv-vicious-
  walker` §0.)
* **`p_N` is not a plain LGV/q-binomial determinant either.** Any Lindström–
  Gessel–Viennot determinant of monic q-binomial entries has lead `= ∏(entry
  leads)`; the natural staircase ansätze give lead `1` and `p_N(1)` values
  `15,140,2520,…` ≠ `180,25200,15876000,…`. The required lead `(2N−1)!!` (≠ 1)
  forces a **confluent / odd-orthogonal (SO(2N+1))** or genuinely *flagged*
  determinant, not a bare q-binomial LGV det. (Reconfirms `§1a`: `p_N` is not a
  Hankel determinant.)
* **Flagged sp(2N) Jacobi–Trudi (Hamel–King 3.29/3.30), geometric spec —
  NO MATCH.** Testing the flagged symplectic character `det(h^{sp}_{λ_i−i+j}(x_1,
  …,x_{b_i}))` with the King flag `b_i` and symplectic complete-homogeneous
  `h^{sp}_r = [tʳ]∏_k 1/((1−x_k t)(1−t/x_k))` at `x_k = q^k`, over the net
  `n ∈ {N−1,N}`, shapes `λ` (parts ≤ 6, length ≤ 2) and four flag schemes (full
  alphabet, King-decreasing, increasing, doubled-King `b_i=2(n−i)`), **none equals
  `p_2 = 1+2q+3q²` nor `p_3`** (exact, search complete). The flagged sp
  character at a *geometric* spec did not reproduce `p_N`; the genuine Hamel–King
  object that would is the **`t`-deformed** flagged character `sp_λ(x;t)` with the
  deformation parameter tied to the **lacunary theta drift** `t_r = r·a^{r²}` —
  *not* a geometric `x_k = q^k`. That deformation was not pinned to `p_N`.

So the flagged/deformed leg is **open**, not closed: the route is structurally
the right shape (degree, lead, King alphabet all match) but no explicit
specialization/deformation was found that yields `p_N` exactly.

---

## 4. OEIS findings

* **Box factor `∏_{k=1}^{N−1}C(2k+1,k) = 1,3,30,1050,132300,…`** is **OEIS
  A203469** (`= ∏_{i=1..n}C(2n−i,i)`), with the clean closed forms
  `a(n) = (n!/2^{n−1})·∏_{j=1}^{n−1} Catalan(j)` and
  `a(n) = (2^n/√π)^n·BarnesG(n+3/2)/(BarnesG(n+2)·BarnesG(3/2))` — a
  **superfactorial / Barnes-`G`** object. Equivalently A296590 (offset shift).
  This confirms the nested-box ballot-number reading but offers **no new
  positivity model** (it is a value/`q=1` statement).
* **Full value `p_N(1) = N!·(box factor) = 1,6,180,25200,15876000,…`** is **not
  catalogued** (no OEIS hit) — consistent with the `N!`-charge being a genuinely
  non-principal, problem-specific entanglement, not a known product sequence.

---

## 5. Verdict and the single sharpest open statement

**New this pass (exact, sympy):**

1. **`S_N` identified exactly** as the **type-A** principal Vandermonde
   `q^{−E(N)}∏_{i<j}(q^j−q^i)`, **not** the symplectic (type-C) denominator
   (§1). The first leg of the Hamel–King hypothesis is the wrong root system.
2. **Palindrome obstruction (§2):** `P_N` is non-palindromic, hence **not a single
   classical character (sp/so/gl) at any geometric specialization** — a clean
   structural impossibility subsuming and sharpening the Farkas negative. The
   only survivor is the genuinely **deformed / flagged** (palindrome-breaking)
   character.
3. **Flagged-character geometric test (§3):** the King-flagged sp(2N) Jacobi–Trudi
   character at a geometric spec `x_k=q^k` does **not** reproduce `p_N` in the
   tested net; the box geometry/lead/alphabet all match but the deformation
   parameter (which must carry the lacunary `a^{r²}` drift, not a geometric `q^k`)
   was not pinned.

**OPEN — the single sharpest remaining statement (unchanged target, sharpened
mechanism):**

> Exhibit the **`t`-deformed flagged sp(2N) character** of Hamel–King with the
> deformation specialization `t_r = r·a^{r²}` (the differentiated-theta /
> lacunary drift, `q = a²`) — equivalently a **King symplectic-tableau sum with a
> type-`C_n` charge/major-index statistic** (Lecouvey) over the nested boxes
> `1×2,…,(N−1)×N` — and prove it equals `p_N(q)` exactly. Concretely:
>
>     p_N(q) = Σ_{T ∈ King-SympTab(δ_N, flag)} q^{charge(T)},
>
> with the King flag supplying the `(2k+1)`-fold top multiplicity (lead `(2N−1)!!`)
> and the type-C charge distributing the `N!` over `S_N` while entangling the boxes
> into the irreducible `p_N`. Coefficient-positivity (`nonnegCoeffs P_N`,
> equivalently `UniformPNDiffNonneg`) would then be manifest and uniform in `N`.

The non-palindromicity (§2) **proves** the statistic must be flag/charge-driven
(no geometric-spec character can do it); the degree/lead/alphabet matches (§3)
**pin the combinatorial objects** (King tableaux of staircase shape, nested-box
`[2k+1,k]_q` weights, `(2k+1)` flag multiplicity); the missing piece is the
explicit type-C charge realizing the `t_r = r·a^{r²}` deformation. This was not
constructed. Value-positivity (`p_N(1) > 0`, §4) is strictly weaker and is **not**
the target. The Wall-2 (analytic, differentiated-Jacobi-triple-product) route is
unaffected.
