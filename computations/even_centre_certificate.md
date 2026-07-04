# R1 even-centre cell — explicit certificate (`Δ²V(N)+2 ≥ 0`, even N, w∈(0,1/2])

**Outcome.** The even-centre cell is **CERTIFIED**: for every even integer `N≥2` and all
`w∈(0,1/2]`, `Δ²V(N)+2 ≥ 59/50 = 1.18 > 0` (with `Δ²V(2)+2 = 3` exactly at the boundary). This
replaces the "same decomposition, larger margin" assertion in `r1_remaining_pieces.md` by an
explicit rational certificate resting on three facts, one already-proved (`V(odd)≥1`), one new
sign-definite lemma (`V(even N) ≤ G_e(w²)`, discrete Chebyshev), and one rational theta bound
(`G_e(1/4) ≤ 141/100`). The true even-centre infimum is the comfortable
`inf = 2 + 2·ϑ₄(1/4)⁴ = 2.13299…` (approached as `N→∞` at `w=1/2`), so `1.18` is a clean, robust
under-estimate — no sub-piece remains open.

Definitions match the parity-gap / L2 / φ / remaining-pieces memos exactly: `g(k)=k w^{k²}`,
`X,Y` iid `∝g`, flux `D=2X−N`, `μ_N(D) ∝ (N²−D²)w^{D²/2}` on `D≡N (mod 2)`, `|D|≤N−2`;
`V(N)=4Var(X|X+Y=N)=⟨D²⟩_{μ_N}`; `Δ²V(N)=V(N−1)−2V(N)+V(N+1)`; untruncated even theta constants
`A_e=Σ_{even D}w^{D²/2}`, `B_e=Σ_{even D}D²w^{D²/2}`, `G_e:=B_e/A_e = E_θ[D²]` (mean of `D²` under
the theta measure `∝ w^{D²/2}`), `q=w²`.

Verification: `computations/even_centre_certificate_verify.py` (`mpmath`, dps 220, `mp.iv`
tail bounds) — all blocks `[OK]`, final line `EVEN-CENTRE CELL: CERTIFIED (margin 59/50 = 1.18)`.

---

## The route — route (a), direct bound (no truncation machinery needed)

For an **even** centre `N`, the neighbours `N−1, N+1` are **odd**, and `V(odd) ≥ 1` is PROVED
(every `D²≥1` on the odd lattice; Lean `dmomNfull_ge_acNfull_odd`). The centre `V(even N)` is
small. Hence for even `N≥4`:

```
   Δ²V(N)+2 = V(N−1) + V(N+1) − 2V(N) + 2
            ≥ 1 + 1 − 2V(N) + 2                 [V(N−1),V(N+1) ≥ 1]
            = 4 − 2V(N)
            ≥ 4 − 2·G_e(w²)                     [even-centre lemma E2]
            ≥ 4 − 2·G_e(1/4)                    [G_e ↑ in q, sup at w=1/2]
            ≥ 4 − 2·(141/100)  =  118/100 = 59/50  >  0.
```

The boundary `N=2` is exact: `V(1)=0` (empty support `X+Y=1`), `V(2)=0` (point mass `X=Y=1`),
`V(3)=1`, so `Δ²V(2)+2 = V(1) − 2V(2) + V(3) + 2 = 3`. Robust for any `V(1)∈[0,∞)`.

Note the direct route needs **no** `V_inf` decomposition, no tail term, no φ-chain — those were
only forced by the near-cancellation on the *odd* parity. On the even parity the margin is `Ω(1)`,
so the crude bound closes it outright.

## The one new lemma (E2): `V(even N) ≤ G_e(w²)` — discrete Chebyshev sum inequality

`V(N)` is the mean of `D²` under the physical measure `μ ∝ (N²−D²)_+ w^{D²/2}`; `G_e` is the mean
of `D²` under the theta measure `ν ∝ w^{D²/2}`. The physical measure is the theta measure
reweighted by `h_D := (N²−D²)_+`, a **non-increasing** function of `t_D := D²` (it equals `N²−t`
for `t≤N²`, then `0`; the `|D|=N` term vanishes and `|D|>N` terms are removed — exactly the
physical truncation). Reweighting by a decreasing function of `D²` shifts mass to small `D²`, so
`E_μ[D²] ≤ E_ν[D²]`. Explicitly, `V(N) ≤ G_e ⟺`

```
   (Σ_D t_D h_D ν_D)(Σ_D ν_D)  ≤  (Σ_D t_D ν_D)(Σ_D h_D ν_D),   ν_D = w^{D²/2},
```

and the difference (RHS − LHS) is the **sign-definite double sum**

```
   RHS − LHS  =  −(1/2) Σ_{D,E even} ν_D ν_E · (t_D − t_E)(h_D − h_E)   ≥  0,
```

because `t` is non-decreasing and `h` is non-increasing in `D²`, so every product
`(t_D−t_E)(h_D−h_E) ≤ 0`. This is the same "sign-definite pair-sum" style already used for
`tail(N)>0`; it is finite/constructive/MLTT-safe (no LEM). Verified term-by-term in the script for
`N∈{4,6,8,12,20,40}`, all four `w`-slices — every summand `≤0`, defect `≥0`. The bound is
**tight only as `N→∞`** (`min(G_e−V) = 5·10⁻²⁷` at `(w=10⁻¹², N=80)`; `V(even N) ↑ G_e`), never
violated. E2 is parity-independent (holds for odd `N` too), but only the even use is needed here.

## The two supporting facts (already established)

* **`G_e(w²) ≤ G_e(1/4)`** on `w≤1/2`: `d/dq G_e = S_e/(4q) ≥ 0` (`S_e = Var_θ(D²) ≥ 0`), so
  `G_e` is increasing in `q=w²`, sup at `w=1/2`. (Same fact already in
  `theta_residual_L2_verify.py` block 3a, "`G_e increasing ⇒ G_e ≤ Ḡ_e`".)
* **`G_e(1/4) ≤ 141/100`**: `G_e(1/4)=1.40950146…`. Rigorous rational upper bound by even-`D`
  truncation at `|D|≤12` plus a positive geometric-majorant tail (`w=1/2`: successive-even-term
  ratio `w^{2D+2}<1`; `tail_A = 2w^{d₀²/2}/(1−r)`, `tail_B = 2d₀²w^{d₀²/2}/(1−r)³`), giving
  `G_e(1/4) ≤ (B_e^{≤12} + tail_B)/A_e^{≤12} = 1.4095015 < 1.41 = 141/100`. Interval-verified
  (`mp.iv`).

## The true (sharp) margin, for the record

The crude `1.18` under-states the truth. Mirroring the odd decomposition, on the even centre the
parity gap enters with the **opposite sign** and *adds*: as `N→∞`, `V(even N)→G_e`,
`V(odd N±1)→G_o = G_e + ϑ₄(w²)⁴`, so

```
   Δ²V(N)+2  →  2(G_o − G_e) + 2  =  2 + 2·ϑ₄(w²)⁴ ,
```

whose infimum over `w≤1/2` is at `w=1/2`: `2 + 2·ϑ₄(1/4)⁴ = 2.13299…` (verified: the even-centre
min is approached monotonically from above — `N=40:2.13421, N=100:2.13319, N=200:2.13304 → 2.13299`).
So the *actual* even-centre floor is `≥ 2 + 2ϑ₄(1/4)⁴ > 2.13`; the certificate uses the cheaper,
airtight `1.18` because it needs only `V(odd)≥1` and `V(even)≤G_e`, both already discharged.

---

## Complete even-cell decomposition (no gap)

| cell | statement | floor |
|---|---|---|
| `N=2`, any `w` | `Δ²V+2 = V(1)−2V(2)+V(3)+2 = 3` (exact, `V(1)=V(2)=0, V(3)=1`) | `= 3` |
| even `N≥4`, `w∈(0,1/2]` | `Δ²V+2 ≥ 4 − 2V(N) ≥ 4 − 2G_e(w²) ≥ 4 − 2G_e(1/4) ≥ 59/50` | `≥ 59/50 = 1.18` |
| even `N≥4`, `w∈[1/2,1)` | Task B (parity-agnostic), `r1_remaining_pieces.md` | `≥ 12/7` |

Together with the odd-centre cell (φ-certificate + Task A) and Task B, **every (parity, w-regime)
cell of R1 is now closed by an explicit certificate**, with the even-centre cell no longer resting
on an assertion.

## Finite rational-inequality list for Lean

The even-centre cell (`even N≥2`, `w∈(0,1/2]`) reduces to:

- **(E-odd)** `V(N−1) ≥ 1` and `V(N+1) ≥ 1` (neighbours odd). — PROVED: `dmomNfull_ge_acNfull_odd`.
- **(E-cheb)** `V(even N) ≤ G_e(w²)`, i.e. the sign-definite double-sum inequality
  `−(1/2) Σ_{D,E even} w^{D²/2} w^{E²/2} (D²−E²)((N²−D²)_+−(N²−E²)_+) ≥ 0`
  (every summand `≤ 0` since `D²` non-decreasing and `(N²−·)_+` non-increasing in `D²`).
- **(E-mono)** `G_e(w²) ≤ G_e(1/4)` on `w≤1/2` (`d/dq G_e = S_e/(4q) ≥ 0`). — already used in L2 memo.
- **(E-const)** `G_e(1/4) ≤ 141/100` (even-`D≤12` partial sum + positive geometric tail).
- **(E-N2)** `V(1)=0`, `V(2)=0`, `V(3)=1` ⟹ `Δ²V(2)+2 = 3`.
- **(E-concl)** even `N≥4`: `Δ²V(N)+2 ≥ 4 − 2·(141/100) = 118/100 = 59/50 > 0`.

**Validator:** `computations/even_centre_certificate_verify.py` (`mpmath` dps 220, `mp.iv`) — all
blocks `[OK]`.

**Sources.** Chebyshev's sum inequality (discrete correlation of a non-decreasing and a
non-increasing function of one variable). Jacobi `ϑ₄` (parity anchor `G_o−G_e = ϑ₄(w²)⁴`, for the
sharp-margin remark only). `S_e = Var_θ(D²) ≥ 0` (Cauchy–Schwarz) for `G_e ↑ q`.
