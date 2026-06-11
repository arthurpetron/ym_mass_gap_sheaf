# Continuum positivity — consolidated status

Single-page map of the SU(2) heat-kernel / uniform-PSD track: what is
machine-checked, the file layout, and the two equivalent walls that remain.
All Lean below is axiom-clean (`[propext]` or `[propext, Quot.sound]`; no
`Classical`, no `sorry`, no `native_decide`). Build is green; the axiom audit
baseline (`lean/AXIOM_AUDIT.md`) tracks every load-bearing theorem.

## 1. The load-bearing reduction

Uniform PSD of the SU(2) heat-kernel character Gram (hence the continuum
positivity input to the mass gap) reduces to a single predicate:

```
MomentSquarePos M  :=  ∀ N c, geRat (momentSquare M c N) 0
```

`GramReduction.psd_of_momentSquare_nonneg` turns `MomentSquarePos` into PSD of
every `N×N` Gram form. **`momentSquare ≡ gramForm` definitionally**
(`MomentBridge.momentSquare_is_gramForm`), so that reduction is content-free —
*supplying* `MomentSquarePos` is the whole game. `MomentData` is abstract; the
genuine heat-kernel moments `m_s = (s+1)·a^{s(s+2)}` instantiate it
(`WilsonFunctional.wilsonMoments`).

Two independent routes supply `MomentSquarePos`, and **each is reduced to one
sharp open statement** (the two walls, §4). N=2 and N=3 close through both
routes unconditionally.

## 2. What is closed (this session)

| Result | Lean | File |
|---|---|---|
| `|T_n(x)| ≤ 1` on `[−1,1]`, all orders | `Tsq_le_one` | `ChebyshevBound.lean` |
| `|U_{n-1}(x)| ≤ n` on `[−1,1]`, all orders | `absU_le` | `ChebyshevU.lean` |
| `S(x)=Σ 2a^{2n-1}/factorₙ` as a convergent CReal, **all `a∈(0,1)`** | `sConvCReal_general` | `HeatKernelConvGen.lean` |
| general `rⁿ→0` modulus (was open in KPLimit) | `pow_base_le` | `HeatKernelConvGen.lean` |
| `ϑ₃` as a convergent CReal (`a≤1/16`) | `thetaConvCReal` | `ThetaConv.lean` |
| full `R = ϑ₃·S ≥ 0` as CReals (`a≤1/16`) | `R_geRat_zero_sixteenth` | `ThetaConv.lean` |
| Chebyshev-U telescoping, general M | `uTelescope_all` | `UTelescope.lean` |
| `K_t=R` reduced to single convergence `Rtrunc M ≈ R` | `Kt_nonneg_of_residual` | `UTelescope.lean` |
| `SOSPresentation → MomentSquarePos` bridge | `momentSquarePosAt_of_sos` | `MomentBridge.lean` |
| N=2,3 uniform PSD through the bridge | `gram_psd_two/three_via_bridge` | `MomentBridge.lean` |
| flat SOS-average shortcut **ruled out** | `flatAvg_is_not_E` | `MomentBridge.lean` |
| Markov–Lukács consumer (any certificate, any degree) | `psatzAvg_nonneg` | `Positivstellensatz.lean` |
| symbolic ML producer family + composition + oracle reduction | `certQuadFamily`, `oracle_implies_existence` | `MarkovLukacs.lean` |

## 3. File map (Continuum/)

- **Chebyshev**: `ChebyshevBound.lean` (T/U recurrences, ladder `linRel_all`,
  Pythagorean `pythForm_all`, `Tsq_le_one`), `ChebyshevU.lean` (`absU_le`).
- **Heat-kernel CReal**: `HeatKernelPos.lean` (termwise `Q'` algebra),
  `HeatKernelPos2.lean` (product-of-nonnegatives engine, finite truncations),
  `HeatKernelConv.lean` (`S` for `a²≤1/2`, `divPos`), `HeatKernelConvGen.lean`
  (`S` for all `a`, general-base engine), `ThetaConv.lean` (`ϑ₃`, full `R≥0`).
- **G2 identity**: `UTelescope.lean` (telescoping engine + `K_t=R` reduction).
- **Moment / PSD bridge**: `GramReduction.lean`, `GramReduction3.lean`,
  `MomentPositivity.lean` (the `Δ_N = S_N²·P_N` factorization + nonneg-coeff
  positivity engine), `MomentBridge.lean` (LDLᵀ `SOSPresentation` bridge).
- **Favard route**: `Favard.lean`, `FavardRec.lean` (β_k closed form),
  `PNInduction.lean` (difference-positivity reduction), `PNPaths.lean`
  (moment path-positivity, Hankel factorization).
- **Positivstellensatz**: `Positivstellensatz.lean`, `MarkovLukacs.lean`.

## 4. The two walls (equivalent — either closes uniform PSD)

### Wall 1 — Favard / `nonnegCoeffs P_N` (algebraic)

The leading Gram minors factor `Δ_N(a) = S_N(a)²·P_N(a)` with `S_N` integer-
coeff and `P_N` (empirically) all-nonneg-coefficient, `P_N(0)=1`, lead
`(2N−1)!!`, even powers only. Favard's `β_s = Δ_s Δ_{s−2}/Δ_{s−1}² ≥ 0` (hence
PD at every order) follows once `P_N ≥ 0` in value, which `MomentPositivity`'s
Horner engine derives from `nonnegCoeffs P_N`. **Open: `nonnegCoeffs P_N` for
all N.** `decide`-verified through N=8.

Reduced (`PNInduction.lean`) to the cleaner **`UniformPNDiffNonneg`**:
`P_N − P_{N−1}` is coefficient-nonneg (P_N coefficient-monotone in N). The
telescoping engine `nonnegCoeffs_of_Pseq_of_uniformDiff` then gives
`nonnegCoeffs P_N` for all N. Verified N≤8.

Ruled out as closers: q-product factorization (`P_N` **irreducible over ℚ**),
fixed-depth linear recurrence with multiplier-degree ≤4, the division-free
Favard quadratic, and the J-fraction path model (division by `S_N²` makes the
weights rational with `P_k` in the denominator).

(Attack-surface analysis: §5.)

### Wall 2 — differentiated Jacobi triple product (analytic)

`K_t(x) = (ϑ₃(x)/2a)·S(x)` with `K_t(x) = a^{-1} Σ n a^{n²} U_{n-1}(x)`. The
positivity object `R = ϑ₃·S ≥ 0` is built (CReals, `a≤1/16`); the finite
telescoping engine `uTelescope_all` and the convergence machinery (G1) are
done. **Open: the identity itself** — the theta-function (Gaussian-weight
`aⁿ²`) identity, which the geometric-weight `uTelescope` does not reach.
`UTelescope.Kt_nonneg_of_residual` shows it suffices to supply the single
convergence `Rtrunc M ≈ R`; all telescoping algebra is closed.

If Wall 2 closes (`K_t ≥ 0` pointwise), the Andréief / positive-measure route
gives every `Δ_N ≥ 0` in value, hence the LDLᵀ pivots `≥ 0`, hence
`SOSPresentation` at every N, hence uniform PSD — bypassing Wall 1.

## 5. Wall-1 attack surface (P_N difference-positivity)

Goal: prove `UniformPNDiffNonneg` — `D_N := P_N − P_{N−1}` coefficient-nonneg
for all N. `P_N` is even in `a`; write `p_N(q) = P_N`, `q = a²`. Structural
probe (sympy, exact, N ≤ 8; `/tmp/pn_*.py` methodology):

**Structure found (new this session):**

1. `deg_q p_N = N(N²−1)/3`, `p_N(0) = 1`, lead `(2N−1)!!`.
2. **`[qᵏ]p_N` is a polynomial in N of degree k**, leading coefficient `2ᵏ/k!`
   (so the low-q tail behaves like `e^{2Nq}` as N→∞). Verified k ≤ 8.
3. In the **stable region `N ≳ k`**, column `[qᵏ]p_N` is *binomially positive*
   in N (nonneg Newton forward-differences); the only negative Newton entries
   are O(1) boundary kinks at small N.
4. `p_N` is coefficient-**monotone** (`D_N ≥ 0`) *and* coefficient-**convex**
   (`D²_N = p_N − 2p_{N−1} + p_{N−2} ≥ 0`) in N. Verified N ≤ 8.
5. Bottom coefficients of `D_N` have explicit uniform-in-N forms, manifestly
   `≥ 0` for all N: `[q¹]D_N = 2`, `[q²]D_N = 4N−3`, `[q³]D_N = 4N²−14` (N≥3).

**Dead ends (ruled out — do not retry):**

- **Fixed-degree holonomic recurrence in N**: none up to order 3, `deg_q ≤ 4`
  (exact nullspace search). And `deg_q p_N ∼ N³` *grows*, so no fixed-`q`-degree
  N-recurrence can exist — this kills the "induction via recurrence"
  formalization route (and re-confirms `PNInduction`'s fixed-depth negative).
- **q-product factorization**: `p_N` is irreducible over ℚ (no `∏` formula).
- **J-fraction / Stieltjes path model for `p_N`**: weights rational with `p_k`
  in the denominator once `S_N²` is divided out (`PNPaths`).
- **Telescoping tower** `D_N → D²_N → D³_N → …`: each order reduces to the next
  (convexity gives `D_N = D_2 + Σ_{k≤N} D²_k`), but it does not terminate
  uniformly — `[qᵏ]` only vanishes after `k+1` differences, and k is unbounded
  per N. Same wall one order up.

**The live surface (recommended attack):** a **direct positive determinant /
LGV model for `p_N` itself** — exhibit `p_N = det(M_N)` (or a non-intersecting
path generating function) with `M_N` having *nonneg-coefficient polynomial*
entries, absorbing the `S_N²` cyclotomic square into a rescaled orthogonalized
character basis **without** sign-bearing rescalers. The obstruction is concrete:
the natural rescalers `(a^{2j}−1)` carry a negative constant term, so dividing
them in introduces signs. Irreducibility of `p_N` forbids a *product* but not a
positive *determinant/path sum*; the coefficient-convexity (#4) hints at a
doubly-graded structure worth a two-variable LGV/Motzkin-path model. This is the
genuine research kernel.

**Reachable partial (formalizable now, low effort):** uniform-in-N
nonnegativity of the *bottom strip* of `D_N` — the explicit closed forms
`[qᵏ]D_N` for small fixed k (degree-k polynomials in N, manifestly `≥ 0` for
N ≥ 3) proved from the polynomial-in-N structure + a finite boundary `decide`.
Closes the wall on the low-q coefficients for *all* N; the bulk stays
`decide`-per-N. Honest but marginal — it does not reach the bulk coefficients
(which, for fixed N, sit at `k ∼ N³`, deep in the boundary region where the
polynomial-in-N description does not apply).

**Verdict:** the difference-positivity is now precisely characterized. The
elementary routes (recurrence, product, value-positivity, telescoping) are
exhausted; the one route with genuine headroom is a sign-clean combinatorial
(determinant/LGV) model for `p_N`, which is a real research problem, not a
mechanical formalization.

### 5b. Determinant-model deep dive (sympy + OEIS + literature sweep)

A focused search (q-enumeration, direct determinant-model fitting, and a
literature sweep) sharpened the picture but did **not** find a model that proves
coefficient-positivity. Durable findings:

- **`P_N(1) = ∏_{k=1}^{N−1} (2k+1)!/(k!)²`** (the per-factor ratio is OEIS
  A002457; `q=1` is the flat-Weyl `a=1` limit; these are Legendre/Jacobi OP
  squared-norms `h_k = (2k+1)C(2k,k)`). The product `6,180,25200,…` and the
  `P_N` rows are **not in OEIS** — the object is uncatalogued.
- **`P_N` is irreducible over ℚ** and **not palindromic** (but log-concave /
  unimodal). Irreducibility ⟹ `P_N` is NOT a principal specialization or any
  symmetry-class (plane-partition / ASM / single-character) generating function
  — all of those factor into cyclotomics. Non-palindromic ⟹ not a symmetric
  volume/box statistic. Any q-enumeration realizing `P_N` must use a
  **non-principal** (descent / major-index / charge-type) statistic.
- **The Gram is Hankel−minus−Toeplitz** — the determinantal signature of
  **symplectic `Sp(2N)` / odd-orthogonal `SO(2N+1)` characters** (Okada /
  Krattenthaler). This is the natural "home" of `P_N`; the recommended live
  route is an `Sp(2N)`-character / non-intersecting-path (LGV) realization with
  a non-principal weight.
- **Literature: no published evaluation.** `S_N` is exactly the
  Stieltjes–Wigert / Chern–Simons q-Vandermonde (the "trivial" factor). The
  moments are **differentiated Jacobi-theta** coefficients (`a·m_{r−1}=r a^{r²}`),
  so `Δ_N` is a theta-derivative Hankel / Toda–KP tau-determinant; the `(s+1)`
  derivative factor moves it off every named q-orthogonal family (Stieltjes–
  Wigert, q-Hermite, Al-Salam–Chihara), and no theorem gives coefficient-
  positivity of such tau-determinants. Refs: Krattenthaler *Adv. Det. Calc.*
  (math/9902004) & *Complement* (math/0503507); Cigler–Zeng (0905.0228);
  Takahashi–Katori (1312.5848); elliptic-DPP (1804.07994).
- **Recurrence-coefficient relation (live structural lead):**
  `λ_k = [∏_{j≤k}(a^{2j}−1)]² · P_{k+1}P_{k−1}/P_k² / 4`, i.e. `λ_k` has
  denominator exactly `P_k²` — a **Toda / log-concavity relation**
  `P_{k−1}P_{k+1} = (manifestly-nonneg cyclotomic)·(positive)·P_k²`. A
  Dodgson/Toda recursion plus induction on coefficient-positivity is the
  realistic self-contained route (no closed form to import).

- **Near-miss (do not mistake for a proof):** a non-symmetric tridiagonal
  `P_N = det J_N` with nonneg-coefficient (but rational, denominator-growing)
  entries exists, via the gauge freedom `g_{k} → g_{k} + r·P_{k}` of the
  non-symmetric Jacobi form. But its recurrence `P_n = b_n P_{n−1} −
  g_{n−1}P_{n−2}` carries a **minus**, and tridiagonal total-nonnegativity gives
  only **value**-positivity (`P_N(q) ≥ 0`, already known), NOT coefficient-
  positivity. Not a closer.

**Refined verdict:** `nonnegCoeffs P_N` is a *genuinely novel* positivity of a
theta-derivative Hankel-determinant residual, symplectic-character-flavored and
irreducible, uncatalogued and unaddressed in the determinant-calculus
literature. The two routes with real headroom — an `Sp(2N)`/LGV non-principal-
weight enumeration, or a Dodgson–Toda induction off the `λ_k` relation — are
research programs, not mechanical formalizations. The Wall-2 (analytic) route to
the same uniform PSD remains the alternative.
