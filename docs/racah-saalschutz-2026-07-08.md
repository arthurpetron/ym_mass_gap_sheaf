# A2 `guardedBEDougall` — the deg-≤4 Saalschütz factor-decomposition route

**Verdict (honest, machine-adjacent):** the deg-≤4 Saalschütz/Vandermonde
decomposition **does NOT close** A2's guarded Racah sum rule. The irreducibly
high-degree factor is the **inner Racah `t`-sum `Sᵢ(x)` itself** — its length grows
without bound in the spins — so no fixed product of deg-≤4 polynomial identities in
the nine labels can span `guardedBEDougall`. A **streaming (parametric/unbounded-
degree) normaliser** is required for the full identity. The route DOES cleanly
close one genuine deg-bounded ∀-spins factor (the degenerate `p=q=r=0` slice, via a
telescope), which is now proved in Lean.

Files: `lean/YMGap/Continuum/RacahSaalschutz.lean` (new), `computations/racah_saalschutz.py` (new).
Build green (`lake build` exit 0); guard OK ("5 Clay-frontier types unconditionally uninhabited"); axiom-clean.

---

## 1. Why the full certificate does NOT factor into deg-≤4 pieces (the refutation)

Ground-truthed bit-for-bit against the Lean `Q'`/`Nat` objects in
`computations/racah_saalschutz.py`:

- **Inner factor grows.** The single-variable inner Racah `t`-sum `Sᵢ(x)` has a
  nonzero-term count that grows *linearly* with the spins — on the `{n n 2n; n n n}`
  diagonal the lengths are `1,2,3,4,5,6,7,8,9` for `n=0..8`, with non-constant
  values (`1, 96, −17010, −20160000, …`). A growing-length alternating sum with
  non-constant value is **not** a single hypergeometric term: no order-0 (Gosper)
  closed product, no fixed-degree polynomial closed form.
- **Coupled outer count grows.** On the fully-symmetric ray (all spins `n`) the
  number of coupled `(x;t₁,t₂,t₃)` summand tuples is `1,10,45,136,325,666,1225`
  (quadratic growth); the outer `x`-support is `1,3,5,7,9,11,13`.
- **Consequence.** A fixed product of deg-≤4 polynomial identities in the nine
  labels is a fixed finite object; it cannot equal a sum whose term-count is
  unbounded in those same labels. Hence `RacahDougallWZ.CoupledCreativeTelescoping`
  is **not** deg-≤4-decomposable. This confirms and sharpens the prior agent's
  "factorial-degree Wegschaider certificate" finding: the factorial degree is the
  *inner Racah sum's unbounded length*, not an artifact of clearing.

Corroborating: a Pfaff–Saalschütz `n=2` balanced ₃F₂, cleared to integer
polynomial form, already reaches total degree ≈ 6–7 in `(A,B,C)` — beyond the deg-4
normaliser. The Saalschütz members themselves outrun the deg-≤4 kernel past the
first nontrivial order, independent of the coupling.

## 2. The genuine deg-bounded ∀-spins factor the route DOES close

On the degenerate slice `p=q=r=0` (which `outerAdm` forces to `a=d=e=m`,
`b=c=f=n`), **every inner Racah sum carries a zero label**, so each is a single
closed term (a 6j with a zero entry is a Kronecker delta). The outer sum collapses
to a single-variable signed-dimension telescope, Python-verified exactly:

  guarded slice weight `w(x) = (−1)^{m+n}(x+1)` on `x = |m−n|, |m−n|+2, …, m+n`,
  and `Σ w(x) = (−1)^{m+n}(m+1)(n+1)` = `beRationalRHS` = the RHS 6j-pair value
  (0 fails over `[0,6]²`).

This is exactly `int_telescope` territory. **Proved ∀-spins in Lean**
(`RacahSaalschutz.lean`, all `propext`/`Quot.sound` only):

| theorem | statement | how |
|---|---|---|
| `apCertBase` | `(n+1)(b+(n+1)) − n(b+n) = b+2n+1`, ∀ `n,b:Int` | `Int.mul_add`/`add_mul` + `omega` abstracting nonlinear atoms `n·b`,`n·n` (NO `ring`) |
| `apCert` | `apF b k = apG b (k+1) − apG b k` (antidiff cert `g(k)=k(b+k)`) | `apCertBase` |
| `apSum` | `Σ_{k<K}(b+2k+1) = g K − g 0`, ∀ `b,K` | `int_telescope` |
| `apSum_closed` | `Σ_{k<K+1}(b+2k+1) = (K+1)(b+K+1)`, ∀ `b,K` | telescope + `omega` |
| `apDim` | `Σ_{k<m+1}((n−m)+2k+1) = (m+1)(n+1)`, ∀ `m≤n` | `apSum_closed` + `omega` |

**Non-vacuity — the abstract telescope hits the ACTUAL guarded Racah objects** (all
`decide`, axiom-free): `slice_val_{1_1,2_2,1_2}` prove
`guardedBERationalLHS = beRationalRHS` at slice tetrahedra `(m,n,n,m,m,n,0,0,0)`,
and `slice_dim_{1_1,2_2,1_2}` prove those equal the telescoped dimension values
`Q'.ofInt {4, 9, −6}` = `(−1)^{m+n}(m+1)(n+1)`. `slice_outerAdm_2_2` certifies the
slice is genuinely admissible.

## 3. What stays NAMED-open (NOT faked, no inhabitant)

- `RacahSaalschutz.SliceInnerCollapse` — the ∀-`(m,n)` symbolic step "each inner
  Racah sum with a zero label = its single closed term, so the guarded slice LHS =
  the AP sum". True (Python-exhaustive), telescope-shaped, needs the single-term 6j
  evaluation ∀-spins. Its *outer* telescope is `apDim` (proved); the inner
  evaluation is deferred, carried as a faithful statement.
- `RacahDougallWZ.CoupledCreativeTelescoping` (unchanged) — the full coupled
  certificate, proven NOT deg-≤4-decomposable (§1); the streaming normaliser is its
  correct tool.

## 4. What A2 / loopy-Zreal discharges

**Nothing new is discharged at the top level.** `guardedBEDougall` remains open, so
`general_be_of_rational` → the A2 signed-6j pentagon → the loopy `Zreal` stay
uninhabited (the guard confirms all 5 Clay-frontier types uninhabited). What
advanced: (a) the degenerate `p=q=r=0` *factor* of the guarded Racah sum rule is now
closed ∀-spins via the telescope; (b) the obstruction is now *sharply located* — the
growing inner Racah `t`-sum — which is a machine-adjacent refutation of the deg-≤4
route and the precise specification for the streaming normaliser the concurrent
agent owns.

## 5. Verification

- `lake build` exit 0 (full project). `lake build YMGapGuard` exit 0;
  `YMGapGuard.lean:84: frontier-guard OK: 5 Clay-frontier types unconditionally
  uninhabited across YMGap.*`.
- `#print axioms` on all 12 new theorems ⊆ `{propext, Quot.sound}` (the `slice_*`
  `decide`s depend on no axioms at all). No `native_decide`, `sorry`, `admit`,
  `ring`, `nlinarith`, or new `axiom` in `RacahSaalschutz.lean` (confirmed by grep).
- `RingNormaliser.lean` / `RacahDougallWZ.lean` / `SixJKernel.lean` /
  `BiedenharnElliottGeneral.lean` **not edited** (read-only, as coordinated). Only
  new files + one import line in `YMGap.lean`. No commit made.

## 6. Honest one-line answer to the task question

> Does the deg-≤4 Saalschütz decomposition close A2's guarded Racah sum rule, or
> which factor is irreducibly high-degree?

It does **not** close it. The irreducibly high-degree factor is the **inner Racah
`t`-sum `Sᵢ(x)`**, whose nonzero-term length grows linearly with the spins (and
whose coupled-summand count grows quadratically); this cannot be captured by any
fixed product of deg-≤4 label-polynomial identities. → the **streaming normaliser**
is needed for the full `guardedBEDougall`. The deg-≤4 route cleanly closes exactly
the degenerate `p=q=r=0` factor (proved ∀-spins here as an `int_telescope`), and
otherwise sharply certifies its own boundary.
