# Adversarial audit of R1: `Δ²V(N) ≥ −2`

**Verdict.** SOUND on the binding branch: I could not break the claim, and the hard
odd-`N`/`w≤½` face is rigorously reduced to a terminal scalar `φ(q)≥0` whose explicit
two-region rational certificate I independently reproduced with positive margin at every
node. One genuine but **non-fatal completeness gap**: the even-`N`, `w∈(0,½]` cell is
discharged in the memos only by an "even parity ⇒ larger margin" assertion backed by
numerics, not by a written certificate — the odd-`N` machinery (φ-chain, Task-A ratio
bound, both explicitly scoped "over odd `N`") does not cover it. It is numerically safe
(margin ≥ 2.13) so it is fixable, not a counterexample.

All computations below are independent (my own from-scratch code, `mpmath`, dps 50–360,
none reused from the project verifiers). Scripts in `/tmp/audit_*.py`.

---

## 1. Independent ground truth (oracle)

Brute-force `V(N)=4·Var(X|X+Y=N)` with `P(X=k)∝ k·w^{k²}`, direct conditional summation,
over a fine `w`-grid (`i/1000`, plus `w=10^{-k}` and `w→1`) and `N=2..60`:

- `Δ²V(N)+2 > 0` **everywhere**; grid infimum `6·10⁻¹⁶` at `(w=10⁻⁸, N=3)`, i.e. the
  true infimum is `0⁺` approached along **odd `N`, `w→0`**. Confirmed to dps 360 down to
  `w=10⁻¹²`: `(Δ²V+2)/w² → 6, 13.111, 14.611` for `N=3,5,7` — never a sign flip.
- Exactly `12/11 = 1.09090909…` at `(w=½, N=3)`; `V(2)=0`, `V(3)=1`, `V(4)|_{½}=12/11`.
- Global even-`N` infimum `= 12/7` (at `≈(1/√2,4)`); odd-`N` is the binding parity.

This **matches the claimed min structure exactly** (`12/11` corner; `0⁺` along odd `N`,
`w→0`). The theorem R1 is TRUE numerically. The audit is therefore about the *proof*.

## 2. Chain re-derivation — each reduction confirmed as an identity/valid inequality

| step | check | result |
|---|---|---|
| `Δ²m = ½ + ¼Δ²V`, so `Δ²m≥0 ⟺ Δ²V≥−2` | algebra: `E[X²|N]=(N²+V)/4`, `E[X|N]=N/2` by `X↔N−X` | ✓ identity |
| `Δ²V+2 = (Δ²V_inf+2)+Δ²(tail)`, `tail=V−V_inf` | definitional given `V_inf` well-defined | ✓ |
| `V_inf` validity `N²>G_p` on `w≤½` | `G_o(¼)=1.476<9`, `G_e(¼)=1.410<4`, all `N≥3` | ✓ (divergence only in the `w≥½` branch, where `V_inf` is not used — not a bug) |
| anchor `G_o−G_e = ϑ₄(q)⁴` | matched to **60 digits**, all `w` | ✓ |
| identity `Δ²V_inf+2 = Δ²F_e + 2(f_e−f_o)` (odd `N`) | re-derived by hand + matched to 60 digits | ✓ |
| `L2* = Δ²V_inf+2` (partial-fraction form) | matched to 60 digits | ✓ |
| `L2(N) ≥ Ψ(N)` (`G_o>0`; `0≤G_e≤Ḡ_e`) | direction correct; numerically `L2−Ψ≥0` | ✓ |
| `Ψ(N)≥Ψ(3)` (`S_e≥S_o` + convexity of `x⁻³`) | `S_e−S_o>0` verified; Ψ increasing verified | ✓ |
| `Ψ(3)=φ(q)` | matches `φ(¼)=0.56789` etc. | ✓ |

Every inequality direction is correct (I re-derived the sign of each `1/(x−G)` replacement
by hand). `S_e≥S_o` holds on `q≤¼` (min gap `0.0032` at `w=0.01`). Partial fractions
`f_p=G_p−S_p/(x−G_p)` reproduce the Möbius maps exactly.

## 3. φ-certificate stress test (independent `mp` reimplementation)

Reproduced every constant of `phi_certificate.md` from scratch:

- `Ḡ_e = G_e(¼) = 1.409501468986676377442` — inside the claimed bracket `[…7417, …7418]`. ✓
- `κ = 0.454564 < 73/160 = 0.45625`; `α = 16−32κ = 1.453957`, `α−7/5 = +0.05396`. ✓
- Leading reduction `73Ḡ_e²−1140Ḡ_e+1472 ≥ 0`: value `10.20 > 0`, `Ḡ_e < x₋=1.42043`. ✓
- `φ'' ≥ 37/5` on `[0,1/16]`: my sampled min `= 13.30`; their rigorous floor `7.4` is
  **conservative** (true min ≈ 13.5). ✓
- `sup|φ'|` on `[1/16,¼]`: my sampled max `= 3.527`; their iv bound `3.942`; `L=4`
  strictly dominates both. ✓
- All 13 grid node lower bounds `ℓ_i ≤ φ(q_i)` hold; binding margin
  `ℓ₀−L·h/2 = 0.16131−1/32 = 0.13006 ≥ 1/10` (worst-case `+0.0301`). ✓
- Tail-bound lemma: geometric majorant over-estimates true tails by >50 orders of
  magnitude (`T₂<8.2·10⁻⁹⁷` vs margin `0.03`). Genuinely conservative. ✓
- `min φ/q → α` (attained as `q→0`), so `φ(q) ≥ α·q > 0` on all `(0,¼]`. ✓

The φ-certificate is a **legitimate finite rigorous argument** (convexity + Lipschitz
grid + conservative rational tail), not merely "verified numerically." I could not break it.

## 4. Task A and Task B

- **Task A** (`Δ²(tail)≥0`, `w≤½`, odd `N`): the reduction
  `tail(N−1)≥2·tail(N) ⇒ Δ²tail = (tail(N−1)−2tail(N)) + tail(N+1) ≥ 0` is valid
  (uses `tail≥0`, itself the proved sign-definite pair-sum + the `M=2` boundary
  `tail(2)=−V_inf(2)≥0`, which I confirm: `4B_e−C_e≤0`, `4A_e−B_e>0`).
  With **precision scaled to resolve the super-exponential tail** the true ratio
  `tail(N)/tail(N−1)` maxes at `0.0304` at `(½,3)` — below the claimed rigorous bound
  `0.0571` and far below `½`. `A_e≤1+3w²` holds on `w≤½`. ✓
  *(Caveat: at fixed dps this test suffers catastrophic cancellation — a naïve dps-60
  run reports a spurious ratio of 32 at `w=0.01`. Precision must scale with `(N+2)²/2·|log₁₀w|`.
  Not a flaw in the proof, but a landmine for anyone re-checking Task A numerically.)*
- **Task B** (`w∈[½,1)`): base cases `N=2:3`, `N=3:12/11` (tight, at `w=½`),
  `N=4:12/7` (at `≈1/√2`), `N=5,6,7 ≥ 12/7`; anchor `ϑ₄(¼)⁴=0.0665 ≤ 7/100`.
  Large-`N` two-region floor: I scanned `N=8..250`, `w∈[½,1)` (incl. `w→1`), min
  `= 1.8139 ≥ 12/7`. No dip below `12/11` anywhere. ✓

## 5. The one gap and other notes

- **Completeness gap (non-fatal): even `N`, `w∈(0,½]`.** The φ-chain identity
  `Δ²V_inf+2 = Δ²F_e+2(f_e−f_o)` is derived for **odd** centres (odd centre, even
  neighbours); Task A's ratio bound is stated "over odd `N`". For even centres the
  analogous `L2_even` is never defined or bounded — `r1_remaining_pieces.md` covers this
  cell with "same decomposition; even parity ✓ larger margin," an assertion, not a
  discharged certificate. It is numerically safe (my scan: min `Δ²V+2 = 2.14` on even
  `N`, `w≤½`, rising to `4` as `w→0`), so **fixable** (an even-centre L2 chain, or the
  crude `V(N±1)→1, V(N)→0` bound, would close it) but as written it is not rigorous.
  For `w≥½`, even `N` *is* covered (Task B is parity-agnostic).
- **Status inconsistency across memos (not a math error).** `parity_gap_lemma_proof.md`
  still lists `(L2)` as "**open — the single residual**"; `theta_residual_L2_proof.md`,
  `phi_certificate.md`, and `r1_remaining_pieces.md` then close it. The earlier status
  line is superseded; a reader diffing the memos will see a contradiction that is only
  chronological. `cond_moment_convexity_proof.md` is an exploratory/impossibility memo
  that frames R1 as still-open (its "smallest gap" §4) — its conclusions are superseded by
  the later chain and should not be read as the current status.
- **`N=2` boundary.** Requires the convention `V(1)=0` (empty support `X+Y=1`); then
  `Δ²V(2)+2 = 3`. Robust (any `V(1)∈[0,∞)` keeps it `≥1>−2`). No issue.
- **Impossibility side-claim (§2 of cond_moment memo).** Not load-bearing for R1's truth;
  consistent with the tail-using proof. I did not re-derive the uniform-law counterexample
  in detail (it only motivates *which* proof strategy is needed).

## 6. Bottom line

The **hard, binding face** of R1 — odd `N`, `w∈(0,½]` — is soundly proved: an exact
reduction to `φ(q)≥0` (every algebraic step an identity I verified to 60 digits, every
inequality direction correct) followed by an honest, conservative two-region rational
certificate for `φ(q)≥0` that I independently reproduced with strictly positive margins.
The `w≥½` half and the tail term are cleanly closed with comfortable margins. The only
thing standing between the memos and a fully airtight R1 is the **even-`N`, `w≤½` cell**,
which is true with a large margin but is currently asserted rather than certified — a
write-up gap, not a mathematical error. No `(w,N)` witness breaks the claim.
