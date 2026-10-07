# Scope: one-polymer ratio-Lipschitz bound and the R1 activity envelope (2026-10-07)

## 1. Ratio-Lipschitz (`PolymerRatioLipschitz.lean`, PROVED, GROUP-BLIND PLUMBING)

Everything is in cross-multiplied form; there is no division in Q'.

- **`cross_step` (exact identity):**
  `Ξ(y::S₀)Ξ(T₀) − Ξ(y::T₀)Ξ(S₀) ≡ z_y·(Ξ(S₀∖N y)Ξ(T₀) − Ξ(T₀∖N y)Ξ(S₀))`.
- **`cross_bound`:** two-sided bound `|D| ≤ ε(M+M)·Ξ(S₀)Ξ(T₀)`, under explicit hypotheses
  (|z_y| ≤ ε and 0 ≤ Ξ(X∖N y) ≤ M·Ξ(X)).
- **`deg24_ratio_lip`:** holds for any `Z4BoxGas BL` with `BL.D = 24`, so for both box and
  torus, and for any S₀, T₀ ⊆ polys, with ±z ≤ ε^{|X|}:
  `|D| ≤ ε^{|y|}·2·(5/3)^{|y|}·Ξ(S₀)Ξ(T₀)`.
  - Equivalently, `|R(S₀) − R(T₀)| ≤ C q^{|y|}` with `R(Λ) = Ξ(y::Λ)/Ξ(Λ)`, C = 2 and
    q = ε·5/3 = 1/6000.
  - It is uniform in S₀ and T₀ and in the volume.

**OPEN: decay in graph distance d.** The target is a bound
`|Ξ(Λ)Ξ(Λ∖A∖B) − Ξ(Λ∖A)Ξ(Λ∖B)| ≤ C q^d Ξ(Λ)Ξ(Λ∖A∖B)`.
- **Route:** iterate `cross_step`. Each step removes one neighbourhood and moves the
  "difference front" one polymer closer. Close the d-step chain with
  `truncated_zero_of_decoupled` (an exact zero once decoupled).
- **Needed:**
  - telescoping over the neighbourhood removals Λ∖N(y) = removal of N(y)'s elements one at a
    time, each controlled by `kpw_main`;
  - a path-counting bound (≤ 24^d paths of length d, each weighted by q^{size}).
- **Estimate:** 500–900 lines.

## 2. R1 wall (`HeatKernelPolymerActivityR1.lean`)

### PROVED
- **The w and ε.** w = 1/40 and `plaqEnv M = Σ_{s=1}^M coeffW w s` (the repo's
  `coeffW = (s+1)w^{s(s+2)}`, via `PlaquetteActivity.plaqActivity_le` ≤ 4w³ = 1/16000).
  So `0 ≤ plaqEnv M ≤ ε = 1/10000` for every M.
- **The activity.** `zHeat M γ = plaqEnv(M)^{|γ|}` satisfies `0 ≤ zHeat ≤ ε^{|γ|}`.
- **`heat_kp`.** The KP bounds and the ratio-Lipschitz bound for this activity, on any
  degree-24 gas (box and torus).
- **HKPS hazard.** `Z4FiniteBoxHeatKernelPacketState` was neither imported nor rebuilt.

### OPEN (the R1 wall proper)
- **Missing identity.** Nothing shows that the Wilson heat-kernel partition function
  equals Ξ(gas). The minimal missing identity is the Haar character expansion
  `∫ Π_p (Σ_{s≤M} coeffW w s χ_s(U_p)) dU = Σ_{compatible families} Π_γ z_true(γ)`.
  It needs `z_true(γ)` defined as the Haar integral of the connected character products
  on γ.
- **Missing bound.** It also needs `|z_true(γ)| ≤ zHeat M γ`, which uses |χ_s| ≤ dim s.
  That bound is already folded into coeffW.
- **Status.** `zHeat` is therefore an *envelope* activity, not the true one.

### Related repo files
- `PlaquetteActivity` (L0a);
- `NonpertActivityHeatKernel`, `ConnectedActivityAssembly` (the R1 tests);
- the `Z4SpinSummedFaceActivity*` envelopes.

None of them provides the gas identity.

## 3. Review fixes (2026-10-07, 01:33 PT)

### (1) Envelope corrected
The earlier text said `|χ_s| ≤ dim s` was "absorbed in coeffW". **That was wrong.** Bounding
the character costs a second factor of (s+1).

- **New envelope:** `charEnv w M = Σ_{s=1}^M (s+1)²·w^{s(s+2)}`, and
  `zHeat M γ = charEnv(1/40, M)^{|γ|}`.
- **Certified threshold interval for |z| ≤ ε = 1/10000:**
  - `charEnv_pass`: at w = 1/40, `0 ≤ charEnv ≤ ε` for every M. The tail is geometric with
    ratio 4w³ = 1/16000, and the invariant is `charEnv ≤ c − c·r^M`.
  - `charEnv_fail`: at w = 1/20, `charEnv > ε` for every M ≥ 1, because the s=1 term alone is
    4w³ = 1/2000.
  - So the threshold w* lies in [1/40, 1/20).
- `PlaquetteActivity.plaqActivity` (the coeffW sum, without the character factor) is no
  longer used.

### (2) Activity hypotheses
- The general KP results assume **only the lower bound `z X ≥ −ε^{|X|}`**:
  - `kpw_main` / `deg24_kp` / `z4_kp` / `torus_kp` (hypothesis `hz1`).
- The decay and Lipschitz results need the **two-sided `|z X| ≤ ε^{|X|}`** (`hz1` + `hz2`):
  - `deg24_ratio_lip`;
  - the d-decay in progress.
- `zHeat` satisfies both, since `0 ≤ zHeat ≤ ε^{|γ|}`.
