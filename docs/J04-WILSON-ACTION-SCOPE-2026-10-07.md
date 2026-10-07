# J04 — SU(2) Wilson action: scope (2026-10-07, YM Group Realizer)

> **STRONG COUPLING ONLY (β ≲ 1e-4).** This track gives a volume-uniform strong-coupling cluster
> expansion for the actual Wilson action. It is equally true for U(1). It is **NOT** evidence for the mass gap
> or the continuum limit. YM Bot accepted this scope on 2026-10-07.
>
> Directions (YM Bot): no reciprocals. Work with the unnormalised Z, carry `c_0^{|P|}`, and use cross-multiplied
> ratios. `β` stays a free rational in the envelope, with a concrete pass lemma at some β₀.
> Simplified envelope (replaces the G-bound below): the dimension identity `Σ_s (s+1) c_s = Σ_k a_k 2^k`
> (evaluation at U = 1) gives `B_K + c_0 = Σ_{k≤K} λ^k 2^k/k! ≤ Σ_k β^k`, so `B_K ≤ 2β` for `β ≤ 1/2`.

## Target
Plaquette weight `exp((β/2) tr U_p)`. Its character expansion is
`Σ_s c_s(β) χ_s(U_p)`, with `c_s = 2(s+1) I_{s+1}(β)/β` and `c_s/c_0 = (s+1) I_{s+1}(β)/I_1(β)`.
Everything so far uses the spin-truncated heat-kernel weight `coeffW`.

## What the repo has (checked)
* No Mathlib reals. The constructive `CReal` has `ExpNeg.expNeg` (`e^{-q}`, `q ≥ 0` rational),
  `ExpPos.expPos` (`e^{q}`, `q ≥ 0`, monotone partial sums `partialSumAbs`), `CRealExp.expNegC`
  (CReal argument with an explicit modulus), and geometric tail bounds (`ExpGeomBound`, `ExpNeg.expNeg_tail_bound`).
* There is no polynomial-valued exponential, and no exp of a `RatPoly`. All plaquette machinery is
  `RatPoly` + `RatPolyCoeffEqv` + `quaternionHaar`. `characterPolynomial x s` has `χ_1 = 2x`
  (the trace when `x = u₀`), and `|x| ≤ 1` holds on the sphere (`block_radius_carrier`), so `|tr| ≤ 2`.
* The bounds for a general character list are already done: `SU2PolymerActivityBound`
  (`charSum`/`bSum`/`polymer_activity_abs_le`, shared links allowed) and `SU2PolymerActivityHeat` (`z_abs_le`).

## Formulation choice
**Primary: Wilson = the sequence `T_K` with explicit rational rates.** Here
`T_K(χ_1) = Σ_{k≤K} a_k χ_1^k` and `a_k = (β/2)^k/k!`. It is a polynomial, so it is a `RatPoly`.
Every statement is uniform in `K`, and Cauchy-in-`K` is given at the coefficient level:
`0 ≤ c_s^{(K')} − c_s^{(K)} ≤ tail_s(K)`. A sequence of polynomials is the honest constructive object.
Every Haar quantity converges with a rate, via `plaq_weighted_le`: a coefficient-ℓ¹ error `Σ Δc_s (s+1)`
bounds the weight error on the sphere.
*Rejected as primary:* a real `exp(βx/2)` on `|x| ≤ 2` with an SOS remainder `R_K² − tail² ≥ 0 mod sphere`.
It needs an exp of a polynomial and a certified SOS for every `K`, which the repo lacks. It stays an optional
cross-check at the CReal level: `T_K(x) ≤ expPos(βx/2)` pointwise for rational `x`.

## Key facts (all rational)
* Clebsch–Gordan: `χ_1 χ_{n+1} = χ_{n+2} + χ_n`. So `χ_1^k = Σ_s m(k,s) χ_s` with the Catalan-triangle
  recursion `m(k+1,s) = m(k,s−1) + m(k,s+1)`. Then `m(k,s) = 0` for `s > k` or `k ≢ s (mod 2)`,
  `m(s,s) = 1`, and `0 ≤ m(k,s) ≤ C(k,(k−s)/2) ≤ 2^k`.
* `c_s^{(K)} = Σ_{k≤K} a_k m(k,s) ≥ 0`. It is nondecreasing in `K`, with `c_0^{(K)} ≥ a_0 = 1`.
  For `β > 0` and `s ≤ K`, `c_s^{(K)} ≥ a_s > 0`, so no zero coefficients and no filtering for `PolymerOK`.
* Uniform bound: `c_s^{(K)} ≤ Σ_j (β/2)^{s+2j}/(j!(s+j)!) ≤ (y^s/s!)·G`, with `y = β/2` and
  `G = 1/(1−y²)` for `y < 1`.
* Normalisation: `c_s/c_0 ≤ c_s`, because `c_0 ≥ 1`. The normalised coefficient is `c_s^{(K)} · recip(c_0^{(K)})`
  (`Q'` has `recip`). For concrete rational `β` it is a concrete rational, so no inverse of a polynomial in β
  is ever needed. For symbolic bounds use `c_s/c_0 ≤ c_s`, which avoids the inverse entirely.
* Wilson envelope: `E_W(β) := Σ_{s≥1} (s+1) c_s/c_0 ≤ G·Σ_{s≥1} (s+1) y^s/s! ≤ 2yG/(1−y)`, since
  `(s+1)/s! ≤ 2`. This is rational and uniform in `K`. Example: `β = 1/50` gives `E_W ≈ 0.0204`.

## Lemma list (dependency order; one commit each, < 400 lines)
1. **[DONE, this commit] `SU2WilsonCharacterPower`**: `chi1_mul_succ`, `cc`, `cc_add`/`cc_smul`/`cc_pad`,
   `mul_cc`, `mult`, `mult_vanish`, `chiPow_expand`, `wilsonPoly`, `wCoeff`, `wilsonPoly_expand`
   (`T_K ≅ Σ_{s≤K} c_s^{(K)} χ_s`, exact).
2. `SU2WilsonCoeffBounds`: `mult_nonneg`, `mult_diag` (`m(s,s)=1`), `mult_le_binom`;
   `wilsonA β k = (β/2)^k/k!`; `wCoeff_nonneg`, `wCoeff_mono` (in K), `wCoeff_zero_ge_one`, `wCoeff_pos` (s ≤ K, β > 0);
   `wCoeff_le` (`≤ y^s/s! · G`, uniform in K); `wCoeff_cauchy` (`c_s^{(K')} − c_s^{(K)} ≤ tail` with
   tail `≤ y^{K+1}·2^{K+1}/(K+1)! · 1/(1−2y/(K+2))`).
3. `SU2WilsonActivity`: `wilsonList β K = [(c_s/c_0, s) | s = 1..K]`, `wilsonF := charSum … wilsonList`;
   `bSum_wilson_le : bSum (wilsonList β K) ≤ E_W(β)`, `wilsonList_pos`; then
   `wilson_z_abs_le : −E_W^{|γ|} ≤ quaternionHaar n (Π_{p∈γ} wilsonF p) ≤ E_W^{|γ|}`, reusing
   `polymer_activity_abs_le` and the `heatPolymer`-style plumbing from `SU2PolymerActivityHeat`.
4. `SU2WilsonPolymerIdentity` (Prover side or joint): `T_K(plaq) ≅ c_0·(1 + wilsonF)` (from item 1 plus
   `χ_0 = 1`), then the `polyPartition_eq_Xi` analogue via the Prover's generic `polymer_identity`
   (`W F c` with `c ≈ 1` after dividing by `c_0^{|P|}`).
5. `SU2WilsonKCauchy`: the Haar-level rate `|h(Π_p T_{K'}) − h(Π_p T_K)| ≤ …`, from the coefficient
   ℓ¹ differences via `plaq_weighted_le` and the product rule `bnd_mul`.
6. (Optional) the CReal cross-check `T_K(x) ↑ expPos(βx/2)` for rational `x ∈ [−2, 2]`.

## Risks
* **Normalisation by c_0:** use `c_0 ≥ 1` and Q' `recip`. The ≈-congruence of `recip` must be checked
  (`recip` is defined on num/den; it needs a `recip_eqv_congr` or works with fixed representatives).
  Fallback: keep the un-normalised activity and absorb `c_0^{|P|}` into the partition function.
* **Small-β only:** the envelope needs `y < 1` and, for KP, `E_W ≤ ε = 10⁻⁴`, so roughly `β ≲ 10⁻⁴`.
  This is strong coupling only. The continuum (large-β) regime is NOT addressed by this track.
* **Parity / centring:** `c_s` for odd `s` is nonzero (no symmetry kill). Centring removes only `s = 0`.
* **`Nat → Q'` coefficients:** `≈` is not `=`, so all congruences are at `.eqv` (done via `cc_congr`).
* **Elaboration cost:** the reflective `decide` steps use ≤ 7 atoms (the current file checks in about 1.2 GiB).
