# J04: RP Cauchy–Schwarz shape for `SU2LogConvexGap` (2026-10-07 PT)

**Consumer.** `SU2LogConvexGap.LogConvex G L := ∀ j, j+2 ≤ L → G(j+1)*G(j+1) ≤ G j * G(j+2)`, where `G : Nat → Q'`.
It is rational and cross-multiplied, with no roots. `Pos G L` is a separate hypothesis.

**Agreed producer shape** (`SU2TorusRPCSShape`, definitions only):

* `rpB hM β K F G := ∫_{|torusLinks (2M)|} thetaT(F) · G · Π_{torusPlaquettes} T_K`. This is the unnormalised
  `T_K` weight. Normalisation by `Z > 0` cancels in CS.
* `PtSup F`: every variable that occurs lies in a `Pt M` block of `torusLinks`. Constants qualify, so the class is
  closed under `F ↦ F − c`, which gives the truncated `F − ⟨F⟩`.
* `TorusRPPoly : ∀ F, PtSup F → 0 ≤ rpB F F` (target 1).
* `TorusCS : ∀ F G, PtSup F → PtSup G → rpB F G * rpB F G ≤ rpB F F * rpB G G` (target 2). This is the same `≤`
  and cross-multiplied form as `LogConvex`.

**From CS to `LogConvex`.** This step is not done here. It needs `G(n) := rpB F (τ_n F)` with time translation
`τ`, and the identity `rpB (τ_x F) (τ_y F) ≈ G(x+y)` (transfer structure), so that `TorusCS` at `(τ_x F, τ_y F)` gives
`G(x+y)² ≤ G(2x)·G(2y)`. Odd `j` additionally needs the CS for the pair `(F, τ_1 F)`. This is a separate open item.

**Proof plan.**
1. A monomial decomposition `PtSup F → F ≡PE eval (obsOf F)`, with `OnLinks Pt`, reduces `TorusRPPoly` to
   `torus_rp`.
2. Bilinearity of `rpB`: `thetaT` is a `RingSub`, and Haar is linear.
3. Symmetry `rpB F G ≈ rpB G F`: by Θ-invariance of Haar (`theta_haar`), `Θ Π T_K ≡ Π T_K` (`theta_prod` over all
   torus plaquettes), and `Θ∘Θ ≡ id` on supported polynomials. All quantities are real, because Θ includes the
   quaternion conjugation on time links, so there is no complex conjugate.
4. Rational polarization: `0 ≤ rpB(sF+tG, sF+tG) ≈ s²a + 2st·b + t²c`.
   * Take `(s,t) = (c, −b)` to get `c(ac−b²)`.
   * Take `(−b, a)` to get `a(ac−b²)`.
   * Take `(1, −b)` with `a ≈ c ≈ 0` to get `−2b²`.
   * Case on the decidable `0 < c` and `0 < a`.

   Q' identities reduce to Int, closed by `simp only [Int.mul_add, …, Int.mul_comm, Int.mul_left_comm]; omega`
   (checked [propext, Quot.sound]; `grind` brings in Classical and is avoided).

Integer discriminant core `SU2TorusRPCSCore.cs_int` and rational form `SU2TorusRPCSRat.cs_q` (`(∀ s t : Int, 0 ≤ quad a b c s t) → b*b ≤ a*c`): PROVED ([propext, Quot.sound]). Symmetry `SU2TorusRPSym.rpB_symm`: `rpB (eval e) (eval e') ≈ rpB (eval e') (eval e)` for observables on torus links,
via `theta_haar`, `theta_prod`, `tp_mir_perm` and `theta2_obs` (`Θ∘Θ ≡ id`): PROVED ([propext, Quot.sound]).
Bilinear expansion (`SU2TorusRPBil`) and `PtSup F → F ≡PE eval (obsOf F)` (`SU2TorusRPObsOf.obsOf_pe`, `obsOf_on`):
PROVED ([propext, Quot.sound]).

**Interface needed from the Prover (time translation, item 3).** `τ : Nat → RatPoly → RatPoly` such that:
(i) `PtSup F → PtSup (τ n F)` (or the `Obs` analogue `OnLinks (· ∈ Pt M)`);
(ii) `rpB (τ x F) (τ y F) ≈ G(x+y)` with `G n := rpB F (τ n F)`, i.e. `Θ∘τ_x = τ_{-x}∘Θ` under the T_K measure,
plus invariance of `Π T_K` under time shifts.
Then `TorusCS` at `(τ_a F, τ_{a+1} F)` gives `G(2a+1)² ≤ G(2a)·G(2a+2)`, which is `LogConvex` at even `j`. Odd `j`
needs a half-step convention (for example reflecting through a link-midpoint plane instead of a site plane). That
choice belongs to the Prover.

**Obs-level CS PROVED:** `SU2TorusRPCSObs.torus_cs_obs`. For `OnLinks (· ∈ Pt M)` observables `e, e'`,
`rpB F G * rpB F G ≤ rpB F F * rpB G G` with `F = eval e`, `G = eval e'` (truncated T_K weight, fixed K). It uses the
bilinearity in `SU2TorusRPBil`. Axioms [propext, Quot.sound]. `Obs` contains constants and is closed under `+`, `·`
and negation, so the truncated `F − c` is again an `Obs`.

**General `PtSup` versions PROVED:** `SU2TorusRPPolyCS.torus_rp_poly : TorusRPPoly hM β K` and
`SU2TorusRPPolyCS.torus_cs_poly : TorusCS hM β K` (for `0 ≤ β`; truncated T_K weight, fixed K), via `rpB_obsOf`.
Axioms [propext, Quot.sound].

**STATUS: SU(2) torus RP and RP Cauchy–Schwarz for `PtSup` polynomials (truncated T_K, fixed K) are PROVED. Still OPEN:
time translation `τ` and its interface (Prover), the odd-`j` convention, `K → ∞`, and LogConvex. J04 (all compact
simple groups) remains OPEN; this is SU(2) only.**

## Correlator identity: who owns what (agreed split, 2026-10-07)

**Prover owns (PROVED, `SU2TimeShift`, read-only to us):** `vs`, `shv`, `tAdd_vs`, `perm_shift` (slice families),
`TKi`, and `tk_shift : TK links (shv t p) = TKi (idxOf ∘ shv t) p` (plain equality).

**Torus-RP side owns (this track; all OPEN unless marked):**
1. `τ_t : RatPoly → RatPoly`, the block reindex `idxOf ℓ ↦ idxOf (shv (2M) t ℓ)` on `torusLinks (2M)`.
   DEFINED as `SU2TorusTau.tau`. PROVED: `SU2TorusTauVar.tau_lv` (`qsub τ_t (linkVar ℓ) ≡ linkVar (shv t ℓ)`).
2. **On HEAD** (`SU2TorusLinksTimeShift.torusPlaquettes_timeShift_perm`, `torusLinks_timeShift_perm`, from darthur's Mac
   session): full-torus permutation `(torusPlaquettes N).map (shv N t) ~ torusPlaquettes N`, and likewise for links. The
   box-only duplicates (`SU2TorusShiftPerm`) were dropped.
3. **PROVED** (`SU2TorusTauTK.tau_ringSub`, `tau_TK`, `tau_prod`): `τ_t (Π_p TK p) ≡PE Π_p TK p`, via `tk_shift` and item 2.
   Also PROVED: `shift_inv`, i.e. `∫ τA·τB·Π T_K ≈ ∫ A·B·Π T_K` (time-shift invariance of the `T_K` torus integral).
4. Haar invariance under `τ_t`. The existing reindex machinery (`SU2TorusRPReindex`) covers block *involutions*
   only. Plan: write `τ_t = ρ_t ∘ ρ_0`, where `ρ_c` is the pure time-coordinate index involution `a ↦ c − a (mod N)`
   (no conjugation). Then `quaternionHaar_reindex` applies to each factor. PROVED (`SU2TorusTimeRefl`): `rt_inv`,
   `rt_comp` (`ρ_t ∘ ρ_0 = vs t` on the time coordinate). Also PROVED: the block involution `SU2TorusTimeRefl.sigma`, the map
   `SU2TorusTau.tau N t hN := σ_t ∘ σ_0`, and `haar_tau` (`∫ τ_t X ≈ ∫ X` for supported `X`).
5. Link level PROVED (`SU2TorusReflShift.refl_shift`: `reflLink (shv x ℓ) = shv (2M − x%2M) (reflLink ℓ)` on the box).
   Polynomial level on link observables PROVED (`SU2TorusThetaTau.theta_tau_obs`: `Θ(τ_x(eval e)) ≡ τ_{2M−x%2M}(Θ(eval e))`).
   **Correlator identity PROVED on link observables** (`SU2TorusCorrelator.corr_obs`, [propext, Quot.sound]):
   `rpB (τ_x F) (τ_z F) ≈ rpB F (τ_{x+z} F)` for `F = eval e`, `e` on torus links, every `x, z`, `β`, `K` (truncated T_K weight,
   fixed K). Also proved: `tau_tau_obs` (`τ_{−x} τ_{x+z} F ≡ τ_z F`).
   OPEN: (a) the `PtSup` (general polynomial) extension via `obsOf`; (b) `PtSup`/`Pt M`-support of `τ_a F`, which is needed
   before `torus_cs_poly` applies to `(τ_a F, τ_{a+1} F)`. It holds only if the support of `F`, shifted by `a+1`, stays in the
   positive half. That is a support condition for the Prover to state. Then `rpB (τ_x F) (τ_y F) ≈ G(x+y)` with `G n := rpB F (τ_n F)`.
   Combined with `torus_cs_poly`, this gives `G(x+y)² ≤ G(2x)·G(2y)`. `τ_x F` must remain `PtSup`, which needs
   `x + (support time) ≤ M`. This is a real restriction and must appear in the statement.
6. **Odd `j` (corrected).** The proved `reflLink` (`rt`: `a ↦ 1 − a mod 2M`) is a *link-midpoint* reflection
   (planes at ½ and M+½). Then `⟨Θ τ_x F · τ_y F⟩ ≈ G(x+y)`, and CS at `(τ_a F, τ_{a+1} F)` gives
   `G(2a+1)² ≤ G(2a)·G(2a+2)`, which is `LogConvex` at EVEN `j`. ODD `j` needs `2x = j` with integer `x`, which is impossible
   with this reflection. It needs RP for a *site-plane* reflection (`a ↦ −a`), and that is OPEN: the layout proof covers
   only the midpoint plane. Alternative that needs no new RP: the Prover consumes `LogConvex` for even `j` only, or for
   `n ↦ G(2n)`. The choice belongs to the Prover.

**Consumer on HEAD:** `SU2TorusGapCond` takes `hshift : rpB (τ x) (τ y) ≈ G (x+y)` as a hypothesis. For
`τ x := tau (2M) x (eval e)` and `G n := rpB (eval e) (tau (2M) n (eval e))`, `SU2TorusCorrelator.corr_obs` discharges
it for every `x, y`. `hsup` (`PtSup (τ x)`) is still the caller's obligation, and is OPEN for general `e`. HEAD's
`SU2TorusCenteredPairShift.hshift` proves the same shape for OWN-centred single-plaquette characters at `betaS`.

**Prover consumes:** item 5 plus `torus_cs_poly` to produce `LogConvex`. The Prover does not reprove items 1–4.

## K → ∞ (status, precise)

PROVED ([propext, Quot.sound]; strong coupling `0 ≤ β`, `2·256·β ≤ 1`; fixed torus `2M`):
* `SU2TorusRPKTail`: `T_{K+j} = T_K ++ tail` (a literal list identity), `l1 tail ≤ 2 (256β)^{K+1}` uniformly in `j`, and
  `l1 T_K ≤ 2`.
* `SU2TorusRPKProd`: telescoping `Π(T_K + D) ≡PE Π T_K ++ E`, `l1 E ≤ eb 2 δ |P|`, and `haar_diff`.
* `SU2TorusRPKCauchy.rpK_cauchy`: `RPKCauchy` for ANY `F G`, i.e. `|rpB_{K+j} F G − rpB_K F G| ≤ l1(ΘF·G) · eb 2 (2(256β)^{K+1}) |P|`
  for all `K, j`. The rate is explicit and independent of `j`, but NOT volume-uniform (`eb 2 δ n ~ n·2^n·δ`).
* `SU2TorusRPKLimit.rp_closed` / `cs_closed` and `SU2TorusRPKClosed.cs_limit`: any rationals that the `rpB_K` approximate
  within `r K` satisfy RP (`0 ≤ x + 2r K`) and CS (`a·a ≤ b·c + 2 s K`, `s K = (C + r K) r K + C r K`).

Route note: the ℓ¹ monomial tail with `wilsonA_pow2_le` is used, not `wCoeff_cauchy`. The per-character rate
`c_s^{(K+j)} − c_s^{(K)} ≤ 2β^{K+1}` is per `s`, and summing it over `s ≤ K+j` is not uniform in `j`.

**NOT proved / not claimed:** no limit object (CReal or otherwise) is defined; the untruncated Wilson weight is not
constructed. The weak-coupling regime is not covered. No volume-uniform rate is given. `C` (a uniform bound on `|rpB_K|`)
is a hypothesis of `cs_limit`; it follows from `l1(ΘF·G)·2^{|P|}` but that corollary is not written.
