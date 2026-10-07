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
2. **PROVED** (`SU2TorusShiftPerm.tp_shift_perm`, `tl_shift_perm`, any `t`, [propext, Quot.sound]): full-torus permutation `(torusPlaquettes N).map (shv N t) ~ torusPlaquettes N`, and likewise for links.
3. **PROVED** (`SU2TorusTauTK.tau_ringSub`, `tau_TK`, `tau_prod`): `τ_t (Π_p TK p) ≡PE Π_p TK p`, via `tk_shift` and item 2.
   Also PROVED: `shift_inv`, i.e. `∫ τA·τB·Π T_K ≈ ∫ A·B·Π T_K` (time-shift invariance of the `T_K` torus integral).
4. Haar invariance under `τ_t`. The existing reindex machinery (`SU2TorusRPReindex`) covers block *involutions*
   only. Plan: write `τ_t = ρ_t ∘ ρ_0`, where `ρ_c` is the pure time-coordinate index involution `a ↦ c − a (mod N)`
   (no conjugation). Then `quaternionHaar_reindex` applies to each factor. PROVED (`SU2TorusTimeRefl`): `rt_inv`,
   `rt_comp` (`ρ_t ∘ ρ_0 = vs t` on the time coordinate). Also PROVED: the block involution `SU2TorusTimeRefl.sigma`, the map
   `SU2TorusTau.tau N t hN := σ_t ∘ σ_0`, and `haar_tau` (`∫ τ_t X ≈ ∫ X` for supported `X`).
5. Link level PROVED (`SU2TorusReflShift.refl_shift`: `reflLink (shv x ℓ) = shv (2M − x%2M) (reflLink ℓ)` on the box).
   OPEN: polynomial level `Θ∘τ_x ≡ τ_{−x}∘Θ` on `PtSup`/`Sup` polynomials. Then `rpB (τ_x F) (τ_y F) ≈ G(x+y)` with `G n := rpB F (τ_n F)`.
   Combined with `torus_cs_poly`, this gives `G(x+y)² ≤ G(2x)·G(2y)`. `τ_x F` must remain `PtSup`, which needs
   `x + (support time) ≤ M`. This is a real restriction and must appear in the statement.
6. **Odd `j` (corrected).** The proved `reflLink` (`rt`: `a ↦ 1 − a mod 2M`) is a *link-midpoint* reflection
   (planes at ½ and M+½). Then `⟨Θ τ_x F · τ_y F⟩ ≈ G(x+y)`, and CS at `(τ_a F, τ_{a+1} F)` gives
   `G(2a+1)² ≤ G(2a)·G(2a+2)`, which is `LogConvex` at EVEN `j`. ODD `j` needs `2x = j` with integer `x`, which is impossible
   with this reflection. It needs RP for a *site-plane* reflection (`a ↦ −a`), and that is OPEN: the layout proof covers
   only the midpoint plane. Alternative that needs no new RP: the Prover consumes `LogConvex` for even `j` only, or for
   `n ↦ G(2n)`. The choice belongs to the Prover.

**Prover consumes:** item 5 plus `torus_cs_poly` to produce `LogConvex`. The Prover does not reprove items 1–4.

## K → ∞ (status, precise)

`SU2TorusRPKLimit` (PROVED, [propext, Quot.sound]):
* `closed_le`;
* `rp_closed`: any rational `x` with `|x − rpB_K F F| ≤ r K` for all K satisfies `0 ≤ x + 2 r K`;
* `cs_closed`: the analogue for `TorusCS`.

`RPKCauchy F G r` (`∀ K j, |rpB_{K+j} F G − rpB_K F G| ≤ r K`) is a **definition only, OPEN**. It needs a Haar-level
rate for `Π T_{K'} − Π T_K`. Plan: use `l1` (`haar_abs`, `l1_mul`, `l1_add_le`) on `T_{K+j} − T_K =
Σ_{k=K+1}^{K+j} a_k χ-powers`, with factorial decay of `wilsonA`. `wCoeff_cauchy` is the character-basis rate; it
applies via `plaq_weighted_le`/`bnd_mul`, but at strong coupling only (`2β ≤ 1`).
**No limit object (CReal or otherwise) is defined. Nothing about the untruncated Wilson measure is proved.**
