# J04 scope: reflection positivity for the torus SU(2) multi-link measure (2026-10-07 PT)

This doc covers the RP row of `audits/SCOPE-R1-CLUSTER-TO-GAP-2026-10-07.md`. The measure is
`SU2TorusMultiLinkPolyGibbs` (`quaternionHaar n` = `multiLinkHaar n`, weights `Π_p W_p`). It is NOT the BF4 slab law.
**STATUS: RP FOR THE ACTUAL TORUS MEASURE IS OPEN.** What is proved is the abstract half-split statement
(`rp_full`, `wilson_rp_full`), with the factorization `hW` as a HYPOTHESIS. The bridge that discharges `hW` for
the torus Wilson integrand has not landed.
The Wilson statements hold for every β ≥ 0 (β-uniform; no strong-coupling label). By itself RP is not gap
evidence. The heat kernel is set aside; Wilson is the target action.

## Formulation (DECIDED: reflection pair of planes, no gauge fixing, split crossing links)

**Why not gauge fixing.** On the periodic torus the crossing temporal links of the two cuts cannot all be set to 1:
together with the time-winding links they carry a Polyakov-loop holonomy that survives any gauge transformation.
The first version of this note was wrong on this point.

**Chosen formulation.**
- **Lattice and reflection:** a torus with even N_t. Θ: t ↦ 1 − t (mod N_t) reflects across the pair of planes
  {t = 1/2, t = (N_t+1)/2}.
- **The halves:**
  - Λ₊ = spatial links at t ∈ {1, …, N_t/2} together with temporal links (x,t)→(x,t+1) for t ∈ {1, …, N_t/2 − 1}.
  - Λ₋ = ΘΛ₊.
  - The crossing temporal links are C₁ = {(x,0)→(x,1)} and C₂ = {(x,N_t/2)→(x,N_t/2+1)}.
- **No gauge fixing.** Each crossing link L is split as a Haar product of a Λ₊ variable B and its reflected copy
  A = ΘB. By Haar invariance, `∫ f(L) dL = ∫∫ f(A*·B) dA dB` at cut 1 and `∫∫ f(B·A*) dA dB` at cut 2.
  - This is the polynomial head shear (`translatedHeadPolynomial_haar`) combined with sign-flip conj invariance
    (`quaternionHaar_signSelected`).
  - There is no Polyakov obstruction, since every link stays an integrated variable.
- **Variables and Θ:** the links are ordered so that blocks 0..a−1 are Λ₊ ∪ {B's} and block a+i is Θ of block i.
  - Each reflected **temporal** link is stored as `conj(shift U)`, via the sign-flip invariance on its block.
    Each reflected spatial link is stored as `shift U`.
  - With this convention Θ is the block translation `shiftPoly a`.
- **Crossing plaquette, cut 1:** spatial links U (t=1) and V = ΘU (t=0), crossing links L, L' at x and x+e. The word
  `V·L'·U*·L*` with `L = A*B` has scalar part `Re(X·Y*)`, where `Y = B·U·B'*` and `X = A·V·A'* = shift Y`.
  - So the scalar is `Σ_c Y_c·shift(Y_c)`, a term of the RPK cone with `A = Y_c`.
  - Cut 2 is the same, with `Y = B*·U·B'`.
- **Non-crossing reflected plaquettes:** the scalar of the reflected word equals the shifted scalar of the original
  word, since `Re(q) = Re(q*)` and traces are cyclic.
- **Target statement (actual torus):** `0 ≤ ∫_{torus} Θ(F)·F·Π_p T_K(U_p)` for F a polynomial in Λ₊ links, the
  integral being the torus `quaternionHaar` over all links.
  - Bridge: (split + conj invariance + reordering by `quaternionHaar_reindex`) turns this into
    `∫_{a+a} ΘF·F·(W₊·ΘW₊·Π_{crossing} T_K(Σ_c Y_c·shift Y_c))`. That is `wilson_rp_full` with the cross kernel
    generalised from `x_{4b+c}` to quaternion-product components `Y_c` (already covered by the RPK cone: any
    `A` on Λ₊).

## Mechanism and what is proved

The crossing scalar is `Re(U V*) = Σ_{c<4} u_c v_c`, a sum of Θ-symmetric products. Haar on `a+a` blocks factorizes
(`haar_factor`), so `∫ (F A)·Θ(F A) = (∫ F A)²`.

### `SU2TorusRPCore` (commit A)

- `sh_mul`: `Θ(pq) = Θp·Θq` (literal).
- RPK cone: `kern a L = Σ c·A·ΘA` with c ≥ 0 and A on Λ₊.
  - `rpk_pos`: `RPK a W → 0 ≤ ∫ F·ΘF·W`.
  - Closure: `rpk_one`, `rpk_append`, `rpk_smul`, `rpk_mul`.
- `rp_full`: if `W ≡ W₊·ΘW₊·W_c` with `W_c ∈ RPK`, then `0 ≤ ∫ ΘF·F·W`.
- Θ is a block translation in this abstract setting. Reflection/conj invariance enters only in the bridge.

### `SU2TorusRPWilson` (commit B)

- `cross a b = Σ_c x_{4b+c} x_{4a+4b+c}` is an RPK. `T_K = Σ_k wilsonA β k · χ₁^k` with `χ₁ = 2σ` is an RPK by
  the power-sum closure. The heat kernel and `D^s` are not used.
- `wilson_cross_rp` and `wilson_rp_full` (any product of crossing `T_K`s, with a positive-half W₊).

## Haar lemmas: exist vs missing

| Need | Status |
|---|---|
| half-split factorization `∫_{a+b} p·shift q = ∫p ∫q` | EXISTS (`haar_factor`) |
| commutative / associative Haar-PE algebra | EXISTS (`SU2HaarAlgebra`) |
| block-involution reindexing `quaternionHaar ∘ reindex = quaternionHaar` | EXISTS (`SU2QuaternionArbitraryHaarBlockReflection.quaternionHaar_reindex`) |
| sign-flip / conj invariance on selected coordinates | EXISTS (`quaternionHaar_signSelected`) |
| split of a crossing link `∫ f(L) = ∫ f(L·A)` (head shear, all degrees) | EXISTS (`translatedHeadPolynomial_haar`). Restated for RP in `SU2TorusRPHaar`. |
| split at an arbitrary block | PROVED (`SU2TorusRPSplitSel.split_sel_cut1/2`) |
| crossing-word identity after the split (coeff level) | PROVED (`SU2TorusRPWord.cross_word_cut1/2`) |
| reflected-plaquette identity | PROVED (`SU2TorusRPWord.refl_word`) |
| quaternion-product crossing kernels, `T_K` congruence, generalized RP | PROVED (`SU2TorusRPKernel.rpk_qdot`, `rpk_cut1`, `wilson_rp_qfull`; `hW` still a hypothesis) |
| torus bridge discharging `hW` | OPEN |
| `D^s` matrix coefficients in real form | MISSING. Needed only for the heat kernel. |

## Heat-kernel plan

- `characterPolynomial x s` (Chebyshev U_s(x)) has alternating-sign coefficients in x. For example,
  `χ₃ = 8x³ − 4x`, so the coefficient of x in `Σ_s c_s χ_s` is `2c₁ − 4c₃ + 6c₅ − …`.
  - The coefficients of the heat-kernel weight in powers of χ₁ are therefore **not termwise nonneg**, and their
    sign is **UNVERIFIED** (correction to the first version of this note).
  - With `c_s ~ w^{s(s+2)}`, lower orders dominate, so they are plausibly ≥ 0 for small w, uniformly in M.
  - Option (0): prove that domination, then reuse the power-sum route with no `D^s`. It needs an explicit
    expansion of `U_s` in powers of x.
- Options:
  - (i) `D^s` route: `χ_s(UV*) = Σ_{ij} D^s_ij(U) conj D^s_ij(V)`. Its real form is a sum of `Re·Re + Im·Im`
    Θ-products, hence an RPK. Each `χ_s(σ)` is an RPK, so the heat kernel is an RPK (coeffW ≥ 0).
  - (ii) Cheaper: show `χ_s(U V*) = Σ` (monomial in u)·(the same monomial in v) with nonnegative weights, via
    symmetric tensor powers of the spin-1/2 representation in quaternion components. This is the same object
    as (i), written polynomially.
- Plan: Wilson first (done at the abstract/crossing level), then the heat kernel via (ii).

## Risks / open

1. **Geometry (the bridge, OPEN).** Under the split formulation above, show the torus Wilson integrand is PE to
   `W₊·ΘW₊·Π T_K(Σ_c Y_c·shift Y_c)`. Until then RP for the actual torus measure is OPEN.
2. **Two cuts on the torus:** both cuts' crossing plaquettes enter. The split formulation handles both, with no
   gauge fixing.
3. **Transfer matrix** (next row of the gap scope) is still OPEN. RP gives a positive semi-definite form on
   Λ₊-polynomials; the GNS/transfer step then uses `CompactTransferGNS`.
4. RP is β-uniform. The gap chain still needs the strong-coupling clustering, so the GAP window (not RP) is
   strong coupling only.

## Bridge status (after items 1–4 part)

PROVED (all [propext, Quot.sound]): `split_sel_cut1/2`, `cross_word_cut1/2`, `refl_word`, `pe_of_coeff`,
`shQ_mul`, `rpk_qdot`, `rpk_cut1`, `wilson_rp_qfull`.

**OPEN: the assembly that discharges `hW`.** RP FOR THE ACTUAL TORUS MEASURE REMAINS OPEN. The exact remaining
obligations:
- (a) **Padding.** `∫_n p = ∫_{n+k} p` for p on the first n blocks, to add the k split variables. This follows
  from `haar_factor` with `q = polyOne`.
- (b) **Substitution homomorphism on the integrand.** The split, conj flip and reindex maps commute with
  `polyMul`/`polyAdd`/`wilsonPoly`/`plaqWord` up to `≅`.
  - The pieces exist (`translatedHeadPolynomial_mul/add/smul`, `selectedLeft/RightTranslatedPolynomial_mul`,
    `reindexQuaternionPolynomial_mul/character`, `signSelectedPolynomial_mul_prefix/character_prefix`), some
    under support guards.
  - Their action on `linkVar` (a coordinate quaternion ↦ the split product) is still to be proved.
- (c) **Geometry.** Partition `torusPlaquettes N` (even N_t) into positive, Θ-reflected and crossing plaquettes.
  Order `links` as Λ₊ ++ split variables ++ Θ-images. Show `plaqWord` of each class is the word used in
  `cross_word_cut1/2` / `refl_word`.
- (d) **Assembly.** With (a)–(c), the transformed integrand is PE to `W₊·ΘW₊·tkProd xs`, with `xs` the crossing
  scalars. This discharges `hW` in `wilson_rp_qfull`.

## Assembly progress (a)/(b)

- (a) PROVED: `SU2TorusRPPad.pad_haar` (∫_{n+k} p ≈ ∫_n p for p on the first n blocks).
- (b) PROVED in part:
  - `SU2TorusRPSubst`: `RingSub n S` (a ring homomorphism up to `PE n`); transport through `T_K`, Hamilton
    words, `plaqWord` shape (`TK_word_sub`) and plaquette products (`prodPoly_sub`).
  - `SU2TorusRPReindex`: block involutions are `RingSub`s with `σ: coordinateVariable b ↦ coordinateVariable (σ b)`.
  - `SU2TorusRPHeadSub`: the head shear `translatedHeadPolynomial T` is a `RingSub`; head coordinate ↦ T, tail fixed.
- (b) PROVED since: the conj flip is a `RingSub` with no support hypothesis (`SU2TorusRPConj.conj_ringSub`, via
  `parity_monoMul`), and `ringSub_comp` holds GIVEN `PECongr n S` (S respects `PE n`).
- (b) PROVED: `PECongr` for the conj flip (`SU2TorusRPConjCongr.conj_peCongr`, support-free, via odd moments vanish).
- (b) OPEN: `PECongr` for reindex / head shear. Haar-context equivalence is not obviously preserved by
  monomial-changing maps. Likely route: support-restricted `PE`, using the invariance lemmas (`quaternionHaar_reindex`,
  `quaternionHaar_signSelected`, `translatedHeadPolynomial_haar`) in shifted contexts.
- (b) earlier note, superseded:
  - The conj flip `signSelectedPolynomial` as a `RingSub`. Its product law exists only as
    `QuaternionPrefixPolynomialEqv` under block support. This needs either a support-restricted `RingSub` or an
    unconditional parity lemma for `selectedExponentParity (monoMul ..)`.
  - The selected (non-head) shear can be obtained as reindex ∘ head ∘ reindex from the instances above. Composing
    `RingSub`s (`RingSub` closed under composition) is routine and not yet written.
- (c), (d) OPEN. **RP FOR THE ACTUAL TORUS MEASURE REMAINS OPEN.**

**(b7) reindex `PECongrOn`** (`SU2TorusRPReindexCongr.lean`): `reindex_peCongrOn σ : PECongrOn n (reindexQuaternionPolynomial σ)`
(supported variant: `Sup n X → Sup n Y → PE n X Y → PE n (σX) (σY)`). Still open: head-shear `PECongrOn`, a supported
`ringSub_comp`, geometry (c), assembly (d). **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(b8) supported composition + chaining** (`SU2TorusRPCompOn.lean`): `RingSubOn`, `ringSubOn_comp` (outer map needs
`PECongrOn`, inner map must keep polynomials supported), `haar_step` (`∫S P ≈ ∫P` and `S P ≈PE P'` give `∫P ≈ ∫P'`).
Head-shear `PECongrOn` is NOT proved. The obstruction: in a context monomial that has head exponents, the shear
changes the head, so moving the context across needs the inverse shear `u ↦ a*·u` plus the sphere relation
`|a|² = 1` under Haar. Plan for (d): it does not need head-shear congruence, because it chains `haar_step`
once per substitution on concrete integrands. Geometry (c) and assembly (d) are NOT started.
**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(c) geometry** (`SU2TorusRPGeom.lean`, `N = 2M`, time = `x0`): Θ is `t ↦ 1−t mod N` (`rt`), and `reflLink`
reverses temporal links. The side labels pos/neg/cross are proved consistent: `refl_invol`, `side_refl` (Θ swaps
pos and neg and keeps cross), `cross_fixed`, `plaq_pos`/`plaq_neg` (each half plaquette's links lie in that half),
`plaq_cross` (a crossing plaquette has 2 crossing temporal links and 2 spatial links that are Θ-images of each
other). Not yet done: linking `reflLink` to the polynomial Θ (`reindex` + `conjSel`) on `linkVar`, and assembly (d).
**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(d1) Θ on link variables** (`SU2TorusRPThetaPoly.lean`): `linkInv links f`, the block involution induced by any
involution `f` under which `links` is closed. `reindex_linkVar`: reindexing sends `linkVar ℓ` to `linkVar (f ℓ)`
(QPE). `thetaInv` is the instance for Θ = `reflLink M`. A Classical leak via `beq_self_eq_true` on `Z4Link` was
avoided (`beq_iff_eq.mpr rfl`). Still open in (d): conjugating reversed temporal links (`conjSel` on `linkVar`),
the `haar_step` chain on the torus integrand, and factorising `Π TK` with `plaq_*`. **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**Correction (PECongr):** the unsupported `PECongr` for reindex is FALSE (Prover's `SU2ReindexPECongr.pecongr_fails`:
n=1, σ=id, monomial x₄). Only the supported forms are used from here on: `reindex_peCongrOn` (ours) /
`pe_reindex` (Prover's), `ringSubOn_comp`, and `haar_step`. Head-shear congruence is not needed.

**(d1b) conj half of Θ** (`SU2TorusRPThetaConj.lean`): `parity_var`, `sign_polyVar`, `conj_coord` (sign flip on
`conjSel T` conjugates exactly the `T` blocks), `theta_linkVar` (`sign ∘ reindex` sends `linkVar ℓ` to
`linkVar (Θℓ)`, conjugated on `T` blocks, QPE). The core `List.nodup_range` uses Classical, so a local
`nodup_range'` replaces it. Open: the `haar_step` chain on `Π TK` and the factorisation via `plaq_*`
(items 2–3 of (d)). **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(d2a) Θpoly on spatial `T_K`** (`SU2TorusRPThetaTK.lean`): `thetaPoly = sign(conjSel tSel) ∘ reindex(thetaInv)`,
`theta_ringSub` (RingSub), `theta_spatial_link`, `theta_TK_spatial`: `thetaPoly (TK (v,P)) ≈PE TK (rv v, P)` for
spatial `P`. Open: time-plaquettes (reflected word via `refl_word`, conjugated temporal links), the `haar_step`
chain over the full product, and the `plaq_*` factorisation. **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(d2b) Θpoly on time-plaquettes** (`SU2TorusRPThetaTime.lean`): `theta_time_word` (from `refl_word` + cyclicity of
`Re`), `rt_shift`/`rv_shift`, `theta_temporal_link` (temporal links are conjugated), `theta_TK_time`:
`thetaPoly (TK (v,P)) ≈PE TK (rv(v+e0), P)` for every time-plaquette. Together with `theta_TK_spatial`, Θpoly sends
every plaquette weight to its mirror's. Open: the `haar_step` product chain, the `plaq_*` factorisation and the
crossing split into `wilson_rp_qfull`. **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(d2c) product chain** (`SU2TorusRPThetaProd.lean`): `mir`, `theta_TK`, `theta_prod`
(`thetaPoly (Π TK) ≈PE Π TK∘mir`), `theta_haar` (∫Θpoly X ≈ ∫X for supported X), `torus_mirror`
(`∫ Π_{ps} TK ≈ ∫ Π_{ps.map mir} TK`). Item 2 of (d) is done. Open: item 3 (pos/neg/cross factorisation, crossing split,
`wilson_rp_qfull`). **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(d3a) shift bridge** (`SU2TorusRPShiftBridge.lean`): `reindex_shift`: if `σ k = k + a` for `k < a`, then
`reindex σ X ≈PE shiftPoly a X` on `Sup a X`. This links the geometric Θ to `rp_full`'s `shiftPoly`. Open for
item 3: ordering the torus links as `L ++ Θ(L)` (pos half, then its mirror) plus the split crossing variables,
the pos/neg/cross factorisation of `Π TK`, and the final `hW`. **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(d3b) item 3 step 1, link order** (`SU2TorusRPHalfOrder.lean`): for `links = L ++ L.map f`, `half_map`
(`linkInv` is `k ↦ k+|L|`) and `reindex_eq_shift` (the reindex half of Θpoly is `shiftPoly |L|` on L-supported
polynomials). Crossing links are Θ-fixed, so they do NOT fit this form; they must first be split into fresh
`A`/`B` blocks (A in L, B = Θ(A)). That split and steps 2–3 are open. **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(d3c) Θpoly = conj ∘ shift** (`SU2TorusRPThetaShift.lean`): `sign_invol` (the sign flip is an involution up to
PE) and `theta_shift` (`sign(sign(reindex σ X)) ≈PE shiftPoly a X` for half-shift σ and `Sup a X`). Undoing the
temporal conj, which is Haar-invariant (`conj_haar`), turns Θpoly into `rp_full`'s `shiftPoly`. Open: the crossing
split into fresh A/B blocks, the pos/neg/cross factorisation of `Π TK`, and `hW`. **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(d3d) item 3 step 2, factorisation** (`SU2TorusRPFactor.lean`): `prod_append`, `prod_perm`, `torus_factor`:
`ps ~ pos ++ pos.map mir ++ cross` gives `Π_ps TK ≈PE (Wp · thetaPoly Wp) · Wc`. Open: (i) the crossing split, so
the layout becomes `L₁ ++ Θ(L₁)`; (ii) a conj on the second half only, so that `thetaPoly Wp` becomes `shiftPoly Wp`
(`theta_shift`); (iii) RPK of the split crossing words (`rpk_cut1`/`cross_word_cut2`); (iv) assembly into
`wilson_rp_qfull`. **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

**(d3e) half-only conj** (`SU2TorusRPHalfConj.lean`): `parity_congr`, `sign_congr`, `sign_first_half` (a second-half
selection fixes first-half polynomials), `sign_second_half` (on second-half polynomials, the full and the restricted
selection flip identically). This settles open point (ii) at the lemma level. Still open: the crossing split, the RPK
crossing words, and assembly into `wilson_rp_qfull`. **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
