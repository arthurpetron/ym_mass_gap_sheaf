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

**(d3f) conclusion step** (`SU2TorusRPAssembly.lean`): `rp_conj_assembly`. Given a Haar-invariant RingSub `C`
that fixes `F` and `Wp`, sends their Θ-images to `shiftPoly`, and makes `C Wc` an RPK, we get
`0 ≤ ∫ (ΘF·F)·((Wp·ΘWp)·Wc)`. `theta_C_shift` and `C_fixes` verify the twist hypotheses for
`C = sign(above 4a T)` and the geometric Θ in the half-shift layout. This discharges `hW` for every integrand of the
`torus_factor` form, conditional on (1) the half-shift layout and (2) RPK of `C Wc`. Both are blocked on the
crossing split, which is still open. **RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**

## d3g — crossing-word RPK (SU2TorusRPCrossSplit.lean)
- `cross_split_word`: once the crossing links are split as `Uᵢ = (ΘBᵢ)*Bᵢ`, the crossing plaquette scalar is `≅ dot (shQ Y) Y` with `Y = B₁PB₂*`.
- `rpk_cross_split`: under `SupQ a Y`, the `T_K` of a split crossing plaquette is an RPK. Axioms: [propext, Quot.sound].
- Still open: carrying out the split on the concrete torus integrand (via haar_step) and the final instantiation of `hW`.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d3h — crossing product & Haar chain (SU2TorusRPCrossProd.lean)
- `crossWord`, `cross_witness`, `rpk_cross_prod`: tkProd over split crossing words with `SupQ` data is an RPK.
- `haar_chain`: iterated `haar_step` for a list of Haar-invariant substitutions. Axioms: [propext, Quot.sound].
- `rp_cross_assembly`: rp_conj_assembly with hWc replaced by `C Wc ≈PE tkProd(crossWords)` + CrossOK data.
- Open: concrete per-link split instances on the torus integrand; identification of `C Wc` with the crossWord product.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d4a–d4e — concrete crossing split, one link at a time
- d4a `haar_extend`: fresh Haar blocks (supported p: ∫_{b+e} p = ∫_b p).
- d4b `prefix_pe`, `steps_ringSub`: the existing all-degree selected-shear chain is a RingSub.
- d4c `step_coord_sel/other`: left/inverse shear maps U_s ↦ U_m*·U_s, fixes other coordinates (QPE).
- d4d `subst_prod`, `split_prod_haar`: any Haar-invariant RingSub acts plaquette-wise on the actual torus Π T_K.
- d4e `split_step`: ∫ Π_ps T_K = ∫ Π_ps T_K[U_s ↦ U_m* U_s] for one crossing link (unconditional in degree).
All axioms [propext, Quot.sound].
Open: iterating split_step over all crossing links (second step acts on the image product, needs an image-of-image
lemma or a simultaneous img), choosing multiplier blocks so that the result is in the L ++ Θ(L) layout, and the
identification C Wc ≈PE tkProd(crossWord) feeding rp_cross_assembly.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d4f–d4h — simultaneous split chain and second-cut crossing words
- d4f/d4g `chain_coord`, `split_chain`: one Haar-invariant chain of selected shears (per-step side, fixed orientation,
  distinct selected blocks, never-selected multipliers) splits ALL crossing links of the actual Π T_K at once:
  U_s ↦ M·U_s (left) or U_s·M (right).
- d4h `cross_word_M`, `rpk_cross_M`: at the cut t = M (right split U = B·(ΘB)*, positive spatial link in the last
  slot) the crossing T_K is an RPK, Y = B₂*P*B₁.
- Layout plan (no reindex needed): links = pos ++ cross ++ map reflLink pos, blocks = 2a with a = |pos|+|cross|;
  fresh multipliers for cross link j at index |pos|+j+a, added by haar_extend. Direct orientation, so that the
  conjugation twist C turns U_m into (ΘB)*.
Open: instantiate this layout for the concrete torus (Nodup/permutation to the integrand's link order), compute
C on the split crossing words (→ crossWord / cross_word_M forms), and discharge the rp_cross_assembly hypotheses.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d5a–d5c — coordinates, concrete twist, and RP for the split half-layout form
- d5a `shQ_cv` (shQ a U_b = U_{b+a}), SupQ lemmas, `rpk_cross0_cv`, `rpk_crossM_cv`.
- d5b `Ctw a T` (conjugate second-half T-selected blocks); `rpk_C_cross0/M`: Ctw of the split crossing T_K
  (direct orientation; left split at t=0, right at t=M) is an RPK.
- d5c `torus_rp_split`: with σ k = k+a on the first half and Θ X = sign(conjSel Tb)(reindex σ X),
  0 ≤ ∫(ΘF·F)·((Wp·ΘWp)·Π_cs G) whenever each Ctw(G c) is an RPK — every rp_conj_assembly hypothesis discharged.
Open: the geometric instantiation (layout pos ++ cross ++ Θpos, σ = thetaInv on it, the shear chain + haar_extend
taking the actual Π T_K to this form, matching each crossing plaquette's image to rpk_C_cross0/M, and the link-order
permutation to the integrand). hW is NOT yet discharged for the actual torus integrand.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d6a–d6c — PE lift, plaquette matching, end-to-end conditional reduction
- d6a `pe_lift`: PE n X Y with X, Y supported on n blocks ⇒ PE (n+e) X Y (moves thetaPoly/torus_factor facts to
  the carrier with fresh split partners).
- d6b `chImg_sel/unsel`, `imgTK_eq_TK`, `rpk_match0/M`: crossing plaquettes with index lists [s₁,p,s₂,p+a] /
  [s₁,p+a,s₂,p] have RPK Ctw-twists; unsplit plaquettes keep T_K.
- d6c `torus_rp_master`: 0 ≤ ∫_{a+a} (ΘF·F)·Π_ps T_K from: ChainOK chain, support/index bounds, chain fixes ΘF·F,
  the factorisation Π_ps T_K[split] ≈PE (Wp·ΘWp)·Π_cs G, and RPK of each Ctw(G c).
Open: instantiate these hypotheses from the torus geometry (concrete layout list, idxOf computations for the
crossing plaquettes, the factorisation via torus_factor + pe_lift + imgTK_eq_TK, chain fixing ΘF·F), and the
link-order / block-count bridge to the integrand. hW is NOT yet discharged for the actual torus integrand.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d7a–d7c — Θ on the split carrier and the hfac factorisation
- d7a `ThetaLike`, `thetaL_TK`, `thetaL_prod`: theta_TK/theta_prod for any Θ-like RingSub on any carrier.
- d7b `halfSwap a` (k ↔ k+a), `thetaH a Tb = sign(conjSel Tb)∘reindex(halfSwap a)` (the Θ of torus_rp_master,
  with hσ by `halfSwap_low`), `thetaH_like`: Θ-like on links with idx ℓ < a, idx Θℓ = idx ℓ + a, Tb(idx ℓ + a) = isT.
- d7c `split_factor`: supplies the hfac hypothesis of torus_rp_master from ps ~ pos ++ mir pos ++ cross.
Open: the concrete layout list and its idxOf facts (HD for pos links, plaqIdx for crossing plaquettes), the chain
construction with ChainOK, the chain fixing ΘF·F, and the bridge from the integrand's link order/block count.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d8a–d8c — layout index facts, block selector, concrete chain
- d8a `lay_pos`, `lay_cross` (+ classical-free `idxOf_lt`, `idxOf_left`, `idxOf_map`) on L = P ++ C ++ P.map Θ.
- d8b `layT` (temporal on links, true on fresh blocks), `lay_HD` (pos links are half-swap admissible), `layT_fresh`.
- d8c `layChain` (one direct shear per crossing link: idx c ↦ multiplier idx c + a, left at t=0, right otherwise),
  `layChain_ok : ChainOK .direct`.
Open: plaqIdx shapes of crossing plaquettes on L (via plaq_cross), the himg facts via chImg_sel/unsel, chain
fixing ΘF·F, choosing P, C from the actual torus links with Nodup/Perm, and the integrand bridge.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d9a–d9b — crossing and non-crossing plaquettes on the layout
- d9a `img_cross`, `img_pos`, `img_hi`, `rpk_lay0`, `rpk_layM`: with the concrete chain, crossing plaquettes whose
  index list is [idx c₁, idx ℓ, idx c₂, idx Θℓ] (cut 0) / [idx c₁, idx Θℓ, idx c₂, idx ℓ] (cut M) have RPK
  Ctw-twists under the layout selector layT.
- d9b `imgTK_noncross`: plaquettes whose link blocks are positive or upper-half keep T_K (the himg of split_factor).
Open: derive the index lists from plaq_cross for the actual torus plaquettes; choose P, C from the torus links
(Nodup, Θ-injectivity, ps ~ pos ++ mir pos ++ cross); the chain fixing ΘF·F; the integrand bridge.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d9c–d9g — geometric instantiation of the master
- d9c `cross_shape0/M`: plaqIdx of an actual in-box crossing plaquette has the rpk_lay0 / rpk_layM shape.
- d9d `rpk_cross_plaq`: every in-box crossing plaquette is RPK after the layout split (C ⊇ crossing links, P ⊇ pos links).
- d9e `refl_box`, `mir_side`, `plaqIdx_eq`.
- d9f `lay_factor`: hfac on the layout for `ps ~ pos ++ mir pos ++ cross`.
- d9g `torus_rp_layout`: torus_rp_master on the concrete layout/chain/selector/half swap; ChainOK, hfac, per-crossing
  RPK and hσ are discharged. Remaining hypotheses: hXfix (chain fixes X), hsup, hps, hWp; plus the choice of P, C
  and the bridge from the torus integrand to this layout.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d9h–d9n — analytic hypotheses of the layout master discharged
- d9h `sup_wilsonPoly`, `sup_TK`, `sup_prodTK`; d9i `mem_lay`, `hps_lay`, `hWp_lay`; d9j `hsup_lay`.
- d9k–d9l `mp_single`, `pe_single`, `poly_fix`: a RingSub that is literally additive, prefix-respecting, with supported
  outputs, fixing every occurring variable, fixes the polynomial.
- d9m `fix_list`, `lay_fix`: the concrete split chain fixes `X = Θ_H F · F` when `F` lives on the first `|P|` blocks.
- d9n `torus_rp_lay`: `0 ≤ ∫ (Θ_H F · F) · ∏_ps T_K` on the layout, from purely combinatorial/geometric data
  (L nodup, C nonempty nodup ⊇ crossing links, P ⊇ pos links in the box, ps ~ pos ++ mir pos ++ cross, ps in box).
Open: choose P, C, pos, cross from the actual torus (ps = all torus plaquettes); bridge from the torus
integrand/observable algebra (its link ordering and F's block placement) to this layout form; then hW.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d9o–d9p — fresh split blocks dropped
- d9o `haar_drop`: Haar blocks carrying no variables can be dropped.
- d9p `torus_rp_layL`: the layout RP statement on exactly `|L| = 2|P| + |C|` link blocks.
Open: P, C, pos, cross from the actual torus link/plaquette lists, and reindexing the torus integrand
(its link order, observables F on positive links) onto the layout; then hW.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d9q — concrete P, C from the torus links
- `Pt M`, `Ct M` (pos / crossing filters of `torusLinks (2M)`); `lay_nodup`, `Ct_nodup`, `Ct_ne`, `mem_Pt/Ct`.
- `torus_rp_PC`: layout RP with P = Pt, C = Ct; remaining hypotheses are only the plaquette decomposition
  `ps ~ pos ++ mir pos ++ cross` (pos in-box pos plaquettes, cross in-box crossing plaquettes, ps in the box).
Open: that plaquette decomposition for the torus plaquette list, and reindexing the torus integrand (torusLinks order,
observable F on positive links) onto the layout order; then hW.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.

## d9r–d9t — torus plaquette decomposition; layout RP for all torus plaquettes
- d9r `perm_ext'` (Classical-free). d9s `mir_invol`, `mir_side_neg`.
- d9t `plaq_perm`: `torusPlaquettes (2M) ~ posT ++ mir posT ++ crossT`; `torus_rp_all`:
  `0 ≤ ∫_{|L|} (Θ_H F · F) · ∏_{torusPlaquettes (2M)} T_K` on the layout `Pt ++ Ct ++ Θ Pt`, any `F` on the first
  `|Pt|` blocks, no remaining hypotheses besides `1 ≤ M`, `β ≥ 0`.
Open: identify the layout integral with the actual torus integrand (torusLinks order, observable algebra on positive
links) by a block reindexing, and state hW in the target's form.

## d9u: single-involution link relabelling (`SU2TorusRPRelabel`)

`relabel_prod`/`relabel_haar`: if a block involution `σ` satisfies `(plaqIdx L p).map σ.map = plaqIdx L' p` on every
plaquette, then `reindex σ (Π T_K[L]) ≡ Π T_K[L']` and `∫ Π T_K[L] = ∫ Π T_K[L']`. Axioms [propext, Quot.sound].
Open: chaining involutions for the general `torusLinks → layout` permutation, carrying the observables and Θ across,
and then `hW`.

## d9v: link-order permutation invariance (`SU2TorusRPSwap`)

`swapInv` is the adjacent block transposition, an involution, and `swap_idx` shows it relabels `idxOf`. Chaining
these along `List.Perm` gives `perm_haar`: for nodup `L₁ ~ L₂` containing every plaquette link,
`∫_{|L₁|} Π T_K[L₁] = ∫ Π T_K[L₂]`. Axioms [propext, Quot.sound]. This covers the bare product only; observables and
Θ are not carried across yet.

## d9w: the torus-order integral equals the layout one (`SU2TorusRPTorusZ`)

`lay_perm` gives `torusLinks (2M) ~ Pt ++ Ct ++ Θ Pt`, and `torus_Z` gives
`∫_{|torusLinks|} Π_{torusPlaquettes} T_K[torusLinks] = ∫_{|L|} Π T_K[L]`, where `L` is the layout. Axioms
[propext, Quot.sound]. Still open: transporting observables `F` and the reflection Θ, which `perm_haar` does not
yet carry, and then `hW`.

## d9x: relabelling with an observable (`SU2TorusRPRelabelX`)

`relabel_haarX` gives `∫ X·Π T_K[L] = ∫ (reindex σ X)·Π T_K[L']` for supported `X`, with one involution step. Open:
chaining it along the permutation with a composed reindexing and its coordinate action, matching the torus Θ
(`thetaPoly` on `torusLinks`) with the layout `halfSwap`/`conjSel` Θ, and then `hW`.
RP FOR THE ACTUAL TORUS MEASURE IS OPEN.
