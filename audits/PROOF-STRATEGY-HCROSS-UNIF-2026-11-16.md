# PROOF STRATEGY: width-uniform crossover `hcross_unif`, step 2 (w 0.35 → 0.56), 2026-11-16 (base 3fe65c9c)

**Label: strategy/literature note. NO Lean was built** (see §4). **NOT chart closure.** MC/TM numerics are evidence, not proof.
Fetched sources are in `/workspace/hcross_lit/` on the box: arXiv PDFs and `pdftotext` output.

## 0. Target and the repo's coupling map
- Target: `hcross_unif` (`lean/YMGap/RG/Robust3CrossUniform.lean:76`). For n < 6 it requires a W-independent `SchurBudget (f n) (c n) (1/64)`,
  plus the fine factor and coarse attainment at **every** width W. Step 2 is the crux. In TM language it needs a vac⊥ gap
  m_F(0.56) ≳ 1.035, uniformly in width (task2n).
- **Map (from the repo, not assumed).** The plaquette weight is f_w = Σ_s (s+1) w^{s(s+2)} χ_s, with **w = e^{−t/4}** (`BF4WilsonAllNomeAFPaddedTrajectory.lean:23`). This is the SU(2) **heat-kernel** action at time t. The U(1) analogue is Villain with β_V = 2/t.
  - Naive map β = 2/t: `BF4WilsonAllNomeAFPaddedTrajectory.lean:22-27` says the standard coupling is "g² = 2t = -8 log w" with "SU(2) β = 4/g²".
    The repo *label* is g² = t, which is non-standard. Numerics `/workspace/ym_tmgap_2026-11-15/README.md:208`: "the naive map β = 2/t is exactly the Prover's g² = 2t".
  - The κ₁-matched map is β_char with I₂(β)/I₁(β) = w³ (one-loop/character matching; heuristic).
  - Values (computed with scipy on the box):

  | w | t | g² = 2t | β_naive = 2/t | w³ | β_char |
  |---|---|---|---|---|---|
  | 0.35 | 4.199 | 8.40 | 0.476 | 0.0429 | 0.172 |
  | 0.56 | 2.319 | 4.64 | 0.862 | 0.1756 | 0.717 |

- **Caveat for all literature below:** the theorems are stated for the **Wilson** action exp(β Σ Re Tr U_p) unless noted. The repo uses
  the heat-kernel action, so any transfer needs either a new proof for the heat-kernel action or a comparison argument. The β maps above
  are heuristic, and the character map is the relevant one at strong coupling.

## 1. Mechanisms, theorem statements, hypotheses, reach

### 1.1 Osterwalder–Seiler 1978 (cluster expansion, strong coupling)
- Source fetched: abstract only (OpenAIRE, https://explore.openaire.eu/search/result?pid=10.1016%2F0003-4916%2878%2990039-8). Ann. Phys. 110, 440–471. The full text is paywalled and was **not** read.
  - Abstract quote: "we verify physical positivity … This implies the existence of a positive self-adjoint transfer matrix. We then prove existence and
    analyticity of the infinite volume limit of strongly coupled Yang-Mills theories on the lattice and we verify Wilson's confinement bound."
- Secondary (fetched): Chatterjee arXiv:2006.16229 §1: "Osterwalder and Seiler [30] proved that the area law is always satisfied at sufficiently large
  coupling strength". Cao–Nissim–Sheffield arXiv:2505.16585 §1: "the only prior result showing area law in dimension four in some regime of β is
  the classical result of Osterwalder-Seiler [OS78], which works in the strong coupling regime (where β is small)".
- **Radius: UNVERIFIED.** I did not read the explicit convergence condition and give no number. Coverage is any compact group, **including U(1)**,
  so the regime carries no non-abelian content. It is volume-uniform (cluster expansion).
- **Reach to w = 0.56: not established.** Quantitative fetched comparator: the Shen–Zhu–Zhu SU(N) strong-coupling threshold below (1.3) reaches only
  w_char ≈ 0.275.

### 1.2 Seiler, Lecture Notes in Physics 159 (1982)
- Fetched: Springer TOC only (https://link.springer.com/book/10.1007/3-540-11559-5). "Gauge Theories as a Problem of Constructive Quantum Field Theory
  and Statistical Mechanics", chapters "Lattice gauge theories" (pp. 3–98) and "Continuum gauge quantum field theories" (pp. 99–181).
- Contents **not read**. Theorems, radii and constants are **UNVERIFIED**; none are quoted.

### 1.3 Shen–Zhu–Zhu 2022 (stochastic analysis; strong coupling; mass gap). Included as the sharpest fetched quantitative strong-coupling gap.
- Fetched full text: arXiv:2204.12737 (https://arxiv.org/pdf/2204.12737), §1.1–1.2.
  - Weight "S(Q) = Nβ Re Σ_p Tr(Q_p)" (1.2). Assumption 1.1 is equivalent to "|β| < 1/(16(d−1))" for SU(N) (1.3).
  - Corollary 1.6 (Mass gap): under Assumption 1.1, "Cov(f, g) ⩽ c1 d(g)e^{−c_N d(Λf,Λg)} …" for cylinder functions with disjoint supports, in the unique infinite-volume measure.
- For SU(2), d = 4: β < 1/48 in their normalisation, i.e. Wilson β_W = 4β < 1/12 (my conversion: Nβ Re Tr = (β_W/N) Re Tr).
  On the character map this is **w ≲ 0.275 < 0.35**, so it does not reach even the coarse end of step 2. Volume-uniform. It is group-agnostic
  in mechanism (Bakry–Émery), so it gives no SU(2)-vs-U(1) separation.

### 1.4 Chatterjee 2020–21: center symmetry ⇒ confinement; strong mass gap + nontrivial center ⇒ area law
- Fetched full text: arXiv:2006.16229 v5 (https://arxiv.org/pdf/2006.16229), §2. CMP 385 (2021) 1007–1039.
  - Setting §2.1: G a closed connected subgroup of U(n), Wilson action H = −Σ Re Tr(ω_p), any d ≥ 2.
  - **Theorem 2.2:** "Suppose that the lattice gauge theory … has unbroken center symmetry in the sense of Definition 2.1. Let π be a finite-dimensional
    irreducible unitary representation of G that acts nontrivially on the center of G. … Then there is a function V : Z₊ → R, satisfying V(R) → ∞
    as R → ∞, such that for any rectangular loop ℓ with side-lengths R ≤ T, and for any Gibbs measure …, we have |⟨W_ℓ⟩| ≤ e^{−V(R)T}."
  - **Definition 2.3** (strong mass gap): "positive constants K1 and K2 depending only on G, β and d, such that for any cube B, for any boundary condition
    δ on B, and for any local functions f and g … |⟨fg⟩_{B,δ} − ⟨f⟩_{B,δ}⟨g⟩_{B,δ}| ≤ K1 e^{−K2 dist(f,g)}."
  - **Theorem 2.4:** "Suppose that it satisfies exponential decay of correlations under arbitrary boundary conditions, according to Definition 2.3.
    Then it has unbroken center symmetry. Moreover, if Wilson loop variables are defined using a … representation π that acts nontrivially on the center
    of G, then any Gibbs measure for the theory satisfies Wilson's area law (2.3) for rectangular loops."
- **Direction: gap ⇒ area law**, not the converse. No "area law ⇒ mass gap" statement appears in the paper. Its stated sufficient regime for
  Definition 2.3 is "when β is small enough, using the methods of Dobrushin and Shlosman" (no constant given). The "large β" case is the open Yang–Mills mass-gap conjecture.
- U(1) has center U(1) (nontrivial), but at weak coupling U(1) has no strong mass gap ("Guth [24] and Fröhlich and Spencer [18] showed that
  four-dimensional U(1) lattice gauge theory is not confining at weak coupling", §1), so the theorem is not applicable there.
- **Reach:** conditional on a strong mass gap. It gives no gap, so it is not a handle for hcross_unif.

### 1.5 Durhuus–Fröhlich 1980 (σ-model clustering ⇒ confinement)
- Fetched: Springer abstract (https://link.springer.com/article/10.1007/BF01222514), CMP 75 (1980) 103–151. Quote: "clustering of certain two-point functions
  of those σ-models implies confinement of static quarks in the corresponding Yang-Mills theory. Clustering is proven … for the SU(2) × SU(2) σ-models
  for a large range of couplings g² ≳ O(ν)."
- Theorem numbers and constants were **not read** (paywalled). Direction: clustering ⇒ confinement (again toward area law, not toward a gap).
  "g² ≳ O(ν)" is strong coupling. At ν = 4 the repo's g² = 2t is 8.4 at w = 0.35 and 4.6 at w = 0.56, which is comparable to O(ν) only up to an
  unspecified constant, so the **reach is UNVERIFIED**.

### 1.6 Mack–Petkova 1979/1980 (Z2 comparison; vortex free energy)
- Fetched abstracts (OpenAIRE):
  - Ann. Phys. 123 (1979) 442–467: "An inequality relating expectation values of the Wilson loop integral in the two theories is established. It shows that
    confinement of static quarks is true in our SU(2) model whenever it holds for the corresponding Z2-model."
  - Ann. Phys. 125 (1980) 117–134: "We derive a sufficient condition for confinement of static quarks by a vortex condensation mechanism … The confining
    potential V(L) is estimated in terms of the change of free energy … induced by a change in vorticity."
- Statements and constants were **not read** in full. Direction: Z2/vortex hypothesis ⇒ SU(2) confinement (area law). No gap statement. Reach: UNVERIFIED.

### 1.7 't Hooft 1978 (center/vortex phases) and Tomboulis 2007 (claimed proof)
- 't Hooft, NPB 138 (1978) 1–25, abstract fetched (OpenAIRE): the topological operators and gauge fields "form a closed algebra from which it is deduced that
  this system can be in one of the four different phases …". This is a physics classification, not a theorem with hypotheses.
- Tomboulis arXiv:0707.2179 (full text fetched, abstract quoted): "A derivation is given … that the SU(2) gauge theory is in a confining phase for all
  values of the coupling … Confining behavior for the vortex free energy order parameter … hence 'area law' for the Wilson loop, is the result for any initial
  coupling."
  - **Disputed:** Ito–Seiler arXiv:0711.4930 ("missing links") and arXiv:0803.3019 ("certain gaps and open problems"). Tomboulis replied in arXiv:0712.2620.
    Abstracts were read via search snippets of the arXiv pages, so treat this as **UNVERIFIED in detail**.
  - Not usable as a theorem. Even if correct, its output is a vortex free energy / area law, not a vacuum-sector gap.

### 1.8 assessment-1 (`/workspace/ym_release/assessment-1.pdf`, Nov 10, 2026; pdftotext read)
- §2: "The construction provides no evidence for or against a mass gap in the theory."
- §4 notes the UV RG "following the general approach of Balaban".
- §8 Open Questions: "3. Establish a uniform mass gap, giving exponential decay of corresponding correlations and a spectral gap in the
  Osterwalder–Schrader Hamiltonian. 4. Construct Wilson loop observables … Establish the area law for Wilson loops."
- So it offers no mechanism and lists exactly hcross-type content as open.

## 2. Is there a rigorous "area law (or center-vortex decay) with uniform constants ⇒ uniform TM gap"? **No (found none).**
- Every fetched rigorous link goes the other way:
  - gap ⇒ area law (Chatterjee Thm 2.4);
  - clustering ⇒ confinement (Durhuus–Fröhlich);
  - Z2 confinement / vortex condensation ⇒ SU(2) confinement (Mack–Petkova).
- A web search surfaced items claiming "area law ⇒ spectral gap" (philarchive manuscripts; a hexagonmath preprint). They are not refereed, and I do not rely on them.
- The repo itself encodes `mass gap ≠ area law` as independent premises: `WilsonAreaLaw.lean:239` `AreaLawAndMassGap`, `:252` `areaLaw_massGap_independence`;
  `OSConfinementAssessment.lean:52,178-191`.
- **Structural reason.** In the KS TM, an area law controls the **center-flux (torelon / 't Hooft electric-flux) sectors**: energy ≳ σ·L for flux winding length L.
  hcross_unif needs the rate on the **whole** vac⊥, including the flux-neutral glueball sector (0++). An area law says nothing direct there, and U(1) fails
  in the neutral sector too (photon). So a reduction "area law ⇒ hcross_unif" would be fake. **No Lean reduction was built.**

## 3. What a genuine attack would need (no claims, just the decomposition)
1. **Sector split** vac⊥ = ⊕ (center-flux sectors) ⊕ (neutral sector). In the flux sectors an area-law / vortex-free-energy hypothesis
   would give a W-uniform lower bound. U(1) fails this, which is good. This piece is reducible.
2. The neutral-sector gap at w ∈ [0.35, 0.56], uniformly in W, is the true residual. No fetched theorem covers it.
   - Strong-coupling methods: the fetched SZZ threshold reaches w_char ≈ 0.275 for the Wilson action. The OS radius is UNVERIFIED.
   - Possible routes, all UNVERIFIED and unproved: a computer-assisted cluster expansion / Dobrushin–Shlosman finite-box criterion at w ≤ 0.56 for the
     heat-kernel action; or an RG step that maps 0.56 into a verified strong-coupling regime (Tomboulis-type, disputed).
3. Numerics for orientation only: SU(2) size-stable ≤ 0.2 % / ≤ 1 % up to w = 0.56. U(1): −14 % (vac) and −41 % (flux) at w = 0.56 (task2n).
   The flux-spreading signal is exactly the sector-1 discriminator.

## 4. Lean decision
- No reduction with verified hypotheses exists, so per instructions no Lean file was written.
- A sector-split interface (item 3.1) would be honest, but its residual neutral-sector hypothesis is not U(1)-failing *because of* center
  symmetry. It is deferred, pending approval.
- **Clarification (2026-11-16, 3:10 PM PT, after YM Bot's check):** the U(1) photon has zero electric flux, so it lives in the
  **neutral** sector. A width-uniform neutral-sector gap at w in [0.35, 0.56] therefore **fails for U(1)**. That residual
  hypothesis is where the essential non-abelian content sits: it is the open core. "Not U(1)-failing *because of* center symmetry" above
  means only that center symmetry / area-law arguments do not control that sector, so they cannot discharge it. It does not mean U(1)
  satisfies it. The flux-sector hypothesis also fails for U(1) in the Coulomb phase (no area law), but on its own it is not enough.
  One sentence in the 3:06 PM report to YM Bot ("would NOT fail for U(1)") was misworded and is superseded by this clarification.
  The sector split stays on hold until Numerics task2o reports which quantity separates SU(2) from U(1) uniformly in L.

## 5. Repo interfaces found (rg over lean/ and audits/)
- `lean/YMGap/Continuum/WilsonAreaLaw.lean`: `ScaleCovariantWilsonAreaLaw` :113, `rectangularWilsonAreaLaw_of_general` :164, `StrongCouplingPlaquetteActivity` :204,
  `strongCoupling_areaLaw` :220 (w ≤ 1/2 activity bound, continuum-scale interface), `AreaLawAndMassGap` :239, `areaLaw_massGap_independence` :252.
- `lean/YMGap/Continuum/OSConfinementAssessment.lean`: area-law route assessment; "mass gap ≠ area law" at :52, :178–191.
- `lean/YMGap/Continuum/UniformCorrelationDecay.lean`: :25, :298, :400. This is correlation decay (OS4), explicitly not an area law.
- Heat-kernel strong-coupling link decay: `SU2LinkDecayHeat.lean` (wH = 1/100000 at :75) and `SU2WilsonLinkDecay.lean:61`.
- Width-independent strong-coupling contraction actually used by Robust3: `uniformRate_of_guards` (`RG/StrongCouplingNomeThreshold.lean:68`), with guards
  for w ≤ 1/55 (:141, :156), used by `r3_seed` (`Robust3UndershootCrossoverInstance.lean:81`).
- `BF4SU2FixedMagneticMehlerCarrier.lean:6` mentions center vortices only in a docstring.
- **No center-symmetry, Z2-vortex, 't Hooft-flux or Polyakov-loop interface exists** (rg found none in lean/).
- Audits mentioning area law / vortex: `SCOPE-SU2-TORUS-WILSON-GIBBS-2026-10-06.md`, `RESEARCH-TARGETED-YM-FRONTIER-2026-09-30.md`, `RESEARCH-MATH-PH-2026-09-27.md`,
  `RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`.

Caveats: literature reach is compared through heuristic β maps for a different action. Nothing here is proof. Not chart closure.
