# FRONTIER: open hypotheses of `robust3_floor_width_uniform` (2026-11-16, base 66028514)

Theorem: `lean/YMGap/RG/Robust3CrossUniform.lean:134`. At every width W it gives (a) the carrier contraction at the W-independent
rate `relativeRate timeRate capDelta n` and (b) floor·aHK(w_n) ≤ (P₃·aHK(w_0))·latticeMargin_n.
**NOT chart closure.** Numerics are evidence, not proof. Build: direct lean against copied oleans, not lake-verified.

**assessment-1.** It is not in `/workspace/ym_v3seed_wt/{audits,docs,work_plan.md}` or in `/workspace/ym_tmgap_2026-11-15`. It was found at
`/workspace/ym_release/assessment-1.pdf`, with a byte-identical copy at `/workspace/openai_ym_audit/YM/docs/assessment-1.pdf`.
The file is "Validation of the OpenAI Yang–Mills construction", Yang–Mills group, Nov 10, 2026, 35 pp. Quoted from it:
- "It does not prove that the infinite-volume limit is unique or that there is a mass gap."
- "The construction provides no evidence for or against a mass gap in the theory."
- On the UV RG: "following the general approach of Balaban but with many improvements"; the infinite-volume limit is obtained
  "only … subsequentially". The bounds (11) hold "in fixed boxes uniformly in the volume" (local boundedness/equicontinuity, not decay).
- Open Questions include "3. Establish a uniform mass gap …" and "4. … Establish the area law for Wilson loops."

So assessment-1 covers **none** of the hypotheses below. It documents that a uniform gap remains open, and it is the closest
source for W-uniform UV control (fixed physical volume, not lattice-width-uniform spectral bounds).

Literature legend: OS = Osterwalder–Seiler, "Gauge field theories on a lattice", Ann. Phys. 110 (1978).
Balaban = T. Bałaban's 1980s CMP series on UV stability / RG for lattice gauge theories in finite volume.
Chatterjee = S. Chatterjee, e.g. "Yang–Mills for probabilists" (arXiv:1803.01950, survey) and the large-N strongly coupled SO(N)
lattice gauge theory paper (CMP, about 2019). I state only coarse scope; I cite no theorem numbers.

| hypothesis (binder) | what would discharge it | literature coverage |
|---|---|---|
| `hupper_unif` (:67): ‖Φ_{W,n}y‖_C ≤ ‖y‖_F at every W | Construct a width-indexed block-spin/RG map between consecutive carriers that is a contraction for the w-dependent `completedInner`, uniformly in W. The rank-one Φ = ‖y‖v_C satisfies it with equality but needs a real scalar action on `VacuumComplement` (absent). | OS: reflection positivity/transfer matrix, which is the structural setting; it gives no RG map between nomes. Balaban: RG blocking maps with effective-action bounds in finite volume; whether they give this norm comparison on this carrier is **uncertain** (not checked). assessment-1: no. |
| `hcross_unif` (:76), steps n < 6 (w: 1/64 → 0.779): fine factor f_n, coarse attainment c_n at every W, and the budget f ≤ 1/64 + (63/64)c | A width-uniform spectral gap on vac⊥ at each crossover nome, i.e. m_F ≥ m_C/2 up to the ℓ_max allowance, uniformly in W, plus a coarse vector attaining ρ_C. Step 2 (0.35 → 0.56) is the crux. | OS: at sufficiently strong coupling (small β) the cluster expansion gives a volume-uniform gap/exponential clustering for any compact group, **including U(1)**. That covers only the small-w steps, and the crossover reaches w ≈ 0.78 (which steps fall in the convergent regime is **uncertain**). Chatterjee: strong-coupling/large-N area-law results are also confined to a strong-coupling regime and are not uniform-gap statements at these w (**uncertain** fit). Balaban: UV/weak coupling, not the crossover. assessment-1: no ("uniform mass gap" listed as open). **U(1) is expected to FAIL here (step 2, Villain transition; task2n estimate, not run). This is the non-abelian content.** |
| `hafδ_unif` (:81), steps n ≥ 6: the same at every W, with budget at afGap²/10 | Width-uniform gap ratios along the AF schedule, with ℓ_n ≤ ℓ_max(n) (overshoot ≤ 0.031 … 0.003 at j6–10, → 0 like afGap²). This is a quantitative weak-coupling mass-gap statement. | None known to me. Balaban controls UV stability in finite volume, not a gap. assessment-1: UV convergence at fixed volume and no gap. Evidence is numerical only (HK MC j6–7; models j6–10; arb model tail j ≤ 10⁷; task2n). U(1): no AF regime. |
| `hpos` (`Robust3SpacingHeatKernel.lean:47`): aHK(w_j) > 0 | A positive string tension (area law) at every Robust3 nome for the heat-kernel action. | OS: area law at strong coupling only (any group, so not non-abelian evidence there). Chatterjee: area-law/confinement results in strong-coupling or large-N regimes (**uncertain** scope for SU(2) at these w). assessment-1: area law listed as open. U(1): expected to fail from j ≥ 3 (Coulomb, numerical). |
| `hwin_MC` (:39/50): spacing 2a_{j+1} ≤ ρ_j a_j for j6–7 | A rigorous bound on a√σ ratios at w6–w8. | None. Evidence is HK MC (task2k/2m), which is not proof. |
| `hoff_OPEN` (:43): spacing for j < 6 and j ≥ 8 | Strong coupling (j < 6): string-tension ratio bounds. AF tail: two-loop-scaling bounds on a(w). j8 is pending (w9 unequilibrated). | Strong-coupling expansions (OS-type) could plausibly give j < 6 bounds at small w (**uncertain**, not checked). Tail: coupling-map models only (arb or analytic, which are map-based, not heat-kernel a(w)). U(1): expected to fail for j ≥ 2. |
| `SERIES_LIMITS_OPEN` (ln2 = lim L_n, π²/18 = lim S_n) | Not a binder of this theorem. It is used only to link the Lemma F partial sums (`Robust3LemmaF*.lean`) to the proof note's constants. A Lean series/limit interface would discharge it. | Classical mathematics (standard series), not formalised here. Group-independent. |
| Meta, not a binder: carrier step = one KS TM step; aHK = the heat-kernel a√σ | Identification theorems linking the repo carrier/nomes to the TM and to the physical string tension | None. These are modelling assumptions behind all numerics (README §1, §6). |

**Summary.**
- The only places where U(1) is expected to fail are `hcross_unif` (step 2) and the string-tension binders (`hpos`, spacing).
  Finite-volume hcross is passed by U(1) and does not imply `hcross_unif`.
- The literature I am confident about covers strong coupling only (OS; Chatterjee's strong-coupling/large-N results). That regime is
  abelian-valid, so it supplies no non-abelian content.
- Balaban and assessment-1 address UV/fixed-volume control, not a uniform gap.
- No source covers the crossover step 2 width-uniformly, the AF-step gap ratios, or the window spacing.
