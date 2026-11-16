# STATUS addendum: r49/Robust3 chain after task2n and task2j (2026-11-16, base b669114f)

Additive to `audits/STATUS-R49-ROBUST3-CHAIN-2026-11-16.md` (c0b22e34, corrected bb181cbf). That file is unchanged; where the
rows below differ from it, **this addendum supersedes it**. **NOT chart closure.** Numerics are evidence, not proof.
Build caveat: direct lean against copied oleans, not lake-verified. Sources: `/workspace/ym_tmgap_2026-11-15/results/task2n_*.md`,
README §20 and §16, and `results/task2h_proof_note.md` (task2j version; the prior copy is `.pre2j.md`).

## 1. hafδ_OPEN (SpacingHeatKernel:80) under the KS carrier: exact characterization
- **Replaces** "δ_min = 0 is only a necessary condition". task2n_hafdelta.md §1: "the least δ ∈ [0,1] for which some pair
  (Φ, D) satisfies hupper and hschur is exactly δ*_n = max(0, 1 − (1 − ρ_F⁴)/(1 − ρ_C²))", attained by Φ(y) := ‖y‖·v_C.
  Hence "hafδ at step n is *equivalent* to an upper bound ℓ_n ≤ ℓ_max(n; m_C), with ℓ_max > 1".
- **What kind of result it is:**
  - The characterization is **analytic**: a short handwritten argument, not machine-checked. It is conditional on (a) the
    meta-identification of the repo carrier step with one KS TM step (`T = M^{1/2}EM^{1/2}`), (b) the spectral facts "(i) the fine contraction
    ‖T_F²y‖ ≤ ρ_F²‖y‖ on vac⊥; (ii) a coarse vector achieving ρ_C; (iii) the gap ratio m_F ≥ m_C/2", and (c) Φ being an
    arbitrary (nonlinear) function, as in the Lean. For a linear/natural Φ, δ can be larger (§4 of the file, proxy).
  - The **numbers** are numerical: central δ* = 0 at HK j6 (ℓ = 0.678 ± 0.018, 19.7σ below ℓ_max = 1.031), HK j7
    (0.662 ± 0.017, 20.8σ below 1.011), all 15 models j6–10, and the arb-certified model tail 10 ≤ j ≤ 10⁷. Overshoot room
    ℓ_max − 1 = 0.031 / 0.011 / 0.006 / 0.0045 / 0.003 at j6–10. j8 is UNRELIABLE (w9 not equilibrated); j9–10 and the tail are models.
    Outliers: small-R π/12 fits give ℓ7 up to 0.994(13), which fails at +2σ.
- **Lean now (b669114f):** `Robust3SchurRankOne.lean` proves the sufficiency core abstractly. `schur_of_spectral` (:138)
  derives the repo `SchurDecomposition` from fine factor f, coarse attainment c and `SchurBudget f c δ` (:53).
  `robust3_physical_floor_lmax_HK` (:233) discharges δ, hd0, hd1, hcross, hafδ, D and hschur, leaving `hbudget_OPEN` (= ℓ_n ≤ ℓ_max(n),
  rational form), `hfine_OPEN`, `hcoarse_OPEN` and `hupper_OPEN`. The rank-one Φ itself cannot be built: there is no real scalar action
  on `VacuumComplement`. The ε cost is `budget_eps` (:57), (1−δ)ε.
- U(1): "U(1) has no AF regime" (old row) stands for n ≥ 6.

## 2. hcross_OPEN (SpacingHeatKernel:79): satisfied by U(1) unless volume-uniform
- task2n_hcross / summary: "on every accessible volume (plaquette, cube, double cube, ≤ 12 sites …), **U(1) passes hcross at all six
  steps** with δ_min ≤ 1.2e-4 (worst case 1.1e-3, double cube step 2). So **as a finite-volume TM statement hcross carries no
  non-abelian content.**"
- **Flag:** hcross as stated (δ datum ≤ 1/64 plus hschur at the chosen `width`) is satisfiable by U(1) at fixed small width
  (numerical, ≤ 12 sites). It encodes non-abelian content only if it is **volume-uniform** (`hcross_unif`, see
  `audits/SCOPE-HCROSS-UNIF-2026-11-16.md`).
- Width-uniformly, U(1) step 2 (0.35 → 0.56) "crosses w_c ≈ 0.463 … δ_min → 1 and it **FAILS**", needing m_F(0.56) ≥ 1.035,
  "which a free-photon estimate violates from periodic L ≈ 6 (an estimate, not run)". It uses the literature β_V,c ≈ 0.65.
  Steps 0–1 pass, and steps 3–5 give δ_min → 0 (both Coulomb, marginal-spectrum caveat).
- Size-stability is the visible discriminator. U(1) changes −14 % / −8.5 % (vac) and −41 % (flux) at w = 0.56; SU(2) changes ≤ 0.2 % / ≤ 1 %.
- hupper/hschur proxy (task2n_proxy): rank1 = δ_min, proj δ ≤ 2e-8 (SU(2)) and ≤ 1e-4 (U(1)), level δ ≤ 1e-8. So "no group discrimination
  here either. The w-dependent completedInner is not modelled", and hupper for the real carrier is untested.
- Old row "U(1): unknown for δ" is superseded: **U(1) passes (finite volume, numerical); fails only volume-uniformly at step 2 (estimate).**

## 3. task2j / Lemma G status
- Proof note §4 is now explicit lemmas (D0, A, B/B′, C, D, E, F, G, H, I, J; map lemmas R5/N4/M4), with R = 11/10 (naive) and 44 (matched),
  RC = 1/1000, RS = 1/5000.
- **Lemma G** (§(4g)): "|Δg/ln2 − T3| ≤ K3/m³ with K3 = 27/10" under m ≥ 10⁶, q ≤ 8325/100000, "(H1) β̄ ≥ m/4; (H2) 0 < Δβ ≤ 26/100" and
  (H3) the Lemma A/B ceilings (e1 = 1053/100, e2 = 567/1000, |a1| = 7/24). (H1)–(H3) follow from Lemmas A, B and Corollary B′.
  - Slack: β̄/m ≥ 0.2575118 against 1/4, and Δβ ≤ 0.2575121 against 0.26.
  - arb worst ratio 0.893; G1 = 1.8452; K3 arb 2.66207.
  - Certificates: §5 tolerates K3 ≤ R3 = 41, so `task2h_lead_1000000_v2.json` stays valid; task2j_lead gives 16/16.
- Status: [P] handwritten with constants in arb. **Not in Lean.** Lean has Lemma F (i)–(iii) on partial sums
  (`Robust3LemmaF.lean`, `Robust3LemmaFiii.lean`). F(iv), G, the log2 ↔ L_n link and SERIES_LIMITS_OPEN remain blocked on an ln/series
  interface. Cited inputs remain L1/L1′ (Bessel ratio). The arb range is j ≤ 10⁷. Scope is the 10 analytic models.

## 4. Unchanged rows
hupper_OPEN (now also the only carrier hypothesis besides hfine/hcoarse in the `lmax` form), `_hpos`, `_hwin_MC`, `_hoff_OPEN`,
SERIES_LIMITS_OPEN, and the TM meta-identification: as in the base STATUS. The U(1) expectations for positivity and spacing
(fails from j ≥ 3 and j ≥ 2, numerical) still hold. No joint witness exists for the carrier hypotheses, so the final theorem
is not shown non-vacuous as a whole.
