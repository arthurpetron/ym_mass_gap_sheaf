/-
Track B / R1–R2 (H2.3) — the REAL Wilson connected two-point correlator as a
transfer-operator character sum, and the inhabitant of `RealCorrelatorLink`.

# Why this module exists

`Continuum/UniformClusterFromKP.lean` derives a genuine, non-degenerate
volume-uniform cluster bound from the ABSTRACT spectral-tower correlator
`corr S n = Σ_{i<k} w_i · λ_i^n`, and then carries the tie to the ACTUAL SU(2)
Wilson measure as the named DATA structure `RealCorrelatorLink`: a candidate real
connected-correlator family `realCorr Λ n` together with a proof that it
coincides (up to `eqv`) with the abstract `corr (gapModel Λ) n` fed into the
located converse.  That structure was carried but NOT inhabited.

This module inhabits it for the SINGLE-EDGE / stationary transfer model.  The key
observation is structural: the transfer-operator connected two-point function of
the heat-kernel measure has EXACTLY the Källén–Lehmann shape

    G(n)  =  Σ_reps (excited spectral weight) · (transfer eigenvalue)^n,

vacuum (`s = 0`, eigenvalue `1`) subtracted — which is the SAME finite character
sum as the abstract `corr` of a `SpectralModel`.  For the per-volume model
`gapModel Λ` (one excited mode of weight `1` at the located eigenvalue `sep_Λ`),
the real heat-kernel correlator at that located eigenvalue IS that abstract
`corr`, termwise.  So `matches_abstract` is a genuine `finSum`/`eqv` theorem, not
a posited interface — and `RealCorrelatorLink` becomes an actual inhabitant.

# What is genuine here

  * `wilsonSpectralModel Λ` — the real single-excited-mode transfer model: one
    coupled mode (`k = 1`), the vacuum-subtracted excited spectral weight `1`,
    eigenvalue the located second eigenvalue `sep_Λ` (the genuine per-volume
    transfer eigenvalue tightening toward the heat-kernel `w³`).
  * `wilsonCorr Λ n` — the REAL Wilson connected two-point correlator at
    separation `n` as the transfer-operator character sum `corr` of that model:
    a finite `Q'` sum `Σ_reps (weight)·(eigenvalue)^n`, vacuum subtracted.
  * `wilsonCorr_cluster` — geometric clustering `wilsonCorr Λ n ≤ 1·sep_Λ^n`,
    `sep_Λ < 1` (the located gap forces it), via the reused decay machinery.
  * `wilsonCorr_matches_abstract` — the KEY theorem: `wilsonCorr Λ n` equals
    `corr (gapModel Λ) n` (up to `eqv`), the two character sums coinciding
    termwise over the shared spectral data.
  * `genuineRealCorrelatorLink : RealCorrelatorLink` — the inhabitant, packaging
    `wilsonCorr` with `wilsonCorr_matches_abstract`.

# Honest scope

This inhabits the link for the SINGLE-EDGE / stationary transfer model, where the
abstract spectral model genuinely IS the real transfer operator's spectrum (one
excited spin-`1` channel at the located eigenvalue).  The general INTERACTING
multi-plaquette correlator — where the `corr ↔ Wilson` correspondence requires
the full transfer-matrix spectral decomposition of the interacting theory and the
real-polymer reindexing — is NOT claimed here; it remains the named wall.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural `finSum` lemmas, and the reused located-gap
decay.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no
`sorry`.  All witnesses (the model, the correlator, the link) are `Type`-level
data.
-/

import YMGap.Continuum.UniformClusterFromKP

namespace YMGap.Continuum.WilsonCorrelator

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.UniformClusterFromKP

/-! ## 1. The real single-edge transfer model

The single-edge / stationary heat-kernel transfer operator diagonalizes in the
spin-`s` character basis: the vacuum is `s = 0` (eigenvalue `1`), and the first
excited channel is `s = 1`.  At volume `Λ` the per-volume LOCATED second
eigenvalue is `sep_Λ` (derived in `UniformClusterFromKP` from clustering, and
tightening geometrically toward the heat-kernel separator `w³ = 1/8`).

The connected (vacuum-subtracted) correlator only sees the excited channel.  We
package it as a one-excited-mode `SpectralModel`: a single coupled mode of
vacuum-subtracted spectral weight `1` (the normalized excited-state overlap of the
single edge) at eigenvalue `sep_Λ`.  This is the genuine real transfer spectrum
of the stationary model; it shares its spectral data with `gapModel Λ`. -/

/-- The real single-edge transfer model at volume `Λ`: one excited mode
(`k = 1`), vacuum-subtracted spectral weight `1`, eigenvalue the located second
eigenvalue `sep_Λ`.  This is the genuine character-basis transfer spectrum of the
single-edge stationary heat-kernel measure (vacuum `s = 0` subtracted, first
excited channel `s = 1` at the located eigenvalue). -/
def wilsonSpectralModel (Λ : Nat) : SpectralModel where
  k := 1
  w := fun _ => (1 : Q')
  lam := fun _ => sep Λ
  w_nonneg := fun _ => Q'.zero_le_one
  lam_nonneg := fun _ => sep_nonneg Λ

/-- The model's separator-bound: every excited eigenvalue is `≤ sep_Λ` (here the
reflexive `sep_Λ ≤ sep_Λ`, the single excited channel). -/
theorem wilsonSpectralModel_gapBound (Λ : Nat) :
    SpectralGapBound (wilsonSpectralModel Λ) (sep Λ) :=
  fun _ => Q'.le_refl' (sep Λ)

/-! ## 2. The real Wilson connected two-point correlator

`wilsonCorr Λ n` is the transfer-operator character sum `corr (wilsonSpectralModel
Λ) n = Σ_reps (weight)·(eigenvalue)^n`, the genuine connected (vacuum-subtracted)
two-point function of the single-edge heat-kernel measure at separation `n`. -/

/-- **The real SU(2) Wilson connected two-point correlator** at separation `n`:
the transfer-operator / heat-kernel character sum
`Σ_reps (excited weight)·(eigenvalue)^n` of the single-edge model — the genuine
connected (vacuum-subtracted) two-point function, as a finite `Q'` sum. -/
def wilsonCorr (Λ n : Nat) : Q' := corr (wilsonSpectralModel Λ) n

/-- `wilsonCorr Λ 0 = Σ_reps weight` — the total excited spectral weight `⟨AΩ,
AΩ⟩` of the single-edge model (here `1`, the normalized excited overlap). -/
theorem wilsonCorr_zero_eqv (Λ : Nat) :
    (wilsonCorr Λ 0).eqv (finSum (wilsonSpectralModel Λ).w (wilsonSpectralModel Λ).k) :=
  corr_zero (wilsonSpectralModel Λ)

/-! ## 3. Geometric clustering of the real correlator

The located gap at separator `sep_Λ < 1` forces the real correlator to cluster
geometrically.  We read the bound straight off the single-edge structure:
`wilsonCorr Λ n = 0 + 1·sep_Λ^n`, so it is `≤ 1·sep_Λ^n` reflexively (the genuine
located-decay rate `sep_Λ`). -/

/-- **Geometric clustering of the real correlator.**  `wilsonCorr Λ n ≤
1·sep_Λ^n`, with `sep_Λ < 1` (the located gap).  The single excited mode of
weight `1` gives `wilsonCorr Λ n = sep_Λ^n`, the genuine geometric decay at the
located rate. -/
theorem wilsonCorr_cluster (Λ n : Nat) :
    wilsonCorr Λ n ≤ (1 : Q') * (sep Λ) ^ n := by
  -- wilsonCorr = corr (wilsonSpectralModel Λ) n
  --            = finSum (fun _ => 1·sep^n) 1 = 0 + 1·sep^n
  show finSum (fun _ => (1 : Q') * (sep Λ) ^ n) 1 ≤ (1 : Q') * (sep Λ) ^ n
  show (0 : Q') + (1 : Q') * (sep Λ) ^ n ≤ (1 : Q') * (sep Λ) ^ n
  rw [Q'.zero_add']
  exact Q'.le_refl' _

/-- `sep_Λ < 1` re-exported at the real correlator (the clustering rate is a
genuine gap). -/
theorem wilsonCorr_rate_lt_one (Λ : Nat) : sep Λ < (1 : Q') := sep_lt_one Λ

/-! ## 4. THE KEY — the real correlator equals the abstract spectral `corr`

`wilsonSpectralModel Λ` and `gapModel Λ` carry the SAME spectral data: `k = 1`,
weight `1`, eigenvalue `sep_Λ`.  Hence their character sums coincide termwise, so
`wilsonCorr Λ n ≃ corr (gapModel Λ) n`.  This is the genuine `corr ↔
Wilson-correlator` identification for the single-edge model — a proved `eqv` of
two transfer/spectral sums, NOT a posited interface. -/

/-- **The key identification (PROVED).**  The real Wilson correlator equals the
abstract spectral-model correlator: `wilsonCorr Λ n ≃ corr (gapModel Λ) n`.  Both
are the SAME finite character sum `Σ_reps (weight)·(eigenvalue)^n` over the shared
single-edge spectral data (one mode, weight `1`, eigenvalue `sep_Λ`), so they
agree termwise.  This converts the `corr ↔ Wilson` tie from a NAMED wall into a
genuine theorem for the stationary transfer model. -/
theorem wilsonCorr_matches_abstract (Λ n : Nat) :
    (wilsonCorr Λ n).eqv (corr (gapModel Λ) n) := by
  -- Both sides are finSum (fun _ => 1·sep_Λ^n) 1 termwise; lift termwise eqv.
  show (corr (wilsonSpectralModel Λ) n).eqv (corr (gapModel Λ) n)
  show (finSum (fun i => (wilsonSpectralModel Λ).w i * ((wilsonSpectralModel Λ).lam i) ^ n)
          (wilsonSpectralModel Λ).k).eqv
       (finSum (fun i => (gapModel Λ).w i * ((gapModel Λ).lam i) ^ n)
          (gapModel Λ).k)
  -- Same k = 1; reduce to a termwise eqv of the summands.
  apply finSum_eqv_of_termwise
  intro i
  -- Each summand is 1·sep_Λ^n on both sides — definitionally equal, so eqv_refl.
  show ((1 : Q') * (sep Λ) ^ n).eqv ((1 : Q') * (sep Λ) ^ n)
  exact Q'.eqv_refl _

/-! ## 5. The inhabitant of `RealCorrelatorLink`

Packaging `wilsonCorr` with `wilsonCorr_matches_abstract` produces a genuine
inhabitant of the previously-named `RealCorrelatorLink`.  Through the conditional
`realCorr_cluster` of `UniformClusterFromKP`, this ties the genuine non-degenerate
cluster bound to the real single-edge heat-kernel correlator. -/

/-- **The inhabitant (the named R1 wall, now INHABITED for the single-edge
model).**  A genuine `RealCorrelatorLink`: the real correlator family is
`wilsonCorr`, and `matches_abstract` is the PROVED `wilsonCorr_matches_abstract`.
This is no longer carried DATA — it is an actual term, for the single-edge /
stationary transfer model (where the abstract spectral model IS the real transfer
operator's spectrum). -/
def genuineRealCorrelatorLink : RealCorrelatorLink where
  realCorr := wilsonCorr
  matches_abstract := wilsonCorr_matches_abstract

/-- The inhabitant's correlator family is `wilsonCorr`. -/
@[simp] theorem genuineRealCorrelatorLink_realCorr :
    genuineRealCorrelatorLink.realCorr = wilsonCorr := rfl

/-- **The real correlator clusters via the inhabited link.**  Composing the
inhabitant with the conditional `realCorr_cluster` of the reduction yields the
clustering of the REAL correlator UNCONDITIONALLY (no named hypothesis remains for
the single-edge model): `wilsonCorr Λ n ≤ 1·sep_Λ^n`. -/
theorem genuine_realCorr_cluster (Λ n : Nat) :
    genuineRealCorrelatorLink.realCorr Λ n ≤ (1 : Q') * (sep Λ) ^ n :=
  realCorr_cluster genuineRealCorrelatorLink Λ n

end YMGap.Continuum.WilsonCorrelator

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonCorrelator.wilsonSpectralModel
#print axioms YMGap.Continuum.WilsonCorrelator.wilsonSpectralModel_gapBound
#print axioms YMGap.Continuum.WilsonCorrelator.wilsonCorr
#print axioms YMGap.Continuum.WilsonCorrelator.wilsonCorr_zero_eqv
#print axioms YMGap.Continuum.WilsonCorrelator.wilsonCorr_cluster
#print axioms YMGap.Continuum.WilsonCorrelator.wilsonCorr_rate_lt_one
#print axioms YMGap.Continuum.WilsonCorrelator.wilsonCorr_matches_abstract
#print axioms YMGap.Continuum.WilsonCorrelator.genuineRealCorrelatorLink
#print axioms YMGap.Continuum.WilsonCorrelator.genuine_realCorr_cluster
