/-
Track B / R2 — Option B, step 2: the LOCATED, STRICT finite-volume gap on the
OS-reconstruction datum.

# What this adds over `OSContent`

`OSContent.FiniteVolumeReconstruction` now carries the strictness
`gapBound < 1` as a structural field (`gapBound_lt_one`), so its
`SpectralGapBound spec gapBound` (`∀ i, λᵢ ≤ gapBound`) is no longer vacuous
(the degenerate `gapBound = 1`, no decay, is excluded by construction).  The
datum's `.located` projection is the genuine `LocatedSpectralGap spec`:
`sep < 1` — the located second eigenvalue STRICTLY below the vacuum eigenvalue
`1` — so its decay `G(n) ≤ G(0)·sep ^ n` is genuinely geometric (a real mass
gap), and the computable `specMax spec ≤ sep` makes the gap LOCATED (one
decidable comparison), per the compact-operator constructive-spectral verdict.

This module exhibits that located strict gap end-to-end and a genuinely-gapped
datum (`sep = 1/2`), and packages the constructive finite-volume mass-gap
statement.

  * `locatedGap_of_reconstruction` — the located strict gap read off the datum's
    structural strictness field, with no side hypothesis.
  * `reconstruction_specMax_le` — the computable located top-of-spectrum is at
    or below the gap bound (the located content on the datum).
  * `gappedSpectralModel` / `gappedLocated` — a CONCRETE genuine strict gap at
    `sep = 1/2 < 1` (not the saturated free case `sep = 0`), exhibiting a real
    mass gap end-to-end.
  * `genuine_gap_summary` — packages "located + strict + geometric decay" as the
    constructive finite-volume mass-gap statement at the bounded transfer-operator
    level (no Stone, no unbounded spectral theorem).

Axiom-clean (`[propext]` / `[propext, Quot.sound]`), reusing the proven
finite-volume decay.
-/

import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.OSContent

namespace YMGap.Continuum.LocatedReconstruction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.OSContent
open YMGap.Continuum.ObservableMeasure

/-! ## Bridging the reconstruction datum to the located strict gap -/

/-- **From the OS reconstruction datum to the located strict gap.**  A
`FiniteVolumeReconstruction` carries the strictness `gapBound < 1` as its
structural field `gapBound_lt_one`, so the genuine `LocatedSpectralGap` is read
off the datum with NO side hypothesis — this is exactly the content the bare
`SpectralGapBound` lacked, now an invariant of every datum. -/
def locatedGap_of_reconstruction {A : ObsAlg}
    (rec : FiniteVolumeReconstruction A) :
    LocatedSpectralGap rec.spec :=
  rec.located

/-- **The located content on the datum.**  The computable top-of-spectrum
`specMax` is at or below the gap bound — equivalently (since `0 ≤ gapBound`) the
whole gap predicate collapses to this single decidable comparison. -/
theorem reconstruction_specMax_le {A : ObsAlg}
    (rec : FiniteVolumeReconstruction A) :
    specMax rec.spec ≤ rec.gapBound :=
  (specMax_le_iff rec.spec rec.gapBound rec.gapBound_nonneg).mpr
    (fun i _ => rec.hasGap i)

/-- **Strict geometric clustering.**  With the datum's strict located gap
(`sep < 1`, by construction), the connected two-point function decays
geometrically, `G(n) ≤ G(0)·sep ^ n`, the genuine finite-volume mass-gap
consequence. -/
theorem located_strict_decay {A : ObsAlg}
    (rec : FiniteVolumeReconstruction A) (n : Nat) :
    corr rec.spec n ≤ (corr rec.spec 0) * rec.gapBound ^ n :=
  (locatedGap_of_reconstruction rec).decay n

/-! ## A concrete genuine strict gap (`sep = 1/2`)

Not the saturated free case `sep = 0` of `OSContent.trivSpectralModel`: a
single excited mode at eigenvalue `1/2`, giving a real located gap below the
vacuum eigenvalue `1`. -/

/-- One excited mode at transfer eigenvalue `λ = 1/2` (mass `m = log 2 > 0`),
weight `1`.  (The vacuum eigenvalue `1` is already subtracted — `corr` is the
CONNECTED correlator, so every listed mode is excited, `< 1`.) -/
def gappedSpectralModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => Q'.mkPos 1 2 (by decide)
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => by decide

/-- A CONCRETE located strict gap at `sep = 1/2 < 1` — a genuine finite-volume
mass gap exhibited end-to-end. -/
def gappedLocated : LocatedSpectralGap gappedSpectralModel where
  sep := Q'.mkPos 1 2 (by decide)
  sep_lt_one := by decide
  bound := fun _ => Q'.le_refl' _

/-- The concrete gap decays geometrically at ratio `1/2`. -/
theorem gappedLocated_decay (n : Nat) :
    corr gappedSpectralModel n
      ≤ (corr gappedSpectralModel 0) * (Q'.mkPos 1 2 (by decide)) ^ n :=
  gappedLocated.decay n

/-! ## The genuine finite-volume mass-gap statement

Packages the three pieces the bounded transfer-operator gap needs — LOCATED
(computable `specMax ≤ sep`), STRICT (`sep < 1`), and DECAYING (`G(n) ≤
G(0)·sep^n`) — into one statement, with the located strict gap as the witness.
This is as far as R2's mass gap is constructively provable at finite volume
WITHOUT Stone / the unbounded spectral theorem (the continuum lift stays the
declared interface of `OSContent.ContinuumSpectralInterface`). -/
theorem genuine_gap_summary {S : SpectralModel} (g : LocatedSpectralGap S) :
    -- located: the computable top-of-spectrum is below the separator
    specMax S ≤ g.sep
    -- strict: the separator is below the vacuum eigenvalue 1
    ∧ g.sep < (1 : Q')
    -- decaying: geometric clustering of the connected correlator
    ∧ (∀ n, corr S n ≤ (corr S 0) * g.sep ^ n) :=
  ⟨g.located, g.sep_lt_one, fun n => g.decay n⟩

/-- The genuine mass-gap summary fires on the concrete `sep = 1/2` model. -/
theorem gappedLocated_genuine_gap :
    specMax gappedSpectralModel ≤ Q'.mkPos 1 2 (by decide)
    ∧ (Q'.mkPos 1 2 (by decide) : Q') < (1 : Q')
    ∧ (∀ n, corr gappedSpectralModel n
        ≤ (corr gappedSpectralModel 0) * (Q'.mkPos 1 2 (by decide)) ^ n) :=
  genuine_gap_summary gappedLocated

/-! ## A genuinely-gapped reconstruction datum (`sep = 1/2`)

The strictness is now a structural field, so a reconstruction datum can be
populated with a REAL mass gap by construction.  Reusing the trivial GNS space
(the `gns` field is independent of the transfer spectral model), the gapped
datum carries `sep = 1/2 < 1` — contrast `OSContent.trivReconstruction`'s
saturated `sep = 0`. -/

/-- A genuinely-gapped finite-volume reconstruction datum: the strict field is
populated with `gapBound = 1/2 < 1`, so its `.located` projection is a
non-degenerate located mass gap by construction. -/
def gappedReconstruction (n : Nat) :=
  { OSContent.trivReconstruction n with
    spec := gappedSpectralModel
    gapBound := Q'.mkPos 1 2 (by decide)
    gapBound_nonneg := by decide
    hasGap := fun _ => Q'.le_refl' _
    gapBound_lt_one := by decide }

/-- The gapped datum carries the genuine located mass gap by construction
(LOCATED ∧ STRICT ∧ DECAYING), with no side hypothesis. -/
theorem gappedReconstruction_genuine_gap (n : Nat) :
    specMax (gappedReconstruction n).spec
        ≤ (locatedGap_of_reconstruction (gappedReconstruction n)).sep
    ∧ (locatedGap_of_reconstruction (gappedReconstruction n)).sep < (1 : Q')
    ∧ (∀ m, corr (gappedReconstruction n).spec m
        ≤ (corr (gappedReconstruction n).spec 0)
          * (locatedGap_of_reconstruction (gappedReconstruction n)).sep ^ m) :=
  genuine_gap_summary (locatedGap_of_reconstruction (gappedReconstruction n))

/-- The gapped datum's connected correlator decays geometrically — the real
finite-volume mass gap, read off the datum. -/
theorem gappedReconstruction_decay (n m : Nat) :
    corr (gappedReconstruction n).spec m
      ≤ (corr (gappedReconstruction n).spec 0) * (gappedReconstruction n).gapBound ^ m :=
  located_strict_decay (gappedReconstruction n) m

/-- The gapped datum has a strictly positive eigenvalue-gap margin `0 < 1 − 1/2`. -/
theorem gappedReconstruction_gapMargin_pos (n : Nat) :
    (0 : Q') < (locatedGap_of_reconstruction (gappedReconstruction n)).gapMargin :=
  (locatedGap_of_reconstruction (gappedReconstruction n)).gapMargin_pos

end YMGap.Continuum.LocatedReconstruction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LocatedReconstruction.locatedGap_of_reconstruction
#print axioms YMGap.Continuum.LocatedReconstruction.reconstruction_specMax_le
#print axioms YMGap.Continuum.LocatedReconstruction.located_strict_decay
#print axioms YMGap.Continuum.LocatedReconstruction.gappedLocated
#print axioms YMGap.Continuum.LocatedReconstruction.genuine_gap_summary
#print axioms YMGap.Continuum.LocatedReconstruction.gappedLocated_genuine_gap
#print axioms YMGap.Continuum.LocatedReconstruction.gappedReconstruction_genuine_gap
#print axioms YMGap.Continuum.LocatedReconstruction.gappedReconstruction_decay
#print axioms YMGap.Continuum.LocatedReconstruction.gappedReconstruction_gapMargin_pos
