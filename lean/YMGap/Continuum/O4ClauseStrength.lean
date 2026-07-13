/-
Track B+RepTheory / R2 — **supplying a named, provably-non-trivial anisotropy
schedule to the weak legacy O4 slot.**

# The two weaknesses this module closes simultaneously

The weak legacy slot `RubricO4Restoration` (`ClayScorecard.lean`) is stated with an
existential inner `∃ defect : Nat → Q'`, so ANY geometric schedule fires it
(`O4RestorationH4.rubricO4Restoration_of_decay`).  On the carrier side,
`CarrierPrecursors.o4_restoration_on_charAlg` witnesses functional equivariance only
under the IDENTITY rotation (`functionalEquivariant_id`); the bar is proved real
(`heatKernel_not_equivariant_under_collapse`) but no genuine non-identity rotation is
supplied.

`StrongO4Restoration` bundles the defect's PROVENANCE: a genuine algebra with a
heat-kernel functional, a NON-TRIVIAL rotation `*`-hom `r` (moves some observable —
the exact content the identity witness lacks), a designated L=4 first-cubic-harmonic
generator `g`, an AF decay schedule whose step-0 coefficient IS the named anisotropy
`|E(r·g) − E(g)|`, and a genuine positivity witness that this anisotropy is nonzero.
`rubricO4Restoration_of_strong` fires the legacy slot from it, reusing the proved
decay-to-zero `O4RestorationH4.breakCoeff_vanishes` verbatim.

The concrete inhabitant `strongO4_charAlg` runs on genuine SU(2) heat-kernel data:
the spin-doubling `*`-endomorphism `doubleHom : χ_s ↦ χ_{2s}` (a provable
non-identity unital `*`-hom, upgrading off both `id` and the vacuum collapse) at the
L=4 generator `g = 4` (χ₄), with defect `|E χ₈ − E χ₄| = |9·(1/2)^80 − 5·(1/2)^24|`,
a closed strictly-positive `Q'`.

# Honest residuals (frontier UNCHANGED — do not overclaim)

  1. `doubleHom` is a non-identity `*`-ENDOMORPHISM, not an invertible H(4) rotation
     automorphism.  On the single-edge toy algebra (`carrier = Nat`, `mul = |a−b|`)
     the only `*`-automorphism is the identity; a genuine invertible 90° H(4)
     rotation lives on the real multi-edge lattice observable algebra where it
     permutes edges — that construction stays engineering-open.  `doubleHom` is the
     strongest honest non-trivial inhabitant of the rotation slot on this substrate.
  2. The geometric schedule `anisoDecay` is a MODEL running.  Pinning `breakCoeff D`
     to the physical rotation-breaking coupling's running (Davoudi–Savage O(a²)) is
     the open sign residual `O4RestorationProgress.CouplingRunning.betaDrop_nonneg`
     on the true 4D interacting coupling — untouched here.
  3. Hasenbusch–Vicari caveat (`O4RestorationH4`): geometric decay is legitimate only
     under the Gaussian-UV/AF hypothesis (spin-4 anisotropy can be relevant at a
     non-trivial IR fixed point).

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'`/`Nat` arithmetic and the reused proved AF-decay pipeline; the sole
non-`rfl`/non-`decide` obligation is `doubleHom.map_mul` (Nat: doubling distributes
over truncated `−` and is monotone on `max`/`min`).  All witnesses are `Type`-level
data.  Every load-bearing declaration is gated with `#print axioms`; permitted output
is `propext` / `Quot.sound` only.
-/

import YMGap.Continuum.O4RestorationH4
import YMGap.Continuum.CarrierPrecursors
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.O4ClauseStrength

open YMGap.Constructive
open YMGap.Continuum.ObservableMeasure (ProbFunctional ObsAlg ObsHom)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.CarrierPrecursors

/-! ## 0. The named anisotropy defect -/

/-- The rotation-breaking (anisotropy) defect of a functional `E` under a rotation
`*`-hom `r`, read off the designated L=4 first-cubic-harmonic generator `g`:
the functional gap `|E(r·g) − E(g)|`.  This is the norm of the leading
rotation-breaking operator restricted to `g`'s channel (Lead 1: L=4 is the minimal
non-trivial channel; Lead 2 / Davoudi–Savage: its coefficient runs O(a²)). -/
def anisoDefect {A : ObsAlg} (E : ProbFunctional A) (r : ObsHom A A)
    (g : A.carrier) : Q' :=
  Q'.abs (E.E (r.map g) - E.E g)

theorem anisoDefect_nonneg {A : ObsAlg} (E : ProbFunctional A) (r : ObsHom A A)
    (g : A.carrier) : (0 : Q') ≤ anisoDefect E r g := Q'.abs_nonneg _

/-! ## 1. The strengthened certificate -/

/-- **Strong O(4)-restoration certificate.**  Unlike the weak clause's anonymous
`∃ defect`, this bundles the defect's provenance:
  * a genuine algebra `A` with heat-kernel functional `E`;
  * a NON-TRIVIAL rotation `*`-hom `r` (moves some observable — the exact content
    `functionalEquivariant_id` lacks);
  * a designated L=4 first-cubic-harmonic defect generator `g`;
  * an AF decay schedule `D` (geometric contraction, degree-margin ≥ 2) whose
    step-0 coefficient IS the named anisotropy `anisoDefect E r g`;
  * a genuine positivity witness that this anisotropy is nonzero (the rotation
    really breaks `E` at the L=4 channel). -/
structure StrongO4Restoration : Type 1 where
  A            : ObsAlg
  E            : ProbFunctional A
  r            : ObsHom A A
  g            : A.carrier
  /-- Genuine non-triviality: `r` moves some observable. -/
  r_nontrivial : ∃ a : A.carrier, r.map a ≠ a
  /-- The AF-flowed anisotropy schedule. -/
  D            : O4RestorationAF.ScalingDimensionDecay
  /-- **Pinning**: the schedule's step-0 coefficient IS the named anisotropy of the
      non-trivial rotation at the L=4 generator. -/
  coeff0_eqv_aniso : (O4RestorationAF.breakCoeff D 0).eqv (anisoDefect E r g)
  /-- **Genuine content**: the anisotropy is strictly positive — `r` really breaks
      `E` at the L=4 channel, so the discharged defect is not a vacuous zero. -/
  aniso_pos    : (0 : Q') < anisoDefect E r g

/-! ## 2. `StrongO4Restoration ⟹` the weak slot (with content exposed) -/

/-- **Provenance-bearing legacy wiring.**  The weak slot fires from a strong
certificate; the discharged `defect` family is the anisotropy schedule
`breakCoeff D` of a genuinely non-trivial rotation, and `breakCoeff_vanishes`
proves it decays below every tolerance (limit = 0).  Full same-action O4
covariance is not a consequence of this target predicate. -/
theorem rubricO4Restoration_of_strong (S : StrongO4Restoration) :
    YMGap.Rubric.ClayScorecard.RubricO4Restoration :=
  O4RestorationH4.rubricO4Restoration_of_decay S.D

/-- **The genuine content the strong certificate carries** (what the anonymous
`∃ defect` cannot): the defect family used to fire the rubric starts at the
STRICTLY-POSITIVE functional gap `|E(r·g) − E(g)|` of a NON-TRIVIAL rotation `r`
on the L=4 generator, and decays to 0. -/
theorem strong_defect_is_positive_aniso (S : StrongO4Restoration) :
    (0 : Q') < O4RestorationAF.breakCoeff S.D 0
    ∧ (O4RestorationAF.breakCoeff S.D 0).eqv (anisoDefect S.E S.r S.g)
    ∧ (∃ a, S.r.map a ≠ a)
    ∧ (∀ ε : Q', 0 < ε → ∃ N, ∀ k, N ≤ k → O4RestorationAF.breakCoeff S.D k < ε) := by
  refine ⟨?_, S.coeff0_eqv_aniso, S.r_nontrivial, O4RestorationH4.breakCoeff_vanishes S.D⟩
  exact Q'.pos_of_lt_of_le S.aniso_pos (Q'.ge_of_eqv S.coeff0_eqv_aniso)

/-! ## 3. Inhabiting the `*`-hom scaffold as far as the toy substrate allows

A genuine NON-IDENTITY `*`-endomorphism of `charAlg` — the spin-doubling map
`χ_s ↦ χ_{2s}` (moves every non-vacuum generator, in particular L=4 → L=8). -/

/-- The doubling map `s ↦ 2·s` on the spin index (kept at `Nat` so instance
resolution does not have to unfold `charAlg.carrier`). -/
def dbl (s : Nat) : Nat := 2 * s

/-- **The one genuine Nat obligation**: doubling distributes over the truncated
Clebsch–Gordan product `|a−b| = max a b − min a b` and is monotone on `max`/`min`. -/
theorem dbl_mul (a b : Nat) :
    dbl (max a b - min a b) = max (dbl a) (dbl b) - min (dbl a) (dbl b) := by
  unfold dbl
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h, Nat.min_eq_left h,
        Nat.max_eq_right (Nat.mul_le_mul_left 2 h),
        Nat.min_eq_left (Nat.mul_le_mul_left 2 h)]
    omega
  · rw [Nat.max_eq_left h, Nat.min_eq_right h,
        Nat.max_eq_left (Nat.mul_le_mul_left 2 h),
        Nat.min_eq_right (Nat.mul_le_mul_left 2 h)]
    omega

/-- The spin-doubling `*`-endomorphism `χ_s ↦ χ_{2s}` on `charAlg`.  A genuine
non-identity unital `*`-hom (upgrading off `id` and off the vacuum-collapse). -/
def doubleHom : ObsHom charAlg charAlg where
  map      := dbl
  map_one  := rfl
  map_star := fun _ => rfl
  map_mul  := dbl_mul

/-- `doubleHom` is genuinely non-identity: it sends `χ_1 ↦ χ_2 ≠ χ_1`. -/
theorem doubleHom_nontrivial : ∃ s : Nat, doubleHom.map s ≠ s :=
  ⟨1, by show dbl 1 ≠ 1; decide⟩

/-! ## 4. The geometric anisotropy schedule -/

/-- A geometric anisotropy schedule with step-0 value `v` (degree margin 2). -/
def anisoDecay (v : Q') (hv : (0 : Q') ≤ v) : O4RestorationAF.ScalingDimensionDecay where
  coeff              := fun k => v * HalfPow.half ^ k
  coeff_nonneg       := fun k =>
    Q'.mul_nonneg _ _ hv (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg k)
  degreeMargin       := 2
  degreeMargin_ge_two := Nat.le_refl 2
  decay              := fun k => by
    -- v·half^(k+1) ≃ half·(v·half^k), so `≤` by `le_of_eqv`.
    show v * HalfPow.half ^ (k + 1) ≤ HalfPow.half * (v * HalfPow.half ^ k)
    have hstep : v * HalfPow.half ^ (k + 1)
        = v * (HalfPow.half * HalfPow.half ^ k) := rfl
    rw [hstep]
    -- v·(half·half^k) ≃ (v·half)·half^k ≃ (half·v)·half^k ≃ half·(v·half^k)
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv v HalfPow.half (HalfPow.half ^ k)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (HalfPow.half ^ k)
          (Q'.mul_comm_eqv v HalfPow.half))
        (Q'.mul_assoc_eqv HalfPow.half v (HalfPow.half ^ k))))

/-- `breakCoeff (anisoDecay v hv) 0 ≃ v` (`half^0 = 1`, `v·1 ≃ v`). -/
theorem anisoDecay_coeff0_eqv (v : Q') (hv : (0 : Q') ≤ v) :
    (O4RestorationAF.breakCoeff (anisoDecay v hv) 0).eqv v :=
  Q'.mul_one_eqv v

/-! ## 5. The concrete strong certificate on genuine SU(2) heat-kernel data -/

/-- The heat-kernel functional anchoring the concrete certificate (`w = 1/2`). -/
def heatE : ProbFunctional charAlg := charFunc heatWeight heatWeight_nonneg

/-- The designated L=4 first-cubic-harmonic generator (χ₄). -/
def genL4 : Nat := 4

/-- The concrete anisotropy value: `|E χ₈ − E χ₄| = |9·(1/2)^80 − 5·(1/2)^24|`,
a closed strictly-positive `Q'` (the `(1/2)^24` term dominates). -/
def charAniso : Q' := anisoDefect heatE doubleHom genL4

/-- `charAniso ≥ 0` by a single delta-unfold to `Q'.abs` (no deep evaluation). -/
theorem charAniso_nonneg : (0 : Q') ≤ charAniso :=
  anisoDefect_nonneg heatE doubleHom genL4

set_option maxRecDepth 20000 in
theorem charAniso_pos : (0 : Q') < charAniso := by decide

/-- **Concrete strong certificate on genuine SU(2) heat-kernel data.** -/
def strongO4_charAlg : StrongO4Restoration where
  A                := charAlg
  E                := heatE
  r                := doubleHom
  g                := genL4
  r_nontrivial     := doubleHom_nontrivial
  D                := anisoDecay charAniso charAniso_nonneg
  coeff0_eqv_aniso := anisoDecay_coeff0_eqv charAniso charAniso_nonneg
  aniso_pos        := charAniso_pos

/-- **Non-vacuity capstone**: the strengthened clause fires from a certificate whose
defect is a genuinely positive L=4 anisotropy of a non-trivial rotation. -/
theorem rubricO4Restoration_strong_charAlg :
    YMGap.Rubric.ClayScorecard.RubricO4Restoration :=
  rubricO4Restoration_of_strong strongO4_charAlg

/-- **The exposed content on the concrete certificate**: strictly-positive L=4
anisotropy of a non-identity rotation, decaying to 0. -/
theorem strong_charAlg_content :
    (0 : Q') < O4RestorationAF.breakCoeff strongO4_charAlg.D 0
    ∧ (O4RestorationAF.breakCoeff strongO4_charAlg.D 0).eqv charAniso
    ∧ (∃ s : Nat, doubleHom.map s ≠ s) :=
  ⟨(strong_defect_is_positive_aniso strongO4_charAlg).1,
   (strong_defect_is_positive_aniso strongO4_charAlg).2.1,
   doubleHom_nontrivial⟩

/-! ## Axiom-dependency gates -/

#print axioms anisoDefect_nonneg
#print axioms rubricO4Restoration_of_strong
#print axioms strong_defect_is_positive_aniso
#print axioms doubleHom
#print axioms doubleHom_nontrivial
#print axioms anisoDecay
#print axioms anisoDecay_coeff0_eqv
#print axioms charAniso_pos
#print axioms strongO4_charAlg
#print axioms rubricO4Restoration_strong_charAlg
#print axioms strong_charAlg_content

end YMGap.Continuum.O4ClauseStrength
