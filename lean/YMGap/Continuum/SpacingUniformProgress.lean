/-
Route 2 sharpening — **shrinking the uniform-curvature wall from full curvature
to curvature ON THE SPECTRAL MODES**.

# What this module sharpens

`UniformCurvatureBound` (the geometric a→0 continuum reduction) carries the named
open input `uniform_CD : ∀ k, (gen k).CD K`, i.e. the FULL Bakry–Émery
curvature-dimension inequality

      ∀ k, ∀ f : state → Q',   K · E[Γ₁(f)]  ≤  E[Γ₂(f)]                    (CD K)

holding at every lattice spacing `k` and for EVERY test function `f`.  This is a
quantifier over the entire (infinite) function space at each spacing — far more
than the downstream gap argument ever consumes.

Reading the proof of the curvature template `eigenvalue_ge_of_CD` shows it only
ever instantiates the curvature hypothesis `CD K` at the SPECIFIC eigenfunctions
whose energies it bounds.  The full `∀ f` quantifier is therefore overkill: the
entire chain to a strictly-positive continuum mass goes through with the
curvature inequality assumed ONLY at the actual spectral modes `eigf k i`.

This module makes that observation a genuine, green reduction:

  * `eigenvalue_ge_of_curv_at` — **the sharpened template**: the SAME
    `K ≤ λ` conclusion as `eigenvalue_ge_of_CD`, but from a SINGLE-FUNCTION
    curvature instance `K · E[Γ₁(f)] ≤ E[Γ₂(f)]` (not the full `CD K`).  This is
    a strict hypothesis weakening of the existing template.
  * `ModeCurvatureBound` — **the sharper named residual**: identical to
    `UniformCurvatureBound` except the `uniform_CD : ∀ k, CD K` field is replaced
    by `curv_on_modes : ∀ k i, K·E[Γ₁(eigf k i)] ≤ E[Γ₂(eigf k i)]`, the
    curvature inequality assumed ONLY at the spectral modes.
  * `ofUniform` — the forward arrow `UniformCurvatureBound → ModeCurvatureBound`,
    PROVED by instantiating `uniform_CD` at the eigenfunctions.  This witnesses
    that the new residual is genuinely IMPLIED by (hence no stronger than) the
    original wall.
  * `mode_curvature_continuum_mass_isPositive` — **the payoff**: a
    `ModeCurvatureBound` already yields a strictly-positive continuum mass, via
    the same located-gap ⇒ uniform-cluster-bound ⇒ positivity pipeline.

# Honest assessment of the distance shrunk

The reduction replaces an `∀ f` curvature obligation by an
`∀ (spectral mode)` curvature obligation at each spacing.  That is a genuine
weakening (the converse — reconstructing full `CD K` from the mode inequalities —
is NOT provided and is not expected to be cheap, as it would require spectral
completeness plus the off-mode curvature content).  It does NOT close the
continuum limit: the spacing-uniform curvature ON THE MODES is still the open
analytic input (Bakry–Émery in mechanism, Bałaban-class in difficulty).  What it
buys is a strictly smaller target — one only needs the Bochner inequality on the
finitely-many excited eigenmodes that carry the gap, not on every observable.

# Axiom-gate (AGENTS.md Rules 1, 6, 8)

Pure `Q'` arithmetic over the proved Bakry–Émery identities and the proved
cluster route; no new `axiom`, no `sorry`/`admit`, no `Classical.*`/
`native_decide`, no `Prop := True` stub.  The `curv_on_modes` field is the named
open input, carried as `Type`-level data (Rule 8).  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.
-/

import YMGap.Continuum.UniformCurvatureBound

namespace YMGap.Continuum.SpacingUniformProgress

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ClusterGapReduction

/-! ## 1. The sharpened curvature template — curvature at ONE function ⇒ `K ≤ λ`

`eigenvalue_ge_of_CD` takes the full `CD K` hypothesis but, in its proof, only
ever uses `hCD f` at the single eigenfunction `f`.  We restate it with exactly
that single instance as the hypothesis: the genuine content (Dirichlet/Bochner
eigen-identities + cancellation of the positive factor `λ·E[f²]`) is unchanged,
the hypothesis is strictly weaker. -/

/-- **The sharpened Bakry–Émery template.**  From the curvature inequality
`K·E[Γ₁(f)] ≤ E[Γ₂(f)]` AT THE SINGLE FUNCTION `f` (rather than the full
`CD K = ∀ f, …`), together with `f` being an eigenfunction of energy `λ > 0` with
positive π-variance, conclude `K ≤ λ`.  Same proof as `eigenvalue_ge_of_CD`,
weaker hypothesis. -/
theorem eigenvalue_ge_of_curv_at (G : BakryEmery.RevGen) {K lam : Q'}
    (f : Nat → Q')
    (hcurv : K * G.E (G.Gamma1 f) ≤ G.E (G.Gamma2 f))
    (hf : G.Eigen f lam)
    (hlam : (0 : Q') < lam)
    (hm : (0 : Q') < G.E (BakryEmery.RevGen.pmul f f)) :
    K ≤ lam := by
  -- m := E[f²];  E[Γ₁ f] ≃ λ·m,  E[Γ₂ f] ≃ λ²·m ≃ λ·(λ·m).
  have hD : (G.E (G.Gamma1 f)).eqv (lam * G.E (BakryEmery.RevGen.pmul f f)) :=
    G.dirichlet_eigen f lam hf
  have hB : (G.E (G.Gamma2 f)).eqv ((lam * lam) * G.E (BakryEmery.RevGen.pmul f f)) :=
    G.bochner_eigen f lam hf
  -- LHS: K·(λ·m) ≤ K·E[Γ₁ f]
  have hL : K * (lam * G.E (BakryEmery.RevGen.pmul f f)) ≤ K * G.E (G.Gamma1 f) :=
    Q'.le_of_eqv (Q'.mul_eqv_congr_left K _ _ (Q'.eqv_symm hD))
  -- RHS: E[Γ₂ f] ≤ λ²·m ≃ λ·(λ·m)
  have hR : G.E (G.Gamma2 f) ≤ lam * (lam * G.E (BakryEmery.RevGen.pmul f f)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hB)
      (Q'.le_of_eqv (Q'.mul_assoc_eqv lam lam (G.E (BakryEmery.RevGen.pmul f f))))
  -- chain: K·(λ·m) ≤ K·E[Γ₁ f] ≤ E[Γ₂ f] ≤ λ·(λ·m)
  have hchain : K * (lam * G.E (BakryEmery.RevGen.pmul f f))
      ≤ lam * (lam * G.E (BakryEmery.RevGen.pmul f f)) :=
    Q'.le_trans' _ _ _ hL (Q'.le_trans' _ _ _ hcurv hR)
  -- cancel the positive factor (λ·m)
  have hpos : (0 : Q') < lam * G.E (BakryEmery.RevGen.pmul f f) :=
    BakryEmery.mul_pos hlam hm
  exact BakryEmery.le_of_mul_le_mul_right_pos hpos hchain

/-! ## 2. The sharper named residual — `ModeCurvatureBound`

Identical interface to `UniformCurvatureBound` save for the one curvature field:
the full `uniform_CD : ∀ k, (gen k).CD K` is replaced by `curv_on_modes`, the
curvature inequality assumed ONLY at the spectral eigenmodes `eigf k i`.  All
other fields (the eigen-link, positivity of energies/variances, the transfer
step) are carried verbatim, as `Type`-level data (Rule 8). -/

/-- **The mode-curvature bound — the sharper continuum residual.**  Like
`UniformCurvatureBound`, but the curvature obligation is only the Bochner
inequality `K·E[Γ₁(eigf k i)] ≤ E[Γ₂(eigf k i)]` AT EACH SPECTRAL MODE, not the
full `∀ f` curvature-dimension bound.  The per-spacing located gaps and the
strictly-positive continuum mass are PROVED from this weaker input. -/
structure ModeCurvatureBound : Type where
  /-- A finite reversible heat-kernel generator at each spacing `k`. -/
  gen : Nat → BakryEmery.RevGen
  /-- The finite transfer spectral model at each spacing `k`. -/
  spec : Nat → SpectralModel
  /-- A SINGLE curvature constant `K`. -/
  K : Q'
  /-- The curvature constant is strictly positive (the no-collapse magnitude). -/
  K_pos : (0 : Q') < K
  /-- A single strictly-positive transfer step `s` (`P = I − s·L`). -/
  s : Q'
  /-- The transfer step is strictly positive. -/
  s_pos : (0 : Q') < s
  /-- The curvature margin `s·K` is strictly below `1`. -/
  step_small : s * K < (1 : Q')
  /-- The eigen-link: an eigenfunction of `gen k` for the `i`-th transfer mode. -/
  eigf : Nat → Nat → (Nat → Q')
  /-- The eigenvalue (generator energy) of the `i`-th transfer mode at spacing
  `k`. -/
  eigval : Nat → Nat → Q'
  /-- `eigf k i` is a genuine eigenfunction of `gen k` with energy `eigval k i`. -/
  eigen : ∀ k i : Nat, (gen k).Eigen (eigf k i) (eigval k i)
  /-- Each generator energy is strictly positive (an excited, non-vacuum mode). -/
  eigval_pos : ∀ k i : Nat, (0 : Q') < eigval k i
  /-- Each mode has strictly positive π-variance. -/
  var_pos : ∀ k i : Nat,
    (0 : Q') < (gen k).E (BakryEmery.RevGen.pmul (eigf k i) (eigf k i))
  /-- **The named open input (SHARPER than `uniform_CD`):** the curvature
  inequality assumed ONLY at the spectral modes — `K·E[Γ₁(eigf k i)] ≤
  E[Γ₂(eigf k i)]` at every spacing `k` and mode `i`. -/
  curv_on_modes : ∀ k i : Nat,
    K * (gen k).E ((gen k).Gamma1 (eigf k i)) ≤ (gen k).E ((gen k).Gamma2 (eigf k i))
  /-- **The eigen-link:** the `i`-th transfer eigenvalue is the transfer
  `1 − s·(eigval k i)` of the `i`-th generator energy. -/
  spec_lam_eq : ∀ k i : Nat, (spec k).lam i = (1 : Q') - s * eigval k i

namespace ModeCurvatureBound

variable (M : ModeCurvatureBound)

/-! ## 3. The forward arrow — the residual is IMPLIED by the original wall

A `UniformCurvatureBound` gives a `ModeCurvatureBound` by instantiating its full
`uniform_CD` at the eigenfunctions.  This PROVES the new residual is no stronger
than the original (so the wall genuinely did not grow); the converse is not
provided. -/

/-- **`ofUniform` — the original wall implies the sharper residual.**  Every
`UniformCurvatureBound` yields a `ModeCurvatureBound`: the mode curvature
`curv_on_modes k i` is just `uniform_CD k` instantiated at the eigenfunction
`eigf k i`.  Witnesses that `ModeCurvatureBound` is a genuine WEAKENING of
`UniformCurvatureBound`. -/
def ofUniform (B : UniformCurvatureBound.UniformCurvatureBound) : ModeCurvatureBound where
  gen := B.gen
  spec := B.spec
  K := B.K
  K_pos := B.K_pos
  s := B.s
  s_pos := B.s_pos
  step_small := B.step_small
  eigf := B.eigf
  eigval := B.eigval
  eigen := B.eigen
  eigval_pos := B.eigval_pos
  var_pos := B.var_pos
  -- the full curvature, instantiated at the spectral eigenfunction
  curv_on_modes := fun k i => B.uniform_CD k (B.eigf k i)
  spec_lam_eq := B.spec_lam_eq

/-! ## 4. The uniform located separator (same `1 − s·K` as the full route) -/

/-- The uniform located separator `1 − s·K`, the same at every spacing. -/
def sep : Q' := (1 : Q') - M.s * M.K

/-- The uniform separator is strictly below the vacuum eigenvalue `1`. -/
theorem sep_lt_one : M.sep < (1 : Q') :=
  BakryEmery.one_sub_lt_one (BakryEmery.mul_pos M.s_pos M.K_pos)

/-! ## 5. The per-spacing transfer bound — mode curvature ⇒ every eigenvalue `≤ sep`

The sharpened template fires on each spectral mode: `curv_on_modes k i` gives
`K ≤ eigval k i`, and the order-reversing transfer map carries that to
`(spec k).lam i ≤ 1 − s·K = sep`.  This is the only place the curvature input is
consumed, and it is consumed ONLY at the modes. -/

/-- **Per-spacing transfer bound (mode curvature ⇒ gap).**  At spacing `k`, every
transfer eigenvalue is `≤ 1 − s·K = sep`, from the mode curvature inequality
through the sharpened template and the order-reversing transfer map. -/
theorem transfer_bound (k : Nat) : SpectralGapBound (M.spec k) M.sep := by
  intro i
  have hKle : M.K ≤ M.eigval k i :=
    eigenvalue_ge_of_curv_at (M.gen k) (M.eigf k i) (M.curv_on_modes k i)
      (M.eigen k i) (M.eigval_pos k i) (M.var_pos k i)
  have htr : (1 : Q') - M.s * M.eigval k i ≤ (1 : Q') - M.s * M.K :=
    UniformCurvatureBound.transfer_le_of_energy_ge (Q'.le_of_lt M.s_pos) hKle
  rw [M.spec_lam_eq k i]
  exact htr

/-! ## 6. The per-spacing located gaps (uniform separator) -/

/-- **The per-spacing LOCATED gap (uniform in `k`).**  Each transfer model has a
located spectral gap with the uniform separator `1 − s·K < 1`, proved from the
mode curvature input. -/
def located (k : Nat) : LocatedSpectralGap (M.spec k) where
  sep := M.sep
  sep_lt_one := M.sep_lt_one
  bound := M.transfer_bound k

/-! ## 7. The reduction to a volume-uniform cluster bound

Identical structure to the full-curvature route: the curvature margin `s·K` is
the SAME at every spacing, so the gap-margin sequence is constant, its geometric
tail is trivial (`tailConst = 0`), and the uniform floor is `s·K` itself. -/

/-- The uniform curvature margin `s·K > 0`. -/
def margin : Q' := M.s * M.K

/-- The curvature margin is strictly positive. -/
theorem margin_pos : (0 : Q') < M.margin :=
  BakryEmery.mul_pos M.s_pos M.K_pos

/-- The curvature margin equals every per-spacing located gap margin:
`s·K = 1 − (1 − s·K)`.  (Definitional unfolding of `gapMargin`/`sep`.) -/
theorem margin_eq_gapMargin (k : Nat) :
    (M.located k).gapMargin.eqv M.margin := by
  show ((1 : Q') - ((1 : Q') - M.s * M.K)).eqv (M.s * M.K)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 : Q') (-((1 : Q') + (-(M.s * M.K))))
      ((-(1 : Q')) + (-(-(M.s * M.K)))) (Q'.neg_add_eqv (1 : Q') (-(M.s * M.K)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 : Q') ((-(1 : Q')) + (-(-(M.s * M.K))))
      ((-(1 : Q')) + (M.s * M.K))
      (Q'.add_eqv_congr_left (-(1 : Q')) (-(-(M.s * M.K))) (M.s * M.K)
        (Q'.neg_neg_eqv (M.s * M.K)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-(1 : Q')) (M.s * M.K))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((1 : Q') + (-(1 : Q'))) 0 (M.s * M.K)
      (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (M.s * M.K))

/-- **The reduction (mode curvature ⇒ cluster).**  The mode-curvature data is
reduced to a volume-uniform cluster bound: the located gaps are the mode-curvature
located gaps (uniform separator `1 − s·K`), the uniform floor is the margin `s·K`,
and the gap-margin sequence is constant so the geometric tail is trivial
(`tailConst = 0`). -/
def toUniformClusterBound : UniformClusterBound where
  gaps := M.spec
  located := M.located
  floorRate := M.margin
  floorRate_pos := M.margin_pos
  uniform_floor := fun Λ => Q'.ge_of_eqv (M.margin_eq_gapMargin Λ)
  tailConst := 0
  tailConst_nonneg := by decide
  incr_up := fun Λ =>
    Q'.add_le_self_of_nonneg ((M.located Λ).gapMargin) (geoIncr 0 Λ)
      (geoIncr_nonneg 0 (by decide) Λ)
  incr_lo := fun Λ =>
    Q'.add_le_self_of_nonneg ((M.located (Λ + 1)).gapMargin) (geoIncr 0 Λ)
      (geoIncr_nonneg 0 (by decide) Λ)
  modulus := fun ε hε =>
    ⟨1, by decide, by
      have h0 : ((Q'.ofNat 2 * (0 : Q')) * (1 : Q')).eqv (0 : Q') := by decide
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h0) (Q'.le_of_lt hε)⟩

/-! ## 8. The capstone — mode curvature ⇒ strictly-positive continuum mass -/

/-- The continuum gap rate built from the mode-curvature data: the `CReal` limit
of the per-spacing gap-margin sequence (the constant sequence `s·K`). -/
def continuumRate : CReal :=
  ClusterGapReduction.continuumRate M.toUniformClusterBound

/-- **THE CAPSTONE (sharpened geometric reduction).**  A `ModeCurvatureBound` —
the spacing-uniform curvature assumed ONLY at the spectral modes — already yields
a strictly-positive continuum mass gap, by the same located-gap ⇒
uniform-cluster-bound ⇒ positivity pipeline used for full curvature. -/
theorem mode_curvature_continuum_mass_isPositive :
    CReal.IsPositive M.continuumRate :=
  ClusterGapReduction.clusterBound_continuum_mass_isPositive M.toUniformClusterBound

/-- **The continuum gap, packaged.**  The continuum mass as `Type`-level `CReal`
data with its strict-positivity proof, produced end-to-end from the sharper
mode-curvature residual. -/
def mode_curvature_continuum_gap_bridge : Σ' m : CReal, CReal.IsPositive m :=
  ⟨M.continuumRate, M.mode_curvature_continuum_mass_isPositive⟩

/-- The packaged mass is exactly the mode-curvature continuum rate. -/
theorem mode_bridge_fst :
    M.mode_curvature_continuum_gap_bridge.1 = M.continuumRate := rfl

/-! ## 9. Consistency with the full-curvature route

The continuum mass produced from `ofUniform B` agrees, by construction, with the
mode-curvature pipeline: both run the same located gaps through the same cluster
reduction.  We record that the located separator coincides with the full route's
`sep` (definitional), confirming the two routes share their gap magnitude. -/

/-- The mode-curvature separator built from `ofUniform B` is the full route's
separator `1 − s·K` (definitionally identical). -/
theorem ofUniform_sep (B : UniformCurvatureBound.UniformCurvatureBound) :
    (ofUniform B).sep = B.sep := rfl

end ModeCurvatureBound

end YMGap.Continuum.SpacingUniformProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SpacingUniformProgress.eigenvalue_ge_of_curv_at
#print axioms YMGap.Continuum.SpacingUniformProgress.ModeCurvatureBound.ofUniform
#print axioms YMGap.Continuum.SpacingUniformProgress.ModeCurvatureBound.sep_lt_one
#print axioms YMGap.Continuum.SpacingUniformProgress.ModeCurvatureBound.transfer_bound
#print axioms YMGap.Continuum.SpacingUniformProgress.ModeCurvatureBound.located
#print axioms YMGap.Continuum.SpacingUniformProgress.ModeCurvatureBound.margin_pos
#print axioms YMGap.Continuum.SpacingUniformProgress.ModeCurvatureBound.margin_eq_gapMargin
#print axioms YMGap.Continuum.SpacingUniformProgress.ModeCurvatureBound.toUniformClusterBound
#print axioms YMGap.Continuum.SpacingUniformProgress.ModeCurvatureBound.mode_curvature_continuum_mass_isPositive
#print axioms YMGap.Continuum.SpacingUniformProgress.ModeCurvatureBound.mode_curvature_continuum_gap_bridge
#print axioms YMGap.Continuum.SpacingUniformProgress.ModeCurvatureBound.ofUniform_sep
