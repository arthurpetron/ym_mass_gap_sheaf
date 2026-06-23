/-
Route 2 capstone reframing — **the uniform-curvature wall**: a spacing-uniform
Bakry–Émery curvature lower bound `CD(K)` with a SINGLE `K > 0`, and the GENUINE
theorem that it forces a strictly-positive continuum mass gap.

# What this module is

The cluster route packages the infinite-volume frontier into ONE volume-uniform
correlation-decay input.  This module is its GEOMETRIC analogue for the a→0
continuum frontier: it packages the per-spacing Yang–Mills heat-kernel transfer
generators together with ONE curvature constant `K > 0` holding UNIFORMLY in the
spacing, and proves that this single uniform curvature bound yields a positive
continuum gap.

The mechanism is the constructive discrete Bakry–Émery template (the
eigenfunction route — pure finite `Q'` linear algebra, no time integral): for a
finite reversible generator `L_k`, the curvature-dimension bound `CD(K)` in
π-mean forces every excited generator energy `λ ≥ K`, hence the transfer
operator `P_k = I − s·L_k` has every excited eigenvalue `≤ 1 − s·K`, a located
spectral gap with margin `s·K`.  Because the SAME `K` (and the same transfer
step `s`) work at every spacing, the per-spacing gap margins share the uniform
positive floor `s·K` — the no-collapse content.  A uniform positive gap-margin
family then yields a strictly-positive continuum mass via the existing
continuum machinery.

# What is PROVED vs what is the NAMED open input

PROVED here (genuine theorems, no new analytic content):
  * `transfer_bound_of_CD` — the per-spacing transfer bound: from the curvature
    `CD K` and the eigen-link `λ_{k,i} = 1 − s·μ_{k,i}` with `μ_{k,i}` a genuine
    excited generator mode, every transfer eigenvalue is `≤ 1 − s·K`.  This is
    the Bakry–Émery template `eigenvalue_ge_of_CD` carried through the transfer
    map.
  * `located` — the per-spacing LOCATED spectral gap with separator `1 − s·K`
    (uniform in `k`), built by the curvature located-gap bridge.
  * `toUniformClusterBound` — the curvature data REDUCED to a volume-uniform
    cluster bound: the constant gap-margin sequence `s·K` (so the geometric tail
    is trivial, `tailConst = 0`) with uniform floor `s·K`.
  * `curvatureBound_continuum_mass_isPositive` — THE REDUCTION: a
    `UniformCurvatureBound` yields a strictly-positive continuum mass, by
    composing `toUniformClusterBound` with the cluster route's positivity
    capstone.

NAMED (the geometric continuum wall, `Type`-level, Rule 8): `uniform_CD` — a
SINGLE curvature constant `K > 0` with `CD(K)` holding at EVERY spacing.  This is
the reshaped continuum problem: the free/Haar part is curved-positive (a compact
Lie group with its bi-invariant metric has nonnegative Ricci curvature; the
free transfer model admits `CD(K)` with a fixed positive `K`), so the
obstruction is the INTERACTING Wilson-action Hessian as `a → 0` — a uniform
lower curvature bound for the interacting lattice heat-kernel measure.  That
spacing-uniform interacting curvature bound is the named open analytic content,
Bakry–Émery in mechanism, Bałaban-class in difficulty; the closest rigorous
lattice precedent is the strong-coupling log-Sobolev / curvature program for
lattice gauge measures (Shen–Zhu–Zhu, CMP 2023).  It is NOT inhabited here.

This is the GEOMETRIC reduction: curvature controls the gap MAGNITUDE directly
(via the eigenvalue bound `λ ≥ K`), unlike topological/located-but-unquantified
routes which give only stability or a phase.  This does NOT close the continuum
limit; it reduces the a→0 gap frontier to the single uniform-curvature input.

# Axiom-gate (AGENTS.md Rules 1, 6, 8)

Pure `Q'` arithmetic over the proved Bakry–Émery template and the proved cluster
route; no new `axiom`, no `sorry`/`admit`, no `Classical.*`/`native_decide`/
`decide`-on-nondecidable, no `Prop := True` stub.  The `uniform_CD` field remains
the named open input, carried as `Type`-level data (Rule 8).  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.
-/

import YMGap.Continuum.BakryEmery
import YMGap.Continuum.ClusterGapReduction

namespace YMGap.Continuum.UniformCurvatureBound

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ClusterGapReduction

/-! ## 0. The transfer step: generator energy `λ ≥ K` ⇒ transfer eigenvalue `≤ 1 − s·K`

For a fixed nonnegative transfer step `s ≥ 0`, the transfer map `μ ↦ 1 − s·μ` is
order-reversing on `Q'`: the curvature lower bound `K ≤ μ` on a generator energy
becomes the upper bound `1 − s·μ ≤ 1 − s·K` on the corresponding transfer
eigenvalue.  Pure `Q'` arithmetic. -/

/-- Order-reversal of the transfer map.  From `K ≤ μ` and `0 ≤ s` conclude
`1 − s·μ ≤ 1 − s·K` (so a curvature lower bound on the generator energy bounds
the transfer eigenvalue from above). -/
theorem transfer_le_of_energy_ge {s K μ : Q'} (hs : (0 : Q') ≤ s) (h : K ≤ μ) :
    (1 : Q') - s * μ ≤ (1 : Q') - s * K := by
  -- s·K ≤ s·μ, negate, add 1 on the left.
  have hmul : s * K ≤ s * μ := Q'.mul_le_mul_of_nonneg_left K μ s h hs
  have hneg : (-(s * μ)) ≤ (-(s * K)) := Q'.neg_le_neg hmul
  -- 1 + (-(s·μ)) ≤ 1 + (-(s·K)), i.e. 1 - s·μ ≤ 1 - s·K.
  exact Q'.add_le_add_left (1 : Q') (-(s * μ)) (-(s * K)) hneg

/-! ## 1. The uniform curvature bound — the single geometric continuum input

`UniformCurvatureBound` packages, all as `Type`-level data (Rule 8):

  * the per-spacing finite reversible generators `gen k` (the YM heat-kernel
    transfer generators) and per-spacing finite transfer models `spec k`;
  * a SINGLE curvature constant `K > 0` together with the uniform field
    `uniform_CD : ∀ k, CD (gen k) K` — THE named open analytic input;
  * a SINGLE nonnegative transfer step `s` with `s·K < 1` (so the located
    separator `1 − s·K` is genuinely below the vacuum eigenvalue `1`);
  * the EIGEN-LINK certifying each transfer eigenvalue is the transfer of a
    genuine excited generator mode: an eigenfunction `eigf k i` with eigenvalue
    `eigval k i`, positive energy and variance, and `spec_lam_eq` tying
    `(spec k).lam i` to `1 − s·(eigval k i)`.

From this, the per-spacing located gaps with the uniform separator `1 − s·K`
(margin `s·K`, independent of `k`) and the positive continuum mass are PROVED. -/

/-- **The volume-uniform CURVATURE bound** — the single geometric input of the
a→0 continuum limit.  An inhabitant asserts a spacing-uniform Bakry–Émery
curvature lower bound `CD(K)` with one `K > 0`, plus the eigen-link making each
transfer eigenvalue the transfer of a genuine excited generator mode.  The
per-spacing located gaps and the strictly-positive continuum mass are PROVED
from this. -/
structure UniformCurvatureBound : Type where
  /-- A finite reversible heat-kernel generator at each spacing `k`. -/
  gen : Nat → BakryEmery.RevGen
  /-- The finite transfer spectral model at each spacing `k`. -/
  spec : Nat → SpectralModel
  /-- **The named open input:** a SINGLE curvature constant `K`. -/
  K : Q'
  /-- The curvature constant is strictly positive (the no-collapse magnitude). -/
  K_pos : (0 : Q') < K
  /-- **THE uniform curvature wall:** the Bakry–Émery bound `CD(K)` holds at
  EVERY spacing with the SAME `K`. -/
  uniform_CD : ∀ k : Nat, (gen k).CD K
  /-- A single strictly-positive transfer step `s` (`P = I − s·L`). -/
  s : Q'
  /-- The transfer step is strictly positive (so the curvature margin `s·K` is a
  genuine positive gap). -/
  s_pos : (0 : Q') < s
  /-- The curvature margin `s·K` is strictly below `1` — the located separator
  `1 − s·K` lies below the vacuum eigenvalue. -/
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
  /-- Each mode has strictly positive π-variance (a genuine spectral mode). -/
  var_pos : ∀ k i : Nat, (0 : Q') < (gen k).E (BakryEmery.RevGen.pmul (eigf k i) (eigf k i))
  /-- **The eigen-link:** the `i`-th transfer eigenvalue is the transfer
  `1 − s·(eigval k i)` of the `i`-th generator energy. -/
  spec_lam_eq : ∀ k i : Nat, (spec k).lam i = (1 : Q') - s * eigval k i

namespace UniformCurvatureBound

variable (B : UniformCurvatureBound)

/-! ## 2. The uniform located separator and its positivity

The single curvature margin `s·K` gives the located separator `1 − s·K`, which is
strictly below `1` (from `step_small`) and the SAME at every spacing — the
uniform-in-`k` content. -/

/-- The uniform located separator `1 − s·K`, the same at every spacing. -/
def sep : Q' := (1 : Q') - B.s * B.K

/-- The uniform separator is strictly below the vacuum eigenvalue `1`.  This is
exactly the curvature located-gap bridge `one_sub_lt_one` at the positive margin
`s·K > 0` (which `step_small` certifies via `s·K < 1`). -/
theorem sep_lt_one : B.sep < (1 : Q') :=
  YMGap.Continuum.BakryEmery.one_sub_lt_one
    (YMGap.Continuum.BakryEmery.mul_pos B.s_pos B.K_pos)

/-! ## 3. THE per-spacing transfer bound — curvature ⇒ every transfer eigenvalue `≤ 1 − s·K`

This is the genuine reduction at a single spacing: feed the curvature `CD K` and
the eigen-link to the Bakry–Émery template `eigenvalue_ge_of_CD` to get
`K ≤ eigval k i`, then transfer-reverse to `(spec k).lam i ≤ 1 − s·K`. -/

/-- **Per-spacing transfer bound (curvature ⇒ gap).**  At spacing `k`, every
transfer eigenvalue is `≤ 1 − s·K = sep`: the curvature bound `CD K` forces each
generator energy `≥ K` (template `eigenvalue_ge_of_CD`), and the order-reversing
transfer map carries that to the eigenvalue upper bound. -/
theorem transfer_bound_of_CD (k : Nat) : SpectralGapBound (B.spec k) B.sep := by
  intro i
  -- K ≤ eigval k i  (Bakry–Émery template at this genuine excited mode)
  have hKle : B.K ≤ B.eigval k i :=
    (B.gen k).eigenvalue_ge_of_CD (B.uniform_CD k) (B.eigf k i) (B.eigen k i)
      (B.eigval_pos k i) (B.var_pos k i)
  -- (spec k).lam i = 1 − s·(eigval k i) ≤ 1 − s·K = sep
  have htr : (1 : Q') - B.s * B.eigval k i ≤ (1 : Q') - B.s * B.K :=
    transfer_le_of_energy_ge (Q'.le_of_lt B.s_pos) hKle
  -- rewrite (spec k).lam i by the eigen-link
  rw [B.spec_lam_eq k i]
  exact htr

/-! ## 4. The per-spacing located spectral gaps (uniform separator)

Each spacing carries a genuine `LocatedSpectralGap` with separator `sep = 1 − s·K`
(strictly below `1`), built from the proved per-spacing transfer bound.  The
separator — hence the gap margin `s·K` — is the SAME at every spacing. -/

/-- **The per-spacing LOCATED gap (uniform in `k`).**  Each transfer model has a
located spectral gap with the uniform separator `1 − s·K < 1`, proved from the
uniform curvature bound. -/
def located (k : Nat) : LocatedSpectralGap (B.spec k) where
  sep := B.sep
  sep_lt_one := B.sep_lt_one
  bound := B.transfer_bound_of_CD k

/-- The per-spacing located gap has margin exactly the curvature margin `s·K`,
the SAME at every spacing: `gapMargin = 1 − (1 − s·K) = s·K`. -/
theorem located_margin (k : Nat) :
    (B.located k).gapMargin = (1 : Q') - ((1 : Q') - B.s * B.K) := rfl

/-! ## 5. THE REDUCTION — curvature data ⇒ a volume-uniform cluster bound

The curvature margin `s·K` is the SAME at every spacing, so the gap-margin
sequence is CONSTANT.  A constant sequence has a trivial geometric tail
(`tailConst = 0`, `geoIncr 0 Λ = 0`), and its uniform floor is `s·K` itself.  We
therefore reduce the curvature data to a `UniformClusterBound`, whose continuum
machinery delivers the positive continuum mass. -/

/-- The uniform curvature margin `s·K > 0` — the constant gap margin and uniform
floor. -/
def margin : Q' := B.s * B.K

/-- The curvature margin equals every per-spacing located gap margin: `s·K =
1 − (1 − s·K)`.  (Definitional unfolding of `gapMargin`/`sep`.) -/
theorem margin_eq_gapMargin (k : Nat) :
    (B.located k).gapMargin.eqv B.margin := by
  -- gapMargin = 1 - (1 - s·K);  margin = s·K.
  show ((1 : Q') - ((1 : Q') - B.s * B.K)).eqv (B.s * B.K)
  -- 1 - (1 + (-(s·K))) ≃ s·K
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 : Q') (-((1 : Q') + (-(B.s * B.K))))
      ((-(1 : Q')) + (-(-(B.s * B.K)))) (Q'.neg_add_eqv (1 : Q') (-(B.s * B.K)))) ?_
  -- 1 + ((-1) + (-(-(s·K)))) ≃ (1 + (-1)) + (s·K) ≃ 0 + s·K ≃ s·K
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 : Q') ((-(1 : Q')) + (-(-(B.s * B.K))))
      ((-(1 : Q')) + (B.s * B.K))
      (Q'.add_eqv_congr_left (-(1 : Q')) (-(-(B.s * B.K))) (B.s * B.K)
        (Q'.neg_neg_eqv (B.s * B.K)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-(1 : Q')) (B.s * B.K))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((1 : Q') + (-(1 : Q'))) 0 (B.s * B.K)
      (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (B.s * B.K))

/-- The curvature margin `s·K` is strictly positive. -/
theorem margin_pos : (0 : Q') < B.margin :=
  YMGap.Continuum.BakryEmery.mul_pos B.s_pos B.K_pos

/-- **THE REDUCTION (curvature ⇒ cluster).**  The curvature data is reduced to a
volume-uniform cluster bound: the located gaps are the curvature located gaps
(uniform separator `1 − s·K`), the uniform floor is the curvature margin `s·K`,
and — because the separator is the SAME at every spacing — the gap-margin
sequence is CONSTANT, so its geometric tail is trivial (`tailConst = 0`,
`geoIncr 0 Λ = 0`).  This converts the geometric curvature input into the cluster
route's continuum machinery. -/
def toUniformClusterBound : UniformClusterBound where
  gaps := B.spec
  located := B.located
  floorRate := B.margin
  floorRate_pos := B.margin_pos
  uniform_floor := fun Λ => Q'.ge_of_eqv (B.margin_eq_gapMargin Λ)
  tailConst := 0
  tailConst_nonneg := by decide
  -- consecutive margins are the SAME term (the separator is uniform in k), so the
  -- single-step bounds reduce to `m ≤ m + 0` (a nonnegative geometric increment).
  incr_up := fun Λ =>
    Q'.add_le_self_of_nonneg ((B.located Λ).gapMargin) (geoIncr 0 Λ)
      (geoIncr_nonneg 0 (by decide) Λ)
  incr_lo := fun Λ =>
    Q'.add_le_self_of_nonneg ((B.located (Λ + 1)).gapMargin) (geoIncr 0 Λ)
      (geoIncr_nonneg 0 (by decide) Λ)
  modulus := fun ε hε =>
    -- with tailConst = 0 the rescaling is vacuous: `(2·0)·δ ≃ 0 ≤ ε`.
    ⟨1, by decide, by
      -- (Q'.ofNat 2 * 0) * 1 ≤ ε  reduces to 0 ≤ ε
      have h0 : ((Q'.ofNat 2 * (0 : Q')) * (1 : Q')).eqv (0 : Q') := by decide
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h0) (Q'.le_of_lt hε)⟩

/-! ## 6. THE CAPSTONE — uniform curvature ⇒ strictly-positive continuum mass

Composing the reduction with the cluster route's positivity capstone gives the
end-to-end geometric theorem: a single spacing-uniform curvature bound `CD(K)`,
`K > 0`, forces a strictly-positive continuum mass gap. -/

/-- The continuum gap rate built from the curvature data: the `CReal` limit of
the per-spacing gap-margin sequence (here the constant sequence `s·K`), via the
cluster route's continuum-rate engine. -/
def continuumRate : CReal :=
  ClusterGapReduction.continuumRate B.toUniformClusterBound

/-- **THE CAPSTONE (geometric reduction).**  A volume-uniform curvature bound
`CD(K)` with a single `K > 0` yields a strictly-positive continuum mass gap.
Proof: reduce the curvature data to a `UniformClusterBound` and apply the cluster
route's positivity capstone.  The gap MAGNITUDE is delivered by the curvature `K`
(through the margin `s·K`), not merely a phase/stability statement. -/
theorem curvatureBound_continuum_mass_isPositive :
    CReal.IsPositive B.continuumRate :=
  ClusterGapReduction.clusterBound_continuum_mass_isPositive B.toUniformClusterBound

/-- **The continuum gap, packaged.**  The continuum mass as `Type`-level `CReal`
data together with its strict-positivity proof, produced end-to-end from the
single uniform-curvature bound. -/
def curvature_continuum_gap_bridge : Σ' m : CReal, CReal.IsPositive m :=
  ⟨B.continuumRate, B.curvatureBound_continuum_mass_isPositive⟩

/-- The packaged mass is exactly the curvature continuum rate. -/
theorem curvature_bridge_fst :
    B.curvature_continuum_gap_bridge.1 = B.continuumRate := rfl

/-! ## 7. CONNECTION to the free anchor and the Stage-2 continuum certificate

The FREE/Haar part is curved-positive: a compact Lie group with its bi-invariant
metric has nonnegative Ricci curvature, and the free transfer model admits a
Bakry–Émery bound `CD(K)` with a fixed positive `K` (the curved-positive anchor;
the concrete two-state reversible chain `BakryEmery.chain2` is the sharp
`CD(K = 2)` inhabitant of the template at finite scale).  A `UniformCurvatureBound`
would require the INTERACTING uniform `CD(K > 0)` to PERSIST as the spacing
`a → 0` — that is the named geometric wall this module isolates.

The conclusion produced here — a strictly-positive continuum mass `CReal` with
its positivity proof — has exactly the shape the Stage-2 capstone consumes for
its gap requirement: the curvature route therefore PARALLELS the dimensionless
ratio route as an alternative geometric supplier of the same positive continuum
gap, packaged below as a `Σ'`-bundled positive mass. -/

/-- **The free curved-positive anchor (sanity).**  The concrete two-state
reversible chain satisfies the curvature template's eigenvalue bound: under the
free curvature `CD(K)` its genuine excited mode has energy `≥ K` (with the sharp
`K = 2`).  This witnesses that the curvature template fires non-vacuously on a
real reversible chain — the curved-positive free anchor underlying any
`UniformCurvatureBound`. -/
theorem free_anchor_curved_positive {K : Q'}
    (hCD : YMGap.Continuum.BakryEmery.chain2.CD K) :
    K ≤ YMGap.Continuum.BakryEmery.two :=
  YMGap.Continuum.BakryEmery.chain2_template hCD

end UniformCurvatureBound

end YMGap.Continuum.UniformCurvatureBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.UniformCurvatureBound.transfer_le_of_energy_ge
#print axioms YMGap.Continuum.UniformCurvatureBound.UniformCurvatureBound.sep_lt_one
#print axioms YMGap.Continuum.UniformCurvatureBound.UniformCurvatureBound.transfer_bound_of_CD
#print axioms YMGap.Continuum.UniformCurvatureBound.UniformCurvatureBound.located
#print axioms YMGap.Continuum.UniformCurvatureBound.UniformCurvatureBound.margin_eq_gapMargin
#print axioms YMGap.Continuum.UniformCurvatureBound.UniformCurvatureBound.margin_pos
#print axioms YMGap.Continuum.UniformCurvatureBound.UniformCurvatureBound.toUniformClusterBound
#print axioms YMGap.Continuum.UniformCurvatureBound.UniformCurvatureBound.curvatureBound_continuum_mass_isPositive
#print axioms YMGap.Continuum.UniformCurvatureBound.UniformCurvatureBound.curvature_continuum_gap_bridge
#print axioms YMGap.Continuum.UniformCurvatureBound.UniformCurvatureBound.free_anchor_curved_positive
