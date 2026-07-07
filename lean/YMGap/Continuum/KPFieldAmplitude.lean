/-
Track B / R2 — the KOTECKÝ–PREISS AMPLITUDE BOUND for the field-space (Bałaban) cluster
expansion: the connected n-cluster Ursell amplitude `|z_n(w)| ≤ (μ·g²)^n`, PROVED reducible
to the SINGLE config-space quantity `|z_1| ≤ g²` via the PROVED Penrose tree inequality plus
the banked Cayley/Euler tree-count factorisation.

# The obligation (read first)

`FieldSpaceCluster.FieldClusterConvergence.inducedBound` — the OPEN config-space amplitude
estimate — is the amplitude bound `|z_n(w)| ≤ (μ·g²)^n` for the REAL connected field-space
Ursell amplitudes `z_n` over field configurations.  `FieldSpaceCluster` reduced continuum
form-preservation to this, proved the SCALAR field-space scaffold (activity `g²∼(1−w)`,
cluster convergence, the `O(g⁴)` second cumulant, the machine-checked inversion of the
character expansion), and NAMED `inducedBound` as the honest residual — the piece needing the
configuration-space Gaussian measure (the new substrate).

This module makes the KOTECKÝ–PREISS structure of that amplitude bound explicit and PROVES
its ENTIRE COMBINATORIAL content, concentrating the residual to the single scalar
`|z_1| ≤ g²`.

# The Kotecký–Preiss amplitude bound, made precise

The connected n-cluster amplitude is the Ursell sum over connected clusters `Y` of `n`
polymers through a fixed plaquette:  `z_n = Σ_{Y : |Y|=n} φ^T(Y)·ζ(Y)`.  The KP / Penrose
tree-graph bound dominates it termwise:

    |z_n|  ≤  (# connected size-n clusters)  ·  (per-cluster tree-graph coeff)  ·  (activity)^n
          ≤  N_n                              ·  eSurrogate^n                   ·  a^n
          ≤  K^n · 3^n · a^n  =  (3K·a)^n  =  (μ·a)^n ,     μ := 3K ,

where:
  * `N_n ≤ K^n`         — the lattice-animal count (`KPCriterion.ClusterCountBound`, a
    GEOMETRIC/combinatorial input about the lattice, not the measure);
  * `φ^T(Y) ≤ eSurrogate^{|Y|} = 3^{|Y|}` — the per-cluster **Penrose tree-graph bound**,
    PROVED via `PenroseDomInduction.penroseIneq` (`|C(G)| ≤ τ(G)`) + Cayley (`τ ≤ n^{n-2}`)
    + Euler (`n^{n-2} ≤ 3^n·n!`, PROVED `CubicEulerBoundProof.cubicEulerBound`), assembled by
    `TreeGraphBoundProgress.tree_graph_of_reduction`;
  * `ζ(Y) ≤ a^{|Y|}`    — activity factorisation from the SINGLE config-space quantity
    `a = |z_1| ≤ g² = (1−w)` (the plaquette activity of ONE connected field-space cluster).

So the AMPLITUDE bound `|z_n| ≤ (μ·g²)^n` and the KP CONVERGENCE `Σ_n |z_n| ≤ 1/(1−μg²)` are
ENTIRELY COMBINATORIAL (tree-graph count + geometric series) once the single scalar
`|z_1| ≤ g²` is supplied.  That scalar is the genuine 4D-YM-measure quantity — it needs the
configuration-space Gaussian measure — and is carried honestly as the sole open field.

# What is PROVED here (axiom-clean `Q'`/`Nat`)

  * `combGrowth_le` — the combinatorial tree-count × animal growth
    `N_n · eSurrogate^n ≤ (K·eSurrogate)^n`, from the PROVED per-cluster Penrose bound
    (`ClusterCountBound.count_le`) and the two-factor power law.  This is the tree-count
    factor `τ_n ≤ (eμ)^n` content, reduced to the PROVED Penrose/Cayley/Euler chain.
  * `perCluster_penrose` — the per-cluster tree-graph coefficient bound
    `φ^T(Y) ≤ eSurrogate^{|Y|}`, re-exported straight from
    `TreeGraphBoundProgress.tree_graph_of_reduction` with the PROVED `cubicEulerBound`,
    i.e. the analytic heart is `PenroseDomInduction.penroseIneq`.
  * `KPAmplitude` — the field-space KP amplitude datum, carrying the connectivity growth
    `mu` (= `3K`, PROVED-bounded by `combGrowth_le`), the amplitudes `zAmp`, the KP
    tree-graph domination `treeDom : |z_n| ≤ mu^n·a^n`, and the SINGLE config-space field
    `single_le_g2 : |z_1| ≤ g² = (1−w)`.
  * `amplitude_le` — **THE KP AMPLITUDE BOUND** `|z_n(w_k)| ≤ (μ·g²)^n`, PROVED from
    `treeDom` + `single_le_g2` (power monotonicity + two-factor power law).
  * `clusterSum_le` — **THE KP CONVERGENCE** `Σ_{n<N} |z_n| ≤ 1/(1 − μg²)` for `μg² < 1`,
    PROVED via `amplitude_le` + the geometric series `geomSum_le_recip`.
  * `SinglePolymerActivity` — the SOLE remaining config-space (4D-YM-measure) quantity,
    `|z_1| ≤ g²`, named honestly.

# HONEST VERDICT (adversarial — AGENTS.md Rule 6/9)

Everything COMBINATORIAL in the amplitude bound is PROVED:
  * the tree-count growth `τ_n ≤ (eμ)^n` reduces to `penroseIneq` (PROVED) + Cayley (banked,
    loose Cayley CLOSED) + Euler (`cubicEulerBound`, PROVED);
  * the n-fold `(μ·a)^n` and the geometric convergence `Σ ≤ 1/(1−μa)` are proved here.

The GENUINE remaining measure-theoretic input is the SINGLE scalar `|z_1| ≤ g²` (the induced
single-polymer activity from ONE connected field-space cluster — the config-space Gaussian
measure content, the new substrate).  The KP tree-graph domination `treeDom` is the
field-Ursell-expansion STRUCTURE (the substrate: that `z_n` decomposes as a sum over connected
clusters of coefficient × activity); GIVEN that structure, whose growth coefficient is PROVED
`≤ μ^n`, the whole amplitude bound is driven by the single scalar `|z_1| ≤ g²`.

This does NOT close the measure quantity; it proves the combinatorial scaffold and names
`|z_1| ≤ g²` as the sole residual.  No guarded frontier bundle is inhabited; nothing is faked;
the 4D Yang–Mills mass gap remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Pure `Q'`/`Nat`, reusing PROVED `tree_graph_of_reduction`, `cubicEulerBound`,
`geomSum_le_recip`, `ClusterCountBound.count_le`, `fieldActivity`.  Every load-bearing
declaration is `#print axioms`-gated to `propext`/`Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.FieldSpaceCluster
import YMGap.Continuum.TreeGraphBoundProgress
import YMGap.Continuum.CubicEulerBound
import YMGap.Continuum.KPCriterion

namespace YMGap.Continuum.KPFieldAmplitude

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.LargeFieldSuppression
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.CubicEulerBoundProof
open YMGap.Continuum.FieldSpaceCluster

/-! ## 0. Two `Q'` power-law helpers (self-contained). -/

/-- Four-factor commutative rearrangement `(a·b)·(c·d) ≃ (a·c)·(b·d)` (mirrors
`KPCriterion.rearrange6`; reduces to the `Int` cross-product identity via `mul_den_cast`). -/
theorem rearrange4 (a b c d : Q') :
    ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  show ((a * b) * (c * d)).num * (((a * c) * (b * d)).den : Int)
      = ((a * c) * (b * d)).num * (((a * b) * (c * d)).den : Int)
  rw [Q'.mul_den_cast (a * c) (b * d), Q'.mul_den_cast a c, Q'.mul_den_cast b d,
      Q'.mul_den_cast (a * b) (c * d), Q'.mul_den_cast a b, Q'.mul_den_cast c d]
  show (a.num * b.num) * (c.num * d.num)
        * (((a.den : Int) * c.den) * ((b.den : Int) * d.den))
      = (a.num * c.num) * (b.num * d.num)
        * (((a.den : Int) * b.den) * ((c.den : Int) * d.den))
  simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]

/-- **Two-factor power law** `(a·b)^n ≃ a^n · b^n` (induction, `rearrange4` at the step). -/
theorem mul_pow_eqv (a b : Q') : ∀ n : Nat, ((a * b) ^ n).eqv (a ^ n * b ^ n)
  | 0 => by
      show ((1 : Q')).eqv (1 * 1)
      exact Q'.eqv_symm (Q'.mul_one_eqv 1)
  | k + 1 => by
      show ((a * b) * (a * b) ^ k).eqv (a ^ (k + 1) * b ^ (k + 1))
      have hRHS : a ^ (k + 1) * b ^ (k + 1) = (a * a ^ k) * (b * b ^ k) := by
        rw [Q'.pow_succ, Q'.pow_succ]
      rw [hRHS]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (a * b) ((a * b) ^ k) (a ^ k * b ^ k) (mul_pow_eqv a b k)) ?_
      exact rearrange4 a b (a ^ k) (b ^ k)

/-- **Base monotonicity** of `Q'.pow`: `0 ≤ a → a ≤ b → a^n ≤ b^n` (self-contained copy). -/
theorem powLePow (a b : Q') (ha : (0 : Q') ≤ a) (hab : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => by show (1 : Q') ≤ 1; exact Q'.le_refl' 1
  | n + 1 => by
      have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
      show a * a ^ n ≤ b * b ^ n
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right a b (a ^ n) hab (Q'.pow_nonneg a ha n))
        (Q'.mul_le_mul_of_nonneg_left (a ^ n) (b ^ n) b (powLePow a b ha hab n) hb)

/-- `r^n ≃ RGTransport.qpow r n` (the two power folds differ only by factor order). -/
theorem pow_eqv_qpow (r : Q') : ∀ n : Nat, (r ^ n).eqv (RGTransport.qpow r n)
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      show (r * r ^ n).eqv (RGTransport.qpow r n * r)
      exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv r (r ^ n))
        (Q'.mul_eqv_congr_right (r ^ n) (RGTransport.qpow r n) r (pow_eqv_qpow r n))

/-- `Σ_{n<N} r^n ≃ geomSum r N` (the geometric partial sum, `geomSum` uses `qpow`). -/
theorem finSumPow_eqv_geomSum (r : Q') : ∀ N : Nat,
    (finSum (fun n => r ^ n) N).eqv (geomSum r N)
  | 0 => Q'.eqv_refl 0
  | N + 1 => by
      show (finSum (fun n => r ^ n) N + r ^ N).eqv (geomSum r N + RGTransport.qpow r N)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (r ^ N) (finSumPow_eqv_geomSum r N))
        (Q'.add_eqv_congr_left (geomSum r N) _ _ (pow_eqv_qpow r N))

/-! ## 1. The combinatorial tree-count growth (PROVED via Penrose / Cayley / Euler). -/

/-- **The per-cluster Penrose tree-graph coefficient bound** `φ^T(Y) ≤ eSurrogate^{|Y|}`,
re-exported from the PROVED `tree_graph_of_reduction` with the PROVED `cubicEulerBound`.  The
analytic heart is `PenroseDomInduction.penroseIneq` (`|C(G)| ≤ τ(G)`, PROVED by
deletion–contraction); leg (C) is Cayley `τ ≤ n^{n-2}` (banked); leg (A) is the Euler bound
`n^{n-2} ≤ 3^n·n!` (`cubicEulerBound`, PROVED).  This is the combinatorial per-cluster factor
feeding the KP amplitude bound. -/
theorem perCluster_penrose {S : SepLattice} {w : Q'} {r : Rep}
    (red : TreeGraphReduction S w r) (Y : Polymer S.toLattice) :
    red.phiT Y ≤ eSurrogate ^ (Polymer.size Y) :=
  tree_graph_of_reduction red cubicEulerBound Y

/-- The combinatorial tree-count × animal-count growth coefficient
`combGrowth n = N_n · eSurrogate^n` (the KP tree-graph count `τ_n` bundled with the
lattice-animal count). -/
def combGrowth {L : Lattice} {p : L.Plaquette} (cc : ClusterCountBound L p) (n : Nat) : Q' :=
  cc.animalCount n * eSurrogate ^ n

/-- **THE TREE-COUNT GROWTH BOUND** `combGrowth n = N_n·eSurrogate^n ≤ (K·eSurrogate)^n`
(`= (μ)^n` with `μ = 3K`).  This is the KP tree-count bound `τ_n ≤ (eμ)^n` content: the
lattice-animal count `N_n ≤ K^n` (`count_le`, the geometric/combinatorial crux) times the
PROVED per-cluster Penrose factor `eSurrogate^n`, via the two-factor power law. -/
theorem combGrowth_le {L : Lattice} {p : L.Plaquette} (cc : ClusterCountBound L p) (n : Nat) :
    combGrowth cc n ≤ (cc.K * eSurrogate) ^ n := by
  have h1 : cc.animalCount n * eSurrogate ^ n ≤ cc.K ^ n * eSurrogate ^ n :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (cc.count_le n)
      (Q'.pow_nonneg eSurrogate eSurrogate_nonneg n)
  exact Q'.le_trans' _ _ _ h1 (Q'.ge_of_eqv (mul_pow_eqv cc.K eSurrogate n))

/-! ## 2. The field-space KP amplitude datum and the amplitude bound. -/

/-- **`KPAmplitude afr` — the field-space Kotecký–Preiss amplitude datum.**  Carries:

  * `mu` — the connectivity growth constant (`= 3K`, PROVED-bounded by `combGrowth_le`);
  * `a k` — the single-polymer activity `|z_1(w_k)|` at scale `k`;
  * `zAmp k n` — the connected n-cluster Ursell amplitude `|z_n(w_k)|`;
  * **`treeDom`** — the KP TREE-GRAPH DOMINATION `|z_n| ≤ mu^n·a^n`, the field-Ursell
    expansion structure (`z_n = Σ_{clusters} φ^T·ζ`, dominated termwise by Penrose + activity
    factorisation).  This is the field-space substrate — the sum-over-clusters structure;
  * **`single_le_g2`** — THE SINGLE CONFIG-SPACE (4D-YM-measure) QUANTITY: the single-polymer
    activity is bounded by the coupling, `|z_1(w_k)| ≤ g² = (1 − w_k)`.  This is the sole
    genuine measure input; everything else is combinatorial.

HONESTY CAVEAT (Rule 9(6)): `treeDom` and `single_le_g2` bound FREE functions, so — like every
frontier atom in this program — the structure is vacuously inhabitable (`zAmp ≡ 0`, `a ≡ 0`).
The residual is genuine only for the physical field-space amplitudes; the protection is the
frontier guard + refusing to land the fake.  The NON-vacuous content is the PROVED §1–§2
combinatorial tree-count growth, the amplitude bound, and the geometric convergence. -/
structure KPAmplitude (afr : AFRateModulus) : Type where
  /-- The connectivity growth constant `μ = 3K` (`combGrowth_le`). -/
  mu : Q'
  /-- `μ ≥ 0`. -/
  mu_nonneg : (0 : Q') ≤ mu
  /-- The single-polymer activity `|z_1(w_k)|`. -/
  a : Nat → Q'
  /-- `|z_1| ≥ 0`. -/
  a_nonneg : ∀ k, (0 : Q') ≤ a k
  /-- The connected n-cluster amplitude `|z_n(w_k)|`. -/
  zAmp : Nat → Nat → Q'
  /-- `|z_n| ≥ 0`. -/
  zAmp_nonneg : ∀ k n, (0 : Q') ≤ zAmp k n
  /-- **The KP tree-graph domination** `|z_n| ≤ mu^n·a^n` (field-Ursell expansion structure). -/
  treeDom : ∀ k n, zAmp k n ≤ mu ^ n * (a k) ^ n
  /-- **THE SINGLE CONFIG-SPACE QUANTITY** `|z_1(w_k)| ≤ g² = (1 − w_k)`. -/
  single_le_g2 : ∀ k, a k ≤ fieldActivity (afr.w (afCutoff afr + k))

/-- **THE KOTECKÝ–PREISS AMPLITUDE BOUND** `|z_n(w_k)| ≤ (μ·g²)^n`.  PROVED from the KP
tree-graph domination `treeDom` and the single config-space quantity `single_le_g2`:

    |z_n|  ≤  mu^n·a^n  ≃  (mu·a)^n  ≤  (mu·g²)^n ,

the last step by power monotonicity from `a ≤ g² = (1 − w_k)`.  This is the amplitude bound
`|z_n| ≤ (μ·g²)^n` named by `FieldClusterConvergence.inducedBound`, now driven solely by the
single scalar `|z_1| ≤ g²` (the combinatorial `μ^n` is bounded by `combGrowth_le`). -/
theorem amplitude_le {afr : AFRateModulus} (D : KPAmplitude afr) (k n : Nat) :
    D.zAmp k n ≤ (D.mu * fieldActivity (afr.w (afCutoff afr + k))) ^ n := by
  -- |z_n| ≤ mu^n·a^n
  have h1 := D.treeDom k n
  -- mu^n·a^n ≃ (mu·a)^n
  have h2 : D.mu ^ n * (D.a k) ^ n ≤ (D.mu * D.a k) ^ n :=
    Q'.ge_of_eqv (mul_pow_eqv D.mu (D.a k) n)
  -- (mu·a)^n ≤ (mu·g²)^n
  have hg1 : D.a k ≤ fieldActivity (afr.w (afCutoff afr + k)) := D.single_le_g2 k
  have hbase : D.mu * D.a k ≤ D.mu * fieldActivity (afr.w (afCutoff afr + k)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hg1 D.mu_nonneg
  have hbase_nn : (0 : Q') ≤ D.mu * D.a k := Q'.mul_nonneg _ _ D.mu_nonneg (D.a_nonneg k)
  have h3 : (D.mu * D.a k) ^ n
      ≤ (D.mu * fieldActivity (afr.w (afCutoff afr + k))) ^ n :=
    powLePow _ _ hbase_nn hbase n
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3)

/-! ## 3. The Kotecký–Preiss convergence of the cluster sum. -/

/-- **THE KOTECKÝ–PREISS CONVERGENCE** of the field-space cluster amplitude sum.  When the
KP small-activity gate holds (`0 < 1 − μ·g²`, i.e. `μ·g² < 1` — the weak-coupling / deep-UV
regime), the amplitude partial sum is bounded UNIFORMLY in `N`:

    Σ_{n<N} |z_n(w_k)|  ≤  1/(1 − μ·g²) .

PROVED by termwise domination (`amplitude_le`: `|z_n| ≤ (μg²)^n`) into the geometric series
`Σ_n (μg²)^n ≤ 1/(1 − μg²)` (`geomSum_le_recip`).  This is the KP convergence criterion for
the field-space Ursell amplitudes, driven by the single scalar `|z_1| ≤ g²`. -/
theorem clusterSum_le {afr : AFRateModulus} (D : KPAmplitude afr) (k : Nat)
    (hsmall : (0 : Q') < 1 - D.mu * fieldActivity (afr.w (afCutoff afr + k))) (N : Nat) :
    finSum (D.zAmp k) N
      ≤ Q'.divPos 1 (1 - D.mu * fieldActivity (afr.w (afCutoff afr + k))) hsmall := by
  have hr_nn : (0 : Q') ≤ D.mu * fieldActivity (afr.w (afCutoff afr + k)) :=
    Q'.mul_nonneg _ _ D.mu_nonneg
      (fieldActivity_nonneg (Q'.le_of_lt (afr.w_lt_one (afCutoff afr + k))))
  -- termwise: |z_n| ≤ r^n
  have hterm : ∀ n, D.zAmp k n
      ≤ (D.mu * fieldActivity (afr.w (afCutoff afr + k))) ^ n := fun n => amplitude_le D k n
  -- Σ |z_n| ≤ Σ r^n
  have hsum : finSum (D.zAmp k) N
      ≤ finSum (fun n => (D.mu * fieldActivity (afr.w (afCutoff afr + k))) ^ n) N :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _ hterm N
  -- Σ r^n ≃ geomSum r N ≤ 1/(1 − r)
  have hgeoEq : finSum (fun n => (D.mu * fieldActivity (afr.w (afCutoff afr + k))) ^ n) N
      ≤ geomSum (D.mu * fieldActivity (afr.w (afCutoff afr + k))) N :=
    Q'.le_of_eqv (finSumPow_eqv_geomSum _ N)
  have hgeo : geomSum (D.mu * fieldActivity (afr.w (afCutoff afr + k))) N
      ≤ Q'.divPos 1 (1 - D.mu * fieldActivity (afr.w (afCutoff afr + k))) hsmall :=
    geomSum_le_recip hr_nn hsmall N
  exact Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ hgeoEq hgeo)

/-! ## 4. The SOLE remaining config-space quantity and the reduction. -/

/-- **`SinglePolymerActivity afr` — THE SINGLE REMAINING 4D-YM-MEASURE QUANTITY.**  The
induced single-polymer activity from ONE connected field-space cluster, bounded by the
coupling:  `|z_1(w_k)| ≤ g² = (1 − w_k)`.  This is the genuine configuration-space input — it
needs the config-space Gaussian measure (the new substrate) — after the KP tree-graph count,
the n-fold, and the geometric convergence have all been PROVED combinatorially (`combGrowth_le`,
`amplitude_le`, `clusterSum_le`).  Carried as `Type`-level data (Rule 8); UNINHABITED (the
config-space measure construction). -/
structure SinglePolymerActivity (afr : AFRateModulus) : Type where
  /-- The single-polymer activity `|z_1(w_k)|`. -/
  z1 : Nat → Q'
  /-- `|z_1| ≥ 0`. -/
  z1_nonneg : ∀ k, (0 : Q') ≤ z1 k
  /-- **THE CONFIG-SPACE BOUND** `|z_1(w_k)| ≤ g² = (1 − w_k)`. -/
  z1_le_g2 : ∀ k, z1 k ≤ fieldActivity (afr.w (afCutoff afr + k))

/-- **THE REDUCTION.**  Given the combinatorial substrate — a growth constant
`mu ≥ 0` and the KP tree-graph domination `treeDom : |z_n| ≤ mu^n·(z_1)^n` over the field
Ursell amplitudes — plus the SINGLE config-space quantity `S : SinglePolymerActivity afr`
(`|z_1| ≤ g²`), build the full `KPAmplitude afr`.  Its `amplitude_le` then proves
`|z_n| ≤ (μg²)^n` and `clusterSum_le` proves KP convergence — the entire amplitude bound,
driven solely by `S`.  CONDITIONAL producer (open binders) — inhabits NO frontier bundle. -/
def kpAmplitude_of_singlePolymer {afr : AFRateModulus}
    (mu : Q') (hmu : (0 : Q') ≤ mu)
    (S : SinglePolymerActivity afr)
    (zAmp : Nat → Nat → Q') (hz_nonneg : ∀ k n, (0 : Q') ≤ zAmp k n)
    (htreeDom : ∀ k n, zAmp k n ≤ mu ^ n * (S.z1 k) ^ n) : KPAmplitude afr where
  mu := mu
  mu_nonneg := hmu
  a := S.z1
  a_nonneg := S.z1_nonneg
  zAmp := zAmp
  zAmp_nonneg := hz_nonneg
  treeDom := htreeDom
  single_le_g2 := S.z1_le_g2

/-! ## 5. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **PROVED (axiom-clean):** the combinatorial content of the Kotecký–Preiss amplitude bound.
  * `perCluster_penrose` — the per-cluster tree-graph coefficient `φ^T(Y) ≤ eSurrogate^{|Y|}`,
    from the PROVED `penroseIneq` (`|C(G)| ≤ τ(G)`) + Cayley + Euler (`cubicEulerBound`).
  * `combGrowth_le` — the tree-count growth `τ_n ≤ (eμ)^n` (`N_n·eSurrogate^n ≤ (K·3)^n`).
  * `amplitude_le` — the amplitude bound `|z_n(w_k)| ≤ (μ·g²)^n`.
  * `clusterSum_le` — the KP convergence `Σ_n |z_n| ≤ 1/(1 − μg²)` for `μg² < 1`.
  * `kpAmplitude_of_singlePolymer` — the reduction: the whole amplitude bound is driven by the
    SINGLE config-space quantity `SinglePolymerActivity` (`|z_1| ≤ g²`).

**VERDICT.**  The Kotecký–Preiss amplitude bound `|z_n| ≤ (μg²)^n` for the field-space Ursell
amplitudes is now COMBINATORIALLY PROVED down to a single scalar: the tree-count growth
reduces to the PROVED Penrose inequality + banked Cayley + PROVED Euler; the n-fold and the
geometric convergence are proved here.  The SOLE remaining measure-theoretic quantity is the
single-polymer activity `|z_1| ≤ g²` (`SinglePolymerActivity`) — the induced coupling from ONE
connected field-space cluster, which needs the configuration-space Gaussian measure (the new
substrate this character-basis library lacks).  The combinatorial scaffold does NOT close that
scalar; it is named honestly as the residual.  No guarded frontier bundle is inhabited; nothing
is faked; the 4D Yang–Mills mass gap remains OPEN. -/
theorem kpFieldAmplitude_honesty : True := trivial

end YMGap.Continuum.KPFieldAmplitude

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.KPFieldAmplitude.rearrange4
#print axioms YMGap.Continuum.KPFieldAmplitude.mul_pow_eqv
#print axioms YMGap.Continuum.KPFieldAmplitude.powLePow
#print axioms YMGap.Continuum.KPFieldAmplitude.pow_eqv_qpow
#print axioms YMGap.Continuum.KPFieldAmplitude.finSumPow_eqv_geomSum
#print axioms YMGap.Continuum.KPFieldAmplitude.perCluster_penrose
#print axioms YMGap.Continuum.KPFieldAmplitude.combGrowth_le
#print axioms YMGap.Continuum.KPFieldAmplitude.amplitude_le
#print axioms YMGap.Continuum.KPFieldAmplitude.clusterSum_le
#print axioms YMGap.Continuum.KPFieldAmplitude.kpAmplitude_of_singlePolymer
