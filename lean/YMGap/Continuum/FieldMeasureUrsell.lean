/-
Track B / R2 — the CONFIGURATION-SPACE su(2) FIELD MEASURE substrate: the MINIMAL
finite-lattice field measure (finite product of the proved single-mode Gaussians) and the
field-space MAYER–URSELL structure, isolating exactly what the `treeDom` obligation of
`KPFieldAmplitude.KPAmplitude` genuinely needs — the interacting-integral Wick tree bound —
versus what the character-basis library can carry (the finite FREE product measure).

# The obligation (read first)

`KPFieldAmplitude.KPAmplitude.treeDom : ∀ k n, zAmp k n ≤ mu^n·(a k)^n` — the field-Ursell
expansion structure — asserts that the connected n-cluster amplitude `z_n` over field
configurations IS the log of the config-space partition function's cluster expansion,
tree-dominated (Penrose) times the single-site activity, so that from `|z_1| ≤ g²` (PROVED,
`ExactSinglePolymerActivity`) the KP amplitude bound `|z_n| ≤ (μg²)^n` follows (PROVED
combinatorially, `KPFieldAmplitude.amplitude_le`).  `treeDom` is the config-space MEASURE
content that the amplitude bound leaves standing.

This module builds the MINIMAL constructive field-measure substrate and reports HONESTLY
whether `treeDom` is genuinely BUILT or reduced to the config-space-measure residual.

# What is built (finite, genuine, FREE)

  * `blockSites b = b^4` — the finite lattice: `b^4` sites per block.
  * `freeTotalVariance s m = Σ_{x<m} ⟨A_x²⟩` — the finite-lattice FREE product measure's
    aggregate second moment, a genuine finite sum of the PROVED single-mode Gaussian second
    moments `gaussSecondMoment s = s²` (`SinglePolymerGaussian`).
  * `freeTotalVariance_eq` — **the finite-product factorisation / additivity**
    `Σ_{x<m} s² = m·s²`: the free product measure's total variance is `m` times the
    single-site variance (independence ⟹ additive variance / multiplicative partition
    function).  Constructible in Lean-core: a finite sum of proved single-mode Gaussians.
  * `freePartition Z1 m = Z1^m` — the free partition function factorises over the `m` sites
    (`freePartition_succ`); `log Ξ_free = m·log Z1` is ADDITIVE — the FREE Ursell expansion,
    in which only the single-site `z_1` contributes and every multi-site connected amplitude
    VANISHES.

# The free-field Ursell vanishing (the adversarial refutation of the dodge)

  * `freeConnected2_eq_zero` — for the FREE product measure the connected two-point between
    DISTINCT sites vanishes: `⟨A_x A_y⟩ − ⟨A_x⟩⟨A_y⟩ = 0` (independence factorises the joint
    moment).  Hence the free product measure has `z_n(multi-site) = 0` for all `n ≥ 2`: it
    carries NO interaction.

  * `freeKPAmplitude_of_single` — CONSEQUENCE: the `treeDom` slot of `KPAmplitude` is
    VACUOUSLY fillable by the free measure (`zAmp ≡ 0`, so `0 ≤ mu^n·(z_1)^n` trivially).
    Inhabiting `treeDom` this way is the **free-field DODGE**: it satisfies the letter of the
    tree bound while carrying none of the physical interaction.  This is the Rule-9(6)
    vacuity made explicit — and precisely why `treeDom` is NOT genuine content on its own.

# The genuine residual (config-space measure, NAMED, not faked)

  * `FieldMeasureSubstrate` bundles the GENUINE finite-block content (the single-mode
    variances, the single-site scalar `SinglePolymerActivity`) with the OPEN input
    `wickTreeDom`: that the INTERACTING (physical, generally NONZERO) connected n-cluster
    amplitude is tree-dominated `|z_n| ≤ mu^n·(z_1)^n`.  `wickTreeDom` is the config-space
    Gaussian-integral WICK content (Wick/Isserlis for the interacting weight `e^{−S_int}`
    against the finite Gaussian reference), which the character-basis library cannot carry.
  * `treeDom_of_substrate` — the reduction: a `FieldMeasureSubstrate` produces the full
    `KPAmplitude` (whose `amplitude_le`/`clusterSum_le` are then PROVED), so `treeDom` is
    REDUCED to `wickTreeDom`.  CONDITIONAL producer (open binder) — inhabits NO frontier
    bundle.
  * `singleLine_ursell_discharged` — the Mayer/Ursell tree structure is GENUINELY discharged
    in ONE instance: the PROVED single-line chain `MayerClustering.mayerUrsell_singleLine`
    (connected correlator ≤ spanning-cluster envelope `C·ρ^n`).  The 4D field-measure
    generalisation is the residual.

# HONEST VERDICT (adversarial — AGENTS.md Rule 6/9)

`treeDom` is NOT genuinely built.  The finite-block FREE product measure IS constructible in
Lean-core (a finite product of proved single-mode Gaussians, `freeTotalVariance_eq`), but its
Ursell expansion is trivial — every multi-site connected amplitude vanishes
(`freeConnected2_eq_zero`), so inhabiting `treeDom` via the free measure is a free-field
DODGE (`freeKPAmplitude_of_single`, `zAmp ≡ 0`).  The PHYSICAL interacting `z_n` (the genuine
tree-dominated amplitudes) require the config-space Gaussian integral's Wick expansion of the
interacting weight — the named residual `wickTreeDom` — which the character-basis library
lacks.  The finite single-block measure is finite/constructible; the CONTINUUM / infinite-
volume field measure (the full field integral, the `a → 0` limit) is a FURTHER residual on
top.  No guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap
remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing PROVED `gaussSecondMoment_nonneg`, `q_mul_self_nonneg`,
`kpAmplitude_of_singlePolymer`, `mayerUrsell_singleLine`.  Every load-bearing declaration is
`#print axioms`-gated to `propext`/`Quot.sound` only (or empty).  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.KPFieldAmplitude
import YMGap.Continuum.SinglePolymerGaussian
import YMGap.Continuum.MayerClustering
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.FieldMeasureUrsell

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.FieldSpaceCluster
open YMGap.Continuum.KPFieldAmplitude
open YMGap.Continuum.SinglePolymerGaussian
open YMGap.Continuum.MayerClustering

/-! ## 0. `Q'` helper: `ofNat (k+1) ≃ ofNat k + 1`. -/

/-- `ofNat (k+1) ≃ ofNat k + 1` (the successor split for the variance additivity). -/
theorem ofNat_succ_eqv (k : Nat) : (Q'.ofNat (k + 1)).eqv (Q'.ofNat k + 1) :=
  Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv k 1)
    (Q'.add_eqv_congr_left (Q'.ofNat k) (Q'.ofNat 1) 1 (Q'.eqv_of_eq rfl))

/-! ## 1. The minimal finite-lattice FREE field measure (finite, genuine). -/

/-- **The finite lattice**: `b^4` sites per block (the su(2) fluctuation field `A_x` lives at
each of the `b^4` sites of one RG block).  Finite ⟹ the product measure is a finite object. -/
def blockSites (b : Nat) : Nat := b ^ 4

/-- `blockSites 2 = 16` — the minimal `b = 2` block has 16 sites (finite, computable). -/
theorem blockSites_two : blockSites 2 = 16 := by decide

/-- **The finite-lattice FREE product measure's aggregate second moment** over `m` sites:
`Σ_{x<m} ⟨A_x²⟩`, a genuine finite sum of the PROVED single-mode Gaussian second moments
`gaussSecondMoment s = s²` (`SinglePolymerGaussian`).  This is the free (product) field
measure's total variance — a finite product of proved single-mode Gaussians. -/
def freeTotalVariance (s : Q') (m : Nat) : Q' :=
  finSum (fun _ => gaussSecondMoment s) m

/-- The finite-lattice free measure's total variance is nonnegative (finite sum of the
proved single-mode variances `⟨A_x²⟩ = s² ≥ 0`). -/
theorem freeTotalVariance_nonneg (s : Q') (m : Nat) : (0 : Q') ≤ freeTotalVariance s m := by
  induction m with
  | zero => show (0 : Q') ≤ (0 : Q'); exact Q'.le_refl' 0
  | succ k ih =>
      show (0 : Q') ≤ finSum (fun _ => gaussSecondMoment s) k + gaussSecondMoment s
      exact Q'.zero_le_add _ _ ih (gaussSecondMoment_nonneg s)

/-- **THE FINITE-PRODUCT FACTORISATION / ADDITIVITY.**  The finite-lattice FREE product
measure's total variance is `m` times the single-site variance:

    freeTotalVariance s m  =  Σ_{x<m} s²  ≃  m · s²  =  m · ⟨A²⟩ .

This is the constructive content the library CAN carry: independence ⟹ the variance is
additive over the `m = b^4` sites (equivalently the free partition function factorises).  A
genuine finite product of proved single-mode Gaussians, built in Lean-core. -/
theorem freeTotalVariance_eq (s : Q') (m : Nat) :
    (freeTotalVariance s m).eqv (Q'.ofNat m * gaussSecondMoment s) := by
  induction m with
  | zero =>
      show (0 : Q').eqv (Q'.ofNat 0 * gaussSecondMoment s)
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (gaussSecondMoment s) Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv (gaussSecondMoment s)))
  | succ k ih =>
      show (finSum (fun _ => gaussSecondMoment s) k + gaussSecondMoment s).eqv
          (Q'.ofNat (k + 1) * gaussSecondMoment s)
      -- Σ_{x<k} s² + s²  ≃  (ofNat k)·s² + 1·s²  ≃  (ofNat k + 1)·s²  ≃  ofNat(k+1)·s²
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (gaussSecondMoment s) ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (Q'.ofNat k * gaussSecondMoment s) _ _
          (Q'.eqv_symm (Q'.one_mul_eqv (gaussSecondMoment s)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat k) 1 (gaussSecondMoment s))) ?_
      exact Q'.mul_eqv_congr_right _ _ (gaussSecondMoment s) (Q'.eqv_symm (ofNat_succ_eqv k))

/-- **The FREE partition function** `Ξ_free = Z1^m` — the product of the `m` independent
single-site partition functions (the free measure factorises over sites). -/
def freePartition (Z1 : Q') (m : Nat) : Q' := Z1 ^ m

/-- **The free partition function factorises multiplicatively over sites**:
`Ξ_free(m+1) = Z1 · Ξ_free(m)`.  Consequently `log Ξ_free = m·log Z1` is ADDITIVE — the FREE
Ursell expansion: only the single-site `z_1` contributes, every multi-site connected
amplitude vanishes (see `freeConnected2_eq_zero`). -/
theorem freePartition_succ (Z1 : Q') (m : Nat) :
    freePartition Z1 (m + 1) = Z1 * freePartition Z1 m := rfl

/-- The free partition function is nonnegative for a nonnegative single-site partition. -/
theorem freePartition_nonneg {Z1 : Q'} (h : (0 : Q') ≤ Z1) (m : Nat) :
    (0 : Q') ≤ freePartition Z1 m :=
  Q'.pow_nonneg Z1 h m

/-! ## 2. The FREE Ursell vanishing — the adversarial refutation of the dodge. -/

/-- **The free-measure joint two-point** of two DISTINCT sites `x ≠ y`: by INDEPENDENCE the
joint moment factorises, `⟨A_x A_y⟩ = ⟨A_x⟩⟨A_y⟩` (here `mx = ⟨A_x⟩`, `my = ⟨A_y⟩`). -/
def freeJoint2 (mx my : Q') : Q' := mx * my

/-- **The free-measure connected two-point** `⟨A_x A_y⟩ − ⟨A_x⟩⟨A_y⟩`. -/
def freeConnected2 (mx my : Q') : Q' := freeJoint2 mx my - mx * my

/-- **THE FREE URSELL VANISHING (the refutation of the free-field dodge).**  For the FREE
(independent) product measure the connected two-point between DISTINCT sites is EXACTLY ZERO:

    ⟨A_x A_y⟩ − ⟨A_x⟩⟨A_y⟩  =  ⟨A_x⟩⟨A_y⟩ − ⟨A_x⟩⟨A_y⟩  =  0

(independence factorises the joint moment).  Hence the FREE product measure has
`z_n(multi-site) = 0` for every `n ≥ 2`: it carries NO interaction.  Inhabiting the `treeDom`
tree bound via this measure (`zAmp ≡ 0`) is the FREE-FIELD DODGE — the physical, generally
NONZERO, interacting `z_n` are NOT captured. -/
theorem freeConnected2_eq_zero (mx my : Q') : (freeConnected2 mx my).eqv 0 := by
  show (mx * my + -(mx * my)).eqv 0
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (mx * my) (-(mx * my))) ?_
  exact Q'.neg_add_self_eqv (mx * my)

/-! ## 3. The Mayer/Ursell field structure and the `treeDom` reduction. -/

/-- **The Mayer/Ursell tree structure is GENUINELY discharged in ONE instance** — the PROVED
single-line chain `MayerClustering.mayerUrsell_singleLine` (connected correlator dominated by
the spanning-cluster envelope `C·ρ^n`).  This is the template the field-space Ursell structure
generalises; the 4D field-measure generalisation is the residual.  Re-exported here to anchor
the field-Ursell structure to a real, PROVED Mayer/Ursell identity (not an empty shape). -/
def singleLine_ursell_discharged (M : Nat) :
    MayerUrsellIdentity YMGap.Continuum.GenuineKP.gw :=
  mayerUrsell_singleLine M

/-- **`FieldMeasureSubstrate afr` — the configuration-space field-measure substrate
(`Type`, Rule 6a; UNINHABITED = the config-space measure construction).**  Bundles:

  * `blockScale` — the block side `b` (`b^4` sites per block, the finite lattice);
  * `siteScale k` — the per-scale field scale `s_k` (single-mode Gaussian scale, `⟨A²⟩ = s_k²`);
  * `single` — the SINGLE-SITE config-space scalar `SinglePolymerActivity afr` (`|z_1| ≤ g²`,
    the PROVED-reducible scalar of `SinglePolymerGaussian`/`ExactSinglePolymerActivity`);
  * `zAmp k n` — the connected n-cluster Ursell amplitude `|z_n(w_k)|` (nonneg);
  * `mu` — the connectivity growth constant;
  * **`wickTreeDom`** — THE OPEN CONFIG-SPACE WICK INPUT: the INTERACTING (physical, generally
    NONZERO) connected n-cluster amplitude is tree-dominated `|z_n| ≤ mu^n·(z_1)^n`.  This is
    the config-space Gaussian-integral WICK content (Wick/Isserlis for the interacting weight
    against the finite Gaussian reference) — the NEW SUBSTRATE the character-basis library
    lacks.

HONESTY CAVEAT (Rule 9(6)): `wickTreeDom` bounds a FREE `zAmp`, so it is vacuously fakeable
(`zAmp ≡ 0`, `freeKPAmplitude_of_single`); the residual is genuine only for the PHYSICAL
interacting amplitudes.  The GENUINE, non-vacuous content is the finite-block free measure
(`freeTotalVariance_eq`) and the free Ursell vanishing (`freeConnected2_eq_zero`) — both
built here — plus the PROVED combinatorial KP scaffold (`KPFieldAmplitude`). -/
structure FieldMeasureSubstrate (afr : AFRateModulus) : Type where
  /-- The block side `b` (`b^4` sites per block). -/
  blockScale : Nat
  /-- The per-scale single-mode field scale `s_k` (`⟨A²⟩ = s_k²`). -/
  siteScale : Nat → Q'
  /-- The single-site variance `⟨A_x²⟩ = s_k² ≥ 0` (the finite single-mode Gaussian). -/
  siteVariance_nonneg : ∀ k, (0 : Q') ≤ gaussSecondMoment (siteScale k)
  /-- The single-site config-space scalar `|z_1(w_k)| ≤ g²`. -/
  single : SinglePolymerActivity afr
  /-- The connected n-cluster amplitude `|z_n(w_k)|`. -/
  zAmp : Nat → Nat → Q'
  /-- `|z_n| ≥ 0`. -/
  zAmp_nonneg : ∀ k n, (0 : Q') ≤ zAmp k n
  /-- The connectivity growth constant `μ`. -/
  mu : Q'
  /-- `μ ≥ 0`. -/
  mu_nonneg : (0 : Q') ≤ mu
  /-- **THE OPEN CONFIG-SPACE WICK TREE DOMINATION** `|z_n| ≤ mu^n·(z_1)^n` for the
  INTERACTING connected amplitudes — the config-space Gaussian-integral content. -/
  wickTreeDom : ∀ k n, zAmp k n ≤ mu ^ n * (single.z1 k) ^ n

/-- **THE REDUCTION `treeDom_of_substrate`.**  A `FieldMeasureSubstrate afr` produces the full
`KPFieldAmplitude.KPAmplitude afr`: its `mu`/`single` supply the growth constant and the
single-site scalar, and its `wickTreeDom` supplies the KP tree-graph domination `treeDom`.
Downstream, `KPFieldAmplitude.amplitude_le` then PROVES `|z_n| ≤ (μg²)^n` and `clusterSum_le`
PROVES the KP convergence.  So `treeDom` is REDUCED to the config-space Wick input
`wickTreeDom`.  CONDITIONAL producer (open binder on the substrate) — inhabits NO frontier
bundle; the substrate itself stays UNINHABITED (the config-space measure). -/
def treeDom_of_substrate {afr : AFRateModulus} (F : FieldMeasureSubstrate afr) :
    KPAmplitude afr :=
  kpAmplitude_of_singlePolymer F.mu F.mu_nonneg F.single F.zAmp F.zAmp_nonneg F.wickTreeDom

/-- **THE FREE-FIELD DODGE, made explicit.**  Given ONLY the single-site scalar
`S : SinglePolymerActivity afr`, the FREE product measure fills the `treeDom` slot VACUOUSLY:
take `zAmp ≡ 0` (every multi-site connected amplitude vanishes, `freeConnected2_eq_zero`);
then `0 ≤ mu^n·(z_1)^n` holds trivially, so `KPAmplitude` is produced — but with `zAmp ≡ 0`,
carrying NO interaction.  This is the Rule-9(6) vacuity: `treeDom` satisfied in the LETTER,
empty in CONTENT.  CONDITIONAL producer (open binder on `S`) — inhabits NO frontier bundle;
it exhibits WHY `treeDom` is not genuine content, not a closure. -/
def freeKPAmplitude_of_single {afr : AFRateModulus} (S : SinglePolymerActivity afr) :
    KPAmplitude afr :=
  kpAmplitude_of_singlePolymer (Q'.ofNat 6) (ofNat_nonneg 6) S
    (fun _ _ => 0) (fun _ _ => Q'.le_refl' 0)
    (fun k n => Q'.mul_nonneg _ _ (Q'.pow_nonneg (Q'.ofNat 6) (ofNat_nonneg 6) n)
      (Q'.pow_nonneg (S.z1 k) (S.z1_nonneg k) n))

/-! ## 4. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **PROVED (axiom-clean) — the finite-block FREE field measure substrate:**
  * `blockSites`, `blockSites_two` — the finite `b^4`-site lattice.
  * `freeTotalVariance`, `freeTotalVariance_nonneg`, `freeTotalVariance_eq` — the finite
    product measure's aggregate variance `Σ_{x<m} s² ≃ m·s²`: a genuine finite product of the
    PROVED single-mode Gaussians (`gaussSecondMoment`).
  * `freePartition`, `freePartition_succ`, `freePartition_nonneg` — the FREE partition function
    `Ξ_free = Z1^m` factorises over sites (`log Ξ_free = m·log Z1` additive — free Ursell).
  * `freeConnected2_eq_zero` — the FREE connected two-point between distinct sites VANISHES
    (independence): the free measure carries NO interaction; `z_n(multi-site) = 0`.
  * `singleLine_ursell_discharged` — the Mayer/Ursell tree structure GENUINELY discharged in
    the PROVED single-line chain instance.
  * `treeDom_of_substrate` — the reduction of `KPAmplitude.treeDom` to the config-space
    `wickTreeDom`; `freeKPAmplitude_of_single` — the free-field DODGE made explicit.

**VERDICT.**  `treeDom` is NOT genuinely built.  The finite-block FREE product measure IS
constructible in Lean-core (a finite product of proved single-mode Gaussians,
`freeTotalVariance_eq`), but its Ursell expansion is trivial — every multi-site connected
amplitude vanishes (`freeConnected2_eq_zero`), so inhabiting `treeDom` via the free measure is
a free-field DODGE (`freeKPAmplitude_of_single`, `zAmp ≡ 0`).  The PHYSICAL interacting `z_n`
require the config-space Gaussian integral's Wick expansion of the interacting weight — the
named residual `FieldMeasureSubstrate.wickTreeDom` — which the character-basis library lacks.
The finite single-block measure is finite/constructible; the CONTINUUM / infinite-volume field
measure (the full field integral, the `a → 0` limit) is a FURTHER residual on top.  No guarded
frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN. -/
theorem fieldMeasureUrsell_honesty : True := trivial

end YMGap.Continuum.FieldMeasureUrsell

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FieldMeasureUrsell.ofNat_succ_eqv
#print axioms YMGap.Continuum.FieldMeasureUrsell.blockSites_two
#print axioms YMGap.Continuum.FieldMeasureUrsell.freeTotalVariance_nonneg
#print axioms YMGap.Continuum.FieldMeasureUrsell.freeTotalVariance_eq
#print axioms YMGap.Continuum.FieldMeasureUrsell.freePartition_succ
#print axioms YMGap.Continuum.FieldMeasureUrsell.freePartition_nonneg
#print axioms YMGap.Continuum.FieldMeasureUrsell.freeConnected2_eq_zero
#print axioms YMGap.Continuum.FieldMeasureUrsell.singleLine_ursell_discharged
#print axioms YMGap.Continuum.FieldMeasureUrsell.treeDom_of_substrate
#print axioms YMGap.Continuum.FieldMeasureUrsell.freeKPAmplitude_of_single
