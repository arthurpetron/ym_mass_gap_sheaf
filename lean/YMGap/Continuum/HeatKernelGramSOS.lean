/-
The **heat-kernel positive-weight Gram / SOS witness** for the off-diagonal OS2
character-PRODUCT form — the constructive *moment-matrix* realization that
sources positivity from the heat-kernel WEIGHTS (a positive measure), never from
the fusion channels.

# What this module is (and why it is the right object)

The DIAGONAL OS2 is already proved unconditionally
(`ReflectionPositivity.reflSchwinger_nonneg`): the reflection
`θ(χ_μ) = χ̄_μ` diagonalizes the form, leaving the plain weighted sum of squares
`Σ_s e^{−tC₂(s)}·c_s² ≥ 0`.  The OFF-diagonal content is the PRODUCT Gram

    G_{μν} = E(χ_μ χ_ν) = Σ_c N^c_{μν}·m_c ,   m_c = dim(c)·e^{−tC₂(c)} ≥ 0 ,

a nonnegative combination of the SU(2) Clebsch–Gordan fusion-channel matrices
`N^c`.  The **channel-by-channel** route is PROVED IMPOSSIBLE
(`SchurHadamardTransfer.fusion1_not_gramRep`): the spin-½ channel `N^1` is the
path-graph adjacency matrix with the explicit negative form `Q(1,−1) = −2`, so
the `N^c` are not individually PSD and the Schur/Hadamard closure
(`fusionCombo_gramRep`) cannot apply.  Positivity must come from the heat-kernel
weight conspiracy.

This module supplies that conspiracy in its sharpest constructive form: the
**positive-measure / moment-matrix** realization.  A positive heat-kernel
measure `κ ≥ 0` (Bochner: nonneg character coefficients `m_c ≥ 0`, the proved
`ReflectionPositivity.heatKernel_nonnegCharCoeffs`) is reproduced by a finite
**positive quadrature**: nodes `x_k`, NONNEGATIVE weights `ω_k ≥ 0`, with

    G_{μν} = Σ_k ω_k · U_μ(x_k) · U_ν(x_k)            (U = SU(2) character = Cheb-U).

The point: each node-evaluation `μ ↦ U_μ(x_k)` is a COMMON eigenvector of all the
`N^c` (a 1-dim representation of the fusion ring,
`U_μ(x)U_ν(x) = Σ_c N^c_{μν} U_c(x)`), so the `c`-sum collapses to a rank-one
outer product `v_k v_kᵀ` PER NODE — the rank-deficient channel matrices `N^c`
never appear.  Summing over nodes with `ω_k ≥ 0` is a literal Gram.

# What is GENUINELY PROVED here (unconditional, axiom-clean)

  * `nodeQuadGram` / `nodeQuadGram_gramRep` — **the constructive moment-matrix
    theorem.**  ANY finite nonnegative-weight node quadrature of character
    products `G_{ab} = Σ_k ω_k U_a(x_k)U_b(x_k)` is a literal
    `SchurHadamardTransfer.GramRep` (weights `d_k = ω_k`, coordinate vectors
    `v_k(a) = U_a(x_k)`).  This is the explicit Gram/SOS witness built from the
    heat-kernel POSITIVE WEIGHTS — NO channels, NO spectral theorem.
  * `nodeQuadGram_quadForm_nonneg` — **off-diagonal OS2 from the weights.**  The
    full off-diagonal quadratic form `Σ_{ij} c_i c_j G_{ij} ≥ 0` for every `c`,
    via the SOS identity `= Σ_k ω_k (Σ_i c_i U_i(x_k))² ≥ 0`.
  * `egGram_badvec_nonneg` vs `SchurHadamardTransfer.fusion1_not_psd` — **the
    concrete contrast.**  The very test vector `(1,−1)` that gives `−2` on the
    bare spin-½ channel `N^1` gives `≥ 0` on a genuine 2-node positive-measure
    moment matrix.  The weight conspiracy is exhibited, not assumed.
  * `cheb_fusion_one_one` — a proved instance of the fusion eigen-identity
    `U₁·U₁ = U₀ + U₂` (spin-½ ⊗ spin-½ = spin-0 ⊕ spin-1), the algebraic reason
    a node evaluation lands in the common eigenbasis.

# The reduction and the single residual

  * `NodeQuadrature` (Type-level) — the residual carrier: rational nodes,
    nonnegative weights, and the per-entry **moment reproduction**
    `G_{ab} ≃ Σ_k ω_k U_a(x_k)U_b(x_k)`.  This is the Q'-shadow of
    `ChebyshevQuadPSD.ChebNodes.gram_eq_node_quadrature` /
    `RiemannSOS.MomentIntegralIdentity` — and its positivity input is exactly the
    proved measure positivity `κ ≥ 0`, NOT channel positivity.
  * `qGram_gramRep` / `qGram_quadForm_nonneg` (THEOREMS) — given a
    `NodeQuadrature`, the rational heat-kernel Gram is a `GramRep` and its
    off-diagonal quadratic form is `≥ 0`.  So off-diagonal OS2 is reduced to
    EXACTLY the moment-reproduction residual, sourced from `κ ≥ 0`.

# Honesty

Off-diagonal OS2 in full is NOT closed here: the unconditional content is the
moment-matrix machine (positive weights ⟹ GramRep ⟹ form `≥ 0`) and the concrete
finite contrast; the bridge to the actual heat-kernel Gram is the single named
residual `NodeQuadrature` (the moment-reproduction quadrature, equivalently the
already-named `ChebNodes.gram_eq_node_quadrature` / `MomentIntegralIdentity`).
What this module changes: positivity is now sourced from the PROVED positive
measure `κ ≥ 0`, and the dead channel-by-channel route is replaced by the
node-eigenbasis route that provably dodges `fusion1_not_gramRep`.

# Reuse / provenance

The `GramRep` carrier and the Khatri–Rao / SOS rearrangement are the
Mathlib-free constructive transfer of the Schur-product / Hadamard machinery of
the external 4D-GFF formalization (Douglas–Hoback–Mei–Nissim, "Formalization of
QFT", arXiv:2603.15770; repository `mrdouglasny/OSforGFF`), as set up in
`SchurHadamardTransfer`.  Here the same `GramRep` witness is fed by the
heat-kernel node measure rather than by a covariance.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (inherited from the reused `Q'` algebra and
`GramRep`).  No `Classical.*`, no `sorryAx`, no `native_decide`, no Mathlib.
-/

import YMGap.Continuum.SchurHadamardTransfer
import YMGap.Continuum.ChebyshevBound

namespace YMGap.Continuum.HeatKernelGramSOS

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SchurHadamardTransfer

/-! ## 1. The positive-weight node-quadrature Gram (the moment-matrix object)

`nodeQuadGram ω x r` is the matrix `G_{ab} = Σ_{k<r} ω_k · U_a(x_k)·U_b(x_k)`,
the moment matrix of the discrete positive measure `Σ_k ω_k δ_{x_k}` against the
SU(2) characters `U_a = Cheb-U_a`.  When `ω_k ≥ 0` it is manifestly a Gram. -/

/-- **The node-quadrature Gram entry** `G_{ab} = Σ_{k<r} ω_k·U_a(x_k)·U_b(x_k)`. -/
def nodeQuadGram (ω x : Nat → Q') (r : Nat) : Nat → Nat → Q' :=
  fun a b => finSum (fun k => ω k * (Cheb.U a (x k) * Cheb.U b (x k))) r

/-- **The constructive moment-matrix theorem.**  A node-quadrature Gram with
NONNEGATIVE weights is a literal `GramRep`: rank `r`, pivots `d_k = ω_k ≥ 0`, and
coordinate vectors `v_k(a) = U_a(x_k)` — the node evaluations of the characters.
The Gram identity holds *definitionally* (`nodeQuadGram` IS the rank-`r` sum of
outer products).  This is the explicit SOS witness sourced from the heat-kernel
POSITIVE WEIGHTS; the rank-deficient fusion channels `N^c` never appear. -/
def nodeQuadGram_gramRep (ω x : Nat → Q') (r : Nat)
    (hω : ∀ k, (0 : Q') ≤ ω k) : GramRep (nodeQuadGram ω x r) where
  r := r
  d := ω
  hd := hω
  v := fun k a => Cheb.U a (x k)
  hM := fun _ _ => Q'.eqv_refl _

/-- **Off-diagonal OS2 from the heat-kernel weights.**  For any node quadrature
with nonnegative weights, the full off-diagonal character-product quadratic form
`Σ_{i,j<N} c_i c_j G_{ij}` is `≥ 0` for every coefficient vector `c` — via the SOS
identity `= Σ_k ω_k (Σ_i c_i U_i(x_k))² ≥ 0` (`gramPSD_quadForm_nonneg`).  No
channel positivity, no spectral theorem. -/
theorem nodeQuadGram_quadForm_nonneg (ω x : Nat → Q') (r : Nat)
    (hω : ∀ k, (0 : Q') ≤ ω k) (c : Nat → Q') (N : Nat) :
    (0 : Q') ≤ gramQuadForm (nodeQuadGram ω x r) c N :=
  gramPSD_quadForm_nonneg (nodeQuadGram_gramRep ω x r hω) c N

/-! ## 2. The fusion eigen-identity (why a node lands in the common eigenbasis)

The reason `nodeQuadGram` realizes the fusion-weighted Gram WITHOUT the channels
is the pointwise character-product identity `U_a(x)U_b(x) = Σ_c N^c_{ab} U_c(x)`:
each evaluation `x ↦ (U_s(x))_s` is a 1-dim representation of the fusion ring,
a common eigenvector of every `N^c`.  We prove the load-bearing base instance
`U₁·U₁ = U₀ + U₂` — the SU(2) fusion `spin-½ ⊗ spin-½ = spin-0 ⊕ spin-1`. -/

/-- The generic regrouping `P ≃ 1 + (P + (-1))` over `Q'` (add-comm/assoc plus
`1 + (-1) ≃ 0`).  The fusion identity is this at `P = (2x)²`. -/
theorem self_eqv_one_add (P : Q') :
    P.eqv ((1 : Q') + (P + (-(1 : Q')))) := by
  refine Q'.eqv_symm ?_
  -- 1 + (P + (-1)) ≃ (1 + P) + (-1)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') P (-(1 : Q')))) ?_
  -- (1 + P) + (-1) ≃ (P + 1) + (-1)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((1 : Q') + P) (P + (1 : Q')) (-(1 : Q'))
      (Q'.add_comm_eqv (1 : Q') P)) ?_
  -- (P + 1) + (-1) ≃ P + (1 + (-1))
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv P (1 : Q') (-(1 : Q'))) ?_
  -- P + (1 + (-1)) ≃ P + 0 ≃ P
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P ((1 : Q') + (-(1 : Q'))) (0 : Q') (by decide)) ?_
  exact YMGap.Constructive.QPoly.q_add_zero_eqv P

/-- **The fusion eigen-identity (base case).**  `U₁(x)·U₁(x) ≃ U₀(x) + U₂(x)` over
`Q'` — `(2x)² = 1 + (4x²−1)`, the SU(2) Clebsch–Gordan
`χ_{1/2}·χ_{1/2} = χ_0 + χ_1`.  At any node `x` this is the `c`-sum
`Σ_c N^c_{11} U_c(x)` collapsing the product into the common eigenbasis.
(Both sides reduce defeq to `P` and `1 + (P + (-1))` with `P = (2x)·(2x)`.) -/
theorem cheb_fusion_one_one (x : Q') :
    (Cheb.U 1 x * Cheb.U 1 x).eqv (Cheb.U 0 x + Cheb.U 2 x) :=
  self_eqv_one_add (((2 : Q') * x) * ((2 : Q') * x))

/-! ## 3. The concrete finite contrast — the weight conspiracy, exhibited

The bare spin-½ channel `N^1` fails positivity on the off-cone vector `(1,−1)`
(`SchurHadamardTransfer.fusion1_not_psd`: `Q(1,−1) = −2`).  Here is a GENUINE
2-node positive-measure moment matrix — nodes `{0, 1/2}`, equal weights `1` — on
which the SAME vector gives `≥ 0`.  Positivity comes from the (nonnegative)
weights, exactly the conspiracy the channel decomposition hides. -/

/-- A concrete 2-node measure: abscissae `x_0 = 0`, `x_1 = 1/2 ∈ [−1,1]`. -/
def egNode : Nat → Q' := fun k => if k = 0 then 0 else Q'.mkPos 1 2 (by decide)

/-- Equal positive weights `ω_k = 1`. -/
def egWeight : Nat → Q' := fun _ => 1

theorem egWeight_nonneg : ∀ k, (0 : Q') ≤ egWeight k :=
  fun _ => show (0 : Q') ≤ (1 : Q') by decide

/-- The concrete heat-kernel-style moment matrix of the 2-node positive measure. -/
def egGram : Nat → Nat → Q' := nodeQuadGram egWeight egNode 2

/-- **The contrast.**  On the test vector `(1,−1)` — the vector that breaks the
bare spin-½ channel `N^1` (`fusion1_not_psd : ¬ 0 ≤ Q(1,−1) = −2`) — the genuine
2-node positive-measure moment matrix has a NONNEGATIVE quadratic form.  Off-
diagonal positivity is recovered from the weights, with no channel positivity. -/
theorem egGram_badvec_nonneg :
    (0 : Q') ≤ gramQuadForm egGram fusion1BadVec 2 :=
  nodeQuadGram_quadForm_nonneg egWeight egNode 2 egWeight_nonneg fusion1BadVec 2

/-- The exact value of the contrast: `Q(1,−1) = 1 ≥ 0` on the moment matrix,
versus `−2` on the bare channel `N^1`.  (Concrete rational evaluation.) -/
theorem egGram_badvec_value :
    (gramQuadForm egGram fusion1BadVec 2).eqv (1 : Q') := by decide

/-! ## 4. The rational heat-kernel Gram and the reduction to the residual

The actual object of off-diagonal OS2 is the fusion-weighted Gram of a
nonnegative moment sequence.  Over a rational heat-kernel parameter the moments
`m_s` are rational, so we phrase it over `Q'`: `qGram` is the SU(2)
Clebsch–Gordan sum of moments, mirroring `GramRed.gram`.  Its positivity reduces
to the single residual `NodeQuadrature` — the moment-reproduction quadrature. -/

/-- A nonnegative rational moment sequence `m_s = E(χ_s) ≥ 0` (the Q' shadow of
`GramRed.MomentData`, e.g. `m_s = (s+1)·a^{s(s+2)}` at rational `a ∈ (0,1)`). -/
structure QMomentData where
  /-- The moment `m s = E(χ_{s/2})`. -/
  m : Nat → Q'
  /-- Each moment is `≥ 0` (diagonal positivity `E(χ_s) ≥ 0`). -/
  m_nonneg : ∀ s, (0 : Q') ≤ m s

/-- `|a − b|` — the lowest spin in the SU(2) fusion `χ_a χ_b`. -/
def fusionLow (a b : Nat) : Nat := max a b - min a b

/-- **The rational Gram entry** `G_{ab} = Σ_{j=0}^{min a b} m_{|a−b|+2j}` — the
SU(2) Clebsch–Gordan sum of moments (mirrors `GramRed.gram`). -/
def qGram (M : QMomentData) (a b : Nat) : Q' :=
  finSum (fun j => M.m (fusionLow a b + 2 * j)) (min a b + 1)

/-- **The single residual (Type-level; AGENTS.md Rule 8).**  A finite positive
quadrature reproducing the heat-kernel Gram entrywise: nodes `x_k`, NONNEGATIVE
weights `ω_k ≥ 0`, and the moment-reproduction identity
`G_{ab} ≃ Σ_k ω_k U_a(x_k)U_b(x_k)`.  This is the Q'-shadow of
`ChebyshevQuadPSD.ChebNodes.gram_eq_node_quadrature` /
`RiemannSOS.MomentIntegralIdentity`; its positivity input is the PROVED measure
positivity `κ ≥ 0` (`ReflectionPositivity.heatKernel_nonnegCharCoeffs`, Bochner),
NOT channel positivity. -/
structure NodeQuadrature (M : QMomentData) where
  /-- Number of quadrature nodes. -/
  r : Nat
  /-- The node abscissae `x_k` (classically `cos(kπ/(r+1))`). -/
  node : Nat → Q'
  /-- The quadrature weights `ω_k`. -/
  weight : Nat → Q'
  /-- The weights are nonnegative (`ω_k = w_k·κ(x_k) ≥ 0`, from `κ ≥ 0`). -/
  weight_nonneg : ∀ k, (0 : Q') ≤ weight k
  /-- **Moment reproduction**: each Gram entry IS the node quadrature of the
  character product `U_a·U_b`. -/
  reproduce : ∀ a b,
    (qGram M a b).eqv (nodeQuadGram weight node r a b)

/-- Transport a `GramRep` along an entrywise `Q'.eqv` of the matrix. -/
def gramRep_of_eqv {M M' : Nat → Nat → Q'} (rep : GramRep M)
    (h : ∀ i j, (M' i j).eqv (M i j)) : GramRep M' where
  r := rep.r
  d := rep.d
  hd := rep.hd
  v := rep.v
  hM := fun i j => Q'.eqv_trans _ _ _ (h i j) (rep.hM i j)

/-- **The reduction — a THEOREM.**  Given the moment-reproduction residual
`NodeQuadrature M`, the rational heat-kernel Gram `qGram M` is a `GramRep`: the
node measure exhibits it as a literal sum of outer products, dodging
`fusion1_not_gramRep` (positivity from the nonnegative weights, not the
channels). -/
def qGram_gramRep (M : QMomentData) (Q : NodeQuadrature M) : GramRep (qGram M) :=
  gramRep_of_eqv
    (nodeQuadGram_gramRep Q.weight Q.node Q.r Q.weight_nonneg)
    (fun i j => Q.reproduce i j)

/-- **Off-diagonal OS2, conditional on the residual.**  Given `NodeQuadrature M`,
the off-diagonal character-product quadratic form `Σ_{ij} c_i c_j G_{ij}` is
`≥ 0` at every order `N` and for every `c` — the full off-diagonal OS2 of the
rational heat-kernel functional, sourced from the positive node measure. -/
theorem qGram_quadForm_nonneg (M : QMomentData) (Q : NodeQuadrature M)
    (c : Nat → Q') (N : Nat) :
    (0 : Q') ≤ gramQuadForm (qGram M) c N :=
  gramPSD_quadForm_nonneg (qGram_gramRep M Q) c N

/-! ## 5. The cone direction is unconditional (no residual needed)

When every `c_i ≥ 0` the off-diagonal form is nonnegative outright — every entry
`G_{ab}` is a sum of nonnegative moments, and every `c_i c_j ≥ 0`.  This isolates
the genuine content of `NodeQuadrature` as exactly the OFF-cone directions, the
part the measure positivity is needed for. -/

/-- Each rational Gram entry is `≥ 0` (a finite sum of nonnegative moments). -/
theorem qGram_entry_nonneg (M : QMomentData) (a b : Nat) :
    (0 : Q') ≤ qGram M a b :=
  YMGap.RG.finSum_nonneg _ (fun _ => M.m_nonneg _) _

/-- **Cone positivity, unconditional.**  For `c` with all entries `≥ 0` the
off-diagonal quadratic form is `≥ 0` with NO residual: each summand
`(c_i c_j ≥ 0)·(G_{ij} ≥ 0) ≥ 0`. -/
theorem qGram_quadForm_cone_nonneg (M : QMomentData) (c : Nat → Q')
    (hc : ∀ i, (0 : Q') ≤ c i) (N : Nat) :
    (0 : Q') ≤ gramQuadForm (qGram M) c N := by
  refine YMGap.RG.finSum_nonneg _ (fun i => YMGap.RG.finSum_nonneg _ (fun j => ?_) N) N
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (hc i) (hc j)) (qGram_entry_nonneg M i j)

end YMGap.Continuum.HeatKernelGramSOS

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HeatKernelGramSOS.nodeQuadGram_gramRep
#print axioms YMGap.Continuum.HeatKernelGramSOS.nodeQuadGram_quadForm_nonneg
#print axioms YMGap.Continuum.HeatKernelGramSOS.cheb_fusion_one_one
#print axioms YMGap.Continuum.HeatKernelGramSOS.egGram_badvec_nonneg
#print axioms YMGap.Continuum.HeatKernelGramSOS.egGram_badvec_value
#print axioms YMGap.Continuum.HeatKernelGramSOS.qGram_gramRep
#print axioms YMGap.Continuum.HeatKernelGramSOS.qGram_quadForm_nonneg
#print axioms YMGap.Continuum.HeatKernelGramSOS.qGram_entry_nonneg
#print axioms YMGap.Continuum.HeatKernelGramSOS.qGram_quadForm_cone_nonneg
