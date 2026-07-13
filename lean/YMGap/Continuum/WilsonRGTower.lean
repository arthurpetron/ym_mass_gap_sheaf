/-
Track B / E3 — the **multi-edge, non-stationary** Wilson RG tower and its
Kolmogorov-consistent inverse limit.

The prior wave built the *stationary single-edge* Wilson inverse limit: a
constant tower whose every scale is the one-edge SU(2) spin-label carrier
`charAlg` and whose coarse→fine map is the identity inclusion (a coarse
Wilson character IS the same fine Wilson character).  Honest as far as it
went, that tower's carrier does NOT grow with the scale — it carries no
genuine volume dependence — and its inclusion moves no variable.

This module takes a type-level next step toward an interacting block-spin
RG tower at fixed spacing: a tower whose per-scale observable algebra is
the lowest-channel spin carrier on a **growing number of edges** (scale `k`
carries `k+1` edges), with a real coarse→fine **block-spin embedding** that
adjoins one fine edge in the vacuum character, and whose per-scale
functionals are the genuine multi-edge heat-kernel moments.  Kolmogorov
consistency of this multi-edge, non-stationary family is PROVED at the
moment level.

# What this object IS and is NOT (read this first)

  * IT IS a genuinely **multi-edge** Wilson observable system: the carrier
    `EdgeVec (k+1)` (a length-indexed snoc-vector of spin indices) grows by
    one edge at every scale — real, type-level volume dependence — and the
    inclusion `inclTower k` is a NON-identity, NON-stationary coarse→fine
    block-spin embedding (it adjoins the new fine edge carrying the trivial
    character `χ_0`, i.e. a coarse multi-edge observable read as a function
    of the fine block-spin variables that does not yet resolve the new
    edge).  This supersedes the stationary single-edge tower.
  * IT IS the **fixed-spacing inverse limit** of the per-scale multi-edge
    heat-kernel Wilson functionals, assembled into a genuine
    `ContinuumMeasure` whose per-scale projection law is proved.
  * IT IS NOT the scaling (`a → 0`) continuum limit; that needs a
    lattice-spacing-uniform two-sided modulus, the named open obligation.
  * IT IS the **independent-product** multi-edge tower: the per-scale weight
    is a product of independent single-edge heat-kernel factors,
    `E (χ_{s₀}⊗⋯⊗χ_{s_k}) = ∏_i dim(s_i)·w^{C₄(s_i)}`.  It is NOT the
    interacting, plaquette-COUPLED Wilson Boltzmann weight (the genuine
    Wilson action coupling neighbouring edges around each plaquette).  That
    coupling — the interacting Boltzmann weight and its RG flow — is named
    as the precise residual below; it is NOT faked here.

# What is genuine here (constructed / proved)

  * `EdgeVec n` — a length-indexed snoc-vector of edge spin indices: the
    carrier of the multi-edge character algebra, which genuinely grows with
    the scale.  `vacVec n` is the all-vacuum (trivial-character) vector.
  * `edgeAlg n` — the multi-edge lowest-channel carrier on `n` edges:
    `one = vacVec`, pointwise Clebsch–Gordan lowest-weight product
    (`mulVec`), `star = id`.  Since the one-edge operation is not associative,
    neither is this a Wilson/character algebra.
  * `inclVacHom` — the genuine coarse→fine block-spin embedding
    `edgeAlg n → edgeAlg (n+1)`, adjoining the new fine edge in the vacuum
    character (`v ↦ v ⊕ χ_0`).  A real unital *-hom (`map_one`/`map_mul`/
    `map_star` proved) that is genuinely NON-identity — it changes the
    algebra (carrier grows) and moves the variable (a new edge appears).
  * `edgeProd w` — the per-scale **product heat-kernel functional**
    `E (χ_{s₀}⊗⋯⊗χ_{s_{n−1}}) = ∏_i dim(s_i)·w^{C₄(s_i)}`, normalized
    (`E one = 1`), positive (a product of nonnegative edge factors), and
    genuinely multi-variable / non-constant.
  * `wilsonTower` / `wilsonTowerFunc` — the multi-edge `ObsSystem` and its
    per-scale product functional (scale `k` = `k+1` edges).
  * `wilsonTowerConsistency` — THE MAIN THEOREM: the multi-edge,
    non-stationary product family is Kolmogorov-consistent,
    `is_consistent (funcProjSystem wilsonTower) wilsonTowerFunc`.  Proved
    via the value-level transport law (`consistent_iff_transport`): the
    fine product over `k+2` edges of a coarse observable carried up by the
    block-spin embedding telescopes through the vacuum factor `χ_0 ↦ 1`
    back to the coarse product over `k+1` edges.  This is a NON-`rfl`
    transport identity on real `Q'` moment data — the genuine step beyond
    the stationary single-edge proof.
  * `wilsonTowerContinuumMeasure` — the genuine multi-edge inverse-limit
    Wilson measure `μ_∞`, with the Daniell–Kolmogorov projection law
    `π_k(μ_∞) = μ_k` proved.

# What remains open (the named residual — honestly isolated)

  * The **interacting, plaquette-coupled** Wilson Boltzmann weight: here the
    per-scale functional is a PRODUCT of independent single-edge factors,
    not the Wilson action `e^{β Σ_p Re tr U_p}` coupling the edges around
    each plaquette.  The interacting weight and its block-spin RG flow (the
    genuine coarse→fine map of the coupled measure, with a quantitative
    per-step contraction) are the precise residual.  They are NOT faked: the
    inclusion here adjoins a vacuum edge and the moments factor across edges.
  * The scaling (`a → 0`) limit and its spacing-uniform modulus.
  * The Daniell–Kolmogorov σ-additive extension of the coherent functional.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Structural / `rfl` / `congrArg` proofs on the length-indexed snoc-vector
carrier; `Q'` order/equality identities reused from the constructive layer.
The carrier `EdgeVec` is a plain inductive type and the block-spin map and
the product telescope are definitional, so no `Fin`-recursor classical
content enters.  No `Classical.*`, no `native_decide`, no `sorry`/`admit`,
no new `axiom`.  All data is `Type`-level.
-/

import YMGap.Continuum.WilsonConsistency

namespace YMGap.Continuum.WilsonRGTower

open YMGap.Constructive
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.RGTransport

/-! ## 1. The multi-edge carrier: a length-indexed snoc-vector of spins

`EdgeVec n` is a vector of `n` edge spin indices, built by `snoc` (append on
the right).  The length lives in the type, so the carrier `EdgeVec (k+1)` of
scale `k` genuinely GROWS by one edge at every coarse→fine step — real,
type-level volume dependence, in contrast to the stationary single-edge
tower whose carrier is the fixed spin index `Nat`.  Using a plain inductive
(rather than `Fin n → Nat`) keeps the block-spin embedding and the product
telescope definitional and free of the classical `Fin`-recursor content. -/

/-- A length-indexed vector of edge spin indices: scale `k` carries `k+1`
edges as `EdgeVec (k+1)`.  Each entry is an SU(2) spin index `s = 2j`. -/
inductive EdgeVec : Nat → Type
  | nil : EdgeVec 0
  | snoc : {n : Nat} → EdgeVec n → Nat → EdgeVec (n + 1)

/-- The all-vacuum edge vector (every edge carries the trivial character
`χ_0`) — the unit of the multi-edge character algebra. -/
def vacVec : (n : Nat) → EdgeVec n
  | 0 => .nil
  | n + 1 => .snoc (vacVec n) 0

/-- Pointwise SU(2) Clebsch–Gordan **lowest-weight** product on two
equal-length edge vectors: edge `i` of `mulVec a b` is the lowest fusion
spin `max (aᵢ) (bᵢ) − min (aᵢ) (bᵢ)` of the two edge characters (the same
single-edge product as `RGTransport.charAlg.mul`, applied per edge). -/
def mulVec : {n : Nat} → EdgeVec n → EdgeVec n → EdgeVec n
  | 0, .nil, .nil => .nil
  | _ + 1, .snoc a x, .snoc b y => .snoc (mulVec a b) (max x y - min x y)

/-- The involution: SU(2) characters are real, so `star = id` on each edge. -/
def starVec {n : Nat} (v : EdgeVec n) : EdgeVec n := v

/-! ## 2. The multi-edge lowest-channel carrier

`edgeAlg n` is a pointwise lowest-channel carrier on `n` edges: carrier
`EdgeVec n`, unit the all-vacuum vector, product the pointwise lowest-weight
projection, involution the identity.  It genuinely has multiple variables,
but its product inherits the one-edge nonassociativity and therefore is not
the SU(2) observable algebra. -/

/-- The multi-edge lowest-channel spin carrier on `n` edges. -/
def edgeAlg (n : Nat) : ObsAlg where
  carrier := EdgeVec n
  one := vacVec n
  mul := mulVec
  star := starVec

@[simp] theorem edgeAlg_carrier (n : Nat) : (edgeAlg n).carrier = EdgeVec n := rfl

/-- The multi-edge carrier at scale `k` (= `k+1` edges) genuinely has
the GROWING carrier `EdgeVec (k+1)` — not the fixed single-edge spin index
`Nat` of the stationary tower. -/
theorem edgeAlg_carrier_grows (k : Nat) : (edgeAlg (k + 1)).carrier = EdgeVec (k + 1) := rfl

/-! ## 3. The coarse→fine block-spin embedding (adjoin a vacuum edge)

`inclVacHom n : edgeAlg n → edgeAlg (n+1)` is the genuine coarse→fine
block-spin embedding: a coarse observable on `n` edges becomes a fine
observable on `n+1` edges by adjoining the new fine edge carrying the
trivial character `χ_0` (`v ↦ v ⊕ χ_0`).  This is the real inclusion of a
coarse multi-edge Wilson observable as a function of the fine block-spin
variables that does not yet resolve the freshly-adjoined edge.  It is a
genuine unital *-homomorphism (proved) AND it is genuinely non-stationary:
it changes the algebra (the carrier grows) and moves the variables (a new
edge appears), unlike the stationary identity inclusion. -/

/-- The block-spin embedding `v ↦ v ⊕ χ_0`: adjoin one fine edge in the
vacuum character.  A genuine unital *-hom `edgeAlg n → edgeAlg (n+1)`. -/
def inclVacHom (n : Nat) : ObsHom (edgeAlg n) (edgeAlg (n + 1)) where
  map := fun v => EdgeVec.snoc v 0
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl

@[simp] theorem inclVacHom_map (n : Nat) (v : EdgeVec n) :
    (inclVacHom n).map v = EdgeVec.snoc v 0 := rfl

/-- The block-spin embedding is genuinely **non-stationary**: it sends the
coarse vector `χ_1` (one edge in spin `1/2`) to the strictly longer fine
vector `χ_1 ⊕ χ_0`, an inhabitant of the GROWN algebra `edgeAlg 1` — not a
self-map of a fixed algebra.  (Stated as the defining `snoc` identity, whose
codomain length `1` exceeds the domain length `0`.) -/
theorem inclVacHom_grows :
    (inclVacHom 0).map (EdgeVec.nil) = EdgeVec.snoc EdgeVec.nil 0 := rfl

/-! ## 4. The per-edge heat-kernel factor and the product functional

The single-edge heat-kernel moment `edgeFactor w s = dim(s)·w^{C₄(s)}` (the
same closed form as `RGTransport.charFunc`'s diagonal value, `w = e^{−t/4}`
discretized to `Q'`).  The per-scale functional is the genuine multi-edge
PRODUCT `E (χ_{s₀}⊗⋯⊗χ_{s_{n−1}}) = ∏_i edgeFactor w sᵢ`. -/

/-- The single-edge heat-kernel moment `dim(s)·w^{C₄(s)}` in `Q'`. -/
def edgeFactor (w : Q') (s : Nat) : Q' := dimQ s * qpow w (c4 s)

/-- The vacuum edge carries factor `1` (`dim 0 = 1`, `C₄ 0 = 0`, `w⁰ = 1`):
the per-edge probability normalization. -/
theorem edgeFactor_vac (w : Q') : edgeFactor w 0 = 1 := by
  show dimQ 0 * qpow w (c4 0) = 1
  rw [dimQ_zero, c4_zero, qpow_zero]; rfl

/-- Each edge factor is `≥ 0` (`dim ≥ 0`, `w^{·} ≥ 0`). -/
theorem edgeFactor_nonneg (w : Q') (hw : (0 : Q') ≤ w) (s : Nat) :
    (0 : Q') ≤ edgeFactor w s :=
  Q'.mul_nonneg _ _ (dimQ_nonneg _) (qpow_nonneg w hw _)

/-- The multi-edge **product heat-kernel functional value**
`∏_i edgeFactor w sᵢ` over an edge vector. -/
def edgeProd (w : Q') : {n : Nat} → EdgeVec n → Q'
  | 0, .nil => 1
  | _ + 1, .snoc v s => edgeProd w v * edgeFactor w s

/-- The product over the all-vacuum vector is `1` (the probability
normalization at the algebra unit). -/
theorem edgeProd_vac (w : Q') : (n : Nat) → edgeProd w (vacVec n) = 1
  | 0 => rfl
  | n + 1 => by
      show edgeProd w (vacVec n) * edgeFactor w 0 = 1
      rw [edgeProd_vac w n, edgeFactor_vac]; decide

/-- The product is `≥ 0`: a product of nonnegative edge factors. -/
theorem edgeProd_nonneg (w : Q') (hw : (0 : Q') ≤ w) :
    {n : Nat} → (v : EdgeVec n) → (0 : Q') ≤ edgeProd w v
  | 0, .nil => by show (0 : Q') ≤ (1 : Q'); decide
  | _ + 1, .snoc v s =>
      Q'.mul_nonneg _ _ (edgeProd_nonneg w hw v) (edgeFactor_nonneg w hw s)

/-- The `mul`-square `mulVec (starVec a) a` is the all-vacuum vector
(`star = id`, and per edge `max s s − min s s = 0`): so `E(a*·a) =
E(vac) = 1 ≥ 0`, the GNS positivity on the diagonal. -/
theorem mulVec_self_vac :
    {n : Nat} → (a : EdgeVec n) → mulVec (starVec a) a = vacVec n
  | 0, .nil => rfl
  | _ + 1, .snoc a s => by
      show EdgeVec.snoc (mulVec a a) (max s s - min s s) = EdgeVec.snoc (vacVec _) 0
      have hself : mulVec (starVec a) a = vacVec _ := mulVec_self_vac a
      have hs : max s s - min s s = 0 := by
        rw [Nat.max_self, Nat.min_self, Nat.sub_self]
      rw [show mulVec a a = mulVec (starVec a) a from rfl, hself, hs]

/-- The **product heat-kernel functional** `E (χ_{s₀}⊗⋯) = ∏_i edgeFactor w sᵢ`
on `edgeAlg n` — genuine multi-edge `Q'`-valued Wilson data: normalized at
the unit and positive on `a*·a`. -/
def edgeFunc (w : Q') (_hw : (0 : Q') ≤ w) (n : Nat) : ProbFunctional (edgeAlg n) where
  E := fun v => edgeProd w v
  normalized := by
    show edgeProd w (vacVec n) = 1
    exact edgeProd_vac w n
  positive := fun a => by
    show (0 : Q') ≤ edgeProd w (mulVec (starVec a) a)
    rw [mulVec_self_vac a, edgeProd_vac]
    decide

/-- **`edgeFunc` is genuinely multi-variable / non-constant** (it is NOT the
`≡ 1` placeholder): at `w = 1/2` on two edges, the vacuum pair has `E = 1`
while the pair `χ_2 ⊕ χ_2` has `E = (3·(1/2)^8)² ≠ 1`.  Hence the
consistency below is about real, non-trivial multi-edge moment data. -/
theorem edgeFunc_nonconstant :
    (edgeFunc (Q'.mkPos 1 2 (by decide)) (by decide) 2).E
        (EdgeVec.snoc (EdgeVec.snoc EdgeVec.nil 0) 0) = 1 ∧
      ¬ ((edgeFunc (Q'.mkPos 1 2 (by decide)) (by decide) 2).E
          (EdgeVec.snoc (EdgeVec.snoc EdgeVec.nil 2) 2) = 1) := by
  refine ⟨?_, ?_⟩
  · show edgeProd (Q'.mkPos 1 2 (by decide)) (vacVec 2) = 1
    exact edgeProd_vac _ 2
  · decide

/-! ## 5. The multi-edge, non-stationary Wilson tower

Scale `k` is the `(k+1)`-edge Wilson algebra `edgeAlg (k+1)`; the coarse→
fine embedding is the block-spin vacuum-adjunction `inclVacHom (k+1)`.  The
carrier grows and the embedding moves a variable at every step — a genuine
non-stationary multi-edge tower. -/

/-- **The multi-edge, non-stationary Wilson `ObsSystem`.**  Scale `k` is the
`(k+1)`-edge Wilson/character algebra `edgeAlg (k+1)`; the coarse→fine
embedding `inclVacHom (k+1)` adjoins one fine edge in the vacuum character.
A real growing tower, superseding the stationary single-edge one. -/
def wilsonTower : ObsSystem where
  Obs := fun k => edgeAlg (k + 1)
  incl := fun k => inclVacHom (k + 1)

@[simp] theorem wilsonTower_obs (k : Nat) : wilsonTower.Obs k = edgeAlg (k + 1) := rfl

@[simp] theorem wilsonTower_incl (k : Nat) :
    wilsonTower.incl k = inclVacHom (k + 1) := rfl

/-- The Wilson tower's per-scale carrier genuinely GROWS with the scale:
scale `k` has carrier `EdgeVec (k+1)` (k+1 edges). -/
theorem wilsonTower_carrier_grows (k : Nat) :
    (wilsonTower.Obs k).carrier = EdgeVec (k + 1) := rfl

/-- The per-scale multi-edge product heat-kernel functional. -/
def wilsonTowerFunc (w : Q') (hw : (0 : Q') ≤ w) (k : Nat) :
    ProbFunctional (wilsonTower.Obs k) :=
  edgeFunc w hw (k + 1)

/-! ## 6. The main theorem: Kolmogorov consistency of the multi-edge tower

By `consistent_iff_transport`, consistency reduces to the value-level
transport law: for every scale `k` and coarse observable `o`,

    (wilsonTowerFunc (k+1)).E ((inclVacHom).map o) = (wilsonTowerFunc k).E o,

i.e. the fine product over `k+2` edges of `o ⊕ χ_0` equals the coarse
product over `k+1` edges of `o`.  Since the adjoined edge carries the vacuum
character with factor `edgeFactor w 0 = 1`, the fine product telescopes
through that unit factor back to the coarse product — a genuine `Q'`
arithmetic identity (NON-`rfl`: the adjoined factor `dim 0 · w⁰` must be
recognized as `1`), not the trivial reflexive witness of a stationary
tower. -/

/-- **The block-spin transport identity** at the moment level: the fine
product of the block-spin image `o ⊕ χ_0` equals the coarse product of `o`.
The fine product is `edgeProd w o · edgeFactor w 0 = edgeProd w o · 1 =
edgeProd w o` — the vacuum edge telescopes away. -/
theorem edgeProd_blockspin (w : Q') {n : Nat} (o : EdgeVec n) :
    edgeProd w (EdgeVec.snoc o 0) = edgeProd w o := by
  show edgeProd w o * edgeFactor w 0 = edgeProd w o
  rw [edgeFactor_vac]
  -- `x * 1 = x` for `Q'` (unnormalized): `x.num * 1 = x.num`, `x.den * 1 - 1 = x.den - 1`.
  cases h : edgeProd w o with
  | mk num den =>
    show Q'.mk (num * 1) (Nat.succ den * 1 - 1) = Q'.mk num den
    rw [Int.mul_one, Nat.mul_one, Nat.succ_sub_one]

/-- **THE MAIN THEOREM — the multi-edge, non-stationary Wilson family is
Kolmogorov-consistent.**  `is_consistent (funcProjSystem wilsonTower)
(wilsonTowerFunc w hw)`: at every scale the fine multi-edge product
functional restricts along the block-spin embedding to the coarse one.
Proved from the real heat-kernel moment structure via the value-level
transport law (`consistent_iff_transport`): the fine product over the
adjoined vacuum edge telescopes back to the coarse product.  This is a
genuine step beyond the stationary single-edge proof — the carrier grows
and the inclusion moves a variable, yet the moments cohere. -/
theorem wilsonTowerConsistency (w : Q') (hw : (0 : Q') ≤ w) :
    is_consistent (funcProjSystem wilsonTower) (fun k => wilsonTowerFunc w hw k) := by
  refine (consistent_iff_transport wilsonTower (fun k => wilsonTowerFunc w hw k)).mpr ?_
  intro k o
  -- (wilsonTowerFunc (k+1)).E ((inclVacHom (k+1)).map o) = (wilsonTowerFunc k).E o
  -- LHS = edgeProd w (snoc o 0); RHS = edgeProd w o.
  show edgeProd w (EdgeVec.snoc o 0) = edgeProd w o
  exact edgeProd_blockspin w o

/-- The value-level transport law made explicit on the real multi-edge
moments: the heat-kernel moment of a coarse multi-edge observable `o`,
carried up by the block-spin embedding, equals its coarse product moment
`∏_i edgeFactor w oᵢ`. -/
theorem wilsonTowerMomentTransport (w : Q') (hw : (0 : Q') ≤ w) (k : Nat)
    (o : EdgeVec (k + 1)) :
    (wilsonTowerFunc w hw (k + 1)).E ((wilsonTower.incl k).map o)
      = edgeProd w o := by
  show edgeProd w (EdgeVec.snoc o 0) = edgeProd w o
  exact edgeProd_blockspin w o

/-! ## 7. The genuine multi-edge inverse-limit Wilson measure

`wilsonTowerContinuumMeasure` is the real `ContinuumMeasure` assembled from
the multi-edge Wilson system, the per-scale product heat-kernel functionals,
and the consistency proof — the fixed-spacing inverse-limit Wilson functional
of the multi-edge tower.  Its per-scale projection is the multi-edge
heat-kernel functional. -/

/-- **The genuine multi-edge inverse-limit Wilson measure `μ_∞`.**  Built
from the multi-edge non-stationary Wilson system, the per-scale product
heat-kernel functionals, and `wilsonTowerConsistency`.  This supersedes the
stationary single-edge inverse limit (its carrier genuinely grows with the
scale). -/
def wilsonTowerContinuumMeasure (w : Q') (hw : (0 : Q') ≤ w) :
    ContinuumMeasure (fun k => ProbFunctional (wilsonTower.Obs k)) :=
  continuumMeasure wilsonTower (fun k => wilsonTowerFunc w hw k)
    (wilsonTowerConsistency w hw)

/-- **The Daniell–Kolmogorov projection law for `μ_∞`** (`π_k(μ_∞) = μ_k`):
the per-scale projection of the multi-edge inverse-limit Wilson measure is
the multi-edge product heat-kernel functional at that scale. -/
theorem wilsonTowerContinuumMeasure_proj (w : Q') (hw : (0 : Q') ≤ w) (k : Nat) :
    (wilsonTowerContinuumMeasure w hw).pushforward_to_stage k
        (wilsonTowerContinuumMeasure w hw).limit
      = wilsonTowerFunc w hw k :=
  (wilsonTowerContinuumMeasure w hw).pushforward_limit_eq k

/-- The inverse-limit thread is itself Kolmogorov-consistent at the limit
(the coherence of `μ_∞` across scales for the multi-edge tower). -/
theorem wilsonTowerContinuumMeasure_coherent (w : Q') (hw : (0 : Q') ≤ w) (k : Nat) :
    (wilsonTowerContinuumMeasure w hw).sys.coarsen k
        ((wilsonTowerContinuumMeasure w hw).pushforward_to_stage (k + 1)
          (wilsonTowerContinuumMeasure w hw).limit)
      = (wilsonTowerContinuumMeasure w hw).pushforward_to_stage k
          (wilsonTowerContinuumMeasure w hw).limit :=
  (wilsonTowerContinuumMeasure w hw).coarsen_pushforward k

end YMGap.Continuum.WilsonRGTower

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonRGTower.edgeAlg
#print axioms YMGap.Continuum.WilsonRGTower.edgeAlg_carrier_grows
#print axioms YMGap.Continuum.WilsonRGTower.inclVacHom
#print axioms YMGap.Continuum.WilsonRGTower.inclVacHom_grows
#print axioms YMGap.Continuum.WilsonRGTower.edgeFactor_vac
#print axioms YMGap.Continuum.WilsonRGTower.edgeProd_vac
#print axioms YMGap.Continuum.WilsonRGTower.edgeProd_nonneg
#print axioms YMGap.Continuum.WilsonRGTower.mulVec_self_vac
#print axioms YMGap.Continuum.WilsonRGTower.edgeFunc
#print axioms YMGap.Continuum.WilsonRGTower.edgeFunc_nonconstant
#print axioms YMGap.Continuum.WilsonRGTower.wilsonTower
#print axioms YMGap.Continuum.WilsonRGTower.wilsonTower_carrier_grows
#print axioms YMGap.Continuum.WilsonRGTower.edgeProd_blockspin
#print axioms YMGap.Continuum.WilsonRGTower.wilsonTowerConsistency
#print axioms YMGap.Continuum.WilsonRGTower.wilsonTowerMomentTransport
#print axioms YMGap.Continuum.WilsonRGTower.wilsonTowerContinuumMeasure
#print axioms YMGap.Continuum.WilsonRGTower.wilsonTowerContinuumMeasure_proj
#print axioms YMGap.Continuum.WilsonRGTower.wilsonTowerContinuumMeasure_coherent
