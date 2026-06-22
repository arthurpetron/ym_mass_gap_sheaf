/-
The polymer / cluster model — Layer 0b STRUCTURE of the strong-coupling
cluster-expansion build.

# Scope (honest underclaim)

This file builds the *combinatorial object* that the cluster expansion
acts on, which was previously ABSENT from the formalization: the
abstract configuration site (`Sheaf/Site.lean`) carries only an
abstract polymer-inclusion predicate `PolySub`, with no plaquette
sets, no size `|X|`, no connectivity, and no Haar link-constraint.

What is DEFINED here:

  * an abstract finite lattice interface (`Lattice`): a type of links,
    a type of plaquettes, and a decidable boundary-incidence relation
    "link `ℓ` lies on the boundary of plaquette `p`";
  * a concrete `d`-independent toy hypercubic sanity witness
    (`toyLattice`);
  * `Polymer` := a `List` of plaquettes (the finite plaquette set),
    `size |X|` (length), and a `connected` predicate (every two
    plaquettes joined by a chain of plaquettes sharing a link);
  * the **Haar-orthogonality link constraint** `linkConstraint`, the
    structural predicate that encodes the SU(2) fusion-to-trivial
    condition around each internal link (decidable, built on the
    existing `fusionOK` Clebsch–Gordan predicate);
  * the **activity** `activity w X label`, the product of the
    heat-kernel character coefficients `coeffW w (label p)` over the
    polymer's plaquettes, with `activity_nonneg` and `activity_pos`;
  * an HONEST, well-typed bridge stub naming how `activity` / `size` /
    `connected` / `linkConstraint` are the intended inputs to the
    Kotecký–Preiss criterion of `Sheaf/Summability.lean`.

What is NOT done here (named, NOT faked — these are Wave 2):

  * `kpCriterion` (the L1 obligation `∑_{X∋p}|ζ(X)|e^{|X|} ≤ a(p)`)
    is exposed only as a `def`-level PREDICATE plus a Prop-valued
    *statement signature* `KPObligation`; its PROOF is Wave 2.
  * the theorem that the Haar link-constraint forces the activity of a
    non-trivial polymer to be small at strong coupling — this is the
    analytic heart of the expansion and is Wave 2;
  * volume-uniformity / convergence of the cluster sum — Wave 2/3.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Q'` and core. No `Classical.*`, no `Real`, no
`native_decide`, no `decide` on non-decidable props. No `sorry` /
`admit` / new `axiom`. Witnesses are Type-level data (the lattice,
polymers, the activity value); the genuinely-propositional side
conditions (incidence, fusion compatibility) are decidable `Prop`s.
-/

import YMGap.Continuum.BondMovingStep
import YMGap.Continuum.FusionResidualBound
import YMGap.Constructive.RationalTail
import YMGap.Sheaf.Summability

namespace YMGap.Continuum.PolymerModel

open YMGap.Continuum.BondMovingStep
open YMGap.Constructive

/-! ## 1. The abstract finite lattice interface

The cluster expansion is UNIFORM over the lattice geometry, so we keep
the lattice abstract: a type of links, a type of plaquettes, and a
decidable incidence relation `boundary p ℓ` reading "link `ℓ` lies on
the boundary of plaquette `p`".  No metric, no dimension — only the
incidence combinatorics the polymer model needs.

Decidability of `boundary` is part of the interface (it is what makes
connectivity and the link-constraint decidable). -/

/-- An abstract finite lattice: a type of `Link`s, a type of
`Plaquette`s, and a decidable boundary-incidence relation
`boundary p ℓ` ("link `ℓ` is on the boundary of plaquette `p`").

Kept abstract so that polymers, connectivity, and the link constraint
are defined uniformly over any lattice geometry; a concrete hypercubic
witness is `toyLattice` below. -/
structure Lattice where
  /-- The type of (oriented) links / edges. -/
  Link : Type
  /-- The type of plaquettes (elementary 2-cells). -/
  Plaquette : Type
  /-- Boundary incidence: `boundary p ℓ` iff link `ℓ` lies on the
  boundary of plaquette `p`. -/
  boundary : Plaquette → Link → Bool

namespace Lattice

variable (L : Lattice)

/-- Two plaquettes are *link-adjacent* if they share at least one
boundary link `ℓ`.  Witness-bearing: carries the shared link as data
together with the two incidence proofs. -/
structure Adjacent (p q : L.Plaquette) where
  /-- The shared boundary link. -/
  link    : L.Link
  /-- `link` is on the boundary of `p`. -/
  on_p    : L.boundary p link = true
  /-- `link` is on the boundary of `q`. -/
  on_q    : L.boundary q link = true

end Lattice

/-! ### A concrete toy hypercubic sanity witness

A minimal concrete instance to confirm the interface is inhabitable.
Plaquettes are encoded by a pair `(siteIndex, planeIndex)` and links
by a pair `(siteIndex, dirIndex)`, all as `Nat`.  The boundary
incidence is a deliberately-simple decidable predicate (a link is on a
plaquette's boundary iff their site indices agree); it is a *sanity*
instance, not the physical 4D incidence (which is Wave 2 geometry).
-/

/-- A toy hypercubic-style lattice witness: links and plaquettes are
`Nat × Nat`, and a link is on a plaquette's boundary iff their first
coordinates (the site index) agree.  Purely a witness that `Lattice`
is inhabitable; not the physical incidence relation. -/
def toyLattice : Lattice where
  Link := Nat × Nat
  Plaquette := Nat × Nat
  boundary := fun p ℓ => p.1 == ℓ.1

/-! ## 2. Polymers

A polymer `X` is a finite set of plaquettes.  We model the finite set
as a `List L.Plaquette` (the substrate is Mathlib-free, so no
`Finset`); `size X := X.length` is the plaquette count `|X|`.

Connectivity is the chain condition: every two plaquettes of `X` are
joined by a chain of plaquettes (each consecutive pair link-adjacent).
We give it as a Type-level relation `ChainConn` (a reflexive–transitive
closure carrying the chain as data) and then `connected` over a
polymer. -/

/-- A polymer over a lattice `L`: a finite list of plaquettes.
Reducible so the `List` membership / append API is available on it. -/
abbrev Polymer (L : Lattice) : Type := List L.Plaquette

namespace Polymer

variable {L : Lattice}

/-- The size `|X|` of a polymer: its plaquette count (list length). -/
def size (X : Polymer L) : Nat := X.length

/-- `size` is a `Nat`, hence always `≥ 0` (recorded for the interface;
the cluster sum uses `0 ≤ |X|` implicitly). -/
theorem size_nonneg (X : Polymer L) : 0 ≤ size X := Nat.zero_le _

/-- The empty polymer has size `0`. -/
@[simp] theorem size_nil : size ([] : Polymer L) = 0 := rfl

/-- Prepending a plaquette increments the size. -/
@[simp] theorem size_cons (p : L.Plaquette) (X : Polymer L) :
    size (p :: X) = size X + 1 := by
  show (p :: X).length = X.length + 1
  rw [List.length_cons]

/-- **Size is additive on (list) union.**  `|X ++ Y| = |X| + |Y|`.
For disjoint polymers (`X` and `Y` sharing no plaquette) the list
concatenation is the set union, so this is the disjoint-union
additivity the cluster sum needs. -/
theorem size_append (X Y : Polymer L) :
    size (X ++ Y) = size X + size Y := by
  show (X ++ Y).length = X.length + Y.length
  rw [List.length_append]

/-- A plaquette `p` *belongs to* the polymer `X` (membership in the
underlying list). -/
def mem (p : L.Plaquette) (X : Polymer L) : Prop := p ∈ X

/-! ### Connectivity (chain condition)

`ChainConn L p q` is the Type-level reflexive–transitive closure of
link-adjacency: either `p = q`, or there is an intermediate plaquette
`r` adjacent to `p` with `ChainConn L r q`.  It carries the chain as
data (a list of `Adjacent` steps), staying inside the Type-level
witness discipline. -/

/-- Chain-connectivity of two plaquettes via link-adjacency steps.
`refl`: a plaquette is connected to itself.  `step`: if `p` is
link-adjacent to `r` and `r` is chain-connected to `q`, then `p` is
chain-connected to `q`.  The constructor data IS the connecting
chain. -/
inductive ChainConn (L : Lattice) : L.Plaquette → L.Plaquette → Type
  | refl (p : L.Plaquette) : ChainConn L p p
  | step {p r q : L.Plaquette}
      (adj : L.Adjacent p r) (rest : ChainConn L r q) : ChainConn L p q

namespace ChainConn

/-- Chain-connectivity is transitive: concatenate the two chains. -/
def trans {L : Lattice} : {p q r : L.Plaquette} →
    ChainConn L p q → ChainConn L q r → ChainConn L p r
  | _, _, _, ChainConn.refl _, h => h
  | _, _, _, ChainConn.step adj rest, h =>
      ChainConn.step adj (trans rest h)

end ChainConn

/-- A polymer is *connected* if every two of its plaquettes are
chain-connected.  Stated as Type-level data: a function producing the
connecting chain for any two member plaquettes.

(The empty polymer and singletons are vacuously / trivially connected;
see `connected_singleton`.) -/
def connected (X : Polymer L) : Type :=
  ∀ p q : L.Plaquette, p ∈ X → q ∈ X → ChainConn L p q

/-- A singleton polymer is connected (the only chain needed is
reflexivity). -/
def connected_singleton (p : L.Plaquette) : connected ([p] : Polymer L) :=
  fun a b ha hb => by
    have hae : a = p := List.mem_singleton.mp ha
    have hbe : b = p := List.mem_singleton.mp hb
    rw [hae, hbe]
    exact ChainConn.refl p

end Polymer

/-! ## 3. The Haar-orthogonality link constraint (THE key predicate)

A rep-labeling assigns to each plaquette an SU(2) spin index
`label p : Rep` (`Rep := Nat`, the doubled spin `s = 2j`).

The character-expansion measure factorizes over plaquettes; integrating
the gauge field on a link `ℓ` (Haar measure) couples the plaquettes
meeting `ℓ`.  For SU(2) the link Haar integral of the product of the
meeting plaquettes' characters is NONZERO iff the tensor product of the
meeting reps contains the trivial rep — i.e. the reps fuse to the
trivial representation.  This is the orthogonality/cancellation
condition that makes the activity of a polymer small at strong
coupling: links whose reps fail it contribute zero.

We encode the SU(2) fusion-to-trivial condition with the existing
Clebsch–Gordan predicate `fusionOK` from `BondMovingStep`:
`fusionOK a b 0` holds iff `χ_0 ∈ χ_a · χ_b`, i.e. `a = b` (the only
SU(2) pair fusing to the trivial rep).  For a link shared by exactly
two plaquettes `p, q` the Haar-cancellation condition is therefore
`fusionOK (label p) (label q) 0 = true`.

`linkConstraint` quantifies this over every internal link of `X`,
where a link is *internal* if it is on the boundary of at least two
plaquettes of `X`.  We state it pairwise over adjacent plaquette pairs
(the binary form sufficient for the planar / two-plaquettes-per-link
case; the general multi-plaquette link integral is Wave 2).  Decidable
because `fusionOK` and `boundary` are decidable. -/

/-- The SU(2) rep label of a plaquette: the doubled-spin index
`s = 2j ∈ {0, 1, 2, …}` (`Rep := Nat`). -/
abbrev Rep : Type := Nat

/-- **The SU(2) Haar fuse-to-trivial condition for one shared link**:
the meeting reps `a, b` admit the trivial rep in their tensor product,
i.e. `χ_0 ∈ χ_a · χ_b`.  For SU(2) this holds iff `a = b`.  Encoded via
the existing Clebsch–Gordan predicate `fusionOK a b 0`. -/
def fusesToTrivial (a b : Rep) : Bool := fusionOK a b 0

/-- For SU(2), `fusesToTrivial a b` holds exactly when `a = b`
(`χ_0 ∈ χ_a · χ_b ⇔ a = b`).  Sanity lemma confirming the encoding
realizes the Haar-orthogonality selection rule. -/
theorem fusesToTrivial_iff_eq (a b : Rep) :
    fusesToTrivial a b = true ↔ a = b := by
  unfold fusesToTrivial fusionOK
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨h1, _h2⟩, _⟩ := h
    -- h1 : max a b - min a b ≤ 0  ⇒ max ≤ min ⇒ a = b
    have hmax : Nat.max a b - Nat.min a b = 0 := Nat.le_zero.mp h1
    have hle : Nat.max a b ≤ Nat.min a b := Nat.sub_eq_zero_iff_le.mp hmax
    have hle1 : a ≤ b := Nat.le_trans (Nat.le_max_left a b)
      (Nat.le_trans hle (Nat.min_le_right a b))
    have hle2 : b ≤ a := Nat.le_trans (Nat.le_max_right a b)
      (Nat.le_trans hle (Nat.min_le_left a b))
    exact Nat.le_antisymm hle1 hle2
  · intro h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.max_self,
      Nat.min_self, Nat.sub_self]
    refine ⟨⟨Nat.le_refl 0, Nat.zero_le _⟩, ?_⟩
    -- (a + a + 0) % 2 = 0
    omega

/-- **The Haar-orthogonality link constraint on a polymer.**

`linkConstraint L X label` holds iff for every pair of plaquettes
`p, q` in `X` that are link-adjacent (share an internal link), their
rep labels fuse to the trivial rep — the Haar-cancellation selection
rule around each internal link.

This is the structural DEFINITION of the constraint that makes
activities small at strong coupling; the THEOREM that it forces small
activities (and hence cluster-sum convergence) is Wave 2. -/
def linkConstraint (L : Lattice) (X : Polymer L) (label : L.Plaquette → Rep) :
    Prop :=
  ∀ p q : L.Plaquette, p ∈ X → q ∈ X →
    L.Adjacent p q → fusesToTrivial (label p) (label q) = true

/-- The link constraint is decidable when membership is decidable and
the plaquette type is finite-enumerable; in the general abstract case
we record the decidable CORE — the per-link fuse-to-trivial test
`fusesToTrivial` is decidable (it is a `Bool`).  This lemma exposes the
decidability of the atomic condition the constraint quantifies. -/
def fusesToTrivial_decidable (a b : Rep) :
    Decidable (fusesToTrivial a b = true) := inferInstance

/-! ## 4. Activity

The activity of a polymer `X` under weight `w` and labeling `label` is
the product of the diagonal heat-kernel character coefficients
`coeffW w (label p)` over the plaquettes `p ∈ X`:

    ζ(X) = ∏_{p ∈ X} coeff_w(label p).

Defined via `List.foldr` over the plaquette list.  `coeffW w 0 = 1`
(vacuum / trivial rep contributes the unit), so the empty polymer has
activity `1`. -/

/-- The per-plaquette activity weight: `coeffW w (label p)`. -/
def plaqWeight {L : Lattice} (w : Q') (label : L.Plaquette → Rep)
    (p : L.Plaquette) : Q' := coeffW w (label p)

/-- **The polymer activity** `ζ(X) = ∏_{p ∈ X} coeff_w(label p)`,
as a `List.foldr` product over the plaquette list. -/
def activity {L : Lattice} (w : Q') (X : Polymer L)
    (label : L.Plaquette → Rep) : Q' :=
  X.foldr (fun p acc => plaqWeight w label p * acc) 1

/-- The empty polymer has activity `1`. -/
@[simp] theorem activity_nil {L : Lattice} (w : Q')
    (label : L.Plaquette → Rep) :
    activity w ([] : Polymer L) label = 1 := rfl

/-- Activity unfolds on `cons`: `ζ(p :: X) = coeff_w(label p) · ζ(X)`. -/
@[simp] theorem activity_cons {L : Lattice} (w : Q') (p : L.Plaquette)
    (X : Polymer L) (label : L.Plaquette → Rep) :
    activity w (p :: X) label
      = plaqWeight w label p * activity w X label := rfl

/-- **`activity_nonneg`**: for `0 ≤ w`, the activity is nonnegative
(a product of nonnegative `coeffW` factors). -/
theorem activity_nonneg {L : Lattice} {w : Q'} (hw : (0 : Q') ≤ w)
    (X : Polymer L) (label : L.Plaquette → Rep) :
    (0 : Q') ≤ activity w X label := by
  induction X with
  | nil => show (0 : Q') ≤ (1 : Q'); decide
  | cons p X ih =>
    rw [activity_cons]
    exact Q'.mul_nonneg _ _ (coeffW_nonneg hw (label p)) ih

/-- **`activity_pos`**: for `0 < w`, the activity is strictly positive
(a product of strictly-positive `coeffW` factors; `coeffW w s =
dimQ s · w^{C₄(s)} > 0` for `0 < w`). -/
theorem activity_pos {L : Lattice} {w : Q'} (hw : (0 : Q') < w)
    (X : Polymer L) (label : L.Plaquette → Rep) :
    (0 : Q') < activity w X label := by
  induction X with
  | nil => show (0 : Q') < (1 : Q'); decide
  | cons p X ih =>
    rw [activity_cons]
    exact Q'.mul_pos (FusionResidualBound.coeffW_pos hw (label p)) ih

/-! ## 5. Honest bridge stub to the Kotecký–Preiss interface

`Sheaf.Summability.KPCertificate` is the abstract witness structure for
a KP datum `(ρ, K)` plus a proof of a regime predicate `P`.  The L1
obligation of the cluster expansion is the single-site summability
criterion

    ∑_{X ∋ p}  |ζ(X)| · e^{|X|}  ≤  a(p)            (the KP / L1 bound)

over the polymer model built above: the sum ranges over connected
polymers `X` containing a fixed plaquette `p` satisfying the
`linkConstraint`, weighted by `activity` and the `size`-exponential.

We expose this connection as a well-typed PREDICATE + statement
SIGNATURE only.  We do NOT prove it; the proof (small-`w`
Haar-cancellation ⇒ geometric activity decay ⇒ summability) is Wave 2.
-/

/-- The single-plaquette KP summand `|ζ(X)| · e^{|X|}` is what the L1
criterion sums over connected polymers `X ∋ p`.  Here we expose only
its activity factor (the `e^{|X|}` weight and the sum-over-polymers are
Wave 2 once a polymer enumeration is in place); for `0 ≤ w` the summand
factor is nonnegative, so `|ζ(X)| = ζ(X)`. -/
def kpSummandActivity {L : Lattice} (w : Q') (X : Polymer L)
    (label : L.Plaquette → Rep) : Q' := activity w X label

/-- **The L1 / Kotecký–Preiss obligation — STATEMENT SIGNATURE ONLY
(Wave 2).**

This is the well-typed Prop that the cluster expansion must discharge:
for a fixed plaquette `p` and a `Q'` budget `a`, the cluster sum of
`activity`-weighted, `size`-penalized connected polymers containing `p`
(those satisfying the `linkConstraint`) is bounded by `a`.

Because no constructive polymer enumeration exists yet, we state the
obligation *abstractly* over a supplied finite index family
`fam : Nat → Polymer L` and its length `n` (the placeholder for "the
connected polymers `X ∋ p`"); the genuine enumeration, the `e^{|X|}`
weight, and the PROOF are Wave 2.  `KPObligation` is the SIGNATURE the
Wave-2 theorem will inhabit — it is deliberately left as a hypothesis
to be supplied, never proved here. -/
def KPObligation {L : Lattice} (w : Q') (label : L.Plaquette → Rep)
    (fam : Nat → Polymer L) (n : Nat) (a : Q') : Prop :=
  YMGap.Constructive.RationalTail.finSum
    (fun i => kpSummandActivity w (fam i) label) n ≤ a

/-- **Honest bridge**: from a supplied (Wave-2) proof of the
`KPObligation` we can package a `Sheaf.KPCertificate` over `Q'` for the
predicate `P ρ K := KPObligation … K` (the budget `a` plays the role of
the amplitude `K`; `ρ` is the decay-rate witness, here recorded as the
weight `w`).

This is a re-PACKAGING, not a proof: it consumes a `KPObligation`
witness and produces the abstract certificate.  It exists to show the
polymer model's outputs (`activity`, `size`, `linkConstraint`,
`KPObligation`) are exactly the inputs `Sheaf.Summability` expects;
inhabiting `KPObligation` is Wave 2. -/
def toKPCertificate {L : Lattice} (w : Q') (label : L.Plaquette → Rep)
    (fam : Nat → Polymer L) (n : Nat) (a : Q')
    (h : KPObligation w label fam n a) :
    YMGap.Sheaf.KPCertificate Q'
      (fun _ρ K => KPObligation w label fam n K) where
  rho := w
  K := a
  satisfies := h

/-! ## 6. Documentation: DEFINED vs Wave-2

DEFINED in this L0b structure module:

  * `Lattice` (Link / Plaquette / decidable `boundary`) + `Adjacent`;
    `toyLattice` sanity witness;
  * `Polymer`, `size` (+ `size_nonneg`, `size_nil`, `size_cons`,
    `size_append`), `mem`;
  * `ChainConn` (+ `trans`), `connected` (+ `connected_singleton`);
  * `Rep`, `fusesToTrivial` (+ `fusesToTrivial_iff_eq`,
    `fusesToTrivial_decidable`), `linkConstraint`;
  * `plaqWeight`, `activity` (+ `activity_nil`, `activity_cons`,
    `activity_nonneg`, `activity_pos`);
  * the KP bridge stub `kpSummandActivity`, `KPObligation` (signature),
    `toKPCertificate` (re-packaging).

NAMED but NOT done (Wave 2 — NOT faked here):

  * the theorem that `linkConstraint` + strong coupling (`w` small)
    forces geometric activity decay (the Haar-cancellation
    CONSEQUENCE);
  * a constructive enumeration of "connected polymers `X ∋ p`" and the
    `e^{|X|}` weighting needed to make `KPObligation` the literal KP
    criterion;
  * the PROOF of `KPObligation` (the L1 summability bound);
  * volume-uniformity and convergence of the cluster sum.

This module is the polymer-model STRUCTURE (the missing combinatorial
object): definitions and basic lemmas only.  It is NOT the
convergence / Haar-cancellation theorems, NOT the cluster expansion,
and NOT a 4D Yang–Mills mass gap. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms Polymer.size_nonneg
#print axioms Polymer.size_append
#print axioms Polymer.size_cons
#print axioms Polymer.ChainConn.trans
#print axioms Polymer.connected_singleton
#print axioms fusesToTrivial_iff_eq
#print axioms fusesToTrivial_decidable
#print axioms activity_nonneg
#print axioms activity_pos
#print axioms toKPCertificate

end YMGap.Continuum.PolymerModel
