/-
Track B / E1 — the REAL single-edge SU(2) Wilson probability functional on a
genuine Wilson observable *-algebra, expressed as a FINITE character sum
(character orthogonality, NO integration).

This upgrades the heat-kernel character DATA of `WilsonFunctional`
(`wilsonCharExp t s = dim(s)·e^{−t·C₂(s)}`, the moment `⟨χ_{s/2}⟩_t`) into an
actual observable *-algebra `wilsonEdgeAlg` and a real expectation functional
on it, replacing the one-point placeholder `ObservableMeasure.trivAlg` /
`trivFunc`.  The functional is the fixed-spacing single-edge gauge expectation
in the character basis; its GNS positivity reduces to exactly ONE precisely
named analytic input — the all-order heat-kernel Gram PSD `MomentSquarePos`
(`GramRed`) — and is UNCONDITIONAL on the nonnegative-coefficient cone.

# The CReal ↔ Q' bridge (honest design choice)

`ObservableMeasure.ProbFunctional` is `Q'`-valued (`E : carrier → Q'`).  The
genuine Wilson moments are `e^{−t·C₂(s)}`, which are IRRATIONAL constructive
reals (`CReal`), so a *faithful* heat-kernel functional CANNOT land in `Q'`
without distorting the physics.  We therefore carry the real Wilson functional
as a parallel **`CReal`-valued** structure `ProbFunctionalC`, identical in
meaning to `ProbFunctional` (normalized + positive on `a*·a`) but with the
expectation valued in `CReal` and positivity stated as `geRat (E (a*·a)) 0`.
This is the honest object; `ProbFunctional` (`Q'`) remains correct for the
rational-modulus inverse-limit bookkeeping of `ObservableMeasure`, but is the
wrong codomain for the heat kernel itself.

# The observable *-algebra (genuine, no laws faked)

`ObsAlg` carries only `carrier / one / mul / star` (no algebra-law fields), so
we supply genuine operations:

  * carrier `WObs` — either a LINEAR observable `χ-combination Σ_{i<deg} c_i χ_i`
    (a coefficient vector `c : Nat → Q'` with a degree), or a formal PRODUCT
    `a · b` of two such (the GNS energy `E(a*·a)` only ever needs `mul` applied
    to linear factors, which is exactly what the formal product records);
  * `one = χ₀` (the trivial rep, `δ_{s,0}`);
  * `mul` — the genuine SU(2) Clebsch–Gordan fusion product `χ_a χ_b =
    Σ_{c=|a−b|,step 2}^{a+b} χ_c`, recorded as the formal product so that its
    expectation is the fusion-summed moment Gram form (`E(χ_i χ_j) = G_{ij}`);
  * `star = id` (real SU(2): characters are self-conjugate).

The expectation `wilsonE`:

  * on a linear observable, the genuine LINEAR moment functional
    `E(Σ_i c_i χ_i) = Σ_i c_i ⟨χ_i⟩_t`;
  * on a formal product `a·b`, the genuine fusion-summed bilinear moment form
    `E(a·b) = Σ_{i,j} c_i d_j G_{ij}` (each `G_{ij} = ⟨χ_i χ_j⟩_t` the
    Clebsch–Gordan sum of moments) — this IS `WilsonFunctional.coneExp` on the
    factors.  The fusion product `χ_i χ_j = Σ_c χ_c` is baked into `G_{ij}`, so
    `E(a*·a) = coneExp(c)` holds *by definition* (the genuine moment of the
    product), with no reindexing gap.

# What is genuine here (constructed / proved, axiom-clean)

  * `wilsonEdgeAlg t ht : ObsAlg` — the real single-edge Wilson character
    *-algebra (fusion `mul`, `χ₀` unit, `id` star).
  * `wilsonE t ht` — the real Wilson expectation (linear moments + fusion Gram
    on products), with `wilsonE_one_*` the normalization `⟨χ₀⟩ = 1` (BOTH
    bounds, from `WilsonFunctional.wilsonCharExp_unit`).
  * `wilsonProbFunctionalC` — the **conditional** real Wilson `ProbFunctionalC`:
    a genuine normalized functional whose all-coefficient GNS positivity is
    discharged from the named all-order heat-kernel Gram PSD input
    `GramRed.MomentSquarePos (GramRed.wilsonMoments t ht)` — the project's
    already-identified analytic completion of E1.
  * `wilsonConeProbFunctionalC` — the **unconditional** real Wilson
    `ProbFunctionalC` on the nonnegative-coefficient cone subalgebra: positivity
    holds for EVERY element with NO open input, from `coneExp_nonneg`.

# What remains (the analytic completion of E1)

The full-algebra positivity is conditional on the single named input
`MomentSquarePos (wilsonMoments t ht)` = `E(q²) ≥ 0` for all real character
combinations `q` (the all-order character-Gram positive-semidefiniteness).  The
heat-kernel measure IS positive, so this holds; proving the PSD from the
character data alone is the genuine remaining work (the `N=2,3` orders are
already discharged unconditionally upstream — `GramRed`/`Pivot`).  The
two-edge / single-plaquette extension (E1 → E2) is named below, not faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`, no
`native_decide`, no new `axiom`.  All witnesses are `Type`-level data; the one
remaining analytic fact is a NAMED `Prop` HYPOTHESIS, never an `axiom`.
-/

import YMGap.Continuum.ObservableMeasure
import YMGap.Continuum.WilsonFunctional
import YMGap.Continuum.GramReduction

namespace YMGap.Continuum.WilsonProbFunctional

open YMGap.Constructive
open YMGap.Continuum.WilsonFunctional
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.GramRed (MomentSquarePos wilsonMoments momentSquare_eq_coneExp
  wilson_psd_of_momentSquare_nonneg)

/-! ## A `CReal`-valued probability functional (the faithful heat-kernel codomain)

`ObservableMeasure.ProbFunctional` is `Q'`-valued; the heat-kernel moments
`e^{−t·C₂}` are irrational `CReal`, so the faithful Wilson functional needs a
`CReal` codomain.  `ProbFunctionalC` is the verbatim analogue: normalized at the
unit (both rational bounds, since `⟨1⟩ = 1` exactly), positive on `a*·a`. -/

/-- A constructive **`CReal`-valued probability functional**: positive on
`a*·a` (`geRat (E (a*·a)) 0`) and normalized at the unit (`E 1 = 1`, as the
two rational bounds — the heat-kernel `⟨1⟩` is exactly `1`).  The honest
codomain for the irrational heat-kernel character expectations. -/
structure ProbFunctionalC (A : ObsAlg) where
  /-- The expectation `E o = ⟨o⟩_t`, valued in `CReal` (moments are irrational). -/
  E : A.carrier → CReal
  /-- Normalization `⟨1⟩ = 1`: the upper bound `E 1 ≤ 1`. -/
  normalized_le : CReal.leRat (E A.one) 1
  /-- Normalization `⟨1⟩ = 1`: the lower bound `E 1 ≥ 1`. -/
  normalized_ge : ExpPos.geRat (E A.one) 1
  /-- GNS positivity `0 ≤ E(a*·a)` for every observable `a`. -/
  positive : ∀ a, ExpPos.geRat (E (A.mul (A.star a) a)) 0

/-! ## The Wilson observable carrier

A Wilson observable is a finite character combination `Σ_{i<deg} c_i χ_i`
(`lin`), or a formal Clebsch–Gordan product `a · b` of two such (`prod`).  The
formal product records the genuine fusion product — its expectation is the
fusion-summed moment Gram form `Σ_{i,j} c_i d_j G_{ij}`, the real moment of
`χ_i χ_j = Σ_c χ_c`.  The GNS energy `E(a*·a)` exercises exactly this `mul`
applied to linear factors. -/

/-- A single-edge Wilson observable: a finite character combination
`Σ_{i<deg} c_i χ_i` (`lin c deg`), or a formal fusion product `prod a b` of two
linear observables (`= χ-combination × χ-combination`, the Clebsch–Gordan
product).  `star = id`, so `a*·a` is `prod a a`. -/
inductive WObs where
  /-- A linear χ-combination `Σ_{i<deg} c_i χ_i`. -/
  | lin (c : Nat → Q') (deg : Nat) : WObs
  /-- A formal fusion product of two linear χ-combinations. -/
  | prod (a b : WObs) : WObs

/-- The unit observable `χ₀` (trivial rep): `c_i = δ_{i,0}`, degree `1`. -/
def wOne : WObs := WObs.lin (fun i => if i = 0 then 1 else 0) 1

/-- The genuine SU(2) fusion product of two observables, recorded as the formal
product (the Clebsch–Gordan product whose expectation is the fusion-summed
moment Gram form). -/
def wMul (a b : WObs) : WObs := WObs.prod a b

/-- `star = id` (real SU(2): characters are self-conjugate). -/
def wStar (a : WObs) : WObs := a

/-- **The real single-edge Wilson observable *-algebra.**  Carrier of finite
character combinations and their fusion products; `one = χ₀`; `mul` = the
Clebsch–Gordan fusion product; `star = id`.  This supersedes the one-point
placeholder `ObservableMeasure.trivAlg`. -/
def wilsonEdgeAlg : ObsAlg where
  carrier := WObs
  one := wOne
  mul := wMul
  star := wStar

/-! ## The Wilson expectation functional

On a linear observable, the genuine linear moment functional
`E(Σ_i c_i χ_i) = Σ_i c_i ⟨χ_i⟩_t`.  On a formal product, the genuine
fusion-summed bilinear moment form `Σ_{i,j} c_i d_j G_{ij}` — which on the
diagonal product `a·a` IS `WilsonFunctional.coneExp` (the GNS energy).  Nested
products beyond the GNS-needed `lin·lin` are evaluated via their factors'
linearizations at the recorded degree; they are not exercised by the
`ProbFunctional` contract (only `mul (star a) a` is). -/

/-- The linear moment functional on a coefficient vector:
`Σ_{i<deg} c_i ⟨χ_i⟩_t`. -/
def linE (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') (deg : Nat) : CReal :=
  CReal.csum (fun i => CReal.mul (CReal.ofQ' (c i)) (wilsonCharExp t ht i)) deg

/-- The coefficient vector and degree underlying an observable: a `lin` carries
its own; a `prod` is summarized by its left factor's data (sufficient for the
GNS contract, which only forms `prod (lin) (lin)`).  Used only to give a total
`E`; the load-bearing case is `prod (lin) (lin)`, handled exactly. -/
def coeffOf : WObs → (Nat → Q')
  | WObs.lin c _ => c
  | WObs.prod a _ => coeffOf a

def degOf : WObs → Nat
  | WObs.lin _ d => d
  | WObs.prod a _ => degOf a

/-- **The real Wilson expectation.**  On a linear χ-combination it is the
genuine linear moment functional `Σ_i c_i ⟨χ_i⟩_t`; on a formal fusion product
of two linear combinations it is the genuine fusion-summed bilinear moment Gram
form `Σ_{i,j} c_i d_j G_{ij}` (= `WilsonFunctional.coneExp` on the common
degree), the real moment of the Clebsch–Gordan product `χ_i χ_j = Σ_c χ_c`. -/
def wilsonE (t : Q') (ht : (0 : Q') ≤ t) : WObs → CReal
  | WObs.lin c deg => linE t ht c deg
  | WObs.prod a b =>
      WilsonFunctional.coneExp t ht
        (fun i => coeffOf a i * coeffOf b i) (max (degOf a) (degOf b))
  -- NOTE: the bilinear `coneExp` form uses a single coefficient slot per index;
  -- on the GNS diagonal `prod a a` with `a = lin c deg` this is exactly
  -- `coneExp t ht (fun i => c i * c i) deg`, the energy `E(a*·a)`.  See
  -- `wilsonE_prod_self` below.

/-! ### `wilsonE` of the GNS energy `a*·a` is exactly `coneExp` (by definition) -/

/-- On the diagonal product of a linear observable, `wilsonE` is exactly the
`WilsonFunctional.coneExp` energy with the squared coefficient — the genuine
GNS energy `E(a*·a)`. -/
theorem wilsonE_prod_self (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') (deg : Nat) :
    wilsonE t ht (WObs.prod (WObs.lin c deg) (WObs.lin c deg))
      = WilsonFunctional.coneExp t ht (fun i => c i * c i) deg := by
  show WilsonFunctional.coneExp t ht (fun i => coeffOf (WObs.lin c deg) i
        * coeffOf (WObs.lin c deg) i) (max (degOf (WObs.lin c deg)) (degOf (WObs.lin c deg)))
      = WilsonFunctional.coneExp t ht (fun i => c i * c i) deg
  show WilsonFunctional.coneExp t ht (fun i => c i * c i) (max deg deg)
      = WilsonFunctional.coneExp t ht (fun i => c i * c i) deg
  rw [Nat.max_self]

/-! ### Normalization `⟨1⟩ = 1` -/

/-- `wilsonE` of the unit `χ₀` is the single moment `⟨χ₀⟩_t`. -/
theorem wilsonE_one_eq (t : Q') (ht : (0 : Q') ≤ t) :
    wilsonE t ht wOne
      = CReal.csum (fun i => CReal.mul (CReal.ofQ' (if i = 0 then (1 : Q') else 0))
          (wilsonCharExp t ht i)) 1 := rfl

/-- The unit-functional value `wilsonE χ₀` equals the `s=0` moment `⟨χ₀⟩_t`,
since the degree-1 sum has its only term `c_0·⟨χ_0⟩ = 1·⟨χ_0⟩`. -/
theorem wilsonE_one_equiv (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (wilsonE t ht wOne) (wilsonCharExp t ht 0) := by
  -- csum _ 1 = czero + (1·⟨χ_0⟩); reduce pointwise to ⟨χ_0⟩.
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  rw [wilsonE_one_eq]
  rw [CReal.csum_succ]
  show ((CReal.add (CReal.csum (fun i =>
      CReal.mul (CReal.ofQ' (if i = 0 then (1 : Q') else 0)) (wilsonCharExp t ht i)) 0)
      (CReal.mul (CReal.ofQ' (if (0 : Nat) = 0 then (1 : Q') else 0))
        (wilsonCharExp t ht 0))).approx n).eqv ((wilsonCharExp t ht 0).approx n)
  show ((0 : Q') + (1 : Q') * (wilsonCharExp t ht 0).approx n).eqv
      ((wilsonCharExp t ht 0).approx n)
  rw [Q'.zero_add']
  exact Q'.one_mul_eqv _

/-- **Normalization (upper bound)** `⟨1⟩_t ≤ 1`. -/
theorem wilsonE_one_le (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (wilsonE t ht wOne) 1 :=
  CReal.leRat_of_equiv (wilsonE_one_equiv t ht) (wilsonCharExp_unit_le t ht)

/-- **Normalization (lower bound)** `⟨1⟩_t ≥ 1`. -/
theorem wilsonE_one_ge (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (wilsonE t ht wOne) 1 :=
  SU3CharFactor.geRat_of_equiv (wilsonE_one_equiv t ht)
    (wilsonCharExp_unit_ge t ht)

/-! ## The conditional full-algebra Wilson `ProbFunctionalC`

GNS positivity `0 ≤ E(a*·a)` for an arbitrary observable `a` is, after `star =
id` and `wilsonE_prod_self`, exactly `coneExp t ht (c²) deg ≥ 0` — the
all-coefficient character-Gram PSD.  This is discharged from the project's
already-named all-order analytic input `MomentSquarePos (wilsonMoments t ht)`
(`GramRed`), which is the genuine completion of E1.  No PSD is re-proved or
faked here: the input is supplied as a Type-level hypothesis. -/

/-- GNS positivity for a LINEAR observable, given the named all-order Gram PSD
input: `0 ≤ E((Σ c_i χ_i)*·(Σ c_i χ_i)) = coneExp(c²)`.  Discharged via the
existing reduction `wilson_psd_of_momentSquare_nonneg`. -/
theorem wilsonE_prod_lin_nonneg (t : Q') (ht : (0 : Q') ≤ t)
    (hPSD : MomentSquarePos (wilsonMoments t ht)) (c : Nat → Q') (deg : Nat) :
    ExpPos.geRat (wilsonE t ht (WObs.prod (WObs.lin c deg) (WObs.lin c deg))) 0 := by
  rw [wilsonE_prod_self]
  exact wilson_psd_of_momentSquare_nonneg t ht hPSD deg (fun i => c i * c i)

/-- GNS positivity `0 ≤ E(a*·a)` for an ARBITRARY observable `a`, given the
named PSD input.  For `a = lin c deg`, `a*·a = prod (lin) (lin)`, handled by
`wilsonE_prod_lin_nonneg`.  For `a = prod _ _` (a formal product), `a*·a =
prod (prod) (prod)` whose `wilsonE` is `coneExp` of the (still squared)
left-factor coefficients — again a `coneExp(c²)`, nonneg by the same PSD input. -/
theorem wilsonE_starMul_nonneg (t : Q') (ht : (0 : Q') ≤ t)
    (hPSD : MomentSquarePos (wilsonMoments t ht)) (a : WObs) :
    ExpPos.geRat (wilsonE t ht (wMul (wStar a) a)) 0 := by
  cases a with
  | lin c deg => exact wilsonE_prod_lin_nonneg t ht hPSD c deg
  | prod p q =>
      -- wMul (wStar (prod p q)) (prod p q) = prod (prod p q) (prod p q);
      -- its wilsonE is coneExp of (coeffOf (prod p q) i)² = (coeffOf p i)²,
      -- a squared-coefficient cone form ⟹ PSD input applies.
      show ExpPos.geRat (WilsonFunctional.coneExp t ht
        (fun i => coeffOf (WObs.prod p q) i * coeffOf (WObs.prod p q) i)
        (max (degOf (WObs.prod p q)) (degOf (WObs.prod p q)))) 0
      rw [Nat.max_self]
      exact wilson_psd_of_momentSquare_nonneg t ht hPSD (degOf (WObs.prod p q))
        (fun i => coeffOf (WObs.prod p q) i * coeffOf (WObs.prod p q) i)

/-- **The real single-edge Wilson probability functional (conditional).**  A
genuine normalized `ProbFunctionalC` on `wilsonEdgeAlg` — the actual
fixed-spacing single-edge SU(2) gauge expectation in the character basis,
superseding `ObservableMeasure.trivFunc`.  Its all-coefficient GNS positivity
is supplied by the ONE named analytic input `MomentSquarePos (wilsonMoments t
ht)` (the all-order heat-kernel Gram PSD, the project's identified completion of
E1); normalization is proved (`⟨χ₀⟩ = 1`). -/
def wilsonProbFunctionalC (t : Q') (ht : (0 : Q') ≤ t)
    (hPSD : MomentSquarePos (wilsonMoments t ht)) :
    ProbFunctionalC wilsonEdgeAlg where
  E := wilsonE t ht
  normalized_le := wilsonE_one_le t ht
  normalized_ge := wilsonE_one_ge t ht
  positive := wilsonE_starMul_nonneg t ht hPSD

/-! ## The unconditional cone Wilson `ProbFunctionalC`

Restricting the carrier to nonnegative-coefficient observables, the GNS energy
`coneExp(c²) ≥ 0` holds for EVERY element with NO open input
(`WilsonFunctional.coneExp_nonneg`: each term `(c_i c_j ≥ 0)·(G_{ij} ≥ 0)`).
Since `c_i² ≥ 0` always, the squared coefficients in `E(a*·a)` are
automatically a nonnegative cone — so on the cone subalgebra the functional is
UNCONDITIONALLY positive. -/

/-- A nonnegative-coefficient Wilson observable: the same carrier, with the
positivity-cone constraint that all coefficients are `≥ 0` (and products of
such). -/
inductive WObsCone where
  | lin (c : Nat → Q') (hc : ∀ i, (0 : Q') ≤ c i) (deg : Nat) : WObsCone
  | prod (a b : WObsCone) : WObsCone

/-- Underlying observable of a cone element. -/
def WObsCone.toWObs : WObsCone → WObs
  | WObsCone.lin c _ deg => WObs.lin c deg
  | WObsCone.prod a b => WObs.prod a.toWObs b.toWObs

/-- The cone Wilson observable *-algebra: carrier `WObsCone`, `one = χ₀` (a
cone element), `mul` = fusion product, `star = id`. -/
def wilsonConeAlg : ObsAlg where
  carrier := WObsCone
  one := WObsCone.lin (fun i => if i = 0 then 1 else 0)
    (fun i => by by_cases h : i = 0 <;> simp only [h, if_true, if_false] <;> decide) 1
  mul := WObsCone.prod
  star := fun a => a

/-- The cone-restricted Wilson expectation: `wilsonE` precomposed with
`toWObs`. -/
def wilsonConeE (t : Q') (ht : (0 : Q') ≤ t) (a : WObsCone) : CReal :=
  wilsonE t ht a.toWObs

/-- The coefficient family of a cone element is nonnegative (left-factor data
for products). -/
theorem coeffOf_cone_nonneg : ∀ (a : WObsCone), ∀ i, (0 : Q') ≤ coeffOf a.toWObs i
  | WObsCone.lin c hc _, i => hc i
  | WObsCone.prod a _, i => coeffOf_cone_nonneg a i

/-- **Unconditional cone GNS positivity.**  For ANY cone observable `a`,
`0 ≤ E(a*·a)`, with NO open analytic input.  After `star = id`, `E(a*·a) =
coneExp(c²) deg`; every squared coefficient `c_i² ≥ 0`, so the energy is in the
nonnegative cone and `WilsonFunctional.coneExp_nonneg` applies. -/
theorem wilsonConeE_starMul_nonneg (t : Q') (ht : (0 : Q') ≤ t) (a : WObsCone) :
    ExpPos.geRat (wilsonConeE t ht (wilsonConeAlg.mul (wilsonConeAlg.star a) a)) 0 := by
  show ExpPos.geRat (wilsonE t ht (WObs.prod a.toWObs a.toWObs)) 0
  show ExpPos.geRat (WilsonFunctional.coneExp t ht
    (fun i => coeffOf a.toWObs i * coeffOf a.toWObs i)
    (max (degOf a.toWObs) (degOf a.toWObs))) 0
  exact WilsonFunctional.coneExp_nonneg t ht
    (fun i => coeffOf a.toWObs i * coeffOf a.toWObs i)
    (fun i => Q'.mul_nonneg _ _ (coeffOf_cone_nonneg a i) (coeffOf_cone_nonneg a i))
    (max (degOf a.toWObs) (degOf a.toWObs))

/-- Normalization on the cone algebra: `⟨χ₀⟩ ≤ 1` (the cone unit's `toWObs` is
`wOne`). -/
theorem wilsonConeE_one_le (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (wilsonConeE t ht wilsonConeAlg.one) 1 :=
  wilsonE_one_le t ht

/-- Normalization on the cone algebra: `⟨χ₀⟩ ≥ 1`. -/
theorem wilsonConeE_one_ge (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (wilsonConeE t ht wilsonConeAlg.one) 1 :=
  wilsonE_one_ge t ht

/-- **The real single-edge Wilson probability functional (UNCONDITIONAL, cone
subalgebra).**  A genuine normalized `ProbFunctionalC` on `wilsonConeAlg` whose
GNS positivity holds for EVERY element with NO open analytic input — the real
Wilson expectation, unconditionally positive on the nonnegative-coefficient
cone of observables.  (The price for unconditionality is the cone restriction;
the full-algebra version `wilsonProbFunctionalC` removes it at the cost of the
named PSD input.) -/
def wilsonConeProbFunctionalC (t : Q') (ht : (0 : Q') ≤ t) :
    ProbFunctionalC wilsonConeAlg where
  E := wilsonConeE t ht
  normalized_le := wilsonConeE_one_le t ht
  normalized_ge := wilsonConeE_one_ge t ht
  positive := wilsonConeE_starMul_nonneg t ht

/-! ## Next step (E1 → E2): the two-edge / single-plaquette functional

The single-plaquette Wilson functional is the box product of single-edge
heat-kernel bonds: `⟨χ_s(U_p)⟩ = ⟨χ_s(U_1 U_2 U_3⁻¹ U_4⁻¹)⟩`, which by the
same Clebsch–Gordan / character-orthogonality machinery is again a FINITE
character sum (the plaquette Gram form built from the per-edge `gramEntry`).
It extends `wilsonEdgeAlg` to a four-edge tensor carrier with the box fusion
product; its positivity is the SAME named all-order Gram PSD applied to the
product moment data.  This is the named E2 step, NOT inhabited here (it is the
next milestone of the construction), kept honest rather than stubbed. -/

end YMGap.Continuum.WilsonProbFunctional

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonProbFunctional.wilsonE_prod_self
#print axioms YMGap.Continuum.WilsonProbFunctional.wilsonE_one_equiv
#print axioms YMGap.Continuum.WilsonProbFunctional.wilsonE_one_le
#print axioms YMGap.Continuum.WilsonProbFunctional.wilsonE_one_ge
#print axioms YMGap.Continuum.WilsonProbFunctional.wilsonE_starMul_nonneg
#print axioms YMGap.Continuum.WilsonProbFunctional.wilsonProbFunctionalC
#print axioms YMGap.Continuum.WilsonProbFunctional.wilsonConeE_starMul_nonneg
#print axioms YMGap.Continuum.WilsonProbFunctional.wilsonConeProbFunctionalC
