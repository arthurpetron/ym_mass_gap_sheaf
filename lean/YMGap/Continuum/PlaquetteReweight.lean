/-
Track B / E2 — the **plaquette-coupled (interacting) finite-volume
functional**, taken one genuine step beyond the decoupled product functional
(`E2ProductFunctional.prodFunctional`).

The interacting finite-volume state is the *reweighted* free measure

    E_β(o) = E_⊗(o · W) / Z ,     W = e^{−S_plaq},     Z = E_⊗(W) > 0,

where `W` is the (positive) plaquette Boltzmann weight and `Z` is the
partition function.  The decoupled `E_⊗` is done; the new content here is
the **reweighting**: that dividing a positive normalized functional by a
positive weight with positive normalization yields again a positive
normalized functional.  This is exactly *why the interacting measure stays
a state*, and it is reusable.

# What is genuine here (constructed / proved)

  * `Q'.recip` — the multiplicative inverse of a STRICTLY POSITIVE `Q'`
    (swap numerator/denominator), with
      - `recip_pos`         : `0 < z → 0 < recip z`,
      - `mul_recip_eqv_one` : `0 < z → (z * recip z) ≃ 1`,
      - `recip_mul_eqv_one` : `0 < z → (recip z * z) ≃ 1`.
    A genuine constructive reciprocal on the positive cone (no `Classical`,
    no Mathlib field).

  * `Reweight A` — a **reweighting datum** over a base functional: the
    weighted expectation `Ew : A.carrier → Q'` (morally `o ↦ μ(W·o)`), the
    partition function `Z`, and the three hypotheses that pin down exactly
    what reweighting positivity needs:
      - `Ew_one  : Ew A.one = Z`        (`Z = μ(W·1) = μ(W)`),
      - `Z_pos   : 0 < Z`              (partition-function positivity),
      - `Ew_pos  : 0 ≤ Ew (a*·a)`      (the weighted form is positive).
    `Ew_pos` is the genuine analytic input (in the real theory it is the
    Wilson-action reflection positivity, OS2); here it is a hypothesis, and
    the lemma below shows it is *all* that is needed.

  * `Reweight.functional : ProbFunctional A` — **the reweighted state**
    `E_β(o) = Ew(o) · recip(Z)`, proved to be a genuine `ProbFunctional`:
      - `normalized` : `E_β 1 = Z · recip Z = 1`  (uses `mul_recip_eqv_one`;
        the equality is via the `Q'`-`eqv` normalization helper below — see
        `Reweight.functional_normalized`),
      - `positive`   : `0 ≤ E_β(a*·a) = Ew(a*·a) · recip Z`  (product of two
        nonnegatives).
    NOTE: `ProbFunctional.normalized` demands a *strict* `Q'` equality
    `E 1 = 1`; the reweighting normalization is only `≃ 1` (the unital
    collapse `Z · recip Z ≃ 1` is `.eqv`, not `rfl`).  We therefore CANNOT
    in general land a bare `ProbFunctional` whose `E` is the literal
    `Ew(o)·recip Z` while also satisfying the strict `normalized` field — so
    we expose the honest pair: the positive functional `Reweight.Eβ` plus
    the proved `Reweight.functional_normalized : (Eβ 1).eqv 1` and
    `Reweight.functional_positive`.  When the datum additionally provides a
    *strict* normalization (`Ew_one_recip_strict`), `Reweight.functional`
    upgrades it to a genuine `ProbFunctional`.

  * `prodReweight` — a concrete inhabitant: reweighting the trivial product
    functional by the trivial (all-ones) weight `W ≡ 1`, `Z = 1`, recovering
    a genuine `ProbFunctional` (so the construction is inhabitable, not a
    `True`/`Unit` placeholder).

# What this is / is NOT

This is the abstract reweighting *state* law — genuine and reusable.  It is
NOT the construction of the actual SU(2) plaquette weight `e^{−S_plaq}` as a
`Q'`/`CReal` observable, and `Ew_pos` (the weighted-form positivity) is an
*input hypothesis* here, NOT the proved Wilson reflection positivity.  See
the OPEN list in `docs/plaquette-notes.md`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (the latter where `Int`/`omega` and
`Quot`-backed `Q'` equalities enter).  No `Classical.*`, no `sorryAx`, no
`native_decide`.
-/

import YMGap.Continuum.E2ProductFunctional
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.PlaquetteReweight

open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.E2ProductFunctional
open YMGap.Constructive

/-! ## A constructive reciprocal on the positive cone of `Q'`

`Q'` has no field structure (no division), but a STRICTLY POSITIVE rational
`z = n/d` (`n > 0`, `d > 0`) has an honest multiplicative inverse `d/n`,
obtained by swapping numerator and denominator.  We build it via `mkPos`
(its denominator must be a positive `Nat`, which `z.num.toNat` is, since
`z.num > 0`). -/

/-- The multiplicative inverse of a strictly positive `z = n/d`: `d/n`.
Total: the swapped denominator `z.num.toNat` is clamped to `≥ 1` (so `mkPos`
is well-defined for any `z`); the inverse law holds only for `0 < z` (where
the clamp is inert, since `z.num > 0 ⇒ z.num.toNat ≥ 1`). -/
def recip (z : Q') : Q' :=
  Q'.mkPos (z.den : Int) (Nat.max 1 z.num.toNat)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 z.num.toNat))

theorem recip_num (z : Q') : (recip z).num = (z.den : Int) := rfl

theorem recip_den (z : Q') : (recip z).den = Nat.max 1 z.num.toNat :=
  Q'.mkPos_den _ _ _

/-- For `0 < z`, the clamp is inert: `max 1 z.num.toNat = z.num.toNat`. -/
theorem recip_den_of_pos {z : Q'} (h : (0 : Q') < z) :
    (recip z).den = z.num.toNat := by
  rw [recip_den]
  have hn : 0 < z.num := CReal.num_pos_of_pos h
  have : 1 ≤ z.num.toNat := by omega
  exact Nat.max_eq_right this

/-- `0 < recip z` when `0 < z` (its numerator `z.den > 0`). -/
theorem recip_pos {z : Q'} (_h : (0 : Q') < z) : (0 : Q') < recip z := by
  apply CReal.pos_of_num_pos
  rw [recip_num]
  exact_mod_cast Q'.den_pos z

/-- `z.num.toNat` cast back to `Int` recovers `z.num` when `0 < z`. -/
theorem toNat_cast_of_pos {z : Q'} (h : (0 : Q') < z) :
    ((z.num.toNat : Nat) : Int) = z.num := by
  have hn : 0 < z.num := CReal.num_pos_of_pos h
  exact Int.toNat_of_nonneg (Int.le_of_lt hn)

/-- **The reciprocal law** `z · recip z ≃ 1` for `0 < z`.  Unfolding `eqv`:
`(z · recip z).num · 1 = 1 · (z · recip z).den`, i.e.
`z.num · z.den = 1 · (z.den · z.num.toNat)`, which holds since
`z.num.toNat = z.num` (positive). -/
theorem mul_recip_eqv_one {z : Q'} (h : (0 : Q') < z) :
    (z * recip z).eqv 1 := by
  -- eqv to 1 : (z*recip z).num * (1).den = (1).num * (z*recip z).den
  show (z * recip z).num * ((1 : Q').den : Int)
      = (1 : Q').num * ((z * recip z).den : Int)
  -- (z*recip z).num = z.num * (recip z).num = z.num * z.den
  -- (z*recip z).den = z.den * (recip z).den = z.den * z.num.toNat
  show (z.num * (recip z).num) * (1 : Int)
      = (1 : Int) * ((z.den * (recip z).den : Nat) : Int)
  rw [recip_num, recip_den_of_pos h]
  -- goal: (z.num * (z.den : Int)) * 1 = 1 * ((z.den * z.num.toNat : Nat) : Int)
  push_cast
  rw [toNat_cast_of_pos h]
  -- (z.num * z.den) * 1 = 1 * (z.den * z.num)
  rw [Int.mul_one, Int.one_mul, Int.mul_comm z.num (z.den : Int)]

/-- `recip z · z ≃ 1` for `0 < z` (commuted form). -/
theorem recip_mul_eqv_one {z : Q'} (h : (0 : Q') < z) :
    (recip z * z).eqv 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (recip z) z) (mul_recip_eqv_one h)

/-! ## The reweighting datum and the reweighted state -/

/-- A **reweighting datum** over an observable algebra `A`: the weighted
expectation `Ew` (`o ↦ μ(W·o)` in the model), its value `Z = Ew 1` at the
unit (the partition function), `Z > 0`, and positivity of the weighted form
on `a*·a`.  `Ew_pos` is the genuine analytic input (Wilson reflection
positivity in the real theory). -/
structure Reweight (A : ObsAlg) where
  /-- The weighted (unnormalized) expectation `o ↦ μ(W·o)`. -/
  Ew : A.carrier → Q'
  /-- The partition function `Z`. -/
  Z : Q'
  /-- `Z = Ew(W·1) = Ew 1`. -/
  Ew_one : Ew A.one = Z
  /-- Partition-function positivity (`Z > 0`). -/
  Z_pos : (0 : Q') < Z
  /-- The weighted form is positive on `a*·a` (the reflection-positivity
  input). -/
  Ew_pos : ∀ a, (0 : Q') ≤ Ew (A.mul (A.star a) a)

/-- **The reweighted state** `E_β(o) = Ew(o) · recip Z`. -/
def Reweight.Eβ {A : ObsAlg} (r : Reweight A) (o : A.carrier) : Q' :=
  r.Ew o * recip r.Z

/-- **Positivity of the reweighted state**: `0 ≤ E_β(a*·a)`.  Product of the
nonnegative weighted form `Ew(a*·a)` and the positive reciprocal `recip Z`. -/
theorem Reweight.functional_positive {A : ObsAlg} (r : Reweight A) (a : A.carrier) :
    (0 : Q') ≤ r.Eβ (A.mul (A.star a) a) := by
  show (0 : Q') ≤ r.Ew (A.mul (A.star a) a) * recip r.Z
  exact Q'.mul_nonneg _ _ (r.Ew_pos a) (Q'.le_of_lt (recip_pos r.Z_pos))

/-- **Normalization of the reweighted state (up to `eqv`)**: `E_β 1 ≃ 1`.
`E_β 1 = Ew 1 · recip Z = Z · recip Z ≃ 1`.  The collapse `Z·recip Z ≃ 1`
is `eqv`, not `rfl`, hence the `eqv` here. -/
theorem Reweight.functional_normalized {A : ObsAlg} (r : Reweight A) :
    (r.Eβ A.one).eqv 1 := by
  show (r.Ew A.one * recip r.Z).eqv 1
  rw [r.Ew_one]
  exact mul_recip_eqv_one r.Z_pos

/-! ## Upgrading to a genuine `ProbFunctional` with a strict normalization

`ProbFunctional.normalized` requires a *strict* `Q'` equality `E 1 = 1`.
The reweighting gives only `≃ 1` (the unital collapse is `eqv`).  A datum
that additionally certifies a strict normalization (`Ew_one_strict :
Ew A.one * recip Z = 1`) packages into a genuine `ProbFunctional`.  The
trivial/decoupled inhabitant below supplies exactly such a strict
certificate (`Z = 1`, `recip 1 = 1`, `1 · 1 = 1` definitionally). -/

/-- A **strictly-normalized** reweighting datum: a `Reweight` whose
normalization holds as a literal `Q'` equality.  This is what lets the
reweighted state be a bona-fide `ProbFunctional`. -/
structure ReweightStrict (A : ObsAlg) extends Reweight A where
  /-- `Ew 1 · recip Z = 1` as a STRICT `Q'` equality. -/
  Ew_one_recip_strict : toReweight.Eβ A.one = 1

/-- **The reweighted functional as a genuine `ProbFunctional`** (when the
normalization is strict): positive on `a*·a`, normalized at the unit. -/
def ReweightStrict.functional {A : ObsAlg} (r : ReweightStrict A) :
    ProbFunctional A where
  E := r.toReweight.Eβ
  normalized := r.Ew_one_recip_strict
  positive := r.toReweight.functional_positive

theorem ReweightStrict.functional_E {A : ObsAlg} (r : ReweightStrict A)
    (o : A.carrier) : (r.functional).E o = r.toReweight.Ew o * recip r.Z := rfl

/-! ## Concrete inhabitant: the trivially-coupled product (W ≡ 1, Z = 1)

The decoupled product functional `prodFunctional` reweighted by the trivial
weight `W ≡ 1`: the weighted expectation is the free expectation itself,
`Z = E_⊗(1) = 1`, and `recip 1 = 1` definitionally, so `E_β = E_⊗` is a
genuine `ProbFunctional`.  This exhibits the reweighting machinery on a real
(non-placeholder) object: the interacting state at *zero* coupling IS the
free state. -/

/-- `recip 1 = 1` strictly: `recip (n=1,d=1)` swaps to `(d=1)/(n.toNat=1)`,
which is structurally `1`. -/
theorem recip_one : recip (1 : Q') = 1 := by
  show Q'.mkPos ((1 : Q').den : Int) (Nat.max 1 ((1 : Q').num.toNat)) _ = 1
  -- (1 : Q').den = 1, (1 : Q').num = 1, toNat = 1, max 1 1 = 1
  rfl

/-- The trivially-coupled reweighting datum over the `n`-edge trivial product:
`Ew = E_⊗`, `Z = 1`.  Strict normalization since `recip 1 = 1` and `E_⊗ 1 = 1`
both hold definitionally. -/
def prodReweightStrict (n : Nat) : ReweightStrict (prodAlg trivFamily n) where
  Ew := (trivProdFunctional n).E
  Z := 1
  Ew_one := (trivProdFunctional n).normalized
  Z_pos := by decide
  Ew_pos := (trivProdFunctional n).positive
  Ew_one_recip_strict := by
    show (trivProdFunctional n).E (prodAlg trivFamily n).one * recip 1 = 1
    rw [(trivProdFunctional n).normalized, recip_one]
    rfl

/-- The trivially-coupled (zero-coupling) interacting state is a genuine
`ProbFunctional` — and equals the free product functional on every
observable. -/
def prodReweight (n : Nat) : ProbFunctional (prodAlg trivFamily n) :=
  (prodReweightStrict n).functional

/-- `v * 1 = v` strictly on `Q'` (`1 = ⟨1,0⟩`: `num*1 = num`, `den*1−1 = denPred`). -/
theorem q_mul_one (v : Q') : v * (1 : Q') = v := by
  cases v with
  | mk num denPred =>
    show (Q'.mul ⟨num, denPred⟩ 1) = ⟨num, denPred⟩
    show (⟨num * (Int.ofNat 1), (denPred + 1) * 1 - 1⟩ : Q') = ⟨num, denPred⟩
    congr 1
    · simp
    · omega

/-- At zero coupling the interacting expectation IS the free expectation:
`E_β(o) = E_⊗(o)` (strictly), since `recip 1 = 1` and `v · 1 = v`. -/
theorem prodReweight_eq_free (n : Nat) (o : (prodAlg trivFamily n).carrier) :
    (prodReweight n).E o = (trivProdFunctional n).E o := by
  show (trivProdFunctional n).E o * recip 1 = (trivProdFunctional n).E o
  rw [recip_one]
  exact q_mul_one _

/-! ## A NONTRIVIAL-`Z` reweighting (exercising the genuine reciprocal)

A scalar weight `W ≡ w` with `w > 0` (not necessarily `1`): `Ew(o) = w · E(o)`
on the trivial algebra, `Z = w`.  Then `E_β(o) = w · 1 · recip w ≃ 1` and the
normalization `E_β 1 ≃ 1` genuinely uses `mul_recip_eqv_one` at `w ≠ 1` — the
reciprocal is doing real work.  This is the simplest reweighting where the
partition function is not `1`. -/

/-- A constant-weight reweighting datum on the trivial algebra: `Ew(o) = w`,
`Z = w`, for any `w > 0`.  (`E` on `trivAlg` is constant `1`, so `Ew = w·1`.) -/
def scalarReweight {w : Q'} (hw : (0 : Q') < w) : Reweight trivAlg where
  Ew := fun _ => w
  Z := w
  Ew_one := rfl
  Z_pos := hw
  Ew_pos := fun _ => Q'.le_of_lt hw

/-- The constant-weight interacting state is normalized up to `eqv`:
`E_β 1 = w · recip w ≃ 1`, with `w` the (arbitrary positive) partition
function — the reciprocal genuinely normalizes a nontrivial `Z`. -/
theorem scalarReweight_normalized {w : Q'} (hw : (0 : Q') < w) :
    ((scalarReweight hw).Eβ trivAlg.one).eqv 1 :=
  (scalarReweight hw).functional_normalized

/-- Its positivity: `0 ≤ E_β(a*·a) = w · recip w` (both factors positive). -/
theorem scalarReweight_positive {w : Q'} (hw : (0 : Q') < w) (a : trivAlg.carrier) :
    (0 : Q') ≤ (scalarReweight hw).Eβ (trivAlg.mul (trivAlg.star a) a) :=
  (scalarReweight hw).functional_positive a

end YMGap.Continuum.PlaquetteReweight

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PlaquetteReweight.recip_pos
#print axioms YMGap.Continuum.PlaquetteReweight.mul_recip_eqv_one
#print axioms YMGap.Continuum.PlaquetteReweight.recip_mul_eqv_one
#print axioms YMGap.Continuum.PlaquetteReweight.Reweight.functional_positive
#print axioms YMGap.Continuum.PlaquetteReweight.Reweight.functional_normalized
#print axioms YMGap.Continuum.PlaquetteReweight.ReweightStrict.functional
#print axioms YMGap.Continuum.PlaquetteReweight.prodReweight
#print axioms YMGap.Continuum.PlaquetteReweight.prodReweight_eq_free
#print axioms YMGap.Continuum.PlaquetteReweight.scalarReweight_normalized
#print axioms YMGap.Continuum.PlaquetteReweight.scalarReweight_positive
