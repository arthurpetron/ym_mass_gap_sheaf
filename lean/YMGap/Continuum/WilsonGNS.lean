/-
Wiring the GNS quotient to the ACTUAL Wilson observable *-algebra.

# Which gap this closes

`Continuum/GNSQuotient.lean` built the genuine positive-DEFINITE GNS quotient
`V/Radical` out of an *abstract* `GNSData` bundle (an abelian-group carrier `V`
with a reflection-positive `Q′`-valued form `B`), and exhibited it on the toy
weighted form `⟨x,y⟩ = w·(x·y)` on `V = Q′`.

`Continuum/FiniteVolumeGNS.lean` built the *actual* finite-volume Wilson GNS
form `⟨a,b⟩ = E_Λ(star a · b)` over an observable *-algebra `A` (`ObsAlg`), with
`inner_nonneg` = reflection positivity (`E_Λ_positive`).  But `ObsAlg` carries
only `one/mul/star` — no `add/neg/sub/smul` — so the radical quotient could not
yet be formed on the Wilson form itself.

This module supplies the **vector-space (module) structure** on a Wilson
observable carrier as the `WilsonGNSData` bundle, equips the Wilson form
`B a b = E(star a · b)` on it, and **derives every `GNSData` field** from the
*-algebra-module laws (star additive/homogeneous, product bilinear, the scalar
action compatible with the product) together with the linearity and
**reflection positivity** of the finite-volume expectation `E`.  Feeding the
resulting `WilsonGNSData.toGNSData` into the `GNSQuotient` machinery yields a
GENUINE positive-definite GNS inner-product space for the actual finite-volume
Wilson theory: `wilson_qInner_posdef`.

# What is genuine here (constructed / proved, axiom-clean)

  * `WilsonGNSData A` — a `Q′`-vector-space structure on a carrier of the Wilson
    *-algebra `A` (abelian group `add/zero/neg` and scalar action `smul`, all up
    to a carrier equivalence `veq`), the *-algebra-module compatibility laws
    (`star_add`, `star_smul`, `mul_add_right`, `smul_mul`, the `mul`/`star`
    congruences), and a finite-volume expectation `E : A.carrier → Q′` that is
    **linear** (`E_add`, `E_smul`), **conjugate-symmetric** on the form
    (`E_conj`, = the `inner_conj`/`hconj` content) and **reflection-positive**
    (`E_self_nonneg : 0 ≤ E(star a · a)`, = the `inner_nonneg`/`E_Λ_positive`
    content).
  * `WilsonGNSData.B a b := E(star a · b)` — the actual Wilson GNS form.
  * `WilsonGNSData.toGNSData` — **the wiring**: every `GNSData` field is
    discharged.  Biadditivity ⇐ `star_add` + `mul_add_right` + `E_add`;
    homogeneity ⇐ `star_smul` + `smul_mul` + `E_smul`; symmetry ⇐ `E_conj`;
    reflection-positivity ⇐ `E_self_nonneg`.
  * `wilson_qInner_posdef` — POSITIVE-DEFINITENESS of the descended Wilson GNS
    inner product, via `GNSData.qInner_posdef`.  The real OS-reconstruction
    payoff on the Wilson form.
  * `WilsonGNSData.ofReferenceWeight` — the connector to the *interacting*
    finite-volume state: with `E := R.E_Λ`, `E_self_nonneg := R.E_Λ_positive`
    (the reflection positivity of `Continuum/FiniteVolume.lean`, REUSED) and
    `E_conj := hconj`, the linearity of `E_Λ` and the module structure of the
    Wilson carrier are exactly the remaining data.  `wilsonForm_eq_inner` shows
    the resulting `GNSData.B` is *definitionally* the `FiniteVolumeGNS.inner` of
    `gnsOfReferenceWeight`.
  * `qWilsonGNS` — a concrete non-degenerate inhabitant: the commutative Wilson
    *-algebra on `V = Q′` (`star = id`) with the linear weighted expectation
    `E x = w·x` (`w ≥ 0`).  Every `WilsonGNSData` field is discharged by `Q′`
    arithmetic, and `qWilsonGNS_posdef` fires the positive-definite Wilson
    quotient end-to-end.

# What stays an honest Type-level boundary (NOT faked)

Materializing a `WilsonGNSData` from the *general* `ReferenceWeight`/`E_Λ`
requires (i) the vector-space structure of the genuine Wilson observable carrier
and (ii) the linearity of `E_Λ` — neither of which the minimal `ObsAlg`/
`ProbFunctional` bundles.  `ofReferenceWeight` takes them as the named data they
are (genuine in the real Wilson algebra), and the concrete inhabitant is built
on the commutative `Q′` *-algebra.  The metric completion remains the
`GNSCompletion` boundary of `GNSQuotient.lean`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only (via `Q′` arithmetic and the
`GNSQuotient`/`Quotient`).  No `Classical.*`, no `sorryAx`, no `native_decide`.
-/

import YMGap.Continuum.GNSQuotient
import YMGap.Continuum.FiniteVolumeGNS

namespace YMGap.Continuum.WilsonGNS

open YMGap.Constructive
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.FiniteVolumeGNS
open YMGap.Continuum.GNSQuotient

/-! ## The Wilson GNS module datum -/

/-- A **Wilson GNS module datum** over an observable *-algebra `A`: a
`Q′`-vector-space structure on `A.carrier` (up to a carrier equivalence `veq`),
the *-algebra-module compatibility laws, and a **linear, conjugate-symmetric,
reflection-positive** finite-volume expectation `E`.  The Wilson GNS form is
`B a b = E(star a · b)`.

Every field is a genuine law of the real Wilson *-algebra and its finite-volume
state; none is faked.  `E_self_nonneg` is the reflection positivity
(`E_Λ_positive`), `E_conj` the conjugate symmetry (`inner_conj`/`hconj`). -/
structure WilsonGNSData (A : ObsAlg) where
  /-- The carrier equivalence (the algebra equality is `≃`, like `Q′`'s `eqv`). -/
  veq : A.carrier → A.carrier → Prop
  veq_refl : ∀ a, veq a a
  veq_symm : ∀ {a b}, veq a b → veq b a
  veq_trans : ∀ {a b c}, veq a b → veq b c → veq a c
  /-- Additive identity. -/
  zero : A.carrier
  /-- Addition. -/
  add : A.carrier → A.carrier → A.carrier
  /-- Negation. -/
  neg : A.carrier → A.carrier
  /-- Rational scalar action. -/
  smul : Q' → A.carrier → A.carrier
  add_congr : ∀ {a a' b b'}, veq a a' → veq b b' → veq (add a b) (add a' b')
  neg_congr : ∀ {a a'}, veq a a' → veq (neg a) (neg a')
  smul_congr : ∀ (s : Q') {a a'}, veq a a' → veq (smul s a) (smul s a')
  add_assoc : ∀ a b c, veq (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, veq (add a b) (add b a)
  zero_add : ∀ a, veq (add zero a) a
  neg_add : ∀ a, veq (add (neg a) a) zero
  /-- The product respects the carrier equivalence. -/
  mul_congr : ∀ {a a' b b'}, veq a a' → veq b b' → veq (A.mul a b) (A.mul a' b')
  /-- The involution respects the carrier equivalence. -/
  star_congr : ∀ {a a'}, veq a a' → veq (A.star a) (A.star a')
  /-- The involution is additive `star (a+b) ≃ star a + star b`. -/
  star_add : ∀ a b, veq (A.star (add a b)) (add (A.star a) (A.star b))
  /-- The involution is (real-)homogeneous `star (s·a) ≃ s · star a`. -/
  star_smul : ∀ (s : Q') (a), veq (A.star (smul s a)) (smul s (A.star a))
  /-- Right-distributivity of the product `(a+b)·c ≃ a·c + b·c`. -/
  mul_add_right : ∀ a b c, veq (A.mul (add a b) c) (add (A.mul a c) (A.mul b c))
  /-- Scalar / product compatibility `(s·a)·b ≃ s·(a·b)`. -/
  smul_mul : ∀ (s : Q') (a b), veq (A.mul (smul s a) b) (smul s (A.mul a b))
  /-- The finite-volume expectation `E` (e.g. `E_Λ`). -/
  E : A.carrier → Q'
  /-- `E` respects the carrier equivalence. -/
  E_congr : ∀ {a b}, veq a b → (E a).eqv (E b)
  /-- `E` is additive `E(a+b) ≃ E a + E b`. -/
  E_add : ∀ a b, (E (add a b)).eqv (E a + E b)
  /-- `E` is homogeneous `E(s·a) ≃ s · E a`. -/
  E_smul : ∀ (s : Q') (a), (E (smul s a)).eqv (s * E a)
  /-- **Conjugate symmetry** of the Wilson form (`inner_conj`/`hconj`):
  `E(star a · b) ≃ E(star b · a)`. -/
  E_conj : ∀ a b, (E (A.mul (A.star a) b)).eqv (E (A.mul (A.star b) a))
  /-- **Reflection positivity** (`inner_nonneg`/`E_Λ_positive`):
  `0 ≤ E(star a · a)`. -/
  E_self_nonneg : ∀ a, (0 : Q') ≤ E (A.mul (A.star a) a)

namespace WilsonGNSData

variable {A : ObsAlg} (W : WilsonGNSData A)

/-- **The Wilson GNS form** `B a b = E(star a · b)`. -/
def B (a b : A.carrier) : Q' := W.E (A.mul (A.star a) b)

/-- The form respects the carrier equivalence on the left:
`a ≃ a' ⇒ E(star a · b) ≃ E(star a' · b)`. -/
theorem B_congr_left {a a' : A.carrier} (b : A.carrier) (h : W.veq a a') :
    (W.B a b).eqv (W.B a' b) :=
  W.E_congr (W.mul_congr (W.star_congr h) (W.veq_refl b))

/-- **Biadditivity (left)** of the Wilson form, from `star_add` +
`mul_add_right` + `E_add`. -/
theorem B_add_left (a b c : A.carrier) :
    (W.B (W.add a b) c).eqv (W.B a c + W.B b c) := by
  -- star(a+b)·c ≃ (star a + star b)·c ≃ star a·c + star b·c, then E_add.
  have e1 : (W.E (A.mul (A.star (W.add a b)) c)).eqv
      (W.E (A.mul (W.add (A.star a) (A.star b)) c)) :=
    W.E_congr (W.mul_congr (W.star_add a b) (W.veq_refl c))
  have e2 : (W.E (A.mul (W.add (A.star a) (A.star b)) c)).eqv
      (W.E (W.add (A.mul (A.star a) c) (A.mul (A.star b) c))) :=
    W.E_congr (W.mul_add_right (A.star a) (A.star b) c)
  have e3 : (W.E (W.add (A.mul (A.star a) c) (A.mul (A.star b) c))).eqv
      (W.E (A.mul (A.star a) c) + W.E (A.mul (A.star b) c)) :=
    W.E_add (A.mul (A.star a) c) (A.mul (A.star b) c)
  exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 e3)

/-- **Homogeneity (left)** of the Wilson form, from `star_smul` + `smul_mul` +
`E_smul`. -/
theorem B_smul_left (s : Q') (a b : A.carrier) :
    (W.B (W.smul s a) b).eqv (s * W.B a b) := by
  -- star(s·a)·b ≃ (s·star a)·b ≃ s·(star a·b), then E_smul.
  have e1 : (W.E (A.mul (A.star (W.smul s a)) b)).eqv
      (W.E (A.mul (W.smul s (A.star a)) b)) :=
    W.E_congr (W.mul_congr (W.star_smul s a) (W.veq_refl b))
  have e2 : (W.E (A.mul (W.smul s (A.star a)) b)).eqv
      (W.E (W.smul s (A.mul (A.star a) b))) :=
    W.E_congr (W.smul_mul s (A.star a) b)
  have e3 : (W.E (W.smul s (A.mul (A.star a) b))).eqv (s * W.E (A.mul (A.star a) b)) :=
    W.E_smul s (A.mul (A.star a) b)
  exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 e3)

/-- **Every `WilsonGNSData` is a `GNSData`** on the Wilson form
`B a b = E(star a · b)`.  This is the wiring of the actual finite-volume Wilson
algebra into the positive-definite GNS quotient machinery. -/
def toGNSData : GNSData where
  V := A.carrier
  veq := W.veq
  veq_refl := W.veq_refl
  veq_symm := W.veq_symm
  veq_trans := W.veq_trans
  zero := W.zero
  add := W.add
  neg := W.neg
  smul := W.smul
  add_congr := W.add_congr
  neg_congr := W.neg_congr
  smul_congr := W.smul_congr
  add_assoc := W.add_assoc
  add_comm := W.add_comm
  zero_add := W.zero_add
  neg_add := W.neg_add
  B := W.B
  B_congr_left := fun {a a'} b h => W.B_congr_left b h
  B_add_left := W.B_add_left
  B_smul_left := W.B_smul_left
  B_symm := W.E_conj
  self_nonneg := W.E_self_nonneg

/-- The Wilson form on classes is the `GNSData` form — definitional. -/
theorem toGNSData_B (a b : A.carrier) : W.toGNSData.B a b = W.B a b := rfl

/-! ### The positive-definite Wilson GNS inner-product space -/

/-- The Wilson GNS quotient `A.carrier / Radical`. -/
def QuotSpace : Type := W.toGNSData.QuotSpace

/-- The descended Wilson GNS inner product, valued in `QR`. -/
def qInner : W.QuotSpace → W.QuotSpace → QR := W.toGNSData.qInner

/-- The Wilson GNS vacuum's quotient class. -/
def qZero : W.QuotSpace := W.toGNSData.qZero

/-- **Sharp Cauchy–Schwarz on the Wilson GNS form.** -/
theorem cauchy_schwarz (a b : A.carrier) :
    W.B a b * W.B a b ≤ W.B a a * W.B b b :=
  W.toGNSData.cauchy_schwarz a b

end WilsonGNSData

/-- **POSITIVE-DEFINITENESS of the Wilson GNS quotient inner product**:
`⟨q,q⟩ = 0 ⇔ q = [0]` on the actual finite-volume Wilson form
`B a b = E(star a · b)`.  The genuine OS-reconstruction payoff: the quotient by
the radical kills exactly the Wilson null vectors. -/
theorem wilson_qInner_posdef {A : ObsAlg} (W : WilsonGNSData A) (q : W.QuotSpace) :
    W.qInner q q = QR.zero ↔ q = W.qZero :=
  W.toGNSData.qInner_posdef q

/-! ## Connector to the interacting finite-volume state `E_Λ`

`ofReferenceWeight` builds a `WilsonGNSData` whose expectation is the *actual*
interacting finite-volume expectation `E_Λ` of `Continuum/FiniteVolume.lean`.
Its reflection positivity is `R.E_Λ_positive` (REUSED, not re-proved), its
conjugate symmetry is the supplied `hconj` (= `gnsOfReferenceWeight`'s `hconj`),
and the linearity of `E_Λ` plus the vector-space structure of the Wilson carrier
are the remaining named data — genuine laws of the real Wilson algebra that the
minimal `ObsAlg`/`ProbFunctional` does not bundle. -/

namespace WilsonGNSData

/-- A **module datum** on a Wilson carrier: the vector-space structure and the
*-algebra-module compatibility laws, packaged separately so the connector to
`E_Λ` only has to add the linearity of `E_Λ`. -/
structure CarrierModule (A : ObsAlg) where
  veq : A.carrier → A.carrier → Prop
  veq_refl : ∀ a, veq a a
  veq_symm : ∀ {a b}, veq a b → veq b a
  veq_trans : ∀ {a b c}, veq a b → veq b c → veq a c
  zero : A.carrier
  add : A.carrier → A.carrier → A.carrier
  neg : A.carrier → A.carrier
  smul : Q' → A.carrier → A.carrier
  add_congr : ∀ {a a' b b'}, veq a a' → veq b b' → veq (add a b) (add a' b')
  neg_congr : ∀ {a a'}, veq a a' → veq (neg a) (neg a')
  smul_congr : ∀ (s : Q') {a a'}, veq a a' → veq (smul s a) (smul s a')
  add_assoc : ∀ a b c, veq (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, veq (add a b) (add b a)
  zero_add : ∀ a, veq (add zero a) a
  neg_add : ∀ a, veq (add (neg a) a) zero
  mul_congr : ∀ {a a' b b'}, veq a a' → veq b b' → veq (A.mul a b) (A.mul a' b')
  star_congr : ∀ {a a'}, veq a a' → veq (A.star a) (A.star a')
  star_add : ∀ a b, veq (A.star (add a b)) (add (A.star a) (A.star b))
  star_smul : ∀ (s : Q') (a), veq (A.star (smul s a)) (smul s (A.star a))
  mul_add_right : ∀ a b c, veq (A.mul (add a b) c) (add (A.mul a c) (A.mul b c))
  smul_mul : ∀ (s : Q') (a b), veq (A.mul (smul s a) b) (smul s (A.mul a b))

/-- **The connector**: a `WilsonGNSData` whose expectation is the interacting
finite-volume `E_Λ`.  Reflection positivity is `R.E_Λ_positive` (reused);
conjugate symmetry is `hconj`; `E_Λ`-linearity (`elin_add`, `elin_smul`,
`elin_congr`) and the module structure `M` are the named data. -/
def ofReferenceWeight {A : ObsAlg} (R : ReferenceWeight A) (M : CarrierModule A)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b, (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))) :
    WilsonGNSData A where
  veq := M.veq
  veq_refl := M.veq_refl
  veq_symm := M.veq_symm
  veq_trans := M.veq_trans
  zero := M.zero
  add := M.add
  neg := M.neg
  smul := M.smul
  add_congr := M.add_congr
  neg_congr := M.neg_congr
  smul_congr := M.smul_congr
  add_assoc := M.add_assoc
  add_comm := M.add_comm
  zero_add := M.zero_add
  neg_add := M.neg_add
  mul_congr := M.mul_congr
  star_congr := M.star_congr
  star_add := M.star_add
  star_smul := M.star_smul
  mul_add_right := M.mul_add_right
  smul_mul := M.smul_mul
  E := R.E_Λ
  E_congr := elin_congr
  E_add := elin_add
  E_smul := elin_smul
  E_conj := hconj
  E_self_nonneg := R.E_Λ_positive

/-- **The Wilson form of `ofReferenceWeight` is definitionally the
`FiniteVolumeGNS.inner` of `gnsOfReferenceWeight`.**  This nails that the GNS
quotient is built on the *same* form `E_Λ(star a · b)` that
`Continuum/FiniteVolumeGNS.lean` already proved reflection-positive — not a new
or weaker object. -/
theorem wilsonForm_eq_inner {A : ObsAlg} (R : ReferenceWeight A) (M : CarrierModule A)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj_eq : ∀ a b, R.E_Λ (A.mul (A.star a) b) = R.E_Λ (A.mul (A.star b) a))
    (hone : A.mul (A.star A.one) A.one = A.one)
    (a b : A.carrier) :
    (ofReferenceWeight R M elin_congr elin_add elin_smul
        (fun x y => (hconj_eq x y) ▸ Q'.eqv_refl _)).B a b
      = (gnsOfReferenceWeight R hconj_eq hone).inner a b := rfl

end WilsonGNSData

/-! ## A concrete non-degenerate inhabitant: the commutative `Q′` Wilson algebra

The commutative Wilson *-algebra on `V = Q′` (`one = 1`, `mul = ·`,
`star = id`) with the **linear weighted expectation** `E x = w·x` (`w ≥ 0`).
This is the genuine Wilson form `E(star a · b) = w·(a·b)` routed through the
*linear-functional* construction (not the abstract weighted form of
`qWeightGNS`): every `WilsonGNSData` field — including `E_add`, `E_smul` and the
*-algebra-module compatibilities — is discharged by `Q′` arithmetic, and the
positive-definite Wilson quotient fires end-to-end. -/

/-- The commutative `Q′` Wilson *-algebra (`star = id`). -/
def qObsAlg : ObsAlg where
  carrier := Q'
  one := 1
  mul := fun x y => x * y
  star := fun x => x

/-- The **concrete Wilson GNS datum** on `V = Q′` with linear weighted
expectation `E x = w·x` (`w ≥ 0`). -/
def qWilsonGNS (w : Q') (hw : (0 : Q') ≤ w) : WilsonGNSData qObsAlg where
  veq := Q'.eqv
  veq_refl := Q'.eqv_refl
  veq_symm := fun h => Q'.eqv_symm h
  veq_trans := fun h1 h2 => Q'.eqv_trans _ _ _ h1 h2
  zero := (0 : Q')
  add := fun (x y : Q') => x + y
  neg := fun (x : Q') => -x
  smul := fun (s : Q') (x : Q') => s * x
  add_congr := fun ha hb => QPoly.q_add_congr ha hb
  neg_congr := fun {a a'} h => Q'.neg_eqv_congr a a' h
  smul_congr := fun s {a a'} h => Q'.mul_eqv_congr_left s a a' h
  add_assoc := Q'.add_assoc_eqv
  add_comm := Q'.add_comm_eqv
  zero_add := QPoly.q_zero_add_eqv
  neg_add := Q'.neg_add_self_eqv
  -- `mul`/`star` congruences and *-algebra-module laws (`star = id`, `mul = ·`):
  mul_congr := fun {a a' b b' : Q'} ha hb =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha) (Q'.mul_eqv_congr_left a' b b' hb)
  star_congr := fun {a a'} h => h
  star_add := fun (a b : Q') => Q'.eqv_refl (a + b)
  star_smul := fun (s : Q') (a : Q') => Q'.eqv_refl (s * a)
  mul_add_right := fun (a b c : Q') => QPoly.q_add_mul a b c
  smul_mul := fun (s : Q') (a b : Q') => Q'.mul_assoc_eqv s a b
  -- the linear weighted expectation `E x = w·x`:
  E := fun (x : Q') => w * x
  E_congr := fun {a b} h => Q'.mul_eqv_congr_left w a b h
  E_add := fun (a b : Q') => Q'.mul_add_eqv w a b
  E_smul := fun (s : Q') (a : Q') => OSReconstructionProgress.mul_pull w s a
  E_conj := fun (a b : Q') =>
    Q'.mul_eqv_congr_left w (a * b) (b * a) (Q'.mul_comm_eqv a b)
  E_self_nonneg := fun (a : Q') => Q'.mul_nonneg w (a * a) hw (SumOfSquares.q_mul_self_nonneg a)

/-- The concrete Wilson GNS form is reflection-positive (fires `E_self_nonneg`). -/
theorem qWilsonGNS_self_nonneg (w : Q') (hw : (0 : Q') ≤ w) (a : Q') :
    (0 : Q') ≤ (qWilsonGNS w hw).B a a :=
  (qWilsonGNS w hw).E_self_nonneg a

/-- Sharp Cauchy–Schwarz fires on the concrete Wilson GNS form. -/
theorem qWilsonGNS_cauchy_schwarz (w : Q') (hw : (0 : Q') ≤ w) (a b : Q') :
    (qWilsonGNS w hw).B a b * (qWilsonGNS w hw).B a b
      ≤ (qWilsonGNS w hw).B a a * (qWilsonGNS w hw).B b b :=
  (qWilsonGNS w hw).cauchy_schwarz a b

/-- **Positive-definiteness fires on the concrete Wilson GNS quotient.** -/
theorem qWilsonGNS_posdef (w : Q') (hw : (0 : Q') ≤ w) (q : (qWilsonGNS w hw).QuotSpace) :
    (qWilsonGNS w hw).qInner q q = QR.zero ↔ q = (qWilsonGNS w hw).qZero :=
  wilson_qInner_posdef (qWilsonGNS w hw) q

end YMGap.Continuum.WilsonGNS

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.toGNSData
#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.B_add_left
#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.B_smul_left
#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.cauchy_schwarz
#print axioms YMGap.Continuum.WilsonGNS.wilson_qInner_posdef
#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.ofReferenceWeight
#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.wilsonForm_eq_inner
#print axioms YMGap.Continuum.WilsonGNS.qWilsonGNS
#print axioms YMGap.Continuum.WilsonGNS.qWilsonGNS_cauchy_schwarz
#print axioms YMGap.Continuum.WilsonGNS.qWilsonGNS_posdef
