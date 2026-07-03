/-
# The DiffJTP capstone assembly (Wall-2, Route A, CReal-derivative layer)

The entire downstream spine of Wall 2 is proved and green:

* `TsumDeriv.fdDeriv_uniqueC` — the genuine `CReal`-valued finite-difference
  derivative-uniqueness engine;
* `DiffProduct.productDerivativeLimit_of_uniq_creal_deriv` — routes two common-`F`
  `FDDerivDataC` to the `CReal.Equiv` of their values;
* `JTPIdentity.DiffJTP_of_uniq_creal_deriv` / `Kt_geRat_zero_of_uniq_creal_deriv`
  — fire `DiffJTP` and `K_t ≥ 0` from a
  `DiffProduct.C1UniqInputsCRealDeriv (dSeriesCReal) (Rhalf)`;
* `ThetaFDDerivAssembly.ThetaCRealDerivResidual` — the named `Type` that IS
  (definitionally) that record, and
  `ThetaFDDerivAssembly.Kt_geRat_zero_of_theta_creal_deriv` — its free firing.

## What this module DELIVERS green

The capstone is ONE record of a named `Type`.  Given

* a common limit function `F : Q' → CReal` (heat-kernel `ϑ₃` as a function of the
  rational differentiation variable),
* a working point `θ₀ : Q'`,
* the product-side witness `Dprod : FDDerivDataC F (Rhalf …) θ₀`, and
* the series-side witness `Dser  : FDDerivDataC F (dSeriesCReal …) θ₀`,

`diffJTPAssembly` BUILDS the record
`DiffProduct.C1UniqInputsCRealDeriv (dSeriesCReal) (Rhalf)` — i.e.
`ThetaFDDerivAssembly.ThetaCRealDerivResidual` — and the two firing theorems
`diffJTP_of_assembly` / `Kt_geRat_zero_of_assembly` produce `DiffJTP` and
`K_t ≥ 0` with NO further analysis.  The record's index types nail the derivative
VALUES: `Dprod` must have value `Rhalf`, `Dser` value `dSeriesCReal`.  There is no
freedom.

This green assembly reduces the ENTIRE Wall-2 residual to EXACTLY the two
`FDDerivDataC` witnesses `Dprod`/`Dser` over ONE common `F`.

## Exactly what remains open (the two carried witnesses, and only those)

`Wall2CRealWitnesses` names the whole remaining input as a single `Type` (the two
witnesses over a common `F`).  Both witnesses factor through:

* **ATOM A** — a `CReal`-valued C¹-uniform-limit engine (the `CReal` analogue of
  `TsumDeriv.fdDeriv_of_unif`), which turns a family of lifted truncation
  derivatives into a `FDDerivDataC` of the genuine `CReal` LIMIT `F = ϑ₃`.  The
  existing bridge `ThetaFDDerivAssembly.ofQ'FDDerivDataC` only lifts a single
  rational `FDDerivData`; it does NOT reach the limit `F = ϑ₃`.  Atom A, fed the
  product-truncation family and the series-truncation family, produces BOTH
  witnesses over the common `F`.  Named honestly at
  `ThetaFDDerivAssembly.lean:48-61`.

* **ATOM B** — the family-level bookkeeping `TsumDeriv.C1Inputs` assembled from the
  fully-proven per-factor moduli `JTPInstance.perFactorModuli` (the `N(ε)`, the
  `M_k`, the denominator lower bound), the exact finite product rule
  `DiffProduct.leibniz`, and the geometric tail — exactly the still-open named
  `Type` `JTPInstance.ThetaFamilyAssembly`.

Neither atom is faked here; each is exposed as a named `Type`-level residual (never
a `sorry`).  This module lands the capstone green and names the residual sharply.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused
`Nat`/`Int`/`omega` helpers).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.DiffProduct
import YMGap.Continuum.JTPIdentity
import YMGap.Continuum.ThetaFDDerivAssembly
import YMGap.Continuum.JTPInstance
import YMGap.Constructive.Reals

namespace YMGap.Continuum.DiffJTPAssembly

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. THE CAPSTONE RECORD

Given a common `F`, a point `θ₀`, and the two common-`F` `CReal` finite-difference
derivatives, build the residual record.  The record's index types FORCE the values:
`Dprod` at `Rhalf`, `Dser` at `dSeriesCReal`. -/

/-- **THE CAPSTONE ASSEMBLY.**  The four fields `F, θ₀, Dprod, Dser` build the
`DiffProduct.C1UniqInputsCRealDeriv (dSeriesCReal) (Rhalf)` record — which is
definitionally `ThetaFDDerivAssembly.ThetaCRealDerivResidual`.  Green: given the two
witnesses over one common `F`, the record typechecks with no further analysis. -/
def diffJTPAssembly {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal) (θ₀ : Q')
    (Dprod : TsumDeriv.FDDerivDataC F (JTPIdentity.Rhalf ha0 ha1 hx hx1) θ₀)
    (Dser  : TsumDeriv.FDDerivDataC F (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) θ₀) :
    ThetaFDDerivAssembly.ThetaCRealDerivResidual ha0 ha1 hx hx1 :=
  ({ F := F, θ := θ₀, Dprod := Dprod, Dser := Dser } :
    DiffProduct.C1UniqInputsCRealDeriv
      (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1)
      (JTPIdentity.Rhalf ha0 ha1 hx hx1))

/-! ## 2. FIRING THE PIPELINE (both free, already proved downstream) -/

/-- **`diffJTPAssembly → DiffJTP`.**  The differentiated Jacobi-triple-product
identity `dSeriesCReal ≈ Rhalf`, produced ENTIRELY by the genuine `CReal`-valued
uniqueness engine, from the two carried witnesses. -/
theorem diffJTP_of_assembly {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal) (θ₀ : Q')
    (Dprod : TsumDeriv.FDDerivDataC F (JTPIdentity.Rhalf ha0 ha1 hx hx1) θ₀)
    (Dser  : TsumDeriv.FDDerivDataC F (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) θ₀) :
    JTPIdentity.DiffJTP ha0 ha1 hx hx1 :=
  JTPIdentity.DiffJTP_of_uniq_creal_deriv ha0 ha1 hx hx1
    (diffJTPAssembly ha0 ha1 hx hx1 F θ₀ Dprod Dser)

/-- **`diffJTPAssembly → K_t ≥ 0`.**  The heat-kernel series `K_t = dSeriesCReal ≥ 0`,
via the already-proven downstream firing.  Positivity flows through the genuine
`TsumDeriv.fdDeriv_uniqueC` engine; the two carried witnesses are the sole input. -/
theorem Kt_geRat_zero_of_assembly {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal) (θ₀ : Q')
    (Dprod : TsumDeriv.FDDerivDataC F (JTPIdentity.Rhalf ha0 ha1 hx hx1) θ₀)
    (Dser  : TsumDeriv.FDDerivDataC F (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) θ₀) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  ThetaFDDerivAssembly.Kt_geRat_zero_of_theta_creal_deriv ha0 ha1 hx hx1
    (diffJTPAssembly ha0 ha1 hx hx1 F θ₀ Dprod Dser)

/-! ## 3. THE WHOLE REMAINING INPUT, NAMED AS ONE `Type`

`Wall2CRealWitnesses` bundles the two common-`F` `CReal` finite-difference
derivatives — the ENTIRE Wall-2 residual after this capstone.  Supplying it fires
`DiffJTP` and `K_t ≥ 0`.  It is (definitionally) the residual record itself, but
stated as a bundle to expose that the sole outstanding data is the pair
`(Dprod, Dser)` over one common `F`. -/

/-- **The whole remaining Wall-2 input as a single named `Type`.**  Fields: the
common limit `F`, the point `θ₀`, and the product-side / series-side `CReal`
finite-difference derivatives (values forced to `Rhalf` / `dSeriesCReal`).  Inhabit
it and `K_t ≥ 0` follows for free (`Kt_geRat_zero_of_witnesses`). -/
structure Wall2CRealWitnesses {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Type where
  /-- The common limit function `F = ϑ₃`, as a `CReal`-valued function of the
  rational differentiation variable. -/
  F : Q' → CReal
  /-- The working point (differentiate in the rational `x`; take `θ₀ := x`). -/
  θ₀ : Q'
  /-- The product-side `CReal` finite-difference derivative of `F` at `θ₀`, value
  `Rhalf` (Atom A on the product-truncation family). -/
  Dprod : TsumDeriv.FDDerivDataC F (JTPIdentity.Rhalf ha0 ha1 hx hx1) θ₀
  /-- The series-side `CReal` finite-difference derivative of the SAME `F` at `θ₀`,
  value `dSeriesCReal` (Atom A on the series-truncation family). -/
  Dser  : TsumDeriv.FDDerivDataC F (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) θ₀

/-- **`Wall2CRealWitnesses → ThetaCRealDerivResidual`.**  The bundle IS the residual
record. -/
def residual_of_witnesses {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2CRealWitnesses ha0 ha1 hx hx1) :
    ThetaFDDerivAssembly.ThetaCRealDerivResidual ha0 ha1 hx hx1 :=
  diffJTPAssembly ha0 ha1 hx hx1 W.F W.θ₀ W.Dprod W.Dser

/-- **`Wall2CRealWitnesses → K_t ≥ 0`.**  The whole conditional closure, from the
single named residual bundle. -/
theorem Kt_geRat_zero_of_witnesses {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2CRealWitnesses ha0 ha1 hx hx1) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  ThetaFDDerivAssembly.Kt_geRat_zero_of_theta_creal_deriv ha0 ha1 hx hx1
    (residual_of_witnesses ha0 ha1 hx hx1 W)

/-! ## 4. THE TWO OPEN ATOMS, NAMED (never `sorry`)

Both witnesses of `Wall2CRealWitnesses` are produced by Atom A (the `CReal`-valued
C¹-uniform-limit engine), whose sole non-trivial input is Atom B
(`JTPInstance.ThetaFamilyAssembly`, the family-level `C1Inputs` from the proved
per-factor moduli).  We name each as a `Type`-level residual and record the
already-proven firing that Atom B alone closes the wall. -/

/-- **ATOM A (named `Type`, NOT discharged).**  A single-side `CReal`-valued
finite-difference derivative of the common limit `F` at `θ₀`, value `d`.  Atom A is
the engine that produces such data as the `M → ∞` uniform limit of the lifted
truncation derivatives `ThetaFDDerivAssembly.ofQ'FDDerivDataC (fdDeriv_of_unif …)`;
the existing bridge only reaches each finite truncation, NOT the limit `F = ϑ₃`.
Instantiated at `d = Rhalf` (product side) and `d = dSeriesCReal` (series side) over
ONE common `F`, the two copies are exactly the fields of `Wall2CRealWitnesses`. -/
def AtomA_CRealC1UniformLimit (F : Q' → CReal) (d : CReal) (θ₀ : Q') : Type :=
  TsumDeriv.FDDerivDataC F d θ₀

/-- **ATOM A closes the wall.**  Given Atom A on BOTH sides over one common `F` (the
two `FDDerivDataC` at values `Rhalf` and `dSeriesCReal`), `K_t ≥ 0` follows.  This is
just `Kt_geRat_zero_of_assembly`; it records that the two Atom-A instances are the
entire residual. -/
theorem Kt_geRat_zero_of_atomA {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal) (θ₀ : Q')
    (AprodAtomA : AtomA_CRealC1UniformLimit F (JTPIdentity.Rhalf ha0 ha1 hx hx1) θ₀)
    (AserAtomA  : AtomA_CRealC1UniformLimit F (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) θ₀) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  Kt_geRat_zero_of_assembly ha0 ha1 hx hx1 F θ₀ AprodAtomA AserAtomA

/-- **ATOM B closes the wall (already-proven route).**  The family-level assembly
`JTPInstance.ThetaFamilyAssembly` (built on the proved per-factor moduli
`perFactorModuli` + `DiffProduct.leibniz` + geometric tail) closes `K_t ≥ 0` through
the `C1`-route firing `JTPInstance.Kt_geRat_zero_of_assembly`.  Re-exposed here so
the full residual chain `AtomB ⟹ K_t ≥ 0` sits alongside the CReal-derivative
capstone. -/
theorem Kt_geRat_zero_of_atomB {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : JTPInstance.ThetaFamilyAssembly ha0 ha1 hx hx1) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  JTPInstance.Kt_geRat_zero_of_assembly ha0 ha1 hx hx1 H

end YMGap.Continuum.DiffJTPAssembly

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`Int`/`omega` helpers).  No `Classical.*`, no
`native_decide`, no `sorry`.  `Wall2CRealWitnesses`, `AtomA_CRealC1UniformLimit`, and
`JTPInstance.ThetaFamilyAssembly` are named `Type`-obligations (the outstanding
analytic inputs), NOT `sorry`. -/

#print axioms YMGap.Continuum.DiffJTPAssembly.diffJTPAssembly
#print axioms YMGap.Continuum.DiffJTPAssembly.diffJTP_of_assembly
#print axioms YMGap.Continuum.DiffJTPAssembly.Kt_geRat_zero_of_assembly
#print axioms YMGap.Continuum.DiffJTPAssembly.Kt_geRat_zero_of_witnesses
#print axioms YMGap.Continuum.DiffJTPAssembly.Kt_geRat_zero_of_atomA
#print axioms YMGap.Continuum.DiffJTPAssembly.Kt_geRat_zero_of_atomB
