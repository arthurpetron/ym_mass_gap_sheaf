/-
# The uniform derivative-tail modulus for the Jacobi theta product
  (Wall-2 differentiation: the `UnifDerivConvAt.Mg` cutoff, at base `q²`)

This module supplies the CONCRETE tail cutoff `Mg(ε)` that the generic
constructive C¹-limit engine `TsumDeriv.UnifDerivConvAt` names for the Jacobi
theta family at a fixed `q = a ∈ (0,1)`.

The per-factor moduli `JTPInstance.fourAmp_le_geo` / `fourAmp_le_of_cutoff` bound
a SINGLE derivative factor `|f_k'(θ)| ≤ 4·q^{2k+1} ≤ Cfour·(q²)^k`.  What the
uniform-derivative field needs is the *tail sum* `S − S_M = Σ_{k≥M} σ_k(θ)` of the
log-derivative, driven (via the Leibniz product rule + the `M→∞` interchange) by
`f'_M θ − g θ = −sin2θ · Θ · (S_M − S)`.  Its magnitude is majorised by the
θ-free geometric tail `geoTailBase Cfour (q²) M = Cmaj·(q²)^M`,
`Cmaj = Cfour/(1−q²)`.

## What is genuinely proved here

* **`CmajTail` / `CmajTail_pos`** — the tail constant `Cmaj = Cfour·(1/(1−q²))`.
* **`fourAmpTail_le_geoTail`** — the θ-free termwise tail: the per-factor
  derivative majorants from index `M` on sum under `geoTailBase Cfour (q²) M`
  (reuse of `fourAmp_le_geo` termwise + `geoTailBase_series_le`).
* **`derivTailCutoff` / `geoTailBase_le_of_cutoff`** — THE data-level cutoff:
  `geoTailBase Cfour (q²) M ≤ ε` for all `M ≥ derivTailCutoff q ε`, a line-for-line
  copy of `JTPInstance.fourAmp_le_of_cutoff` with `Cfour → CmajTail q`.  No
  `Exists.choose`; the cutoff is a `Nat`-valued function of `ε`.
* **`thetaUnifDerivFromDriver`** — the packaged `UnifDerivConvAt`: GIVEN the driver
  bound `|f'_M θ − g θ| ≤ Bmag q · geoTailBase Cfour (q²) M` (the named residual,
  `ThetaDerivDriver`), the tail engine folds the θ-free prefactor `Bmag q` into the
  constant and produces the modulus `Mg = thetaDerivCutoff q`.

## The honest residual (AGENTS.md Rule 6)

`ThetaDerivDriver` is a `Type`-level HYPOTHESIS, not a theorem: it packages the
identity `f'_M θ − g θ = −sin2θ · Θ · (S_M − S)` (`DiffProduct.leibniz` for the
finite product, composed with the `M→∞` differentiation–limit interchange, the
`DiffJTP`/`ProductDerivativeLimit` node) together with the per-factor
log-derivative ratio bound `|σ_k| ≤ fourAmp q k · (1/(1−q)²)` (the denominator
floor `jFac_lb`).  This module builds the tail engine that CONSUMES that driver
and turns it into the `UnifDerivConvAt.Mg` modulus; it does NOT discharge the
interchange itself.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused
`Nat`/`Int`/`omega` helpers).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.JTPInstance
import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.TsumDeriv
import YMGap.Constructive.CharacterTail
import YMGap.Constructive.RationalTail

namespace YMGap.Continuum.ThetaUnifDerivModulus

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.JTPInstance
open YMGap.Constructive.RationalTail

local infix:50 " ≈ " => Q'.eqv

/-! ## Layer 0 — the tail constant `Cmaj = Cfour/(1−q²)` -/

/-- The geometric-tail constant `Cmaj = Cfour·(1/(1−q²))`, i.e. the `K = C·H` of
`geoTailBase` at base `r = q·q`.  θ-free. -/
def CmajTail (q : Q') : Q' := Cfour * HKConv.divPos 1 (1 + (-(q * q)))

/-- `Cmaj > 0`.  `Cfour > 0` and `divPos 1 _ > 0` (numerator `1 > 0`). -/
theorem CmajTail_pos (q : Q') : (0 : Q') < CmajTail q :=
  HKPos.q_mul_pos Cfour_pos (HKConv.divPos_pos (by decide))

theorem CmajTail_nonneg (q : Q') : (0 : Q') ≤ CmajTail q :=
  Q'.le_of_lt (CmajTail_pos q)

/-! ## Layer 1 — the θ-free termwise derivative tail -/

/-- **The θ-free derivative-tail bound.**  The per-factor derivative majorants
`fourAmp q (M+i)` from index `M` on sum under the geometric tail
`geoTailBase Cfour (q²) M`.  Termwise `fourAmp_le_geo` then `geoTailBase_series_le`. -/
theorem fourAmpTail_le_geoTail {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (M d : Nat) :
    finSum (fun i => fourAmp q (M + i)) d ≤ geoTailBase Cfour (q * q) M := by
  have hqq0 : (0 : Q') < q * q := HKPos.q_mul_pos hq0 hq0
  have hqq1 : q * q < (1 : Q') := qq_lt_one hq0 hq1
  -- termwise: fourAmp q (M+i) ≤ geoIncrBase Cfour (q·q) (M+i) = Cfour·(q·q)^(M+i)
  have hterm : finSum (fun i => fourAmp q (M + i)) d
      ≤ finSum (fun i => geoIncrBase Cfour (q * q) (M + i)) d :=
    CharacterTail.finSum_le_termwise
      (fun i => fourAmp q (M + i))
      (fun i => geoIncrBase Cfour (q * q) (M + i))
      (fun k => fourAmp_le_geo (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) (M + k)) d
  exact Q'.le_trans' _ _ _ hterm
    (geoTailBase_series_le Cfour_nonneg hqq0 hqq1 M d)

/-! ## Layer 2 — the data-level cutoff `geoTailBase Cfour (q²) M ≤ ε` -/

/-- **The explicit closed-form derivative-tail cutoff `N(ε)`** (Rule 8.3 `Type`-level
data): the `powBaseCutoff` of the geometric engine at base `q²` and tolerance
`δ = ε/Cmaj`.  A `Nat`-valued function of `ε`. -/
def derivTailCutoff (q ε : Q') : Nat :=
  HKConvGen.powBaseCutoff (q * q) (HKConv.divPos ε (CmajTail q))

/-- **THE UNIFORM DERIVATIVE-TAIL MODULUS.**  For `0 < q < 1` and `ε > 0`, the
θ-free geometric derivative tail satisfies `geoTailBase Cfour (q²) M ≤ ε` for ALL
`M ≥ derivTailCutoff q ε`.  A line-for-line copy of
`JTPInstance.fourAmp_le_of_cutoff` with `Cfour → CmajTail q`. -/
theorem geoTailBase_le_of_cutoff {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε) (M : Nat) (hM : derivTailCutoff q ε ≤ M) :
    geoTailBase Cfour (q * q) M ≤ ε := by
  have hqq0 : (0 : Q') < q * q := HKPos.q_mul_pos hq0 hq0
  have hqq1 : q * q < (1 : Q') := qq_lt_one hq0 hq1
  have hCnum : 0 < (CmajTail q).num := CReal.num_pos_of_pos (CmajTail_pos q)
  have hδpos : (0 : Q') < HKConv.divPos ε (CmajTail q) :=
    HKConv.divPos_pos (CReal.num_pos_of_pos hε)
  -- Cmaj · (ε/Cmaj) ≈ ε
  have hCδ : (CmajTail q * HKConv.divPos ε (CmajTail q)) ≈ ε := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (CmajTail q) (HKConv.divPos ε (CmajTail q))) ?_
    exact HKConv.divPos_mul_eqv hCnum
  -- (q·q)^M ≤ ε/Cmaj for M ≥ cutoff (pow_base_antitone + pow_base_le_cutoff)
  have hpow : (q * q) ^ M ≤ HKConv.divPos ε (CmajTail q) := by
    refine Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt hqq0) (Q'.le_of_lt hqq1) hM) ?_
    exact HKConvGen.pow_base_le_cutoff hqq0 hqq1 hδpos
  -- geoTailBase Cfour (q·q) M ≈ Cmaj · (q·q)^M  (the K·r^n reassociation)
  have he : (geoTailBase Cfour (q * q) M) ≈ (CmajTail q * (q * q) ^ M) := by
    show ((Cfour * (q * q) ^ M) * HKConv.divPos 1 (1 + (-(q * q)))) ≈
        ((Cfour * HKConv.divPos 1 (1 + (-(q * q)))) * (q * q) ^ M)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv Cfour ((q * q) ^ M) (HKConv.divPos 1 (1 + (-(q * q))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left Cfour _ _
        (Q'.mul_comm_eqv ((q * q) ^ M) (HKConv.divPos 1 (1 + (-(q * q)))))) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv Cfour (HKConv.divPos 1 (1 + (-(q * q)))) ((q * q) ^ M))
  -- geoTailBase ≈ Cmaj·(q·q)^M ≤ Cmaj·(ε/Cmaj) ≈ ε
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left ((q * q) ^ M) (HKConv.divPos ε (CmajTail q))
      (CmajTail q) hpow (CmajTail_nonneg q)) ?_
  exact Q'.le_of_eqv hCδ

/-! ## Layer 3 — package the `UnifDerivConvAt` modulus from the driver -/

/-- **The honest residual (named `Type`-level hypothesis).**  The driver bound
`|f'_M θ − g θ| ≤ Bmag q · geoTailBase Cfour (q²) M`, i.e. the Leibniz identity
`f'_M θ − g θ = −sin2θ · Θ · (S_M − S)` (`DiffProduct.leibniz` + the `M→∞`
interchange) with `|sin2θ| ≤ 1`, `|Θ| ≤ Bmag q`, and the log-derivative tail
`|S − S_M| ≤ geoTailBase Cfour (q²) M`.  NOT discharged here — it is the interchange
node the tail engine consumes. -/
structure ThetaDerivDriver (f' : Nat → Q' → Q') (g : Q' → Q') (q θ : Q') : Type where
  /-- The θ-free geometric majorant of the derivative-limit defect at stage `M`. -/
  driver : ∀ M : Nat,
    Q'.abs ((f' M θ) + (-(g θ))) ≤ ThetaConvGen.Bmag q * geoTailBase Cfour (q * q) M

/-- The θ-free full constant `Cmaj_full = Bmag q + 1`, folding the (uniform)
product-magnitude prefactor `Bmag q` into the tail constant while staying strictly
positive. -/
def CmajFull (q : Q') : Q' := ThetaConvGen.Bmag q + 1

/-- The full derivative modulus: the tail cutoff at rescaled tolerance
`ε' = ε/(Bmag q + 1)`. -/
def thetaDerivCutoff (q ε : Q') : Nat :=
  derivTailCutoff q (HKConv.divPos ε (CmajFull q))

/-- **The packaged uniform derivative-convergence modulus.**  Given the driver
bound (`ThetaDerivDriver`, the interchange residual), the tail engine produces a
genuine `TsumDeriv.UnifDerivConvAt` with the explicit data cutoff
`Mg = thetaDerivCutoff q`. -/
def thetaUnifDerivFromDriver {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {f' : Nat → Q' → Q'} {g : Q' → Q'} {θ : Q'}
    (drv : ThetaDerivDriver f' g q θ) :
    TsumDeriv.UnifDerivConvAt f' g θ where
  Mg := thetaDerivCutoff q
  conv := by
    intro ε hε M hM
    have hBnn : (0 : Q') ≤ ThetaConvGen.Bmag q := ThetaConvGen.Bmag_nonneg hq0
    -- ε' = ε/(Bmag q + 1) > 0
    have hε'pos : (0 : Q') < HKConv.divPos ε (CmajFull q) :=
      HKConv.divPos_pos (CReal.num_pos_of_pos hε)
    -- geoTailBase ≤ ε' for M ≥ thetaDerivCutoff q ε
    have hgt : geoTailBase Cfour (q * q) M ≤ HKConv.divPos ε (CmajFull q) :=
      geoTailBase_le_of_cutoff hq0 hq1 hε'pos M hM
    -- Bmag q · geoTailBase ≤ Bmag q · ε'
    have h1 : ThetaConvGen.Bmag q * geoTailBase Cfour (q * q) M
        ≤ ThetaConvGen.Bmag q * HKConv.divPos ε (CmajFull q) :=
      Q'.mul_le_mul_of_nonneg_left _ _ (ThetaConvGen.Bmag q) hgt hBnn
    -- Bmag q ≤ Bmag q + 1 = CmajFull q
    have hBle : ThetaConvGen.Bmag q ≤ CmajFull q := by
      show ThetaConvGen.Bmag q ≤ ThetaConvGen.Bmag q + 1
      exact Q'.add_le_self_of_nonneg (ThetaConvGen.Bmag q) 1 (by decide)
    -- Bmag q · ε' ≤ CmajFull q · ε'
    have h2 : ThetaConvGen.Bmag q * HKConv.divPos ε (CmajFull q)
        ≤ CmajFull q * HKConv.divPos ε (CmajFull q) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hBle (Q'.le_of_lt hε'pos)
    -- CmajFull q · ε' ≈ ε
    have h01 : (0 : Q') < 1 := CReal.pos_of_num_pos (by decide)
    have hCFnum : 0 < (CmajFull q).num := by
      apply CReal.num_pos_of_pos
      show (0 : Q') < ThetaConvGen.Bmag q + 1
      refine Q'.pos_of_lt_of_le h01 ?_
      refine Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' 1))) ?_
      exact Q'.add_le_add_right 0 (ThetaConvGen.Bmag q) 1 hBnn
    have h3 : (CmajFull q * HKConv.divPos ε (CmajFull q)) ≈ ε := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv (CmajFull q) (HKConv.divPos ε (CmajFull q))) ?_
      exact HKConv.divPos_mul_eqv hCFnum
    -- assemble:  |f'_M θ − g θ| ≤ Bmag q · geoTailBase ≤ … ≤ ε
    refine Q'.le_trans' _ _ _ (drv.driver M) ?_
    exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv h3))

end YMGap.Continuum.ThetaUnifDerivModulus

#print axioms YMGap.Continuum.ThetaUnifDerivModulus.geoTailBase_le_of_cutoff
#print axioms YMGap.Continuum.ThetaUnifDerivModulus.fourAmpTail_le_geoTail
#print axioms YMGap.Continuum.ThetaUnifDerivModulus.thetaUnifDerivFromDriver
