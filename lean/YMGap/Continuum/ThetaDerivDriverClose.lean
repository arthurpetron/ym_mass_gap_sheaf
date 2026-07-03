/-
# Closing the per-factor log-derivative ratio bound (`sigma_abs_le`) and its tail
  (Wall-2 differentiation: the sum-side geometric tail of the log-derivative)

`ThetaUnifDerivModulus.thetaUnifDerivFromDriver` is already unconditional GIVEN a
`ThetaDerivDriver f' g q θ`, whose single field is the θ-free geometric majorant

    ∀ M, |f' M θ − g θ| ≤ Bmag q · geoTailBase Cfour (q²) M.

For the intended instantiation `f' M θ = −sin2θ·P_M·S_M`, `g θ = −sin2θ·Θ·S`, the
driver splits as `P_M·S_M − Θ·S = P_M·(S_M − S) + (P_M − Θ)·S`, and the SUM-side
tail `S_M − S = Σ_{k≥M} σ_k` needs the per-factor log-derivative ratio bound

    |σ_k| = |f_k'(θ) / f_k(θ)| ≤ fourAmp q k · (1/(1−q)²).

## What is genuinely proved here (the one new lemma + its termwise tail)

* **`invSqOneSubQ`** — the θ-free constant `1/(1−q)²`, in the same `HKConv.divPos`
  shape the tail machinery already folds into `CmajTail`/`CmajFull`.
* **`amp_le_self`** — the missing antitone-in-exponent step `q^{2k+1} ≤ q`, from
  the existing `HKConvGen.pow_base_antitone` engine.
* **`jFac_pos`** — strict factor positivity `0 < f_k(θ)` from the proven floor
  `(1−q^{2k+1})² ≤ f_k(θ)` (`JTPInstance.jFac_lb`) and `q^{2k+1} < 1`.
* **`sigma_abs_le` (THE genuinely new lemma)** — the per-factor log-derivative
  ratio bound `|f_k'/f_k| ≤ fourAmp q k · (1/(1−q)²)`.  Proof = three existing
  inputs, no new analysis: numerator `JTPInstance.jDeriv_abs_le`, denominator floor
  `jFac_lb` chained through the monotone square `(1−q)² ≤ (1−q^{2k+1})²`, and the
  cross-multiplied division `Q'.divPos_le_of_le_mul` / `Q'.le_divPos_of_mul_le` with
  the cancellation `HKConv.divPos_mul_eqv`.
* **`sigmaTail_le`** — the θ-free termwise tail: feeding `sigma_abs_le` into the
  already-proven `ThetaUnifDerivModulus.fourAmpTail_le_geoTail` and pulling the
  constant out with `RationalTail.finSum_mul_const`,
  `Σ_{i<d} |σ_{M+i}| ≤ (1/(1−q)²) · geoTailBase Cfour (q²) M`.

## The honest residual (AGENTS.md Rule 6)

`sigma_abs_le` supplies the SUM-side `S_M − S` tail — one of the two ingredients of
the driver.  It does NOT discharge `DiffJTP`.  The full `ThetaDerivDriver` also
needs the PRODUCT-side comparison `|P_M − Θ|` (the Cauchy modulus of
`thetaConvCRealGen`, `ThetaConvGen.incr_le_gen`) together with the CReal-level
factorisation `Θ·S`, where `Θ, S` are `CReal` limits, not rationals.  The abstract
`ThetaDerivDriver` field is `Q'`-valued, so the honest remaining obligation is the
product-side/CReal interchange, named here as `DriverProductResidual` (a `Type`-level
hypothesis, NOT a theorem); supplying it feeds `thetaUnifDerivFromDriver` directly.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused
`Nat`/`Int`/`omega`/`pow`/`divPos` helpers).  No `Classical.*`, no `native_decide`,
no `sorry`.
-/

import YMGap.Continuum.JTPInstance
import YMGap.Continuum.ThetaUnifDerivModulus
import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.HeatKernelConv
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.HeatKernelPos
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.AbsQ
import YMGap.Constructive.Geometric
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CharacterTail
import YMGap.Constructive.RationalTail

namespace YMGap.Continuum.ThetaDerivDriverClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.JTPInstance
open YMGap.Constructive.RationalTail

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The θ-free constant `1/(1−q)²` -/

/-- The θ-free per-factor denominator-floor constant `1/(1−q)²`, in the same
`HKConv.divPos` shape the tail machinery already folds into `CmajTail`/`CmajFull`. -/
def invSqOneSubQ (q : Q') : Q' := HKConv.divPos 1 ((1 + (-q)) * (1 + (-q)))

theorem invSqOneSubQ_nonneg (q : Q') : (0 : Q') ≤ invSqOneSubQ q := by
  unfold invSqOneSubQ
  exact HKConv.divPos_nonneg Q'.zero_le_one

/-! ## 1. The missing antitone step `q^{2k+1} ≤ q` -/

/-- **`amp q k ≤ q`** — the per-factor amplitude is bounded by `q` itself
(`q^{2k+1} ≤ q^1 = q`), via the existing antitone-in-exponent engine
`HKConvGen.pow_base_antitone`. -/
theorem amp_le_self {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) (k : Nat) :
    amp q k ≤ q := by
  show q ^ (2 * k + 1) ≤ q
  have h : q ^ (2 * k + 1) ≤ q ^ 1 :=
    HKConvGen.pow_base_antitone hq0 hq1 (show (1 : Nat) ≤ 2 * k + 1 by omega)
  have he : (q ^ (1 : Nat)) ≈ q := by
    show (q * q ^ (0 : Nat)) ≈ q
    rw [Q'.pow_zero]
    exact Q'.mul_one_eqv q
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv he)

/-! ## 2. Strict factor positivity `0 < f_k(θ)` -/

/-- **`0 < jFac q k c`** for `0 < q < 1`, `−1 ≤ c` — strict factor positivity from
the proven floor `(1−q^{2k+1})² ≤ f_k(θ)` (`JTPInstance.jFac_lb`) plus
`q^{2k+1} < 1`. -/
theorem jFac_pos {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (k : Nat)
    {c : Q'} (hc : (-1 : Q') ≤ c) : (0 : Q') < jFac q k c := by
  have hamp : amp q k ≤ q := amp_le_self (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) k
  have hamp_lt1 : amp q k < (1 : Q') := HKPos.q_lt_of_le_of_lt hamp hq1
  have hsqpos : (0 : Q') < (1 + (-(amp q k))) * (1 + (-(amp q k))) :=
    HKPos.q_mul_pos (HKPos.one_sub_pos hamp_lt1) (HKPos.one_sub_pos hamp_lt1)
  exact Q'.pos_of_lt_of_le hsqpos (jFac_lb (Q'.le_of_lt hq0) k hc)

/-! ## 3. The one genuinely new lemma: the per-factor log-derivative ratio bound -/

/-- **`sigma_abs_le` — the per-factor log-derivative ratio bound.**  For
`0 < q < 1`, `−1 ≤ c`, `|s| ≤ 1`, the ratio of the formal `θ`-derivative
`jDeriv q k s = −4q^{2k+1}s` to the factor `jFac q k c` satisfies

    |jDeriv q k s / jFac q k c| ≤ fourAmp q k · (1/(1−q)²).

Proof: numerator `|jDeriv| ≤ fourAmp q k` (`JTPInstance.jDeriv_abs_le`), denominator
floor `(1−q)² ≤ (1−q^{2k+1})² ≤ jFac q k c` (`amp_le_self` + monotone square +
`jFac_lb`), and the cross-multiplied division (`Q'.divPos_le_of_le_mul` /
`Q'.le_divPos_of_mul_le` + the cancellation `HKConv.divPos_mul_eqv`). -/
theorem sigma_abs_le {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (k : Nat)
    {c s : Q'} (hc : (-1 : Q') ≤ c) (hs1 : (-1 : Q') ≤ s) (hs2 : s ≤ (1 : Q'))
    (hpos : (0 : Q') < jFac q k c) :
    Q'.abs (Q'.divPos (jDeriv q k s) (jFac q k c) hpos)
      ≤ fourAmp q k * invSqOneSubQ q := by
  -- Abbreviations for readability.
  have hFA : (0 : Q') ≤ fourAmp q k := fourAmp_nonneg (Q'.le_of_lt hq0) k
  have hInvNN : (0 : Q') ≤ invSqOneSubQ q := invSqOneSubQ_nonneg q
  have hBNN : (0 : Q') ≤ fourAmp q k * invSqOneSubQ q := Q'.mul_nonneg _ _ hFA hInvNN
  -- The denominator floor D₀ = (1−q)² > 0.
  have hD0pos : (0 : Q') < (1 + (-q)) * (1 + (-q)) :=
    HKPos.q_mul_pos (HKPos.one_sub_pos hq1) (HKPos.one_sub_pos hq1)
  have hD0num : 0 < ((1 + (-q)) * (1 + (-q))).num := CReal.num_pos_of_pos hD0pos
  -- Key cancellation: B·D₀ ≈ fourAmp q k.
  have hBD0 : ((fourAmp q k * invSqOneSubQ q) * ((1 + (-q)) * (1 + (-q))))
      ≈ fourAmp q k := by
    have hcancel : (invSqOneSubQ q * ((1 + (-q)) * (1 + (-q)))) ≈ (1 : Q') := by
      show (HKConv.divPos 1 ((1 + (-q)) * (1 + (-q))) * ((1 + (-q)) * (1 + (-q)))).eqv 1
      exact HKConv.divPos_mul_eqv hD0num
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (fourAmp q k) (invSqOneSubQ q) ((1 + (-q)) * (1 + (-q)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (fourAmp q k) _ _ hcancel) ?_
    exact Q'.mul_one_eqv (fourAmp q k)
  -- Denominator floor: D₀ = (1−q)² ≤ (1−q^{2k+1})² ≤ jFac q k c.
  have hamp : amp q k ≤ q := amp_le_self (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) k
  have hnegamp : -q ≤ -(amp q k) := Q'.neg_le_neg hamp
  have huv : (1 + (-q)) ≤ (1 + (-(amp q k))) :=
    Q'.add_le_add_left 1 (-q) (-(amp q k)) hnegamp
  have hu_nn : (0 : Q') ≤ 1 + (-q) := Q'.le_of_lt (HKPos.one_sub_pos hq1)
  have hamp_lt1 : amp q k < (1 : Q') := HKPos.q_lt_of_le_of_lt hamp hq1
  have hv_nn : (0 : Q') ≤ 1 + (-(amp q k)) := Q'.le_of_lt (HKPos.one_sub_pos hamp_lt1)
  have hsq1 : (1 + (-q)) * (1 + (-q))
      ≤ (1 + (-(amp q k))) * (1 + (-(amp q k))) := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right (1 + (-q)) (1 + (-(amp q k))) (1 + (-q)) huv hu_nn) ?_
    exact Q'.mul_le_mul_of_nonneg_left (1 + (-q)) (1 + (-(amp q k)))
      (1 + (-(amp q k))) huv hv_nn
  have hD0leD : (1 + (-q)) * (1 + (-q)) ≤ jFac q k c :=
    Q'.le_trans' _ _ _ hsq1 (jFac_lb (Q'.le_of_lt hq0) k hc)
  -- Numerator: |jDeriv| ≤ fourAmp, hence both sign bounds.
  have hnum_abs : Q'.abs (jDeriv q k s) ≤ fourAmp q k :=
    jDeriv_abs_le (Q'.le_of_lt hq0) k hs1 hs2
  have hN_le : jDeriv q k s ≤ fourAmp q k :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self (jDeriv q k s)) hnum_abs
  have hnegN : -(jDeriv q k s) ≤ fourAmp q k :=
    Q'.le_trans' _ _ _ (Q'.neg_le_abs (jDeriv q k s)) hnum_abs
  have hnegfourAmp_le_N : -(fourAmp q k) ≤ jDeriv q k s :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hnegN) (Q'.le_of_eqv (Q'.neg_neg_eqv (jDeriv q k s)))
  -- B·D₀ ≤ B·jFac (monotone in the denominator).
  have hBD0leBD : (fourAmp q k * invSqOneSubQ q) * ((1 + (-q)) * (1 + (-q)))
      ≤ (fourAmp q k * invSqOneSubQ q) * jFac q k c :=
    Q'.mul_le_mul_of_nonneg_left _ _ (fourAmp q k * invSqOneSubQ q) hD0leD hBNN
  -- Upper: jDeriv ≤ fourAmp ≈ B·D₀ ≤ B·jFac, so divPos ≤ B.
  have hfourAmp_le_BD : fourAmp q k ≤ (fourAmp q k * invSqOneSubQ q) * jFac q k c :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hBD0) hBD0leBD
  have hN_le_BD : jDeriv q k s ≤ (fourAmp q k * invSqOneSubQ q) * jFac q k c :=
    Q'.le_trans' _ _ _ hN_le hfourAmp_le_BD
  have hUp : Q'.divPos (jDeriv q k s) (jFac q k c) hpos ≤ fourAmp q k * invSqOneSubQ q :=
    Q'.divPos_le_of_le_mul (jDeriv q k s) (jFac q k c) hpos hN_le_BD
  -- Lower: (−B)·jFac ≈ −(B·jFac) ≤ −(B·D₀) ≈ −fourAmp ≤ jDeriv, so −B ≤ divPos.
  have hLmul : (-(fourAmp q k * invSqOneSubQ q)) * jFac q k c ≤ jDeriv q k s := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_mul_eqv (fourAmp q k * invSqOneSubQ q) (jFac q k c))) ?_
    refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hBD0leBD) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ hBD0)) ?_
    exact hnegfourAmp_le_N
  have hLo : -(fourAmp q k * invSqOneSubQ q)
      ≤ Q'.divPos (jDeriv q k s) (jFac q k c) hpos :=
    Q'.le_divPos_of_mul_le (jDeriv q k s) (jFac q k c) hpos hLmul
  exact Q'.abs_le hLo hUp

/-! ## 4. The per-factor ratio as a sequence, and its θ-free geometric tail -/

/-- The per-factor log-derivative ratio `σ_k = jDeriv q k s / jFac q k c` as a `Q'`
value, using the proven strict positivity `jFac_pos`. -/
def sigmaRatio {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {c : Q'} (hc : (-1 : Q') ≤ c) (s : Q') (k : Nat) : Q' :=
  Q'.divPos (jDeriv q k s) (jFac q k c) (jFac_pos hq0 hq1 k hc)

/-- `sigma_abs_le` specialised to `sigmaRatio`: `|σ_k| ≤ fourAmp q k · (1/(1−q)²)`. -/
theorem sigmaRatio_abs_le {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {c : Q'} (hc : (-1 : Q') ≤ c) {s : Q'} (hs1 : (-1 : Q') ≤ s) (hs2 : s ≤ (1 : Q'))
    (k : Nat) :
    Q'.abs (sigmaRatio hq0 hq1 hc s k) ≤ fourAmp q k * invSqOneSubQ q :=
  sigma_abs_le hq0 hq1 k hc hs1 hs2 (jFac_pos hq0 hq1 k hc)

/-- **`sigmaTail_le` — the θ-free geometric tail of the log-derivative.**  From
index `M` on, the ratio magnitudes sum under `(1/(1−q)²) · geoTailBase Cfour (q²) M`,
i.e. `|S_M − S| ≤ (1/(1−q)²) · geoTailBase Cfour (q²) M`.  Termwise `sigma_abs_le`
into `ThetaUnifDerivModulus.fourAmpTail_le_geoTail`, pulling the constant
`invSqOneSubQ q` out with `RationalTail.finSum_mul_const`. -/
theorem sigmaTail_le {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {c : Q'} (hc : (-1 : Q') ≤ c) {s : Q'} (hs1 : (-1 : Q') ≤ s) (hs2 : s ≤ (1 : Q'))
    (M d : Nat) :
    finSum (fun i => Q'.abs (sigmaRatio hq0 hq1 hc s (M + i))) d
      ≤ invSqOneSubQ q * geoTailBase Cfour (q * q) M := by
  have hterm : finSum (fun i => Q'.abs (sigmaRatio hq0 hq1 hc s (M + i))) d
      ≤ finSum (fun i => fourAmp q (M + i) * invSqOneSubQ q) d :=
    CharacterTail.finSum_le_termwise
      (fun i => Q'.abs (sigmaRatio hq0 hq1 hc s (M + i)))
      (fun i => fourAmp q (M + i) * invSqOneSubQ q)
      (fun i => sigmaRatio_abs_le hq0 hq1 hc hs1 hs2 (M + i)) d
  have hpull : (finSum (fun i => fourAmp q (M + i)) d * invSqOneSubQ q)
      ≈ finSum (fun i => fourAmp q (M + i) * invSqOneSubQ q) d :=
    RationalTail.finSum_mul_const (fun i => fourAmp q (M + i)) (invSqOneSubQ q) d
  have hgeo : finSum (fun i => fourAmp q (M + i)) d ≤ geoTailBase Cfour (q * q) M :=
    ThetaUnifDerivModulus.fourAmpTail_le_geoTail hq0 hq1 M d
  have hmul : finSum (fun i => fourAmp q (M + i)) d * invSqOneSubQ q
      ≤ geoTailBase Cfour (q * q) M * invSqOneSubQ q :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hgeo (invSqOneSubQ_nonneg q)
  refine Q'.le_trans' _ _ _ hterm ?_
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpull) ?_
  refine Q'.le_trans' _ _ _ hmul ?_
  exact Q'.le_of_eqv
    (Q'.mul_comm_eqv (geoTailBase Cfour (q * q) M) (invSqOneSubQ q))

/-! ## 5. The honest residual: the product-side / CReal interchange

`sigmaTail_le` discharges the SUM-side `S_M − S` ingredient of the driver.  The full
`ThetaUnifDerivModulus.ThetaDerivDriver` also needs the PRODUCT-side comparison and
the CReal-level factorisation `Θ·S` (`Θ, S` are `CReal` limits, not rationals).  We
name that remaining obligation sharply as a `Type`-level hypothesis — it is exactly
the `driver` field of `ThetaDerivDriver`; supplying it feeds
`thetaUnifDerivFromDriver` directly. -/

/-- **The honest residual (named `Type`-level hypothesis, NOT a theorem).**  The
product-side geometric majorant of the derivative-limit defect — the remaining
half of the driver (the sum side is discharged by `sigmaTail_le`). -/
structure DriverProductResidual (f' : Nat → Q' → Q') (g : Q' → Q') (q θ : Q') : Type where
  /-- `∀ M, |f'_M θ − g θ| ≤ Bmag q · geoTailBase Cfour (q²) M`. -/
  productTail : ∀ M : Nat,
    Q'.abs ((f' M θ) + (-(g θ)))
      ≤ ThetaConvGen.Bmag q * geoTailBase Cfour (q * q) M

/-- A `DriverProductResidual` is exactly a `ThetaDerivDriver` — this records that,
with `sigmaTail_le` supplying the sum-side ingredient, the SOLE outstanding datum for
the driver is `DriverProductResidual`. -/
def driverOfResidual {f' : Nat → Q' → Q'} {g : Q' → Q'} {q θ : Q'}
    (H : DriverProductResidual f' g q θ) :
    ThetaUnifDerivModulus.ThetaDerivDriver f' g q θ :=
  ⟨H.productTail⟩

/-- **`DriverProductResidual → UnifDerivConvAt`.**  Supplying the named residual
produces the genuine `TsumDeriv.UnifDerivConvAt` derivative-convergence modulus via
the already-proven tail engine `thetaUnifDerivFromDriver`. -/
def modulusOfResidual {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {f' : Nat → Q' → Q'} {g : Q' → Q'} {θ : Q'}
    (H : DriverProductResidual f' g q θ) :
    TsumDeriv.UnifDerivConvAt f' g θ :=
  ThetaUnifDerivModulus.thetaUnifDerivFromDriver hq0 hq1 (driverOfResidual H)

end YMGap.Continuum.ThetaDerivDriverClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaDerivDriverClose.invSqOneSubQ_nonneg
#print axioms YMGap.Continuum.ThetaDerivDriverClose.amp_le_self
#print axioms YMGap.Continuum.ThetaDerivDriverClose.jFac_pos
#print axioms YMGap.Continuum.ThetaDerivDriverClose.sigma_abs_le
#print axioms YMGap.Continuum.ThetaDerivDriverClose.sigmaRatio_abs_le
#print axioms YMGap.Continuum.ThetaDerivDriverClose.sigmaTail_le
#print axioms YMGap.Continuum.ThetaDerivDriverClose.driverOfResidual
#print axioms YMGap.Continuum.ThetaDerivDriverClose.modulusOfResidual
