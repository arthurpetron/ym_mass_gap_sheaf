/-
# Inhabiting the theta-product running-cap bundle `ProdSecondDiffRunningInputs`
  (`HinRunningCapClose`)

`ProdSecondDiffInputsClose.prodSecondDiffOfRunning` turns a
`ProdSecondDiffRunningInputs fk dk x B` into the exact datum
`ProdUnifModulusClose.ProdSecondDiffResidual fk dk x B` that
`prodFlatModulus` / `prodUnifModulus` / `fdboundFlat` consume.  For the Jacobi
theta product the concrete instance is

    fk := fun k t => JTPInstance.jFac a k t          -- the affine (in c) k-th factor
    dk := fun k   => JTPInstance.amp a k + JTPInstance.amp a k   -- its c-slope 2·a^{2k+1}

with head multiplier `g M = |jFac a M x| + |amp+amp|`, additive coefficient
`c M = |prodDeriv fk dk x M · (amp+amp)|`, and `F M h = c M · h²`.

## What is GENUINELY proved here (new, axiom-clean)

Seven of the eight `ProdSecondDiffRunningInputs` fields are discharged outright:

* `hstep` — the one-factor Leibniz recursion, via
  `ProdSecondDiffInputsClose.hstep_of_vanishing` fed with
  `DkProducerClose.jacFdRem_vanishes` (the affine ring cancellation).  A one-liner.
* `hgnn` / `hcnn` / `hFc` — `Q'.abs_nonneg` and the definitional `F = c·h²`.
* `hBpos` — `HKPos.q_mul_pos` from `P, S > 0`.

The remaining `hBrun_le : ∀ M, runningCap g c M ≤ B` is REDUCED — not asserted — to
two honest uniform caps (`HinCaps`), via the fully-proved general telescoping

    runningCap g c M ≤ (∏_{i<M} g_i) · (∑_{j<M} c_j)      (`runningCap_le_prodP_sumC`)

valid whenever `g_i ≥ 1` and `c_j ≥ 0`.  The head lower bound `g_M ≥ 1` on the
Chebyshev domain `x ∈ [−1,1]` is itself proved here (`gFun_ge_one`) from
`JTPInstance.jFac_lb`'s `(1−amp)²` positivity plus the elementary identity
`(1−A)² + 2A = 1 + A²` (`oneSubSq_add_two_ge_one`, obtained by specialising
`JTPInstance.jFac_split_abs` at `c = 0`).

## The honest residual (AGENTS.md Rule 6/8)

`HinCaps a x` carries exactly the two uniform caps left open:

* `hPcap` — the uniform product cap `∏_{i<M} g_i ≤ P` (geometric-`a²` product
  floor; sub-obligations 1+2 of the running-cap decomposition);
* `hScap` — the uniform partial-sum cap `∑_{j<M} c_j ≤ S` (geometric-`a²` sum;
  sub-obligation 3).

Given a `HinCaps`, `hinRunningCap` produces the full bundle at `B := P·S` and
`hinResidual` the downstream `ProdSecondDiffResidual`.  The two caps are the only
outstanding analytic inputs; everything turning them (plus `g_M ≥ 1`, `c_M ≥ 0`)
into `hBrun_le` is proved here.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.
-/

import YMGap.Continuum.ProdSecondDiffInputsClose
import YMGap.Continuum.DkProducerClose
import YMGap.Continuum.FiniteProductFDDeriv
import YMGap.Continuum.HeatKernelPos

namespace YMGap.Continuum.HinRunningCapClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteProductFDDeriv (prodDeriv)
open YMGap.Continuum.ProdSecondDiffInputsClose
  (runningCap ProdSecondDiffRunningInputs prodSecondDiffOfRunning hstep_of_vanishing)
open YMGap.Continuum.ProdUnifModulusClose (ProdSecondDiffResidual)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The concrete theta factor / slope families. -/

/-- The theta factor family `fk k t = jFac a k t` (affine in the cos-variable). -/
def fkθ (a : Q') : Nat → Q' → Q' := fun k t => JTPInstance.jFac a k t

/-- The theta c-slope family `dk k = amp a k + amp a k = 2·a^{2k+1}`. -/
def dkθ (a : Q') : Nat → Q' := fun k => JTPInstance.amp a k + JTPInstance.amp a k

/-- The head multiplier `g M = |jFac a M x| + |amp+amp|`. -/
def gFun (a x : Q') (M : Nat) : Q' :=
  Q'.abs (JTPInstance.jFac a M x) + Q'.abs (JTPInstance.amp a M + JTPInstance.amp a M)

/-- The additive coefficient `c M = |prodDeriv fk dk x M · (amp+amp)|`. -/
def cFun (a x : Q') (M : Nat) : Q' :=
  Q'.abs (prodDeriv (fkθ a) (dkθ a) x M * dkθ a M)

/-! ## 1. General telescoping: `runningCap g c M ≤ (∏ g)·(∑ c)`.

Pure `Q'`, arbitrary `g`, `c` with `g_i ≥ 1`, `c_j ≥ 0`.  The empty product is `1`,
the empty sum is `0`. -/

/-- The prefix product `∏_{i<M} g_i` (empty product `= 1`). -/
def prodP (g : Nat → Q') : Nat → Q'
  | 0     => 1
  | M + 1 => prodP g M * g M

/-- The prefix sum `∑_{j<M} c_j` (empty sum `= 0`). -/
def sumC (c : Nat → Q') : Nat → Q'
  | 0     => 0
  | M + 1 => sumC c M + c M

/-- `∏_{i<M} g_i ≥ 1` when every `g_i ≥ 1`. -/
theorem prodP_ge_one (g : Nat → Q') (hg : ∀ i, (1 : Q') ≤ g i) :
    ∀ M, (1 : Q') ≤ prodP g M
  | 0     => Q'.le_refl' 1
  | M + 1 => by
    have ih := prodP_ge_one g hg M
    have hP0 : (0 : Q') ≤ prodP g M := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) ih
    -- prodP g M ≤ prodP g M * g M (multiply the ≥1 factor)
    have hstep : prodP g M ≤ prodP g M * g M := by
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv (prodP g M))) ?_
      exact Q'.mul_le_mul_of_nonneg_left 1 (g M) (prodP g M) (hg M) hP0
    exact Q'.le_trans' _ _ _ ih hstep

/-- `∑_{j<M} c_j ≥ 0` when every `c_j ≥ 0`. -/
theorem sumC_nonneg (c : Nat → Q') (hc : ∀ j, (0 : Q') ≤ c j) :
    ∀ M, (0 : Q') ≤ sumC c M
  | 0     => Q'.le_refl' 0
  | M + 1 => Q'.zero_le_add _ _ (sumC_nonneg c hc M) (hc M)

/-- **The telescoping running-cap bound.**  For `g_i ≥ 1`, `c_j ≥ 0`,

    runningCap g c M ≤ (∏_{i<M} g_i) · (∑_{j<M} c_j).

Induction: base `0 ≤ 1·0`; step chains monotonicity of `runningCap`, the product
factor `∏g·g ≥ 1` (so `c_M ≤ (∏g·g)·c_M`), and the ring rearrangement
`g·(∏g·∑c) ≈ (∏g·g)·∑c`. -/
theorem runningCap_le_prodP_sumC (g c : Nat → Q')
    (hg : ∀ i, (1 : Q') ≤ g i) (hc : ∀ j, (0 : Q') ≤ c j) :
    ∀ M, runningCap g c M ≤ prodP g M * sumC c M
  | 0     => by
    show (0 : Q') ≤ (1 : Q') * (0 : Q')
    exact Q'.ge_of_eqv (Q'.mul_zero_eqv (1 : Q'))
  | M + 1 => by
    have ih := runningCap_le_prodP_sumC g c hg hc M
    show g M * runningCap g c M + c M ≤ prodP g M * g M * (sumC c M + c M)
    -- abbreviations for readability
    have hGnn : (0 : Q') ≤ g M := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) (hg M)
    have hP1 := prodP_ge_one g hg M
    have hP0 : (0 : Q') ≤ prodP g M := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) hP1
    -- 1 ≤ prodP g M * g M
    have hPG1 : (1 : Q') ≤ prodP g M * g M := by
      refine Q'.le_trans' _ _ _ hP1 ?_
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv (prodP g M))) ?_
      exact Q'.mul_le_mul_of_nonneg_left 1 (g M) (prodP g M) (hg M) hP0
    -- c M ≤ (prodP g M * g M) * c M
    have hcc : c M ≤ prodP g M * g M * c M := by
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (c M))) ?_
      exact Q'.mul_le_mul_of_nonneg_right 1 (prodP g M * g M) (c M) hPG1 (hc M)
    -- LHS ≤ g M * (prodP·sumC) + c M
    have h1 : g M * runningCap g c M ≤ g M * (prodP g M * sumC c M) :=
      Q'.mul_le_mul_of_nonneg_left _ _ (g M) ih hGnn
    have hL : g M * runningCap g c M + c M
        ≤ g M * (prodP g M * sumC c M) + c M :=
      Q'.add_le_add h1 (Q'.le_refl' (c M))
    -- g M * (prodP·sumC) ≈ (prodP·g M)·sumC
    have hGPS : g M * (prodP g M * sumC c M) ≈ prodP g M * g M * sumC c M :=
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (g M) (prodP g M) (sumC c M)))
        (Q'.mul_eqv_congr_right _ _ (sumC c M) (Q'.mul_comm_eqv (g M) (prodP g M)))
    -- g M * (prodP·sumC) + c M ≤ (prodP·g M)·(sumC + c M)
    have hR : g M * (prodP g M * sumC c M) + c M
        ≤ prodP g M * g M * (sumC c M + c M) := by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ (c M) hGPS)) ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add (Q'.le_refl' (prodP g M * g M * sumC c M)) hcc) ?_
      exact Q'.le_of_eqv
        (Q'.eqv_symm (Q'.mul_add_eqv (prodP g M * g M) (sumC c M) (c M)))
    exact Q'.le_trans' _ _ _ hL hR

/-- Uniform caps `∏ g ≤ P`, `∑ c ≤ S` (both nonneg) give `runningCap g c M ≤ P·S`. -/
theorem runningCap_le_of_caps (g c : Nat → Q')
    (hg : ∀ i, (1 : Q') ≤ g i) (hc : ∀ j, (0 : Q') ≤ c j)
    (P S : Q') (hP : ∀ M, prodP g M ≤ P) (hPnn : (0 : Q') ≤ P)
    (hS : ∀ M, sumC c M ≤ S) (M : Nat) :
    runningCap g c M ≤ P * S := by
  refine Q'.le_trans' _ _ _ (runningCap_le_prodP_sumC g c hg hc M) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (hP M) (sumC_nonneg c hc M)) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ (hS M) hPnn

/-! ## 2. The head lower bound `g_M ≥ 1` on the Chebyshev domain. -/

/-- The elementary identity `(1−A)² + 2A ≥ 1` (i.e. `(1−A)²+2A = 1+A²`), for `A ≥ 0`.
Obtained by specialising `JTPInstance.jFac_split_abs` at `c = 0`:

    1 + A²  ≈  1 + ((A+A)·0 + A·A)  ≈  (1+(−A))² + (A+A)·(0+1)  ≈  (1+(−A))² + (A+A),

then `1 ≤ 1 + A²` from `A·A ≥ 0`. -/
theorem oneSubSq_add_two_ge_one (A : Q') (hA : (0 : Q') ≤ A) :
    (1 : Q') ≤ (1 + (-A)) * (1 + (-A)) + (A + A) := by
  have base := JTPInstance.jFac_split_abs A 0
  -- LHS of base ≈ 1 + A*A
  have hLHS : (1 + ((A + A) * 0 + A * A)) ≈ (1 + A * A) := by
    refine Q'.add_eqv_congr_left 1 _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ 0 (A * A) (Q'.mul_zero_eqv (A + A))) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (A * A))
  -- RHS of base ≈ (1+(-A))² + (A+A)
  have hRHS : ((1 + (-A)) * (1 + (-A)) + (A + A) * (0 + 1))
      ≈ ((1 + (-A)) * (1 + (-A)) + (A + A)) := by
    refine Q'.add_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (A + A) (0 + 1) 1 (Q'.eqv_of_eq (Q'.zero_add' 1))) ?_
    exact Q'.mul_one_eqv (A + A)
  have hid : (1 + A * A) ≈ ((1 + (-A)) * (1 + (-A)) + (A + A)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hLHS) (Q'.eqv_trans _ _ _ base hRHS)
  have hAA : (0 : Q') ≤ A * A := Q'.mul_nonneg A A hA hA
  have h1 : (1 : Q') ≤ 1 + A * A := Q'.add_le_self_of_nonneg 1 (A * A) hAA
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv hid)

/-- **`g_M ≥ 1` on `x ∈ [−1,1]`.**  From `jFac_lb` (`(1−amp)² ≤ jFac`), `a ≤ |a|`,
and the identity `(1−amp)² + 2·amp ≥ 1`:

    1 ≤ (1−amp)² + (amp+amp) ≤ |jFac a M x| + |amp+amp| = g M. -/
theorem gFun_ge_one {a : Q'} (ha0 : (0 : Q') ≤ a) (x : Q') (hx : (-1 : Q') ≤ x)
    (M : Nat) : (1 : Q') ≤ gFun a x M := by
  have hA : (0 : Q') ≤ JTPInstance.amp a M := JTPInstance.amp_nonneg ha0 M
  -- (1−amp)² ≤ |jFac|
  have hjf : (1 + (-(JTPInstance.amp a M))) * (1 + (-(JTPInstance.amp a M)))
      ≤ JTPInstance.jFac a M x := JTPInstance.jFac_lb ha0 M hx
  have hjabs : (1 + (-(JTPInstance.amp a M))) * (1 + (-(JTPInstance.amp a M)))
      ≤ Q'.abs (JTPInstance.jFac a M x) :=
    Q'.le_trans' _ _ _ hjf (Q'.le_abs_self _)
  -- (amp+amp) ≤ |amp+amp|
  have hdabs : (JTPInstance.amp a M + JTPInstance.amp a M)
      ≤ Q'.abs (JTPInstance.amp a M + JTPInstance.amp a M) := Q'.le_abs_self _
  -- add and prepend the identity floor
  have hsum : (1 + (-(JTPInstance.amp a M))) * (1 + (-(JTPInstance.amp a M)))
        + (JTPInstance.amp a M + JTPInstance.amp a M)
      ≤ gFun a x M := Q'.add_le_add hjabs hdabs
  exact Q'.le_trans' _ _ _ (oneSubSq_add_two_ge_one (JTPInstance.amp a M) hA) hsum

/-! ## 3. The honest residual and the running-cap bundle. -/

/-- **The honest uniform-cap residual (AGENTS.md Rule 6/8).**  The two outstanding
analytic inputs to `hBrun_le`: a uniform product cap `P` for `∏_{i<M} g_i` and a
uniform partial-sum cap `S` for `∑_{j<M} c_j`, both strictly positive.  Everything
else in the bundle is proved. -/
structure HinCaps (a x : Q') : Type where
  /-- The uniform product cap. -/
  P : Q'
  /-- Strict positivity of the product cap. -/
  hPpos : (0 : Q') < P
  /-- `∏_{i<M} g_i ≤ P` for every prefix length. -/
  hPcap : ∀ M, prodP (gFun a x) M ≤ P
  /-- The uniform partial-sum cap. -/
  S : Q'
  /-- Strict positivity of the sum cap. -/
  hSpos : (0 : Q') < S
  /-- `∑_{j<M} c_j ≤ S` for every prefix length. -/
  hScap : ∀ M, sumC (cFun a x) M ≤ S

/-- **The running-cap bundle for the theta product.**  Seven fields discharged
outright; the eighth (`hBrun_le`) reduced to the two `HinCaps` uniform caps via
`runningCap_le_of_caps`, `gFun_ge_one`, and `Q'.abs_nonneg`.  The global prefactor
is `B := P·S`. -/
def hinRunningCap {a : Q'} (ha0 : (0 : Q') < a) (x : Q') (hx : (-1 : Q') ≤ x)
    (caps : HinCaps a x) :
    ProdSecondDiffRunningInputs (fkθ a) (dkθ a) x (caps.P * caps.S) where
  hBpos := HKPos.q_mul_pos caps.hPpos caps.hSpos
  g := gFun a x
  hgnn := fun _ => JTPInstance.add_nonneg' (Q'.abs_nonneg _) (Q'.abs_nonneg _)
  c := cFun a x
  hcnn := fun _ => Q'.abs_nonneg _
  F := fun M h => cFun a x M * (h * h)
  hFc := fun _ _ _ => Q'.le_refl' _
  hstep := fun M h hh1 =>
    hstep_of_vanishing (fkθ a) (dkθ a) x M h hh1
      (DkProducerClose.jacFdRem_vanishes a M x h)
  hBrun_le := fun M =>
    runningCap_le_of_caps (gFun a x) (cFun a x)
      (fun i => gFun_ge_one (Q'.le_of_lt ha0) x hx i)
      (fun _ => Q'.abs_nonneg _)
      caps.P caps.S caps.hPcap (Q'.le_of_lt caps.hPpos) caps.hScap M

/-- **The downstream residual.**  Feeding `hinRunningCap` through
`prodSecondDiffOfRunning` yields the exact `ProdSecondDiffResidual` datum consumed
by `prodFlatModulus` / `prodUnifModulus` / `fdboundFlat`. -/
def hinResidual {a : Q'} (ha0 : (0 : Q') < a) (x : Q') (hx : (-1 : Q') ≤ x)
    (caps : HinCaps a x) :
    ProdSecondDiffResidual (fkθ a) (dkθ a) x (caps.P * caps.S) :=
  prodSecondDiffOfRunning (hinRunningCap ha0 x hx caps)

end YMGap.Continuum.HinRunningCapClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HinRunningCapClose.prodP_ge_one
#print axioms YMGap.Continuum.HinRunningCapClose.sumC_nonneg
#print axioms YMGap.Continuum.HinRunningCapClose.runningCap_le_prodP_sumC
#print axioms YMGap.Continuum.HinRunningCapClose.runningCap_le_of_caps
#print axioms YMGap.Continuum.HinRunningCapClose.oneSubSq_add_two_ge_one
#print axioms YMGap.Continuum.HinRunningCapClose.gFun_ge_one
#print axioms YMGap.Continuum.HinRunningCapClose.hinRunningCap
#print axioms YMGap.Continuum.HinRunningCapClose.hinResidual
