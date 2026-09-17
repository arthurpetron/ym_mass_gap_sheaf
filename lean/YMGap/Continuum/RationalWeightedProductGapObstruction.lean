/-
# A finite obstruction to transporting one-factor gaps through endpoint weights

The fixed positive stochastic symmetric kernel is k tensor k, where
k=[[3/4,1/4],[1/4,3/4]]. Its positive endpoint weight is (9,1,1,9)
and its probe is (1,0,0,-1), in the displayed four-state order.
The ORIGINAL weighted marginal is a*(K a), not uniform counting measure.
Its centered probe has raw norm 108, transfer cross 81 and energy 27.
Thus the one-factor floor/cap fraction 1/3 is not a universal weighted gap.

The actual division-free coordinate residuals sum to the probe and each
satisfies the proposed bound, but their mixed energy is negative. The exact
defect computations isolate the cross-energy issue; they are not estimates
for a physical Yang--Mills model. This refutes neither a corrected smaller
constant nor a separately justified volume-uniform interacting theorem.
-/

import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.RationalWeightedProductGapObstruction

set_option autoImplicit false

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

abbrev State := Bool × Bool

/-- The state order is 00, 01, 10, 11; all sums are literal finite sums. -/
def sum4 (f : State → Q') : Q' :=
  ((f (false, false) + f (false, true)) + f (true, false)) + f (true, true)

def singleKernel (x y : Bool) : Q' :=
  if x = y then Q'.mkPos 3 4 (by decide) else Q'.mkPos 1 4 (by decide)

def kernel (x y : State) : Q' := singleKernel x.1 y.1 * singleKernel x.2 y.2

def applyKernel (f : State → Q') (x : State) : Q' :=
  sum4 (fun y => kernel x y * f y)

def endpoint (x : State) : Q' := if x.1 = x.2 then 9 else 1

def probe : State → Q'
  | (false, false) => 1
  | (true, true) => -1
  | _ => 0

def marginal (a : State → Q') (x : State) : Q' := a x * applyKernel a x

def mean (a f : State → Q') : Q' := sum4 (fun x => marginal a x * f x)

def normPair (a f g : State → Q') : Q' :=
  sum4 (fun x => marginal a x * f x * g x)

def crossPair (a f g : State → Q') : Q' :=
  sum4 (fun x => a x * f x * applyKernel (fun y => a y * g y) x)

/-- The original symmetric edge energy, with BOTH endpoint factors retained. -/
def energyPair (a f g : State → Q') : Q' :=
  Q'.mkPos 1 2 (by decide) *
    sum4 (fun x => sum4 (fun y =>
      a x * kernel x y * a y * (f x + -(f y)) * (g x + -(g y))))

def norm (a f : State → Q') : Q' := normPair a f f

def cross (a f : State → Q') : Q' := crossPair a f f

def energy (a f : State → Q') : Q' := energyPair a f f

def singleFactorRatio : Q' := Q'.mkPos 1 3 (by decide)

theorem singleKernel_window (x y : Bool) :
    Q'.mkPos 1 4 (by decide) ≤ singleKernel x y ∧
      singleKernel x y ≤ Q'.mkPos 3 4 (by decide) := by
  cases x <;> cases y <;> decide

/-- 1/3 is precisely this one-factor lower/upper ratio. -/
theorem singleFactorRatio_pin :
    singleFactorRatio * Q'.mkPos 3 4 (by decide) ≈ Q'.mkPos 1 4 (by decide) := by
  decide

theorem kernel_positive (x y : State) : (0 : Q') < kernel x y := by
  rcases x with ⟨x0, x1⟩
  rcases y with ⟨y0, y1⟩
  cases x0 <;> cases x1 <;> cases y0 <;> cases y1 <;> decide

theorem kernel_stochastic (x : State) : sum4 (kernel x) ≈ 1 := by
  rcases x with ⟨x0, x1⟩
  cases x0 <;> cases x1 <;> decide

theorem kernel_symmetric (x y : State) : kernel x y ≈ kernel y x := by
  rcases x with ⟨x0, x1⟩
  rcases y with ⟨y0, y1⟩
  cases x0 <;> cases x1 <;> cases y0 <;> cases y1 <;> decide

theorem endpoint_positive (x : State) : (0 : Q') < endpoint x := by
  rcases x with ⟨x0, x1⟩
  cases x0 <;> cases x1 <;> decide

theorem applyKernel_endpoint (x : State) :
    applyKernel endpoint x ≈ if x.1 = x.2 then 6 else 4 := by
  rcases x with ⟨x0, x1⟩
  cases x0 <;> cases x1 <;> decide

theorem marginal_endpoint (x : State) :
    marginal endpoint x ≈ if x.1 = x.2 then 54 else 4 := by
  rcases x with ⟨x0, x1⟩
  cases x0 <;> cases x1 <;> decide

theorem marginal_mass : sum4 (marginal endpoint) ≈ 116 := by decide

theorem mean_probe_zero : mean endpoint probe ≈ 0 := by decide

theorem norm_probe : norm endpoint probe ≈ 108 := by decide

theorem cross_probe : cross endpoint probe ≈ 81 := by decide

theorem energy_probe : energy endpoint probe ≈ 27 := by decide

theorem energy_probe_difference :
    energy endpoint probe ≈ norm endpoint probe + -(cross endpoint probe) := by decide

theorem energy_probe_quarter :
    energy endpoint probe ≈ Q'.mkPos 1 4 (by decide) * norm endpoint probe := by decide

theorem energy_probe_lt_singleFactorRatio :
    energy endpoint probe < singleFactorRatio * norm endpoint probe := by decide

/-- Positivity and centering do NOT preserve the one-factor floor/cap gap,
even for this fixed two-factor positive symmetric stochastic kernel. -/
theorem no_universal_singleFactor_gap :
    ¬ (∀ a f : State → Q', (∀ x, (0 : Q') < a x) → mean a f ≈ 0 →
      singleFactorRatio * norm a f ≤ energy a f) := by
  intro h
  exact (by decide : ¬ (singleFactorRatio * norm endpoint probe ≤ energy endpoint probe))
    (h endpoint probe endpoint_positive mean_probe_zero)

/-- Coordinate Haar averages in this finite model, retaining the other bit. -/
def projectFirst (f : State → Q') (x : State) : Q' :=
  Q'.mkPos 1 2 (by decide) * (f (false, x.2) + f (true, x.2))

def projectSecond (f : State → Q') (x : State) : Q' :=
  Q'.mkPos 1 2 (by decide) * (f (x.1, false) + f (x.1, true))

def firstResidual (x : State) : Q' :=
  projectFirst endpoint x * probe x + -(projectFirst (fun y => endpoint y * probe y) x)

def secondResidual (x : State) : Q' :=
  projectSecond endpoint x * probe x + -(projectSecond (fun y => endpoint y * probe y) x)

theorem firstResidual_values :
    firstResidual (false, false) ≈ Q'.mkPos 1 2 (by decide) ∧
    firstResidual (false, true) ≈ Q'.mkPos 9 2 (by decide) ∧
    firstResidual (true, false) ≈ -(Q'.mkPos 9 2 (by decide)) ∧
    firstResidual (true, true) ≈ -(Q'.mkPos 1 2 (by decide)) := by decide

theorem secondResidual_values :
    secondResidual (false, false) ≈ Q'.mkPos 1 2 (by decide) ∧
    secondResidual (false, true) ≈ -(Q'.mkPos 9 2 (by decide)) ∧
    secondResidual (true, false) ≈ Q'.mkPos 9 2 (by decide) ∧
    secondResidual (true, true) ≈ -(Q'.mkPos 1 2 (by decide)) := by decide

theorem firstResidual_weighted_centered (x : State) :
    projectFirst (fun y => endpoint y * firstResidual y) x ≈ 0 := by
  rcases x with ⟨x0, x1⟩
  cases x0 <;> cases x1 <;> decide

theorem secondResidual_weighted_centered (x : State) :
    projectSecond (fun y => endpoint y * secondResidual y) x ≈ 0 := by
  rcases x with ⟨x0, x1⟩
  cases x0 <;> cases x1 <;> decide

theorem residual_sum (x : State) : firstResidual x + secondResidual x ≈ probe x := by
  rcases x with ⟨x0, x1⟩
  cases x0 <;> cases x1 <;> decide

theorem residuals_marginal_centered :
    mean endpoint firstResidual ≈ 0 ∧ mean endpoint secondResidual ≈ 0 := by decide

theorem residual_norms :
    norm endpoint firstResidual ≈ 189 ∧ norm endpoint secondResidual ≈ 189 := by decide

theorem residual_energies :
    energy endpoint firstResidual ≈ Q'.mkPos 297 2 (by decide) ∧
      energy endpoint secondResidual ≈ Q'.mkPos 297 2 (by decide) := by decide

/-- Both actual centered sectors individually satisfy the proposed fraction. -/
theorem residual_sector_bounds :
    singleFactorRatio * norm endpoint firstResidual ≤ energy endpoint firstResidual ∧
      singleFactorRatio * norm endpoint secondResidual ≤ energy endpoint secondResidual := by decide

theorem residual_mixed_norm : normPair endpoint firstResidual secondResidual ≈ -135 := by decide

theorem residual_mixed_transfer : crossPair endpoint firstResidual secondResidual ≈ 0 := by decide

theorem residual_mixed_energy : energyPair endpoint firstResidual secondResidual ≈ -135 := by decide

/-- Each diagonal gap defect is positive, but the mixed gap defect is negative. -/
theorem residual_gap_defects :
    energy endpoint firstResidual + -(singleFactorRatio * norm endpoint firstResidual) ≈
      Q'.mkPos 171 2 (by decide) ∧
    energy endpoint secondResidual + -(singleFactorRatio * norm endpoint secondResidual) ≈
      Q'.mkPos 171 2 (by decide) ∧
    energyPair endpoint firstResidual secondResidual +
      -(singleFactorRatio * normPair endpoint firstResidual secondResidual) ≈ -90 := by decide

/-- The sum of these two centered residuals violates the proposed fraction. -/
theorem probe_gap_defect :
    energy endpoint probe + -(singleFactorRatio * norm endpoint probe) ≈ -9 := by decide

end YMGap.Continuum.RationalWeightedProductGapObstruction

#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.State
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.sum4
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.singleKernel
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.kernel
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.applyKernel
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.endpoint
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.probe
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.marginal
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.mean
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.normPair
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.crossPair
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.energyPair
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.norm
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.cross
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.energy
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.singleFactorRatio
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.singleKernel_window
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.singleFactorRatio_pin
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.kernel_positive
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.kernel_stochastic
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.kernel_symmetric
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.endpoint_positive
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.applyKernel_endpoint
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.marginal_endpoint
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.marginal_mass
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.mean_probe_zero
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.norm_probe
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.cross_probe
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.energy_probe
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.energy_probe_difference
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.energy_probe_quarter
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.energy_probe_lt_singleFactorRatio
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.no_universal_singleFactor_gap
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.projectFirst
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.projectSecond
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.firstResidual
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.secondResidual
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.firstResidual_values
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.secondResidual_values
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.firstResidual_weighted_centered
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.secondResidual_weighted_centered
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.residual_sum
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.residuals_marginal_centered
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.residual_norms
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.residual_energies
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.residual_sector_bounds
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.residual_mixed_norm
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.residual_mixed_transfer
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.residual_mixed_energy
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.residual_gap_defects
#print axioms YMGap.Continuum.RationalWeightedProductGapObstruction.probe_gap_defect
