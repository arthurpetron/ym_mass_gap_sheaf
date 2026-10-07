/-
# The trace route on a real carrier: strong coupling (non-vacuity) and one
# intermediate-coupling certified interval

ADDITIVE.  Attaches `SpectralHalvingMargin` to the existing all-nome Wilson carrier.

* `scFamily W`: the literal width-`W` all-nome Wilson carrier at the pilot nome
  `w = 1/1024`, dyadic spacing `2^-j`, rate `timeRate` (`≈ 1/4`, by
  `allNome_strongCoupling_vacuumSq_all_widths`).  Unconditional.
* `rateModel`: the one-mode `SpectralModel` with `λ₀ = timeRate`.
* `scFamily_hlink` (PROVED): `(scFamily W).rate j ≤ specMax rateModel`.
  **CIRCULAR / non-vacuity only**: the model is built from the known rate.
* `scFamily_trace` (PROVED): `excitedTrace rateModel (1·2^j) ≤ 1/2` for all `j`.
* `scFamily_lowerMargin_via_trace` (PROVED): the full
  `wilsonLowerMargin_of_traceCertificates` chain instantiated, giving
  `WilsonLowerMargin (scFamily W) (1/2)`: every hypothesis is satisfiable.
* Genuine-link no-go at this nome (PROVED): the heat-kernel excited character
  model `excitedCharModel w N` has `specMax ≤ w³ < timeRate`
  (`excitedChar_specMax_lt_rate`), so `hlink` FAILS for it: the 1/4 rate is a
  crude cluster bound, not a heat-kernel eigenvalue.
* Intermediate coupling (`w = 1/2`, three excited spins): certified interval
  `1/9 ≤ specMax ≤ 13/100` from exact rational traces via
  `specMax_mem_of_trace_bounds`.  This certifies the closed-form model's top
  eigenvalue only; the link to any Wilson rate at `w = 1/2` is OPEN (no
  intermediate-coupling `WilsonDynamicFamily` rate exists: the strong-coupling
  guards fail there).

U(1) rule: all statements here are group-blind except through the carrier
(`scFamily` is the SU(2) quaternion carrier; `rateModel` and the trace algebra are
group-blind).  Nothing here is refuted by U(1) since no large-β claim is made.
Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.SpectralHalvingMargin
import YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate
import YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
import YMGap.Continuum.WilsonSpectralBridge

namespace YMGap.Continuum.SpectralHalvingStrongCouplingCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.Continuum.SpectralGap (SpectralModel)
open YMGap.Continuum (specMax)
open YMGap.Continuum.SpectralTraceSandwich (excitedTrace specMax_mem_of_trace_bounds)
open YMGap.Continuum.SpectralHalvingMargin (wilsonLowerMargin_of_traceCertificates)
open YMGap.Continuum.BF4WilsonHalvingTimeMargin (halvingMargin)
open YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily (WilsonDynamicFamily WilsonLowerMargin)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay
  (timeRate timeRate_positive timeRate_lt_one)
open YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate
  (allNome_strongCoupling_vacuumSq_all_widths)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
  (dyadicPhysicalSpacing dyadicSpacingToZero)
open YMGap.Continuum.WilsonSpectralBridge (excitedCharModel)

/-- The literal width-`W` all-nome carrier at `w = 1/1024`, rate `timeRate`. -/
def scFamily (W : Nat) : WilsonDynamicFamily where
  nome := fun _ => nome
  nome_pos := fun _ => nome_pos
  nome_lt_one := fun _ => nome_lt_one
  width := fun _ => W
  transferSpacing := dyadicPhysicalSpacing
  transferSpacingToZero := dyadicSpacingToZero
  rate := fun _ => timeRate
  rate_nonnegative := fun _ => Q'.le_of_lt timeRate_positive
  rate_lt_one := fun _ => timeRate_lt_one
  contraction := fun _ =>
    allNome_strongCoupling_vacuumSq_all_widths nome_pos nome_lt_one
      existingNome_guards.1 existingNome_guards.2 existingNome_entropyRate.2 W

/-- One-mode model carrying the known rate (CIRCULAR by construction). -/
def rateModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => timeRate
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => Q'.le_of_lt timeRate_positive

theorem rate_le_specMax_rateModel : timeRate ≤ specMax rateModel := by decide

/-- `hlink` on the real carrier (CIRCULAR: non-vacuity, no new information). -/
theorem scFamily_hlink (W j : Nat) : (scFamily W).rate j ≤ specMax rateModel :=
  rate_le_specMax_rateModel

theorem timeRate_le_half : timeRate ≤ half := by decide

/-- `r^(n+1) ≤ r` for `0 ≤ r ≤ 1`. -/
theorem pow_succ_le_self (r : Q') (h0 : (0 : Q') ≤ r) (h1 : r ≤ 1) (n : Nat) :
    r ^ (n + 1) ≤ r := by
  show r * r ^ n ≤ r
  have hp : r ^ n ≤ (1 : Q') ^ n := YMGap.Continuum.SpectralGap.pow_le_pow_left h0 h1 n
  have hq : r ^ n ≤ 1 :=
    Q'.le_trans' _ _ _ hp
      (Q'.le_of_eqv (YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling.lc_one_pow n))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ r hq h0)
    (Q'.le_of_eqv (Q'.mul_one_eqv r))

theorem scFamily_trace (j : Nat) : excitedTrace rateModel (1 * 2 ^ j) ≤ half := by
  have hpos : 0 < 1 * 2 ^ j := Nat.mul_pos (by decide) (Nat.two_pow_pos j)
  obtain ⟨m, hm⟩ : ∃ m, 1 * 2 ^ j = m + 1 := ⟨1 * 2 ^ j - 1, by omega⟩
  rw [hm]
  show (0 : Q') + timeRate ^ (m + 1) ≤ half
  rw [Q'.zero_add']
  exact Q'.le_trans' _ _ _
    (pow_succ_le_self timeRate (Q'.le_of_lt timeRate_positive)
      (Q'.le_of_lt timeRate_lt_one) m) timeRate_le_half

/-- **Non-vacuity of the whole trace chain** on the real strong-coupling carrier. -/
theorem scFamily_lowerMargin_via_trace (W : Nat) :
    WilsonLowerMargin (scFamily W) (halvingMargin 1) :=
  wilsonLowerMargin_of_traceCertificates (scFamily W) 1 (by decide) (fun _ => rfl)
    (fun _ => rateModel) (fun _ => half) (fun j => scFamily_hlink W j)
    scFamily_trace (fun _ => Q'.le_refl' _)

/-! ## Genuine link fails for the heat-kernel model at `w = 1/1024` -/

theorem nome_cube_lt_rate : YMGap.Continuum.RGTransport.qpow nome 3 < timeRate := by decide

/-- Every excited heat-kernel eigenvalue at the pilot nome is `≤ w³ < timeRate`:
`hlink` with `excitedCharModel` is FALSE for this carrier's rate. -/
theorem excitedChar_specMax_lt_rate (N : Nat) :
    specMax (excitedCharModel nome (Q'.le_of_lt nome_pos) N) ≤
      YMGap.Continuum.RGTransport.qpow nome 3 :=
  (YMGap.Continuum.specMax_le_iff _ _ (by decide)).2 fun i _ =>
    YMGap.Continuum.WilsonSpectralBridge.casimir_qpow_le (Q'.le_of_lt nome_pos)
      (Q'.le_of_lt nome_lt_one) i

/-! ## Intermediate coupling `w = 1/2`: certified interval -/

def wMid : Q' := Q'.mkPos 1 2 (by decide)

theorem wMid_nonneg : (0 : Q') ≤ wMid := by decide

def midModel : SpectralModel := excitedCharModel wMid wMid_nonneg 3

theorem midModel_interval :
    Q'.mkPos 1 9 (by decide) ≤ specMax midModel ∧
      specMax midModel ≤ Q'.mkPos 13 100 (by decide) :=
  specMax_mem_of_trace_bounds midModel 1 (by decide) _ _
    (excitedTrace midModel 2) (excitedTrace midModel 1) (by decide) (by decide)
    (Q'.le_refl' _) (Q'.le_refl' _) (by decide) (by decide)

end YMGap.Continuum.SpectralHalvingStrongCouplingCarrier
#print axioms YMGap.Continuum.SpectralHalvingStrongCouplingCarrier.scFamily_hlink
#print axioms YMGap.Continuum.SpectralHalvingStrongCouplingCarrier.scFamily_lowerMargin_via_trace
#print axioms YMGap.Continuum.SpectralHalvingStrongCouplingCarrier.excitedChar_specMax_lt_rate
#print axioms YMGap.Continuum.SpectralHalvingStrongCouplingCarrier.nome_cube_lt_rate
#print axioms YMGap.Continuum.SpectralHalvingStrongCouplingCarrier.midModel_interval
