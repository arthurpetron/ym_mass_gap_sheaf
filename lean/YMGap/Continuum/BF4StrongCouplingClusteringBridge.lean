/-
# Strong-coupling clustering from the vacuum-orthogonal contraction (+ explicit torus bridge)

**Labels: U(1)-true. Fixed-coupling gap (small nome `w ≤ 1/1024` regime).
NOT evidence for a non-abelian mass gap.**

Proved on the BF4 all-nome heat-kernel carrier (`Completion hw0 hw1 width`), uniform in `width`:

* `vacuumSq_iterate`: a one-step contraction `B(T y,T y) ≤ r² B(y,y)` on the vacuum
  complement iterates to `B(T^m y, T^m y) ≤ (r²)^m B(y,y)` (T preserves the complement).
* `even_correlator_decay`: the truncated (vacuum-orthogonal) correlator at lag `n = 2m`,
  `B(y, T^(2m) y) = B(T^m y, T^m y) ≤ (r²)^m B(y,y)`.
* `strongCoupling_even_correlator_decay` / `pilot_even_correlator_decay`: with
  `allNome_strongCoupling_vacuumSq` (`r = timeRate`, `timeRate = 1/4`), at `w = 1/1024`
  every width has `B(y, T^n y) ≤ timeRate^n B(y,y)` for even `n`, i.e. `(1/4)^n` decay.

**Bridge (OPEN, explicit hypothesis).** The SU(2) Wilson `T_K` torus carrier
(`SU2ClusterBridge.cov`, `SU2TorusNormalizedRatio.Ehat`) and the BF4 heat-kernel carrier are
different; no identification exists in the repo. `TorusChiBridge` states as a HYPOTHESIS that
the torus χ1 normalized covariance `Ehat m = cov(2m)` is dominated by `C·B(y, T^(2m) y)` for
one vacuum-orthogonal BF4 vector `y`. Under it, `torus_chi_decay_of_bridge` gives
`Ehat m ≤ C·(timeRate²)^m·B(y,y)`. Without the bridge, the torus side already has the
unconditional rate `λ = 6/7` (`SU2ClusterBridge.cov_decay`), not `1/4`.
`SpectralGap.decay_of_spectralGap_corr0` is a finite diagonal-mode model; it is not
instantiated on either carrier and is not consumed (see the audit).

Odd lags are not treated. Axioms: `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate
import YMGap.Continuum.SU2TorusNormalizedRatio

namespace YMGap.Continuum.BF4StrongCouplingClusteringBridge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_zero completedTime_add VacuumComplement
   completedTime_preserves_vacuumComplement completedInner_time_sum)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate timeRate_positive)
open YMGap.Continuum.BF4WilsonStrongCouplingUniformRate (existingPilotNome)
open YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate
  (existingNome_allNome_strongCoupling)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plane)
open YMGap.Continuum.SU2TorusNormalizedRatio (Ehat)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

section Carrier

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Iterated vacuum-orthogonal contraction: `B(T^m y, T^m y) ≤ (r²)^m B(y,y)`. -/
theorem vacuumSq_iterate (r : Q') (hr : (0 : Q') ≤ r * r)
    (h : WilsonVacuumSqContraction hw0 hw1 width r) :
    ∀ (m : Nat) (y : VacuumComplement hw0 hw1 (width := width)),
      RCle (B (T m y.val) (T m y.val)) (RCscale ((r * r) ^ m) (B y.val y.val))
  | 0, y => by
    rw [completedTime_zero hw0 hw1, show (r * r) ^ 0 = (1 : Q') from rfl, RCscale_one]
    exact RCle_refl _
  | m + 1, y => by
    have h1 := h ⟨T m y.val, completedTime_preserves_vacuumComplement hw0 hw1 m y.val y.property⟩
    have h2 := RCscale_mono hr (vacuumSq_iterate r hr h m y)
    rw [RCscale_RCscale] at h2
    have hT : T (m + 1) y.val = T 1 (T m y.val) := by
      rw [Nat.add_comm m 1]; exact completedTime_add hw0 hw1 1 m y.val
    rw [hT]
    exact RCle_trans h1 h2

/-- **Truncated even-lag correlator decay** on the vacuum complement:
`B(y, T^(2m) y) ≤ (r²)^m B(y,y)`. -/
theorem even_correlator_decay (r : Q') (hr : (0 : Q') ≤ r * r)
    (h : WilsonVacuumSqContraction hw0 hw1 width r) (m : Nat)
    (y : VacuumComplement hw0 hw1 (width := width)) :
    RCle (B y.val (T (2 * m) y.val)) (RCscale ((r * r) ^ m) (B y.val y.val)) := by
  rw [Nat.two_mul, ← completedInner_time_sum (width := width) hw0 hw1 m m y.val y.val]
  exact vacuumSq_iterate hw0 hw1 width r hr h m y

/-- **OPEN bridge (explicit hypothesis).** The SU(2) torus χ1 normalized covariance at lag
`2m` is dominated by `C·B(y, T^(2m) y)` for a vacuum-orthogonal BF4 vector `y`. -/
def TorusChiBridge {M : Nat} (K b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width)) (C : Q') : Prop :=
  ∀ m : Nat, RCle (Rq (Ehat (M := M) K b c d plane m)) (RCscale C (B y.val (T (2 * m) y.val)))

/-- Under the OPEN bridge, the torus χ1 covariance inherits the BF4 rate. -/
theorem torus_chi_decay_of_bridge (r : Q') (hr : (0 : Q') ≤ r * r)
    (h : WilsonVacuumSqContraction hw0 hw1 width r) {M : Nat} (K b c d : Nat)
    (plane : Z4Plane) (y : VacuumComplement hw0 hw1 (width := width)) (C : Q')
    (hC : (0 : Q') ≤ C) (hbr : TorusChiBridge hw0 hw1 width (M := M) K b c d plane y C)
    (m : Nat) :
    RCle (Rq (Ehat (M := M) K b c d plane m)) (RCscale (C * (r * r) ^ m) (B y.val y.val)) := by
  have h1 := RCscale_mono hC (even_correlator_decay hw0 hw1 width r hr h m y)
  rw [RCscale_RCscale] at h1
  exact RCle_trans (hbr m) h1

end Carrier

/-- **Pilot strong-coupling clustering (unconditional, BF4 carrier).** At `w = 1/1024`,
every width: `B(y, T^(2m) y) ≤ (timeRate²)^m B(y,y)` on the vacuum complement,
`timeRate = 1/4`. U(1)-true; fixed-coupling gap; NOT non-abelian mass-gap evidence. -/
theorem pilot_even_correlator_decay :
    let w := existingPilotNome
    ∃ (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')),
      ∀ (width m : Nat) (y : VacuumComplement hw0 hw1 (width := width)),
        RCle (completedInner hw0 hw1 y.val (completedTime hw0 hw1 (2 * m) y.val))
          (RCscale ((timeRate * timeRate) ^ m) (completedInner hw0 hw1 y.val y.val)) := by
  intro w
  obtain ⟨hw0, hw1, hpos, _, hc⟩ := existingNome_allNome_strongCoupling
  have hr : (0 : Q') ≤ timeRate * timeRate :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hpos) (Q'.le_of_lt hpos)
  exact ⟨hw0, hw1, fun width m y => even_correlator_decay hw0 hw1 width timeRate hr (hc width) m y⟩

end YMGap.Continuum.BF4StrongCouplingClusteringBridge
