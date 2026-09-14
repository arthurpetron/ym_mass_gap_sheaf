/-
# Spectator-relative ORIGINAL centered norm floor, every cutoff and volume

The actual two-test reference budget is at most 2*s*Zsp^3. Together with
the original interacting minor floor (s/2)^2*Zsp^4, positive-factor
cancellation gives rawForm(P-c,P-c) >= (s/8)*Zsp for EVERY rational c.
Here s=(2*w^3)^4/32768 and w is the existing fixed nome 1/1024.

The coefficient s/8 is explicit and independent of cutoff and volume.
Zsp is still the full spectator partition, NOT the original full partition.
The SAME full-partition upper comparison and cutoff/thermodynamic limit
passages are separate downstream steps; this raw floor alone is not a
normalized excitation witness. No coupling-uniform gap or continuum
frontier is discharged.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor
import YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor

namespace YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference (bulkProbe)
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor (original_scalar_energy_pin)
open YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests (testAmplitude referenceEnergy)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS (rawForm rawForm_nonnegative)
open YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor (recentered)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor (product_upper_of_abs)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)

local infix:50 " ≈ " => Q'.eqv

def unitAmplitudeCap : Q' := 1 + unitUnitCap
def budgetCoefficient : Q' := 2 *
  (scalarUnitCap*scalarUnitCap + energyScale nome*(unitAmplitudeCap*unitAmplitudeCap))
def budgetCeiling : Q' := 2 * signal nome
def rawFloorCoefficient : Q' := signal nome * Q'.invSucc 7

/-- Exact-rational checks mirror the pilot; no external numerical oracle. -/
theorem homogeneous_guards :
    (0 : Q') ≤ energyScale nome ∧ budgetCoefficient ≤ budgetCeiling ∧
    (0 : Q') < budgetCeiling ∧ (0 : Q') < rawFloorCoefficient ∧
    rawFloorCoefficient*budgetCeiling ≈
      BF4ExactSlabBulkProbeInteractingMinor.margin*BF4ExactSlabBulkProbeInteractingMinor.margin := by decide

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

variable (K : Nat) (hK : 1 ≤ K) (half : Nat)

local notation "hw" => Q'.le_of_lt nome_pos
local notation "Z" => backgroundMass nome K half
local notation "A0" => testAmplitude hw K hK half (localChoice half none) (spectatorHeat nome K half)
local notation "A1" => testAmplitude hw K hK half (localChoice half (some (false,false))) (scalarTest nome K half)

theorem unitUnit_upper : A0 .unit ≤ unitAmplitudeCap*Z := by
  have h := Q'.eqv_trans _ _ _ (unitAmplitude_split hw K hK (.unit : PlaquetteExpression half))
    (Q'.add_eqv_congr_right _ _ _ (unit_unit_pin hw K half))
  have he := unitUnit_error_bound hw (Q'.le_of_lt nome_lt_one) existingNome_guards.1
    (Q'.le_of_lt existingNome_guards.2) K half
  have hsum := Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
    (Q'.add_le_add_left Z _ _ (Q'.le_trans' _ _ _ (Q'.le_abs_self _) he))
  have hp : (1+unitUnitCap)*Z ≈ Z+unitUnitCap*Z :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
      (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv Z))
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hp)

theorem unitUnit_nonnegative : (0 : Q') ≤ A0 .unit :=
  Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ coefficient_guards.1 (Q'.le_of_lt (existingNome_background_positive K half)))
    (unitUnit_lower K hK half)

theorem unitUnit_abs : Q'.abs (A0 .unit) ≤ unitAmplitudeCap*Z := by
  rw [ExpNeg.abs_of_nonneg (unitUnit_nonnegative K hK half)]
  exact unitUnit_upper K hK half

/-- Pin the budget to the original test energies, not the reference amplitudes. -/
theorem localReferenceBudget_pin : localReferenceBudget hw K hK half ≈
    2*(Z*(A1 .unit*A1 .unit) + (energyScale nome*Z)*(A0 .unit*A0 .unit)) :=
  Q'.mul_eqv_congr_left (2 : Q') _ _ (Q'.add_eqv_congr'
    (qmul (unitEnergy_pin hw K hK half) (Q'.eqv_refl _))
    (qmul (original_scalar_energy_pin hw K hK half) (Q'.eqv_refl _)))

private theorem budget_model (d e u z : Q') :
    2*(z*((d*z)*(d*z))+(e*z)*((u*z)*(u*z))) ≈
      (2*(d*d+e*(u*u)))*(z*z*z) :=
  poly_identity_of_normal_eq
    (.mul (.const 2) (.add (.mul (.var 3) (.mul (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 3))))
      (.mul (.mul (.var 1) (.var 3)) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))))))
    (.mul (.mul (.const 2) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 2)))))
      (.mul (.mul (.var 3) (.var 3)) (.var 3))) (by decide)
    (fun | 0 => d | 1 => e | 2 => u | _ => z)

private theorem budget_bound {a0 a1 d e u z : Q'}
    (hz : (0 : Q') ≤ z) (he : (0 : Q') ≤ e)
    (ha0 : Q'.abs a0 ≤ u*z) (ha1 : Q'.abs a1 ≤ d*z) :
    2*(z*(a1*a1)+(e*z)*(a0*a0)) ≤ (2*(d*d+e*(u*u)))*(z*z*z) := by
  have h0 := product_upper_of_abs ha0 ha0
  have h1 := product_upper_of_abs ha1 ha1
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
    (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ z h1 hz)
      (Q'.mul_le_mul_of_nonneg_left _ _ (e*z) h0 (Q'.mul_nonneg _ _ he hz)))
    (by decide : (0 : Q') ≤ 2)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (budget_model d e u z))

theorem localReferenceBudget_coefficient_bound :
    localReferenceBudget hw K hK half ≤ budgetCoefficient*(Z*Z*Z) := by
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (localReferenceBudget_pin K hK half))
    (budget_bound (Q'.le_of_lt (existingNome_background_positive K half)) homogeneous_guards.1
      (unitUnit_abs K hK half) (scalarUnit_abs K hK half))

/-- The coefficient 2*s is independent of K and half; Zsp is not. -/
theorem localReferenceBudget_upper : localReferenceBudget hw K hK half ≤ budgetCeiling*(Z*Z*Z) :=
  Q'.le_trans' _ _ _ (localReferenceBudget_coefficient_bound K hK half)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ homogeneous_guards.2.1
      (Q'.le_of_lt (Q'.mul_pos (Q'.mul_pos (existingNome_background_positive K half)
        (existingNome_background_positive K half)) (existingNome_background_positive K half))))

private theorem cancel_homogeneous {m r g z f : Q'}
    (hz : (0 : Q') < z) (hr : (0 : Q') < r) (hbalance : g*r ≈ m*m)
    (h : (m*(z*z))*(m*(z*z)) ≤ f*(r*(z*z*z))) : g*z ≤ f := by
  have hleft : (r*(z*z*z))*(g*z) ≈ (g*r)*((z*z)*(z*z)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.mul (.var 2) (.var 2)) (.var 2))) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => r | 1 => g | _ => z)
  have hsquare : (m*(z*z))*(m*(z*z)) ≈ (m*m)*((z*z)*(z*z)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1))))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => m | _ => z)
  have hpin := Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hbalance) (Q'.eqv_symm hsquare))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv f (r*(z*z*z))))))
    (Q'.mul_pos hr (Q'.mul_pos (Q'.mul_pos hz hz) hz))

include hK

/-- Every rational recentering, on the SAME original finite-volume form. -/
theorem rawForm_relative_floor (c : Q') : rawFloorCoefficient*Z ≤
    rawForm nome K (recentered half (bulkProbe half) c) (recentered half (bulkProbe half) c) := by
  have h := Q'.le_trans' _ _ _ (interactingMinor_floor K hK half)
    (Q'.le_trans' _ _ _ (localMinor_recentered_bound hw K hK half c)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (localReferenceBudget_upper K hK half)
        (rawForm_nonnegative nome hw K _)))
  exact cancel_homogeneous (existingNome_background_positive K half)
    homogeneous_guards.2.2.1 homogeneous_guards.2.2.2.2 h

theorem rawForm_recentered_positive (c : Q') : (0 : Q') <
    rawForm nome K (recentered half (bulkProbe half) c) (recentered half (bulkProbe half) c) :=
  Q'.pos_of_lt_of_le (Q'.mul_pos homogeneous_guards.2.2.2.1 (existingNome_background_positive K half))
    (rawForm_relative_floor K hK half c)

end YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.unitAmplitudeCap
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.budgetCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.budgetCeiling
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.rawFloorCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.homogeneous_guards
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.unitUnit_upper
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.unitUnit_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.unitUnit_abs
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.localReferenceBudget_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.localReferenceBudget_coefficient_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.localReferenceBudget_upper
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.rawForm_relative_floor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor.rawForm_recentered_positive
