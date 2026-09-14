/-
# Positive ORIGINAL interacting minor at every translated volume and cutoff

At the existing fixed nome, the four signed amplitude errors are small
relative to the SAME full spectator background Zsp. The exact-rational
pilot's coefficient margin is independently checked by the kernel.
The actual whole-forest determinant is at most -(signal/2)*Zsp^2;
its square therefore has the explicit positive floor ((signal/2)*Zsp^2)^2.

The floor still contains Zsp. A comparison to the SAME full original
partition and homogeneous reference budget is needed before a normalized
volume-uniform excitation floor can pass to the thermodynamic completion.
No continuum, coupling-uniform gap, or canonical frontier closure is claimed.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation
import YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor

namespace YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels (channelWeightPower)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor (product_upper_of_abs)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound (determinant)

local infix:50 " ≈ " => Q'.eqv

def eta : Q' := productErrorCap nome 24
def unitProbeCap : Q' := 2*eta
def unitUnitCap : Q' := eta
def scalarProbeCap : Q' := channelWeightPower nome 4 * ((2*eta)*Q'.invSucc 255)
def scalarUnitCap : Q' := channelWeightPower nome 4 * (eta*Q'.invSucc 255)
def margin : Q' := signal nome * HalfPow.half

/-- The pilot's margin, checked on exact rational expressions, not imported as data. -/
theorem coefficient_guards :
    (0 : Q') ≤ 1 + -unitUnitCap ∧ (0 : Q') ≤ signal nome + -scalarProbeCap ∧
    unitProbeCap*scalarUnitCap + -((signal nome + -scalarProbeCap)*(1 + -unitUnitCap)) ≤ -margin ∧
    (0 : Q') < margin := by decide

private theorem regroup (a b c d : Q') : a*(b*(c*d)) ≈ (a*(b*c))*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)))
    (Q'.eqv_symm (Q'.mul_assoc_eqv a (b*c) d))

private theorem lower_from_error {x b e d : Q'} (hx : x ≈ b+e) (he : Q'.abs e ≤ d) : b + -d ≤ x :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_left b _ _ (Q'.le_trans' _ _ _ (Q'.neg_le_neg he) (ExpNeg.neg_abs_le e)))
    (Q'.ge_of_eqv hx)

private theorem subtract_scale (a b z : Q') : (a + -b)*z ≈ a*z + -(b*z) :=
  poly_identity_of_normal_eq (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
    (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2)))) (by decide)
    (fun | 0 => a | 1 => b | _ => z)

variable (K : Nat) (hK : 1 ≤ K) (half : Nat)

local notation "hw" => Q'.le_of_lt nome_pos
local notation "Z" => backgroundMass nome K half
local notation "A0" e => testAmplitude hw K hK half (localChoice half none) (spectatorHeat nome K half) e
local notation "A1" e => testAmplitude hw K hK half (localChoice half (some (false,false))) (scalarTest nome K half) e

theorem unitProbe_abs : Q'.abs (A0 (bulkProbe half)) ≤ unitProbeCap * Z := by
  have h := Q'.eqv_trans _ _ _ (unitAmplitude_split hw K hK (bulkProbe half))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (unit_probe_zero hw K half))
      (Q'.eqv_of_eq (Q'.zero_add' _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr h))
    (unitProbe_error_bound hw (Q'.le_of_lt nome_lt_one) existingNome_guards.1 (Q'.le_of_lt existingNome_guards.2) K half)

theorem scalarUnit_abs : Q'.abs (A1 .unit) ≤ scalarUnitCap * Z := by
  have h := Q'.eqv_trans _ _ _ (scalarAmplitude_split hw K hK (.unit : PlaquetteExpression half))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (scalar_unit_zero hw K half))
      (Q'.eqv_of_eq (Q'.zero_add' _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr h))
    (Q'.le_trans' _ _ _
      (scalarUnit_error_bound hw (Q'.le_of_lt nome_lt_one) existingNome_guards.1 (Q'.le_of_lt existingNome_guards.2) K half)
      (Q'.le_of_eqv (regroup _ _ _ _)))

theorem unitUnit_lower : (1 + -unitUnitCap)*Z ≤ A0 .unit := by
  have h := Q'.eqv_trans _ _ _ (unitAmplitude_split hw K hK (.unit : PlaquetteExpression half))
    (Q'.add_eqv_congr_right _ _ _ (unit_unit_pin hw K half))
  have he := unitUnit_error_bound hw (Q'.le_of_lt nome_lt_one) existingNome_guards.1 (Q'.le_of_lt existingNome_guards.2) K half
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (subtract_scale 1 unitUnitCap Z)
    (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv Z)))) (lower_from_error h he)

theorem scalarProbe_lower : (signal nome + -scalarProbeCap)*Z ≤ A1 (bulkProbe half) := by
  have h := Q'.eqv_trans _ _ _ (scalarAmplitude_split hw K hK (bulkProbe half))
    (Q'.add_eqv_congr_right _ _ _ (scalar_probe_pin hw K half))
  have he := Q'.le_trans' _ _ _
    (scalarProbe_error_bound hw (Q'.le_of_lt nome_lt_one) existingNome_guards.1 (Q'.le_of_lt existingNome_guards.2) K half)
    (Q'.le_of_eqv (regroup (channelWeightPower nome 4) (2*eta) (Q'.invSucc 255) Z))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (subtract_scale (signal nome) scalarProbeCap Z)) (lower_from_error h he)

def interactingDeterminant : Q' := determinant (A0 (bulkProbe half)) (A1 (bulkProbe half)) (A0 .unit) (A1 .unit)

private theorem determinant_model (a b c d s z : Q') :
    (a*z)*(d*z) + -(((s + -c)*z)*((1 + -b)*z)) ≈
      (a*d + -((s + -c)*(1 + -b)))*(z*z) :=
  poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.var 5)) (.mul (.var 3) (.var 5)))
      (.neg (.mul (.mul (.add (.var 4) (.neg (.var 2))) (.var 5))
        (.mul (.add (.const 1) (.neg (.var 1))) (.var 5)))))
    (.mul (.add (.mul (.var 0) (.var 3))
      (.neg (.mul (.add (.var 4) (.neg (.var 2))) (.add (.const 1) (.neg (.var 1)))))) (.mul (.var 5) (.var 5)))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | 3 => d | 4 => s | _ => z)

/-- The actual interacting determinant, not the collar-removed reference. -/
theorem interactingDeterminant_upper : interactingDeterminant K hK half ≤ -(margin*(Z*Z)) := by
  have hz := Q'.le_of_lt (existingNome_background_positive K half)
  have hU : (0 : Q') ≤ (1 + -unitUnitCap)*Z := Q'.mul_nonneg _ _ coefficient_guards.1 hz
  have hP : (0 : Q') ≤ (signal nome + -scalarProbeCap)*Z := Q'.mul_nonneg _ _ coefficient_guards.2.1 hz
  have hprod := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (scalarProbe_lower K hK half) hU)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (unitUnit_lower K hK half)
      (Q'.le_trans' _ _ _ hP (scalarProbe_lower K hK half)))
  have herr := product_upper_of_abs (unitProbe_abs K hK half) (scalarUnit_abs K hK half)
  exact Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 herr (Q'.neg_le_neg hprod))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (determinant_model unitProbeCap unitUnitCap scalarProbeCap scalarUnitCap (signal nome) Z))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ coefficient_guards.2.2.1 (SumOfSquares.q_mul_self_nonneg Z))
        (Q'.le_of_eqv (Q'.neg_mul_eqv margin (Z*Z)))))

omit hK in
def interactingMinorFloor (K half : Nat) : Q' :=
  let z := backgroundMass nome K half
  (margin*(z*z))*(margin*(z*z))

private theorem neg_square (a : Q') : (-a)*(-a) ≈ a*a :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-a))
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a a)) (Q'.neg_neg_eqv _))

/-- Explicit floor on the ORIGINAL centering-invariant whole-forest minor. -/
theorem interactingMinor_floor : interactingMinorFloor K half ≤ localMinor hw K hK half := by
  have hz := existingNome_background_positive K half
  have hm := Q'.le_of_lt (Q'.mul_pos coefficient_guards.2.2.2 (Q'.mul_pos hz hz))
  have hd : margin*(Z*Z) ≤ -(interactingDeterminant K hK half) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv _)) (Q'.neg_le_neg (interactingDeterminant_upper K hK half))
  have hn := Q'.le_trans' _ _ _ hm hd
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hd hm)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hd hn)
      (Q'.le_of_eqv (neg_square (interactingDeterminant K hK half))))

omit hK in
theorem interactingMinorFloor_positive (K half : Nat) : (0 : Q') < interactingMinorFloor K half := by
  have hz := existingNome_background_positive K half
  have hm := Q'.mul_pos coefficient_guards.2.2.2 (Q'.mul_pos hz hz)
  exact Q'.mul_pos hm hm

theorem interactingMinor_positive : (0 : Q') < localMinor hw K hK half :=
  Q'.pos_of_lt_of_le (interactingMinorFloor_positive K half) (interactingMinor_floor K hK half)

end YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.eta
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.unitProbeCap
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.unitUnitCap
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.scalarProbeCap
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.scalarUnitCap
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.margin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.coefficient_guards
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.unitProbe_abs
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.scalarUnit_abs
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.unitUnit_lower
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.scalarProbe_lower
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.interactingDeterminant
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.interactingDeterminant_upper
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.interactingMinorFloor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.interactingMinor_floor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.interactingMinorFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingMinor.interactingMinor_positive
