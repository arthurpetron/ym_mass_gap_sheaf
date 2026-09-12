/-
# Completed reflected carrier of the ORIGINAL finite-cutoff signed slab

The new exact-law positivity theorem supplies the last field of an actual
GNSData on signed boundary coefficient functions. Its B field is definitionally
the original finiteJointBilinear, not a positive-law comparison or replacement
Gram. The generic null quotient and CReal/RC completion therefore apply to
that precise reflected form.

The vacuum-code direction has norm one and is not null. No transfer or
stationarity is asserted for it. Scope: extent one and a fixed but arbitrary
cutoff K, w >= 0. This is NOT removal of K, a thermodynamic/continuum limit,
or the canonical positive-time root. Completeness uses the existing
representative-family, explicit-modulus API; no arbitrary quotient-valued
sequence is given a representative by choice.
-/

import YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
import YMGap.Continuum.GNSComplete

namespace YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-- The algebra is pointwise rational algebra, and B is the ORIGINAL
reflected signed kernel on the ORIGINAL bounded half-state list. -/
def exactGNSData (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : GNSData where
  V := EdgeLabelling → Q'
  veq := fun a b => ∀ state, (a state).eqv (b state)
  veq_refl := fun _ _ => Q'.eqv_refl _
  veq_symm := fun h state => Q'.eqv_symm (h state)
  veq_trans := fun h k state => Q'.eqv_trans _ _ _ (h state) (k state)
  zero := fun _ => 0
  add := fun a b state => a state + b state
  neg := fun a state => -a state
  smul := fun s a state => s * a state
  add_congr := fun h k state => Q'.add_eqv_congr' (h state) (k state)
  neg_congr := fun h state => Q'.neg_eqv_congr _ _ (h state)
  smul_congr := by
    intro s a b h state
    exact Q'.mul_eqv_congr_left s _ _ (h state)
  add_assoc := fun a b c state => Q'.add_assoc_eqv (a state) (b state) (c state)
  add_comm := fun a b state => Q'.add_comm_eqv (a state) (b state)
  zero_add := fun a state => Q'.eqv_of_eq (Q'.zero_add' (a state))
  neg_add := fun a state => Q'.neg_add_self_eqv (a state)
  B := fun a b => finiteJointBilinear (centralHalfStates K 0) a b (exactCorrectedSlabReflectedKernel w K 0)
  B_congr_left := by
    intro a a' b h
    exact finiteJointBilinear_coefficient_eqv_on _ a a' b b _ (fun s _ => h s) (fun _ _ => Q'.eqv_refl _)
  B_add_left := fun a b c => finiteJointBilinear_add_left _ a b c _
  B_smul_left := fun s a b => finiteJointBilinear_scale_left _ s a b _
  B_symm := fun a b => finiteJointBilinear_swap_of_symmetric _ a b _
    (fun l r _ _ => exactCorrectedSlabReflectedKernel_symmetric w K l r)
  self_nonneg := exact_quadratic_nonnegative hw K

theorem exactGNSData_form (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (a b : EdgeLabelling → Q') :
    (exactGNSData w hw K).B a b =
      finiteJointBilinear (centralHalfStates K 0) a b (exactCorrectedSlabReflectedKernel w K 0) := rfl

theorem exactGNSData_quadratic (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (a : EdgeLabelling → Q') :
    (exactGNSData w hw K).B a a = exactSlabAllCutoffQuadratic w K a := rfl

/-- Completion of this exact finite-cutoff reflected norm, with the
library's stated representative-family completeness boundary. -/
def exactCompletion (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    CompleteGNSHilbertGeneral (exactGNSData w hw K) := (exactGNSData w hw K).gnsComplete_general

abbrev ExactCarrier (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :=
  (exactCompletion w hw K).hilbert.carrier

def exactEmbed (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (a : EdgeLabelling → Q') : ExactCarrier w hw K :=
  (exactCompletion w hw K).hilbert.ι ((exactGNSData w hw K).qmk a)

/-- The completed pairing on the dense image is the SAME signed bilinear,
not just a norm comparison or a separately chosen finite Gram. -/
theorem exactEmbed_pairing (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (a b : EdgeLabelling → Q') :
    (exactCompletion w hw K).hilbert.cinner (exactEmbed w hw K a) (exactEmbed w hw K b) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ'
        (finiteJointBilinear (centralHalfStates K 0) a b (exactCorrectedSlabReflectedKernel w K 0))) :=
  (exactCompletion w hw K).hilbert.ι_inner a b

/-- An actual limit representative, including its Cauchy modulus, rather
than existence obtained by selecting representatives of quotient points. -/
def limitRepresentative (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (X : GeneralCompletionCauchy (exactGNSData w hw K)) : CauchyGNS (exactGNSData w hw K) := X.lim

theorem limitRepresentative_converges (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (X : GeneralCompletionCauchy (exactGNSData w hw K)) :
    ∀ ε : Q', (0 : Q') < ε → ∃ P : Nat, ∀ p : Nat, P ≤ p →
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        (exactGNSData w hw K).distSqQ ((X.pt p).seq n) ((limitRepresentative w hw K X).seq n) ≤ ε :=
  X.converges

theorem vacuumCode_norm (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    ((exactGNSData w hw K).B (vacuumCodeDelta K) (vacuumCodeDelta K)).eqv 1 :=
  exactSlabAllCutoffQuadratic_vacuumCodeDelta_eqv_one w K

theorem vacuumCode_not_null (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    ¬ (exactGNSData w hw K).rad (vacuumCodeDelta K) (exactGNSData w hw K).zero := by
  intro h
  have hz := ((exactGNSData w hw K).rad_zero_iff (vacuumCodeDelta K)).mp h
  have hbad : (1 : Q').eqv 0 := Q'.eqv_trans _ _ _ (Q'.eqv_symm (vacuumCode_norm w hw K)) hz
  exact (by decide : ¬ (1 : Q').eqv 0) hbad

theorem vacuumCode_completed_norm (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (exactCompletion w hw K).hilbert.cinner
      (exactEmbed w hw K (vacuumCodeDelta K)) (exactEmbed w hw K (vacuumCodeDelta K)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 1) :=
  (exactEmbed_pairing w hw K _ _).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (vacuumCode_norm w hw K)))

theorem vacuumCode_completed_ne_zero (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    exactEmbed w hw K (vacuumCodeDelta K) ≠ exactEmbed w hw K (fun _ => 0) := by
  intro h
  have he := (exactCompletion w hw K).hilbert.ι_injective h
  exact vacuumCode_not_null w hw K (Quotient.exact he)

end YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS

#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.exactGNSData
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.exactGNSData_form
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.exactGNSData_quadratic
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.exactCompletion
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.ExactCarrier
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.exactEmbed
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.exactEmbed_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.limitRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.limitRepresentative_converges
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.vacuumCode_norm
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.vacuumCode_not_null
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.vacuumCode_completed_norm
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS.vacuumCode_completed_ne_zero
