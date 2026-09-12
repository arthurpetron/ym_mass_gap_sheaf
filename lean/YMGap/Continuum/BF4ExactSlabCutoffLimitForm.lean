/-
# One original reflected form on all finite boundary observables

Observables may have different explicit cutoff witnesses. Their limit
pairing is evaluated at a common anchor and the already-computed exact
interface saturation index. The original finite pairing agrees with it at
every sufficiently large cutoff.

All form laws are transported from one common finite cutoff chosen by
explicit maxima. Thus equality is independent of cutoff witnesses, and
addition, scalar multiplication, symmetry and positivity belong to the
SAME original signed law. No limit-form law is assumed as an input.
-/

import YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable

namespace YMGap.Continuum.BF4ExactSlabCutoffLimitForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit
open YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Same original signed kernel and same actual finite state list. -/
def finiteForm (w : Q') (K : Nat) (a b : BoundaryObservable) : Q' :=
  finiteJointBilinear (centralHalfStates K 0) a.coefficient b.coefficient
    (exactCorrectedSlabReflectedKernel w K 0)

def limitForm (w : Q') (a b : BoundaryObservable) : Q' :=
  exactCutoffPairingValue w (max a.cutoff b.cutoff) a.coefficient b.coefficient

def formModulus (w : Q') (a b : BoundaryObservable) : Nat :=
  exactCutoffPairingModulus w (max a.cutoff b.cutoff) a.coefficient b.coefficient

/-- A computed common stage relates the actual finite forms to this one form. -/
theorem finiteForm_stable (w : Q') (K : Nat) (a b : BoundaryObservable)
    (hK : formModulus w a b ≤ K) : finiteForm w K a b ≈ limitForm w a b := by
  have he : exactCutoffPairing w (max a.cutoff b.cutoff) K a.coefficient b.coefficient ≈
      finiteForm w K a b :=
    finiteJointBilinear_coefficient_eqv_on _ _ _ _ _ _
      (fun state _ => a.extension_eqv _ (Nat.le_max_left _ _) state)
      (fun state _ => b.extension_eqv _ (Nat.le_max_right _ _) state)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm he)
    (exactCutoffPairing_stable w _ K a.coefficient b.coefficient hK)

/-- In particular, changing only the stored finite witness cannot change B. -/
theorem limitForm_congr_left (w : Q') (a a' b : BoundaryObservable)
    (h : a.CoefficientEqv a') : limitForm w a b ≈ limitForm w a' b := by
  let K := max (formModulus w a b) (formModulus w a' b)
  have ha := finiteForm_stable w K a b (Nat.le_max_left _ _)
  have hb := finiteForm_stable w K a' b (Nat.le_max_right _ _)
  have he : finiteForm w K a b ≈ finiteForm w K a' b :=
    finiteJointBilinear_coefficient_eqv_on _ _ _ _ _ _
      (fun state _ => h state) (fun _ _ => Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm ha) (Q'.eqv_trans _ _ _ he hb)

theorem limitForm_add_left (w : Q') (a b c : BoundaryObservable) :
    limitForm w (a.add b) c ≈ limitForm w a c + limitForm w b c := by
  let K := max (formModulus w (a.add b) c) (max (formModulus w a c) (formModulus w b c))
  have hab := finiteForm_stable w K (a.add b) c (Nat.le_max_left _ _)
  have ha := finiteForm_stable w K a c (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  have hb := finiteForm_stable w K b c (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have he : finiteForm w K (a.add b) c ≈ finiteForm w K a c + finiteForm w K b c :=
    finiteJointBilinear_add_left _ _ _ _ _
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hab) (Q'.eqv_trans _ _ _ he (Q'.add_eqv_congr' ha hb))

theorem limitForm_smul_left (w s : Q') (a b : BoundaryObservable) :
    limitForm w (a.smul s) b ≈ s * limitForm w a b := by
  let K := max (formModulus w (a.smul s) b) (formModulus w a b)
  have hs := finiteForm_stable w K (a.smul s) b (Nat.le_max_left _ _)
  have ha := finiteForm_stable w K a b (Nat.le_max_right _ _)
  have he : finiteForm w K (a.smul s) b ≈ s * finiteForm w K a b :=
    finiteJointBilinear_scale_left _ s _ _ _
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hs)
    (Q'.eqv_trans _ _ _ he (Q'.mul_eqv_congr_left _ _ _ ha))

theorem limitForm_symm (w : Q') (a b : BoundaryObservable) : limitForm w a b ≈ limitForm w b a := by
  let K := max (formModulus w a b) (formModulus w b a)
  have hab := finiteForm_stable w K a b (Nat.le_max_left _ _)
  have hba := finiteForm_stable w K b a (Nat.le_max_right _ _)
  have he : finiteForm w K a b ≈ finiteForm w K b a :=
    finiteJointBilinear_swap_of_symmetric _ _ _ _
      (fun l r _ _ => exactCorrectedSlabReflectedKernel_symmetric w K l r)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hab) (Q'.eqv_trans _ _ _ he hba)

theorem limitForm_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (a : BoundaryObservable) :
    (0 : Q') ≤ limitForm w a a :=
  exactCutoffPairingValue_nonnegative hw _ a.coefficient

/-- The new form is pinned to the previously proved ORIGINAL anchored
limit for every supplied finite coefficient function. -/
theorem limitForm_ofCoefficients (w : Q') (anchor : Nat) (a b : EdgeLabelling → Q') :
    limitForm w (BoundaryObservable.ofCoefficients anchor a) (BoundaryObservable.ofCoefficients anchor b) ≈
      exactCutoffPairingValue w anchor a b := by
  let x := BoundaryObservable.ofCoefficients anchor a
  let y := BoundaryObservable.ofCoefficients anchor b
  let K := max (formModulus w x y) (exactCutoffPairingModulus w anchor a b)
  have hform := finiteForm_stable w K x y (Nat.le_max_left _ _)
  have hanchor := exactCutoffPairing_stable w anchor K a b (Nat.le_max_right _ _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hform) hanchor

/-- One GNS datum containing all finite anchor cutoffs, with no fixed K
parameter. Every field is proved for the ORIGINAL signed cutoff-limit form. -/
def cutoffLimitGNSData (w : Q') (hw : (0 : Q') ≤ w) : GNSData where
  V := BoundaryObservable
  veq := BoundaryObservable.CoefficientEqv
  veq_refl := fun _ _ => Q'.eqv_refl _
  veq_symm := fun h state => Q'.eqv_symm (h state)
  veq_trans := fun h k state => Q'.eqv_trans _ _ _ (h state) (k state)
  zero := BoundaryObservable.zero
  add := BoundaryObservable.add
  neg := BoundaryObservable.neg
  smul := BoundaryObservable.smul
  add_congr := fun h k state => Q'.add_eqv_congr' (h state) (k state)
  neg_congr := fun h state => Q'.neg_eqv_congr _ _ (h state)
  smul_congr := by
    intro s a a' h state
    exact Q'.mul_eqv_congr_left s _ _ (h state)
  add_assoc := fun a b c state => Q'.add_assoc_eqv (a.coefficient state) (b.coefficient state) (c.coefficient state)
  add_comm := fun a b state => Q'.add_comm_eqv (a.coefficient state) (b.coefficient state)
  zero_add := fun a state => Q'.eqv_of_eq (Q'.zero_add' (a.coefficient state))
  neg_add := fun a state => Q'.neg_add_self_eqv (a.coefficient state)
  B := limitForm w
  B_congr_left := by
    intro a a' b h
    exact limitForm_congr_left w a a' b h
  B_add_left := limitForm_add_left w
  B_smul_left := limitForm_smul_left w
  B_symm := limitForm_symm w
  self_nonneg := limitForm_nonnegative hw

theorem cutoffLimitGNSData_form (w : Q') (hw : (0 : Q') ≤ w) (a b : BoundaryObservable) :
    (cutoffLimitGNSData w hw).B a b = limitForm w a b := rfl

end YMGap.Continuum.BF4ExactSlabCutoffLimitForm

#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.finiteForm
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.limitForm
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.formModulus
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.finiteForm_stable
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.limitForm_congr_left
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.limitForm_add_left
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.limitForm_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.limitForm_symm
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.limitForm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.limitForm_ofCoefficients
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.cutoffLimitGNSData
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitForm.cutoffLimitGNSData_form
