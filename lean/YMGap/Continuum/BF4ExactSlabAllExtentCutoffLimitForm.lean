/-
# One original cutoff-limit GNS form at each odd slab extent

All finite boundary observables, with arbitrary explicit cutoff witnesses,
belong to one carrier per slab. Their common limit form is pinned to the
ORIGINAL finite signed bilinear at a computed stage. Congruence, addition
and scalar laws are transported from explicit common finite cutoffs.

Symmetry comes from the original mixed-channel Gram theorem; positivity
comes from original reflection positivity. No GNS law is assumed. The
result is a family of slab forms, not compatibility between those slabs,
physical time, a stationary vacuum, strict gap or continuum QFT.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
import YMGap.Continuum.BF4ExactSlabAllExtentBilinearGram

namespace YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentBilinearGram
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Same original signed kernel and actual finite state list. -/
def finiteForm (w : Q') (K : Nat) {half : Nat} (a b : BoundaryObservable half) : Q' :=
  finiteJointBilinear (centralHalfStates K half) a.coefficient b.coefficient
    (exactCorrectedSlabReflectedKernel w K half)

def limitForm (w : Q') {half : Nat} (a b : BoundaryObservable half) : Q' :=
  exactCutoffPairingValue w (max a.cutoff b.cutoff) half a.coefficient b.coefficient

def formModulus (w : Q') {half : Nat} (a b : BoundaryObservable half) : Nat :=
  exactCutoffPairingModulus w (max a.cutoff b.cutoff) half a.coefficient b.coefficient

theorem finiteForm_stable (w : Q') (K : Nat) {half : Nat} (a b : BoundaryObservable half)
    (hK : formModulus w a b ≤ K) : finiteForm w K a b ≈ limitForm w a b := by
  have he : exactCutoffPairing w (max a.cutoff b.cutoff) K half a.coefficient b.coefficient ≈ finiteForm w K a b :=
    finiteJointBilinear_coefficient_eqv_on _ _ _ _ _ _
      (fun state _ => a.extension_eqv _ (Nat.le_max_left _ _) state)
      (fun state _ => b.extension_eqv _ (Nat.le_max_right _ _) state)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm he)
    (exactCutoffPairing_stable w _ K half a.coefficient b.coefficient hK)

/-- Changing only a stored cutoff witness cannot change the pairing. -/
theorem limitForm_congr_left (w : Q') {half : Nat} (a a' b : BoundaryObservable half)
    (h : a.CoefficientEqv a') : limitForm w a b ≈ limitForm w a' b := by
  let K := max (formModulus w a b) (formModulus w a' b)
  have ha := finiteForm_stable w K a b (Nat.le_max_left _ _)
  have hb := finiteForm_stable w K a' b (Nat.le_max_right _ _)
  have he : finiteForm w K a b ≈ finiteForm w K a' b :=
    finiteJointBilinear_coefficient_eqv_on _ _ _ _ _ _ (fun state _ => h state) (fun _ _ => Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm ha) (Q'.eqv_trans _ _ _ he hb)

theorem limitForm_add_left (w : Q') {half : Nat} (a b c : BoundaryObservable half) :
    limitForm w (a.add b) c ≈ limitForm w a c + limitForm w b c := by
  let K := max (formModulus w (a.add b) c) (max (formModulus w a c) (formModulus w b c))
  have hab := finiteForm_stable w K (a.add b) c (Nat.le_max_left _ _)
  have ha := finiteForm_stable w K a c (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  have hb := finiteForm_stable w K b c (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have he : finiteForm w K (a.add b) c ≈ finiteForm w K a c + finiteForm w K b c :=
    finiteJointBilinear_add_left _ _ _ _ _
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hab) (Q'.eqv_trans _ _ _ he (Q'.add_eqv_congr' ha hb))

theorem limitForm_smul_left (w s : Q') {half : Nat} (a b : BoundaryObservable half) :
    limitForm w (a.smul s) b ≈ s * limitForm w a b := by
  let K := max (formModulus w (a.smul s) b) (formModulus w a b)
  have hs := finiteForm_stable w K (a.smul s) b (Nat.le_max_left _ _)
  have ha := finiteForm_stable w K a b (Nat.le_max_right _ _)
  have he : finiteForm w K (a.smul s) b ≈ s * finiteForm w K a b :=
    finiteJointBilinear_scale_left _ s _ _ _
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hs) (Q'.eqv_trans _ _ _ he (Q'.mul_eqv_congr_left _ _ _ ha))

theorem limitForm_symm {w : Q'} (hw : (0 : Q') ≤ w) {half : Nat} (a b : BoundaryObservable half) :
    limitForm w a b ≈ limitForm w b a := by
  let K := max (formModulus w a b) (formModulus w b a)
  have hab := finiteForm_stable w K a b (Nat.le_max_left _ _)
  have hba := finiteForm_stable w K b a (Nat.le_max_right _ _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hab)
    (Q'.eqv_trans _ _ _ (exact_bilinear_symmetric hw K half a.coefficient b.coefficient) hba)

theorem limitForm_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) {half : Nat} (a : BoundaryObservable half) :
    (0 : Q') ≤ limitForm w a a := exactCutoffPairingValue_nonnegative hw _ half a.coefficient

/-- Each original finite anchor is identified with its independently constructed limit. -/
theorem limitForm_ofCoefficients (w : Q') (half anchor : Nat) (a b : EdgeLabelling → Q') :
    limitForm w (BoundaryObservable.ofCoefficients half anchor a) (BoundaryObservable.ofCoefficients half anchor b) ≈
      exactCutoffPairingValue w anchor half a b := by
  let x := BoundaryObservable.ofCoefficients half anchor a
  let y := BoundaryObservable.ofCoefficients half anchor b
  let K := max (formModulus w x y) (exactCutoffPairingModulus w anchor half a b)
  have hform := finiteForm_stable w K x y (Nat.le_max_left _ _)
  have hanchor := exactCutoffPairing_stable w anchor K half a b (Nat.le_max_right _ _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hform) hanchor

/-- Constructed original-law GNS datum at any odd extent, with no fixed K. -/
def cutoffLimitGNSData (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : GNSData where
  V := BoundaryObservable half
  veq := BoundaryObservable.CoefficientEqv
  veq_refl := fun _ _ => Q'.eqv_refl _
  veq_symm := fun h state => Q'.eqv_symm (h state)
  veq_trans := fun h k state => Q'.eqv_trans _ _ _ (h state) (k state)
  zero := BoundaryObservable.zero half
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
  B_smul_left := fun s a b => limitForm_smul_left w s a b
  B_symm := limitForm_symm hw
  self_nonneg := limitForm_nonnegative hw

theorem cutoffLimitGNSData_form (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (a b : BoundaryObservable half) :
    (cutoffLimitGNSData w hw half).B a b = limitForm w a b := by
  unfold cutoffLimitGNSData
  rfl

end YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.finiteForm
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.limitForm
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.formModulus
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.finiteForm_stable
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.limitForm_congr_left
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.limitForm_add_left
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.limitForm_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.limitForm_symm
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.limitForm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.limitForm_ofCoefficients
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.cutoffLimitGNSData
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm.cutoffLimitGNSData_form
