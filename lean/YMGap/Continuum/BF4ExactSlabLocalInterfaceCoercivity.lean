/-
# Only CHANGED physical crossing faces pay the finite comparison floor

Set the crossing nome to one on a selected Boolean face mask and keep the
original w everywhere else. The SAME p and every untouched heat factor
remain in both forms, even when variables overlap. The exact positive
lower factor is w^(sum of K_f(K_f+2) over changed physical faces).
Untouched face counts and cutoffs do not enter this factor.

For a common cutoff K this becomes w^(K(K+2)*changedFaceCount), instead
of the old whole-interface count. The constant target profile and actual
bulk-dressed p are pinned to the ORIGINAL full-action numerator.

This removes an unnecessary whole-interface loss, not the dependence on
changed-face cutoffs or w. No volume-uniform original-norm coercivity,
unshifted range approximation, injectivity, time-zero continuity,
physical Hamiltonian, continuum/QFT or Clay result follows here.
-/

import YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison
import YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity

namespace YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow c4 qpow_nonneg)
open YMGap.Continuum.HeatKernelRGStep (qpow_add qpow_antitone)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity (dressedLower dressedLower_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

def referenceNome (w : Q') (selected : Nat → Bool) (id : Nat) : Q' :=
  match selected id with | false => w | true => 1

theorem referenceNome_nonnegative (w : Q') (hw : (0 : Q') ≤ w) (selected : Nat → Bool) (id : Nat) :
    (0 : Q') ≤ referenceNome w selected id := by
  cases h : selected id <;> simp only [referenceNome,h]
  · exact hw
  · exact Q'.zero_le_one

def faceFactor (w : Q') (selected : Nat → Bool) (cutoff : Nat → Nat) (id : Nat) : Q' :=
  match selected id with | false => 1 | true => coefficientFloor w (cutoff id)

theorem faceFactor_nonnegative (w : Q') (hw : (0 : Q') ≤ w)
    (selected : Nat → Bool) (cutoff : Nat → Nat) (id : Nat) : (0 : Q') ≤ faceFactor w selected cutoff id := by
  cases h : selected id <;> simp only [faceFactor,h]
  · exact Q'.zero_le_one
  · exact qpow_nonneg w hw _

/-- Exact physical energy sum; no charge for an unchanged face. -/
def changedEnergy (selected : Nat → Bool) (cutoff : Nat → Nat) : List Nat → Nat
  | [] => 0
  | id::ids => (match selected id with | false => 0 | true => c4 (cutoff id)) + changedEnergy selected cutoff ids

theorem factorProduct_pin (w : Q') (selected : Nat → Bool) (cutoff : Nat → Nat) : ∀ ids : List Nat,
    factorProduct (faceFactor w selected cutoff) ids ≈ qpow w (changedEnergy selected cutoff ids)
  | [] => Q'.eqv_refl _
  | id::ids => by
      cases h : selected id
      · simp only [factorProduct,faceFactor,changedEnergy,h,Nat.zero_add]
        exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (factorProduct_pin w selected cutoff ids)
      · simp only [factorProduct,faceFactor,changedEnergy,h]
        exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (factorProduct_pin w selected cutoff ids))
          (Q'.eqv_symm (qpow_add w _ _))

def localFloor (w : Q') (selected : Nat → Bool) (cutoff : Nat → Nat) (half : Nat) : Q' :=
  qpow w (changedEnergy selected cutoff (centralFixedFaceIds half))

private theorem power_positive (w : Q') (hw : (0 : Q') < w) : ∀ n,(0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (power_positive w hw n) hw

theorem localFloor_positive (w : Q') (hw : (0 : Q') < w)
    (selected : Nat → Bool) (cutoff : Nat → Nat) (half : Nat) : (0 : Q') < localFloor w selected cutoff half :=
  power_positive w hw _

/-- A reference INTERFACE with all untouched w/cutoffs and the original p retained. -/
def localReference (w : Q') (selected : Nat → Bool) (cutoff : Nat → Nat) (half : Nat) (p : RatPoly) : Q' :=
  profileForm (referenceNome w selected) cutoff half p

theorem local_lower (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (selected : Nat → Bool) (cutoff : Nat → Nat) (half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    localFloor w selected cutoff half * localReference w selected cutoff half p ≤ profileForm (fun _ => w) cutoff half p := by
  have h := profile_form_comparison (referenceNome w selected) (fun _ => w) (faceFactor w selected cutoff)
    (referenceNome_nonnegative w hw0 selected) (fun _ => hw0) (faceFactor_nonnegative w hw0 selected cutoff)
    cutoff half p hp hl (by
      intro id _ s hs
      cases h : selected id <;> simp only [faceFactor,referenceNome,h]
      · exact Q'.le_of_eqv (Q'.one_mul_eqv _)
      · exact coefficient_lower w hw0 hw1 (cutoff id) s hs)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ (factorProduct_pin w selected cutoff _))) h

private theorem factorProduct_one : ∀ ids : List Nat, factorProduct (fun _ => (1 : Q')) ids ≈ 1
  | [] => Q'.eqv_refl _
  | _::ids => Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (factorProduct_one ids)

theorem local_upper (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (selected : Nat → Bool) (cutoff : Nat → Nat) (half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) : profileForm (fun _ => w) cutoff half p ≤ localReference w selected cutoff half p := by
  have h := profile_form_comparison (fun _ => w) (referenceNome w selected) (fun _ => 1)
    (fun _ => hw0) (referenceNome_nonnegative w hw0 selected) (fun _ => Q'.zero_le_one)
    cutoff half p hp hl (by
      intro id _ s _
      cases h : selected id <;> simp only [referenceNome,h]
      · exact Q'.le_of_eqv (Q'.one_mul_eqv _)
      · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) (coefficient_upper w hw0 hw1 s))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (factorProduct_one _)) (Q'.one_mul_eqv _))) h

def changedFaceCount (selected : Nat → Bool) (half : Nat) : Nat :=
  ((centralFixedFaceIds half).filter selected).length

theorem changedEnergy_constant (selected : Nat → Bool) (K : Nat) : ∀ ids : List Nat,
    changedEnergy selected (fun _ => K) ids=c4 K * (ids.filter selected).length
  | [] => (Nat.mul_zero _).symm
  | id::ids => by
      cases h : selected id <;> simp only [changedEnergy,List.filter,h,List.length_cons,
        changedEnergy_constant selected K ids,Nat.zero_add,Nat.mul_succ,Nat.add_comm]

/-- The exponent counts ONLY selected physical faces, not the whole interface. -/
theorem localFloor_constant (w : Q') (selected : Nat → Bool) (K half : Nat) :
    localFloor w selected (fun _ => K) half=qpow w (K*(K+2)*changedFaceCount selected half) := by
  unfold localFloor changedFaceCount
  rw [changedEnergy_constant]
  rfl

/-- Only selected cutoffs are bounded; every other cutoff is arbitrary. -/
theorem changedEnergy_bound (selected : Nat → Bool) (cutoff : Nat → Nat) (N : Nat) :
    ∀ ids : List Nat, (∀ id,id ∈ ids → selected id=true → cutoff id ≤ N) →
      changedEnergy selected cutoff ids ≤ c4 N * (ids.filter selected).length
  | [], _ => by simp only [changedEnergy,List.filter,List.length_nil,Nat.mul_zero,Nat.le_refl]
  | id::ids, hN => by
      have ht := changedEnergy_bound selected cutoff N ids (fun j hj => hN j (List.mem_cons_of_mem id hj))
      cases h : selected id
      · simpa only [changedEnergy,List.filter,h,Nat.zero_add] using ht
      · have hk := hN id List.mem_cons_self h
        have hc : c4 (cutoff id) ≤ c4 N := Nat.mul_le_mul hk (Nat.add_le_add_right hk 2)
        simpa only [changedEnergy,List.filter,h,List.length_cons,Nat.mul_succ,Nat.add_comm] using Nat.add_le_add hc ht

/-- One explicit floor for EVERY choice of untouched-face cutoffs. This is
not yet a lower estimate for the thermodynamic OS norm. -/
theorem local_lower_bounded (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (selected : Nat → Bool) (N half : Nat) (cutoff : Nat → Nat)
    (hN : ∀ id,id ∈ centralFixedFaceIds half → selected id=true → cutoff id ≤ N)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    qpow w (N*(N+2)*changedFaceCount selected half) * localReference w selected cutoff half p ≤
      profileForm (fun _ => w) cutoff half p :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (qpow_antitone hw0 hw1 _ _ (changedEnergy_bound selected cutoff N _ hN))
      (profileForm_nonnegative (referenceNome w selected) (referenceNome_nonnegative w hw0 selected) cutoff half p hp hl))
    (local_lower w hw0 hw1 selected cutoff half p hp hl)

def originalLocalReference (w : Q') (selected : Nat → Bool) (K : Nat)
    {half : Nat} (e : PlaquetteExpression half) : Q' :=
  localReference w selected (fun _ => K) half (dressedLower w K e)

/-- The right side is the ORIGINAL full interacting numerator, with its old proof pin. -/
theorem original_local_lower (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (selected : Nat → Bool) (K : Nat) {half : Nat} (e : PlaquetteExpression half) :
    qpow w (K*(K+2)*changedFaceCount selected half) * originalLocalReference w selected K e ≤ originalQuadratic w K e := by
  have h := local_lower w hw0 hw1 selected (fun _ => K) half (dressedLower w K e)
    (dressedLower_supported w K e) (dressedLower_local w K e)
  rw [profileForm_constant,localFloor_constant] at h
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (original_interface_pin w hw0 K e))

theorem original_local_upper (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (selected : Nat → Bool) (K : Nat) {half : Nat} (e : PlaquetteExpression half) :
    originalQuadratic w K e ≤ originalLocalReference w selected K e :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (original_interface_pin w hw0 K e))
    (local_upper w hw0 hw1 selected (fun _ => K) half (dressedLower w K e)
      (dressedLower_supported w K e) (dressedLower_local w K e))

end YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.referenceNome
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.referenceNome_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.faceFactor
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.faceFactor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.changedEnergy
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.factorProduct_pin
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.localFloor
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.localFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.localReference
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.local_lower
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.local_upper
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.changedFaceCount
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.changedEnergy_constant
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.localFloor_constant
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.changedEnergy_bound
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.local_lower_bounded
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.originalLocalReference
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.original_local_lower
#print axioms YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity.original_local_upper
