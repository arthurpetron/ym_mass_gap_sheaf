/-
# An explicit original plaquette/channel minor test

The actual unit leaf and scalar closed-boundary coordinate leaf determine
an executable finite minor for the actual fundamental plaquette observable.
Its rational floor bounds every rational recentering of the ORIGINAL raw
reflected numerator. Two arbitrary leaf estimates cost a factor two; no
distinct-path certificate is required (coincident channels give zero minor).

No positivity of this concrete minor has been proved. Positive leaf weights
do not settle it. The normalized cutoff-limit excitation and physical gap
remain open.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
import YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor

namespace YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
open YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

variable (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)

local notation "tree" => LocalSquareExpansion.tree (interfaceExpansion hw K half)
local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent half))

theorem leaf_amplitude_bound (l : Leaf tree) (e : PlaquetteExpression half) :
    l.weight * (channelAmplitude w hw K half l e * channelAmplitude w hw K half l e) ≤ rawForm w K e e := by
  have h := (l.multiplyTerm 1 (dressedLower w K e)).value_le blocks
    (SquareTree.multiplyTerm_nonnegative 1 _ Q'.zero_le_one _ (interfaceExpansion hw K half).weightsNonnegative)
  rw [Leaf.multiplyTerm_weight, Leaf.multiplyTerm_channel] at h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)))
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (rawForm_eq_dressedSquareSum w hw K half e)))

def twoProbeEnergy (l r : Leaf tree) (e : PlaquetteExpression half) : Q' :=
  energy l.weight r.weight (channelAmplitude w hw K half l e) (channelAmplitude w hw K half r e)

def twoProbeMinor (l r : Leaf tree) (e : PlaquetteExpression half) : Q' :=
  minor l.weight r.weight (channelAmplitude w hw K half l e) (channelAmplitude w hw K half r e)
    (channelAmplitude w hw K half l .unit) (channelAmplitude w hw K half r .unit)

theorem twoProbeEnergy_nonnegative (l r : Leaf tree) (e : PlaquetteExpression half) :
    (0 : Q') ≤ twoProbeEnergy w hw K half l r e :=
  energy_nonnegative (Pair.weight_nonnegative l (interfaceExpansion hw K half).weightsNonnegative)
    (Pair.weight_nonnegative r (interfaceExpansion hw K half).weightsNonnegative) _ _

theorem twoProbeEnergy_bound (l r : Leaf tree) (e : PlaquetteExpression half) :
    twoProbeEnergy w hw K half l r e ≤ rawForm w K e e + rawForm w K e e :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (leaf_amplitude_bound w hw K half l e))
    (Q'.add_le_add_left _ _ _ (leaf_amplitude_bound w hw K half r e))

theorem twoProbeMinor_recentered (l r : Leaf tree) (e : PlaquetteExpression half) (c : Q') :
    twoProbeMinor w hw K half l r (recentered half e c) ≈ twoProbeMinor w hw K half l r e := by
  have h : determinant (channelAmplitude w hw K half l (recentered half e c))
      (channelAmplitude w hw K half r (recentered half e c))
      (channelAmplitude w hw K half l .unit) (channelAmplitude w hw K half r .unit) ≈
      determinant (channelAmplitude w hw K half l e) (channelAmplitude w hw K half r e)
        (channelAmplitude w hw K half l .unit) (channelAmplitude w hw K half r .unit) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (channelAmplitude_recentered w hw K half l e c))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ (channelAmplitude_recentered w hw K half r e c))))
      (determinant_shift _ _ _ _ c)
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ h))

def referenceBudget (l r : Leaf tree) : Q' :=
  twoProbeEnergy w hw K half l r .unit + twoProbeEnergy w hw K half l r .unit

theorem referenceBudget_nonnegative (l r : Leaf tree) : (0 : Q') ≤ referenceBudget w hw K half l r :=
  Q'.zero_le_add _ _ (twoProbeEnergy_nonnegative w hw K half l r .unit)
    (twoProbeEnergy_nonnegative w hw K half l r .unit)

theorem twoProbeMinor_bound (l r : Leaf tree) (e : PlaquetteExpression half) :
    twoProbeMinor w hw K half l r e ≤ rawForm w K e e * referenceBudget w hw K half l r := by
  have h := Q'.le_trans' _ _ _ (minor_le_energy_product l.weight r.weight
    (channelAmplitude w hw K half l e) (channelAmplitude w hw K half r e)
    (channelAmplitude w hw K half l .unit) (channelAmplitude w hw K half r .unit))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (twoProbeEnergy_bound w hw K half l r e)
      (twoProbeEnergy_nonnegative w hw K half l r .unit))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (RingNormaliser.q_add_mul _ _ _) (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))))

theorem denominator_pos (l r : Leaf tree) : (0 : Q') < referenceBudget w hw K half l r + 1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (referenceBudget_nonnegative w hw K half l r))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

def twoProbeFloor (l r : Leaf tree) (e : PlaquetteExpression half) : Q' :=
  Q'.divPos (twoProbeMinor w hw K half l r e) (referenceBudget w hw K half l r + 1)
    (denominator_pos w hw K half l r)

theorem twoProbeFloor_bound (l r : Leaf tree) (e : PlaquetteExpression half) (c : Q') :
    twoProbeFloor w hw K half l r e ≤ rawForm w K (recentered half e c) (recentered half e c) :=
  Q'.divPos_le_of_le_mul _ _ _ (Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (twoProbeMinor_recentered w hw K half l r e c))
    (Q'.le_trans' _ _ _ (twoProbeMinor_bound w hw K half l r (recentered half e c))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
        (rawForm_nonnegative w hw K _))))

def scalarPlaquetteMinor (hK : 1 ≤ K) : Q' :=
  twoProbeMinor w hw K 0 (interfaceUnit hw K 0).leaf (scalarLoopChannel hw K hK).leaf probe

def scalarPlaquetteFloor (hK : 1 ≤ K) : Q' :=
  twoProbeFloor w hw K 0 (interfaceUnit hw K 0).leaf (scalarLoopChannel hw K hK).leaf probe

/-- Fully specified observable and channel paths: only w,K,c remain. -/
theorem scalarPlaquetteFloor_bound (hK : 1 ≤ K) (c : Q') :
    scalarPlaquetteFloor w hw K hK ≤ rawForm w K (recentered 0 probe c) (recentered 0 probe c) :=
  twoProbeFloor_bound w hw K 0 _ _ probe c

/-- An exact finite test; no successful w,K instance is supplied here. -/
theorem scalarPlaquetteFloor_positive (hK : 1 ≤ K) (h : (0 : Q') < scalarPlaquetteMinor w hw K hK) :
    (0 : Q') < scalarPlaquetteFloor w hw K hK := Q'.divPos_pos _ _ _ h

end YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.leaf_amplitude_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.twoProbeEnergy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.twoProbeMinor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.twoProbeEnergy_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.twoProbeEnergy_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.twoProbeMinor_recentered
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.referenceBudget
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.referenceBudget_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.twoProbeMinor_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.denominator_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.twoProbeFloor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.twoProbeFloor_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.scalarPlaquetteMinor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.scalarPlaquetteFloor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.scalarPlaquetteFloor_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor.scalarPlaquetteFloor_positive
