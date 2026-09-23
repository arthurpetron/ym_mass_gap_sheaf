/-
# Conditional Haar averaging contracts original angular energy

Differentiate before averaging every distinct block, and use the actual
family-Haar square contraction. At an averaged block the derivative vanishes.
Thus every original block energy, and their finite sum, decreases with
coefficient one. No heat parameter, cutoff or replacement carrier is involved.
-/

import YMGap.Continuum.SU2QuaternionSelectedHaarDerivative
import YMGap.Continuum.SU2QuaternionHaarFamilyPythagoras
import YMGap.Continuum.SU2QuaternionAngularReindex
import YMGap.Continuum.SU2QuaternionHaarTailDerivative
import YMGap.Constructive.CornerBound

namespace YMGap.Continuum.SU2QuaternionHaarFamilyAngularContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (coordinateInQuaternionBlock)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyPythagoras
open YMGap.Continuum.SU2QuaternionSelectedHaarDerivative
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem project_smul (block : Nat) (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv (project block (polySmul c f)) (polySmul c (project block f)) := by
  have ht : RatPolyTermwiseEqv
      (project block (polySmul c f)) (polySmul c (project block f)) := by
    induction f with
    | nil => exact True.intro
    | cons t rest ih => exact ⟨rfl, Q'.mul_assoc_eqv _ _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem family_smul (ids : List Nat) (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv (familyProject ids (polySmul c f))
      (polySmul c (familyProject ids f)) := by
  induction ids generalizing f with
  | nil => exact .refl _
  | cons s ids ih =>
      exact (familyProject_congr ids (project_smul s c f)).trans (ih (project s f))

private theorem derivative_familyProject (ids : List Nat) (block component : Nat)
    (hc : component < 4) (hnot : block ∉ ids) (f : RatPoly) :
    RatPolyCoeffEqv (ratDerivative (4*block+component) (familyProject ids f))
      (familyProject ids (ratDerivative (4*block+component) f)) := by
  induction ids generalizing f with
  | nil => exact .refl _
  | cons s ids ih =>
      have hne : block ≠ s := fun he => hnot (he.symm ▸ List.mem_cons_self)
      exact (ih (fun ht => hnot (List.mem_cons_of_mem s ht)) (project s f)).trans
        (familyProject_congr ids (ratDerivative_project_of_ne hne hc f))

/-- A block angular derivative commutes with averaging distinct blocks,
at coefficient equality on the original coordinate positions. -/
theorem blockAngularDerivative_familyProject (ids : List Nat) (block i j : Nat)
    (hi : i < 4) (hj : j < 4) (hnot : block ∉ ids) (f : RatPoly) :
    RatPolyCoeffEqv (blockAngularDerivative block i j (familyProject ids f))
      (familyProject ids (blockAngularDerivative block i j f)) := by
  have outside (k : Nat) (hk : k < 4) (s : Nat) (hs : s ∈ ids) :
      ¬ coordinateInQuaternionBlock s (4*block+k) := by
    have hne : block ≠ s := fun he => hnot (he.symm ▸ hs)
    unfold coordinateInQuaternionBlock
    omega
  have independent (k : Nat) (hk : k < 4) (s : Nat) (hs : s ∈ ids) :
      QuaternionBlockIndependent s (polyVar (4*block+k)) :=
    quaternionBlockIndependent_polyVar_of_outside s _ (outside k hk s hs)
  have di := derivative_familyProject ids block i hi hnot f
  have dj := derivative_familyProject ids block j hj hnot f
  have pi := familyProject_mul_of_independent ids (polyVar (4*block+i))
    (ratDerivative (4*block+j) f) (independent i hi)
  have pj := familyProject_mul_of_independent ids (polyVar (4*block+j))
    (ratDerivative (4*block+i) f) (independent j hj)
  unfold blockAngularDerivative angularDerivative
  refine ((dj.mul_left _).add ((di.mul_left _).smul (-1))).trans ?_
  refine (pi.symm.add ((pj.symm.smul (-1)).trans (family_smul ids (-1) _).symm)).trans ?_
  rw [familyProject_add]
  exact .refl _

/-- Each original angular derivative square decreases under the actual
conditional Haar projection, including when its own block is averaged. -/
theorem familyProject_blockAngularDerivative_square_le
    (blocks : Nat) (ids : List Nat) (hids : ∀ s, s ∈ ids → s < blocks)
    (block i j : Nat) (hb : block < blocks) (hi : i < 4) (hj : j < 4)
    (f : RatPoly) (hf : SupportedQuaternionBlocks blocks f) :
    quaternionHaar blocks
        (polyMul (blockAngularDerivative block i j (familyProject ids f))
          (blockAngularDerivative block i j (familyProject ids f))) ≤
      quaternionHaar blocks
        (polyMul (blockAngularDerivative block i j f) (blockAngularDerivative block i j f)) := by
  have hs : SupportedQuaternionBlocks blocks (blockAngularDerivative block i j f) :=
    angularDerivative_supported_at (by omega) (by omega) hf
  by_cases hm : block ∈ ids
  · have hz := angularDerivative_blockIndependent_zero hi hj
      (familyProject_independent ids f block hm)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (hz.mul hz)))
      (Certificate.haar_nonnegative (.square _ hs))
  · have hd := blockAngularDerivative_familyProject ids block i j hi hj hm f
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (hd.mul hd)))
      (familyProject_square_le blocks ids hids _ hs)

private theorem haar_six_unweighted (blocks : Nat) (f : Nat → Nat → RatPoly) :
    quaternionHaar blocks (six f) ≈ sixValue (fun i j => quaternionHaar blocks (f i j)) := by
  unfold six sixValue
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
            (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
                (Q'.add_eqv_congr' (Q'.eqv_refl _)
                  (quaternionHaar_append blocks _ _))))))))

/-- Coefficient-one contraction for each original block angular energy. -/
theorem familyProject_blockAngularSquare_le
    (blocks : Nat) (ids : List Nat) (hids : ∀ s, s ∈ ids → s < blocks)
    (block : Nat) (hb : block < blocks) (f : RatPoly)
    (hf : SupportedQuaternionBlocks blocks f) :
    quaternionHaar blocks (blockAngularSquare block (familyProject ids f)) ≤
      quaternionHaar blocks (blockAngularSquare block f) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_six_unweighted blocks _))
    (Q'.le_trans' _ _ _
      (sixValue_mono _ _ (fun i j hi hj =>
        familyProject_blockAngularDerivative_square_le blocks ids hids block i j hb hi hj f hf))
      (Q'.ge_of_eqv (haar_six_unweighted blocks _)))

/-- The complete original angular sum decreases with no block-count loss. -/
theorem familyProject_angularSum_le (blocks : Nat) (ids : List Nat)
    (hids : ∀ s, s ∈ ids → s < blocks) (f : RatPoly)
    (hf : SupportedQuaternionBlocks blocks f) :
    finSum (fun i => quaternionHaar blocks
      (blockAngularSquare i (familyProject ids f))) blocks ≤
      finSum (fun i => quaternionHaar blocks (blockAngularSquare i f)) blocks :=
  finSum_le_lt _ _ blocks (fun i hi => familyProject_blockAngularSquare_le blocks ids hids i hi f hf)

#print axioms blockAngularDerivative_familyProject
#print axioms familyProject_blockAngularDerivative_square_le
#print axioms familyProject_blockAngularSquare_le
#print axioms familyProject_angularSum_le

end YMGap.Continuum.SU2QuaternionHaarFamilyAngularContraction
