/-
# The original heat interface in literal path-pair Gram coordinates

Each original heat factor is replaced by its actual path-pair Gram sum,
with the same coeffW weights. Arbitrary-insertion Haar equivalence composes
these replacements across the 24 crossing faces even though they share
links. The final consumer is the ORIGINAL signed reflected quadratic.

This is an identity, not positivity. The path pairs still contain shared
time links; their integration into a global reflected square remains open.
-/

import YMGap.Continuum.BF4ExactSlabPlaquettePathGram
import YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm

namespace YMGap.Continuum.BF4ExactSlabInterfacePathGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem sum_haar_congr {A : Type} (blocks : Nat) (f g : A → RatPoly) :
    ∀ xs : List A, (∀ a, a ∈ xs → QuaternionHaarCarrierEqv blocks (f a) (g a)) →
      QuaternionHaarCarrierEqv blocks (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => QuaternionHaarCarrierEqv.refl blocks _
  | a :: xs, h => QuaternionHaarCarrierEqv.add (h a List.mem_cons_self)
      (sum_haar_congr blocks f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- The ORIGINAL heat coefficients multiplying Gram kernels of the literal
two paths, not independent replacements for shared link variables. -/
def faceHeatPathGram (w : Q') (K id : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffW w spin)
    (slabFacePathGram 1 (slabPlaquetteAt 1 id) spin).1) (List.range (K + 1))

/-- Every original fixed-face heat factor has its path-pair Gram expression
under every spectator insertion, for every rational w and cutoff K. -/
theorem faceHeatPolynomial_haar_pathGram (w : Q') (K : Nat) {id : Nat}
    (hid : id ∈ centralFixedFaceIds 0) :
    QuaternionHaarCarrierEqv 116 (faceHeatPolynomial w K id) (faceHeatPathGram w K id) := by
  refine QuaternionHaarCarrierEqv.trans
    (RatPolyCoeffEqv.haarCarrier (faceHeatPolynomial_eq_heat_sum w K id)) ?_
  apply sum_haar_congr
  intro spin _
  apply QuaternionHaarCarrierEqv.smul
  have h := crossing_face_character_haar_pathGram hid spin
  change QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks 1).length _ _ at h
  rw [correctedSlabLinks_extent_one_length] at h
  exact h

/-- The same 24-face interface, with all shared link coordinates retained. -/
def interfacePathGram (w : Q') (K : Nat) : RatPoly :=
  (centralFixedFaceIds 0).foldr (fun id p => polyMul (faceHeatPathGram w K id) p) polyOne

/-- Arbitrary-insertion equivalence permits simultaneous replacement of
overlapping face factors. No independence or gluing positivity is assumed. -/
theorem interfaceHeatProduct_haar_pathGram (w : Q') (K : Nat) :
    QuaternionHaarCarrierEqv 116 (interfaceHeatProduct w K) (interfacePathGram w K) := by
  have hfold : ∀ ids : List Nat, (∀ id, id ∈ ids → id ∈ centralFixedFaceIds 0) →
      QuaternionHaarCarrierEqv 116
        (ids.foldr (fun id p => polyMul (faceHeatPolynomial w K id) p) polyOne)
        (ids.foldr (fun id p => polyMul (faceHeatPathGram w K id) p) polyOne) := by
    intro ids
    induction ids with
    | nil => intro _; exact QuaternionHaarCarrierEqv.refl 116 _
    | cons id rest ih =>
      intro hids
      exact QuaternionHaarCarrierEqv.mul
        (faceHeatPolynomial_haar_pathGram w K (hids id List.mem_cons_self))
        (ih (fun j hj => hids j (List.mem_cons_of_mem id hj)))
  exact hfold (centralFixedFaceIds 0) (fun _ h => h)

/-- The ORIGINAL signed bilinear form with its actual reflected observable
and literal heat-weighted path channels on the same 116-link Haar carrier. -/
theorem exact_bilinear_eq_pathGramHaar (w : Q') (K : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K 0) left right (exactCorrectedSlabReflectedKernel w K 0) ≈
      quaternionHaar 116 (polyMul (lowerObservable w K left)
        (polyMul (interfacePathGram w K) (reflectCorrectedSlabPolynomial 1 (lowerObservable w K right)))) :=
  Q'.eqv_trans _ _ _ (exact_bilinear_eq_reflectedHaar w K left right)
    ((QuaternionHaarCarrierEqv.mul_right (interfaceHeatProduct_haar_pathGram w K)
      (reflectCorrectedSlabPolynomial 1 (lowerObservable w K right))) (lowerObservable w K left))

/-- Same-law quadratic identity at every cutoff. A global reflected-square
decomposition is still needed before this can imply nonnegativity. -/
theorem exact_quadratic_eq_pathGramHaar (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    exactSlabAllCutoffQuadratic w K c ≈
      quaternionHaar 116 (polyMul (lowerObservable w K c)
        (polyMul (interfacePathGram w K) (reflectCorrectedSlabPolynomial 1 (lowerObservable w K c)))) :=
  exact_bilinear_eq_pathGramHaar w K c c

end YMGap.Continuum.BF4ExactSlabInterfacePathGram

#print axioms YMGap.Continuum.BF4ExactSlabInterfacePathGram.faceHeatPathGram
#print axioms YMGap.Continuum.BF4ExactSlabInterfacePathGram.faceHeatPolynomial_haar_pathGram
#print axioms YMGap.Continuum.BF4ExactSlabInterfacePathGram.interfacePathGram
#print axioms YMGap.Continuum.BF4ExactSlabInterfacePathGram.interfaceHeatProduct_haar_pathGram
#print axioms YMGap.Continuum.BF4ExactSlabInterfacePathGram.exact_bilinear_eq_pathGramHaar
#print axioms YMGap.Continuum.BF4ExactSlabInterfacePathGram.exact_quadratic_eq_pathGramHaar
