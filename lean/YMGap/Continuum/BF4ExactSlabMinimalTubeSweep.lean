/-
# The original minimal tube moment under the common temporal gauge sweep

The same fourteen original face characters are swept together. The two
spatial endpoints remain unchanged and the twelve sides become the
already-pinned literal relative characters on one full slab carrier.
No Haar value or leading-enumeration multiplicity is assumed.
-/

import YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin
import YMGap.Continuum.BF4ExactSlabTubeCarrierContraction

namespace YMGap.Continuum.BF4ExactSlabMinimalTubeSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep
open YMGap.Continuum.BF4ExactSlabTubeCarrierWords
open YMGap.Continuum.BF4ExactSlabTubeCarrierContraction
open YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "N" margin => List.length (boundaryCompleteSlabLinks (responseExtent margin))

theorem singleton_character_product (chars : Z4Plaq → Nat → RatPoly) : ∀ faces : List Z4Plaq,
    RatPolyCoeffEqv (product chars (faces.map (fun f => (f,[(1,1)]))))
      (polynomialProduct (fun f => chars f 1) faces)
  | [] => RatPolyCoeffEqv.refl polyOne
  | f::fs => by
    have hh : RatPolyCoeffEqv (factor chars (f,[(1,1)])) (chars f 1) :=
      (RatPolyCoeffEqv.add_zero _).trans (RatPolyCoeffEqv.one_smul _)
    exact hh.mul (singleton_character_product chars fs)

theorem product_as_factors {A : Type} (f : A → RatPoly) : ∀ xs : List A,
    polynomialProduct f xs = factorProduct (xs.map f)
  | [] => rfl
  | x::xs => congrArg (polyMul (f x)) (product_as_factors f xs)

theorem swept_tube_product (margin : Nat) :
    polynomialProduct (fun f => sweptCharacter (responseExtent margin) (margin+3) f 1) (tubeFaceList margin) =
      factorProduct (literalFactors margin ++ [literalSlice margin ⟨3,by decide⟩]) := by
  let F := fun f => sweptCharacter (responseExtent margin) (margin+3) f 1
  have h0 : F (sliceFace margin 0) = literalSlice margin ⟨0,by decide⟩ :=
    if_neg (slice_not_swept margin 0 (margin+3))
  have h3 : F (sliceFace margin 3) = literalSlice margin ⟨3,by decide⟩ :=
    if_neg (slice_not_swept margin 3 (margin+3))
  have hm : (tubeFaceList margin).map F = literalFactors margin ++ [literalSlice margin ⟨3,by decide⟩] := by
    rw [tubeFaceList,List.map_cons,List.map_append,List.map_cons,List.map_nil,h0,h3,
      ← side_faces_pin margin,List.map_map]
    rfl
  rw [product_as_factors]
  exact congrArg factorProduct hm

theorem original_tube_sweep (margin : Nat) : bareTubeMoment margin ≈
    quaternionHaar (N margin) (factorProduct (literalFactors margin ++ [literalSlice margin ⟨3,by decide⟩])) := by
  let fs : List FaceFactor := (tubeFaceList margin).map (fun f => (f,[(1,1)]))
  have hp : ∀ f, f ∈ fs → f.1 ∈ boundaryCompleteSlabPlaquettes (responseExtent margin) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    exact tubeFaceList_physical margin g hg
  have h0 : RatPolyCoeffEqv (sweptProduct (responseExtent margin) 0 fs) (bareTubePolynomial margin) := by
    rw [swept_zero]
    exact singleton_character_product _ _
  have h3 := singleton_character_product
    (sweptCharacter (responseExtent margin) (margin+3)) (tubeFaceList margin)
  rw [swept_tube_product] at h3
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff h0))
    (Q'.eqv_trans _ _ _ (sweep_haar (responseExtent margin) (margin+3) fs hp) (haar_of_coeff h3))

end YMGap.Continuum.BF4ExactSlabMinimalTubeSweep

#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeSweep.singleton_character_product
#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeSweep.product_as_factors
#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeSweep.swept_tube_product
#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeSweep.original_tube_sweep
