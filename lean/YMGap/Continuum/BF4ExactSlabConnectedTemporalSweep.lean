/-
# A common temporal sweep preserves all four connected moments

The probes and action are finite original face factors, with arbitrary
signed coefficients and repeated faces allowed. The same sweep is applied
to the partition, both means and mixed moment. No independence of the
full action is assumed. This is an exact change of variables, not a bound.
-/

import YMGap.Continuum.BF4ExactSlabTemporalSweep
import YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance
import YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation

namespace YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

theorem connected_coeff_congr (blocks : Nat) {p q r p' q' r' : RatPoly}
    (hp : RatPolyCoeffEqv p p') (hq : RatPolyCoeffEqv q q') (hr : RatPolyCoeffEqv r r') :
    connectedNumerator blocks p q r ≈ connectedNumerator blocks p' q' r' :=
  Q'.add_eqv_congr' (qmul (haar_of_coeff hr) (haar_of_coeff (hp.mul (hq.mul hr))))
    (Q'.neg_eqv_congr _ _ (qmul (haar_of_coeff (hp.mul hr)) (haar_of_coeff (hq.mul hr))))

/-- Pin the existing original numerator, including its partition and association order. -/
theorem original_connected_pin (w : Q') (K extent : Nat) (ids : List Nat) (p q : RatPoly) :
    BF4ExactSlabDisconnectedHaarCancellation.connectedNumerator w K extent ids p q ≈
      connectedNumerator (boundaryCompleteSlabLinks extent).length p q
        (polynomialProduct (BF4ExactSlabAllExtentObservableHaarForm.faceHeatPolynomial w K extent) ids) := by
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)))
  · exact Q'.eqv_refl _

theorem swept_append (extent cut : Nat) (xs ys : List FaceFactor) :
    RatPolyCoeffEqv (sweptProduct extent cut (xs++ys))
      (polyMul (sweptProduct extent cut xs) (sweptProduct extent cut ys)) :=
  polynomialProduct_append _ xs ys

private theorem physical_append {extent : Nat} {xs ys : List FaceFactor}
    (hx : ∀ f, f ∈ xs → f.1 ∈ boundaryCompleteSlabPlaquettes extent)
    (hy : ∀ f, f ∈ ys → f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    ∀ f, f ∈ xs++ys → f.1 ∈ boundaryCompleteSlabPlaquettes extent :=
  fun f hf => (List.mem_append.mp hf).elim (hx f) (hy f)

theorem sweep_product_haar (extent stop : Nat) (xs ys : List FaceFactor)
    (hx : ∀ f, f ∈ xs → f.1 ∈ boundaryCompleteSlabPlaquettes extent)
    (hy : ∀ f, f ∈ ys → f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (sweptProduct extent 0 xs) (sweptProduct extent 0 ys)) ≈
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (sweptProduct extent stop xs) (sweptProduct extent stop ys)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (swept_append extent 0 xs ys)))
    (Q'.eqv_trans _ _ _ (sweep_haar extent stop (xs++ys) (physical_append hx hy))
      (haar_of_coeff (swept_append extent stop xs ys)))

theorem sweep_connected (extent stop : Nat) (ps qs rs : List FaceFactor)
    (hp : ∀ f, f ∈ ps → f.1 ∈ boundaryCompleteSlabPlaquettes extent)
    (hq : ∀ f, f ∈ qs → f.1 ∈ boundaryCompleteSlabPlaquettes extent)
    (hr : ∀ f, f ∈ rs → f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    connectedNumerator (boundaryCompleteSlabLinks extent).length
      (sweptProduct extent 0 ps) (sweptProduct extent 0 qs) (sweptProduct extent 0 rs) ≈
    connectedNumerator (boundaryCompleteSlabLinks extent).length
      (sweptProduct extent stop ps) (sweptProduct extent stop qs) (sweptProduct extent stop rs) := by
  have hm := sweep_product_haar extent stop ps (qs++rs) hp (physical_append hq hr)
  have hm' := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff ((swept_append extent 0 qs rs).mul_left (sweptProduct extent 0 ps))))
    (Q'.eqv_trans _ _ _ hm
      (haar_of_coeff ((swept_append extent stop qs rs).mul_left (sweptProduct extent stop ps))))
  exact Q'.add_eqv_congr' (qmul (sweep_haar extent stop rs hr) hm')
    (Q'.neg_eqv_congr _ _ (qmul (sweep_product_haar extent stop ps rs hp hr)
      (sweep_product_haar extent stop qs rs hq hr)))

end YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep

#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep.connected_coeff_congr
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep.original_connected_pin
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep.swept_append
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep.sweep_product_haar
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep.sweep_connected
