/-
# Finite two-nome face schedules

This is only the literal finite bookkeeping for changing selected face
factors.  It introduces no analytic estimate or path limit.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap

namespace YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap

def nomeAt (u v : Q') (chosen : List Nat) (id : Nat) : Q' :=
  if id ∈ chosen then v else u

def density (u v : Q') (K extent : Nat) (chosen ambient : List Nat) : RatPoly :=
  polynomialProduct (fun j => faceHeatPolynomial (nomeAt u v chosen j) K extent j) ambient

theorem density_add_pin (u v : Q') (K extent : Nat) (chosen ambient : List Nat) (id : Nat)
    (hn : ambient.Nodup) (hi : id ∈ ambient) :
    RatPolyCoeffEqv (density u v K extent (id :: chosen) ambient)
      (polyMul (density u v K extent chosen (eraseIndex id ambient))
        (faceHeatPolynomial v K extent id)) := by
  let f := fun j => faceHeatPolynomial (nomeAt u v (id :: chosen) j) K extent j
  have hrest : polynomialProduct f (eraseIndex id ambient) =
      polynomialProduct (fun j => faceHeatPolynomial (nomeAt u v chosen j) K extent j)
        (eraseIndex id ambient) := by
    apply polynomialProduct_congr
    intro j hj
    have hne : j ≠ id := by
      intro he
      subst j
      exact (not_mem_erase id hn) hj
    simp [f, nomeAt, hne]
  have hfac : polynomialProduct f (id :: eraseIndex id ambient) =
      polyMul (faceHeatPolynomial v K extent id)
        (polynomialProduct f (eraseIndex id ambient)) := by
    simp only [polynomialProduct, f]
    simp [nomeAt]
  have hfacEqv : RatPolyCoeffEqv (polynomialProduct f (id :: eraseIndex id ambient))
      (polyMul (faceHeatPolynomial v K extent id)
        (polynomialProduct f (eraseIndex id ambient))) := by
    rw [hfac]
    exact RatPolyCoeffEqv.refl _
  have hrestEqv : RatPolyCoeffEqv
      (polynomialProduct f (eraseIndex id ambient))
      (polynomialProduct (fun j => faceHeatPolynomial (nomeAt u v chosen j) K extent j)
        (eraseIndex id ambient)) := by
    rw [hrest]
    exact RatPolyCoeffEqv.refl _
  have hperm := polynomialProduct_perm f (select_perm id hi)
  unfold density
  exact hperm.trans (hfacEqv.trans
    (hrestEqv.mul_left (faceHeatPolynomial v K extent id)))
    |>.trans (RatPolyCoeffEqv.mul_comm _ _)

theorem density_old_pin (u v : Q') (K extent : Nat) (chosen ambient : List Nat) (id : Nat)
    (hi : id ∈ ambient) (hnot : id ∉ chosen) :
    RatPolyCoeffEqv (density u v K extent chosen ambient)
      (polyMul (density u v K extent chosen (eraseIndex id ambient))
        (faceHeatPolynomial u K extent id)) := by
  let f := fun j => faceHeatPolynomial (nomeAt u v chosen j) K extent j
  have hfac : polynomialProduct f (id :: eraseIndex id ambient) =
      polyMul (faceHeatPolynomial u K extent id)
        (polynomialProduct f (eraseIndex id ambient)) := by
    have hid : nomeAt u v chosen id = u := by simp [nomeAt, hnot]
    change polyMul (faceHeatPolynomial (nomeAt u v chosen id) K extent id)
      (polynomialProduct f (eraseIndex id ambient)) = _
    rw [hid]
  have hfacEqv : RatPolyCoeffEqv (polynomialProduct f (id :: eraseIndex id ambient))
      (polyMul (faceHeatPolynomial u K extent id)
        (polynomialProduct f (eraseIndex id ambient))) := by
    rw [hfac]
    exact RatPolyCoeffEqv.refl _
  have hperm := polynomialProduct_perm f (select_perm id hi)
  unfold density
  exact hperm.trans hfacEqv
    |>.trans (RatPolyCoeffEqv.mul_comm _ _)

theorem nomeAt_nonnegative {u v : Q'} (hu0 : (0 : Q') ≤ u) (hv0 : (0 : Q') ≤ v)
    (chosen : List Nat) (id : Nat) : (0 : Q') ≤ nomeAt u v chosen id := by
  by_cases h : id ∈ chosen <;> simp [nomeAt, h, hv0, hu0]

theorem nomeAt_le {u v W : Q'} (huW : u ≤ W) (hvW : v ≤ W)
    (chosen : List Nat) (id : Nat) : nomeAt u v chosen id ≤ W := by
  by_cases h : id ∈ chosen <;> simp [nomeAt, h, hvW, huW]

theorem density_nil (u v : Q') (K extent : Nat) (ambient : List Nat) :
    RatPolyCoeffEqv (density u v K extent [] ambient)
      (polynomialProduct (fun j => faceHeatPolynomial u K extent j) ambient) := by
  have he : density u v K extent [] ambient =
      polynomialProduct (fun j => faceHeatPolynomial u K extent j) ambient := by
    unfold density
    apply polynomialProduct_congr
    intro id hid
    simp [nomeAt]
  rw [he]
  exact RatPolyCoeffEqv.refl _

theorem density_all (u v : Q') (K extent : Nat) (ambient : List Nat) :
    RatPolyCoeffEqv (density u v K extent ambient ambient)
      (polynomialProduct (fun j => faceHeatPolynomial v K extent j) ambient) := by
  have he : density u v K extent ambient ambient =
      polynomialProduct (fun j => faceHeatPolynomial v K extent j) ambient := by
    unfold density
    apply polynomialProduct_congr
    intro id hid
    simp [nomeAt, hid]
  rw [he]
  exact RatPolyCoeffEqv.refl _

end YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule

#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule.nomeAt
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule.density
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule.density_add_pin
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule.density_old_pin
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule.nomeAt_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule.nomeAt_le
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule.density_nil
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule.density_all
