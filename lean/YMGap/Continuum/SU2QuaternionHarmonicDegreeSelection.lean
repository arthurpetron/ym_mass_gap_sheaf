/-
# Exact high-degree harmonic annihilation with all tail coefficients retained

Gaussian integration by parts and the homogeneous Euler identity give
n E[P Q] = E[grad P . grad Q] when P is harmonic of degree n.
Applying the same identity to Q reduces its Laplacian by two degrees.
Induction proves E[P Q] = 0 whenever deg Q < n. The explicit radial
denominator then gives the SAME statement for the original partial Haar
integral. No limiting argument, spectral gap or independent-tail assumption
is used. This is a degree-selection ingredient for cutoff stabilization,
not yet stabilization of the full reflected slab kernel.
-/

import YMGap.Continuum.SU2QuaternionHeadDegreeDifferential

namespace YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini

private theorem add_cancel (a b : Q') : ((a + b) + -b).eqv a :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (-b))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv b))
      (Q'.eqv_of_eq (Q'.add_zero' a)))

private theorem natural_scale_zero {n d : Nat} (hd : d < n) (v : Q')
    (h : (Q'.ofNat n * v).eqv (Q'.ofNat d * v)) : v.eqv 0 := by
  have hpos : (0 : Q') < Q'.ofNat (n - d) := by
    cases he : n - d with
    | zero => omega
    | succ k => exact Q'.ofNat_succ_pos k
  apply Q'.mul_eqv_zero_of_pos hpos
  have hs : (Q'.ofNat (n - d) * v + Q'.ofNat d * v).eqv (Q'.ofNat n * v) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ v))
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.ofNat_add_eqv (n - d) d))
        (by rw [Nat.sub_add_cancel (Nat.le_of_lt hd)]; exact Q'.eqv_refl _)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (add_cancel _ _))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ hs h))
      (Q'.add_neg_self_eqv _))

/-- Distinct homogeneous degrees can be cancelled without choosing a
nonzero coefficient or using a field division on the polynomial carrier. -/
theorem smul_degrees_eq_zero {n d : Nat} (hd : d < n) {p : RatPoly}
    (h : RatPolyCoeffEqv (polySmul (Q'.ofNat n) p) (polySmul (Q'.ofNat d) p)) :
    RatPolyCoeffEqv p polyZero := by
  intro weight
  exact natural_scale_zero hd _ (Q'.eqv_trans _ _ _
    (Q'.eqv_symm (ratWeightedSum_smul weight _ p))
    (Q'.eqv_trans _ _ _ (h weight) (ratWeightedSum_smul weight _ p)))

/-- Euler/IBP specialized only by an explicitly zero Laplacian pairing. -/
theorem homogeneous_euler_pairing {n : Nat} {p : RatPoly} (q : RatPoly)
    (hp : HasQuaternionBlockDegree 0 n p)
    (hz : RatPolyCoeffEqv (partialGaussianHead (polyMul (headLaplacian p) q)) polyZero) :
    RatPolyCoeffEqv (polySmul (Q'.ofNat n) (partialGaussianHead (polyMul p q)))
      (partialGaussianHead (headGradientDot p q)) := by
  have he := partialGaussianHead_congr
    (((headEuler_of_blockDegree n p hp).mul_right q).trans
      (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
  have he' := he.trans (partialGaussianHead_smul _ _)
  have h := he'.symm.trans (partialGaussianHead_euler_product p q)
  rw [partialGaussianHead_add] at h
  exact h.trans ((hz.add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _))

/-- Exact polynomial-valued Gaussian annihilation by degree induction. -/
theorem partialGaussianHead_harmonic_lower_degree {n : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    ∀ d, d < n → ∀ q : RatPoly, HasQuaternionBlockDegree 0 d q →
      RatPolyCoeffEqv (partialGaussianHead (polyMul p q)) polyZero := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro hd q hq
    have hl : RatPolyCoeffEqv (partialGaussianHead (polyMul (headLaplacian p) q)) polyZero :=
      partialGaussianHead_congr ((hh.mul_right q).trans (RatPolyCoeffEqv.mul_zero_left q))
    have hr : RatPolyCoeffEqv (partialGaussianHead (polyMul (headLaplacian q) p)) polyZero := by
      have hactive : RatPolyCoeffEqv (partialGaussianHead (polyMul p (activeLaplacian q))) polyZero := by
        cases d with
        | zero =>
          rw [activeLaplacian_zero hq]
          exact partialGaussianHead_congr (RatPolyCoeffEqv.mul_zero_right p)
        | succ d => exact ih (d + 1 - 2) (by omega) (by omega) _ (activeLaplacian_degree hq)
      exact (partialGaussianHead_congr
        ((RatPolyCoeffEqv.mul_comm _ _).trans ((activeLaplacian_coeff q).symm.mul_left p))).trans hactive
    have hleft := homogeneous_euler_pairing q hp hl
    have hright := homogeneous_euler_pairing p hq hr
    have hswap := (partialGaussianHead_congr (RatPolyCoeffEqv.mul_comm p q)).smul (Q'.ofNat d)
    have hgrad := partialGaussianHead_congr (headGradientDot_comm q p)
    exact smul_degrees_eq_zero hd (hleft.trans ((hswap.trans (hright.trans hgrad)).symm))

/-- Transfer the annihilation to the original partial sphere moment,
using the existing explicit radial factor and exact odd parity. -/
theorem partialHaarHead_harmonic_lower_degree {n d : Nat} {p q : RatPoly}
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hq : HasQuaternionBlockDegree 0 d q) (hd : d < n) :
    RatPolyCoeffEqv (partialHaarHead (polyMul p q)) polyZero := by
  have hprod := hp.mul hq
  by_cases heven : (n + d) % 2 = 0
  · have hdeg : n + d = 2 * ((n + d) / 2) := by omega
    have hrad := partialHaarHead_mul_radial ((n + d) / 2) (polyMul p q) (hprod.relabel hdeg)
    have hz := partialGaussianHead_harmonic_lower_degree hp hh d hd q hq
    intro weight
    apply Q'.mul_eqv_zero_of_pos (radialDenominator_positive ((n + d) / 2))
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (ratWeightedSum_smul weight _ _))
      (Q'.eqv_trans _ _ _ (hrad weight) (hz weight))
  · apply partialHaarHead_eq_zero_of_odd
    intro term ht
    have hg := hprod term ht
    change headQuaternionDegree term.1 = n + d at hg
    rw [hg]
    omega

/-- An arbitrary polynomial, not necessarily homogeneous, is annihilated
when every one of its monomials has lower head degree than the harmonic. -/
theorem partialHaarHead_harmonic_degree_bound {n : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    ∀ q : RatPoly, (∀ term, term ∈ q → quaternionBlockDegree term.1 0 < n) →
      RatPolyCoeffEqv (partialHaarHead (polyMul p q)) polyZero
  | [], _ => partialHaarHead_congr (RatPolyCoeffEqv.mul_zero_right p)
  | t :: rest, hq => by
    have hs : HasQuaternionBlockDegree 0 (quaternionBlockDegree t.1 0) [t] := by
      intro term ht
      have he := List.mem_singleton.mp ht
      subst term
      rfl
    have hhead := partialHaarHead_harmonic_lower_degree hp hh hs (hq t List.mem_cons_self)
    have htail := partialHaarHead_harmonic_degree_bound hp hh rest
      (fun s hs => hq s (List.mem_cons_of_mem t hs))
    have hsplit := partialHaarHead_congr (RatPolyCoeffEqv.mul_add_right p [t] rest)
    have hadd : partialHaarHead (polyAdd (polyMul p [t]) (polyMul p rest)) =
        polyAdd (partialHaarHead (polyMul p [t])) (partialHaarHead (polyMul p rest)) := List.map_append
    rw [hadd] at hsplit
    exact hsplit.trans (hhead.add htail)

end YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection

#print axioms YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection.smul_degrees_eq_zero
#print axioms YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection.homogeneous_euler_pairing
#print axioms YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection.partialGaussianHead_harmonic_lower_degree
#print axioms YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection.partialHaarHead_harmonic_lower_degree
#print axioms YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection.partialHaarHead_harmonic_degree_bound
