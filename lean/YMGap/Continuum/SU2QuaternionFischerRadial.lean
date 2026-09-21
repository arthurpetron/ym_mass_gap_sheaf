/-
# Constructive radial antiderivatives for head-harmonic polynomials

The four-dimensional Laplacian of r^(2(k+1))*h is
4(k+1)(d+k+2)*r^(2k)*h for head-harmonic homogeneous h of degree d.
The denominator is an explicit positive natural number. This supplies the
finite radial lift needed to decompose an arbitrary homogeneous polynomial;
no harmonicity of the original weighted source is assumed.
-/

import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
import YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport

namespace YMGap.Continuum.SU2QuaternionFischerRadial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport

local infix:50 " ≈ " => Q'.eqv

/-- Raw coefficient equality retains exponent-list padding. -/
def HeadPadded (p : RatPoly) : Prop := ∀ t, t ∈ p → 4 ≤ t.1.length

private theorem zeroPrefix_monoMul : ∀ (n : Nat) (m : List Nat), n ≤ m.length →
    monoMul (List.replicate n 0) m = m
  | 0, _, _ => rfl
  | n+1, [], h => by simp at h
  | n+1, a::m, h => by
      simp only [List.replicate_succ, monoMul, Nat.zero_add]
      rw [zeroPrefix_monoMul n m (by simpa using h)]

private theorem zeroPrefix_mul (n : Nat) (c : Q') (p : RatPoly)
    (hp : ∀ t, t ∈ p → n ≤ t.1.length) :
    polyMul [(List.replicate n 0, c)] p = polySmul c p := by
  simp only [polyMul, List.flatMap_cons, List.flatMap_nil, List.append_nil, polySmul]
  apply List.map_congr_left
  intro t ht
  rw [zeroPrefix_monoMul n t.1 (hp t ht)]

private theorem laplacian_radius_constants : RatPolyCoeffEqv
    (headLaplacian (quaternionRadiusPolynomial 0))
    (polyFour [([0],2)] [([0,0],2)] [([0,0,0],2)] [([0,0,0,0],2)]) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

theorem laplacian_radius_mul_first {p : RatPoly} (hp : HeadPadded p) :
    RatPolyCoeffEqv (polyMul (headLaplacian (quaternionRadiusPolynomial 0)) p)
      (polySmul 8 p) := by
  apply (laplacian_radius_constants.mul_right p).trans
  unfold polyFour
  rw [polyMul_add_left_exact, polyMul_add_left_exact, polyMul_add_left_exact]
  have h (n : Nat) (hn : n ≤ 4) :
      polyMul [(List.replicate n 0, 2)] p = polySmul 2 p :=
    zeroPrefix_mul n 2 p (fun t ht => Nat.le_trans hn (hp t ht))
  have h1 : polyMul [([0],2)] p = polySmul 2 p := by simpa using h 1 (by decide)
  have h2 : polyMul [([0,0],2)] p = polySmul 2 p := by simpa using h 2 (by decide)
  have h3 : polyMul [([0,0,0],2)] p = polySmul 2 p := by simpa using h 3 (by decide)
  have h4 : polyMul [([0,0,0,0],2)] p = polySmul 2 p := by simpa using h 4 (by decide)
  rw [h1, h2, h3, h4]
  exact ((RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.refl _).add
    (RatPolyCoeffEqv.add_smul_same 2 2 p))).trans
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_smul_same 2 (2+2) p)).trans
        ((RatPolyCoeffEqv.add_smul_same 2 (2+(2+2)) p).trans
          (RatPolyCoeffEqv.smul_coefficient (by decide) p)))

/-- Euler and the full product rule, without a harmonicity premise. -/
theorem laplacian_radius_mul {d : Nat} {p : RatPoly}
    (hd : HasQuaternionBlockDegree 0 d p) (hp : HeadPadded p) :
    RatPolyCoeffEqv (headLaplacian (polyMul (quaternionRadiusPolynomial 0) p))
      (polyAdd (polySmul (Q'.ofNat (4*(d+2))) p)
        (polyMul (quaternionRadiusPolynomial 0) (headLaplacian p))) := by
  have hfirst := laplacian_radius_mul_first hp
  have hcross := ((headGradientDot_headRadius_left p).smul 2).trans
    ((twice_twice_smul (headEuler p)).trans
      (((headEuler_of_blockDegree d p hd).smul 4).trans
        (RatPolyCoeffEqv.smul_assoc 4 (Q'.ofNat d) p)))
  have hscale : (8 : Q') + 4 * Q'.ofNat d ≈ Q'.ofNat (4*(d+2)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (four_mul_ofNat_add_two_eqv d))
      (SU3CharFactor.ofNat_mul_eqv 4 (d+2))
  exact (headLaplacian_mul _ p).trans
    ((hfirst.add (hcross.add (RatPolyCoeffEqv.refl _))).trans
      ((RatPolyCoeffEqv.add_assoc _ _ _).symm.trans
        (((RatPolyCoeffEqv.add_smul_same 8 (4*Q'.ofNat d) p).trans
          (RatPolyCoeffEqv.smul_coefficient hscale p)).add (RatPolyCoeffEqv.refl _))))

theorem radiusIter_degree {d : Nat} {p : RatPoly}
    (hd : HasQuaternionBlockDegree 0 d p) : ∀ k,
    HasQuaternionBlockDegree 0 (d+2*k) (quaternionRadiusIter 0 k p)
  | 0 => by simpa using hd
  | k+1 => by
      have hR : HasQuaternionBlockDegree 0 2 (quaternionRadiusPolynomial 0) :=
        hasQuaternionBlockDegree_radius 0 0
      exact ((radiusIter_degree hd k).mul hR).relabel (by omega)

theorem radiusIter_supported {blocks : Nat} (hb : 0 < blocks)
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) : ∀ k,
    SupportedQuaternionBlocks blocks (quaternionRadiusIter 0 k p)
  | 0 => hp
  | k+1 => supported_polyMul (radiusIter_supported hb hp k)
      (quaternionRadiusPolynomial_supported blocks 0 hb)

private theorem monoMul_length_ge_left : ∀ a b : List Nat,
    a.length ≤ (monoMul a b).length
  | [], _ => Nat.zero_le _
  | _::_, [] => Nat.le_refl _
  | _::a, _::b => Nat.succ_le_succ (monoMul_length_ge_left a b)

theorem HeadPadded.mul_right {p : RatPoly} (hp : HeadPadded p) (q : RatPoly) :
    HeadPadded (polyMul p q) := by
  intro t ht
  obtain ⟨a, ha, b, _, rfl⟩ := mem_polyMul ht
  exact Nat.le_trans (hp a ha) (monoMul_length_ge_left _ _)

theorem radiusIter_padded {p : RatPoly} (hp : HeadPadded p) : ∀ k,
    HeadPadded (quaternionRadiusIter 0 k p)
  | 0 => hp
  | k+1 => (radiusIter_padded hp k).mul_right _

theorem HeadPadded.add {p q : RatPoly} (hp : HeadPadded p) (hq : HeadPadded q) :
    HeadPadded (polyAdd p q) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · exact hq t ht

theorem HeadPadded.smul {p : RatPoly} (hp : HeadPadded p) (c : Q') :
    HeadPadded (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem lowerExponentAt_length (i : Nat) : ∀ m : List Nat,
    (lowerExponentAt i m).length = m.length
  | [] => by cases i <;> rfl
  | _::m => by
      cases i with
      | zero => rfl
      | succ i => exact congrArg Nat.succ (lowerExponentAt_length i m)

theorem HeadPadded.activeDerivative {p : RatPoly} (hp : HeadPadded p) (i : Nat) :
    HeadPadded (activeDerivative i p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  rw [lowerExponentAt_length]
  exact hp s (List.mem_filter.mp hs).1

theorem HeadPadded.activeLaplacian {p : RatPoly} (hp : HeadPadded p) :
    HeadPadded (activeLaplacian p) :=
  ((hp.activeDerivative 0).activeDerivative 0).add
    (((hp.activeDerivative 1).activeDerivative 1).add
      (((hp.activeDerivative 2).activeDerivative 2).add
        ((hp.activeDerivative 3).activeDerivative 3)))

/-- This is the actual coefficient, not an opaque integration constant. -/
def radialFactor (d k : Nat) : Nat := 4*(k+1)*(d+k+2)

theorem radialFactor_positive (d k : Nat) : 0 < radialFactor d k :=
  Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)

theorem radialFactor_step (d k : Nat) :
    4*(d+2*(k+1)+2) + radialFactor d k = radialFactor d (k+1) := by
  simp only [radialFactor, Nat.mul_add, Nat.add_mul]
  omega

/-- Integrating one radial level is finite and has a nonzero denominator. -/
theorem laplacian_radiusIter {d : Nat} {p : RatPoly}
    (hd : HasQuaternionBlockDegree 0 d p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) (hp : HeadPadded p) : ∀ k,
    RatPolyCoeffEqv (headLaplacian (quaternionRadiusIter 0 (k+1) p))
      (polySmul (Q'.ofNat (radialFactor d k)) (quaternionRadiusIter 0 k p))
  | 0 => by
      have h := ((RatPolyCoeffEqv.mul_comm p (quaternionRadiusPolynomial 0)).headLaplacian).trans
        (laplacian_radius_mul hd hp)
      exact h.trans (((RatPolyCoeffEqv.refl _).add
        ((hh.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _))).trans
          (RatPolyCoeffEqv.add_zero _))
  | k+1 => by
      let q := quaternionRadiusIter 0 (k+1) p
      have hthird : RatPolyCoeffEqv
          (polyMul (quaternionRadiusPolynomial 0) (headLaplacian q))
          (polySmul (Q'.ofNat (radialFactor d k)) q) :=
        ((laplacian_radiusIter hd hh hp k).mul_left _).trans
          ((RatPolyCoeffEqv.polyMul_smul_right _ _ _).trans
            ((RatPolyCoeffEqv.mul_comm _ _).smul _))
      have hscale : Q'.ofNat (4*(d+2*(k+1)+2)) + Q'.ofNat (radialFactor d k) ≈
          Q'.ofNat (radialFactor d (k+1)) := by
        rw [← radialFactor_step d k]
        exact Q'.eqv_symm (Q'.ofNat_add_eqv _ _)
      exact ((RatPolyCoeffEqv.mul_comm q (quaternionRadiusPolynomial 0)).headLaplacian).trans
        ((laplacian_radius_mul (radiusIter_degree hd (k+1)) (radiusIter_padded hp (k+1))).trans
          (((RatPolyCoeffEqv.refl _).add hthird).trans
            ((RatPolyCoeffEqv.add_smul_same _ _ q).trans
              (RatPolyCoeffEqv.smul_coefficient hscale q))))

theorem activeDerivative_supported {blocks i : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (activeDerivative i p) :=
  ratDerivative_supported (fun t ht => hp t (List.mem_filter.mp ht).1)

theorem activeLaplacian_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (activeLaplacian p) := by
  have hi (i : Nat) : SupportedQuaternionBlocks blocks (activeDerivative i (activeDerivative i p)) :=
    activeDerivative_supported (activeDerivative_supported hp)
  exact polyAdd_supported (hi 0) (polyAdd_supported (hi 1) (polyAdd_supported (hi 2) (hi 3)))

theorem harmonic_low_degree {d : Nat} {p : RatPoly}
    (hd : HasQuaternionBlockDegree 0 d p) (hsmall : d < 2) :
    RatPolyCoeffEqv (headLaplacian p) polyZero := by
  have hi (i : Nat) (hlt : i < 4) : activeDerivative i (activeDerivative i p) = [] :=
    activeDerivative_zero hlt _ ((activeDerivative_degree hlt hd).relabel (by omega))
  apply (activeLaplacian_coeff p).symm.trans
  rw [activeLaplacian, hi 0 (by decide), hi 1 (by decide), hi 2 (by decide), hi 3 (by decide)]
  exact RatPolyCoeffEqv.refl _

end YMGap.Continuum.SU2QuaternionFischerRadial

#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.laplacian_radius_mul_first
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.laplacian_radius_mul
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.radiusIter_degree
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.radiusIter_supported
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.HeadPadded.mul_right
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.radiusIter_padded
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.HeadPadded.add
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.HeadPadded.smul
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.HeadPadded.activeDerivative
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.HeadPadded.activeLaplacian
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.radialFactor_positive
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.radialFactor_step
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.laplacian_radiusIter
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.activeDerivative_supported
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.activeLaplacian_supported
#print axioms YMGap.Continuum.SU2QuaternionFischerRadial.harmonic_low_degree
