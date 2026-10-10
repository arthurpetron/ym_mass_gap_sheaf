/-
Recoding a supported original one-block monomial for the actual four-coordinate
Bernstein rows.  The affine factors are inverted on the ORIGINAL polynomial
Haar carrier; trailing zero exponents are compared semantically, never by a
false raw coefficient-list equality.  This is finite polynomial data only.
-/

import YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
import YMGap.Continuum.QuaternionHaarTensorBernsteinError
import YMGap.Continuum.SU2QuaternionHaarSparseEquality
import YMGap.Continuum.SU2MultiLinkHaarFactorization

namespace YMGap.Continuum.QuaternionHaarBernsteinMonomialRecoding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate
open YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
open YMGap.Continuum.QuaternionHaarTensorBernsteinError
open YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.SU2QuaternionHaarSparseEquality
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2MultiLinkHaarFactorization
open YMGap.Continuum.BernsteinFallingProductError

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private abbrev pvar := YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pvar
private abbrev ppow := YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.ppow

/-- Pull back the original exponent through `x=2y-1`. -/
def monomialFactor (m : List Nat) (i : Fin 4) : Poly :=
  compose [-1,2] (ppow pvar (exponentAt m i.val))

/-- All four factors remain on the SAME one-block Haar carrier. -/
def monomialSeparable (m : List Nat) : RatPoly :=
  polyMul (subst (shiftedCoordinate ⟨0, by decide⟩)
      (monomialFactor m ⟨0, by decide⟩))
    (polyMul (subst (shiftedCoordinate ⟨1, by decide⟩)
        (monomialFactor m ⟨1, by decide⟩))
      (polyMul (subst (shiftedCoordinate ⟨2, by decide⟩)
          (monomialFactor m ⟨2, by decide⟩))
        (subst (shiftedCoordinate ⟨3, by decide⟩)
          (monomialFactor m ⟨3, by decide⟩))))

private theorem subst_pvar (X : RatPoly) :
    RatPolyCoeffEqv (subst X pvar) X := by
  change RatPolyCoeffEqv (subst X [0,1]) X
  exact (subst_zero_cons X [1]).trans
    ((((subst_singleton X 1).trans (RatPolyCoeffEqv.one_smul polyOne)).mul_left X).trans
      (RatPolyCoeffEqv.mul_one X))

private def rawPower (i : Nat) : Nat → RatPoly
  | 0 => polyOne
  | e+1 => polyMul (polyVar i) (rawPower i e)

private theorem subst_pvar_power (i : Nat) : ∀ e : Nat,
    RatPolyCoeffEqv (subst (polyVar i) (ppow pvar e)) (rawPower i e)
  | 0 => by
      change RatPolyCoeffEqv (subst (polyVar i) [1]) polyOne
      exact (subst_singleton (polyVar i) 1).trans
        (RatPolyCoeffEqv.one_smul polyOne)
  | e+1 => by
      change RatPolyCoeffEqv
        (subst (polyVar i) (pmul pvar (ppow pvar e)))
        (polyMul (polyVar i) (rawPower i e))
      exact (subst_pmul (polyVar i) pvar (ppow pvar e)).trans
        ((subst_pvar (polyVar i)).mul (subst_pvar_power i e))

private theorem factor_unshift (m : List Nat) (i : Fin 4) :
    RatPolyCoeffEqv
      (subst (shiftedCoordinate i) (monomialFactor m i))
      (rawPower i.val (exponentAt m i.val)) := by
  exact (unitArgument_unshift (polyVar i.val)
      (ppow pvar (exponentAt m i.val))).trans
    (subst_pvar_power i.val (exponentAt m i.val))

private def rawFour (m : List Nat) : RatPoly :=
  polyMul (rawPower 0 (exponentAt m 0))
    (polyMul (rawPower 1 (exponentAt m 1))
      (polyMul (rawPower 2 (exponentAt m 2))
        (rawPower 3 (exponentAt m 3))))

private theorem separable_rawFour (m : List Nat) :
    RatPolyCoeffEqv (monomialSeparable m) (rawFour m) := by
  exact (factor_unshift m ⟨0, by decide⟩).mul
    ((factor_unshift m ⟨1, by decide⟩).mul
      ((factor_unshift m ⟨2, by decide⟩).mul
        (factor_unshift m ⟨3, by decide⟩)))

private def powerMono (i : Nat) : Nat → List Nat
  | 0 => []
  | e+1 => monoMul (varMono i) (powerMono i e)

private theorem rawPower_singleton (i : Nat) : ∀ e : Nat,
    rawPower i e = [(powerMono i e, (1 : Q'))]
  | 0 => rfl
  | e+1 => by rw [rawPower, rawPower_singleton i e]; rfl

private def fourMono (m : List Nat) : List Nat :=
  monoMul (powerMono 0 (exponentAt m 0))
    (monoMul (powerMono 1 (exponentAt m 1))
      (monoMul (powerMono 2 (exponentAt m 2))
        (powerMono 3 (exponentAt m 3))))

private theorem rawFour_singleton (m : List Nat) :
    rawFour m = [(fourMono m, (1 : Q'))] := by
  unfold rawFour fourMono
  rw [rawPower_singleton, rawPower_singleton,
    rawPower_singleton, rawPower_singleton]
  rfl

private theorem exponentAt_varMono_local (source coordinate : Nat) :
    exponentAt (varMono source) coordinate =
      if coordinate = source then 1 else 0 := by
  induction source generalizing coordinate with
  | zero => cases coordinate <;> rfl
  | succ source ih =>
      cases coordinate with
      | zero => rfl
      | succ coordinate => simpa [varMono, exponentAt] using ih coordinate

private theorem powerMono_exponent (i j : Nat) : ∀ e : Nat,
    exponentAt (powerMono i e) j = if j = i then e else 0
  | 0 => by simp [powerMono, exponentAt]
  | e+1 => by
      rw [powerMono, exponentAt_monoMul, exponentAt_varMono_local,
        powerMono_exponent i j e]
      by_cases h : j = i <;> simp [h] <;> omega

private theorem fourMono_exponent (m : List Nat) (hm : m.length ≤ 4)
    (j : Nat) : exponentAt (fourMono m) j = exponentAt m j := by
  simp only [fourMono, exponentAt_monoMul, powerMono_exponent]
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j := by omega
  rcases hj with rfl | rfl | rfl | rfl | hj
  · simp
  · simp
  · simp
  · simp
  · have hz : exponentAt m j = 0 :=
      exponentAt_of_length_le m j (by omega)
    simp [show j ≠ 0 by omega, show j ≠ 1 by omega,
      show j ≠ 2 by omega, show j ≠ 3 by omega, hz]

private theorem haar_eq_weighted : ∀ r : RatPoly,
    quaternionHaar 1 r = ratWeightedSum (quaternionHaarMono 1) r
  | [] => rfl
  | _ :: rest => by
      unfold quaternionHaar ratWeightedSum
      rw [haar_eq_weighted rest]

private theorem haar_of_coeff (p q : RatPoly)
    (h : RatPolyCoeffEqv p q) : quaternionHaar 1 p ≈ quaternionHaar 1 q := by
  rw [haar_eq_weighted p, haar_eq_weighted q]
  exact h _

/-- The four substituted factors have the Haar moment of the ORIGINAL
monomial, including unequal-length zero padding. -/
theorem monomialSeparable_haar (m : List Nat) (hm : m.length ≤ 4) :
    quaternionHaar 1 (monomialSeparable m) ≈ quaternionHaarMono 1 m := by
  have hc := haar_of_coeff (monomialSeparable m) (rawFour m)
    (separable_rawFour m)
  rw [rawFour_singleton] at hc
  have he := haarMono_congr 1 (fourMono m) m (fourMono_exponent m hm)
  exact Q'.eqv_trans _ _ _ hc
    (Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv _))
        (q_add_zero_eqv _))
      (Q'.eqv_of_eq he))

private theorem eval_affine_grid (n k : Nat) :
    QPoly.eval [-1,2] (grid n k) ≈ rawCoordinate n k := by
  change (-1 : Q') + grid n k * (2 + grid n k * 0) ≈
    2 * grid n k + -1
  exact poly_identity_of_normal_eq
    (.add (.const (-1)) (.mul (.var 0)
      (.add (.const 2) (.mul (.var 0) (.const 0)))))
    (.add (.mul (.const 2) (.var 0)) (.const (-1)))
    (by decide) (fun _ => grid n k)

private theorem eval_ppow_pvar_qpow (x : Q') : ∀ e : Nat,
    QPoly.eval (ppow pvar e) x ≈ qpow x e
  | 0 => by
      change QPoly.eval [1] x ≈ 1
      exact Q'.eqv_trans _ _ _ (eval_pconst 1 x) (Q'.eqv_refl _)
  | e+1 => by
      change QPoly.eval (pmul pvar (ppow pvar e)) x ≈ qpow x e * x
      exact Q'.eqv_trans _ _ _ (eval_pmul _ _ _)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (eval_pvar x))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (eval_ppow_pvar_qpow x e))
            (Q'.mul_comm_eqv _ _)))

private theorem factor_grid (m : List Nat) (i : Fin 4) (n k : Nat) :
    QPoly.eval (monomialFactor m i) (grid n k) ≈
      qpow (rawCoordinate n k) (exponentAt m i.val) := by
  exact Q'.eqv_trans _ _ _
    (eval_compose [-1,2] (grid n k) (ppow pvar (exponentAt m i.val)))
    (Q'.eqv_trans _ _ _
      (eval_ppow_pvar_qpow (QPoly.eval [-1,2] (grid n k)) (exponentAt m i.val))
      (qpow_eqv_congr (eval_affine_grid n k) _))

private theorem fourPower_eval (rho : Nat → Q') (m : List Nat)
    (hm : m.length ≤ 4) :
    qpow (rho 0) (exponentAt m 0) *
      (qpow (rho 1) (exponentAt m 1) *
        (qpow (rho 2) (exponentAt m 2) *
          qpow (rho 3) (exponentAt m 3))) ≈ evalMono rho m := by
  rcases m with _ | ⟨a,m⟩
  · change ((1 : Q')*(1*(1*1))) ≈ 1
    decide
  rcases m with _ | ⟨b,m⟩
  · change qpow (rho 0) a*(1*(1*1)) ≈ qpow (rho 0) a*1
    exact poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.const 1) (.mul (.const 1) (.const 1))))
      (.mul (.var 0) (.const 1)) (by decide) (fun _ => qpow (rho 0) a)
  rcases m with _ | ⟨c,m⟩
  · change qpow (rho 0) a*(qpow (rho 1) b*(1*1)) ≈
      qpow (rho 0) a*(qpow (rho 1) b*1)
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.one_mul_eqv 1))
  rcases m with _ | ⟨d,m⟩
  · change qpow (rho 0) a*(qpow (rho 1) b*(qpow (rho 2) c*1)) ≈
      qpow (rho 0) a*(qpow (rho 1) b*(qpow (rho 2) c*1))
    exact Q'.eqv_refl _
  cases m with
  | nil =>
      change qpow (rho 0) a*(qpow (rho 1) b*
        (qpow (rho 2) c*qpow (rho 3) d)) ≈
        qpow (rho 0) a*(qpow (rho 1) b*
          (qpow (rho 2) c*(qpow (rho 3) d*1)))
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv _))))
  | cons x xs => simp at hm

/-- The rational four-grid product evaluates the SAME original monomial,
not a canonical-padded surrogate. -/
theorem monomial_gridProduct (m : List Nat) (hm : m.length ≤ 4)
    (n k0 k1 k2 k3 : Nat) :
    gridProduct n (monomialFactor m ⟨0, by decide⟩)
      (monomialFactor m ⟨1, by decide⟩)
      (monomialFactor m ⟨2, by decide⟩)
      (monomialFactor m ⟨3, by decide⟩) k0 k1 k2 k3 ≈
      evalMono (rawEnvironment n k0 k1 k2 k3) m := by
  have h0 := factor_grid m ⟨0, by decide⟩ n k0
  have h1 := factor_grid m ⟨1, by decide⟩ n k1
  have h2 := factor_grid m ⟨2, by decide⟩ n k2
  have h3 := factor_grid m ⟨3, by decide⟩ n k3
  change _ ≈ evalMono (rawEnvironment n k0 k1 k2 k3) m
  exact Q'.eqv_trans _ _ _
    (mul_congr h0 (mul_congr h1 (mul_congr h2 h3)))
    (fourPower_eval (rawEnvironment n k0 k1 k2 k3) m hm)

end YMGap.Continuum.QuaternionHaarBernsteinMonomialRecoding

#print axioms YMGap.Continuum.QuaternionHaarBernsteinMonomialRecoding.monomialFactor
#print axioms YMGap.Continuum.QuaternionHaarBernsteinMonomialRecoding.monomialSeparable
#print axioms YMGap.Continuum.QuaternionHaarBernsteinMonomialRecoding.monomialSeparable_haar
#print axioms YMGap.Continuum.QuaternionHaarBernsteinMonomialRecoding.monomial_gridProduct
