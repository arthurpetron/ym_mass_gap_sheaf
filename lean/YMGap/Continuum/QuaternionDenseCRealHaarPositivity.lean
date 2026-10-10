/-
The ACTUAL original-Haar candidate preserves signed rational lower bounds
on supplied dense constructive-real data. Eventual input order and the
computed polynomial error meet at a point-dependent row; the input residual
is eliminated BEFORE applying original polynomial Haar. No early-row
positivity, point-uniform row index or continuous-Haar positivity is assumed.
This is not yet normalized/invariant continuous Haar, J04 or physical YM.
-/

import YMGap.Continuum.QuaternionDenseCRealHaarComparison

namespace YMGap.Continuum.QuaternionDenseCRealHaarPositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid
open YMGap.Continuum.QuaternionPointBernsteinCRealApproximation
open YMGap.Continuum.QuaternionDenseCRealHaarApproximation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets

local infix:50 " ≈ " => Q'.eqv

variable (F : UnitNorm → CReal) (R : ∀ q, InnerRegularity (F q))
variable (M : Q') (radius : Q' → Q')
variable (radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e)
variable (hM : ∀ q, leRat (CReal.abs (F q)) M)
variable (hmod : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ radius e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)

include radius_positive hM hmod in
/-- Only the actual polynomial approximation error survives in the Haar
stage. The bound c is signed; the eventual input-order residual vanishes. -/
theorem haarLower_stage (c : Q')
    (hlow : ∀ q, leEv (CReal.ofQ' c) (F q)) (k : Nat) :
    c ≤ haarApproximationValue F R M radius k + Q'.invSucc k := by
  let tau := Q'.invSucc k
  let p := haarApproximationPolynomial F R M radius k
  have hp : SupportedQuaternionBlocks 1 p :=
    realApproximation_supported F R tau _
  have hpoint (q : UnitNorm) :
      c + -tau ≤ evalRatPoly (environmentOf q.val) p := by
    let v := evalRatPoly (environmentOf q.val) p
    apply Q'.le_of_le_add_mul_invSucc _ _ 1
    intro N
    let delta := Q'.invSucc N
    obtain ⟨K, hK⟩ := hlow q delta (Q'.invSucc_pos N)
    let j := max K (realApproximationOutputRate F R tau q)
    have hinput : c ≤ (F q).approx j + delta :=
      hK j (Nat.le_max_left _ _)
    have herr : Q'.abs ((F q).approx j + -v) ≤ tau :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _))
        (realApproximation_error_at_index F R M radius radius_positive hM hmod
          tau (Q'.invSucc_pos k) _ (Nat.le_refl _) q j (Nat.le_max_right _ _))
    have hupper : c ≤ (v+tau)+delta :=
      Q'.le_trans' _ _ _ hinput
        (Q'.add_le_add_right _ _ delta (ExpNeg.le_add_of_abs_sub_le herr))
    have hcancel : ((v+tau)+delta)+ -tau ≈ v+delta :=
      poly_identity_of_normal_eq
        (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.var 1)))
        (.add (.var 0) (.var 2))
        (by decide) (fun | 0 => v | 1 => tau | _ => delta)
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-tau) hupper)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hcancel
        (Q'.add_eqv_congr_left v _ _ (Q'.eqv_symm (Q'.one_mul_eqv delta)))))
  have hl : c + -tau ≤ quaternionHaar 1 p := haar_lower_bound p hp _ hpoint
  have hcancel : (c + -tau)+tau ≈ c :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => c | _ => tau)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
    (Q'.add_le_add_right _ _ tau hl)

/-- Explicit order cutoff, retained as data rather than extracted from a
propositional eventual-order witness. -/
def haarLowerRate (epsilon : Q') : Nat := epsilon.den

/-- Signed lower-order preservation in the GENUINE real quotient, with the
computed rate above. The quotient output is the actual original-Haar candidate. -/
theorem haarLower_order (c : Q')
    (hlow : ∀ q, leEv (CReal.ofQ' c) (F q)) :
    RCle (Quotient.mk crealSetoid (CReal.ofQ' c))
      (Quotient.mk crealSetoid
        (haarApproximationReal F R M radius radius_positive hM hmod)) := by
  intro epsilon he
  refine ⟨haarLowerRate epsilon, fun k hk => ?_⟩
  have htail : Q'.invSucc k ≤ epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hk)
      (HalfPow.invSucc_den_le epsilon he)
  exact Q'.le_trans' _ _ _
    (haarLower_stage F R M radius radius_positive hM hmod c hlow k)
    (Q'.add_le_add_left _ _ _ htail)

/-- Sound input nonnegativity gives genuine quotient nonnegativity. No
coefficient-sign or early-approximation positivity hypothesis is added. -/
theorem haar_nonnegative (hpos : ∀ q, leEv CReal.czero (F q)) :
    RCnonneg (Quotient.mk crealSetoid
      (haarApproximationReal F R M radius radius_positive hM hmod)) :=
  haarLower_order F R M radius radius_positive hM hmod 0 hpos

end YMGap.Continuum.QuaternionDenseCRealHaarPositivity

#print axioms YMGap.Continuum.QuaternionDenseCRealHaarPositivity.haarLower_stage
#print axioms YMGap.Continuum.QuaternionDenseCRealHaarPositivity.haarLowerRate
#print axioms YMGap.Continuum.QuaternionDenseCRealHaarPositivity.haarLower_order
#print axioms YMGap.Continuum.QuaternionDenseCRealHaarPositivity.haar_nonnegative
