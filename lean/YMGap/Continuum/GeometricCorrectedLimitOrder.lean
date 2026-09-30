/-
# Removing a geometric correction in a rational Cauchy limit

An explicit geometric cutoff makes the finite correction arbitrarily small.
The right-hand rational stream comes with its actual Type-level QCauchy
modulus; the conclusion uses precisely its constructed CReal limit.
-/

import YMGap.Continuum.RCCauchySchwarz
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.TrigAddCReal
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.GeometricCorrectedLimitOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Explicit cutoff for the absolute correction, including zero rate and
zero initial mass. No modulus is extracted from a proposition. -/
def correctionCutoff (rho c I epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff rho (c * I) epsilon

/-- A finite lower bound with one geometric defect passes to the exact
constructed limit of its rational Cauchy right-hand stream. -/
theorem geometric_corrected_limit_order (rho c I a : Q')
    (hrho0 : (0 : Q') ≤ rho) (hrho1 : rho < (1 : Q'))
    (hc : (0 : Q') ≤ c) (hI : (0 : Q') ≤ I)
    (r : Nat → Q') (cr : CReal.QCauchy r)
    (hfinite : ∀ k : Nat, (c * (1 + -(rho^k))) * I ≤ a * r k) :
    RCle (Quotient.mk CReal.crealSetoid (CReal.ofQ' (c * I)))
      (RCmul (Quotient.mk CReal.crealSetoid (CReal.ofQ' a))
        (Quotient.mk CReal.crealSetoid (CReal.ofQ'CauchySeq r cr))) := by
  let t := c * I
  let R := CReal.ofQ'CauchySeq r cr
  have ht : (0 : Q') ≤ t := Q'.mul_nonneg c I hc hI
  have hright : CReal.ConvergesTo (fun k => CReal.ofQ' (a * r k))
      (CReal.mul (CReal.ofQ' a) R) := by
    apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (s := fun k => CReal.mul (CReal.ofQ' a) (CReal.ofQ' (r k)))
    · intro k
      exact CReal.Equiv.symm (CRealAlg.ofQ'_mul a (r k))
    · exact CReal.convergesTo_const_mul (CReal.ofQ' a)
        (CReal.convergesTo_ofQ'CauchySeq r cr)
  change CReal.leEv (CReal.ofQ' t) (CReal.mul (CReal.ofQ' a) R)
  apply CReal.leEv_of_ofQ'_limit_le
    (r := fun _ => t) (r' := fun k => a * r k)
    (CReal.convergesTo_const _) hright
  intro epsilon he
  refine ⟨correctionCutoff rho c I epsilon, fun k hk => ?_⟩
  have hbudget : t * rho^k ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (PositiveContractionResidual.geometric_bound hrho0 hrho1 ht he k hk)
  have halgebra : t ≈ (c * (1 + -(rho^k))) * I + t * rho^k :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.var 1))
      (.add (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 2)))) (.var 1))
        (.mul (.mul (.var 0) (.var 1)) (.var 2)))
      (by decide) (fun | 0 => c | 1 => I | _ => rho^k)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv halgebra)
    (Q'.add_le_add (hfinite k) hbudget)

#print axioms correctionCutoff
#print axioms geometric_corrected_limit_order

end YMGap.Continuum.GeometricCorrectedLimitOrder
