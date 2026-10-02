/-
# Exact normalized coefficients of the original elevated monomial row

The existing unnormalised Bernstein coefficient is exactly C(N,j) times
the ACTUAL normalized falling product (j)_r/(N)_r. Positive denominator
data come from the computed cutoff, not an assumed coefficient identity.
Both the supported suffix and the zero prefix j<r are included.

The final reconstruction is a direct transport of the existing monomial
reconstruction. This is coefficient algebra, not a positivity theorem,
an original Haar square certificate or a continuum result.
-/

import YMGap.Continuum.BernsteinNormalizedFallingProductError
import YMGap.Continuum.HarmonicThetaPascalEvaluation

namespace YMGap.Continuum.BernsteinNormalizedMonomialCoefficient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.BernsteinFallingProductError
open YMGap.Continuum.BernsteinNormalizedFallingProductError
open YMGap.Continuum.SU2TransvectantMixedPentagon (tvFact)
open YMGap.Continuum.SU2TransvectantFactorialSeed (tvFact_pos)
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
  (tvFallingNat tvFallingNat_mul_tailFact choose_mul_factorial_den)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments
  (falling_zero_of_lt)
open YMGap.Continuum.HarmonicThetaPascalEvaluation (pnChoose_eq_binom)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Cleared natural coefficient identity, including the truncated prefix. -/
theorem elevatedMonoCoeff_mul_falling (N r j : Nat) (hr : r ≤ N) (hj : j ≤ N) :
    elevatedMonoCoeff N r j * tvFallingNat N r =
      YMGap.RG.binom N j * tvFallingNat j r := by
  by_cases hrj : r ≤ j
  · rw [elevatedMonoCoeff, if_pos hrj, ← pnChoose_eq_binom, ← pnChoose_eq_binom]
    let D := tvFact (j-r)*tvFact (N-j)
    have hD : 0 < D := Nat.mul_pos (tvFact_pos _) (tvFact_pos _)
    have hsub : (N-r)-(j-r) = N-j := by omega
    have hleft : PNPaths.choose (N-r) (j-r)*D = tvFact (N-r) := by
      simpa only [D, hsub] using
        (choose_mul_factorial_den (N-r) (j-r) (by omega))
    have hfallj := tvFallingNat_mul_tailFact r j hrj
    have hfallN := tvFallingNat_mul_tailFact r N hr
    have hcross :
        D*(PNPaths.choose (N-r) (j-r)*tvFallingNat N r) =
          D*(PNPaths.choose N j*tvFallingNat j r) := by
      calc
        D*(PNPaths.choose (N-r) (j-r)*tvFallingNat N r) =
            (PNPaths.choose (N-r) (j-r)*D)*tvFallingNat N r := by ac_rfl
        _ = tvFact (N-r)*tvFallingNat N r := by rw [hleft]
        _ = tvFact N := by simpa only [Nat.mul_comm] using hfallN
        _ = PNPaths.choose N j*(tvFact j*tvFact (N-j)) :=
          (choose_mul_factorial_den N j hj).symm
        _ = D*(PNPaths.choose N j*tvFallingNat j r) := by
          rw [← hfallj]
          dsimp only [D]
          ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hD hcross
  · rw [elevatedMonoCoeff, if_neg hrj,
      falling_zero_of_lt j r (by omega), Nat.zero_mul, Nat.mul_zero]

/-- The original coefficient equals the binomial weight times the actual
normalized product, at the computed positive-denominator cutoff. -/
theorem elevatedMonoCoeff_eqv_normalizedProduct (n r j : Nat)
    (hr : r ≤ n+1) (hj : j ≤ n+1) (hn : denominatorCutoff r ≤ n) :
    Q'.ofNat (elevatedMonoCoeff (n+1) r j) ≈
      Q'.ofNat (YMGap.RG.binom (n+1) j)*normalizedProduct n j r hn := by
  let E := Q'.ofNat (elevatedMonoCoeff (n+1) r j)
  let C := Q'.ofNat (YMGap.RG.binom (n+1) j)
  let A := product n j r
  let B := product n (n+1) r
  let rho := Q'.invSucc n^r
  have hnat := elevatedMonoCoeff_mul_falling (n+1) r j hr hj
  have hq : E*Q'.ofNat (tvFallingNat (n+1) r) ≈ C*Q'.ofNat (tvFallingNat j r) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (SU3CharFactor.ofNat_mul_eqv _ _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (congrArg Q'.ofNat hnat))
        (SU3CharFactor.ofNat_mul_eqv _ _))
  have hring (x y z : Q') : x*(y*z) ≈ y*(x*z) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => x | 1 => y | _ => z)
  have hcleared : E*B ≈ C*A :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left E _ _ (product_falling n (n+1) r))
      (Q'.eqv_trans _ _ _ (hring E rho _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left rho _ _ hq)
          (Q'.eqv_trans _ _ _ (hring rho C _)
            (Q'.mul_eqv_congr_left C _ _ (Q'.eqv_symm (product_falling n j r))))))
  let invB := Q'.recipPos B (topProduct_positive n r hn)
  have hcancel : (E*B)*invB ≈ E :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv E B invB)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left E _ _ (Q'.mul_recipPos_eqv B (topProduct_positive n r hn)))
        (Q'.mul_one_eqv E))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancel)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ invB hcleared)
      (Q'.mul_assoc_eqv C A invB))

/-- Exact monomial reconstruction using the actual normalized coefficients.
This is only transport of the existing original elevated-monomial identity. -/
theorem normalizedProduct_reconstruction (n r : Nat) (hr : r ≤ n+1)
    (hn : denominatorCutoff r ≤ n) (w : Q') :
    finSum (fun j => (Q'.ofNat (YMGap.RG.binom (n+1) j)*normalizedProduct n j r hn)*
      bernsteinBasis (n+1) w j) (n+2) ≈ w^r := by
  refine Q'.eqv_trans _ _ _ (finSum_eqv_congr_lt _ _ (n+2) ?_)
    (elevatedMonoEval_eqv_pow (n+1) r w hr)
  intro j hj
  exact Q'.mul_eqv_congr_right _ _ (bernsteinBasis (n+1) w j)
    (Q'.eqv_symm (elevatedMonoCoeff_eqv_normalizedProduct n r j hr (by omega) hn))

#print axioms elevatedMonoCoeff_mul_falling
#print axioms elevatedMonoCoeff_eqv_normalizedProduct
#print axioms normalizedProduct_reconstruction

end YMGap.Continuum.BernsteinNormalizedMonomialCoefficient
