/-
# Signed mixed-form comparison from two diagonal square bounds

The comparison is on the same supported quaternion-polynomial carrier. It
uses both p+q and p-q and retains the mixed sign. No positive certificate
for either weight, square root, or spectral argument is introduced here.
-/

import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.AbsQ
import YMGap.Constructive.CRealAdd

namespace YMGap.Continuum.QuaternionHaarSignedFormComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem weighted_add_right (blocks : Nat) (W p q r : RatPoly) :
    weightedPair blocks W p (polyAdd q r) ≈
      weightedPair blocks W p q + weightedPair blocks W p r :=
  Q'.eqv_trans _ _ _ (weighted_symm blocks W p (polyAdd q r))
    (Q'.eqv_trans _ _ _ (weighted_add_left blocks W q r p)
      (Q'.add_eqv_congr'
        (weighted_symm blocks W q p) (weighted_symm blocks W r p)))

private theorem weighted_smul_right (blocks : Nat) (W : RatPoly) (c : Q')
    (p q : RatPoly) :
    weightedPair blocks W p (polySmul c q) ≈
      c * weightedPair blocks W p q :=
  Q'.eqv_trans _ _ _ (weighted_symm blocks W p (polySmul c q))
    (Q'.eqv_trans _ _ _ (weighted_smul_left blocks W c q p)
      (Q'.mul_eqv_congr_left _ _ _ (weighted_symm blocks W q p)))

private theorem weighted_diag_linear (blocks : Nat) (W p q : RatPoly) (s : Q') :
    weightedPair blocks W (polyAdd p (polySmul s q))
      (polyAdd p (polySmul s q)) ≈
    (weightedPair blocks W p p + s * weightedPair blocks W p q) +
      (s * weightedPair blocks W p q +
        (s * s) * weightedPair blocks W q q) := by
  let t := polyAdd p (polySmul s q)
  have hp : weightedPair blocks W p t ≈
      weightedPair blocks W p p + s * weightedPair blocks W p q :=
    Q'.eqv_trans _ _ _ (weighted_add_right blocks W p p (polySmul s q))
      (Q'.add_eqv_congr_left _ _ _ (weighted_smul_right blocks W s p q))
  have hq : weightedPair blocks W (polySmul s q) t ≈
      s * (weightedPair blocks W p q + s * weightedPair blocks W q q) :=
    Q'.eqv_trans _ _ _ (weighted_smul_left blocks W s q t)
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (weighted_add_right blocks W q p (polySmul s q))
          (Q'.add_eqv_congr'
            (weighted_symm blocks W q p)
            (weighted_smul_right blocks W s q q))))
  exact Q'.eqv_trans _ _ _ (weighted_add_left blocks W p (polySmul s q) t)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hp hq)
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.var 3) (.var 1)))
          (.mul (.var 3) (.add (.var 1) (.mul (.var 3) (.var 2)))))
        (.add (.add (.var 0) (.mul (.var 3) (.var 1)))
          (.add (.mul (.var 3) (.var 1))
            (.mul (.mul (.var 3) (.var 3)) (.var 2))))
        (by decide)
        (fun | 0 => weightedPair blocks W p p
             | 1 => weightedPair blocks W p q
             | 2 => weightedPair blocks W q q
             | _ => s)))

private theorem weighted_polarization (blocks : Nat) (W p q : RatPoly) :
    let plus := polyAdd p (polySmul 1 q)
    let minus := polyAdd p (polySmul (-1) q)
    weightedPair blocks W plus plus + -(weightedPair blocks W minus minus) ≈
      4 * weightedPair blocks W p q := by
  let plus := polyAdd p (polySmul 1 q)
  let minus := polyAdd p (polySmul (-1) q)
  have hp := weighted_diag_linear blocks W p q 1
  have hm := weighted_diag_linear blocks W p q (-1)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hp (Q'.neg_eqv_congr _ _ hm))
    (poly_identity_of_normal_eq
      (.add
        (.add (.add (.var 0) (.mul (.const 1) (.var 1)))
          (.add (.mul (.const 1) (.var 1))
            (.mul (.mul (.const 1) (.const 1)) (.var 2))))
        (.neg
          (.add (.add (.var 0) (.mul (.neg (.const 1)) (.var 1)))
            (.add (.mul (.neg (.const 1)) (.var 1))
              (.mul (.mul (.neg (.const 1)) (.neg (.const 1))) (.var 2))))))
      (.mul (.const 4) (.var 1)) (by decide)
      (fun | 0 => weightedPair blocks W p p
           | 1 => weightedPair blocks W p q
           | _ => weightedPair blocks W q q))

/-- Centered polarization of a two-sided diagonal form comparison. The
quadratic bounds are required for every supported test, so they apply to
both explicit signed combinations of p and q. -/
theorem centered_polarization {blocks : Nat} (W W0 : RatPoly) (L U : Q')
    (hdiag : ∀ z : RatPoly, SupportedQuaternionBlocks blocks z →
      L * weightedPair blocks W0 z z ≤ weightedPair blocks W z z ∧
      weightedPair blocks W z z ≤ U * weightedPair blocks W0 z z)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) :
    -((U + -L) * (weightedPair blocks W0 p p + weightedPair blocks W0 q q)) ≤
      4 * weightedPair blocks W p q +
        -(2 * (L + U) * weightedPair blocks W0 p q) ∧
    4 * weightedPair blocks W p q +
        -(2 * (L + U) * weightedPair blocks W0 p q) ≤
      (U + -L) * (weightedPair blocks W0 p p + weightedPair blocks W0 q q) := by
  let plus := polyAdd p (polySmul 1 q)
  let minus := polyAdd p (polySmul (-1) q)
  have hplus : SupportedQuaternionBlocks blocks plus :=
    supported_add hp (support_smul hq 1)
  have hminus : SupportedQuaternionBlocks blocks minus :=
    supported_add hp (support_smul hq (-1))
  let bp := weightedPair blocks W plus plus
  let bm := weightedPair blocks W minus minus
  let cp := weightedPair blocks W0 plus plus
  let cm := weightedPair blocks W0 minus minus
  let P := weightedPair blocks W p q
  let C := weightedPair blocks W0 p q
  let X := weightedPair blocks W0 p p
  let Y := weightedPair blocks W0 q q
  have hBp : bp + -bm ≈ 4 * P := weighted_polarization blocks W p q
  have hUpper : bp + -bm ≤ U * cp + -(L * cm) :=
    Q'.add_le_add (hdiag plus hplus).2 (Q'.neg_le_neg (hdiag minus hminus).1)
  have hLower : L * cp + -(U * cm) ≤ bp + -bm :=
    Q'.add_le_add (hdiag plus hplus).1 (Q'.neg_le_neg (hdiag minus hminus).2)
  have hplusC := weighted_diag_linear blocks W0 p q 1
  have hminusC := weighted_diag_linear blocks W0 p q (-1)
  have hupperAlg : U * cp + -(L * cm) + -(2 * (L + U) * C) ≈
      (U + -L) * (X + Y) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ hplusC)
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hminusC)))
        (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add
          (.add
            (.mul (.var 0)
              (.add (.add (.var 2) (.mul (.const 1) (.var 3)))
                (.add (.mul (.const 1) (.var 3))
                  (.mul (.mul (.const 1) (.const 1)) (.var 4)))))
            (.neg (.mul (.var 1)
              (.add (.add (.var 2) (.mul (.neg (.const 1)) (.var 3)))
                (.add (.mul (.neg (.const 1)) (.var 3))
                  (.mul (.mul (.neg (.const 1)) (.neg (.const 1))) (.var 4)))))))
          (.neg (.mul (.mul (.const 2) (.add (.var 1) (.var 0))) (.var 3))))
        (.mul (.add (.var 0) (.neg (.var 1)))
          (.add (.var 2) (.var 4)))
        (by decide) (fun | 0 => U | 1 => L | 2 => X | 3 => C | _ => Y))
  have hlowerAlg : L * cp + -(U * cm) + -(2 * (L + U) * C) ≈
      -((U + -L) * (X + Y)) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ hplusC)
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hminusC)))
        (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add
          (.add
            (.mul (.var 1)
              (.add (.add (.var 2) (.mul (.const 1) (.var 3)))
                (.add (.mul (.const 1) (.var 3))
                  (.mul (.mul (.const 1) (.const 1)) (.var 4)))))
            (.neg (.mul (.var 0)
              (.add (.add (.var 2) (.mul (.neg (.const 1)) (.var 3)))
                (.add (.mul (.neg (.const 1)) (.var 3))
                  (.mul (.mul (.neg (.const 1)) (.neg (.const 1))) (.var 4)))))))
          (.neg (.mul (.mul (.const 2) (.add (.var 1) (.var 0))) (.var 3))))
        (.neg (.mul (.add (.var 0) (.neg (.var 1)))
          (.add (.var 2) (.var 4))))
        (by decide) (fun | 0 => U | 1 => L | 2 => X | 3 => C | _ => Y))
  have hleft : (bp + -bm) + -(2 * (L + U) * C) ≈
      4 * P + -(2 * (L + U) * C) :=
    Q'.add_eqv_congr' hBp (Q'.eqv_refl _)
  have hUpperShift := Q'.add_le_add_right (bp + -bm)
    (U * cp + -(L * cm)) (-(2 * (L + U) * C)) hUpper
  have hLowerShift := Q'.add_le_add_right (L * cp + -(U * cm))
    (bp + -bm) (-(2 * (L + U) * C)) hLower
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hlowerAlg)
      (Q'.le_trans' _ _ _ hLowerShift (Q'.le_of_eqv hleft))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hUpperShift (Q'.le_of_eqv hupperAlg))

end YMGap.Continuum.QuaternionHaarSignedFormComparison

#print axioms YMGap.Continuum.QuaternionHaarSignedFormComparison.centered_polarization
