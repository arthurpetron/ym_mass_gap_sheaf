/-
# Finite ordered products of mixed relative angular certificates

This is certificate algebra for the literal ordered `polynomialProduct`.
Every factor is certified on the same two angular planes. The cap depends
only on the list length, not on ambient block count or polynomial degree.
-/

import YMGap.Continuum.QuaternionHaarMixedRelativeAngularBound
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization

namespace YMGap.Continuum.QuaternionHaarMixedRelativeProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.QuaternionHaarMixedRelativeAngularBound
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈ " => Q'.eqv

/-- The ordered product has one mixed term per factor and two ordered
cross terms per factor pair. The square is a convenient upper cap. -/
def productMixedCost (c m : Q') (n : Nat) : Q' :=
  Q'.ofNat n * m +
    (Q'.ofNat n * c) * (Q'.ofNat n * c)

private theorem step_first (n c : Q') :
    c + n*c ≈ (n+1)*c :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.mul (.var 1) (.var 0)))
    (.mul (.add (.var 1) (.const 1)) (.var 0))
    (by decide) (fun | 0 => c | _ => n)

private theorem step_mixed (n c m : Q') (hc : (0 : Q') ≤ c) :
    (m + (n*m + (n*c)*(n*c))) +
      (c*(n*c) + c*(n*c)) ≤
    (n+1)*m + ((n+1)*c)*((n+1)*c) := by
  have hcc : (0 : Q') ≤ c*c := Q'.mul_nonneg _ _ hc hc
  have hle := Q'.add_le_self_of_nonneg
    ((m + (n*m + (n*c)*(n*c))) + (c*(n*c)+c*(n*c)))
    (c*c) hcc
  have he :
      ((m + (n*m + (n*c)*(n*c))) + (c*(n*c)+c*(n*c))) + c*c ≈
      (n+1)*m + ((n+1)*c)*((n+1)*c) :=
    poly_identity_of_normal_eq
      (.add
        (.add
          (.add (.var 2)
            (.add (.mul (.var 0) (.var 2))
              (.mul (.mul (.var 0) (.var 1))
                (.mul (.var 0) (.var 1)))))
          (.add (.mul (.var 1) (.mul (.var 0) (.var 1)))
            (.mul (.var 1) (.mul (.var 0) (.var 1)))))
        (.mul (.var 1) (.var 1)))
      (.add (.mul (.add (.var 0) (.const 1)) (.var 2))
        (.mul (.mul (.add (.var 0) (.const 1)) (.var 1))
          (.mul (.add (.var 0) (.const 1)) (.var 1))))
      (by decide) (fun | 0 => n | 1 => c | _ => m)
  exact Q'.le_trans' _ _ _ hle (Q'.le_of_eqv he)

private theorem nat_succ_cap (n : Nat) (c : Q') :
    (Q'.ofNat n + 1)*c ≈ Q'.ofNat (n+1)*c :=
  Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (Q'.ofNat_add_eqv n 1))

private theorem nat_succ_mixed (n : Nat) (c m : Q') :
    (Q'.ofNat n+1)*m +
      ((Q'.ofNat n+1)*c)*((Q'.ofNat n+1)*c) ≈
    productMixedCost c m (n+1) := by
  let a := Q'.ofNat n + 1
  let b := Q'.ofNat (n+1)
  have h : a ≈ b := Q'.eqv_symm (Q'.ofNat_add_eqv n 1)
  have hc : a*c ≈ b*c := Q'.mul_eqv_congr_right _ _ _ h
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hc)
      (Q'.mul_eqv_congr_left _ _ _ hc))

/-- Every factor in the actual list may have its own polynomial, but the
same first/mixed caps. Repetitions and order are retained. -/
def productBound {T : Type} {blocks oi oj ii ij : Nat}
    {c m : Q'} (f : T → RatPoly) :
    (ids : List T) →
    (∀ id, id ∈ ids → MixedBound blocks oi oj ii ij (f id) c c m) →
    (0 : Q') ≤ c → (0 : Q') ≤ m →
    MixedBound blocks oi oj ii ij (polynomialProduct f ids)
      (Q'.ofNat ids.length*c) (Q'.ofNat ids.length*c)
      (productMixedCost c m ids.length)
  | [], _, _, _ => by
      have H := MixedBound.ofCoeff
        (RatPolyCoeffEqv.one_smul polyOne).symm
        (MixedBound.constant blocks oi oj ii ij 1 Q'.zero_le_one)
      have h0 : (0 : Q') ≈ Q'.ofNat (List.length ([] : List T))*c :=
        Q'.eqv_symm (Q'.zero_mul_eqv c)
      have hm0 : (0 : Q') ≈ productMixedCost c m (List.length ([] : List T)) :=
        poly_identity_of_normal_eq
          (.const 0)
          (.add (.mul (.const 0) (.var 0))
            (.mul (.mul (.const 0) (.var 1))
              (.mul (.const 0) (.var 1))))
          (by decide) (fun | 0 => m | _ => c)
      exact H.changeCaps h0 h0 hm0
  | id :: ids, h, hc, hm => by
      have F := h id List.mem_cons_self
      have T := productBound f ids
        (fun a ha => h a (List.mem_cons_of_mem id ha)) hc hm
      have P := F.mul T
      let n := Q'.ofNat ids.length
      have hfirst : c + Q'.ofNat ids.length*c ≈
          Q'.ofNat (id :: ids).length*c := by
        exact Q'.eqv_trans _ _ _ (step_first n c) (nat_succ_cap ids.length c)
      have hmixed :
          (m + productMixedCost c m ids.length) +
            (c*(Q'.ofNat ids.length*c) +
              c*(Q'.ofNat ids.length*c)) ≤
          productMixedCost c m (id :: ids).length := by
        exact Q'.le_trans' _ _ _ (step_mixed n c m hc)
          (Q'.le_of_eqv (nat_succ_mixed ids.length c m))
      exact P.weaken (Q'.le_of_eqv hfirst)
        (Q'.le_of_eqv hfirst) hmixed

/-- Weaken the length-dependent certificate to any supplied finite cap.
For a two-link plaquette collar the intended cap is `N=12`. -/
def productBoundAtLength {T : Type} {blocks oi oj ii ij : Nat}
    {c m : Q'} (f : T → RatPoly) (ids : List T)
    (h : ∀ id, id ∈ ids → MixedBound blocks oi oj ii ij (f id) c c m)
    (hc : (0 : Q') ≤ c) (hm : (0 : Q') ≤ m)
    (N : Nat) (hN : ids.length ≤ N) :
    MixedBound blocks oi oj ii ij (polynomialProduct f ids)
      (Q'.ofNat N*c) (Q'.ofNat N*c)
      (productMixedCost c m N) := by
  let n := Q'.ofNat ids.length
  let M := Q'.ofNat N
  have hnM : n ≤ M := CReal.ofNat_le_ofNat hN
  have hnc : n*c ≤ M*c :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hnM hc
  have hn0 : (0 : Q') ≤ n*c :=
    Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) hc
  have hM0 : (0 : Q') ≤ M*c :=
    Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) hc
  have hsq : (n*c)*(n*c) ≤ (M*c)*(M*c) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hnc hn0)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hnc hM0)
  have hcost : productMixedCost c m ids.length ≤ productMixedCost c m N :=
    Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hnM hm) hsq
  exact (productBound f ids h hc hm).weaken hnc hnc hcost

end YMGap.Continuum.QuaternionHaarMixedRelativeProduct

#print axioms YMGap.Continuum.QuaternionHaarMixedRelativeProduct.productMixedCost
#print axioms YMGap.Continuum.QuaternionHaarMixedRelativeProduct.productBound
#print axioms YMGap.Continuum.QuaternionHaarMixedRelativeProduct.productBoundAtLength
