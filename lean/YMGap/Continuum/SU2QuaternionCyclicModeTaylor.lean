/-
# Signed Taylor expansion on the computed cyclic degree tree

No joint orthogonality or diagonal positivity is used.  Every budget takes
absolute values only after reaching the actual signed leaf Haar pairing.
-/

import YMGap.Continuum.SU2QuaternionCyclicModeReassembly
import YMGap.Constructive.AbsQ
import YMGap.Constructive.CRealAbs
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2QuaternionCyclicModeTaylor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeReassembly
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem totalCasimir_nonnegative_local : ∀ degrees : List Nat,
    (0 : Q') ≤ totalCasimir degrees
  | [] => Q'.le_refl' 0
  | _::ds => Q'.le_trans' _ _ _
      (CReal.ofNat_le_ofNat (Nat.zero_le _))
      (Q'.add_le_self_of_nonneg _ _ (totalCasimir_nonnegative_local ds))

private theorem neg_abs_le_self (x : Q') : -(Q'.abs x) ≤ x := by
  have h := Q'.neg_le_neg (Q'.le_abs_self (-x))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (Q'.neg_eqv_congr _ _ (Q'.abs_neg' x))))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv x)))

/-- Signed sum over the actual computed cyclic degree leaves. -/
def leafSum (tail : Nat) : Nat → RatPoly → RatPoly →
    (List Nat → Q') → Q'
  | 0, p, test, weight => weight [] * H (tail+1) (polyMul test p)
  | m+1, p, test, weight => qListSum ((branchDegrees tail p).map fun d =>
      leafSum tail m (nextPiece tail p d) test (fun ds => weight (d::ds)))

/-- Absolute leaf budget with a supplied nonnegative path coefficient. -/
def leafAbsSum (tail : Nat) : Nat → RatPoly → RatPoly →
    (List Nat → Q') → Q'
  | 0, p, test, weight => weight [] * Q'.abs (H (tail+1) (polyMul test p))
  | m+1, p, test, weight => qListSum ((branchDegrees tail p).map fun d =>
      leafAbsSum tail m (nextPiece tail p d) test (fun ds => weight (d::ds)))

private theorem qListSum_eqv_congr (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → f d ≈ g d) →
    qListSum (ids.map f) ≈ qListSum (ids.map g)
  | [], _ => Q'.eqv_refl _
  | d::ds, h => Q'.add_eqv_congr' (h d List.mem_cons_self)
      (qListSum_eqv_congr f g ds (fun k hk => h k (List.mem_cons_of_mem d hk)))

private theorem qListSum_le_congr (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → f d ≤ g d) →
    qListSum (ids.map f) ≤ qListSum (ids.map g)
  | [], _ => Q'.le_refl' _
  | d::ds, h => Q'.add_le_add (h d List.mem_cons_self)
      (qListSum_le_congr f g ds (fun k hk => h k (List.mem_cons_of_mem d hk)))

private theorem qListSum_neg_eqv (f : Nat → Q') : ∀ ids : List Nat,
    -(qListSum (ids.map f)) ≈ qListSum (ids.map fun d => -(f d))
  | [] => Q'.eqv_refl _
  | _d::ds => Q'.eqv_trans _ _ _ (Q'.neg_add_eqv _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (qListSum_neg_eqv f ds))

private theorem qListSum_add_eqv (f g : Nat → Q') : ∀ ids : List Nat,
    qListSum (ids.map fun d => f d + g d) ≈
      qListSum (ids.map f) + qListSum (ids.map g)
  | [] => Q'.eqv_refl _
  | d::ds => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (qListSum_add_eqv f g ds))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide) (fun
          | 0 => f d
          | 1 => g d
          | 2 => qListSum (ds.map f)
          | _ => qListSum (ds.map g)))

private theorem qListSum_smul_eqv (c : Q') (f : Nat → Q') : ∀ ids : List Nat,
    qListSum (ids.map fun d => c * f d) ≈ c * qListSum (ids.map f)
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | _d::ds => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (qListSum_smul_eqv c f ds))
      (Q'.eqv_symm (Q'.mul_add_eqv c _ _))

theorem leafSum_congr (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (left right : List Nat → Q'),
    (∀ ds, ds.length = m → left ds ≈ right ds) →
    leafSum tail m p test left ≈ leafSum tail m p test right
  | 0, p, test, left, right, h => Q'.mul_eqv_congr_right _ _ _ (h [] rfl)
  | m+1, p, test, left, right, h =>
      qListSum_eqv_congr _ _ _ (fun d _ =>
        leafSum_congr tail m (nextPiece tail p d) test _ _
          (fun ds hlen => h (d::ds) (by simp only [List.length_cons, hlen])))

theorem leafSum_add (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (left right : List Nat → Q'),
    leafSum tail m p test (fun ds => left ds + right ds) ≈
      leafSum tail m p test left + leafSum tail m p test right
  | 0, p, test, left, right =>
      poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (by decide) (fun
          | 0 => left []
          | 1 => right []
          | _ => H (tail+1) (polyMul test p))
  | m+1, p, test, left, right => by
      unfold leafSum
      exact Q'.eqv_trans _ _ _
        (qListSum_eqv_congr _ _ _ (fun d _ =>
          leafSum_add tail m (nextPiece tail p d) test _ _))
        (qListSum_add_eqv _ _ _)

theorem leafSum_smul (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (c : Q') (weight : List Nat → Q'),
    leafSum tail m p test (fun ds => c * weight ds) ≈
      c * leafSum tail m p test weight
  | 0, p, test, c, weight => Q'.mul_assoc_eqv _ _ _
  | m+1, p, test, c, weight => by
      unfold leafSum
      exact Q'.eqv_trans _ _ _
        (qListSum_eqv_congr _ _ _ (fun d _ =>
          leafSum_smul tail m (nextPiece tail p d) test c _))
        (qListSum_smul_eqv c _ _)

theorem leafAbsSum_smul (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (c : Q') (weight : List Nat → Q'),
    leafAbsSum tail m p test (fun ds => c * weight ds) ≈
      c * leafAbsSum tail m p test weight
  | 0, p, test, c, weight => Q'.mul_assoc_eqv _ _ _
  | m+1, p, test, c, weight => by
      unfold leafAbsSum
      exact Q'.eqv_trans _ _ _
        (qListSum_eqv_congr _ _ _ (fun d _ =>
          leafAbsSum_smul tail m (nextPiece tail p d) test c _))
        (qListSum_smul_eqv c _ _)

/-- The recursive scalar leaf sum is the Haar pairing with `modeFold`. -/
theorem leafSum_modeFold (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (weight : List Nat → Q'),
    H (tail+1) (polyMul test (modeFold tail m p weight)) ≈
      leafSum tail m p test weight
  | 0, p, test, weight => quaternionHaar_polyMul_smul_right _ _ _ _
  | m+1, p, test, weight => by
      unfold modeFold leafSum
      induction branchDegrees tail p with
      | nil => exact haar_of_coeff (RatPolyCoeffEqv.mul_zero_right test)
      | cons d ds ih =>
          exact Q'.eqv_trans _ _ _
            (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
            (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
              (Q'.add_eqv_congr'
                (leafSum_modeFold tail m (nextPiece tail p d) test _)
                ih))

private theorem leafSum_taylor (tail : Nat) (m : Nat) (p test : RatPoly)
    (w : Q') (K : Nat) :
    leafSum tail m p test (productAttenuation w K) ≈
      leafSum tail m p test (fun _ => (1 : Q')) +
        -( ((1 : Q')-w) * leafSum tail m p test totalCasimir) +
        leafSum tail m p test (productRemainder w K) := by
  have hp : ∀ ds, ds.length = m →
      productAttenuation w K ds ≈
        ((1 : Q') + -(((1 : Q')-w)*totalCasimir ds)) + productRemainder w K ds := by
    intro ds _
    unfold productRemainder
    exact poly_identity_of_normal_eq
      (.var 0)
      (.add (.add (.const 1) (.neg (.mul (.var 1) (.var 2))))
        (.add (.add (.var 0) (.neg (.const 1))) (.mul (.var 1) (.var 2))))
      (by decide) (fun
        | 0 => productAttenuation w K ds
        | 1 => (1 : Q')-w
        | _ => totalCasimir ds)
  exact Q'.eqv_trans _ _ _ (leafSum_congr tail m p test _ _ hp)
    (Q'.eqv_trans _ _ _
      (leafSum_add tail m p test _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (leafSum_add tail m p test _ _)
          (Q'.add_eqv_congr' (leafSum_congr tail m p test _ _
            (fun _ _ => Q'.eqv_refl _))
            (Q'.eqv_trans _ _ _
              (leafSum_congr tail m p test _ _ (fun ds _ =>
                poly_identity_of_normal_eq
                  (.neg (.mul (.var 0) (.var 1)))
                  (.mul (.neg (.var 0)) (.var 1)) (by decide)
                  (fun | 0 => (1 : Q')-w | _ => totalCasimir ds)))
              (Q'.eqv_trans _ _ _ (leafSum_smul tail m p test (-((1 : Q')-w)) totalCasimir)
              (poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.var 1))
                (.neg (.mul (.var 0) (.var 1))) (by decide)
                (fun
                  | 0 => (1 : Q')-w
                  | _ => leafSum tail m p test totalCasimir))))))
        (Q'.eqv_refl _)))

theorem leaf_two_sided_bound (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (weight bound : List Nat → Q'),
    (∀ ds, ds.length = m → (0 : Q') ≤ weight ds) →
    (∀ ds, ds.length = m → weight ds ≤ bound ds) →
    (∀ ds, ds.length = m → (0 : Q') ≤ bound ds) →
    -(leafAbsSum tail m p test bound) ≤ leafSum tail m p test weight ∧
      leafSum tail m p test weight ≤ leafAbsSum tail m p test bound
  | 0, p, test, weight, bound, hw0, hwb, hb0 => by
      let x := H (tail+1) (polyMul test p)
      have hweightLower : -(bound []) ≤ weight [] := by
        have hn := Q'.neg_le_neg (hb0 [] rfl)
        exact Q'.le_trans' _ _ _ hn
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv (by decide : (-(0 : Q')) ≈ 0)) (hw0 [] rfl))
      have hu := Q'.mul_le_of_bounds (hb0 [] rfl) (Q'.abs_nonneg x)
        hweightLower (hwb [] rfl) (neg_abs_le_self x) (Q'.le_abs_self x)
      have hlneg := Q'.mul_le_of_bounds (hb0 [] rfl) (Q'.abs_nonneg (-x))
        hweightLower (hwb [] rfl) (neg_abs_le_self (-x)) (Q'.le_abs_self (-x))
      have habsneg : Q'.abs (-x) ≈ Q'.abs x := Q'.abs_neg' x
      have hl : -(bound [] * Q'.abs x) ≤ weight [] * x := by
        have hn := Q'.neg_le_neg hlneg
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm habsneg))))
          (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv
            (poly_identity_of_normal_eq
              (.neg (.mul (.var 0) (.neg (.var 1)))) (.mul (.var 0) (.var 1))
              (by decide) (fun
                | 0 => weight []
                | _ => x))))
      exact ⟨hl, hu⟩
  | m+1, p, test, weight, bound, hw0, hwb, hb0 => by
      have hbranch (d : Nat) := leaf_two_sided_bound tail m (nextPiece tail p d) test
        (fun ds => weight (d::ds)) (fun ds => bound (d::ds))
        (fun ds h => hw0 (d::ds) (by simp only [List.length_cons, h]))
        (fun ds h => hwb (d::ds) (by simp only [List.length_cons, h]))
        (fun ds h => hb0 (d::ds) (by simp only [List.length_cons, h]))
      have hu := qListSum_le_congr _ _ (branchDegrees tail p) (fun d _ => (hbranch d).2)
      have hl0 := qListSum_le_congr
        (fun d => -(leafAbsSum tail m (nextPiece tail p d) test (fun ds => bound (d::ds))))
        (fun d => leafSum tail m (nextPiece tail p d) test (fun ds => weight (d::ds)))
        (branchDegrees tail p) (fun d _ => (hbranch d).1)
      exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (qListSum_neg_eqv _ _)) hl0, hu⟩

def pairCasimir (tail : Nat) (p test : RatPoly) : Q' :=
  leafSum tail (tail+1) p test totalCasimir

def pairRemainder (tail : Nat) (w : Q') (K : Nat) (p test : RatPoly) : Q' :=
  leafSum tail (tail+1) p test (productRemainder w K)

def pairBudget (tail : Nat) (p test : RatPoly) : Q' :=
  leafAbsSum tail (tail+1) p test
    (fun ds => totalCasimir ds * totalCasimir ds)

/-- Exact signed first-order expansion of the original full product pairing. -/
theorem productPair_taylor (tail : Nat) (w : Q') (K : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    H (tail+1) (polyMul test
      (productMap (tail+1) w K (List.range (tail+1)) p)) ≈
      H (tail+1) (polyMul test p) +
        -(((1 : Q')-w)*pairCasimir tail p test) +
        pairRemainder tail w K p test := by
  exact Q'.eqv_trans _ _ _ (productMap_modeFold tail w K p hp test)
    (Q'.eqv_trans _ _ _ (leafSum_modeFold tail (tail+1) p test _)
      (Q'.eqv_trans _ _ _ (leafSum_taylor tail (tail+1) p test w K)
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _
              (Q'.eqv_symm (leafSum_modeFold tail (tail+1) p test _))
              (full_modeFold_one_carrier tail p hp test))
            (Q'.eqv_refl _)) (Q'.eqv_refl _))))

private theorem pairRemainder_two_sided (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p test : RatPoly) :
    -((((1 : Q')-w)*((1 : Q')-w))*pairBudget tail p test) ≤
        pairRemainder tail w K p test ∧
      pairRemainder tail w K p test ≤
        (((1 : Q')-w)*((1 : Q')-w))*pairBudget tail p test := by
  let eps2 := ((1 : Q')-w)*((1 : Q')-w)
  have hraw := leaf_two_sided_bound tail (tail+1) p test
    (productRemainder w K)
    (fun ds => eps2*(totalCasimir ds*totalCasimir ds))
    (fun ds _ => (productRemainder_bounds_of_sufficientCutoff hw0 hw1 hK ds).1)
    (fun ds _ => (productRemainder_bounds_of_sufficientCutoff hw0 hw1 hK ds).2)
    (fun ds _ => Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
        (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
      (Q'.mul_nonneg _ _ (totalCasimir_nonnegative_local ds)
        (totalCasimir_nonnegative_local ds)))
  have habsScale : leafAbsSum tail (tail+1) p test
      (fun ds => eps2*(totalCasimir ds*totalCasimir ds)) ≈
      eps2*pairBudget tail p test := by
    exact leafAbsSum_smul tail (tail+1) p test eps2 _
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (Q'.eqv_symm (Q'.neg_eqv_congr _ _ habsScale))) hraw.1,
    Q'.le_trans' _ _ _ hraw.2 (Q'.le_of_eqv habsScale)⟩

theorem pairRemainder_le_quadratic (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p test : RatPoly) :
    pairRemainder tail w K p test ≤
      (((1 : Q')-w)*((1 : Q')-w))*pairBudget tail p test :=
  (pairRemainder_two_sided tail hw0 hw1 K hK p test).2

theorem neg_pairRemainder_le_quadratic (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p test : RatPoly) :
    -(pairRemainder tail w K p test) ≤
      (((1 : Q')-w)*((1 : Q')-w))*pairBudget tail p test := by
  have h := (pairRemainder_two_sided tail hw0 hw1 K hK p test).1
  exact Q'.le_trans' _ _ _ (Q'.neg_le_neg h)
    (Q'.le_of_eqv (Q'.neg_neg_eqv _))

end YMGap.Continuum.SU2QuaternionCyclicModeTaylor

#print axioms YMGap.Continuum.SU2QuaternionCyclicModeTaylor.leafSum_modeFold
#print axioms YMGap.Continuum.SU2QuaternionCyclicModeTaylor.productPair_taylor
#print axioms YMGap.Continuum.SU2QuaternionCyclicModeTaylor.leafSum_congr
#print axioms YMGap.Continuum.SU2QuaternionCyclicModeTaylor.leafSum_add
#print axioms YMGap.Continuum.SU2QuaternionCyclicModeTaylor.leafSum_smul
#print axioms YMGap.Continuum.SU2QuaternionCyclicModeTaylor.leafAbsSum_smul
#print axioms YMGap.Continuum.SU2QuaternionCyclicModeTaylor.leaf_two_sided_bound
#print axioms YMGap.Continuum.SU2QuaternionCyclicModeTaylor.pairRemainder_le_quadratic
#print axioms YMGap.Continuum.SU2QuaternionCyclicModeTaylor.neg_pairRemainder_le_quadratic
