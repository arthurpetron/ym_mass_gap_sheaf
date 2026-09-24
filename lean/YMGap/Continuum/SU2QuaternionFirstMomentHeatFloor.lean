/-
# A finite-path first-moment floor for the full quaternion heat pairing

The scalar first-moment attenuation floor is summed on the actual full-cycle
diagonal path measure.  Positivity belongs to the diagonal path pairings, not
to the signed input polynomial.  The result keeps the first Casimir moment
unattenuated and assumes neither a source-degree cutoff nor a new projector.
-/

import YMGap.Continuum.SU2HeatProductFirstMomentFloor
import YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment
import YMGap.Continuum.SU2QuaternionCyclicPathReassembly

namespace YMGap.Continuum.SU2QuaternionFirstMomentHeatFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
  (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatProductFirstMomentFloor
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_carrier)

local notation:max "H" n:arg => quaternionHaar n
local infix:50 " ≈ " => Q'.eqv

private theorem neg_one_mul (x : Q') : (-1 : Q') * x ≈ -x :=
  poly_identity_of_normal_eq
    (.mul (.neg (.const 1)) (.var 0)) (.neg (.var 0))
    (by decide) (fun _ => x)

private theorem half_two_mul (x : Q') : HalfPow.half * (2*x) ≈ x :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half 2 x))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ x (by decide : HalfPow.half*2 ≈ 1))
      (Q'.one_mul_eqv x))

private theorem two_mul (x : Q') : (2 : Q')*x ≈ x+x :=
  poly_identity_of_normal_eq
    (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0))
    (by decide) (fun _ => x)

private theorem sub_add_cancel (x y : Q') : (x-y)+y ≈ x :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
    (by decide) (fun | 0 => x | _ => y)

private theorem half_add_self (x : Q') :
    HalfPow.half*x + HalfPow.half*x ≈ x :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv HalfPow.half x x))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left HalfPow.half _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl x) (Q'.eqv_refl x)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left HalfPow.half _ _
          (Q'.eqv_symm (two_mul x)))
        (half_two_mul x)))

private theorem add_cancel_right {a b c : Q'} (h : a+c ≤ b+c) : a ≤ b := by
  have hc (x : Q') : (x+c)+(-c) ≈ x :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv x c (-c))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left x _ _ (Q'.add_neg_self_eqv c))
        (Q'.eqv_of_eq (Q'.add_zero' x)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hc a))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-c) h)
      (Q'.le_of_eqv (hc b)))

private theorem qListSum_add (f g : Nat → Q') : ∀ ids : List Nat,
    qListSum (ids.map fun d => f d + g d) ≈
      qListSum (ids.map f) + qListSum (ids.map g)
  | [] => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | d::ds => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (qListSum_add f g ds))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide) (fun
          | 0 => f d | 1 => g d
          | 2 => qListSum (ds.map f) | _ => qListSum (ds.map g)))

private theorem qListSum_congr (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → f d ≈ g d) →
    qListSum (ids.map f) ≈ qListSum (ids.map g)
  | [], _ => Q'.eqv_refl _
  | d::ds, h => Q'.add_eqv_congr' (h d List.mem_cons_self)
      (qListSum_congr f g ds
        (fun k hk => h k (List.mem_cons_of_mem d hk)))

private theorem qListSum_scale (c : Q') (f : Nat → Q') : ∀ ids : List Nat,
    qListSum (ids.map fun d => c * f d) ≈ c * qListSum (ids.map f)
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | _::ds => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (qListSum_scale c f ds))
      (Q'.eqv_symm (Q'.mul_add_eqv c _ _))

private theorem leaf_congr (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (left right : List Nat → Q'),
    (∀ ds, ds.length = m → left ds ≈ right ds) →
    leafSum tail m p test left ≈ leafSum tail m p test right
  | 0, p, test, left, right, h => Q'.mul_eqv_congr_right _ _ _ (h [] rfl)
  | m+1, p, test, left, right, h =>
      qListSum_congr _ _ _ (fun d _ =>
        leaf_congr tail m (nextPiece tail p d) test _ _
          (fun ds hlen => h (d::ds) (by simp only [List.length_cons, hlen])))

private theorem leaf_add (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (left right : List Nat → Q'),
    leafSum tail m p test (fun ds => left ds + right ds) ≈
      leafSum tail m p test left + leafSum tail m p test right
  | 0, p, test, left, right =>
      poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (by decide) (fun
          | 0 => left [] | 1 => right []
          | _ => H (tail+1) (polyMul test p))
  | m+1, p, test, left, right => by
      unfold leafSum
      exact Q'.eqv_trans _ _ _
        (qListSum_congr _ _ _ (fun d _ =>
          leaf_add tail m (nextPiece tail p d) test _ _))
        (qListSum_add
          (fun d => leafSum tail m (nextPiece tail p d) test
            (fun ds => left (d::ds)))
          (fun d => leafSum tail m (nextPiece tail p d) test
            (fun ds => right (d::ds))) _)

private theorem leaf_scale (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (c : Q') (weight : List Nat → Q'),
    leafSum tail m p test (fun ds => c * weight ds) ≈
      c * leafSum tail m p test weight
  | 0, _, _, _, _ => Q'.mul_assoc_eqv _ _ _
  | m+1, p, test, c, weight => by
      unfold leafSum
      exact Q'.eqv_trans _ _ _
        (qListSum_congr _ _ _ (fun d _ =>
          leaf_scale tail m (nextPiece tail p d) test c _))
        (qListSum_scale c _ _)

private theorem firstMoment_leaf_eq (tail M : Nat) (w : Q') (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    leafSum tail (tail+1) p p (fun ds =>
      RGTransport.qpow w M * (Q'.ofNat M - totalCasimir ds)) ≈
      RGTransport.qpow w M *
        (Q'.ofNat M * H (tail+1) (polyMul p p) - pairCasimir tail p p) := by
  let oneWeight := fun _ : List Nat => (1 : Q')
  have hsplit := leaf_congr tail (tail+1) p p
    (fun ds => RGTransport.qpow w M * (Q'.ofNat M - totalCasimir ds))
    (fun ds => RGTransport.qpow w M *
      (Q'.ofNat M * oneWeight ds + (-1) * totalCasimir ds))
    (fun ds _ => poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.mul (.var 0)
        (.add (.mul (.var 1) (.const 1)) (.mul (.neg (.const 1)) (.var 2))))
      (by decide) (fun | 0 => RGTransport.qpow w M | 1 => Q'.ofNat M
                       | _ => totalCasimir ds))
  refine Q'.eqv_trans _ _ _ hsplit (Q'.eqv_trans _ _ _
    (leaf_scale tail (tail+1) p p (RGTransport.qpow w M) _) ?_)
  refine Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
    (leaf_add tail (tail+1) p p
      (fun ds => Q'.ofNat M * oneWeight ds)
      (fun ds => (-1) * totalCasimir ds)) ?_)
  have hone := Q'.eqv_trans _ _ _
    (leaf_scale tail (tail+1) p p (Q'.ofNat M) oneWeight)
    (Q'.mul_eqv_congr_left _ _ _ (full_leafSum_one tail p p hp))
  have hcasimir := Q'.eqv_trans _ _ _
    (leaf_scale tail (tail+1) p p (-1) totalCasimir)
    (neg_one_mul (pairCasimir tail p p))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hone hcasimir)
    (Q'.eqv_refl _)

private theorem attenuation_leaf_eq (tail M : Nat) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    leafSum tail (tail+1) p p (fun ds =>
      Q'.ofNat M * productAttenuation w K ds) ≈
      Q'.ofNat M * H (tail+1) (polyMul p
        (productMap (tail+1) w K (List.range (tail+1)) p)) := by
  refine Q'.eqv_trans _ _ _
    (leaf_scale tail (tail+1) p p (Q'.ofNat M) _) ?_
  apply Q'.mul_eqv_congr_left
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (leafSum_modeFold tail (tail+1) p p _))
    (haar_of_carrier (HaarCarrierEqv.mul_left p
      (productMap_modeFold tail w K p hp).symm))

/-- Full finite-path first-moment heat floor for an arbitrary supported signed
polynomial. The first Casimir moment is not attenuated and no source-degree
cutoff hypothesis is used. -/
theorem fullProductPairing_firstMoment_floor (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K M : Nat) (hMK : M ≤ K)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    RGTransport.qpow w M *
        (Q'.ofNat M * H (tail+1) (polyMul p p) - pairCasimir tail p p) ≤
      Q'.ofNat M * H (tail+1) (polyMul p
        (productMap (tail+1) w K (List.range (tail+1)) p)) := by
  have hpaths := full_leafSum_diagonal_mono tail p hp
    (fun ds => RGTransport.qpow w M * (Q'.ofNat M - totalCasimir ds))
    (fun ds => Q'.ofNat M * productAttenuation w K ds)
    (fun ds _ => productAttenuation_firstMoment_floor hw0 hw1 K M hMK ds)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (firstMoment_leaf_eq tail M w p hp))
    (Q'.le_trans' _ _ _ hpaths
      (Q'.le_of_eqv (attenuation_leaf_eq tail M w K p hp)))

/-- Scalar extraction used after summing several first-moment floors.  An
aggregate energy cost at most `D*A`, together with `2*D ≤ M`, leaves half of
the unattenuated `M*A` term.  No division is used. -/
theorem firstMoment_half_floor (power M A E Z D : Q')
    (hpower : (0 : Q') ≤ power) (hM : (0 : Q') < M)
    (hA : (0 : Q') ≤ A) (hE : E ≤ D*A) (hcap : 2*D ≤ M)
    (hheat : power*(M*A-E) ≤ M*Z) :
    (HalfPow.half*power)*A ≤ Z := by
  have htwE : 2*E ≤ M*A := by
    have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ _ hE (by decide : (0 : Q') ≤ 2)
    have hsecond := Q'.mul_le_mul_of_nonneg_right _ _ _ hcap hA
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv
        (poly_identity_of_normal_eq
          (.mul (.const 2) (.mul (.var 0) (.var 1)))
          (.mul (.mul (.const 2) (.var 0)) (.var 1)) (by decide)
          (fun | 0 => D | _ => A))) hsecond)
  have hEhalf : E ≤ HalfPow.half*(M*A) := by
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ htwE
      (by decide : (0 : Q') ≤ HalfPow.half)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
      (half_two_mul E))
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.eqv_refl _)))
  have hhalf : HalfPow.half*(M*A) ≤ M*A-E := by
    have hadd := Q'.add_le_add_right E (HalfPow.half*(M*A))
      (HalfPow.half*(M*A)) hEhalf
    apply add_cancel_right (c := E)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_comm_eqv E _))
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (half_add_self (M*A))
          (Q'.eqv_symm (sub_add_cancel (M*A) E)))))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hhalf hpower
  apply Q'.le_of_mul_le_mul_left (c := M) (hc := hM)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.var 2) (.mul (.var 1) (.mul (.var 0) (.var 3))))
      (by decide)
      (fun | 0 => M | 1 => HalfPow.half | 2 => power | _ => A)))
    (Q'.le_trans' _ _ _ hscaled hheat)

#print axioms fullProductPairing_firstMoment_floor
#print axioms firstMoment_half_floor

end YMGap.Continuum.SU2QuaternionFirstMomentHeatFloor
