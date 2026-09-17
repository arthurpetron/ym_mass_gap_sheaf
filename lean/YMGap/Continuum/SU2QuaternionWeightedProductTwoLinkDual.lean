/-
# Two erased factors, one original temporal energy budget

Specialize the four-cell positive form to actual SU(2) heat factors. The
endpoint weight a is kept on both slices. The dual tests have separate
conditional centerings, while the energy observable f is arbitrary.
The twice-erased cross marginal is signed and retained, not bounded away.
-/

import YMGap.Continuum.QuaternionHaarTwoFactorDual
import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy

namespace YMGap.Continuum.SU2QuaternionWeightedProductTwoLinkDual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate heatAt_floorCertificate)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarTwoFactorDual

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- Reordering the selected kinetic factors preserves the same marginal. -/
theorem marginalPair_perm (n : Nat) (w : Q') (K : Nat) {ids js : List Nat}
    (hp : ids.Perm js) (a f r : RatPoly) :
    marginalPair n w K ids a f r ≈ marginalPair n w K js a f r := by
  have hm : RatPolyCoeffEqv (productMap n w K ids a) (productMap n w K js a) :=
    partialHaarHeads_congr n ((polynomialProduct_perm _ hp).mul_right a)
  exact haar_of_coeff ((hm.mul_left a).mul_right (polyMul f r))

private theorem edge_cons (n : Nat) (w : Q') (K i : Nat) (ids : List Nat) (a : RatPoly) :
    RatPolyCoeffEqv (polyMul (edgeWeight n w K ids a) (heatAt i (n+i) w K))
      (edgeWeight n w K (i::ids) a) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
    (.mul (.mul (.mul (.var 3) (.var 0)) (.var 1)) (.var 2)) (by decide)
    (fun | 0 => productHeat n w K ids | 1 => a | 2 => liftBoundary n a | _ => heatAt i (n+i) w K)

private theorem pair_weight {n : Nat} {p q : RatPoly} (hp : RatPolyCoeffEqv p q)
    (x y : RatPoly) : weightedPair n p x y ≈ weightedPair n q x y :=
  haar_of_coeff (hp.mul_left (polyMul x y))

/-- Genuine two-link estimate: the full jump energy of arbitrary f controls
the sum of two dual pairings, retaining the twice-erased signed cross term. -/
theorem two_link_dual_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (i j : Nat) (ids : List Nat) (hi : i < n) (hj : j < n) (hne : i ≠ j)
    (hni : i ∉ ids) (hnj : j ∉ ids) (hids : ∀ k, k ∈ ids → k < n)
    {a f r s : RatPoly} (ha : SupportedQuaternionBlocks n a)
    (hf : SupportedQuaternionBlocks n f) (hr : SupportedQuaternionBlocks n r)
    (hs : SupportedQuaternionBlocks n s) (C : Certificate n a)
    (hc : RatPolyCoeffEqv (project i (polyMul a r)) polyZero)
    (hd : RatPolyCoeffEqv (project j (polyMul a s)) polyZero) :
    let L := marginalPair n w K (j::ids) a f r + marginalPair n w K (i::ids) a f s
    let R := marginalPair n w K (j::ids) a r r + marginalPair n w K (i::ids) a s s +
      ((2 : Q')*headFloor w)*marginalPair n w K ids a r s
    ((2 : Q')*headFloor w)*(L*L) ≤
      weightedPair (n+n) (edgeWeight n w K (i::j::ids) a) (jump n f) (jump n f)*R := by
  let mu := edgeWeight n w K ids a
  let A := heatAt i (n+i) w K
  let B := heatAt j (n+j) w K
  let M : Certificate (n+n) mu :=
    ((productHeatCertificate n hw0 hw1 K hK ids hids).mul (certificate_extend n ha C)).mul
      (lift_certificate n C)
  have hin : i ∉ j::ids := fun h => (List.mem_cons.mp h).elim hne hni
  have hjn : j ∉ i::ids := fun h => (List.mem_cons.mp h).elim (Ne.symm hne) hnj
  have hjs : ∀ k, k ∈ j::ids → k < n := fun k hk =>
    (List.mem_cons.mp hk).elim (fun he => he ▸ hj) (hids k)
  have his : ∀ k, k ∈ i::ids → k < n := fun k hk =>
    (List.mem_cons.mp hk).elim (fun he => he ▸ hi) (hids k)
  have hb (x y : RatPoly) : weightedPair (n+n) (polyMul mu B) x y ≈
      weightedPair (n+n) (edgeWeight n w K (j::ids) a) x y :=
    pair_weight (edge_cons n w K j ids a) x y
  have ha' (x y : RatPoly) : weightedPair (n+n) (polyMul mu A) x y ≈
      weightedPair (n+n) (edgeWeight n w K (i::ids) a) x y :=
    pair_weight (edge_cons n w K i ids a) x y
  have hab : RatPolyCoeffEqv (polyMul (polyMul mu A) B) (edgeWeight n w K (i::j::ids) a) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4))
      (.mul (.mul (.mul (.var 3) (.mul (.var 4) (.var 0))) (.var 1)) (.var 2)) (by decide)
      (fun | 0 => productHeat n w K ids | 1 => a | 2 => liftBoundary n a | 3 => A | _ => B)
  let Li := marginalPair n w K (j::ids) a f r
  let Lj := marginalPair n w K (i::ids) a f s
  let Ri := marginalPair n w K (j::ids) a r r
  let Rj := marginalPair n w K (i::ids) a s s
  let X := marginalPair n w K ids a r s
  let J := weightedPair (n+n) (edgeWeight n w K (i::j::ids) a) (jump n f) (jump n f)
  let h := headFloor w
  have hLi := Q'.eqv_trans _ _ _ (hb (jump n f) (jump n r))
    (erased_jump_pairing n w K i (j::ids) hi hin hjs ha hf hr hc)
  have hLj := Q'.eqv_trans _ _ _ (ha' (jump n f) (jump n s))
    (erased_jump_pairing n w K j (i::ids) hj hjn his ha hf hs hd)
  have hRi := Q'.eqv_trans _ _ _ (hb (jump n r) (jump n r))
    (erased_jump_pairing n w K i (j::ids) hi hin hjs ha hr hr hc)
  have hRj := Q'.eqv_trans _ _ _ (ha' (jump n s) (jump n s))
    (erased_jump_pairing n w K j (i::ids) hj hjn his ha hs hs hd)
  have hX := erased_jump_pairing n w K j ids hj hnj hids ha hr hs hd
  have hl : weightedPair (n+n) (polyMul mu B) (jump n f) (jump n r) +
      weightedPair (n+n) (polyMul mu A) (jump n f) (jump n s) ≈ (2 : Q')*(Li+Lj) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hLi hLj) (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
  have hq : weightedPair (n+n) (polyMul mu B) (jump n r) (jump n r) +
      weightedPair (n+n) (polyMul mu A) (jump n s) (jump n s) +
      h*(weightedPair (n+n) mu (jump n r) (jump n s) +
        weightedPair (n+n) mu (jump n r) (jump n s)) ≈
      (2 : Q')*(Ri+Rj+((2 : Q')*h)*X) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' hRi hRj)
        (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' hX hX)))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
          (.mul (.var 2) (.add (.mul (.const 2) (.var 3)) (.mul (.const 2) (.var 3)))))
        (.mul (.const 2) (.add (.add (.var 0) (.var 1)) (.mul (.mul (.const 2) (.var 2)) (.var 3))))
        (by decide) (fun | 0 => Ri | 1 => Rj | 2 => h | _ => X))
  have hbase := two_factor_dual (headFloor_positive hw0 hw1) M
    (heatAt_floorCertificate (show i<n+n by omega) (show n+i<n+n by omega) hw0 hw1 K hK)
    (heatAt_floorCertificate (show j<n+n by omega) (show n+j<n+n by omega) hw0 hw1 K hK)
    (jump_supported hf) (jump_supported hr) (jump_supported hs)
  have hbound : h*(((2 : Q')*(Li+Lj))*((2 : Q')*(Li+Lj))) ≤
      J*((2 : Q')*(Ri+Rj+((2 : Q')*h)*X)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ (qmul hl hl)))
      (Q'.le_trans' _ _ _ hbase
        (Q'.le_of_eqv (qmul (pair_weight hab (jump n f) (jump n f)) hq)))
  have hleft : h*(((2 : Q')*(Li+Lj))*((2 : Q')*(Li+Lj))) ≈
      (2 : Q')*(((2 : Q')*h)*((Li+Lj)*(Li+Lj))) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 1))))
      (.mul (.const 2) (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => h | _ => Li+Lj)
  have hright : J*((2 : Q')*(Ri+Rj+((2 : Q')*h)*X)) ≈
      (2 : Q')*(J*(Ri+Rj+((2 : Q')*h)*X)) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 2) (.var 1)))
      (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => J | _ => Ri+Rj+((2 : Q')*h)*X)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hright))) (show (0 : Q') < (2 : Q') by decide)

end YMGap.Continuum.SU2QuaternionWeightedProductTwoLinkDual

#print axioms YMGap.Continuum.SU2QuaternionWeightedProductTwoLinkDual.marginalPair_perm
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductTwoLinkDual.two_link_dual_bound
