/-
# Near-unit cutoff comparison of ORIGINAL product heat polynomials

The actual character tail is bounded on the same Haar carrier and combined
with the constructed original head floor. Both cutoffs may vary independently
above one computed threshold. Per-factor tolerance eta/(2(count+1)) keeps the
product comparison factor at 1+eta, rather than exponentially enlarging it.
The cutoff depends on the nome, tolerance and number of retained factors.
No source, conditional variance, terminal message or norm is inverted.
This is cutoff stability, not an analytic conditional Poincare estimate or a
changing-family survival theorem.
-/

import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.RationalLinearPowerCeiling
import YMGap.Constructive.RegularCReal

namespace YMGap.Continuum.SU2QuaternionProductHeatRelativeCutoff

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState (coeffAt_heatKernelPacket)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate (heatTerm termInterval)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
  (tailCutoff shiftedMajorant_block closedTail_small)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headCutoff headFloor headFloor_positive)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (pointwiseHeatMajorant)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
  (spacingLabelCutoff spacingTailCauchyCutoff)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat)
open YMGap.Continuum.SU2QuaternionProductHeatContraction
  (heatAt_floorCertificate productHeatCertificate)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.RationalLinearPowerCeiling (linear_inverse_bound)

local infix:50 " ≈ " => Q'.eqv

/-- Positive local tolerance, including an empty product without division
by its length. It equals eta/(2*count+2). -/
def factorTolerance (eta : Q') (count : Nat) : Q' := eta * Q'.invSucc (2*count+1)

/-- SAME threshold for both arbitrary later cutoffs and all ambient blocks. -/
def productRelativeCutoff (w eta : Q') (count : Nat) : Nat :=
  max (headCutoff w) (tailCutoff w (factorTolerance eta count * headFloor w))

private theorem factorTolerance_positive (eta : Q') (he : (0 : Q') < eta) (count : Nat) :
    (0 : Q') < factorTolerance eta count := Q'.mul_pos he (Q'.invSucc_pos _)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private def interval_neg {blocks : Nat} {p : RatPoly} {c : Q'} (P : Interval blocks p c) :
    Interval blocks (polyNeg p) c where
  support := support_neg P.support
  nonnegative := P.nonnegative
  upper := Certificate.ofCoeff
    ((RatPolyCoeffEqv.refl _).add
      (coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0)
        (by decide) (fun _ => p))) P.lower
  lower := P.upper

private theorem sum_append {T : Type} (f : T → RatPoly) : ∀ xs ys : List T,
    finitePolySum f (xs++ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], ys => rfl
  | t::ts, ys => by
      simp only [List.cons_append, finitePolySum, sum_append f ts ys, polyAdd, List.append_assoc]

private theorem sum_map {T U : Type} (f : U → RatPoly) (g : T → U) : ∀ xs : List T,
    finitePolySum f (xs.map g) = finitePolySum (fun x => f (g x)) xs
  | [] => rfl
  | t::ts => by
      simp only [List.map_cons, finitePolySum, sum_map f g ts]

private theorem sum_congr (f g : Nat → RatPoly) : ∀ xs : List Nat,
    (∀ j, j ∈ xs → f j = g j) → finitePolySum f xs = finitePolySum g xs
  | [], _ => rfl
  | j::js, h => by
      simp only [finitePolySum, h j List.mem_cons_self,
        sum_congr f g js (fun i hi => h i (List.mem_cons_of_mem j hi))]

private theorem heatAt_eq_prefix (a b : Nat) (w : Q') (K : Nat) :
    heatAt a b w K = heatPrefix w K (scalarAt a b) := by
  unfold heatAt heatPrefix
  apply sum_congr
  intro j hj
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hj)]

private def tail (w : Q') (x : RatPoly) (start count : Nat) : RatPoly :=
  finitePolySum (fun j => heatTerm w x (start+j)) (List.range count)

private theorem prefix_append (w : Q') (x : RatPoly) (K count : Nat) :
    heatPrefix w (K+count) x = polyAdd (heatPrefix w K x) (tail w x (K+1) count) := by
  unfold heatPrefix tail heatTerm
  rw [show K+count+1 = (K+1)+count by omega, List.range_add, sum_append, sum_map]

private def tail_interval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K count : Nat)
    (hK : tailCutoff w epsilon ≤ K) : Interval blocks (tail w x (K+1) count) epsilon := by
  have hN : spacingLabelCutoff w ≤ K+1 := by unfold tailCutoff at hK; omega
  have hM : spacingTailCauchyCutoff w epsilon ≤ K+1-spacingLabelCutoff w := by
    unfold tailCutoff at hK
    omega
  have h := shiftedMajorant_block hw0 hw1 (K+1-spacingLabelCutoff w) count
  simp only [← Nat.add_assoc, Nat.add_sub_of_le hN] at h
  exact (Interval.finiteRange (fun j => heatTerm w x (K+1+j))
    (fun j => pointwiseHeatMajorant w (K+1+j))
    (fun j => termInterval (Q'.le_of_lt hw0) P _) count).weaken
      (Q'.le_trans' _ _ _ h (closedTail_small hw0 hw1 epsilon he _ hM))

private def ordered_difference_interval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat) (hKL : K ≤ L)
    (hK : tailCutoff w epsilon ≤ K) :
    Interval blocks (polyAdd (heatPrefix w L x) (polyNeg (heatPrefix w K x))) epsilon := by
  have hs : SupportedQuaternionBlocks blocks (heatPrefix w K x) :=
    (QuaternionHaarAllNomeHeatCertificate.prefixInterval hw0 hw1 P K).support
  have ht : SupportedQuaternionBlocks blocks (heatPrefix w L x) :=
    (QuaternionHaarAllNomeHeatCertificate.prefixInterval hw0 hw1 P L).support
  have hx : RatPolyCoeffEqv
      (polyAdd (heatPrefix w L x) (polyNeg (heatPrefix w K x))) (tail w x (K+1) (L-K)) := by
    have hsplit : heatPrefix w L x =
        polyAdd (heatPrefix w K x) (tail w x (K+1) (L-K)) := by
      simpa only [Nat.add_sub_of_le hKL] using prefix_append w x K (L-K)
    rw [hsplit]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1) (by decide)
      (fun
        | 0 => heatPrefix w K x
        | _ => tail w x (K+1) (L-K))
  exact Interval.ofCoeff (supported_add ht (support_neg hs)) hx
    (tail_interval hw0 hw1 P epsilon he K (L-K) hK)

/-- Source-independent difference certificate on any actual ambient carrier. -/
def heatAt_differenceInterval {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat)
    (hK : tailCutoff w epsilon ≤ K) (hL : tailCutoff w epsilon ≤ L) :
    Interval blocks (polyAdd (heatAt a b w K) (polyNeg (heatAt a b w L))) epsilon := by
  let p := PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))
  have hp : Supported blocks p := (Supported.coordinate ha).mul (Supported.coordinate hb).conj
  have hu : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne :=
    haarNorm_mul (haarNorm_coordinate ha)
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate hb))
  have P : SquareBound blocks (scalarAt a b) 1 := .scalar hp hu
  rw [heatAt_eq_prefix, heatAt_eq_prefix]
  by_cases hLK : L ≤ K
  · exact ordered_difference_interval hw0 hw1 P epsilon he L K hLK hL
  · have hKL : K ≤ L := by omega
    have R := interval_neg (ordered_difference_interval hw0 hw1 P epsilon he K L hKL hK)
    exact Interval.ofCoeff (supported_add
      (QuaternionHaarAllNomeHeatCertificate.prefixInterval hw0 hw1 P K).support
      (support_neg (QuaternionHaarAllNomeHeatCertificate.prefixInterval hw0 hw1 P L).support))
      (coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 0)))) (by decide)
        (fun
          | 0 => heatPrefix w K (scalarAt a b)
          | _ => heatPrefix w L (scalarAt a b))) R

private def factor_upper {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (delta : Q') (hd : (0 : Q') < delta) (K L : Nat)
    (hK : max (headCutoff w) (tailCutoff w (delta*headFloor w)) ≤ K)
    (hL : max (headCutoff w) (tailCutoff w (delta*headFloor w)) ≤ L) :
    Certificate blocks (polyAdd (polyMul (cap (1+delta)) (heatAt a b w L))
      (polyNeg (heatAt a b w K))) := by
  let H := heatAt a b w L
  let F := heatAt a b w K
  let D := cap delta
  let E := cap (headFloor w)
  have P := heatAt_floorCertificate ha hb hw0 hw1 L (Nat.le_trans (Nat.le_max_left _ _) hL)
  have T := heatAt_differenceInterval ha hb hw0 hw1 (delta*headFloor w)
    (Q'.mul_pos hd (headFloor_positive hw0 hw1)) K L
    (Nat.le_trans (Nat.le_max_right _ _) hK) (Nat.le_trans (Nat.le_max_right _ _) hL)
  have PT : Certificate blocks (polyAdd (polyMul D E) (polyNeg (polyAdd F (polyNeg H)))) :=
    Certificate.ofCoeff ((cap_mul delta (headFloor w)).add (RatPolyCoeffEqv.refl _)) T.upper
  have PR := (Certificate.constant blocks delta (Q'.le_of_lt hd)).mul P
  have hc : RatPolyCoeffEqv (cap (1+delta)) (polyAdd (cap 1) D) :=
    (cap_add 1 delta).symm
  have halg : RatPolyCoeffEqv (polyAdd (polyMul (cap (1+delta)) H) (polyNeg F))
      (polyAdd (polyMul D (polyAdd H (polyNeg E)))
        (polyAdd (polyMul D E) (polyNeg (polyAdd F (polyNeg H))))) :=
    ((hc.mul_right H).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.const 1) (.var 2)) (.var 0)) (.neg (.var 1)))
        (.add (.mul (.var 2) (.add (.var 0) (.neg (.var 3))))
          (.add (.mul (.var 2) (.var 3)) (.neg (.add (.var 1) (.neg (.var 0))))))
        (by decide) (fun
          | 0 => H
          | 1 => F
          | 2 => D
          | _ => E))
  exact Certificate.ofCoeff halg (PR.add PT)

private theorem count_fraction_le_half (count : Nat) :
    Q'.ofNat count * Q'.invSucc (2*count+1) ≤ HalfPow.half := by
  change (Q'.ofNat count * Q'.invSucc (2*count+1)).num * 2 ≤
    1 * ((Q'.ofNat count * Q'.invSucc (2*count+1)).den : Int)
  rw [Q'.ofNat_mul_invSucc_num, Q'.ofNat_mul_invSucc_den]
  omega

private theorem count_tolerance_le (eta : Q') (he : (0 : Q') ≤ eta) (count : Nat) :
    Q'.ofNat count * factorTolerance eta count ≤ eta*HalfPow.half := by
  have hr := Q'.mul_le_mul_of_nonneg_left _ _ eta (count_fraction_le_half count) he
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun
      | 0 => Q'.ofNat count
      | 1 => eta
      | _ => Q'.invSucc (2*count+1)))) hr

private theorem factor_power_le (eta : Q') (he : (0 : Q') < eta) (he1 : eta ≤ 1) (count : Nat) :
    (1+factorTolerance eta count)^count ≤ 1+eta := by
  let d := factorTolerance eta count
  let z := Q'.ofNat count*d
  let margin := (1 : Q') + -z
  have hd := Q'.le_of_lt (factorTolerance_positive eta he count)
  have hz : z ≤ eta*HalfPow.half := count_tolerance_le eta (Q'.le_of_lt he) count
  have hhalf : eta*HalfPow.half ≤ HalfPow.half := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ HalfPow.half he1 (by decide))
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hm : HalfPow.half ≤ margin := by
    have h := Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_trans' _ _ _ hz hhalf))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : HalfPow.half ≈ 1 + -HalfPow.half)) h
  have hmpos : (0 : Q') < margin := Q'.pos_of_lt_of_le (by decide) hm
  have hone : (1 : Q')+eta ≤ 2 := Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 eta 1 he1) (by decide)
  have hp0 : (0 : Q') ≤ (1 : Q')+eta := Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt he)
  have hzprod : z*(1+eta) ≤ eta := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hz hp0)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hone
        (Q'.mul_nonneg _ _ (Q'.le_of_lt he) (by decide)))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv eta HalfPow.half 2)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left eta (HalfPow.half*2) 1 (by decide))
          (Q'.mul_one_eqv eta)))))
  have hnonneg : (0 : Q') ≤ eta + -(z*(1+eta)) := Q'.sub_nonneg_of_le hzprod
  have hguard : (1 : Q') ≤ margin*(1+eta) := by
    apply Q'.le_of_sub_nonneg
    exact Q'.le_trans' _ _ _ hnonneg (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.var 1) (.add (.const 1) (.var 0)))))
      (.add (.mul (.add (.const 1) (.neg (.var 1))) (.add (.const 1) (.var 0))) (.neg (.const 1)))
      (by decide) (fun
        | 0 => eta
        | _ => z)))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (linear_inverse_bound hd count) hguard) hmpos

private def product_order {blocks : Nat} (c d : Q') (hc : (0 : Q') ≤ c)
    (p q P Q : RatPoly) (Pq : Certificate blocks q) (PP : Certificate blocks P)
    (Hp : Certificate blocks (polyAdd (polyMul (cap c) P) (polyNeg p)))
    (Hq : Certificate blocks (polyAdd (polyMul (cap d) Q) (polyNeg q))) :
    Certificate blocks (polyAdd (polyMul (cap (c*d)) (polyMul P Q)) (polyNeg (polyMul p q))) := by
  have H := (Hp.mul Pq).add (((Certificate.constant blocks c hc).mul PP).mul Hq)
  have h := ((cap_mul c d).symm.mul_right (polyMul P Q)).add
    (RatPolyCoeffEqv.refl (polyNeg (polyMul p q)))
  exact Certificate.ofCoeff (h.trans (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.var 4) (.var 5)) (.mul (.var 2) (.var 3))) (.neg (.mul (.var 0) (.var 1))))
    (.add (.mul (.add (.mul (.var 4) (.var 2)) (.neg (.var 0))) (.var 1))
      (.mul (.mul (.var 4) (.var 2)) (.add (.mul (.var 5) (.var 3)) (.neg (.var 1)))))
    (by decide) (fun
      | 0 => p
      | 1 => q
      | 2 => P
      | 3 => Q
      | 4 => cap c
      | _ => cap d))) H

private def product_upper_power (n : Nat) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (delta : Q') (hd : (0 : Q') < delta) (K L : Nat)
    (hK : max (headCutoff w) (tailCutoff w (delta*headFloor w)) ≤ K)
    (hL : max (headCutoff w) (tailCutoff w (delta*headFloor w)) ≤ L) :
    (ids : List Nat) → (∀ i, i ∈ ids → i < n) →
    Certificate (n+n) (polyAdd (polyMul (cap ((1+delta)^ids.length)) (productHeat n w L ids))
      (polyNeg (productHeat n w K ids)))
  | [], _ => by
      have hc := (cap_mul_left 1 polyOne).trans (RatPolyCoeffEqv.one_smul polyOne)
      exact Certificate.ofCoeff ((hc.add (RatPolyCoeffEqv.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
          (by decide) (fun _ => polyOne))) (Certificate.constant _ 0 (Q'.le_refl' _))
  | i::ids, hi => by
      have hin := hi i List.mem_cons_self
      have hit (j : Nat) (hj : j ∈ ids) : j < n := hi j (List.mem_cons_of_mem i hj)
      have Pq := productHeatCertificate n hw0 hw1 K (Nat.le_trans (Nat.le_max_left _ _) hK) ids hit
      have PP := productHeatCertificate n hw0 hw1 L (Nat.le_trans (Nat.le_max_left _ _) hL) [i]
        (fun j hj => by
          have he := List.mem_singleton.mp hj
          subst j
          exact hin)
      have PP' : Certificate (n+n) (heatAt i (n+i) w L) :=
        Certificate.ofCoeff (RatPolyCoeffEqv.mul_one _).symm PP
      have H := product_order (1+delta) ((1+delta)^ids.length)
        (Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt hd))
        (heatAt i (n+i) w K) (productHeat n w K ids)
        (heatAt i (n+i) w L) (productHeat n w L ids) Pq PP'
        (factor_upper (by omega) (by omega) hw0 hw1 delta hd K L hK hL)
        (product_upper_power n hw0 hw1 delta hd K L hK hL ids hit)
      simpa only [List.length_cons, Q'.pow_succ, productHeat, polynomialProduct, List.foldr_cons] using H

/-- Near-unit comparison of both ORIGINAL prefixes, without cutoff ordering.
The actual selected list may contain repeated factors. -/
def productHeat_relative_upperCertificate (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (eta : Q') (he : (0 : Q') < eta) (he1 : eta ≤ 1)
    (K L : Nat) (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (hK : productRelativeCutoff w eta ids.length ≤ K)
    (hL : productRelativeCutoff w eta ids.length ≤ L) :
    Certificate (n+n) (polyAdd (polySmul (1+eta) (productHeat n w L ids))
      (polyNeg (productHeat n w K ids))) := by
  let c := (1+factorTolerance eta ids.length)^ids.length
  let gap := (1+eta) + -c
  have hgap : (0 : Q') ≤ gap := Q'.sub_nonneg_of_le (factor_power_le eta he he1 ids.length)
  have H := product_upper_power n hw0 hw1 (factorTolerance eta ids.length)
    (factorTolerance_positive eta he ids.length) K L hK hL ids hids
  have P := productHeatCertificate n hw0 hw1 L (Nat.le_trans (Nat.le_max_left _ _) hL) ids hids
  have hc : c+gap ≈ 1+eta := poly_identity_of_normal_eq
    (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1) (by decide)
    (fun
      | 0 => c
      | _ => 1+eta)
  have hs : RatPolyCoeffEqv
      (polyAdd (polyMul (cap c) (productHeat n w L ids))
        (polyMul (cap gap) (productHeat n w L ids)))
      (polySmul (1+eta) (productHeat n w L ids)) :=
    ((cap_mul_left c _).add (cap_mul_left gap _)).trans
      ((RatPolyCoeffEqv.add_smul_same c gap _).trans (RatPolyCoeffEqv.smul_coefficient hc _))
  have halg : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul (cap c) (productHeat n w L ids))
        (polyNeg (productHeat n w K ids))) (polyMul (cap gap) (productHeat n w L ids)))
      (polyAdd (polyAdd (polyMul (cap c) (productHeat n w L ids))
        (polyMul (cap gap) (productHeat n w L ids))) (polyNeg (productHeat n w K ids))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.neg (.var 1))) (by decide)
      (fun
        | 0 => polyMul (cap c) (productHeat n w L ids)
        | 1 => productHeat n w K ids
        | _ => polyMul (cap gap) (productHeat n w L ids))
  exact Certificate.ofCoeff (halg.trans (hs.add (RatPolyCoeffEqv.refl _))).symm
    (H.add ((Certificate.constant _ gap hgap).mul P))

end YMGap.Continuum.SU2QuaternionProductHeatRelativeCutoff

#print axioms YMGap.Continuum.SU2QuaternionProductHeatRelativeCutoff.factorTolerance
#print axioms YMGap.Continuum.SU2QuaternionProductHeatRelativeCutoff.productRelativeCutoff
#print axioms YMGap.Continuum.SU2QuaternionProductHeatRelativeCutoff.heatAt_differenceInterval
#print axioms YMGap.Continuum.SU2QuaternionProductHeatRelativeCutoff.productHeat_relative_upperCertificate
