/-
# The retained companion square of a product-heat source increment

The difference-square increment has an exact positive plus-square companion.
Together they recover both endpoint second moments of the SAME symmetric
product heat. No source sign, ground-state condition, or analytic budget is
used. The companion is retained for source-specific downstream estimates.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments
import YMGap.Continuum.SU2QuaternionProductHeatMomentDefect
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension
import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.SU2QuaternionReplicaPairBounds
import YMGap.Continuum.SU2QuaternionCoordinateColumnLift

namespace YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_add lift_product lift_supported)
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionReplicaPairBounds (lift_cap_carrier)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatMomentDefect (heatLossPair jump_heatLoss_pin)
open YMGap.Continuum.SU2QuaternionProductHeatDualForm (kineticPair_symm)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap gap SquareBound)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The positive plus-square paired to the literal source increment. -/
def sourceCompanionCost (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (q f : RatPoly) : Q' :=
  let p := polyMul (jump n q) (polyAdd f (liftBoundary n f))
  weightedPair (n+n) (productHeat n w K ids) p p

/-- The literal cap-sixteen deficit of the companion test under the same
two-copy heat. The observable, not the source, carries the cap-four input. -/
def sourceCapDeficitCost (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (q f : RatPoly) : Q' :=
  let W := productHeat n w K ids
  let dq := jump n q
  let fs := polyAdd f (liftBoundary n f)
  H (n+n) (polyMul (polyMul W (polyMul dq dq)) (gap 16 fs))

/-- The SAME source jump observed through the lower endpoint's cap-four
deficit. The source itself is signed and has no pointwise cap. -/
def sourceObservedLoss (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (q f : RatPoly) : Q' :=
  let W := productHeat n w K ids
  let dq := jump n q
  H (n+n) (polyMul (polyMul W (polyMul dq dq)) (gap 4 f))

private theorem support_first {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks (n+n) p :=
  fun t ht => Nat.le_trans (hp t ht)
    (Nat.mul_le_mul_left 4 (Nat.le_add_right n n))

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem gap_supported {n : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (gap 4 f) := by
  unfold gap cap
  exact supported_add
    (by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact supported_one n s hs)
    (support_neg (supported_polyMul hf hf))

private def lowerSquareBound {n : Nat} {f : RatPoly}
    (P : SquareBound n f 4) : SquareBound (n+n) f 4 where
  support := support_first P.support
  nonnegative := P.nonnegative
  certificate := certificate_extend n (gap_supported P.support) P.certificate

private def upperSquareBound {n : Nat} {f : RatPoly}
    (P : SquareBound n f 4) :
    SquareBound (n+n) (liftBoundary n f) 4 where
  support := lift_supported P.support n
  nonnegative := P.nonnegative
  certificate := by
    have hc : HaarCarrierEqv (n+n)
        (liftBoundary n (gap 4 f)) (gap 4 (liftBoundary n f)) := by
      unfold gap
      rw [lift_add, lift_neg, lift_product]
      exact HaarCarrierEqv.add (lift_cap_carrier n 4) (HaarCarrierEqv.refl _ _)
    exact .transport hc.symm (lift_certificate n P.certificate)

theorem sourceCompanionCost_nonnegative (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) :
    (0 : Q') ≤ sourceCompanionCost n w K ids q f := by
  let p := polyMul (jump n q) (polyAdd f (liftBoundary n f))
  have hfl : SupportedQuaternionBlocks (n+n) f :=
    fun t ht => Nat.le_trans (hf t ht)
      (Nat.mul_le_mul_left 4 (Nat.le_add_right n n))
  have hp : SupportedQuaternionBlocks (n+n) p :=
    supported_polyMul (jump_supported hq)
      (supported_add hfl (lift_supported hf n))
  exact (productHeatCertificate n hw0 hw1 K hK ids hids).square_insertion_nonnegative p hp

theorem sourceCapDeficitCost_nonnegative (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q) (P : SquareBound n f 4) :
    (0 : Q') ≤ sourceCapDeficitCost n w K ids q f := by
  let W := productHeat n w K ids
  let dq := jump n q
  let fs := polyAdd f (liftBoundary n f)
  have hfs : SquareBound (n+n) fs 16 :=
    SquareBound.changeCap (by decide)
      ((lowerSquareBound P).add (upperSquareBound P))
  have hc : Certificate (n+n)
      (polyMul (polyMul W (polyMul dq dq)) (gap 16 fs)) :=
    ((productHeatCertificate n hw0 hw1 K hK ids hids).mul
      (Certificate.square dq (jump_supported hq))).mul hfs.certificate
  exact hc.haar_nonnegative

theorem sourceObservedLoss_nonnegative (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q) (P : SquareBound n f 4) :
    (0 : Q') ≤ sourceObservedLoss n w K ids q f := by
  let W := productHeat n w K ids
  let dq := jump n q
  have hc : Certificate (n+n)
      (polyMul (polyMul W (polyMul dq dq)) (gap 4 f)) :=
    ((productHeatCertificate n hw0 hw1 K hK ids hids).mul
      (Certificate.square dq (jump_supported hq))).mul (lowerSquareBound P).certificate
  exact hc.haar_nonnegative

/-- Difference and companion squares recover four times the role-swapped
one-ended cost; the original positive product heat is unchanged. -/
theorem increment_add_companion_pin (n : Nat)
    (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) :
    sourceIncrementCost n w K ids q f + sourceCompanionCost n w K ids q f ≈
      4*singleEndedCost n w K ids f q := by
  let W := productHeat n w K ids
  let im := polyMul (jump n q) (jump n f)
  let ip := polyMul (jump n q) (polyAdd f (liftBoundary n f))
  let u := polyMul f (jump n q)
  let v := polyMul (liftBoundary n f) (jump n q)
  let C := singleEndedCost n w K ids f q
  let D := weightedPair (n+n) W v v
  have hp : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul im im) W) (polyMul (polyMul ip ip) W))
      (polyAdd
        (polyAdd (polyMul (polyMul u u) W) (polyMul (polyMul u u) W))
        (polyAdd (polyMul (polyMul v v) W) (polyMul (polyMul v v) W))) := by
    let q0 : RingNormaliser.PolyExpr := .var 0
    let q1 : RingNormaliser.PolyExpr := .var 1
    let f0 : RingNormaliser.PolyExpr := .var 2
    let f1 : RingNormaliser.PolyExpr := .var 3
    let wt : RingNormaliser.PolyExpr := .var 4
    let dq := RingNormaliser.PolyExpr.add q0 (.neg q1)
    let dm := RingNormaliser.PolyExpr.add f0 (.neg f1)
    let dp := RingNormaliser.PolyExpr.add f0 f1
    let squareW (a : RingNormaliser.PolyExpr) :=
      RingNormaliser.PolyExpr.mul (.mul a a) wt
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (squareW (.mul dq dm)) (squareW (.mul dq dp)))
      (.add (.add (squareW (.mul f0 dq)) (squareW (.mul f0 dq)))
        (.add (squareW (.mul f1 dq)) (squareW (.mul f1 dq))))
      (by decide)
      (fun | 0 => q | 1 => liftBoundary n q | 2 => f
           | 3 => liftBoundary n f | _ => W)
  have hleft : sourceIncrementCost n w K ids q f +
      sourceCompanionCost n w K ids q f ≈
      H (n+n) (polyAdd (polyMul (polyMul im im) W)
        (polyMul (polyMul ip ip) W)) := by
    exact Q'.eqv_symm (quaternionHaar_append (n+n) _ _)
  have hright : H (n+n) (polyAdd
      (polyAdd (polyMul (polyMul u u) W) (polyMul (polyMul u u) W))
      (polyAdd (polyMul (polyMul v v) W) (polyMul (polyMul v v) W))) ≈
      (C+C)+(D+D) := by
    exact Q'.eqv_trans _ _ _ (quaternionHaar_append (n+n) _ _)
      (Q'.add_eqv_congr'
        (quaternionHaar_append (n+n) _ _)
        (quaternionHaar_append (n+n) _ _))
  have hs : C ≈ D := singleEnded_swap n w K ids hids hf hq
  have hfour : (C+C)+(D+D) ≈ 4*C :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl (C+C))
        (Q'.add_eqv_congr' (Q'.eqv_symm hs) (Q'.eqv_symm hs)))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
        (.mul (.const 4) (.var 0)) (by decide) (fun _ => C))
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ (haar_of_coeff hp)
      (Q'.eqv_trans _ _ _ hright hfour))

/-- The cap deficit contains the ENTIRE increment plus four times the
observed source loss. Hence inserting it into a cost formula cancels a
matching increment credit; it does not create a second independent credit.
No sign, cap, cutoff-largeness or normalized-marginal premise enters this
identity. Bounding the observed loss by its cap returns a coarse source-loss
bound, not a new survival estimate. -/
theorem capDeficit_eq_increment_observedLoss_pin (n : Nat)
    (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) :
    sourceCapDeficitCost n w K ids q f ≈
      sourceIncrementCost n w K ids q f+4*sourceObservedLoss n w K ids q f := by
  let W := productHeat n w K ids
  let dq := jump n q
  let fs := polyAdd f (liftBoundary n f)
  let p := polyMul dq fs
  let u := polyMul f dq
  let od := polyMul (polyMul W (polyMul dq dq)) (gap 4 f)
  let cd := polyMul (polyMul u u) W
  let D := sourceCapDeficitCost n w K ids q f
  let I := sourceIncrementCost n w K ids q f
  let J := sourceCompanionCost n w K ids q f
  let O := sourceObservedLoss n w K ids q f
  let C := singleEndedCost n w K ids f q
  have hp : RatPolyCoeffEqv
      (polyAdd
        (polyMul (polyMul W (polyMul dq dq)) (gap 16 fs))
        (polyMul (polyMul p p) W))
      (polyAdd (polySmul 4 od) (polySmul 4 cd)) := by
    refine (coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.add (.const 16) (.neg (.mul (.var 3) (.var 3)))))
        (.mul (.mul (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 3))) (.var 0)))
      (.add
        (.mul (.const 4)
          (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
            (.add (.const 4) (.neg (.mul (.var 2) (.var 2))))))
        (.mul (.const 4)
          (.mul (.mul (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 1))) (.var 0))))
      (by decide) (fun | 0 => W | 1 => dq | 2 => f | _ => fs)).trans ?_
    exact (YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_mul_left 4 od).add
      (YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_mul_left 4 cd)
  have hleft : D+J ≈ H (n+n)
      (polyAdd
        (polyMul (polyMul W (polyMul dq dq)) (gap 16 fs))
        (polyMul (polyMul p p) W)) :=
    Q'.eqv_symm (quaternionHaar_append (n+n) _ _)
  have hright : H (n+n) (polyAdd (polySmul 4 od) (polySmul 4 cd)) ≈
      4*O+4*C :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append (n+n) _ _)
      (Q'.add_eqv_congr'
        (quaternionHaar_polySmul (n+n) 4 od)
        (quaternionHaar_polySmul (n+n) 4 cd))
  have hsum : D+J ≈ 4*O+4*C :=
    Q'.eqv_trans _ _ _ hleft
      (Q'.eqv_trans _ _ _ (haar_of_coeff hp) hright)
  have hIJ : I+J ≈ 4*C := increment_add_companion_pin n w K ids hids hq hf
  have hcancel : (D+J)+(-J) ≈ (4*O+(I+J))+(-J) :=
    Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ hsum
        (Q'.add_eqv_congr_left (4*O) _ _ (Q'.eqv_symm hIJ)))
      (Q'.eqv_refl (-J))
  have hl : (D+J)+(-J) ≈ D :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => D | _ => J)
  have hr : (4*O+(I+J))+(-J) ≈ I+4*O :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.const 4) (.var 0)) (.add (.var 1) (.var 2))) (.neg (.var 2)))
      (.add (.var 1) (.mul (.const 4) (.var 0)))
      (by decide) (fun | 0 => O | 1 => I | _ => J)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hl) (Q'.eqv_trans _ _ _ hcancel hr)

/-- Exact original second-moment identity with BOTH positive two-copy
squares retained. It is not an interacting variance comparison. -/
theorem eight_sourceMoment_add_increment_companion_pin
    (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    {q f : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f) :
    8*sourceMoment n w K ids q (polyMul f f)+
      sourceIncrementCost n w K ids q f+sourceCompanionCost n w K ids q f ≈
      4*(H n (polyMul (polyMul q q) (polyMul f f))+
        H n (polyMul (polyMul q q) (productMap n w K ids (polyMul f f)))) := by
  let Q := H n (polyMul (polyMul q q) (polyMul f f))
  let R := H n (polyMul (polyMul q q) (productMap n w K ids (polyMul f f)))
  let U := sourceMoment n w K ids q (polyMul f f)
  let I := sourceIncrementCost n w K ids q f
  let J := sourceCompanionCost n w K ids q f
  let C := singleEndedCost n w K ids f q
  have hQ : H n (polyMul (polyMul f f) (polyMul q q)) ≈ Q :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hR : H n (polyMul (polyMul f f) (productMap n w K ids (polyMul q q))) ≈ R :=
    kineticPair_symm n w K ids hids (polyMul f f) (polyMul q q)
      (supported_polyMul hf hf) (supported_polyMul hq hq)
  have hU : H n (polyMul (polyMul (polyMul f f) q) (productMap n w K ids q)) ≈ U :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_comm (polyMul f f) q).mul_right _)
  have hC : C ≈ Q+R-2*U := Q'.eqv_trans _ _ _
    (singleEndedCost_eq_moments n w K ids hnd hids hf hq)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hQ
      (Q'.add_eqv_congr' hR (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ hU))))
      (Q'.add_assoc_eqv Q R (-(2*U))).symm)
  have hIJ : I+J ≈ 4*C :=
    increment_add_companion_pin n w K ids hids hq hf
  have hshape : 8*U+I+J ≈ 8*U+4*C :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (8*U) I J)
      (Q'.add_eqv_congr_left (8*U) _ _ hIJ)
  have hsum : 8*U+4*C ≈ 4*(Q+R) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left 4 _ _ hC))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 8) (.var 0))
          (.mul (.const 4) (.add (.add (.var 1) (.var 2))
            (.neg (.mul (.const 2) (.var 0))))))
        (.mul (.const 4) (.add (.var 1) (.var 2)))
        (by decide) (fun | 0 => U | 1 => Q | _ => R))
  exact Q'.eqv_trans _ _ _ hshape hsum

/-- The companion and its cap deficit partition the SAME source jump loss.
The identity has no heat-sign or cap hypothesis; those enter positivity. -/
theorem companion_add_capDeficit_heatLoss_pin (n : Nat) (w : Q')
    (K : Nat) (ids : List Nat) (hnd : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q)
    (_hf : SupportedQuaternionBlocks n f) :
    sourceCompanionCost n w K ids q f+
      sourceCapDeficitCost n w K ids q f ≈
      32*heatLossPair n w K ids q q := by
  let W := productHeat n w K ids
  let dq := jump n q
  let fs := polyAdd f (liftBoundary n f)
  let p := polyMul dq fs
  have hpoly : RatPolyCoeffEqv
      (polyAdd
        (polyMul (polyMul p p) W)
        (polyMul (polyMul W (polyMul dq dq)) (gap 16 fs)))
      (polySmul 16 (polyMul (polyMul dq dq) W)) := by
    refine (coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
          (.var 2))
        (.mul (.mul (.var 2) (.mul (.var 0) (.var 0)))
          (.add (.const 16) (.neg (.mul (.var 1) (.var 1))))))
      (.mul (.const 16) (.mul (.mul (.var 0) (.var 0)) (.var 2)))
      (by decide) (fun | 0 => dq | 1 => fs | _ => W)).trans ?_
    exact YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_mul_left 16 _
  have hsum : sourceCompanionCost n w K ids q f+
      sourceCapDeficitCost n w K ids q f ≈
      16*weightedPair (n+n) W dq dq :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (quaternionHaar_append (n+n) _ _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff hpoly)
        (quaternionHaar_polySmul (n+n) 16 _))
  have hheat := jump_heatLoss_pin n w K ids hnd hids q q hq hq
  exact Q'.eqv_trans _ _ _ hsum
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 16 _ _ hheat)
      (poly_identity_of_normal_eq
        (.mul (.const 16) (.mul (.const 2) (.var 0)))
        (.mul (.const 32) (.var 0))
        (by decide) (fun _ => heatLossPair n w K ids q q)))

end YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion

#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion.sourceCompanionCost
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion.sourceCapDeficitCost
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion.sourceObservedLoss
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion.sourceCompanionCost_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion.sourceCapDeficitCost_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion.sourceObservedLoss_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion.increment_add_companion_pin
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion.capDeficit_eq_increment_observedLoss_pin
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion.eight_sourceMoment_add_increment_companion_pin
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion.companion_add_capDeficit_heatLoss_pin
