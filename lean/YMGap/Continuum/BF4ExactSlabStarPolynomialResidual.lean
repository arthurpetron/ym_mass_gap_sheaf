/-
# A polynomial test in the genuine interacting conditional kernel

For an original full-action polynomial p, form D*p-Np after lifting the
actual one-link normalizer D and inserted numerator Np to the same original
carrier. This polynomial pairs to zero against every exterior probe under
the original full action, hence its completed conditional projection is zero.
It supplies an explicit dual test for the original residual; no contraction,
coercivity, scaling, or OS conclusion is claimed.
-/

import YMGap.Continuum.BF4ExactSlabConditionalSweep
import YMGap.Continuum.BF4ExactSlabStarVarianceReplica
import YMGap.Continuum.GNSFiniteSumEnergy

namespace YMGap.Continuum.BF4ExactSlabStarPolynomialResidual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarCompletedInverse
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabStarVarianceReplica
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "N" => numeratorMap hw0 hw1 K extent hK i.val i.property
local notation "M" => normalizerMap hw0 hw1 K extent hK i.val i.property
local notation "P" => projections hw0 hw1 K extent hK

private def density : (G).V :=
  ⟨normalizer w K extent i.val i.property,
    normalizer_supported w K extent i.val i.property⟩

private def densityProduct (p : (F).V) : (F).V :=
  ⟨polyMul (J (density hw0 hw1 K extent hK i)).val p.val,
    supported_polyMul (J (density hw0 hw1 K extent hK i)).property p.property⟩

/-- A literal supported polynomial D*p-Np on the original full-action carrier. -/
def polynomialResidual (p : (F).V) : (F).V :=
  (F).sub (densityProduct hw0 hw1 K extent hK i p) (J (N p))

/-- The original weighted form, not the star-deleted Haar form, annihilates
every exterior test against the polynomial residual. -/
theorem polynomialResidual_probe_zero (p : (F).V) (r : (G).V) :
    (F).B (J r) (polynomialResidual hw0 hw1 K extent hK i p) ≈ 0 := by
  let d := density hw0 hw1 K extent hK i
  let rd : (G).V := ⟨polyMul r.val d.val, supported_polyMul r.property d.property⟩
  have hJ : (J rd).val = polyMul (J r).val (J d).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) r.val d.val
  have hfirst : (F).B (J r) (densityProduct hw0 hw1 K extent hK i p) ≈
      (G).B rd (N p) := by
    have hc : (F).B (J r) (densityProduct hw0 hw1 K extent hK i p) ≈
        (F).B (J rd) p := by
      change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
      rw [hJ]
      exact haar_of_coeff ((RatPolyCoeffEqv.mul_assoc (J r).val (J d).val p.val).symm.mul_right _)
    exact Q'.eqv_trans _ _ _ hc
      (probeMap_test hw0 hw1 K extent hK i.val i.property rd p)
  have hsecond : (G).B rd (N p) ≈ (G).B r (M (N p)) := by
    change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
    exact haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
      (fun | 0 => r.val | 1 => d.val | _ => (N p).val)).mul_right _)
  have hthird := probeMap_pair hw0 hw1 K extent hK i.val i.property r (N p)
  exact Q'.eqv_trans _ _ _ ((F).B_add_right (J r)
    (densityProduct hw0 hw1 K extent hK i p) ((F).neg (J (N p))))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ hfirst hsecond)
      ((F).B_neg_right (J r) (J (N p))))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ hthird)) (Q'.add_neg_self_eqv _)))

private theorem haar_neg (blocks : Nat) : ∀ q : RatPoly,
    quaternionHaar blocks (polyNeg q) ≈ -(quaternionHaar blocks q)
  | [] => by change (0 : Q') ≈ -0; decide
  | t :: qs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 _) (haar_neg blocks qs))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

set_option maxHeartbeats 2000000 in
/-- Pairing the computed kernel polynomial with its original input is exactly the
two-copy conditional variance numerator, with the original exterior action. -/
theorem polynomialResidual_variance_pair (p : (F).V) :
    (F).B p (polynomialResidual hw0 hw1 K extent hK i p) ≈
      quaternionHaar ((boundaryCompleteSlabLinks extent).length-1)
        (polyMul (varianceNumerator w K extent i.val i.property p.val)
          (exterior w K extent i.val i.property)) := by
  let d := density hw0 hw1 K extent hK i
  let pp : (F).V := ⟨polyMul p.val p.val, supported_polyMul p.property p.property⟩
  have hfirst : (F).B p (densityProduct hw0 hw1 K extent hK i p) ≈
      (G).B d (N pp) := by
    have hp : (F).B p (densityProduct hw0 hw1 K extent hK i p) ≈
        (F).B (J d) pp := by
      change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
      exact haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 1) (.var 0)))
        (.mul (.var 1) (.mul (.var 0) (.var 0))) (by decide)
        (fun | 0 => p.val | _ => (J d).val)).mul_right _)
    exact Q'.eqv_trans _ _ _ hp
      (probeMap_test hw0 hw1 K extent hK i.val i.property d pp)
  have hsecond : (F).B p (J (N p)) ≈ (G).B (N p) (N p) :=
    Q'.eqv_trans _ _ _ ((F).B_symm p (J (N p)))
      (probeMap_test hw0 hw1 K extent hK i.val i.property (N p) p)
  have hneg : quaternionHaar ((boundaryCompleteSlabLinks extent).length-1)
      (polyMul (polyNeg (polyMul (N p).val (N p).val))
        (exterior w K extent i.val i.property)) ≈
      -(quaternionHaar ((boundaryCompleteSlabLinks extent).length-1)
        (polyMul (polyMul (N p).val (N p).val)
          (exterior w K extent i.val i.property))) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.neg (.var 0)) (.var 1)) (.neg (.mul (.var 0) (.var 1)))
        (by decide)
        (fun
          | 0 => polyMul (N p).val (N p).val
          | _ => exterior w K extent i.val i.property)))
      (haar_neg _ _)
  have hvariance : (G).B d (N pp) + -((G).B (N p) (N p)) ≈
      quaternionHaar ((boundaryCompleteSlabLinks extent).length-1)
        (polyMul (varianceNumerator w K extent i.val i.property p.val)
          (exterior w K extent i.val i.property)) := by
    change _ ≈ quaternionHaar _ (polyMul
      (polyAdd (polyMul d.val (N pp).val)
        (polyNeg (polyMul (N p).val (N p).val)))
      (exterior w K extent i.val i.property))
    rw [polyMul_add_left_exact]
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hneg))
  exact Q'.eqv_trans _ _ _ ((F).B_add_right p
    (densityProduct hw0 hw1 K extent hK i p) ((F).neg (J (N p))))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hfirst
      (Q'.eqv_trans _ _ _ ((F).B_neg_right p (J (N p)))
        (Q'.neg_eqv_congr _ _ hsecond))) hvariance)

private theorem polynomialResidual_numerator_rad (p : (F).V) :
    (G).rad (N (polynomialResidual hw0 hw1 K extent hK i p)) (G).zero := by
  let t := polynomialResidual hw0 hw1 K extent hK i p
  apply ((G).rad_zero_iff (N t)).2
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (probeMap_test hw0 hw1 K extent hK i.val i.property (N t) t))
    (polynomialResidual_probe_zero hw0 hw1 K extent hK i p (N t))

private theorem eq_zero_of_norm_zero (x : GNSCompletionSpace F)
    (h : (F).cinnerCompl x x = RCzero) : x = embedV F (F).zero := by
  have hz : RCsub RCzero RCzero = RCzero :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.add_neg_self_eqv 0))
  apply eq_of_distance_le_zero
  rw [(F).cinnerCompl_cSub_left, (F).cinnerCompl_embedZero_left,
    (F).cinnerCompl_comm x ((F).cSub x (embedV F (F).zero)),
    (F).cinnerCompl_cSub_left, (F).cinnerCompl_embedZero_left, h, hz, hz]
  exact RCle_refl _

/-- The computed original polynomial lies in the actual completed
conditional-projection kernel, not merely the star-deleted free kernel. -/
theorem polynomialResidual_projection_zero (p : (F).V) :
    (P).op i (embedV F (polynomialResidual hw0 hw1 K extent hK i p)) =
      embedV F (F).zero := by
  let t := polynomialResidual hw0 hw1 K extent hK i p
  have hn : embedV G (N t) = embedV G (G).zero :=
    Quotient.sound (embed_null_of_rad G
      (polynomialResidual_numerator_rad hw0 hw1 K extent hK i p))
  have hself : (F).cinnerCompl
      (conditionalUpdate hw0 hw1 K extent hK i.val i.property t)
      (conditionalUpdate hw0 hw1 K extent hK i.val i.property t) = RCzero := by
    rw [conditionalUpdate_self_pairing]
    change (F).cinnerCompl
      (probeCompletion hw0 hw1 K extent hK i.val i.property
        (inverseState hw0 hw1 K extent hK i.val i.property (N t)))
      (embedV F t) = RCzero
    rw [probeCompletion_test, hn, (G).cinnerCompl_embedZero_right]
  change conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F t) = _
  rw [conditionalProjection_embed]
  exact eq_zero_of_norm_zero hw0 hw1 K extent hK _ hself

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem le_of_sub_nonneg {a b : RC} (h : RCnonneg (RCsub b a)) : RCle a b := by
  have he : RCadd (RCsub b a) a = b := by
    refine Quotient.inductionOn₂ b a ?_
    intro B A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.sub_add_cancel_eqv _ _))
  have hs := RCadd_le_add h (RCle_refl a)
  rw [rc_zero_add, he] at hs
  exact hs

private theorem dual_sub_identity (a b c : RC) :
    RCsub (RCsub a b) (RCsub b c) =
      RCsub a (RCsub (RCadd b b) c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 0) (.neg (.add (.add (.var 1) (.var 1)) (.neg (.var 2)))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

/-- A genuine polynomial dual test for the original conditional residual.
The inequality has no coarse normalizer-floor factor; its strength depends
on finding a test with useful signed pairing and norm. -/
theorem polynomialResidual_dual_lower (p f : (F).V) :
    let t := polynomialResidual hw0 hw1 K extent hK i p
    let x := embedV F f
    let y := embedV F t
    RCle (RCsub (RCadd ((F).cinnerCompl x y) ((F).cinnerCompl x y))
      ((F).cinnerCompl y y)) (normSq ((P).residual i x)) := by
  dsimp only
  let t := polynomialResidual hw0 hw1 K extent hK i p
  let x := embedV F f
  let y := embedV F t
  let v := (P).residual i x
  have ht := polynomialResidual_projection_zero hw0 hw1 K extent hK i p
  have hv : (F).cinnerCompl v y = (F).cinnerCompl x y := by
    change (F).cinnerCompl ((F).cSub x ((P).op i x)) y = _
    rw [(F).cinnerCompl_cSub_left, (P).adjoint i x y, ht,
      (F).cinnerCompl_embedZero_right, rc_sub_zero]
  have hs : RCnonneg (normSq ((F).cSub v y)) := (F).cinner_self_nonneg _
  have hexp : normSq ((F).cSub v y) =
      RCsub (RCsub (normSq v) ((F).cinnerCompl v y))
        (RCsub ((F).cinnerCompl v y) (normSq y)) := by
    unfold normSq
    rw [(F).cinnerCompl_cSub_left,
      (F).cinnerCompl_comm v ((F).cSub v y),
      (F).cinnerCompl_cSub_left,
      (F).cinnerCompl_comm y ((F).cSub v y),
      (F).cinnerCompl_cSub_left,
      (F).cinnerCompl_comm y v]
  rw [hexp, hv, dual_sub_identity] at hs
  exact le_of_sub_nonneg hs

/-- Entirely finite rational data for a proposed polynomial dual test. -/
def dualValue (p f : (F).V) : Q' :=
  let t := polynomialResidual hw0 hw1 K extent hK i p
  ((F).B f t + (F).B f t) + -((F).B t t)

private theorem embed_pair (D : GNSData) (a b : D.V) :
    D.cinnerCompl (embedV D a) (embedV D b) =
      Quotient.mk crealSetoid (ofQ' (D.B a b)) := D.cinnerCompl_embed a b

private theorem embed_dual (D : GNSData) (f t : D.V) :
    Quotient.mk crealSetoid (ofQ' ((D.B f t + D.B f t) + -(D.B t t))) =
      RCsub (RCadd (D.cinnerCompl (embedV D f) (embedV D t))
        (D.cinnerCompl (embedV D f) (embedV D t)))
        (D.cinnerCompl (embedV D t) (embedV D t)) := by
  rw [embed_pair, embed_pair]
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- A computed rational test value bounds the ACTUAL completed residual.
No positivity or nonzero denominator hypothesis is needed. -/
theorem dualValue_lower (p f : (F).V) :
    RCle (Quotient.mk crealSetoid (ofQ' (dualValue hw0 hw1 K extent hK i p f)))
      (normSq ((P).residual i (embedV F f))) := by
  have h := polynomialResidual_dual_lower hw0 hw1 K extent hK i p f
  dsimp only at h
  rw [← embed_dual] at h
  exact h

#print axioms polynomialResidual
#print axioms polynomialResidual_probe_zero
#print axioms polynomialResidual_variance_pair
#print axioms polynomialResidual_projection_zero
#print axioms polynomialResidual_dual_lower
#print axioms dualValue
#print axioms dualValue_lower

end YMGap.Continuum.BF4ExactSlabStarPolynomialResidual
