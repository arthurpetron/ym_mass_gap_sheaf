/-
# Polynomial kernel tests approximate the ACTUAL completed residual

For the original reciprocal iteration a_n, use the genuine polynomial
kernel test t(J(a_n)*p). Its distance to (I-C_i)p is bounded by the original
norm of J(1-D*a_n)*p, hence by q^(2n) times the original squared norm of p.
All action factors are retained. This is density with an explicit modulus
at fixed nome, not a useful global centered coercivity estimate.
-/

import YMGap.Continuum.BF4ExactSlabStarCertifiedApproximation
import YMGap.Continuum.BF4ExactSlabStarExteriorSeedNorm

namespace YMGap.Continuum.BF4ExactSlabStarResidualApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabStarPolynomialResidual
open YMGap.Continuum.BF4ExactSlabStarExteriorResidual
open YMGap.Continuum.BF4ExactSlabStarExteriorSeedNorm
open YMGap.Continuum.BF4ExactSlabStarCertifiedApproximation
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) := (boundaryCompleteSlabLinks extent).length

/-- Explicit unpadded exterior unit, with its support witness. -/
def unitExterior (extent : Nat) : {p : RatPoly // SupportedQuaternionBlocks (blocks extent-1) p} :=
  ⟨polyOne, supported_one (blocks extent-1)⟩

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem rat_mono {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) :=
  leEv_ofQ'_of_approx_ge (fun _ => h)

private theorem embed_pair (D : GNSData) (a b : D.V) :
    D.cinnerCompl (embedV D a) (embedV D b) = rat (D.B a b) := D.cinnerCompl_embed a b

private theorem embed_congr (D : GNSData) {a b : D.V} (h : D.veq a b) :
    embedV D a = embedV D b := by
  apply eq_of_dense_pairings
  intro c
  rw [embed_pair, embed_pair]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => D.B_congr_left c h))

private theorem embed_sub (D : GNSData) (a b : D.V) :
    embedV D (D.sub a b) = D.cSub (embedV D a) (embedV D b) := by
  apply eq_of_dense_pairings
  intro c
  rw [D.cinnerCompl_cSub_left, embed_pair, embed_pair, embed_pair]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _ (D.B_add_left a (D.neg b) c)
      (Q'.add_eqv_congr_left _ _ _ (D.B_neg_left b c))))

private theorem cSub_zero (D : GNSData) (x : GNSCompletionSpace D) :
    D.cSub x (embedV D D.zero) = x := by
  apply eq_of_pairings_equal
  intro z
  rw [D.cinnerCompl_cSub_left, D.cinnerCompl_embedZero_left]
  generalize D.cinnerCompl x z = b
  refine Quotient.inductionOn b ?_
  intro B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : (-0 : Q') ≈ 0))
      (Q'.eqv_of_eq (Q'.add_zero' (B.approx n)))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "N" => numeratorMap hw0 hw1 K extent hK i.val i.property
local notation "M" => normalizerMap hw0 hw1 K extent hK i.val i.property
local notation "A" => approximateInverse hw0 hw1 K extent hK i.val i.property
local notation "P" => projections hw0 hw1 K extent hK
local notation "E" => exteriorSeed hw0 hw1 K extent hK i
local notation "t" => polynomialResidual hw0 hw1 K extent hK i
local notation "one" => unitExterior extent

private theorem exterior_sub (a b : (G).V) (p : (F).V) :
    embedV F (E ((G).sub a b) p) =
      (F).cSub (embedV F (E a p)) (embedV F (E b p)) := by
  have he : (F).veq (E ((G).sub a b) p) ((F).sub (E a p) (E b p)) := by
    have hJ := probeMap_sub hw0 hw1 K extent hK i.val i.property a b
    refine (hJ.mul_right p.val).trans ?_
    change RatPolyCoeffEqv (polyMul (polyAdd (J a).val (polySmul (-1) (J b).val)) p.val) _
    rw [polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_left _ _ _)
  exact (embed_congr F he).trans (embed_sub F _ _)

private theorem test_split (a : (G).V) (p : (F).V) :
    let an : (G).V := ⟨polyMul a.val (N p).val, supported_polyMul a.property (N p).property⟩
    embedV F (t (E a p)) = (F).cSub (embedV F (E (M a) p)) (embedV F (J an)) := by
  dsimp only
  let d : (G).V := ⟨normalizer w K extent i.val i.property,
    normalizer_supported w K extent i.val i.property⟩
  let an : (G).V := ⟨polyMul a.val (N p).val, supported_polyMul a.property (N p).property⟩
  have hJd : (J (M a)).val = polyMul (J a).val (J d).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) a.val d.val
  have hJn : (J an).val = polyMul (J a).val (J (N p)).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) a.val (N p).val
  have he : (F).veq (E a (t p)) ((F).sub (E (M a) p) (J an)) := by
    change RatPolyCoeffEqv
      (polyMul (J a).val
        (polyAdd (polyMul (J d).val p.val) (polySmul (-1) (J (N p)).val)))
      (polyAdd (polyMul (J (M a)).val p.val) (polySmul (-1) (J an).val))
    rw [hJd, hJn]
    exact (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul_assoc _ _ _).symm
        (RatPolyCoeffEqv.polyMul_smul_right _ _ _))
  exact (polynomialResidual_exteriorSeed_completed hw0 hw1 K extent hK i a p).trans
    ((embed_congr F he).trans (embed_sub F _ _))

/-- Exact original completed error identity for ANY exterior approximant.
The projection removes the exterior numerator term, not an absolute-value
estimate or a discarded action factor. -/
theorem residual_error_identity (a : (G).V) (p : (F).V) :
    (F).cSub ((P).residual i (embedV F p)) (embedV F (t (E a p))) =
      (P).residual i (embedV F (E ((G).sub one (M a)) p)) := by
  let an : (G).V := ⟨polyMul a.val (N p).val, supported_polyMul a.property (N p).property⟩
  have hy : (P).residual i (embedV F (t (E a p))) = embedV F (t (E a p)) := by
    unfold Family.residual
    rw [polynomialResidual_projection_zero, cSub_zero]
  have hj : (P).op i (embedV F (J an)) = embedV F (J an) := by
    change conditionalProjection hw0 hw1 K extent hK i.val i.property
      (embedV F (J an)) = embedV F (J an)
    rw [← probeCompletion_embed]
    exact conditionalProjection_fix_exterior hw0 hw1 K extent hK i.val i.property _
  have hrj : (P).residual i (embedV F (J an)) = embedV F (F).zero := by
    rw [← hj]
    exact (P).residual_after_own i _
  have hrm : (P).residual i (embedV F (E (M a) p)) = embedV F (t (E a p)) := by
    have he := congrArg ((P).residual i) (test_split hw0 hw1 K extent hK i a p)
    rw [hy, (P).residual_sub, hrj, cSub_zero] at he
    exact he.symm
  have hu : embedV F (E one p) = embedV F p :=
    exteriorSeed_one_completed hw0 hw1 K extent hK i p
  rw [exterior_sub, hu, (P).residual_sub, hrm]

/-- The actual reciprocal approximant is already a supported exterior
polynomial. It is independent of the polynomial whose residual is tested. -/
def reciprocalApproximation (n : Nat) : (G).V := A one n

/-- Original supported seed whose genuine kernel test approximates the
original conditional residual. -/
def approximationSeed (p : (F).V) (n : Nat) : (F).V :=
  E (reciprocalApproximation hw0 hw1 K extent hK i n) p

set_option maxHeartbeats 2000000 in
/-- Actual completed distance bound, with prefactor the original norm and
without a coarse normalizer comparison multiplying that prefactor. -/
theorem residual_approximation_norm (p : (F).V) (n : Nat) :
    RCle (normSq ((F).cSub ((P).residual i (embedV F p))
      (embedV F (t (approximationSeed hw0 hw1 K extent hK i p n)))))
      (rat ((inverseRate w * inverseRate w)^n * (F).B p p)) := by
  let a := reciprocalApproximation hw0 hw1 K extent hK i n
  let e := (G).sub one (M a)
  have hc := certified_residual_norm hw0 hw1 K extent hK i.val i.property
    (tailSquare_certificate hw0 hw1 K extent hK i p) one n
  change weightedPair (blocks extent-1)
      (polyMul (insertedNormalizer w K extent i.val i.property (polyMul p.val p.val))
        (exterior w K extent i.val i.property)) e.val e.val ≤
    (inverseRate w * inverseRate w)^n * weightedPair (blocks extent-1)
      (polyMul (insertedNormalizer w K extent i.val i.property (polyMul p.val p.val))
        (exterior w K extent i.val i.property)) polyOne polyOne at hc
  have hb : (F).B (E e p) (E e p) ≤
      (inverseRate w * inverseRate w)^n * (F).B p p := by
    have he := exteriorSeed_norm_pin hw0 hw1 K extent hK i e p
    have hW := original_norm_pin hw0 hw1 K extent hK i p
    have heq :
        quaternionHaar (blocks extent-1)
          (polyMul (polyMul (polyMul e.val e.val)
            (insertedNormalizer w K extent i.val i.property (polyMul p.val p.val)))
            (exterior w K extent i.val i.property)) ≈
        weightedPair (blocks extent-1)
          (polyMul (insertedNormalizer w K extent i.val i.property (polyMul p.val p.val))
            (exterior w K extent i.val i.property)) e.val e.val :=
      haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)
    have hunit :
        weightedPair (blocks extent-1)
          (polyMul (insertedNormalizer w K extent i.val i.property (polyMul p.val p.val))
            (exterior w K extent i.val i.property)) polyOne polyOne ≈ (F).B p p :=
      Q'.eqv_trans _ _ _
        (haar_of_coeff (((RatPolyCoeffEqv.one_mul polyOne).mul_right _).trans
          (RatPolyCoeffEqv.one_mul _))) (Q'.eqv_symm hW)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ he heq))
      (Q'.le_trans' _ _ _ hc (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hunit)))
  change RCle (normSq ((F).cSub ((P).residual i (embedV F p))
    (embedV F (t (E a p))))) _
  rw [residual_error_identity]
  exact RCle_trans ((P).residual_norm i (embedV F (E e p)))
    (by rw [normSq, embed_pair]; exact rat_mono hb)

/-- An explicit iteration count for squared distance to the existing
completed conditional residual; zero original norm is allowed. -/
def residualCutoff (p : (F).V) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff
    (inverseRate w * inverseRate w) ((F).B p p) epsilon

theorem residual_approximation_error_le (p : (F).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : residualCutoff hw0 hw1 K extent hK p epsilon ≤ n) :
    RCle (normSq ((F).cSub ((P).residual i (embedV F p))
      (embedV F (t (approximationSeed hw0 hw1 K extent hK i p n))))) (rat epsilon) := by
  have hq := inverseRate_bounds hw0 hw1
  have hq2 : inverseRate w * inverseRate w < (1 : Q') :=
    Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hq.2) hq.1)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))) hq.2
  exact RCle_trans (residual_approximation_norm hw0 hw1 K extent hK i p n)
    (rat_mono (PositiveContractionResidual.geometric_bound
      (Q'.mul_nonneg _ _ hq.1 hq.1) hq2 ((F).self_nonneg p) hepsilon n hn))

/-- Relative-error iteration count, independent of volume, heat cutoff,
link placement and the input polynomial. The nome dependence is explicit. -/
def relativeCutoff (w epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff
    (inverseRate w * inverseRate w) 1 epsilon

/-- Uniform relative approximation at fixed nome. This estimates the error
of a polynomial approximation to R_i p, not the size of R_i p itself. -/
theorem residual_relative_error_le (p : (F).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : relativeCutoff w epsilon ≤ n) :
    RCle (normSq ((F).cSub ((P).residual i (embedV F p))
      (embedV F (t (approximationSeed hw0 hw1 K extent hK i p n)))))
      (rat (epsilon * (F).B p p)) := by
  have hq := inverseRate_bounds hw0 hw1
  have hq2 : inverseRate w * inverseRate w < (1 : Q') :=
    Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hq.2) hq.1)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))) hq.2
  have hp : (inverseRate w * inverseRate w)^n ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (PositiveContractionResidual.geometric_bound
        (Q'.mul_nonneg _ _ hq.1 hq.1) hq2 (by decide : (0 : Q') ≤ 1) hepsilon n hn)
  exact RCle_trans (residual_approximation_norm hw0 hw1 K extent hK i p n)
    (rat_mono (Q'.mul_le_mul_of_nonneg_right _ _ _ hp ((F).self_nonneg p)))

#print axioms unitExterior
#print axioms residual_error_identity
#print axioms reciprocalApproximation
#print axioms approximationSeed
#print axioms residual_approximation_norm
#print axioms residualCutoff
#print axioms residual_approximation_error_le
#print axioms relativeCutoff
#print axioms residual_relative_error_le

end YMGap.Continuum.BF4ExactSlabStarResidualApproximation
