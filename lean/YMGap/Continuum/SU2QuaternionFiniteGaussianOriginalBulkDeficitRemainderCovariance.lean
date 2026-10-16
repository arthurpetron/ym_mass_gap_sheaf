/-
# The original bulk scalar remainder as a selected-action covariance

The local identity

  4*(1-r)^2 = 5 - 4*chi_1(r) + chi_2(r)

rewrites every scalar-square plaquette remainder as a literal physical
face-character factor.  An outer coefficient `1/4` restores the original
normalization.  The complete positively weighted bulk remainder is therefore
an actual finite scheduled source span, with no change of action, partition,
cutoff, or normalization.

For an arbitrary chronological offset, the normalized square around any
rational center then splits exactly into the covariance of that SAME selected
original action plus the square of the finite mean mismatch.  This exposes
the pairwise spatial-covariance consumer needed to replace the previous
cap-times-first-moment estimate.  No spatial summation, uniform smallness,
cutoff removal, continuum Hamiltonian, or Clay mass gap is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitLagControl
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
import YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (sourceProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary liftHead)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow (lift_cap_carrier)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabPhysicalFaceEdges)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem qmul {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

/-- Integer character coefficients of `4*(1-r)^2`. -/
def scalarSquareRemainderTerms : List (Nat × Q') :=
  [(0, 5), (1, -4), (2, 1)]

private def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- One physical scalar-square remainder at the specified chronological offset. -/
def scalarSquareRemainderSchedule (offset : Nat) (face : Z4Plaq) :
    List (Nat × List FaceFactor) :=
  [(offset, [(face, scalarSquareRemainderTerms)])]

/-- The complete weighted bulk scalar-square remainder schedule. -/
def originalBulkScalarSquareRemainderSchedule
    (s : Nat) (hs : 0 < s) (offset : Nat) :
    List (Q' × List (Nat × List FaceFactor)) :=
  (bulkSourceFaces s).map (fun face =>
    (quarter * bulkSourceCoefficient s hs face,
      scalarSquareRemainderSchedule offset face))

private theorem local_character_identity (scalar : RatPoly) :
    RatPolyCoeffEqv
      (finitePolySum
        (fun term : Nat × Q' => polySmul term.2 (characterPolynomial scalar term.1))
        scalarSquareRemainderTerms)
      (polySmul 4
        (polyMul (polyAdd polyOne (polyNeg scalar))
          (polyAdd polyOne (polyNeg scalar)))) := by
  let leftExpression : PolyExpr :=
    (.add
      (.const 5)
      (.add
        (.mul (.const (-4)) (.mul (.const 2) (.var 0)))
        (.add
          (.mul (.const 1)
            (.add
              (.mul (.mul (.const 2) (.var 0))
                (.mul (.const 2) (.var 0)))
              (.const (-1))))
          (.const 0))))
  let rightExpression : PolyExpr :=
    (.mul (.const 4)
      (.mul (.add (.const 1) (.neg (.var 0)))
        (.add (.const 1) (.neg (.var 0)))))
  let environment : Nat → RatPoly := fun _ => scalar
  have hring : RatPolyCoeffEqv
      (coeffEvalExpr environment leftExpression)
      (coeffEvalExpr environment rightExpression) :=
    coeffEvalExpr_eqv_of_normalize_eq leftExpression rightExpression
      (by decide) environment
  have hleft : RatPolyCoeffEqv
      (finitePolySum
        (fun term : Nat × Q' => polySmul term.2 (characterPolynomial scalar term.1))
        scalarSquareRemainderTerms)
      (coeffEvalExpr environment leftExpression) := by
    let twoScalar := polySmul 2 scalar
    let rawTwoScalar := polyMul (cap 2) scalar
    let spinTwo := polyAdd (polyMul twoScalar twoScalar) (polySmul (-1) polyOne)
    let rawSpinTwo := polyAdd
      (polyMul rawTwoScalar rawTwoScalar) (cap (-1))
    have htwo : RatPolyCoeffEqv twoScalar rawTwoScalar :=
      (cap_mul_left 2 scalar).symm
    have hspinTwo : RatPolyCoeffEqv spinTwo rawSpinTwo := by
      exact (htwo.mul htwo).add (RatPolyCoeffEqv.refl _)
    have hminusFour : RatPolyCoeffEqv
        (polySmul (-4) twoScalar)
        (polyMul (cap (-4)) rawTwoScalar) :=
      (cap_mul_left (-4) twoScalar).symm.trans
        ((RatPolyCoeffEqv.refl _).mul htwo)
    have honeSpin : RatPolyCoeffEqv
        (polySmul 1 spinTwo) (polyMul (cap 1) rawSpinTwo) :=
      (RatPolyCoeffEqv.one_smul spinTwo).trans
        ((hspinTwo.trans
          ((cap_mul_left 1 rawSpinTwo).trans
            (RatPolyCoeffEqv.one_smul rawSpinTwo)).symm))
    have hzero : RatPolyCoeffEqv polyZero (cap 0) :=
      (RatPolyCoeffEqv.zero_smul polyOne).symm
    change RatPolyCoeffEqv
      (polyAdd (polySmul 5 polyOne)
        (polyAdd (polySmul (-4) twoScalar)
          (polyAdd (polySmul 1 spinTwo) polyZero)))
      (polyAdd (cap 5)
        (polyAdd (polyMul (cap (-4)) rawTwoScalar)
          (polyAdd (polyMul (cap 1) rawSpinTwo) (cap 0))))
    exact (RatPolyCoeffEqv.refl _).add
      (hminusFour.add (honeSpin.add hzero))
  have hright : RatPolyCoeffEqv
      (coeffEvalExpr environment rightExpression)
      (polySmul 4
        (polyMul (polyAdd polyOne (polyNeg scalar))
          (polyAdd polyOne (polyNeg scalar)))) := by
    have hone : RatPolyCoeffEqv
        (polyAdd (cap 1) (polyNeg scalar))
        (polyAdd polyOne (polyNeg scalar)) :=
      (RatPolyCoeffEqv.one_smul polyOne).add (RatPolyCoeffEqv.refl _)
    change RatPolyCoeffEqv
      (polyMul (cap 4)
        (polyMul (polyAdd (cap 1) (polyNeg scalar))
          (polyAdd (cap 1) (polyNeg scalar)))) _
    exact ((RatPolyCoeffEqv.refl _).mul (hone.mul hone)).trans
      (cap_mul_left 4 _)
  exact hleft.trans (hring.trans hright)

/-- Exact local physical-character recoding of the scalar-square remainder. -/
theorem plaquetteScalarSquareRemainder_character
    (width : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (sourceProbe width [(face, scalarSquareRemainderTerms)])
      (polySmul 4 (plaquetteScalarSquareRemainder width face)) := by
  unfold sourceProbe product polynomialProduct factor
    plaquetteScalarSquareRemainder plaquetteScalarDeficit
  exact (local_character_identity (plaquette width face).scalar).mul_right polyOne |>.trans
    (RatPolyCoeffEqv.mul_one _)

private theorem single_source
    (width offset : Nat) (coefficient : Q') (face : Z4Plaq) :
    RatPolyCoeffEqv
      (polySmul (quarter * coefficient)
        (windowProbe width (scalarSquareRemainderSchedule offset face)))
      (polySmul coefficient
        (liftBoundary (offset * N width)
          (plaquetteScalarSquareRemainder width face))) := by
  have hlocal : RatPolyCoeffEqv
      (windowProbe width (scalarSquareRemainderSchedule offset face))
      (polySmul 4
        (liftBoundary (offset * N width)
          (plaquetteScalarSquareRemainder width face))) := by
    unfold scalarSquareRemainderSchedule windowProbe polynomialProduct
    have h := ((lift_coeff (offset * N width)
      (plaquetteScalarSquareRemainder_character width face)).mul_right polyOne).trans
      (RatPolyCoeffEqv.mul_one _)
    simpa only [lift_smul] using h
  exact (hlocal.smul (quarter * coefficient)).trans
    ((RatPolyCoeffEqv.smul_assoc (quarter * coefficient) 4 _).trans
      (RatPolyCoeffEqv.smul_coefficient
        (by
          have hquarter : quarter * 4 ≈ 1 := by
            unfold quarter
            decide
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ 4
              (Q'.mul_comm_eqv quarter coefficient))
            (Q'.eqv_trans _ _ _
              (Q'.mul_assoc_eqv coefficient quarter 4)
              (Q'.eqv_trans _ _ _
                (Q'.mul_eqv_congr_left coefficient _ _ hquarter)
                (Q'.mul_one_eqv coefficient)))) _))

private theorem sum_congr {A : Type} (f g : A → RatPoly) :
    (xs : List A) → (∀ a, a ∈ xs → RatPolyCoeffEqv (f a) (g a)) →
      RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => RatPolyCoeffEqv.refl _
  | a :: xs, h => (h a List.mem_cons_self).add
      (sum_congr f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem lift_zero : ∀ n : Nat, liftBoundary n polyZero = polyZero
  | 0 => rfl
  | n + 1 => by
      change liftHead (liftBoundary n polyZero) = polyZero
      rw [lift_zero n]
      rfl

private theorem lift_weighted_sum {A : Type}
    (n : Nat) (coefficient : A → Q') (polynomial : A → RatPoly) :
    ∀ xs : List A,
      liftBoundary n
          (finitePolySum (fun a => polySmul (coefficient a) (polynomial a)) xs) =
        finitePolySum
          (fun a => polySmul (coefficient a) (liftBoundary n (polynomial a))) xs
  | [] => lift_zero n
  | a :: xs => by
      simp only [finitePolySum, lift_add, lift_smul,
        lift_weighted_sum n coefficient polynomial xs]

/-- The complete source span is exactly the chronological lift of the already
defined global scalar-square remainder. -/
theorem originalBulkScalarSquareRemainderSchedule_source
    (s : Nat) (hs : 0 < s) (offset : Nat) :
    RatPolyCoeffEqv
      (sourceSpan (s * s)
        (originalBulkScalarSquareRemainderSchedule s hs offset))
      (liftBoundary (offset * N (s * s))
        (originalBulkScalarSquareRemainder s hs)) := by
  unfold sourceSpan originalBulkScalarSquareRemainderSchedule
    originalBulkScalarSquareRemainder
  rw [YMGap.Continuum.PolynomialWeightedSumBounds.sum_map,
    lift_weighted_sum]
  exact sum_congr _ _ (bulkSourceFaces s) (fun face _ =>
    single_source (s * s) offset (bulkSourceCoefficient s hs face) face)

theorem originalBulkScalarSquareRemainderSchedule_within
    (s : Nat) (hs : 0 < s) (offset : Nat) :
    ∀ x, x ∈ originalBulkScalarSquareRemainderSchedule s hs offset →
      ∀ e, e ∈ x.2 → e.1 ≤ offset := by
  intro x hx e he
  obtain ⟨face, _, rfl⟩ := List.mem_map.mp hx
  have h := List.mem_singleton.mp he
  subst e
  exact Nat.le_refl _

theorem originalBulkScalarSquareRemainderSchedule_faces
    (s : Nat) (hs : 0 < s) (offset : Nat) :
    ∀ x, x ∈ originalBulkScalarSquareRemainderSchedule s hs offset →
      ∀ e, e ∈ x.2 → ∀ factor, factor ∈ e.2 →
        factor.1 ∈ spatialFaces (s * s) := by
  intro x hx e he factor hfactor
  obtain ⟨face, hface, rfl⟩ := List.mem_map.mp hx
  have heq := List.mem_singleton.mp he
  subst e
  have hfactorEq := List.mem_singleton.mp hfactor
  subst factor
  exact bulkSourceFace_mem_spatialFaces_square hface

private theorem sourceSpan_unit (width : Nat) :
    RatPolyCoeffEqv (sourceSpan width [(1, [])]) polyOne := by
  unfold sourceSpan windowProbe sourceProbe product polynomialProduct finitePolySum
  exact ((RatPolyCoeffEqv.one_smul polyOne).add
    (RatPolyCoeffEqv.refl polyZero)).trans (RatPolyCoeffEqv.add_zero polyOne)

private theorem placedSpan_unit (extent start : Nat) :
    RatPolyCoeffEqv (placedSpan extent start [(1, [])]) polyOne := by
  unfold placedSpan placeWindowProbes sweptProduct product polynomialProduct finitePolySum
  exact ((RatPolyCoeffEqv.one_smul polyOne).add
    (RatPolyCoeffEqv.refl polyZero)).trans (RatPolyCoeffEqv.add_zero polyOne)

/-- Linear companion to the existing bilinear span pin, obtained by pairing
with the literal empty schedule. -/
theorem windowRatio_span_originalFiniteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start m L n extent : Nat}
    (hw : width ≤ extent) (ht : start + (m + (L + n)) ≤ extent)
    (xs : List (Q' × List (Nat × List FaceFactor)))
    (hxwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ L)
    (hxfaces : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 →
      ∀ factor, factor ∈ e.2 → factor.1 ∈ spatialFaces width)
    (stage : Nat) :
    windowRatio hw0 hw1 (headCutoff w + stage) width
        (Nat.le_add_right _ _) m L n (sourceSpan width xs) ≈
      finiteValue w hw0 hw1 extent
        (YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds
          extent width start (m + (L + n)))
        (fun _ hi =>
          YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds_physical hi)
        (placedSpan extent (start + m) xs) stage := by
  have h := windowRatio_span_mul_originalFiniteValue hw0 hw1 hw ht
    xs [(1, [])] hxwithin hxfaces
    (fun x hx => by cases hx with | head => intro e he; cases he | tail _ hx => cases hx)
    (fun x hx => by cases hx with | head => intro e he; cases he | tail _ hx => cases hx)
    stage
  have hsourceOne : RatPolyCoeffEqv
      (polyMul (sourceSpan width xs) (sourceSpan width [(1, [])]))
      (sourceSpan width xs) :=
    ((RatPolyCoeffEqv.refl _).mul (sourceSpan_unit width)).trans
      (RatPolyCoeffEqv.mul_one _)
  have hplacedOne : RatPolyCoeffEqv
      (polyMul (placedSpan extent (start + m) xs)
        (placedSpan extent (start + m) [(1, [])]))
      (placedSpan extent (start + m) xs) :=
    ((RatPolyCoeffEqv.refl _).mul (placedSpan_unit extent (start + m))).trans
      (RatPolyCoeffEqv.mul_one _)
  exact Q'.eqv_trans _ _ _
    (windowRatio_congr hw0 hw1 (headCutoff w + stage) width
      (Nat.le_add_right _ _) m L n hsourceOne.symm)
    (Q'.eqv_trans _ _ _ h
      (YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance.finiteValue_coeff_congr
        w hw0 hw1 extent
        (YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds
          extent width start (m + (L + n)))
        (fun _ hi =>
          YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds_physical hi)
        _ _ hplacedOne stage))

private theorem shifted_square_window_identity {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (polynomial : RatPoly) (center : Q') :
    windowRatio hw0 hw1 K width hK m L n
        (polyMul (shifted polynomial center) (shifted polynomial center)) ≈
      (windowRatio hw0 hw1 K width hK m L n (polyMul polynomial polynomial) +
        -(windowRatio hw0 hw1 K width hK m L n polynomial *
          windowRatio hw0 hw1 K width hK m L n polynomial)) +
      ((windowRatio hw0 hw1 K width hK m L n polynomial + -center) *
        (windowRatio hw0 hw1 K width hK m L n polynomial + -center)) := by
  let F := windowRatio hw0 hw1 K width hK m L n
  have addL (a b c : RatPoly) : F (polyMul (polyAdd a b) c) ≈
      F (polyMul a c) + F (polyMul b c) := by
    rw [polyMul_add_left_exact]
    exact windowRatio_add hw0 hw1 K width hK m L n _ _
  have addR (a b c : RatPoly) : F (polyMul a (polyAdd b c)) ≈
      F (polyMul a b) + F (polyMul a c) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK m L n
        (RatPolyCoeffEqv.mul_add_right a b c))
      (windowRatio_add hw0 hw1 K width hK m L n _ _)
  have scaleL (c : Q') (a b : RatPoly) : F (polyMul (polySmul c a) b) ≈
      c * F (polyMul a b) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK m L n
        (RatPolyCoeffEqv.polyMul_smul_left c a b))
      (windowRatio_smul hw0 hw1 K width hK m L n c _)
  have scaleR (c : Q') (a b : RatPoly) : F (polyMul a (polySmul c b)) ≈
      c * F (polyMul a b) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK m L n
        (RatPolyCoeffEqv.polyMul_smul_right c a b))
      (windowRatio_smul hw0 hw1 K width hK m L n c _)
  have right (a : RatPoly) : F (polyMul a (shifted polynomial center)) ≈
      1 * F (polyMul a polynomial) + (-center) * F (polyMul a polyOne) :=
    Q'.eqv_trans _ _ _ (addR a _ _)
      (Q'.add_eqv_congr' (scaleR 1 a polynomial)
        (scaleR (-center) a polyOne))
  have hpOne : F (polyMul polynomial polyOne) ≈ F polynomial :=
    windowRatio_congr hw0 hw1 K width hK m L n
      (RatPolyCoeffEqv.mul_one polynomial)
  have honeP : F (polyMul polyOne polynomial) ≈ F polynomial :=
    windowRatio_congr hw0 hw1 K width hK m L n
      (RatPolyCoeffEqv.one_mul polynomial)
  have honeOne : F (polyMul polyOne polyOne) ≈ 1 :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK m L n
        (RatPolyCoeffEqv.mul_one polyOne))
      (windowRatio_one hw0 hw1 K width hK m L n)
  have he : F (polyMul (shifted polynomial center) (shifted polynomial center)) ≈
      1 * (1 * F (polyMul polynomial polynomial) + (-center) * F polynomial) +
        (-center) * (1 * F polynomial + (-center) * 1) :=
    Q'.eqv_trans _ _ _ (addL _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (scaleL 1 polynomial _)
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_trans _ _ _ (right polynomial)
              (Q'.add_eqv_congr' (Q'.eqv_refl _)
                (Q'.mul_eqv_congr_left _ _ _ hpOne)))))
        (Q'.eqv_trans _ _ _ (scaleL (-center) polyOne _)
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_trans _ _ _ (right polyOne)
              (Q'.add_eqv_congr'
                (Q'.mul_eqv_congr_left _ _ _ honeP)
                (Q'.mul_eqv_congr_left _ _ _ honeOne))))))
  exact Q'.eqv_trans _ _ _ he
    (poly_identity_of_normal_eq
      (.add
        (.mul (.const 1)
          (.add (.mul (.const 1) (.var 0))
            (.mul (.neg (.var 2)) (.var 1))))
        (.mul (.neg (.var 2))
          (.add (.mul (.const 1) (.var 1))
            (.mul (.neg (.var 2)) (.const 1)))))
      (.add
        (.add (.var 0) (.neg (.mul (.var 1) (.var 1))))
        (.mul (.add (.var 1) (.neg (.var 2)))
          (.add (.var 1) (.neg (.var 2)))))
      (by decide)
      (fun index =>
        if index = 0 then F (polyMul polynomial polynomial)
        else if index = 1 then F polynomial
        else center))

/-- Canonical ambient slab large enough for the complete finite window. -/
def originalBulkScalarSquareRemainderExtent (s n L : Nat) : Nat :=
  s * s + (n + (L + n))

/-- The unchanged selected original action in the canonical ambient slab. -/
def originalBulkScalarSquareRemainderIds (s n L : Nat) : List Nat :=
  YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds
    (originalBulkScalarSquareRemainderExtent s n L) (s * s) 0 (n + (L + n))

theorem originalBulkScalarSquareRemainderIds_physical (s n L : Nat) :
    ∀ id, id ∈ originalBulkScalarSquareRemainderIds s n L →
      id ∈ slabPhysicalFaceEdges (originalBulkScalarSquareRemainderExtent s n L) := by
  intro id hid
  exact YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds_physical hid

/-- The literal placed bulk remainder in the canonical ambient slab. -/
def originalBulkScalarSquareRemainderPlaced
    (s : Nat) (hs : 0 < s) (n offset L : Nat) : RatPoly :=
  placedSpan (originalBulkScalarSquareRemainderExtent s n L) n
    (originalBulkScalarSquareRemainderSchedule s hs offset)

/-- The finite mean under the SAME selected action used by the covariance. -/
def originalBulkScalarSquareRemainderSelectedMean {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat) : Q' :=
  finiteValue w hw0 hw1 (originalBulkScalarSquareRemainderExtent s n L)
    (originalBulkScalarSquareRemainderIds s n L)
    (originalBulkScalarSquareRemainderIds_physical s n L)
    (originalBulkScalarSquareRemainderPlaced s hs n offset L) stage

/-- The finite covariance under the SAME selected action and normalization. -/
def originalBulkScalarSquareRemainderSelectedCovariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat) : Q' :=
  finiteCovariance w hw0 hw1
    (originalBulkScalarSquareRemainderExtent s n L)
    (originalBulkScalarSquareRemainderIds s n L)
    (originalBulkScalarSquareRemainderIds_physical s n L)
    (originalBulkScalarSquareRemainderPlaced s hs n offset L)
    (originalBulkScalarSquareRemainderPlaced s hs n offset L) stage

/-- Exact finite diagonal split for the scalar-square remainder at any
chronological offset.  The first term is the covariance of the SAME selected
original action; the second is only the finite mean mismatch. -/
theorem originalBulkScalarSquareRemainder_diagonal_covariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat)
    (hoffset : offset ≤ L) (center : Q') :
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul
          (shifted (liftBoundary (offset * N (s * s))
            (originalBulkScalarSquareRemainder s hs)) center)
          (shifted (liftBoundary (offset * N (s * s))
            (originalBulkScalarSquareRemainder s hs)) center)) ≈
      originalBulkScalarSquareRemainderSelectedCovariance
          hw0 hw1 s hs stage n L offset +
        ((originalBulkScalarSquareRemainderSelectedMean
            hw0 hw1 s hs stage n L offset + -center) *
          (originalBulkScalarSquareRemainderSelectedMean
            hw0 hw1 s hs stage n L offset + -center)) := by
  let extent := originalBulkScalarSquareRemainderExtent s n L
  let schedule := originalBulkScalarSquareRemainderSchedule s hs offset
  let source := sourceSpan (s * s) schedule
  let placed := originalBulkScalarSquareRemainderPlaced s hs n offset L
  let ids := originalBulkScalarSquareRemainderIds s n L
  let hids := originalBulkScalarSquareRemainderIds_physical s n L
  have hsource := originalBulkScalarSquareRemainderSchedule_source s hs offset
  have hwithin : ∀ x, x ∈ schedule → ∀ e, e ∈ x.2 → e.1 ≤ L := by
    intro x hx e he
    exact Nat.le_trans
      (originalBulkScalarSquareRemainderSchedule_within s hs offset x hx e he)
      hoffset
  have hfaces : ∀ x, x ∈ schedule → ∀ e, e ∈ x.2 →
      ∀ factor, factor ∈ e.2 → factor.1 ∈ spatialFaces (s * s) :=
    originalBulkScalarSquareRemainderSchedule_faces s hs offset
  have hwidth : s * s ≤ extent := by
    unfold extent originalBulkScalarSquareRemainderExtent
    omega
  have htime : 0 + (n + (L + n)) ≤ extent := by
    unfold extent originalBulkScalarSquareRemainderExtent
    omega
  have hmeanRaw := windowRatio_span_originalFiniteValue hw0 hw1 hwidth htime
    schedule hwithin hfaces stage
  have hmean : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n source ≈
      finiteValue w hw0 hw1 extent ids hids placed stage := by
    simpa only [Nat.zero_add, source, placed, ids, extent,
      originalBulkScalarSquareRemainderPlaced,
      originalBulkScalarSquareRemainderIds] using hmeanRaw
  have hsquareRaw := windowRatio_span_mul_originalFiniteValue hw0 hw1
    hwidth htime schedule schedule hwithin hfaces hwithin hfaces stage
  have hsquare : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (polyMul source source) ≈
      finiteValue w hw0 hw1 extent ids hids (polyMul placed placed) stage := by
    simpa only [Nat.zero_add, source, placed, ids, extent,
      originalBulkScalarSquareRemainderPlaced,
      originalBulkScalarSquareRemainderIds] using hsquareRaw
  have hsourceShift : RatPolyCoeffEqv
      (shifted (liftBoundary (offset * N (s * s))
        (originalBulkScalarSquareRemainder s hs)) center)
      (shifted source center) := by
    unfold shifted
    exact (hsource.symm.smul 1).add (RatPolyCoeffEqv.refl _)
  have hleft := shifted_square_window_identity hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L n source center
  have hreplace : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul
        (shifted (liftBoundary (offset * N (s * s))
          (originalBulkScalarSquareRemainder s hs)) center)
        (shifted (liftBoundary (offset * N (s * s))
          (originalBulkScalarSquareRemainder s hs)) center)) ≈
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (shifted source center) (shifted source center)) :=
    windowRatio_congr hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (hsourceShift.mul hsourceShift)
  have hmeanSelected : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n source ≈
      originalBulkScalarSquareRemainderSelectedMean
        hw0 hw1 s hs stage n L offset := by
    simpa only [originalBulkScalarSquareRemainderSelectedMean,
      originalBulkScalarSquareRemainderPlaced,
      originalBulkScalarSquareRemainderIds,
      originalBulkScalarSquareRemainderExtent, source, extent, placed, ids]
      using hmean
  have hcovarianceSelected :
      (windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n (polyMul source source) +
        -(windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
            (Nat.le_add_right _ _) n L n source *
          windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
            (Nat.le_add_right _ _) n L n source)) ≈
      originalBulkScalarSquareRemainderSelectedCovariance
        hw0 hw1 s hs stage n L offset := by
    unfold originalBulkScalarSquareRemainderSelectedCovariance finiteCovariance
    exact Q'.add_eqv_congr' hsquare
      (Q'.neg_eqv_congr _ _ (qmul hmean hmean))
  exact Q'.eqv_trans _ _ _ hreplace
    (Q'.eqv_trans _ _ _ hleft
      (Q'.add_eqv_congr'
        hcovarianceSelected
        (qmul
          (Q'.add_eqv_congr_right _ _ (-center) hmeanSelected)
          (Q'.add_eqv_congr_right _ _ (-center) hmeanSelected))))

/-- The literal lower diagonal used by the remainder Cauchy bounds is now a
SAME-selected covariance plus only its finite OWN-center mismatch. -/
theorem originalBulkScalarSquareRemainder_leftDiagonal_covariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainder s hs
    let center := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (shifted remainder center) (shifted remainder center)) ≈
      originalBulkScalarSquareRemainderSelectedCovariance
          hw0 hw1 s hs stage n L 0 +
        ((originalBulkScalarSquareRemainderSelectedMean
            hw0 hw1 s hs stage n L 0 + -center) *
          (originalBulkScalarSquareRemainderSelectedMean
            hw0 hw1 s hs stage n L 0 + -center)) := by
  dsimp only
  simpa only [Nat.zero_mul, liftBoundary] using
    (originalBulkScalarSquareRemainder_diagonal_covariance
      hw0 hw1 s hs stage n L 0 (Nat.zero_le _)
      (originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n))

/-- The literal chronologically lifted upper diagonal has the matching
selected-action split, with the same center and the probe placed at offset
`L`. -/
theorem originalBulkScalarSquareRemainder_rightDiagonal_covariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainder s hs
    let center := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
    let lifted := liftBoundary (L * N (s * s)) (shifted remainder center)
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul lifted lifted) ≈
      originalBulkScalarSquareRemainderSelectedCovariance
          hw0 hw1 s hs stage n L L +
        ((originalBulkScalarSquareRemainderSelectedMean
            hw0 hw1 s hs stage n L L + -center) *
          (originalBulkScalarSquareRemainderSelectedMean
            hw0 hw1 s hs stage n L L + -center)) := by
  dsimp only
  let blocks := N (s * s)
  let shift := L * blocks
  let remainder := originalBulkScalarSquareRemainder s hs
  let center := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
  have hsize : (L + 1) * blocks = blocks + shift := by
    unfold shift
    rw [Nat.succ_mul]
    omega
  have hshift : HaarCarrierEqv ((L + 1) * blocks)
      (liftBoundary shift (shifted remainder center))
      (shifted (liftBoundary shift remainder) center) := by
    unfold shifted
    rw [lift_add, lift_smul]
    exact HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (by
        rw [hsize]
        simpa only [cap, lift_smul] using
          (lift_cap_carrier blocks shift (-center)))
  have hcongr : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul (liftBoundary shift (shifted remainder center))
        (liftBoundary shift (shifted remainder center))) ≈
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (shifted (liftBoundary shift remainder) center)
          (shifted (liftBoundary shift remainder) center)) :=
    windowRatio_carrier_congr hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (HaarCarrierEqv.mul hshift hshift)
  exact Q'.eqv_trans _ _ _ hcongr
    (originalBulkScalarSquareRemainder_diagonal_covariance
      hw0 hw1 s hs stage n L L (Nat.le_refl _) center)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance.plaquetteScalarSquareRemainder_character
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance.originalBulkScalarSquareRemainderSchedule_source
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance.windowRatio_span_originalFiniteValue
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance.originalBulkScalarSquareRemainder_diagonal_covariance
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance.originalBulkScalarSquareRemainder_leftDiagonal_covariance
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance.originalBulkScalarSquareRemainder_rightDiagonal_covariance
