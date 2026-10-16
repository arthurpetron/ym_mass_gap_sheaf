/-
# The original bulk vector jet as a selected physical-character source

The unit-quaternion identity

  4 * (i^2 + j^2 + k^2) = 3 - chi_2(r)

rewrites the vector-coordinate quadratic jet as one bounded physical
plaquette-character factor.  With the literal outer quarter coefficient, the
complete weighted jet is therefore a finite scheduled source span under the
same ORIGINAL action.  This is the exact recoding needed before applying the
selected spatial-covariance estimates.

No ORIGINAL-to-FREE law comparison, covariance sum, neighboring sign, cutoff
removal, continuum Hamiltonian, or Clay mass gap is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
import YMGap.Continuum.SU2QuaternionHaarCertificateLift

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance

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
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
  (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (carrier_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_carrier)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary liftHead)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow (lift_cap_carrier)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabPhysicalFaceEdges)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- Integer character coefficients of `4*(i^2+j^2+k^2)`. -/
def vectorQuadraticJetTerms : List (Nat × Q') :=
  [(0, 3), (2, -1)]

private def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- One physical vector-jet factor at the specified chronological offset. -/
def vectorQuadraticJetSchedule (offset : Nat) (face : Z4Plaq) :
    List (Nat × List FaceFactor) :=
  [(offset, [(face, vectorQuadraticJetTerms)])]

/-- The complete positively weighted bulk vector-jet schedule. -/
def originalBulkVectorQuadraticJetSchedule
    (s : Nat) (hs : 0 < s) (offset : Nat) :
    List (Q' × List (Nat × List FaceFactor)) :=
  (bulkSourceFaces s).map (fun face =>
    (quarter * bulkSourceCoefficient s hs face,
      vectorQuadraticJetSchedule offset face))

private theorem local_character_identity (scalar : RatPoly) :
    RatPolyCoeffEqv
      (finitePolySum
        (fun term : Nat × Q' =>
          polySmul term.2 (characterPolynomial scalar term.1))
        vectorQuadraticJetTerms)
      (polySmul 4
        (polyAdd polyOne (polyNeg (polyMul scalar scalar)))) := by
  let leftExpression : PolyExpr :=
    (.add
      (.const 3)
      (.add
        (.mul (.const (-1))
          (.add
            (.mul (.mul (.const 2) (.var 0))
              (.mul (.const 2) (.var 0)))
            (.const (-1))))
        (.const 0)))
  let rightExpression : PolyExpr :=
    (.mul (.const 4)
      (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))))
  let environment : Nat → RatPoly := fun _ => scalar
  have hring : RatPolyCoeffEqv
      (coeffEvalExpr environment leftExpression)
      (coeffEvalExpr environment rightExpression) :=
    coeffEvalExpr_eqv_of_normalize_eq leftExpression rightExpression
      (by decide) environment
  have hleft : RatPolyCoeffEqv
      (finitePolySum
        (fun term : Nat × Q' =>
          polySmul term.2 (characterPolynomial scalar term.1))
        vectorQuadraticJetTerms)
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
    have hminusOne : RatPolyCoeffEqv
        (polySmul (-1) spinTwo)
        (polyMul (cap (-1)) rawSpinTwo) :=
      (cap_mul_left (-1) spinTwo).symm.trans
        ((RatPolyCoeffEqv.refl _).mul hspinTwo)
    have hzero : RatPolyCoeffEqv polyZero (cap 0) :=
      (RatPolyCoeffEqv.zero_smul polyOne).symm
    change RatPolyCoeffEqv
      (polyAdd (polySmul 3 polyOne)
        (polyAdd (polySmul (-1) spinTwo) polyZero))
      (polyAdd (cap 3)
        (polyAdd (polyMul (cap (-1)) rawSpinTwo) (cap 0)))
    exact (RatPolyCoeffEqv.refl _).add (hminusOne.add hzero)
  have hright : RatPolyCoeffEqv
      (coeffEvalExpr environment rightExpression)
      (polySmul 4
        (polyAdd polyOne (polyNeg (polyMul scalar scalar)))) := by
    have hone : RatPolyCoeffEqv (cap 1) polyOne :=
      RatPolyCoeffEqv.one_smul polyOne
    change RatPolyCoeffEqv
      (polyMul (cap 4)
        (polyAdd (cap 1) (polyNeg (polyMul scalar scalar)))) _
    exact ((RatPolyCoeffEqv.refl _).mul
      (hone.add (RatPolyCoeffEqv.refl _))).trans
        (cap_mul_left 4 _)
  exact hleft.trans (hring.trans hright)

private theorem scalar_proxy_vector_jet
    (width : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (N width)
      (polyAdd polyOne
        (polyNeg (polyMul (plaquette width face).scalar
          (plaquette width face).scalar)))
      (plaquetteVectorQuadraticJet width face) := by
  let q := plaquette width face
  let scalarSquare := polyMul q.scalar q.scalar
  have hreplace : HaarCarrierEqv (N width)
      (polyAdd polyOne (polyNeg scalarSquare))
      (polyAdd (polyQuaternionNorm q) (polyNeg scalarSquare)) :=
    HaarCarrierEqv.add
      (plaquette_unit width (N width) (Nat.le_refl _) face).symm
      (HaarCarrierEqv.refl _ _)
  have hcancel : RatPolyCoeffEqv
      (polyAdd (polyQuaternionNorm q) (polyNeg scalarSquare))
      (plaquetteVectorQuadraticJet width face) := by
    unfold polyQuaternionNorm plaquetteVectorQuadraticJet scalarSquare q
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.mul (.var 0) (.var 0))
          (.add (.mul (.var 1) (.var 1))
            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
        (.neg (.mul (.var 0) (.var 0))))
      (.add (.mul (.var 1) (.var 1))
        (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))
      (by decide)
      (fun
        | 0 => (plaquette width face).scalar
        | 1 => (plaquette width face).iPart
        | 2 => (plaquette width face).jPart
        | _ => (plaquette width face).kPart)
  exact hreplace.trans (RatPolyCoeffEqv.haarCarrier hcancel)

/-- On the same unit-quaternion carrier, the complement of the vector jet is
the scalar-coordinate square. -/
theorem plaquetteVectorQuadraticJet_complement
    (width : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (N width)
      (polyAdd polyOne
        (polyNeg (plaquetteVectorQuadraticJet width face)))
      (polyMul (plaquette width face).scalar
        (plaquette width face).scalar) := by
  let q := plaquette width face
  let jet := plaquetteVectorQuadraticJet width face
  have hreplace : HaarCarrierEqv (N width)
      (polyAdd polyOne (polyNeg jet))
      (polyAdd (polyQuaternionNorm q) (polyNeg jet)) :=
    HaarCarrierEqv.add
      (plaquette_unit width (N width) (Nat.le_refl _) face).symm
      (HaarCarrierEqv.refl _ _)
  have hcancel : RatPolyCoeffEqv
      (polyAdd (polyQuaternionNorm q) (polyNeg jet))
      (polyMul q.scalar q.scalar) := by
    dsimp only [jet, q]
    unfold polyQuaternionNorm plaquetteVectorQuadraticJet
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.mul (.var 0) (.var 0))
          (.add (.mul (.var 1) (.var 1))
            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
        (.neg
          (.add (.mul (.var 1) (.var 1))
            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))))
      (.mul (.var 0) (.var 0))
      (by decide)
      (fun
        | 0 => (plaquette width face).scalar
        | 1 => (plaquette width face).iPart
        | 2 => (plaquette width face).jPart
        | _ => (plaquette width face).kPart)
  exact hreplace.trans (RatPolyCoeffEqv.haarCarrier hcancel)

/-- Exact local physical-character recoding of the vector-coordinate jet. -/
theorem plaquetteVectorQuadraticJet_character
    (width : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (N width)
      (sourceProbe width [(face, vectorQuadraticJetTerms)])
      (polySmul 4 (plaquetteVectorQuadraticJet width face)) := by
  have hcharacter : RatPolyCoeffEqv
      (sourceProbe width [(face, vectorQuadraticJetTerms)])
      (polySmul 4
        (polyAdd polyOne
          (polyNeg (polyMul (plaquette width face).scalar
            (plaquette width face).scalar)))) := by
    unfold sourceProbe product polynomialProduct
    exact (local_character_identity (plaquette width face).scalar).mul_right polyOne
      |>.trans (RatPolyCoeffEqv.mul_one _)
  exact (RatPolyCoeffEqv.haarCarrier hcharacter).trans
    (HaarCarrierEqv.smul 4 (scalar_proxy_vector_jet width face))

private theorem single_source
    (width offset : Nat) (coefficient : Q') (face : Z4Plaq) :
    HaarCarrierEqv (N width + offset * N width)
      (polySmul (quarter * coefficient)
        (windowProbe width (vectorQuadraticJetSchedule offset face)))
      (polySmul coefficient
        (liftBoundary (offset * N width)
          (plaquetteVectorQuadraticJet width face))) := by
  let shift := offset * N width
  have hlift := lift_carrier shift
    (plaquetteVectorQuadraticJet_character width face)
  have hlocal : HaarCarrierEqv (N width + shift)
      (windowProbe width (vectorQuadraticJetSchedule offset face))
      (polySmul 4
        (liftBoundary shift (plaquetteVectorQuadraticJet width face))) := by
    unfold vectorQuadraticJetSchedule windowProbe polynomialProduct
    have hproduct := HaarCarrierEqv.mul_right polyOne hlift
    have hproduct' := hproduct.trans
      (RatPolyCoeffEqv.haarCarrier
        (RatPolyCoeffEqv.mul_one
          (liftBoundary shift
            (polySmul 4 (plaquetteVectorQuadraticJet width face)))))
    simpa only [List.foldr, lift_smul, shift] using hproduct'
  have hscaled := HaarCarrierEqv.smul (quarter * coefficient) hlocal
  have hcoefficient : (quarter * coefficient) * 4 ≈ coefficient := by
    have hquarter : quarter * 4 ≈ 1 := by
      unfold quarter
      decide
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ 4 (Q'.mul_comm_eqv quarter coefficient))
      (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv coefficient quarter 4)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left coefficient _ _ hquarter)
          (Q'.mul_one_eqv coefficient)))
  exact hscaled.trans
    (RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.smul_assoc (quarter * coefficient) 4 _).trans
        (RatPolyCoeffEqv.smul_coefficient hcoefficient _)))

private theorem finiteSum_carrier_local
    {Index : Type} {blocks : Nat} (left right : Index → RatPoly) :
    ∀ items : List Index,
      (∀ index, index ∈ items → HaarCarrierEqv blocks (left index) (right index)) →
      HaarCarrierEqv blocks (finitePolySum left items) (finitePolySum right items)
  | [], _ => HaarCarrierEqv.refl _ _
  | index :: items, h =>
      HaarCarrierEqv.add (h index List.mem_cons_self)
        (finiteSum_carrier_local left right items
          (fun next hnext => h next (List.mem_cons_of_mem index hnext)))

private theorem lift_zero : ∀ n : Nat, liftBoundary n polyZero = polyZero
  | 0 => rfl
  | n + 1 => by
      change liftHead (liftBoundary n polyZero) = polyZero
      rw [lift_zero n]
      rfl

private theorem lift_weighted_sum {Index : Type}
    (n : Nat) (coefficient : Index → Q') (polynomial : Index → RatPoly) :
    ∀ items : List Index,
      liftBoundary n
          (finitePolySum
            (fun index => polySmul (coefficient index) (polynomial index)) items) =
        finitePolySum
          (fun index =>
            polySmul (coefficient index) (liftBoundary n (polynomial index))) items
  | [] => lift_zero n
  | index :: items => by
      simp only [finitePolySum, lift_add, lift_smul,
        lift_weighted_sum n coefficient polynomial items]

/-- The complete scheduled character span is the chronological lift of the
physical vector jet under every insertion on its natural carrier. -/
theorem originalBulkVectorQuadraticJetSchedule_source
    (s : Nat) (hs : 0 < s) (offset : Nat) :
    HaarCarrierEqv (N (s * s) + offset * N (s * s))
      (sourceSpan (s * s)
        (originalBulkVectorQuadraticJetSchedule s hs offset))
      (liftBoundary (offset * N (s * s))
        (originalBulkVectorQuadraticJet s hs)) := by
  unfold sourceSpan originalBulkVectorQuadraticJetSchedule
    originalBulkVectorQuadraticJet
  rw [YMGap.Continuum.PolynomialWeightedSumBounds.sum_map,
    lift_weighted_sum]
  exact finiteSum_carrier_local _ _ (bulkSourceFaces s) (fun face _ =>
    single_source (s * s) offset (bulkSourceCoefficient s hs face) face)

theorem originalBulkVectorQuadraticJetSchedule_within
    (s : Nat) (hs : 0 < s) (offset : Nat) :
    ∀ x, x ∈ originalBulkVectorQuadraticJetSchedule s hs offset →
      ∀ entry, entry ∈ x.2 → entry.1 ≤ offset := by
  intro x hx entry hentry
  obtain ⟨face, _, rfl⟩ := List.mem_map.mp hx
  have h := List.mem_singleton.mp hentry
  subst entry
  exact Nat.le_refl _

theorem originalBulkVectorQuadraticJetSchedule_faces
    (s : Nat) (hs : 0 < s) (offset : Nat) :
    ∀ x, x ∈ originalBulkVectorQuadraticJetSchedule s hs offset →
      ∀ entry, entry ∈ x.2 → ∀ factor, factor ∈ entry.2 →
        factor.1 ∈ spatialFaces (s * s) := by
  intro x hx entry hentry factor hfactor
  obtain ⟨face, hface, rfl⟩ := List.mem_map.mp hx
  have hentryEq := List.mem_singleton.mp hentry
  subst entry
  have hfactorEq := List.mem_singleton.mp hfactor
  subst factor
  exact bulkSourceFace_mem_spatialFaces_square hface

/-- The scheduled vector-jet carrier identity extended to any complete lag
window containing its chronological offset. -/
theorem originalBulkVectorQuadraticJetSchedule_source_full
    (s : Nat) (hs : 0 < s) (offset L : Nat) (hoffset : offset ≤ L) :
    HaarCarrierEqv ((L + 1) * N (s * s))
      (sourceSpan (s * s)
        (originalBulkVectorQuadraticJetSchedule s hs offset))
      (liftBoundary (offset * N (s * s))
        (originalBulkVectorQuadraticJet s hs)) := by
  let blocks := N (s * s)
  let shift := offset * blocks
  let extra := (L - offset) * blocks
  let schedule := originalBulkVectorQuadraticJetSchedule s hs offset
  let source := sourceSpan (s * s) schedule
  let jet := originalBulkVectorQuadraticJet s hs
  have hsmall : HaarCarrierEqv (blocks + shift) source
      (liftBoundary shift jet) := by
    simpa only [blocks, shift, source, schedule, jet] using
      (originalBulkVectorQuadraticJetSchedule_source s hs offset)
  have hsourceSupport : SupportedQuaternionBlocks (blocks + shift) source := by
    have h := sourceSpan_supported (s * s) offset schedule
      (originalBulkVectorQuadraticJetSchedule_within s hs offset)
    simpa only [blocks, shift, Nat.add_mul, Nat.one_mul, Nat.add_comm] using h
  have hjetSupport : SupportedQuaternionBlocks (blocks + shift)
      (liftBoundary shift jet) :=
    lift_supported (originalBulkVectorQuadraticJet_supported s hs) shift
  have hfullSize : blocks + shift + extra = (L + 1) * blocks := by
    unfold shift extra
    calc
      blocks + offset * blocks + (L - offset) * blocks =
          blocks + (offset * blocks + (L - offset) * blocks) := by omega
      _ = blocks + (offset + (L - offset)) * blocks := by
        rw [Nat.add_mul]
      _ = blocks + L * blocks := by rw [Nat.add_sub_of_le hoffset]
      _ = (L + 1) * blocks := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
  have h := carrier_extend extra hsourceSupport hjetSupport hsmall
  rwa [hfullSize] at h

private theorem qmul {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

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
  have scaleL (coefficient : Q') (a b : RatPoly) :
      F (polyMul (polySmul coefficient a) b) ≈
        coefficient * F (polyMul a b) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK m L n
        (RatPolyCoeffEqv.polyMul_smul_left coefficient a b))
      (windowRatio_smul hw0 hw1 K width hK m L n coefficient _)
  have scaleR (coefficient : Q') (a b : RatPoly) :
      F (polyMul a (polySmul coefficient b)) ≈
        coefficient * F (polyMul a b) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK m L n
        (RatPolyCoeffEqv.polyMul_smul_right coefficient a b))
      (windowRatio_smul hw0 hw1 K width hK m L n coefficient _)
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

/-- Canonical ambient slab shared with the scalar remainder. -/
def originalBulkVectorQuadraticJetExtent (s n L : Nat) : Nat :=
  originalBulkScalarSquareRemainderExtent s n L

/-- The unchanged selected original action shared with the scalar remainder. -/
def originalBulkVectorQuadraticJetIds (s n L : Nat) : List Nat :=
  originalBulkScalarSquareRemainderIds s n L

theorem originalBulkVectorQuadraticJetIds_physical (s n L : Nat) :
    ∀ id, id ∈ originalBulkVectorQuadraticJetIds s n L →
      id ∈ slabPhysicalFaceEdges (originalBulkVectorQuadraticJetExtent s n L) := by
  exact originalBulkScalarSquareRemainderIds_physical s n L

/-- The literal placed bulk vector jet in the canonical ambient slab. -/
def originalBulkVectorQuadraticJetPlaced
    (s : Nat) (hs : 0 < s) (n offset L : Nat) : RatPoly :=
  placedSpan (originalBulkVectorQuadraticJetExtent s n L) n
    (originalBulkVectorQuadraticJetSchedule s hs offset)

/-- Finite vector-jet mean under the SAME selected original action. -/
def originalBulkVectorQuadraticJetSelectedMean {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat) : Q' :=
  finiteValue w hw0 hw1 (originalBulkVectorQuadraticJetExtent s n L)
    (originalBulkVectorQuadraticJetIds s n L)
    (originalBulkVectorQuadraticJetIds_physical s n L)
    (originalBulkVectorQuadraticJetPlaced s hs n offset L) stage

/-- Finite vector-jet covariance under the SAME action and normalization. -/
def originalBulkVectorQuadraticJetSelectedCovariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat) : Q' :=
  finiteCovariance w hw0 hw1
    (originalBulkVectorQuadraticJetExtent s n L)
    (originalBulkVectorQuadraticJetIds s n L)
    (originalBulkVectorQuadraticJetIds_physical s n L)
    (originalBulkVectorQuadraticJetPlaced s hs n offset L)
    (originalBulkVectorQuadraticJetPlaced s hs n offset L) stage

/-- Exact selected covariance plus center-mismatch split for the physical
vector jet at any chronological offset. -/
theorem originalBulkVectorQuadraticJet_diagonal_covariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat)
    (hoffset : offset ≤ L) (center : Q') :
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul
          (shifted (liftBoundary (offset * N (s * s))
            (originalBulkVectorQuadraticJet s hs)) center)
          (shifted (liftBoundary (offset * N (s * s))
            (originalBulkVectorQuadraticJet s hs)) center)) ≈
      originalBulkVectorQuadraticJetSelectedCovariance
          hw0 hw1 s hs stage n L offset +
        ((originalBulkVectorQuadraticJetSelectedMean
            hw0 hw1 s hs stage n L offset + -center) *
          (originalBulkVectorQuadraticJetSelectedMean
            hw0 hw1 s hs stage n L offset + -center)) := by
  let blocks := N (s * s)
  let shift := offset * blocks
  let extra := (L - offset) * blocks
  let extent := originalBulkVectorQuadraticJetExtent s n L
  let schedule := originalBulkVectorQuadraticJetSchedule s hs offset
  let source := sourceSpan (s * s) schedule
  let jet := originalBulkVectorQuadraticJet s hs
  let placed := originalBulkVectorQuadraticJetPlaced s hs n offset L
  let ids := originalBulkVectorQuadraticJetIds s n L
  let hids := originalBulkVectorQuadraticJetIds_physical s n L
  have hsourceSmall : HaarCarrierEqv (blocks + shift) source
      (liftBoundary shift jet) := by
    simpa only [blocks, shift, source, schedule, jet] using
      (originalBulkVectorQuadraticJetSchedule_source s hs offset)
  have hsourceSupport : SupportedQuaternionBlocks (blocks + shift) source := by
    have h := sourceSpan_supported (s * s) offset schedule
      (originalBulkVectorQuadraticJetSchedule_within s hs offset)
    simpa only [blocks, shift, Nat.add_mul, Nat.one_mul, Nat.add_comm] using h
  have hjetSupport : SupportedQuaternionBlocks (blocks + shift)
      (liftBoundary shift jet) := by
    exact lift_supported (originalBulkVectorQuadraticJet_supported s hs) shift
  have hfullSize : blocks + shift + extra = (L + 1) * blocks := by
    unfold shift extra
    calc
      blocks + offset * blocks + (L - offset) * blocks =
          blocks + (offset * blocks + (L - offset) * blocks) := by omega
      _ = blocks + (offset + (L - offset)) * blocks := by
        rw [Nat.add_mul]
      _ = blocks + L * blocks := by rw [Nat.add_sub_of_le hoffset]
      _ = (L + 1) * blocks := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
  have hsourceFull : HaarCarrierEqv ((L + 1) * blocks) source
      (liftBoundary shift jet) := by
    have h := carrier_extend extra hsourceSupport hjetSupport hsourceSmall
    rwa [hfullSize] at h
  have hwithin : ∀ x, x ∈ schedule → ∀ entry, entry ∈ x.2 → entry.1 ≤ L := by
    intro x hx entry hentry
    exact Nat.le_trans
      (originalBulkVectorQuadraticJetSchedule_within
        s hs offset x hx entry hentry)
      hoffset
  have hfaces : ∀ x, x ∈ schedule → ∀ entry, entry ∈ x.2 →
      ∀ factor, factor ∈ entry.2 → factor.1 ∈ spatialFaces (s * s) :=
    originalBulkVectorQuadraticJetSchedule_faces s hs offset
  have hwidth : s * s ≤ extent := by
    unfold extent originalBulkVectorQuadraticJetExtent
      originalBulkScalarSquareRemainderExtent
    omega
  have htime : 0 + (n + (L + n)) ≤ extent := by
    unfold extent originalBulkVectorQuadraticJetExtent
      originalBulkScalarSquareRemainderExtent
    omega
  have hmeanRaw := windowRatio_span_originalFiniteValue hw0 hw1 hwidth htime
    schedule hwithin hfaces stage
  have hmean : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n source ≈
      finiteValue w hw0 hw1 extent ids hids placed stage := by
    simpa only [Nat.zero_add, source, placed, ids, extent,
      originalBulkVectorQuadraticJetPlaced,
      originalBulkVectorQuadraticJetIds,
      originalBulkVectorQuadraticJetExtent] using hmeanRaw
  have hsquareRaw := windowRatio_span_mul_originalFiniteValue hw0 hw1
    hwidth htime schedule schedule hwithin hfaces hwithin hfaces stage
  have hsquare : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (polyMul source source) ≈
      finiteValue w hw0 hw1 extent ids hids (polyMul placed placed) stage := by
    simpa only [Nat.zero_add, source, placed, ids, extent,
      originalBulkVectorQuadraticJetPlaced,
      originalBulkVectorQuadraticJetIds,
      originalBulkVectorQuadraticJetExtent] using hsquareRaw
  have hsourceShift : HaarCarrierEqv ((L + 1) * blocks)
      (shifted (liftBoundary shift jet) center)
      (shifted source center) := by
    unfold shifted
    exact HaarCarrierEqv.add
      (HaarCarrierEqv.smul 1 hsourceFull.symm)
      (HaarCarrierEqv.refl _ _)
  have hreplace : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul
        (shifted (liftBoundary shift jet) center)
        (shifted (liftBoundary shift jet) center)) ≈
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (shifted source center) (shifted source center)) :=
    windowRatio_carrier_congr hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (HaarCarrierEqv.mul hsourceShift hsourceShift)
  have hleft := shifted_square_window_identity hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L n source center
  have hmeanSelected : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n source ≈
      originalBulkVectorQuadraticJetSelectedMean
        hw0 hw1 s hs stage n L offset := by
    simpa only [originalBulkVectorQuadraticJetSelectedMean,
      originalBulkVectorQuadraticJetPlaced,
      originalBulkVectorQuadraticJetIds,
      originalBulkVectorQuadraticJetExtent, source, extent, placed, ids]
      using hmean
  have hcovarianceSelected :
      (windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n (polyMul source source) +
        -(windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
            (Nat.le_add_right _ _) n L n source *
          windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
            (Nat.le_add_right _ _) n L n source)) ≈
      originalBulkVectorQuadraticJetSelectedCovariance
        hw0 hw1 s hs stage n L offset := by
    unfold originalBulkVectorQuadraticJetSelectedCovariance finiteCovariance
    exact Q'.add_eqv_congr' hsquare
      (Q'.neg_eqv_congr _ _ (qmul hmean hmean))
  exact Q'.eqv_trans _ _ _ hreplace
    (Q'.eqv_trans _ _ _ hleft
      (Q'.add_eqv_congr'
        hcovarianceSelected
        (qmul
          (Q'.add_eqv_congr_right _ _ (-center) hmeanSelected)
          (Q'.add_eqv_congr_right _ _ (-center) hmeanSelected))))

/-- The literal lower vector-jet diagonal is a SAME-selected covariance plus
only its finite OWN-center mismatch. -/
theorem originalBulkVectorQuadraticJet_leftDiagonal_covariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJet s hs
    let center := originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (shifted jet center) (shifted jet center)) ≈
      originalBulkVectorQuadraticJetSelectedCovariance
          hw0 hw1 s hs stage n L 0 +
        ((originalBulkVectorQuadraticJetSelectedMean
            hw0 hw1 s hs stage n L 0 + -center) *
          (originalBulkVectorQuadraticJetSelectedMean
            hw0 hw1 s hs stage n L 0 + -center)) := by
  dsimp only
  simpa only [Nat.zero_mul, liftBoundary] using
    (originalBulkVectorQuadraticJet_diagonal_covariance
      hw0 hw1 s hs stage n L 0 (Nat.zero_le _)
      (originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n))

/-- The chronologically lifted upper vector-jet diagonal has the matching
SAME-selected covariance split at offset `L`. -/
theorem originalBulkVectorQuadraticJet_rightDiagonal_covariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJet s hs
    let center := originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
    let lifted := liftBoundary (L * N (s * s)) (shifted jet center)
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul lifted lifted) ≈
      originalBulkVectorQuadraticJetSelectedCovariance
          hw0 hw1 s hs stage n L L +
        ((originalBulkVectorQuadraticJetSelectedMean
            hw0 hw1 s hs stage n L L + -center) *
          (originalBulkVectorQuadraticJetSelectedMean
            hw0 hw1 s hs stage n L L + -center)) := by
  dsimp only
  let blocks := N (s * s)
  let shift := L * blocks
  let jet := originalBulkVectorQuadraticJet s hs
  let center := originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
  have hsize : (L + 1) * blocks = blocks + shift := by
    unfold shift
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hshift : HaarCarrierEqv ((L + 1) * blocks)
      (liftBoundary shift (shifted jet center))
      (shifted (liftBoundary shift jet) center) := by
    unfold shifted
    rw [lift_add, lift_smul]
    exact HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (by
        rw [hsize]
        simpa only [cap, lift_smul] using
          (lift_cap_carrier blocks shift (-center)))
  have hcongr : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul (liftBoundary shift (shifted jet center))
        (liftBoundary shift (shifted jet center))) ≈
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (shifted (liftBoundary shift jet) center)
          (shifted (liftBoundary shift jet) center)) :=
    windowRatio_carrier_congr hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (HaarCarrierEqv.mul hshift hshift)
  exact Q'.eqv_trans _ _ _ hcongr
    (originalBulkVectorQuadraticJet_diagonal_covariance
      hw0 hw1 s hs stage n L L (Nat.le_refl _) center)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance.plaquetteVectorQuadraticJet_character
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance.plaquetteVectorQuadraticJet_complement
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance.originalBulkVectorQuadraticJetSchedule_source
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance.originalBulkVectorQuadraticJetSchedule_within
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance.originalBulkVectorQuadraticJetSchedule_faces
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance.originalBulkVectorQuadraticJetSchedule_source_full
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance.originalBulkVectorQuadraticJetIds_physical
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance.originalBulkVectorQuadraticJet_diagonal_covariance
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance.originalBulkVectorQuadraticJet_leftDiagonal_covariance
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance.originalBulkVectorQuadraticJet_rightDiagonal_covariance
