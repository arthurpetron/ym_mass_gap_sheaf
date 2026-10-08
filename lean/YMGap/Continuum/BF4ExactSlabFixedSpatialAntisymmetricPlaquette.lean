/-
# An exactly centered antisymmetric ORIGINAL plaquette source

The origin p01 minus p02 fundamental characters form one literal radius-zero
Wilson expression. Spatial x1/x2 exchange preserves the complete chronological
action and exchanges these two ordered words without reversal. Every finite
original mean, including its moving OWN mean, is therefore exactly zero in
the rational setoid. This removes centering debt only: no filtered energy,
positive-time survival, scaling estimate or continuum claim is made.
-/

import YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
import YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
import YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialAntisymmetricPlaquette

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWilsonLoop
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWilsonWindow
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison (shifted)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def face01 : Z4Plaq := ((0, 0, 0, 0), .p01)
def face02 : Z4Plaq := ((0, 0, 0, 0), .p02)
def faces : List Z4Plaq := [face01, face02]
def coefficient (p : Z4Plaq) : Q' := if p = face01 then 1 else -1

theorem faces_nodup : faces.Nodup := by decide

theorem faces_physical {width : Nat} (hw : 1 ≤ width) :
    ∀ p, p ∈ faces → p ∈ spatialFaces width := by
  intro p hp
  have hpos : 0 < width := by omega
  have hp' : p = face01 ∨ p = face02 := by
    simpa only [faces, List.mem_cons, List.not_mem_nil, or_false] using hp
  rcases hp' with rfl | rfl
  · exact (spatialFaces_mem_iff width face01).mpr
      ⟨hpos, hpos, hpos, rfl, by decide⟩
  · exact (spatialFaces_mem_iff width face02).mpr
      ⟨hpos, hpos, hpos, rfl, by decide⟩

theorem coefficient_square_budget :
    listQSum (fun p => coefficient p * coefficient p) faces ≈ 2 := by decide

def expression {width : Nat} (hw : 1 ≤ width) : WindowExpression width :=
  familyExpression width faces coefficient (faces_physical hw)

theorem expression_within {width : Nat} (hw : 1 ≤ width) :
    Within 0 (expression hw) := family_within width faces coefficient (faces_physical hw)

private theorem sourceLoop_ext {width : Nat} (x y : SourceLoop width)
    (hs : x.start = y.start) (he : x.edges = y.edges) : x = y := by
  cases x
  cases y
  cases hs
  cases he
  rfl

/-- No reverse flag or edge order changes for p01 to p02. -/
theorem swapSourceLoop_face01 {width : Nat} (hw : 1 ≤ width) :
    swapSourceLoop (plaquetteLoop face01 (faces_physical hw face01 (by simp [faces]))) =
      plaquetteLoop face02 (faces_physical hw face02 (by simp [faces])) := by
  apply sourceLoop_ext
  · rfl
  · rfl

theorem swapSourceLoop_face02 {width : Nat} (hw : 1 ≤ width) :
    swapSourceLoop (plaquetteLoop face02 (faces_physical hw face02 (by simp [faces]))) =
      plaquetteLoop face01 (faces_physical hw face01 (by simp [faces])) := by
  apply sourceLoop_ext
  · rfl
  · rfl

private theorem original_add {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width : Nat} (L : Nat) (e f : WindowExpression width)
    (he : Within L e) (hf : Within L f) (stage m n : Nat) :
    originalWindowScalar hw0 hw1 L (.add e f) stage m n ≈
      originalWindowScalar hw0 hw1 L e stage m n +
        originalWindowScalar hw0 hw1 L f stage m n :=
  Q'.eqv_trans _ _ _ (originalWindowScalar_pin hw0 hw1 L (.add e f) ⟨he, hf⟩ stage m n)
    (Q'.eqv_trans _ _ _
      (windowRatio_add hw0 hw1 _ width (Nat.le_add_right _ _) m L n _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L e he stage m n))
        (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L f hf stage m n))))

private theorem original_smul {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width : Nat} (L : Nat) (c : Q') (e : WindowExpression width)
    (he : Within L e) (stage m n : Nat) :
    originalWindowScalar hw0 hw1 L (.smul c e) stage m n ≈
      c * originalWindowScalar hw0 hw1 L e stage m n :=
  Q'.eqv_trans _ _ _ (originalWindowScalar_pin hw0 hw1 L (.smul c e) he stage m n)
    (Q'.eqv_trans _ _ _
      (windowRatio_smul hw0 hw1 _ width (Nat.le_add_right _ _) m L n c _)
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L e he stage m n))))

/-- Every finite chronological mean vanishes, not only its diagonal limit. -/
theorem original_mean_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width : Nat} (hw : 1 ≤ width) (L stage m n : Nat) :
    originalWindowScalar hw0 hw1 L (expression hw) stage m n ≈ 0 := by
  let e01 : WindowExpression width :=
    .loop 0 (plaquetteLoop face01 (faces_physical hw face01 (by simp [faces]))) 1
  let e02 : WindowExpression width :=
    .loop 0 (plaquetteLoop face02 (faces_physical hw face02 (by simp [faces]))) 1
  have he01 : Within L e01 := Nat.zero_le L
  have he02 : Within L e02 := Nat.zero_le L
  have hexpr : expression hw = .add (.smul 1 e01)
      (.add (.smul (-1) e02) (.smul 0 .one)) := rfl
  have hs : swapExpression e01 = e02 := by
    dsimp only [e01, e02, swapExpression]
    rw [swapSourceLoop_face01 hw]
  have hm : originalWindowScalar hw0 hw1 L e02 stage m n ≈
      originalWindowScalar hw0 hw1 L e01 stage m n := by
    rw [← hs]
    exact originalWindowScalar_swap hw0 hw1 L e01 stage m n
  rw [hexpr]
  have hlin := Q'.eqv_trans _ _ _
    (original_add hw0 hw1 L (.smul 1 e01)
      (.add (.smul (-1) e02) (.smul 0 .one)) he01 ⟨he02, True.intro⟩ stage m n)
    (Q'.add_eqv_congr'
      (original_smul hw0 hw1 L 1 e01 he01 stage m n)
      (Q'.eqv_trans _ _ _
        (original_add hw0 hw1 L (.smul (-1) e02) (.smul 0 .one)
          he02 True.intro stage m n)
        (Q'.add_eqv_congr'
          (original_smul hw0 hw1 L (-1) e02 he02 stage m n)
          (original_smul hw0 hw1 L 0 .one True.intro stage m n))))
  exact Q'.eqv_trans _ _ _ hlin
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hm) (Q'.eqv_refl _)))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 1) (.var 0))
          (.add (.mul (.neg (.const 1)) (.var 0)) (.mul (.const 0) (.var 1))))
        (.const 0) (by decide)
        (fun
          | 0 => originalWindowScalar hw0 hw1 L e01 stage m n
          | _ => originalWindowScalar hw0 hw1 L .one stage m n)))

theorem endpointMean_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width : Nat} (hw : 1 ≤ width) (stage n L : Nat) :
    expressionEndpointMean hw0 hw1 (expression hw) stage n L ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L (expression hw)
      (within_mono (Nat.zero_le L) _ (expression_within hw)) stage n n))
    (original_mean_zero hw0 hw1 hw L stage n n)

theorem ownMean_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width : Nat} (hw : 1 ≤ width) (stage n : Nat) :
    expressionOwnMean hw0 hw1 (expression hw) stage n ≈ 0 := by
  have hsource : SupportedQuaternionBlocks (baseLinks width).length
      (sourcePolynomial (expression hw)) := by
    simpa only [Nat.zero_add, Nat.one_mul] using source_supported 0 _ (expression_within hw)
  exact Q'.eqv_trans _ _ _
    (middleRatio_swap hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      (n+1) n (sourcePolynomial (expression hw)))
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (lower_endpoint_mean hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) n 1 hsource))
      (endpointMean_zero hw0 hw1 hw stage n 1))

/-- The literal finite OWN-centered polynomial equals this uncentered source. -/
theorem shifted_source_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width : Nat} (hw : 1 ≤ width) (stage n : Nat) :
    RatPolyCoeffEqv
      (shifted (sourcePolynomial (expression hw))
        (expressionOwnMean hw0 hw1 (expression hw) stage n))
      (sourcePolynomial (expression hw)) := by
  unfold shifted
  exact ((RatPolyCoeffEqv.one_smul _).add
    ((RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (ownMean_zero hw0 hw1 hw stage n))
        (by decide : -(0 : Q') ≈ 0)) polyOne).trans
      (RatPolyCoeffEqv.zero_smul polyOne))).trans (RatPolyCoeffEqv.add_zero _)

#print axioms face01
#print axioms face02
#print axioms faces
#print axioms coefficient
#print axioms faces_nodup
#print axioms faces_physical
#print axioms coefficient_square_budget
#print axioms expression
#print axioms expression_within
#print axioms swapSourceLoop_face01
#print axioms swapSourceLoop_face02
#print axioms original_mean_zero
#print axioms endpointMean_zero
#print axioms ownMean_zero
#print axioms shifted_source_pin

end YMGap.Continuum.BF4ExactSlabFixedSpatialAntisymmetricPlaquette
