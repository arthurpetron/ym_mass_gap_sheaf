/-
# Exact product-Haar resummation of the centered BF4 vacuum moments

The centered vacuum ledger leaves two signed-Haar scalars: the complete
vacuum row and the complete constant quadratic moment.  Their definitions
place a 116-link product-Haar evaluation inside two or three finite label
sums.  This file proves the exact finite Fubini step that moves those sums
inside the Haar functional.

The result is one explicit rational polynomial for each moment.  Evaluating
these polynomials still requires the geometric gauge-fixing/resummation
bridge from the literal 116-link carrier to the five transmitted holonomies;
no value, sign, or positivity claim is made here.

## Axiom gate

Finite lists, exact `Q'` arithmetic, and rational-polynomial product Haar
only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
import YMGap.Continuum.BF4CompactActionCPOrder

namespace YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumProbe
open YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite polynomial sums commute with product Haar -/

/-- Literal finite sum of rational polynomials.  It preserves the unreduced
monomial ledger, so the product-Haar theorem below is purely linear. -/
def finitePolySum {Index : Type}
    (polynomial : Index → RatPoly) : List Index → RatPoly
  | [] => polyZero
  | head :: tail =>
      polyAdd (polynomial head) (finitePolySum polynomial tail)

/-- Exact product Haar commutes with every literal finite polynomial sum. -/
theorem quaternionHaar_finitePolySum {Index : Type}
    (blocks : Nat) (polynomial : Index → RatPoly) :
    ∀ items : List Index,
      quaternionHaar blocks (finitePolySum polynomial items) ≈
        listQSum
          (fun item => quaternionHaar blocks (polynomial item))
          items
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      refine Q'.eqv_trans _
        (quaternionHaar blocks (polynomial head) +
          quaternionHaar blocks
            (finitePolySum polynomial tail)) _ ?_ ?_
      · exact quaternionHaar_append blocks
          (polynomial head) (finitePolySum polynomial tail)
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (quaternionHaar_finitePolySum
            blocks polynomial tail)

/-- Two nested finite polynomial sums may be evaluated by one product-Haar
functional. -/
theorem quaternionHaar_finitePolySum₂
    {Left Right : Type} (blocks : Nat)
    (polynomial : Left → Right → RatPoly)
    (leftItems : List Left) (rightItems : List Right) :
    quaternionHaar blocks
        (finitePolySum
          (fun left =>
            finitePolySum (polynomial left) rightItems)
          leftItems) ≈
      listQSum
        (fun left =>
          listQSum
            (fun right =>
              quaternionHaar blocks (polynomial left right))
            rightItems)
        leftItems := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        quaternionHaar blocks
          (finitePolySum (polynomial left) rightItems))
      leftItems) _ ?_ ?_
  · exact quaternionHaar_finitePolySum blocks _ leftItems
  · exact listQSum_congr
      (fun left =>
        quaternionHaar_finitePolySum
          blocks (polynomial left) rightItems)
      leftItems

/-- Three nested finite polynomial sums may likewise be evaluated by one
product-Haar functional. -/
theorem quaternionHaar_finitePolySum₃
    {Left Middle Right : Type} (blocks : Nat)
    (polynomial : Left → Middle → Right → RatPoly)
    (leftItems : List Left) (middleItems : List Middle)
    (rightItems : List Right) :
    quaternionHaar blocks
        (finitePolySum
          (fun left =>
            finitePolySum
              (fun middle =>
                finitePolySum
                  (polynomial left middle) rightItems)
              middleItems)
          leftItems) ≈
      listQSum
        (fun left =>
          listQSum
            (fun middle =>
              listQSum
                (fun right =>
                  quaternionHaar blocks
                    (polynomial left middle right))
                rightItems)
            middleItems)
        leftItems := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        quaternionHaar blocks
          (finitePolySum
            (fun middle =>
              finitePolySum
                (polynomial left middle) rightItems)
            middleItems))
      leftItems) _ ?_ ?_
  · exact quaternionHaar_finitePolySum blocks _ leftItems
  · exact listQSum_congr
      (fun left =>
        quaternionHaar_finitePolySum₂
          blocks (polynomial left)
          middleItems rightItems)
      leftItems

/-! ## 2. The literal weighted 116-link polynomial -/

/-- Move the positive heat-kernel face coefficient into the literal
extent-one signed Haar-network polynomial. -/
def exactCorrectedSlabWeightedIntegrand
    (w : Q') (K : Nat) (faceLabel : EdgeLabelling) : RatPoly :=
  polySmul
    (slabParametricKPhysicalFaceFactor w K 1 faceLabel)
    (exactCorrectedSlabSpinNetworkIntegrand 1 faceLabel)

/-- One exact dual summand is the normalized 116-link product-Haar value of
its weighted polynomial integrand. -/
theorem exactCorrectedSlabDualTerm_eq_weightedHaar
    (w : Q') (K : Nat) (faceLabel : EdgeLabelling) :
    exactCorrectedSlabDualTerm w K 1 faceLabel ≈
      quaternionHaar 116
        (exactCorrectedSlabWeightedIntegrand w K faceLabel) := by
  unfold exactCorrectedSlabDualTerm
    exactCorrectedSlabHaarCoefficient
    exactCorrectedSlabWeightedIntegrand
  rw [correctedSlabLinks_extent_one_length]
  exact Q'.eqv_symm
    (quaternionHaar_polySmul 116
      (slabParametricKPhysicalFaceFactor w K 1 faceLabel)
      (exactCorrectedSlabSpinNetworkIntegrand 1 faceLabel))

/-! ## 3. Resummed exact vacuum-row and constant polynomials -/

/-- One polynomial whose 116-link Haar value is the complete signed vacuum
row.  The right-boundary and fixed-interface label sums have been performed
inside the polynomial ledger. -/
def exactVacuumRowResummedPolynomial
    (w : Q') (K : Nat) : RatPoly :=
  finitePolySum
    (fun right =>
      finitePolySum
        (fun boundary =>
          exactCorrectedSlabWeightedIntegrand w K
            (assembleReflectedSlabLabelling
              0 zeroEdgeLabelling boundary right))
        (centralBoundaryChannels K 0))
    (centralHalfStates K 0)

/-- One polynomial whose 116-link Haar value is the complete constant
quadratic moment.  Both spatial boundary sums and the fixed-interface sum
are inside the polynomial ledger. -/
def exactConstantMomentResummedPolynomial
    (w : Q') (K : Nat) : RatPoly :=
  finitePolySum
    (fun left =>
      finitePolySum
        (fun right =>
          finitePolySum
            (fun boundary =>
              exactCorrectedSlabWeightedIntegrand w K
                (assembleReflectedSlabLabelling
                  0 left boundary right))
            (centralBoundaryChannels K 0))
        (centralHalfStates K 0))
    (centralHalfStates K 0)

/-- The bilinear form with constant one in both slots is the complete joint
sum. -/
theorem finiteJointBilinear_one_one_eq_joint_sum
    {State : Type} (states : List State)
    (joint : State → State → Q') :
    finiteJointBilinear states (fun _ => 1) (fun _ => 1) joint ≈
      listQSum
        (fun left => listQSum (joint left) states)
        states := by
  unfold finiteJointBilinear
  apply listQSum_congr
  intro left
  apply listQSum_congr
  intro right
  exact Q'.eqv_trans _ (1 * joint left right) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.one_mul_eqv 1))
    (Q'.one_mul_eqv (joint left right))

/-- **Vacuum-row product-Haar resummation.**  The first unresolved signed
moment is one explicit normalized Haar value on the literal 116-link
carrier. -/
theorem exactVacuumRightConstantCrossMoment_eq_resummedHaar
    (w : Q') (K : Nat) :
    exactVacuumRightConstantCrossMoment w K ≈
      quaternionHaar 116
        (exactVacuumRowResummedPolynomial w K) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun right =>
        listQSum
          (fun boundary =>
            quaternionHaar 116
              (exactCorrectedSlabWeightedIntegrand w K
                (assembleReflectedSlabLabelling
                  0 zeroEdgeLabelling boundary right)))
          (centralBoundaryChannels K 0))
      (centralHalfStates K 0)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (exactCorrectedSlabReflectedKernel
          w K 0 zeroEdgeLabelling)
        (centralHalfStates K 0)) _
      (exactVacuumRightConstantCrossMoment_eq_vacuumRowSum
        w K) ?_
    apply listQSum_congr
    intro right
    unfold exactCorrectedSlabReflectedKernel
    apply listQSum_congr
    intro boundary
    exact exactCorrectedSlabDualTerm_eq_weightedHaar
      w K
      (assembleReflectedSlabLabelling
        0 zeroEdgeLabelling boundary right)
  · exact Q'.eqv_symm
      (quaternionHaar_finitePolySum₂
        116
        (fun right boundary =>
          exactCorrectedSlabWeightedIntegrand w K
            (assembleReflectedSlabLabelling
              0 zeroEdgeLabelling boundary right))
        (centralHalfStates K 0)
        (centralBoundaryChannels K 0))

/-- **Constant-moment product-Haar resummation.**  The second unresolved
signed moment is one explicit normalized Haar value on the same literal
116-link carrier. -/
theorem exactConstantQuadraticMoment_eq_resummedHaar
    (w : Q') (K : Nat) :
    exactConstantQuadraticMoment w K ≈
      quaternionHaar 116
        (exactConstantMomentResummedPolynomial w K) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            listQSum
              (fun boundary =>
                quaternionHaar 116
                  (exactCorrectedSlabWeightedIntegrand w K
                    (assembleReflectedSlabLabelling
                      0 left boundary right)))
              (centralBoundaryChannels K 0))
          (centralHalfStates K 0))
      (centralHalfStates K 0)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum
            (exactCorrectedSlabReflectedKernel w K 0 left)
            (centralHalfStates K 0))
        (centralHalfStates K 0)) _
      (finiteJointBilinear_one_one_eq_joint_sum
        (centralHalfStates K 0)
        (exactCorrectedSlabReflectedKernel w K 0)) ?_
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    unfold exactCorrectedSlabReflectedKernel
    apply listQSum_congr
    intro boundary
    exact exactCorrectedSlabDualTerm_eq_weightedHaar
      w K
      (assembleReflectedSlabLabelling
        0 left boundary right)
  · exact Q'.eqv_symm
      (quaternionHaar_finitePolySum₃
        116
        (fun left right boundary =>
          exactCorrectedSlabWeightedIntegrand w K
            (assembleReflectedSlabLabelling
              0 left boundary right))
        (centralHalfStates K 0)
        (centralHalfStates K 0)
        (centralBoundaryChannels K 0))

/-! ## 4. The centered seam in resummed Haar form -/

/-- Signed-Haar side of the centered vacuum probe after finite label
resummation. -/
def exactResummedCenteredVacuumMomentExpression
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  1 +
    ((-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling) *
        quaternionHaar 116
          (exactVacuumRowResummedPolynomial w K) +
    ((-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling) *
        quaternionHaar 116
          (exactVacuumRowResummedPolynomial w K) +
    ((-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling) *
      (-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling)) *
        quaternionHaar 116
          (exactConstantMomentResummedPolynomial w K)))

/-- The exact centered vacuum quadratic equals its two-polynomial resummed
Haar expression. -/
theorem exactSlabAllCutoffQuadratic_centeredVacuum_eq_resummedHaar
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    exactSlabAllCutoffQuadratic
        w K (centeredVacuumCodeDelta w hw K) ≈
      exactResummedCenteredVacuumMomentExpression w hw K := by
  unfold exactResummedCenteredVacuumMomentExpression
  refine Q'.eqv_trans _ _ _
    (exactSlabAllCutoffQuadratic_centeredVacuum_symmetric_expansion
      w hw K) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl 1)
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left
        (-centralPhysicalRowMarginal
          w hw K 0 zeroEdgeLabelling) _ _
        (exactVacuumRightConstantCrossMoment_eq_resummedHaar
          w K))
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left
          (-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling) _ _
          (exactVacuumRightConstantCrossMoment_eq_resummedHaar
            w K))
        (Q'.mul_eqv_congr_left
          ((-centralPhysicalRowMarginal
              w hw K 0 zeroEdgeLabelling) *
            (-centralPhysicalRowMarginal
              w hw K 0 zeroEdgeLabelling)) _ _
          (exactConstantQuadraticMoment_eq_resummedHaar
            w K))))

/-- Any centered same-action inhabitant must equate the explicit resummed
116-link Haar expression with the closed positive physical variance. -/
theorem ExactHaarPhysicalPerronCenteredSameActionAt.resummedVacuumMoment_balance
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (identification :
      ExactHaarPhysicalPerronCenteredSameActionAt w hw K) :
    exactResummedCenteredVacuumMomentExpression w hw K ≈
      physicalCenteredVacuumMomentExpression w hw K := by
  exact Q'.eqv_trans _
    (exactCenteredVacuumMomentExpression w hw K) _
    (Q'.eqv_trans _
      (exactSlabAllCutoffQuadratic
        w K (centeredVacuumCodeDelta w hw K)) _
      (Q'.eqv_symm
        (exactSlabAllCutoffQuadratic_centeredVacuum_eq_resummedHaar
          w hw K))
      (exactSlabAllCutoffQuadratic_centeredVacuum_symmetric_expansion
        w hw K))
    (YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.ExactHaarPhysicalPerronCenteredSameActionAt.vacuumMoment_balance
      identification)

end YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation.quaternionHaar_finitePolySum
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation.quaternionHaar_finitePolySum₂
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation.quaternionHaar_finitePolySum₃
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation.exactCorrectedSlabDualTerm_eq_weightedHaar
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation.finiteJointBilinear_one_one_eq_joint_sum
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation.exactVacuumRightConstantCrossMoment_eq_resummedHaar
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation.exactConstantQuadraticMoment_eq_resummedHaar
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation.exactSlabAllCutoffQuadratic_centeredVacuum_eq_resummedHaar
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation.ExactHaarPhysicalPerronCenteredSameActionAt.resummedVacuumMoment_balance
