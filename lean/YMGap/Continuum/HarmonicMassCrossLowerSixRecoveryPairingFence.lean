/-
The lower-six recovery block cannot be paid by the most immediate
cell-by-cell matching: already at the first uniform scale, pairing the first
adverse cell with the first recovery cell is still adverse.  This exact
rational counterexample fences off that tempting route and forces a genuinely
cumulative argument.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryPairingFence

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private def endpointComplementPolyL : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let B := RingNormaliser.PolyExpr.var 2
  let D := RingNormaliser.PolyExpr.var 3
  let E := RingNormaliser.PolyExpr.var 4
  .add
    (.add
      (.add (.mul (.const 4) D)
        (.neg (.mul (.mul u (.add (.const 12) (.mul u u))) I)))
      (.mul (.const 4) B))
    (.neg (.mul (.const 4) E))

private def endpointComplementPolyR : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let B := RingNormaliser.PolyExpr.var 2
  let D := RingNormaliser.PolyExpr.var 3
  let E := RingNormaliser.PolyExpr.var 4
  let core :=
    .add
      (.add
        (.mul (.mul u (.add (.add (.const 12) u) (.mul u u))) I)
        (.neg (.mul (.const 4) B)))
      (.neg (.mul (.const 4) D))
  .add (.add (.mul (.mul u u) I) (.neg core))
    (.neg (.mul (.const 4) E))

private theorem endpointComplementPoly_normal :
    RingNormaliser.normalize endpointComplementPolyL =
      RingNormaliser.normalize endpointComplementPolyR := by
  decide

private theorem endpoint_complement_algebra (u I B D E : Q') :
    ((Q'.ofNat 4 * D +
          -((u * (Q'.ofNat 12 + u * u)) * I)) +
        Q'.ofNat 4 * B) + -(Q'.ofNat 4 * E) ≈
      ((u * u) * I +
        -(((u * ((Q'.ofNat 12 + u) + u * u)) * I +
            -(Q'.ofNat 4 * B)) + -(Q'.ofNat 4 * D))) +
        -(Q'.ofNat 4 * E) := by
  simpa [endpointComplementPolyL, endpointComplementPolyR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      endpointComplementPolyL endpointComplementPolyR
      endpointComplementPoly_normal
      (fun | 0 => u | 1 => I | 2 => B | 3 => D | _ => E))

/-- At `k = 48`, the first adverse mode (`n = 3`) and the first cell after
the central window (`n = 13`) still have a strictly negative combined
increment.  Hence no proof can pair these two cells directly. -/
theorem lowerSix_first_adverse_first_recovery_pair_fails :
    ¬ ((0 : Q') ≤
      lowerSixDirichletIncrement 48 3 +
        lowerSixDirichletIncrement 48 13) := by
  unfold lowerSixDirichletIncrement lowerSixDirichletProfile
    thetaDirichletCell thetaRootTerm integerThetaTerm harmW harmU
    oneSub unit qpow
  decide

/-- Endpoint-aware complement identity.  The lower-six payment is not the
negative of the seven-core sign theorem: it is the available `u²` mass minus
that core and minus the positive terminal mode.  This fixes the direction of
any Pascal-certificate attack. -/
theorem lowerSix_payment_eqv_sevenCore_complement (k : Nat) :
    (lowerSixDirichletSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1) +
        -(Q'.ofNat 4 *
          integerThetaTerm (harmW k) (growingAnchor k + 2)) ≈
      ((harmU k * harmU k) *
          integerThetaSum (harmW k) (growingAnchor k) +
        -sevenDirichletCoreGap k) +
        -(Q'.ofNat 4 *
          integerThetaTerm (harmW k) (growingAnchor k + 2)) := by
  let u := harmU k
  let I := integerThetaSum (harmW k) (growingAnchor k)
  let B := integerThetaTerm (harmW k) 1
  let D := finSum (fun j => thetaDirichletCell (harmW k) (j + 1))
    (growingAnchor k + 1)
  let E := integerThetaTerm (harmW k) (growingAnchor k + 2)
  have hsum : lowerSixDirichletSum k ≈
      Q'.ofNat 4 * D +
        -(lowerSixDirichletProfile k * I) := by
    dsimp only [D, I]
    exact lowerSixDirichletSum_eqv k
  refine Q'.eqv_trans _
    (((Q'.ofNat 4 * D +
          -(lowerSixDirichletProfile k * I)) +
        Q'.ofNat 4 * B) + -(Q'.ofNat 4 * E)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ _ hsum)
  · unfold lowerSixDirichletProfile sevenDirichletCoreGap
      sevenDirichletProfile
    dsimp only [u, I, B, D, E]
    exact endpoint_complement_algebra (harmU k)
      (integerThetaSum (harmW k) (growingAnchor k))
      (integerThetaTerm (harmW k) 1)
      (finSum (fun j => thetaDirichletCell (harmW k) (j + 1))
        (growingAnchor k + 1))
      (integerThetaTerm (harmW k) (growingAnchor k + 2))

#print axioms lowerSix_first_adverse_first_recovery_pair_fails
#print axioms lowerSix_payment_eqv_sevenCore_complement

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryPairingFence
