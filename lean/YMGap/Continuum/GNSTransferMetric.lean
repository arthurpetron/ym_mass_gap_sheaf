/-
# Squared-distance laws for a completed GNS transfer

The completed GNS pairing determines a squared distance. Self-adjointness
forces a transfer operator to preserve subtraction, so its supplied norm
contraction also contracts distances between arbitrary completed vectors.
These are generic ordinary-GNS facts; no physical carrier identification is
asserted here.
-/

import YMGap.Continuum.GNSDenseCompletionLaws
import YMGap.Continuum.RCBilinearDifference
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
import YMGap.Continuum.CRealSeminormCompletedApproximation

namespace YMGap.Continuum.GNSTransferMetric

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter)

/-- The squared distance on the existing completed GNS carrier. -/
def distanceSq (D : GNSData) (x y : GNSCompletionSpace D) : RC :=
  D.cinnerCompl (D.cSub x y) (D.cSub x y)

/-- The quadratic triangle inequality, descended from the rational GNS
distance of the supplied Cauchy representatives. -/
theorem distance_triangle (D : GNSData) (x y z : GNSCompletionSpace D) :
    RCle (distanceSq D x z)
      (RCadd
        (RCadd (distanceSq D x y) (distanceSq D x y))
        (RCadd (distanceSq D y z) (distanceSq D y z))) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z
  exact CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy X Z))
    (CReal.convergesTo_add
      (CReal.convergesTo_add
        (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy X Y))
        (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy X Y)))
      (CReal.convergesTo_add
        (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy Y Z))
        (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy Y Z))))
    (fun n => CReal.leEv_of_le
      (CReal.ofQ'_le_ofQ' (D.distSqQ_triangle (X.seq n) (Y.seq n) (Z.seq n))))

/-- Two quarter-tolerance distance bounds yield one full-tolerance bound. -/
theorem distance_two_segment (D : GNSData) (x y z : GNSCompletionSpace D)
    (epsilon : Q')
    (hxy : RCle (distanceSq D x y)
      (Quotient.mk crealSetoid (ofQ' (quarter epsilon))))
    (hyz : RCle (distanceSq D y z)
      (Quotient.mk crealSetoid (ofQ' (quarter epsilon)))) :
    RCle (distanceSq D x z)
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hsum := RCadd_le_add (RCadd_le_add hxy hxy) (RCadd_le_add hyz hyz)
  have h := RCle_trans (distance_triangle D x y z) hsum
  have hbudget : RCle
      (Quotient.mk crealSetoid (ofQ'
        ((quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
    leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (ExpNeg.two_halves (HalfPow.half * epsilon))
          (ExpNeg.two_halves (HalfPow.half * epsilon)))
        (ExpNeg.two_halves epsilon)))
  exact RCle_trans h hbudget

/-- A distance below every positive rational tolerance is zero. The proof
constructs the original Cauchy-null witness directly, with half the requested
tolerance reserved for the eventual-order slack. -/
theorem eq_of_forall_small (D : GNSData) (x y : GNSCompletionSpace D)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon →
      RCle (distanceSq D x y) (Quotient.mk crealSetoid (ofQ' epsilon))) :
    x = y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h
  apply Quotient.sound
  intro epsilon hepsilon
  have hhalf : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨N, hN⟩ := GNSDenseCompletionExtension.distance_eventually_le
    D X Y (HalfPow.half * epsilon)
    (h (HalfPow.half * epsilon) hhalf)
    (HalfPow.half * epsilon) hhalf
  refine ⟨N, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (hN n hn)
    (Q'.le_of_eqv (ExpNeg.two_halves epsilon))

/-- Self-adjointness and nondegeneracy force subtraction preservation; no
linearity field is added to the transfer interface. -/
theorem transfer_sub (D : GNSData) (T : TransferOperator D.gnsComplete)
    (x y : GNSCompletionSpace D) :
    T.T (D.cSub x y) = D.cSub (T.T x) (T.T y) := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  calc
    D.cinnerCompl (T.T (D.cSub x y)) z =
        D.cinnerCompl (D.cSub x y) (T.T z) := T.selfAdjoint _ _
    _ = RCsub (D.cinnerCompl x (T.T z)) (D.cinnerCompl y (T.T z)) :=
      D.cinnerCompl_cSub_left x y (T.T z)
    _ = RCsub (D.cinnerCompl (T.T x) z) (D.cinnerCompl (T.T y) z) := by
      have hx : D.cinnerCompl (T.T x) z = D.cinnerCompl x (T.T z) :=
        T.selfAdjoint x z
      have hy : D.cinnerCompl (T.T y) z = D.cinnerCompl y (T.T z) :=
        T.selfAdjoint y z
      rw [hx, hy]
    _ = D.cinnerCompl (D.cSub (T.T x) (T.T y)) z :=
      (D.cinnerCompl_cSub_left (T.T x) (T.T y) z).symm

/-- Norm contraction becomes pairwise squared-distance contraction. -/
theorem transfer_nonexpansive (D : GNSData) (T : TransferOperator D.gnsComplete)
    (x y : GNSCompletionSpace D) :
    RCle (distanceSq D (T.T x) (T.T y)) (distanceSq D x y) := by
  unfold distanceSq
  rw [← transfer_sub D T x y]
  exact T.contraction (D.cSub x y)

/-- Two nonexpansive maps from a represented constructive completion agree
everywhere if they agree on its original dense carrier. The destination can
be any GNS datum, including a reflected positive-time datum; no ordinary
Wilson form, continuum-existence hypothesis or rational dense image is used. -/
theorem maps_eq_of_dense
    {S : CRealSeminormCompletion.SquaredSeminorm}
    (source : CRealSeminormCompletedApproximation.DistanceData S)
    (D : GNSData) (f g : S.Completion → GNSCompletionSpace D)
    (hf : ∀ x y, RCle (distanceSq D (f x) (f y)) (source.completedDist x y))
    (hg : ∀ x y, RCle (distanceSq D (g x) (g y)) (source.completedDist x y))
    (dense : ∀ s, f (S.embedRep s) = g (S.embedRep s))
    (x : S.Completion) : f x = g x :=
  CRealSeminormCompletedApproximation.maps_eq_of_dense source
    (distanceSq D) (eq_of_forall_small D) (distance_two_segment D) f g hf hg dense x

end YMGap.Continuum.GNSTransferMetric

#print axioms YMGap.Continuum.GNSTransferMetric.distanceSq
#print axioms YMGap.Continuum.GNSTransferMetric.distance_triangle
#print axioms YMGap.Continuum.GNSTransferMetric.distance_two_segment
#print axioms YMGap.Continuum.GNSTransferMetric.eq_of_forall_small
#print axioms YMGap.Continuum.GNSTransferMetric.transfer_sub
#print axioms YMGap.Continuum.GNSTransferMetric.transfer_nonexpansive
#print axioms YMGap.Continuum.GNSTransferMetric.maps_eq_of_dense
