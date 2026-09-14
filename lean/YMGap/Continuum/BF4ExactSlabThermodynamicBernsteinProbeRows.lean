/-
# Actual finite probability rows for the normalized ORIGINAL probe

At every positive degree N, binary words give rational nodes k/N in [0,1]
and nonnegative CReal weights with explicit QCauchy moduli. Their sum is
exactly one. Their first moment is exactly the original normalized
two-step response, with its already-proved strictly positive lower floor
and upper bound 1/2. The certificate returns the nodes and weights as data.

These are the uncoalesced finite Bernstein rows for the SAME T2. Repeated
nodes are intentional; they are not alleged eigenvalues. No spectral
measure convergence, full functional calculus, continuous-time generator,
continuum scaling or Clay conclusion is claimed. Fixed SU(2) nome/spacing.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords
import YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe

namespace YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor (probePresentation)
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)

/-- The known representative of the actual normalized vector, never selected. -/
def probeCauchy : seminorm.Cauchy :=
  realScalarCauchy normalizer normalizerCauchy (centerCauchy (seminorm.constant probePresentation))

theorem probeCauchy_pin : Quotient.mk seminorm.completionSetoid probeCauchy=unitProbe.val := rfl

/-- Degree is n+1, so the denominator is always positive. -/
def node (n : Nat) (p : Word (n+1)) : Q' := Q'.invSucc n * Q'.ofNat (timeCount p)

theorem node_nonnegative (n : Nat) (p : Word (n+1)) : (0 : Q')≤node n p :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos n)) (Q'.ofNat_nonneg _)

theorem node_le_one (n : Nat) (p : Word (n+1)) : node n p≤(1 : Q') := by
  have hc : timeCount p≤n+1 := by have h := counts_sum p; omega
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.ofNat_le_ofNat hc) (Q'.le_of_lt (Q'.invSucc_pos n)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.ofNat_succ_mul_invSucc n)))

def weight (n : Nat) (p : Word (n+1)) : CReal :=
  momentRepresentative probeCauchy (timeCount p) (defectCount p)

def weightCauchy (n : Nat) (p : Word (n+1)) : QCauchy (weight n p).approx :=
  momentCauchy probeCauchy (timeCount p) (defectCount p)

theorem weight_pin (n : Nat) (p : Word (n+1)) :
    Quotient.mk crealSetoid (weight n p)=wordMoment unitProbe.val 0 0 p := by
  rw [← probeCauchy_pin]
  simp only [wordMoment,Nat.zero_add]
  exact (moment_pin probeCauchy (timeCount p) (defectCount p)).symm

theorem weight_nonnegative (n : Nat) (p : Word (n+1)) : leEv czero (weight n p) := by
  have h := BF4ExactSlabThermodynamicBernsteinWords.weight_nonnegative unitProbe.val p
  rw [← weight_pin] at h
  exact h

theorem weight_total (n : Nat) :
    wordSum (n+1) (fun p => Quotient.mk crealSetoid (weight n p))=Quotient.mk crealSetoid cone := by
  simp only [weight_pin]
  exact (weights_total unitProbe.val (n+1)).trans unitProbe_norm

theorem weighted_node_mean (n : Nat) :
    wordSum (n+1) (fun p => RCscale (node n p) (Quotient.mk crealSetoid (weight n p)))=
      Quotient.mk crealSetoid normalizedResponse := by
  simp only [weight_pin,node,← RCscale_RCscale,wordSum_scale,weighted_time_count]
  have hscalar : Q'.eqv (Q'.invSucc n*Q'.ofNat (n+1)) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.ofNat_succ_mul_invSucc n)
  rw [RCscale_RCscale,scale_congr hscalar,RCscale_one]
  exact normalizedResponse_pin

theorem row_mean_floor (n : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' rayleighFloor))
      (wordSum (n+1) (fun p => RCscale (node n p) (Quotient.mk crealSetoid (weight n p)))) := by
  rw [weighted_node_mean]
  exact normalizedResponse_floor

theorem row_mean_upper (n : Nat) :
    RCle (wordSum (n+1) (fun p => RCscale (node n p) (Quotient.mk crealSetoid (weight n p))))
      (Quotient.mk crealSetoid (ofQ' HalfPow.half)) := by
  rw [weighted_node_mean]
  exact normalizedResponse_upper

/-- Finite original probability data, including every weight's usable modulus. -/
def rowCertificate (n : Nat) :
    Σ' points : Word (n+1) → Q', Σ' weights : Word (n+1) → CReal,
      (∀ p,QCauchy (weights p).approx) ×'
      (∀ p,(0 : Q')≤points p ∧ points p≤(1 : Q')) ×'
      (∀ p,leEv czero (weights p)) ×'
      (wordSum (n+1) (fun p => Quotient.mk crealSetoid (weights p))=Quotient.mk crealSetoid cone) ×'
      (wordSum (n+1) (fun p => RCscale (points p) (Quotient.mk crealSetoid (weights p)))=
        completedInner unitProbe.val (twoStepTransfer unitProbe.val)) :=
  ⟨node n,weight n,weightCauchy n,fun p => ⟨node_nonnegative n p,node_le_one n p⟩,
    weight_nonnegative n,weight_total n,(weighted_node_mean n).trans normalizedResponse_pin.symm⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.probeCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.probeCauchy_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.node
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.node_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.node_le_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.weight
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.weightCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.weight_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.weight_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.weight_total
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.weighted_node_mean
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.row_mean_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.row_mean_upper
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows.rowCertificate
