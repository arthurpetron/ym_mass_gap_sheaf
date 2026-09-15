/-
# Exact dyadic differentiability domain of the ORIGINAL time action

The normalized quotients q_n u=2^n(u-S_n u) satisfy T2(q_n u)=Q_n u,
where the OLD Q_n converge to J u on the original completion.
Thus any supplied norm-convergence rate q_n u -> v forces J u=T2 v.
Conversely, the whole-graph Taylor bound computes such a rate, using
the original graph radius and an explicit dyadic cutoff.

These maps identify the constructed graph EXACTLY with the domain of
modulus-bearing negative dyadic derivatives. The preceding real-time
theorem proves the stronger full positive-real-increment derivative
for every graph point. No graph or generator hypothesis is added.
This is the original REAL space at fixed SU(2), nome 1/1024 and spacing,
in T2-time units, not a physical Hamiltonian/spectral, continuum or
all-group Clay theorem.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RegularLinearGeometricModulus (halfCutoff halfCutoff_spec)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation (completedDist_two_segment)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows (completed_eq_of_small)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (smul_norm)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (full_mesh_time)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay (defect time_defect)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages (smul_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative (mesh_normalization mesh_value)
open YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative (remainder radius radius_positive mesh_taylor_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation (GraphPoint)

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

/-- Negative difference quotient on an arbitrary original state, without T2 smoothing. -/
def quotient (depth : Nat) (u : Completion) : Completion :=
  completedSmul (Q'.ofNat (2^depth)) (defect depth u)

theorem quotient_transfer (depth : Nat) (u : Completion) :
    twoStepTransfer (quotient depth u)=differenceQuotient depth u := by
  unfold quotient differenceQuotient twoStepTransfer
  rw [completedTime_smul]
  change completedSmul (Q'.ofNat (2^depth)) (twoStepTransfer (defect depth u))=
    completedSmul (Q'.ofNat (2^depth)) (defect depth (twoStepTransfer u))
  rw [← full_mesh_time depth (defect depth u),time_defect,full_mesh_time]

theorem normalization (depth : Nat) : Q'.eqv (value ⟨depth,1⟩*Q'.ofNat (2^depth)) 1 := by
  have h := mesh_normalization depth 0
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv _))) h

theorem quotient_remainder (depth : Nat) (u v : Completion) :
    completedSub (quotient depth u) v=
      completedSmul (Q'.ofNat (2^depth)) (remainder depth 1 u v) := by
  unfold remainder
  rw [smul_sub,completedSmul_mul,completedSmul_congr
    (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (normalization depth)),completedSmul_one]
  rfl

theorem normalize_square (c t epsilon : Q') (h : Q'.eqv (t*c) 1) :
    RCscale (c*c) (rat ((t*t)*epsilon))=rat epsilon := by
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro _
  have hp : Q'.eqv ((c*c)*((t*t)*epsilon)) ((t*c)*((t*c)*epsilon)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.mul (.mul (.var 1) (.var 0)) (.var 2)))
      (by decide) (fun | 0 => c | 1 => t | _ => epsilon)
  have hinner : Q'.eqv ((t*c)*epsilon) epsilon :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.one_mul_eqv _)
  exact Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) hinner))

def rate (U V : seminorm.Cauchy) (epsilon : Q') : Nat := halfCutoff (radius U V epsilon)

theorem rate_small (U V : seminorm.Cauchy) (epsilon : Q') (n : Nat) (hn : rate U V epsilon≤n) :
    value ⟨n,1⟩≤radius U V epsilon := by
  have hvalue : Q'.eqv (value ⟨n,1⟩) (HalfPow.half^n) :=
    Q'.eqv_trans _ _ _ (mesh_value n 1) (Q'.one_mul_eqv _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hvalue)
    (Q'.le_trans' _ _ _ (half_pow_antitone _ n hn) (halfCutoff_spec _ (radius_positive U V epsilon)))

theorem quotient_bound (U V : seminorm.Cauchy)
    (hgraph : derivativeAction (point U)=twoStepTransfer (point V))
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : rate U V epsilon≤n) :
    RCle (completedDist (quotient n (point U)) (point V)) (rat epsilon) := by
  unfold completedDist
  rw [quotient_remainder,smul_norm]
  have h := RCscale_mono (SumOfSquares.q_mul_self_nonneg (Q'.ofNat (2^n)))
    (mesh_taylor_bound U V hgraph epsilon he n 1 (rate_small U V epsilon n hn))
  rw [normalize_square _ _ _ (normalization n)] at h
  exact h

/-- Any actual modulus-bearing dyadic derivative lies in the ORIGINAL graph. -/
theorem graph_of_quotient_bound (U : seminorm.Cauchy) (v : Completion) (modulus : Q' → Nat)
    (h : ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,modulus epsilon≤n →
      RCle (completedDist (quotient n (point U)) v) (rat epsilon)) :
    derivativeAction (point U)=twoStepTransfer v := by
  apply completed_eq_of_small
  intro epsilon he
  let delta := quarter epsilon
  have hd : (0 : Q')<delta := quarter_pos he
  let n := max (derivativeRate U delta) (modulus delta)
  have hleft := derivative_bound U delta hd n (Nat.le_max_left _ _)
  rw [completedDist_symm] at hleft
  have hright := RCle_trans (completedTime_distance_contraction 2 (quotient n (point U)) v)
    (h delta hd n (Nat.le_max_right _ _))
  change RCle (completedDist (twoStepTransfer (quotient n (point U))) (twoStepTransfer v)) _ at hright
  rw [quotient_transfer] at hright
  exact completedDist_two_segment _ _ _ epsilon hleft hright

/-- Forward domain map retains its computed convergence rate as data. -/
def derivativeCertificate (U V : seminorm.Cauchy)
    (hgraph : derivativeAction (point U)=twoStepTransfer (point V)) :
    {modulus : Q' → Nat // ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,modulus epsilon≤n →
      RCle (completedDist (quotient n (point U)) (point V)) (rat epsilon)} :=
  ⟨rate U V,quotient_bound U V hgraph⟩

/-- Reverse domain map, without assuming the graph equation or choosing a state. -/
def graphFromDerivative (U : seminorm.Cauchy) (v : Completion) (modulus : Q' → Nat)
    (h : ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,modulus epsilon≤n →
      RCle (completedDist (quotient n (point U)) v) (rat epsilon)) : GraphPoint :=
  ⟨point U,v,graph_of_quotient_bound U v modulus h⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.quotient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.quotient_transfer
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.normalization
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.quotient_remainder
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.normalize_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.rate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.rate_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.quotient_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.graph_of_quotient_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.derivativeCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain.graphFromDerivative
