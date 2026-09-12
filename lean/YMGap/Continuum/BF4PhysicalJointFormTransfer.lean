/-
# The actual BF4 conditional operator on its reflected joint-form completion

At every finite cutoff the physical marginal-weighted form D and normalized
reflected joint form E satisfy E(a,b) = D(a,Pb), where P is the SAME physical
row-conditional macro operator. The positive-contraction identity constructs P
on E's completion without assuming equivalent norms or a strict spectral gap.
The canonical comparison decreases norms, intertwines P, transports its unit
fixed stationary vacuum, and preserves all moments with one extra P insertion.

This is a finite-cutoff physical bridge, not yet a cutoff-coherent operator on
BF4PhysicalCubeCompletion's all-spin stable RAW form. It does not identify a
macro iteration with a geometric Euclidean time shift, isolate the vacuum,
prove a strict gap, or construct a thermodynamic/continuum limit.
-/

import YMGap.Continuum.PositiveContractionOneStepCompletion
import YMGap.Continuum.BF4PhysicalMarkovGNSCompletion

namespace YMGap.Continuum.BF4PhysicalJointFormTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.PositiveContractionOneStepForm
open YMGap.Continuum.PositiveContractionOneStepCompletion
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

variable (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)

local notation "D" => centralPhysicalSmulGNS w hw K half
local notation "S" => centralPhysicalMarkovSymbol w hw K half
private theorem physical_form_selfAdjoint (a b : (D).toGNSData.V) :
    (D).toGNSData.B a ((S).Dv b) ≈ (D).toGNSData.B ((S).Dv a) b :=
  centralPhysicalMarkovApply_self_adjoint w hw K half a b

private theorem physical_form_positive (a : (D).toGNSData.V) :
    (0 : Q') ≤ (D).toGNSData.B a ((S).Dv a) :=
  centralPhysicalMarkovApply_positive w hw K half a

private theorem physical_form_upper (a : (D).toGNSData.V) :
    (D).toGNSData.B a ((S).Dv a) ≤ (D).toGNSData.B a a :=
  (centralPhysicalMarkovApply_form_interval w hw K half a).2

private theorem physical_symbol_sub (a b : (D).toGNSData.V) :
    (D).toGNSData.veq ((S).Dv ((D).toGNSData.sub a b))
      ((D).toGNSData.sub ((S).Dv a) ((S).Dv b)) :=
  centralPhysicalMarkovApply_sub w hw K half a b

local notation "hsa" => physical_form_selfAdjoint w hw K half
local notation "hpos" => physical_form_positive w hw K half
local notation "hupper" => physical_form_upper w hw K half
local notation "hsub" => physical_symbol_sub w hw K half

def physicalJointSmulGNS : SmulGNSData := oneStepSmulGNSData D (S).Dv hsa hpos

def physicalJointSymbol : DiagonalTransferSymbol (physicalJointSmulGNS w hw K half) :=
  oneStepSymbol D S hsub hsa hpos hupper

def physicalJointBilinear (a b : EdgeLabelling → Q') : Q' :=
  listQSum (fun source => listQSum (fun target => (a source * b target) *
    centralNormalizedPhysicalReflectedKernel w hw K half source target)
    (centralPositiveHalfStates w hw K half)) (centralPositiveHalfStates w hw K half)

private theorem four_mul_reorder (a b c d : Q') :
    (a * b) * (c * d) ≈ (b * d) * (a * c) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- Full bilinear identification with the original partition-normalized OS entries. -/
theorem physicalJoint_B_eq_joint (a b : EdgeLabelling → Q') :
    (physicalJointSmulGNS w hw K half).toGNSData.B a b ≈
      physicalJointBilinear w hw K half a b := by
  change centralPhysicalWeightedInner w hw K half a
    (centralPhysicalMarkovApply w hw K half b) ≈ _
  unfold centralPhysicalWeightedInner centralPhysicalMarkovApply physicalJointBilinear
  apply listQSum_congr_on
  intro source hsource
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_mul_left _ _ _)) ?_
  apply listQSum_congr_on
  intro target _
  exact Q'.eqv_trans _ _ _ (four_mul_reorder _ _ _ _)
    (Q'.mul_eqv_congr_left _ _ _ (centralPhysicalMarginal_mul_conditional_eqv_joint hsource))

/-- Zero-marginal filtering changes neither this norm nor the full normalized OS quadratic. -/
theorem physicalJoint_norm_eq_full (a : EdgeLabelling → Q') :
    (physicalJointSmulGNS w hw K half).toGNSData.B a a ≈
      centralNormalizedFullPhysicalReflectionQuadratic w hw K half a :=
  Q'.eqv_trans _ _ _ (centralPhysicalWeightedMarkovQuadratic_eq_joint w hw K half a)
    (centralPhysicalJointQuadratic_eq_normalizedFull w hw K half a)

/-- The complete physical OS quadratic contracts under its actual conditional action. -/
theorem physicalJoint_full_contraction (a : EdgeLabelling → Q') :
    centralNormalizedFullPhysicalReflectionQuadratic w hw K half
        (centralPhysicalMarkovApply w hw K half a) ≤
      centralNormalizedFullPhysicalReflectionQuadratic w hw K half a := by
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (physicalJoint_norm_eq_full w hw K half _))
    (Q'.le_trans' _ _ _ (oneStep_contraction (D).toGNSData (S).Dv hsa hpos hupper a)
      (Q'.le_of_eqv (physicalJoint_norm_eq_full w hw K half a)))

private theorem cancel_common_partition (a b Z : Q') (hZ : (0 : Q') < Z)
    (h : Q'.divPos a Z hZ ≤ Q'.divPos b Z hZ) : a ≤ b := by
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ Z h (Q'.le_of_lt hZ)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.divPos_mul_eqv a Z hZ))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.divPos_mul_eqv b Z hZ)))

/-- The same contraction holds for the unnormalized full OS form: the common
positive partition factor cancels, without an estimate on its size. -/
theorem physicalRaw_full_contraction (a : EdgeLabelling → Q') :
    centralFullPhysicalReflectionQuadratic w K half
        (centralPhysicalMarkovApply w hw K half a) ≤
      centralFullPhysicalReflectionQuadratic w K half a := by
  exact cancel_common_partition _ _
    (slabParametricKPhysicalPartition w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos hw K (centralExtent half))
    (physicalJoint_full_contraction w hw K half a)

abbrev PhysicalJointCompletion := GNSCompletionSpace (physicalJointSmulGNS w hw K half).toGNSData

def physicalJointTransfer : PhysicalJointCompletion w hw K half → PhysicalJointCompletion w hw K half :=
  (physicalJointSymbol w hw K half).TqSymb

def physicalJointComparison : CentralPhysicalGNSCompletion w hw K half → PhysicalJointCompletion w hw K half :=
  comparison D S hsa hpos hupper

theorem physicalJointComparison_embed (a : EdgeLabelling → Q') :
    physicalJointComparison w hw K half (embedV (D).toGNSData a) =
      embedV (physicalJointSmulGNS w hw K half).toGNSData a := rfl

theorem physicalJointTransfer_embed (a : EdgeLabelling → Q') :
    physicalJointTransfer w hw K half (embedV (physicalJointSmulGNS w hw K half).toGNSData a) =
      embedV (physicalJointSmulGNS w hw K half).toGNSData
        (centralPhysicalMarkovApply w hw K half a) :=
  (physicalJointSymbol w hw K half).TqSymb_embed a

theorem physicalJointComparison_intertwines (x : CentralPhysicalGNSCompletion w hw K half) :
    physicalJointComparison w hw K half (centralPhysicalCompletedMarkovTransfer w hw K half x) =
      physicalJointTransfer w hw K half (physicalJointComparison w hw K half x) :=
  comparison_intertwines D S hsub hsa hpos hupper x

theorem physicalJointComparison_contraction (x : CentralPhysicalGNSCompletion w hw K half) :
    CReal.RCle ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
        (physicalJointComparison w hw K half x) (physicalJointComparison w hw K half x))
      ((D).toGNSData.cinnerCompl x x) :=
  comparison_contraction D S hsa hpos hupper x

/-- The actual finite stationary vacuum, transported rather than freely chosen. -/
def physicalJointVacuum : PhysicalJointCompletion w hw K half :=
  physicalJointComparison w hw K half (centralPhysicalCompletedVacuum w hw K half)

theorem physicalJointVacuum_fixed :
    physicalJointTransfer w hw K half (physicalJointVacuum w hw K half) =
      physicalJointVacuum w hw K half := by
  exact Eq.trans (physicalJointComparison_intertwines w hw K half _).symm
    (congrArg (physicalJointComparison w hw K half)
      (centralPhysicalCompletedMarkovTransfer_vacuum_fixed w hw K half))

theorem physicalJointVacuum_norm_one :
    (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
        (physicalJointVacuum w hw K half) (physicalJointVacuum w hw K half) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 1) := by
  refine Eq.trans (comparison_inner D S hsa hpos hupper
    (centralPhysicalCompletedVacuum w hw K half) (centralPhysicalCompletedVacuum w hw K half)) ?_
  change (D).toGNSData.cinnerCompl (centralPhysicalCompletedVacuum w hw K half)
    (centralPhysicalCompletedMarkovTransfer w hw K half (centralPhysicalCompletedVacuum w hw K half)) = _
  rw [centralPhysicalCompletedMarkovTransfer_vacuum_fixed]
  exact centralPhysicalCompletedVacuum_inner_self_eq_one w hw K half

def physicalJointLinearTransfer : LinearTransferOperator (physicalJointSmulGNS w hw K half) :=
  (physicalJointSymbol w hw K half).toLinearTransfer (physicalJointVacuum w hw K half)
    (completed_selfAdjoint D S hsub hsa hpos hupper)
    (completed_positive D S hsub hsa hpos hupper)
    (completed_contraction D S hsub hsa hpos hupper)

/-- Exact same-object macro moments. This is not an identification with geometric time. -/
theorem physicalJointComparison_moments (n : Nat) (x y : CentralPhysicalGNSCompletion w hw K half) :
    (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
        (physicalJointComparison w hw K half x)
        (actionIterate (physicalJointTransfer w hw K half) n (physicalJointComparison w hw K half y)) =
      (D).toGNSData.cinnerCompl x (actionIterate (centralPhysicalCompletedMarkovTransfer w hw K half) (n+1) y) :=
  comparison_moments D S hsub hsa hpos hupper n x y

def PhysicalJointVacuumOrthogonal (x : PhysicalJointCompletion w hw K half) : Prop :=
  (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl x (physicalJointVacuum w hw K half) = CReal.RCzero

/-- Centering uses the same stationary vacuum on both sides of the comparison. -/
theorem physicalJointComparison_vacuum_inner (x : CentralPhysicalGNSCompletion w hw K half) :
    (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
        (physicalJointComparison w hw K half x) (physicalJointVacuum w hw K half) =
      (D).toGNSData.cinnerCompl x (centralPhysicalCompletedVacuum w hw K half) := by
  refine Eq.trans (comparison_inner D S hsa hpos hupper x
    (centralPhysicalCompletedVacuum w hw K half)) ?_
  exact congrArg ((D).toGNSData.cinnerCompl x)
    (centralPhysicalCompletedMarkovTransfer_vacuum_fixed w hw K half)

theorem physicalJointComparison_vacuumOrthogonal_iff (x : CentralPhysicalGNSCompletion w hw K half) :
    PhysicalJointVacuumOrthogonal w hw K half (physicalJointComparison w hw K half x) ↔
      CentralPhysicalCompletedVacuumOrthogonal w hw K half x := by
  unfold PhysicalJointVacuumOrthogonal CentralPhysicalCompletedVacuumOrthogonal
  rw [physicalJointComparison_vacuum_inner]

theorem physicalJointVacuumOrthogonal_preserved {x : PhysicalJointCompletion w hw K half}
    (hx : PhysicalJointVacuumOrthogonal w hw K half x) :
    PhysicalJointVacuumOrthogonal w hw K half (physicalJointTransfer w hw K half x) := by
  unfold PhysicalJointVacuumOrthogonal at hx ⊢
  have he : (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
      (physicalJointTransfer w hw K half x) (physicalJointVacuum w hw K half) =
      (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl x
        (physicalJointTransfer w hw K half (physicalJointVacuum w hw K half)) :=
    completed_selfAdjoint D S hsub hsa hpos hupper x (physicalJointVacuum w hw K half)
  exact Eq.trans he (Eq.trans
    (congrArg ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl x)
      (physicalJointVacuum_fixed w hw K half)) hx)

end YMGap.Continuum.BF4PhysicalJointFormTransfer

#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointSmulGNS
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointSymbol
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJoint_B_eq_joint
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJoint_norm_eq_full
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJoint_full_contraction
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalRaw_full_contraction
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointComparison_embed
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointTransfer_embed
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointComparison_intertwines
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointComparison_contraction
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointVacuum_fixed
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointVacuum_norm_one
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointLinearTransfer
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointComparison_moments
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointComparison_vacuum_inner
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointComparison_vacuumOrthogonal_iff
#print axioms YMGap.Continuum.BF4PhysicalJointFormTransfer.physicalJointVacuumOrthogonal_preserved
