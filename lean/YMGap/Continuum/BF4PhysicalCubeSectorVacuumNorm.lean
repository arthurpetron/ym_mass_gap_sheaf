/-
# A positive norm for the actual stationary sector vector

At the fixed anchor w=1/400 and extent one, the zero-labelled state belongs
to the sector event. Its normalized diagonal weight alone gives the explicit
floor 64/65 for the sector's squared norm, at EVERY representation cutoff.
The cutoff limit is pinned to the reflected completion's actual pairing.

This constructs a nonzero stationary vector, not an isolated vacuum: the
orthogonal complement is invariant under the same conditional transfer, but
no strict contraction, geometric-time identification, or continuum gap is
asserted. The numerical floor is not uniform in the coupling.
-/

import YMGap.Continuum.BF4PhysicalCubeSectorVacuum
import YMGap.Continuum.FinitePositiveMaximumEntry

namespace YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeCompletion
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeSectorIndicator
open YMGap.Continuum.BF4PhysicalCubeSectorVacuum
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FinitePositiveMaximumEntry
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "floor" => Q'.mkPos 64 65 (by decide)

/-- The norm witness retains the original physical cutoff approximations. -/
def sectorVacuumNorm : CReal :=
  innerLimit (w := anchorCoupling) (by decide) (by decide) 0
    sectorLinearObservable sectorLinearObservable

def sectorVacuumNormRegularity : CReal.InnerRegularity sectorVacuumNorm :=
  innerLimitInnerRegularity (w := anchorCoupling) (by decide) (by decide) 0
    sectorLinearObservable sectorLinearObservable

/-- A single positive diagonal entry pays the claimed fixed-anchor floor. -/
theorem vacuumRow_floor (K : Nat) :
    floor ≤ centralPhysicalRowMarginal anchorCoupling (by decide) K 0 zeroEdgeLabelling := by
  have hrecip := inversePartitionLimit_approx (w := anchorCoupling) (by decide) (by decide) K
  have hraw := one_le_centralPhysicalReflectedKernel_vacuum (w := anchorCoupling) (by decide) K 0
  have hZ := slabParametricKPhysicalPartition_pos (w := anchorCoupling) (by decide) K 1
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.recipPos (slabParametricKPhysicalPartition anchorCoupling K 1) hZ) hraw
    (Q'.le_of_lt (Q'.recipPos_pos _ hZ))
  have hentry : floor ≤ centralNormalizedPhysicalReflectedKernel
      anchorCoupling (by decide) K 0 zeroEdgeLabelling zeroEdgeLabelling := by
    exact Q'.le_trans' _ _ _ (inversePartitionLimit_anchor_floor K)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hrecip)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) hscaled))
  exact Q'.le_trans' _ _ _ hentry
    (le_listQSum_of_mem_nonnegative
      (centralNormalizedPhysicalReflectedKernel anchorCoupling (by decide) K 0 zeroEdgeLabelling)
      (centralHalfStates K 0) zeroEdgeLabelling
      (zeroEdgeLabelling_mem_centralHalfStates K 0)
      (fun state _ => centralNormalizedPhysicalReflectedKernel_nonnegative (by decide) K 0 _ state))

theorem sectorVacuumNorm_floor (K : Nat) : floor ≤ sectorVacuumNorm.approx K := by
  have hterm := le_listQSum_of_mem_nonnegative
    (fun state => centralPhysicalRowMarginal anchorCoupling (by decide) K 0 state *
      (cubeSectorIndicator state * cubeSectorIndicator state))
    (centralPositiveHalfStates anchorCoupling (by decide) K 0) zeroEdgeLabelling
    (zeroEdgeLabelling_mem_centralPositiveHalfStates (by decide) K 0)
    (fun state _ => Q'.mul_nonneg _ _
      (centralPhysicalRowMarginal_nonnegative (by decide) K 0 state)
      (Q'.mul_nonneg _ _ (cubeSectorObservable.nonnegative state) (cubeSectorObservable.nonnegative state)))
  change centralPhysicalRowMarginal anchorCoupling (by decide) K 0 zeroEdgeLabelling *
    (cubeSectorIndicator zeroEdgeLabelling * cubeSectorIndicator zeroEdgeLabelling) ≤ _ at hterm
  rw [cubeSectorIndicator_zero] at hterm
  have hroot : centralPhysicalRowMarginal anchorCoupling (by decide) K 0 zeroEdgeLabelling *
      ((1 : Q') * 1) ≈ centralPhysicalRowMarginal anchorCoupling (by decide) K 0 zeroEdgeLabelling :=
    Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv 1)) (Q'.mul_one_eqv _)
  have hstage := innerLimit_approx_eqv_stage (w := anchorCoupling)
    (by decide) (by decide) 0 K sectorLinearObservable sectorLinearObservable
  exact Q'.le_trans' _ _ _ (vacuumRow_floor K)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hroot)
      (Q'.le_trans' _ _ _ hterm (Q'.ge_of_eqv hstage)))

/-- The scalar witness is the norm of this SAME completed stationary vector. -/
theorem reflectedSectorVacuum_norm :
    cubeReflectedInner reflectedSectorVacuum reflectedSectorVacuum =
      Quotient.mk CReal.crealSetoid sectorVacuumNorm := by
  unfold reflectedSectorVacuum
  rw [sectorToReflected_pairing, sectorVacuum_global]
  unfold completedReflectedForm
  rw [globalSectorVacuum_fixed]
  exact centralPhysicalCutoffCompletedInner_embedRep (w := anchorCoupling)
    (by decide) (by decide) 0 sectorLinearObservable sectorLinearObservable

theorem reflectedSectorVacuum_norm_floor :
    CReal.RCle (Quotient.mk CReal.crealSetoid (CReal.ofQ' floor))
      (cubeReflectedInner reflectedSectorVacuum reflectedSectorVacuum) := by
  rw [reflectedSectorVacuum_norm]
  intro epsilon hepsilon
  exact ⟨0, fun K _ => Q'.le_trans' _ _ _ (sectorVacuumNorm_floor K)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon))⟩

theorem cubeReflectedInner_zero_left (x : CubeReflectedCompletion) :
    cubeReflectedInner (cubeReflectedEmbed []) x = CReal.RCzero := by
  have h := cubeReflectedInner_comparison (embedSpan anchorCoupling (by decide) []) (reflectedToRaw x)
  rw [rawToReflected_embed, reflected_raw_inverse] at h
  have hz : completedInner anchorCoupling (by decide)
      (embedSpan anchorCoupling (by decide) []) (reflectedToRaw x) = CReal.RCzero :=
    (D).cinnerCompl_embedZero_left (reflectedToRaw x)
  rw [hz] at h
  exact Eq.trans h (Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.zero_mul_eqv _)))

theorem reflectedSectorVacuum_ne_zero : reflectedSectorVacuum ≠ cubeReflectedEmbed [] := by
  intro hzero
  have h := reflectedSectorVacuum_norm
  rw [hzero, cubeReflectedInner_zero_left] at h
  have heq : CReal.Equiv sectorVacuumNorm CReal.czero := Quotient.exact h.symm
  obtain ⟨N, hN⟩ := heq (Q'.mkPos 1 4 (by decide)) (by decide)
  have hbad := Q'.le_trans' _ _ _ (sectorVacuumNorm_floor N) (hN N (Nat.le_refl N)).1
  exact (by decide : ¬ floor ≤ (0 : Q') + Q'.mkPos 1 4 (by decide)) hbad

/-- Orthogonality to the constructed stationary vector in the actual E form. -/
def CubeSectorVacuumComplement :=
  {x : CubeReflectedCompletion // cubeReflectedInner reflectedSectorVacuum x = CReal.RCzero}

theorem cubeTransfer_preserves_vacuumComplement (x : CubeSectorVacuumComplement) :
    cubeReflectedInner reflectedSectorVacuum (cubeTransfer x.val) = CReal.RCzero := by
  rw [← cubeTransfer_selfAdjoint, reflectedSectorVacuum_fixed]
  exact x.property

/-- Restriction of the existing operator, with no new dynamics or gap input. -/
def sectorComplementTransfer (x : CubeSectorVacuumComplement) : CubeSectorVacuumComplement :=
  ⟨cubeTransfer x.val, cubeTransfer_preserves_vacuumComplement x⟩

theorem sectorComplementTransfer_selfAdjoint (x y : CubeSectorVacuumComplement) :
    cubeReflectedInner (sectorComplementTransfer x).val y.val =
      cubeReflectedInner x.val (sectorComplementTransfer y).val :=
  cubeTransfer_selfAdjoint x.val y.val

theorem sectorComplementTransfer_positive (x : CubeSectorVacuumComplement) :
    CReal.RCnonneg (cubeReflectedInner (sectorComplementTransfer x).val x.val) :=
  cubeTransfer_positive x.val

theorem sectorComplementTransfer_contraction (x : CubeSectorVacuumComplement) :
    CReal.RCle (cubeReflectedInner (sectorComplementTransfer x).val (sectorComplementTransfer x).val)
      (cubeReflectedInner x.val x.val) := cubeTransfer_contraction x.val

end YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm

#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.sectorVacuumNorm
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.sectorVacuumNormRegularity
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.vacuumRow_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.sectorVacuumNorm_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.reflectedSectorVacuum_norm
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.reflectedSectorVacuum_norm_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.cubeReflectedInner_zero_left
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.reflectedSectorVacuum_ne_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.CubeSectorVacuumComplement
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.cubeTransfer_preserves_vacuumComplement
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.sectorComplementTransfer
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.sectorComplementTransfer_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.sectorComplementTransfer_positive
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm.sectorComplementTransfer_contraction
