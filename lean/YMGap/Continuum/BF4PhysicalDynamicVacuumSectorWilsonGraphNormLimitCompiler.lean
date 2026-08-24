/-
# Dynamic physical-time all-vector graph-norm limit compiler

At every cutoff, `DynamicVacuumSectorCompletedFamily` already carries a
squared-norm contraction for every vector in its completed vacuum complement.
For a continuum operator gap, the relevant finite operator is not one lattice
step: it is the scheduled power representing one unit of physical time.

This module states the choice-free graph-norm compatibility needed to pass
that all-vector finite estimate to the selected Wilson completion.  Explicit
continuum Cauchy representatives are approximated by vectors in the varying
completed BF4 sectors, and explicit `CReal` norm representatives converge for
both the vector and its scheduled image.  The limit of the exact scheduled
one-unit squared rates is pinned, by `CReal.Equiv`, to the square of the
selected Wilson separator.

From those data the compiler constructs `WilsonOperatorNormGapPin`, quantified
over every completed vacuum-orthogonal Wilson vector.  This is the correct
all-vector direction; no single observable is used to infer the operator gap.

No graph-norm approximation, rate-limit pin, projective measure, Wilson GNS
datum, or continuum Yang--Mills theory is inhabited here.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
import YMGap.Continuum.BF4PhysicalModulatedGapLimitStability

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. Choice-free physical-time graph-norm data -/

/-- Representative-level graph-norm convergence for the scheduled one-unit
physical-time powers of one dynamic BF4 family.

All finite approximants are requested only after a proof that the selected
continuum representative lies in the vacuum complement.  Thus the interface
does not falsely approximate vacuum-shifted vectors by mean-zero vectors. -/
structure DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
    (family : DynamicVacuumSectorCompletedFamily 0)
    (ratePower : NormalizedMovingCubeSampledRatePowerLimit family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 3 where
  /-- The exact scheduled one-unit squared-rate limit is the square of the
  separator used by the selected Wilson transfer. -/
  rateLimitPinned : CReal.Equiv
    (ratePower.limitRepresentative 1)
    (CReal.ofQ'
      (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep))
  /-- A representative-level lift of the selected continuum transfer. -/
  transferredRepresentative :
    SelectedWilsonCauchy D -> SelectedWilsonCauchy D
  /-- The lift denotes exactly the quotient-level selected transfer. -/
  transferredRepresentative_class : forall X,
    selectedWilsonPoint D (transferredRepresentative X) =
      D.timeTranslation.op.T (selectedWilsonPoint D X)
  /-- A finite completed-sector approximation of each explicitly represented
  continuum vacuum-complement vector. -/
  approximant : forall (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      (scale : Nat) ->
        CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
          (family.nome_pos scale) (family.nome_lt_one scale) 0
  /-- An explicit representative of the finite approximant's squared norm. -/
  normRepresentative : forall (X : SelectedWilsonCauchy D)
    (_hX : D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)),
      Nat -> CReal
  /-- The supplied norm representative denotes the actual finite completed
  sector inner product. -/
  normRepresents : forall (X : SelectedWilsonCauchy D)
    (hX : D.selectedSpectralData.vacPerp (selectedWilsonPoint D X))
    (scale : Nat),
    (Quotient.mk CReal.crealSetoid
        (normRepresentative X hX scale) : CReal.RC) =
      centralPhysicalVacuumSectorCylinderCompletedInner
        (family.nome_pos scale) (family.nome_lt_one scale) 0
        (approximant X hX scale).1 (approximant X hX scale).1
  /-- An explicit representative of the squared norm after the scheduled
  finite transfer power for one unit of physical time. -/
  transferredNormRepresentative : forall (X : SelectedWilsonCauchy D)
    (_hX : D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)),
      Nat -> CReal
  /-- The transferred representative denotes the actual scheduled-power norm. -/
  transferredNormRepresents : forall (X : SelectedWilsonCauchy D)
    (hX : D.selectedSpectralData.vacPerp (selectedWilsonPoint D X))
    (scale : Nat),
    (Quotient.mk CReal.crealSetoid
        (transferredNormRepresentative X hX scale) : CReal.RC) =
      centralPhysicalVacuumSectorCylinderCompletedInner
        (family.nome_pos scale) (family.nome_lt_one scale) 0
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          (family.nome_pos scale) (family.nome_lt_one scale) 0
          (centralPhysicalDynamicRCLatticeSteps family scale 1)
          (approximant X hX scale)).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          (family.nome_pos scale) (family.nome_lt_one scale) 0
          (centralPhysicalDynamicRCLatticeSteps family scale 1)
          (approximant X hX scale)).1
  /-- Finite squared norms converge to the literal inner representative of
  the selected continuum Cauchy sequence. -/
  norm_converges : forall (X : SelectedWilsonCauchy D)
    (hX : D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)),
    CReal.ConvergesTo (normRepresentative X hX)
      (D.wilson.toGNSData.cinnerRep X X)
  /-- Scheduled finite-image norms converge to the literal representative of
  the selected continuum transfer image. -/
  transferredNorm_converges : forall (X : SelectedWilsonCauchy D)
    (hX : D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)),
    CReal.ConvergesTo (transferredNormRepresentative X hX)
      (D.wilson.toGNSData.cinnerRep
        (transferredRepresentative X) (transferredRepresentative X))

namespace DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit

/-! ## 2. Finite and limiting all-vector inequalities -/

/-- The dynamic family's finite all-vector contraction, specialized to the
scheduled power for one unit of physical time and expressed in the exact
representatives selected by the graph-norm data. -/
theorem finitePhysicalTimeRepresentative_norm_gap
    {family : DynamicVacuumSectorCompletedFamily 0}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family ratePower D)
    (X : SelectedWilsonCauchy D)
    (hX : D.selectedSpectralData.vacPerp (selectedWilsonPoint D X))
    (scale : Nat) :
    CReal.leEv
      (data.transferredNormRepresentative X hX scale)
      (CReal.mul
        (CReal.ofQ'
          (normalizedMovingCubeSampledRatePower family scale 1))
        (data.normRepresentative X hX scale)) := by
  have hgap :=
    centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_norm_decay
      (family.completedGap scale)
      (centralPhysicalDynamicRCLatticeSteps family scale 1)
      (data.approximant X hX scale)
  have hrc : CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (data.transferredNormRepresentative X hX scale))
      (Quotient.mk CReal.crealSetoid
        (CReal.mul
          (CReal.ofQ'
            (normalizedMovingCubeSampledRatePower family scale 1))
          (data.normRepresentative X hX scale))) := by
    rw [← CReal.RCscale_mk]
    rw [data.transferredNormRepresents X hX scale,
      data.normRepresents X hX scale]
    simpa [normalizedMovingCubeSampledRatePower] using hgap
  exact hrc

/-- The scheduled finite all-vector inequality survives the matching
graph-norm and exact rate-power limits. -/
theorem physicalTimeOne_limit_operator_norm_gap
    {family : DynamicVacuumSectorCompletedFamily 0}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family ratePower D)
    (X : SelectedWilsonCauchy D)
    (hX : D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.leEv
      (D.wilson.toGNSData.cinnerRep
        (data.transferredRepresentative X)
        (data.transferredRepresentative X))
      (CReal.mul
        (ratePower.limitRepresentative 1)
        (D.wilson.toGNSData.cinnerRep X X)) := by
  have hright : CReal.ConvergesTo
      (fun scale => CReal.mul
        (CReal.ofQ'
          (normalizedMovingCubeSampledRatePower family scale 1))
        (data.normRepresentative X hX scale))
      (CReal.mul
        (ratePower.limitRepresentative 1)
        (D.wilson.toGNSData.cinnerRep X X)) :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (ratePower.converges 1) (data.norm_converges X hX)
  apply CReal.leEv_of_convergesTo_le
    (data.transferredNorm_converges X hX) hright
  intro scale
  exact data.finitePhysicalTimeRepresentative_norm_gap X hX scale

/-! ## 3. Contract to the selected Wilson all-vector gap -/

/-- The physical-time graph-norm data construct the uniform operator-norm gap
on every completed selected Wilson vacuum-complement vector. -/
def toWilsonOperatorNormGapPin
    {family : DynamicVacuumSectorCompletedFamily 0}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family ratePower D) :
    WilsonOperatorNormGapPin D where
  normGap := by
    intro vector
    refine Quotient.inductionOn vector ?_
    intro X hX
    change CReal.RCle
      (D.wilson.toGNSData.gnsComplete.hilbert.cinner
        (D.timeTranslation.op.T (selectedWilsonPoint D X))
        (D.timeTranslation.op.T (selectedWilsonPoint D X)))
      (CReal.RCscale
        (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep)
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (selectedWilsonPoint D X) (selectedWilsonPoint D X)))
    rw [← data.transferredRepresentative_class X]
    change CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (D.wilson.toGNSData.cinnerRep
          (data.transferredRepresentative X)
          (data.transferredRepresentative X)))
      (CReal.RCscale
        (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep)
        (Quotient.mk CReal.crealSetoid
          (D.wilson.toGNSData.cinnerRep X X)))
    have hlimit := data.physicalTimeOne_limit_operator_norm_gap X hX
    have hrc : CReal.RCle
        (Quotient.mk CReal.crealSetoid
          (D.wilson.toGNSData.cinnerRep
            (data.transferredRepresentative X)
            (data.transferredRepresentative X)))
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            (ratePower.limitRepresentative 1))
          (Quotient.mk CReal.crealSetoid
            (D.wilson.toGNSData.cinnerRep X X))) := by
      exact hlimit
    have hrate :
        (Quotient.mk CReal.crealSetoid
          (ratePower.limitRepresentative 1) : CReal.RC) =
        Quotient.mk CReal.crealSetoid
          (CReal.ofQ'
            (D.selectedSpectralData.gap.sep *
              D.selectedSpectralData.gap.sep)) :=
      Quotient.sound data.rateLimitPinned
    rw [hrate] at hrc
    simpa only [CReal.RCscale_mk, CReal.RCmul_mk] using hrc

end DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler.DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit.finitePhysicalTimeRepresentative_norm_gap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler.DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit.physicalTimeOne_limit_operator_norm_gap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler.DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit.toWilsonOperatorNormGapPin
