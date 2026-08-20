/- Generated certificate data.  The generator is untrusted; Lean checks this file. -/
import YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter

namespace YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarterExample

open YMGap.Constructive
open YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh
open YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter
open YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence
open YMGap.Continuum.ConstructiveRefreshContraction

-- Generator-side maximum relative error: 1/20
def exactBoundaryMessagePilotSources : List (Fin 2) := [0, 1]
def exactBoundaryMessagePilotTargets : List (Fin 2) := [0, 1]

def exactBoundaryMessagePilotKernel (source : Fin 2) (target : Fin 2) : Q' :=
  match source.val, target.val with
  | 0, 0 => Q'.mkPos 21 2 (by decide)
  | 0, 1 => Q'.mkPos 19 10 (by decide)
  | 1, 0 => Q'.mkPos 57 4 (by decide)
  | 1, 1 => Q'.mkPos 63 20 (by decide)
  | _, _ => 0

def exactBoundaryMessagePilotSourceProfile (index : Fin 2) : Q' :=
  match index.val with
  | 0 => Q'.mkPos 2 1 (by decide)
  | 1 => Q'.mkPos 3 1 (by decide)
  | _ => 0

def exactBoundaryMessagePilotTargetProfile (index : Fin 2) : Q' :=
  match index.val with
  | 0 => Q'.mkPos 5 1 (by decide)
  | 1 => Q'.mkPos 1 1 (by decide)
  | _ => 0

def exactBoundaryMessagePilotTerminal (index : Fin 2) : Q' :=
  match index.val with
  | 0 => Q'.mkPos 7 1 (by decide)
  | 1 => Q'.mkPos 11 1 (by decide)
  | _ => 0

def exactBoundaryMessagePilotWitness :
    FiniteRelativeRankOneQuarterWitness
      exactBoundaryMessagePilotKernel
      exactBoundaryMessagePilotSources
      exactBoundaryMessagePilotTargets where
  sourceProfile := exactBoundaryMessagePilotSourceProfile
  targetProfile := exactBoundaryMessagePilotTargetProfile
  sourceProfile_pos := by decide
  targetProfile_pos := by decide
  relative_error := by decide

theorem exactBoundaryMessagePilotTerminal_pos :
    ∀ target, target ∈ exactBoundaryMessagePilotTargets →
      (0 : Q') < exactBoundaryMessagePilotTerminal target := by
  decide

theorem exactBoundaryMessagePilotDenominator_pos :
    ∀ source,
      (0 : Q') < terminalWeightedDenominator
        exactBoundaryMessagePilotTargets
        exactBoundaryMessagePilotKernel
        exactBoundaryMessagePilotTerminal source := by
  decide

def exactBoundaryMessagePilotRefresh :
    FiniteRefreshCertificate
      exactBoundaryMessagePilotSources
      exactBoundaryMessagePilotTargets :=
  terminalProjectiveRefreshCertificate
    exactBoundaryMessagePilotWitness.toCrossRatioCertificate
    exactBoundaryMessagePilotTerminal
    exactBoundaryMessagePilotTerminal_pos
    exactBoundaryMessagePilotDenominator_pos
    exactBoundaryMessagePilotWitness.commonMass_lt_one
    0 (by decide)

theorem exactBoundaryMessagePilotRefresh_rate_le_quarter :
    exactBoundaryMessagePilotRefresh.rate ≤ quarterRate := by
  exact terminalProjectiveRefresh_rate_le_quarter
    exactBoundaryMessagePilotWitness.toCrossRatioCertificate
    exactBoundaryMessagePilotTerminal
    exactBoundaryMessagePilotTerminal_pos
    exactBoundaryMessagePilotDenominator_pos
    exactBoundaryMessagePilotWitness.commonMass_lt_one
    0 (by decide)
    relativeRankOneSpread_square_le_fourThirds

end YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarterExample

#print axioms YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarterExample.exactBoundaryMessagePilotRefresh_rate_le_quarter
