/-
# Proof-carrying support closure interface for cutoff-two BF4

This module specializes the generic finite code-closure checker to the
genuine cutoff-two physical Gram kernel.  A generated certificate supplies a
Boolean possible-edge table, proves that every `false` entry forces the exact
physical kernel entry to vanish, includes the forced seed codes, and carries
the kernel-reduced finite closure check.

The full retained carrier gives a baseline inhabitant.  The computational
research task is to replace that baseline by a smaller sparse generated
sector while preserving all proof fields.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed
import YMGap.Continuum.FiniteKernelCodeClosureCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovClosureCertificate

set_option maxRecDepth 300000
set_option maxHeartbeats 200000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteKernelCodeClosureCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- A replayable cutoff-two support-closure certificate.  An external program
may generate `possibleEdge`, `sectorCodes`, and the closed Boolean check, but
Lean requires the model-specific zero theorem before accepting the result. -/
structure CutoffTwoPhysicalKrylovClosureCertificate where
  possibleEdge : Nat → Nat → Bool
  zero_of_edge_false :
    ∀ source target : EdgeLabelling,
      source ∈ cutoffTwoVacuumColumnCarrier →
      target ∈ cutoffTwoVacuumColumnCarrier →
      possibleEdge (bf4StateCode 2 0 source)
          (bf4StateCode 2 0 target) = false →
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        source target ≈ 0
  sectorCodes : List Nat
  sectorCodes_nodup : sectorCodes.Nodup
  forcedSeedIncluded :
    ∀ code : Nat,
      code ∈ cutoffTwoFirstKrylovSeedCodes → code ∈ sectorCodes
  closure_checked : finiteKernelCodeSectorRowClosedB
    cutoffTwoVacuumColumnCarrier
    (bf4StateCode 2 0)
    sectorCodes possibleEdge = true

namespace CutoffTwoPhysicalKrylovClosureCertificate

theorem rowClosed
    (certificate : CutoffTwoPhysicalKrylovClosureCertificate) :
    cutoffTwoPhysicalCodeSectorRowClosed certificate.sectorCodes := by
  exact finiteKernelCodeSectorRowClosed_of_check
    cutoffTwoVacuumColumnCarrier
    (bf4StateCode 2 0)
    (centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0)
    certificate.sectorCodes certificate.possibleEdge
    certificate.zero_of_edge_false certificate.closure_checked

theorem contains_forced_seed
    (certificate : CutoffTwoPhysicalKrylovClosureCertificate)
    (code : Nat)
    (hcode : code ∈ cutoffTwoFirstKrylovSeedCodes) :
    code ∈ certificate.sectorCodes :=
  certificate.forcedSeedIncluded code hcode

end CutoffTwoPhysicalKrylovClosureCertificate

/-! ## Baseline full-carrier certificate -/

def cutoffTwoFullCarrierCodes : List Nat :=
  cutoffTwoVacuumColumnCarrier.map (bf4StateCode 2 0)

theorem cutoffTwoFullCarrierCode_mem
    (state : EdgeLabelling)
    (hstate : state ∈ cutoffTwoVacuumColumnCarrier) :
    bf4StateCode 2 0 state ∈ cutoffTwoFullCarrierCodes := by
  unfold cutoffTwoFullCarrierCodes
  exact List.mem_map.mpr ⟨state, hstate, rfl⟩

theorem cutoffTwoFullCarrierCodes_nodup :
    cutoffTwoFullCarrierCodes.Nodup := by
  unfold cutoffTwoFullCarrierCodes
  exact nodup_map_of_injOn (bf4StateCode 2 0)
    cutoffTwoVacuumColumnCarrier
    (centralPositiveHalfStates_nodup cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)
    (fun left hleft right hright hcode =>
      bf4StateCode_injective_on_positive hleft hright hcode)

private theorem cutoffTwoFullCarrier_closure_checked :
    finiteKernelCodeSectorRowClosedB
      cutoffTwoVacuumColumnCarrier
      (bf4StateCode 2 0)
      cutoffTwoFullCarrierCodes
      (fun _ _ => true) = true := by
  unfold finiteKernelCodeSectorRowClosedB
  apply List.all_eq_true.mpr
  intro source hsource
  have hsourceCode := cutoffTwoFullCarrierCode_mem source hsource
  simp only [hsourceCode, decide_true, if_true]
  apply List.all_eq_true.mpr
  intro target htarget
  have htargetCode := cutoffTwoFullCarrierCode_mem target htarget
  simp only [htargetCode, decide_true, if_true]

/-- The full retained carrier is the fail-safe closed sector.  Its all-true
possible-edge oracle certifies no sparsity; it only proves that the interface
is inhabited before a generated smaller closure certificate is supplied. -/
def cutoffTwoFullCarrierKrylovClosureCertificate :
    CutoffTwoPhysicalKrylovClosureCertificate where
  possibleEdge := fun _ _ => true
  zero_of_edge_false := by
    intro _source _target _hsource _htarget hedge
    exact False.elim (Bool.false_ne_true hedge.symm)
  sectorCodes := cutoffTwoFullCarrierCodes
  sectorCodes_nodup := cutoffTwoFullCarrierCodes_nodup
  forcedSeedIncluded := by
    intro code hcode
    have hstates :
        ∀ state : EdgeLabelling,
          state ∈ cutoffTwoFirstKrylovSeedStates →
          bf4StateCode 2 0 state ∈ cutoffTwoFullCarrierCodes := by
      intro state hstate
      exact cutoffTwoFullCarrierCode_mem state
        (cutoffTwoFirstKrylovSeedStates_subset_carrier state hstate)
    unfold cutoffTwoFirstKrylovSeedCodes at hcode
    rcases List.mem_cons.mp hcode with hcode | htail
    · subst code
      exact hstates zeroEdgeLabelling List.mem_cons_self
    rcases List.mem_cons.mp htail with hcode | htail
    · subst code
      exact hstates centralLowerCubeState
        (List.mem_cons_of_mem zeroEdgeLabelling List.mem_cons_self)
    rcases List.mem_cons.mp htail with hcode | hempty
    · subst code
      exact hstates cutoffTwoVacuumCubeLeakageState
        (List.mem_cons_of_mem zeroEdgeLabelling
          (List.mem_cons_of_mem centralLowerCubeState List.mem_cons_self))
    · exact False.elim (List.not_mem_nil hempty)
  closure_checked := cutoffTwoFullCarrier_closure_checked

theorem cutoffTwoFullCarrierKrylovClosureCertificate_rowClosed :
    cutoffTwoPhysicalCodeSectorRowClosed cutoffTwoFullCarrierCodes := by
  intro _source target _hsource htarget _hsourceCode htargetOutside
  exact False.elim
    (htargetOutside (cutoffTwoFullCarrierCode_mem target htarget))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovClosureCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovClosureCertificate.CutoffTwoPhysicalKrylovClosureCertificate.rowClosed
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovClosureCertificate.cutoffTwoFullCarrierCodes_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovClosureCertificate.cutoffTwoFullCarrierKrylovClosureCertificate_rowClosed
