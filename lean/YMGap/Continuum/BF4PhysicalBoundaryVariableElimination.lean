/-
# Variable-elimination certificates for the physical BF4 boundary carrier

The physical half-boundary construction uses two finite Cartesian carriers:
lower-face states and fixed-face boundary channels.  The retained source
carrier is a decidable filter of the lower-face carrier.  This module
connects all three objects to the generic word-based elimination checker.

Filtered source sums are represented by a zero mask on the full Cartesian
carrier.  Thus an external exact-arithmetic program may eliminate the full
word model without being trusted to reproduce Lean's physical-state filter:
Lean evaluates the mask and checks every staged elimination equation.

The results are exact finite-cutoff identities only.  They do not supply a
small-width factorization, a cutoff-uniform estimate, or a continuum limit.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
import YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination

namespace YMGap.Continuum.BF4PhysicalBoundaryVariableElimination

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteVariableEliminationCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

local infix:50 " ≈ " => Q'.eqv

/-- The exact decidable predicate used by the retained physical source
filter. -/
def centralPositiveHalfStateTest
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (source : EdgeLabelling) : Bool :=
  decide ((0 : Q') <
    centralPhysicalRowMarginal w hw K half source)

theorem centralPositiveHalfStates_eq_filter_test
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    centralPositiveHalfStates w hw K half =
      (centralHalfStates K half).filter
        (centralPositiveHalfStateTest w hw K half) :=
  rfl

/-- The lower-state carrier is exactly a decoded fixed-length word list. -/
theorem centralHalfStates_eq_map_allSeqs (K half : Nat) :
    centralHalfStates K half =
      (allSeqs (K + 1) (centralLowerFaceIds half).length).map
        (wordToEdgeLabelling (centralLowerFaceIds half)) := by
  unfold centralHalfStates
  exact boundedEdgeLabellings_eq_map_allSeqs K
    (centralLowerFaceIds half)

/-- The fixed-interface carrier is exactly a decoded fixed-length word list. -/
theorem centralBoundaryChannels_eq_map_allSeqs (K half : Nat) :
    centralBoundaryChannels K half =
      (allSeqs (K + 1) (centralFixedFaceIds half).length).map
        (wordToEdgeLabelling (centralFixedFaceIds half)) := by
  unfold centralBoundaryChannels
  exact boundedEdgeLabellings_eq_map_allSeqs K
    (centralFixedFaceIds half)

/-- Any sum over retained positive lower states is the word sum of its exact
Boolean zero extension to the full lower-face Cartesian carrier. -/
theorem listQSum_centralPositiveHalfStates_eqv_finiteAssignmentSum
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (value : EdgeLabelling → Q') :
    listQSum value (centralPositiveHalfStates w hw K half) ≈
      finiteAssignmentSum (K + 1) (centralLowerFaceIds half).length
        (fun word =>
          finiteMaskedValue
            (centralPositiveHalfStateTest w hw K half)
            value
            (wordToEdgeLabelling (centralLowerFaceIds half) word)) := by
  rw [centralPositiveHalfStates_eq_filter_test]
  refine Q'.eqv_trans _
    (listQSum
      (finiteMaskedValue
        (centralPositiveHalfStateTest w hw K half) value)
      (centralHalfStates K half)) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_finiteMaskedValue_eqv_filter
        (centralPositiveHalfStateTest w hw K half)
        value (centralHalfStates K half))
  · unfold centralHalfStates
    exact listQSum_boundedEdgeLabellings_eqv_finiteAssignmentSum
      K (centralLowerFaceIds half)
      (finiteMaskedValue
        (centralPositiveHalfStateTest w hw K half) value)

/-- A checked elimination trace certifies any retained-positive-source sum. -/
theorem listQSum_centralPositiveHalfStates_eqv_certificateBottom
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {value : EdgeLabelling → Q'}
    (certificate : ExactVariableEliminationCertificate
      (K + 1) (centralLowerFaceIds half).length
      (fun word =>
        finiteMaskedValue
          (centralPositiveHalfStateTest w hw K half)
          value
          (wordToEdgeLabelling (centralLowerFaceIds half) word))) :
    listQSum value (centralPositiveHalfStates w hw K half) ≈
      certificate.table 0 [] := by
  exact Q'.eqv_trans _ _ _
    (listQSum_centralPositiveHalfStates_eqv_finiteAssignmentSum
      w hw K half value)
    certificate.assignmentSum_eqv_bottom

/-- A checked elimination trace for the physical half amplitude, with the
retained-source mask evaluated by Lean, certifies one full boundary column. -/
theorem centralBoundaryColumnMass_eqv_certificateBottom
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {boundary : EdgeLabelling}
    (certificate : ExactVariableEliminationCertificate
      (K + 1) (centralLowerFaceIds half).length
      (fun word =>
        finiteMaskedValue
          (centralPositiveHalfStateTest w hw K half)
          (fun source =>
            centralHalfAmplitude w K half source boundary)
          (wordToEdgeLabelling (centralLowerFaceIds half) word))) :
    centralBoundaryColumnMass w hw K half boundary ≈
      certificate.table 0 [] := by
  unfold centralBoundaryColumnMass
  exact listQSum_centralPositiveHalfStates_eqv_certificateBottom certificate

/-- A checked elimination trace over fixed-face words certifies the exact
mass of one physical half-amplitude row. -/
theorem centralHalfAmplitudeBoundaryRowMass_eqv_certificateBottom
    {w : Q'} {K half : Nat} {source : EdgeLabelling}
    (certificate : ExactVariableEliminationCertificate
      (K + 1) (centralFixedFaceIds half).length
      (fun word =>
        centralHalfAmplitude w K half source
          (wordToEdgeLabelling (centralFixedFaceIds half) word))) :
    centralHalfAmplitudeBoundaryRowMass w K half source ≈
      certificate.table 0 [] := by
  unfold centralHalfAmplitudeBoundaryRowMass centralBoundaryChannels
  exact listQSum_boundedEdgeLabellings_eqv_certificateBottom certificate

end YMGap.Continuum.BF4PhysicalBoundaryVariableElimination

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVariableElimination.centralHalfStates_eq_map_allSeqs
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVariableElimination.listQSum_centralPositiveHalfStates_eqv_certificateBottom
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVariableElimination.centralBoundaryColumnMass_eqv_certificateBottom
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVariableElimination.centralHalfAmplitudeBoundaryRowMass_eqv_certificateBottom
