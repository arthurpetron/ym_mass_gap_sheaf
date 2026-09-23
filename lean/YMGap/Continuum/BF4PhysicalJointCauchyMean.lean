/-
# Joint vacuum-pairing convergence for arbitrary completed representatives

The centered-cylinder certificate handles finite observables by exact rational
subtraction.  The next necessary ingredient for arbitrary completed joint
vectors is the scalar correction itself: the stagewise pairing with the joint
vacuum must converge to zero on the vacuum complement.  This module proves
that convergence with the existing CReal pairing modulus; it does not yet
construct the centered Cauchy representative or the full density witness.
-/

import YMGap.Continuum.BF4PhysicalJointCenteredKernel

namespace YMGap.Continuum.BF4PhysicalJointCauchyMean

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4PhysicalJointFormTransfer
open YMGap.Continuum.BF4PhysicalJointCenteredKernel
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- The exact rational joint-vacuum pairing of each stage of a joint Cauchy
representative, embedded as a constructive real. -/
def physicalJointCauchyMeanSeq
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (X : CauchyGNS
      (physicalJointSmulGNS w hw K half).toGNSData)
    (stage : Nat) : CReal :=
  CReal.ofQ'
    ((physicalJointSmulGNS w hw K half).toGNSData.B
      (X.seq stage) centralPhysicalVacuumCarrier)

/-- The joint vacuum-pairing sequence of any vacuum-orthogonal completed vector
converges to zero.  This is the scalar modulus needed before a stagewise exact
centering construction can be attempted. -/
theorem physicalJointCauchyMeanSeq_converges_zero
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (X : CauchyGNS
      (physicalJointSmulGNS w hw K half).toGNSData)
    (horthogonal : PhysicalJointVacuumOrthogonal w hw K half
      (Quotient.mk
        (cauchySetoid
          (physicalJointSmulGNS w hw K half).toGNSData) X)) :
    CReal.ConvergesTo
      (physicalJointCauchyMeanSeq w hw K half X) CReal.czero := by
  let D := (physicalJointSmulGNS w hw K half).toGNSData
  let vacuumRep := constCauchy D centralPhysicalVacuumCarrier
  have hpair : CReal.ConvergesTo
      (fun stage => CReal.ofQ' (D.cInnerSeq X vacuumRep stage))
      (D.cinnerRep X vacuumRep) :=
    CReal.convergesTo_ofQ'CauchySeq
      (D.cInnerSeq X vacuumRep) (D.cInnerQCauchy X vacuumRep)
  have hmean : CReal.ConvergesTo
      (physicalJointCauchyMeanSeq w hw K half X)
      (D.cinnerRep X vacuumRep) := by
    apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (s := fun stage => CReal.ofQ' (D.cInnerSeq X vacuumRep stage))
    · intro stage
      exact CReal.Equiv.refl _
    · simpa only [physicalJointCauchyMeanSeq, vacuumRep,
        GNSData.cInnerSeq] using hpair
  have hvacuum : physicalJointVacuum w hw K half =
      embedV D centralPhysicalVacuumCarrier := by
    exact physicalJointComparison_embed w hw K half
      centralPhysicalVacuumCarrier
  have hquotient :
      Quotient.mk CReal.crealSetoid (D.cinnerRep X vacuumRep) =
        Quotient.mk CReal.crealSetoid CReal.czero := by
    unfold PhysicalJointVacuumOrthogonal at horthogonal
    rw [hvacuum] at horthogonal
    exact horthogonal
  exact CReal.convergesTo_limit_congr hmean (Quotient.exact hquotient)

#print axioms physicalJointCauchyMeanSeq
#print axioms physicalJointCauchyMeanSeq_converges_zero

end YMGap.Continuum.BF4PhysicalJointCauchyMean
