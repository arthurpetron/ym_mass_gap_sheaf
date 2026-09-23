/-
# The BF4-specific reverse comparison obligation

`BF4PhysicalJointFormTransfer` exposes the actual finite physical marginal
carrier and its reflected-joint carrier, but only proves the forward norm
comparison.  This module names the missing physical lower comparison without
inventing a witness: a supplied positive `κ` must bound the joint-form
distance below by the original physical distance.

Once supplied, the generic reverse comparison gives a concrete map between the
two BF4 completions, both quotient round trips, and transfer intertwining.
The certificate is intentionally conditional and finite-parameterized.
-/

import YMGap.Continuum.BF4PhysicalJointFormTransfer
import YMGap.Continuum.PositiveContractionReverseComparison

namespace YMGap.Continuum.BF4PhysicalJointReverseComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.PositiveContractionOneStepForm
open YMGap.Continuum.PositiveContractionOneStepCompletion
open YMGap.Continuum.PositiveContractionReverseComparison
open YMGap.Continuum.BF4PhysicalJointFormTransfer
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

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

/-- The exact missing finite BF4 lower comparison.  No inhabitant is supplied
by this declaration; it is the physical input required to reverse the
canonical comparison between the marginal and reflected-joint completions. -/
structure PhysicalJointReverseComparisonCertificate : Type where
  κ : Q'
  κ_pos : (0 : Q') < κ
  lower : ∀ a b : (D).toGNSData.V,
    κ * (D).toGNSData.distSqQ a b ≤
      (physicalJointSmulGNS w hw K half).toGNSData.distSqQ a b

/-- Adapt the BF4-specific lower certificate to the generic reverse bridge. -/
def PhysicalJointReverseComparisonCertificate.toGeneric
    (certificate : PhysicalJointReverseComparisonCertificate w hw K half) :
    ReverseComparisonCoercivity D S hsa hpos where
  κ := certificate.κ
  κ_pos := certificate.κ_pos
  lower := by
    intro a b
    simpa [physicalJointSmulGNS, hsa, hpos] using certificate.lower a b

abbrev PhysicalJointReverseComparison : Type :=
  PhysicalJointCompletion w hw K half →
    CentralPhysicalGNSCompletion w hw K half

/-- The concrete BF4 reverse map, conditional on the named lower certificate. -/
def physicalJointReverseComparison
    (certificate : PhysicalJointReverseComparisonCertificate w hw K half) :
    PhysicalJointReverseComparison w hw K half :=
  reverseComparison (certificate.toGeneric w hw K half)

theorem physicalJointReverseComparison_comparison
    (certificate : PhysicalJointReverseComparisonCertificate w hw K half)
    (x : CentralPhysicalGNSCompletion w hw K half) :
    physicalJointReverseComparison w hw K half certificate
        (physicalJointComparison w hw K half x) = x := by
  exact reverseComparison_comparison
    (certificate.toGeneric w hw K half) x

theorem physicalJointComparison_reverseComparison
    (certificate : PhysicalJointReverseComparisonCertificate w hw K half)
    (y : PhysicalJointCompletion w hw K half) :
    physicalJointComparison w hw K half
        (physicalJointReverseComparison w hw K half certificate y) = y := by
  exact comparison_reverseComparison
    (certificate.toGeneric w hw K half) y

theorem physicalJointReverseComparison_intertwines
    (certificate : PhysicalJointReverseComparisonCertificate w hw K half)
    (x : PhysicalJointCompletion w hw K half) :
    physicalJointReverseComparison w hw K half certificate
        (physicalJointTransfer w hw K half x) =
      centralPhysicalCompletedMarkovTransfer w hw K half
        (physicalJointReverseComparison w hw K half certificate x) := by
  exact reverseComparison_intertwines
    (certificate.toGeneric w hw K half) x

end YMGap.Continuum.BF4PhysicalJointReverseComparison

#print axioms
  YMGap.Continuum.BF4PhysicalJointReverseComparison.PhysicalJointReverseComparisonCertificate.toGeneric
#print axioms
  YMGap.Continuum.BF4PhysicalJointReverseComparison.physicalJointReverseComparison
#print axioms
  YMGap.Continuum.BF4PhysicalJointReverseComparison.physicalJointReverseComparison_comparison
#print axioms
  YMGap.Continuum.BF4PhysicalJointReverseComparison.physicalJointComparison_reverseComparison
#print axioms
  YMGap.Continuum.BF4PhysicalJointReverseComparison.physicalJointReverseComparison_intertwines
