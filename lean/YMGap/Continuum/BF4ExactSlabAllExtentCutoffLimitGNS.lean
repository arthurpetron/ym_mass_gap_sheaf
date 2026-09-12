/-
# Original cutoff-limit completed carriers at every odd slab extent

The constructed symmetric positive form supplies the constructive null
quotient and Hilbert completion. At each slab, all finite cutoff anchors
embed into ONE carrier, with pairings pinned to the ORIGINAL signed law.
The slab extent remains an explicit parameter: no compatibility between
different slabs or physical time-translation law is assumed or proved.

Completeness takes a sequence with supplied Cauchy representatives and
modulus. Its limit representative and outer convergence rate are data;
the eventual inner representative-index bound has the existing purely
propositional reading. No arbitrary quotient representatives are chosen.
Vacuum normalization/non-nullness at all extents, stationary physical
vacuum, transfer, strict gap and continuum QFT are not asserted here.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
import YMGap.Continuum.GNSJointPairingContinuity

namespace YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- No fixed representation cutoff remains on this completed slab carrier. -/
def cutoffLimitCompletion (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) :
    CompleteGNSHilbertGeneral (cutoffLimitGNSData w hw half) :=
  (cutoffLimitGNSData w hw half).gnsComplete_general

abbrev CutoffLimitCarrier (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) :=
  (cutoffLimitCompletion w hw half).hilbert.carrier

def cutoffLimitEmbed (w : Q') (hw : (0 : Q') ≤ w) {half : Nat}
    (a : BoundaryObservable half) : CutoffLimitCarrier w hw half :=
  (cutoffLimitCompletion w hw half).hilbert.ι ((cutoffLimitGNSData w hw half).qmk a)

theorem cutoffLimitEmbed_pairing (w : Q') (hw : (0 : Q') ≤ w) {half : Nat}
    (a b : BoundaryObservable half) :
    (cutoffLimitCompletion w hw half).hilbert.cinner (cutoffLimitEmbed w hw a) (cutoffLimitEmbed w hw b) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (limitForm w a b)) := by
  have h := (cutoffLimitCompletion w hw half).hilbert.ι_inner a b
  unfold GNSData.cInner at h
  rw [cutoffLimitGNSData_form] at h
  exact h

/-- The same original finite pairing beyond its explicit pair-dependent stage. -/
theorem cutoffLimitEmbed_finite_pairing (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    {half : Nat} (a b : BoundaryObservable half) (hK : formModulus w a b ≤ K) :
    (cutoffLimitCompletion w hw half).hilbert.cinner (cutoffLimitEmbed w hw a) (cutoffLimitEmbed w hw b) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (finiteForm w K a b)) :=
  (cutoffLimitEmbed_pairing w hw a b).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (Q'.eqv_symm (finiteForm_stable w K a b hK))))

/-- Every finite anchor at this extent embeds into the same original-law completion. -/
theorem cutoffLimitEmbed_anchored_pairing (w : Q') (hw : (0 : Q') ≤ w) (half anchor : Nat)
    (a b : EdgeLabelling → Q') :
    (cutoffLimitCompletion w hw half).hilbert.cinner
      (cutoffLimitEmbed w hw (BoundaryObservable.ofCoefficients half anchor a))
      (cutoffLimitEmbed w hw (BoundaryObservable.ofCoefficients half anchor b)) =
      Quotient.mk CReal.crealSetoid (exactCutoffPairingLimit w anchor half a b) :=
  (cutoffLimitEmbed_pairing w hw _ _).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (limitForm_ofCoefficients w half anchor a b)))

/-- Specified representative of the constructive diagonal limit. -/
def limitRepresentative (w : Q') (hw : (0 : Q') ≤ w) (half : Nat)
    (X : GeneralCompletionCauchy (cutoffLimitGNSData w hw half)) :
    CauchyGNS (cutoffLimitGNSData w hw half) := X.lim

/-- Explicit outer convergence rate, retaining the supplied modulus as data. -/
def completionRate (w : Q') (hw : (0 : Q') ≤ w) (half : Nat)
    (X : GeneralCompletionCauchy (cutoffLimitGNSData w hw half)) (epsilon : Q') : Nat :=
  GNSJointPairingContinuity.limitRate X epsilon

theorem limitRepresentative_close_at (w : Q') (hw : (0 : Q') ≤ w) (half : Nat)
    (X : GeneralCompletionCauchy (cutoffLimitGNSData w hw half)) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (p : Nat) (hp : completionRate w hw half X epsilon ≤ p) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      (cutoffLimitGNSData w hw half).distSqQ ((X.pt p).seq n)
        ((limitRepresentative w hw half X).seq n) ≤ epsilon :=
  GNSJointPairingContinuity.limit_close_at X epsilon hepsilon p hp

end YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS.cutoffLimitCompletion
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS.CutoffLimitCarrier
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS.cutoffLimitEmbed
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS.cutoffLimitEmbed_pairing
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS.cutoffLimitEmbed_finite_pairing
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS.cutoffLimitEmbed_anchored_pairing
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS.limitRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS.completionRate
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS.limitRepresentative_close_at
