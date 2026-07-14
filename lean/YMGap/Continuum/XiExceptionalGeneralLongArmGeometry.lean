/-
# The minimal ordered-ear word invariant

An exceptional source entry determines two admissible occurrence families,
but not an ordering of those occurrences into the canonical short and long
ear words used by the uniform carrier construction.  This module records the
minimal missing chart: the three exact word identities for the source, the
short carrier, and every indexed long carrier.  All quantities in the chart
are actual activities of occurrences in `Gamma`; positivity is therefore
derived rather than stored.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge

namespace YMGap.Continuum.XiExceptionalGeneralLongArmGeometry

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalGeneralLongArmAlgebra
open YMGap.Continuum.XiExceptionalMultiReserveAlgebra
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge

local infix:50 " ≈ " => Q'.eqv

variable {L : Lattice} [DecidableEq L.Plaquette]

def endpointActivity (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) : Q' :=
  activity w (polyAt Gamma 0) label * activity w (polyAt Gamma 3) label

def shortActivityOne (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) : Q' :=
  activity w (polyAt Gamma 1) label

def shortActivityTwo (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) : Q' :=
  activity w (polyAt Gamma 2) label

def evenLongActivity (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) (i : Nat) : Q' :=
  activity w (polyAt Gamma (4 + 2 * i)) label

def oddLongActivity (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) (i : Nat) : Q' :=
  activity w (polyAt Gamma (5 + 2 * i)) label

/-- A canonical occurrence chart for a one-pair short ear and a long arm.
Unlike raw exceptional-source membership, this invariant fixes which actual
occurrence occupies every algebraic variable and certifies that the selected
source and carrier words reduce to those variables. -/
structure CanonicalEarWordGeometry
    (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop where
  source_word : ∀ w label,
    occurrencePairWeight w qP b1 b2 Gamma label entry.1 ≈
      endpointActivity w Gamma label *
        uniformSource
          (shortActivityOne w Gamma label)
          (shortActivityTwo w Gamma label)
          (indexValues (longCount k) (evenLongActivity w Gamma label))
          (indexValues (longCount k) (oddLongActivity w Gamma label))
  short_word : ∀ w label,
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (shortCarrierCode Gamma k hGamma) ≈
      endpointActivity w Gamma label *
        shortSquare
          (shortActivityOne w Gamma label)
          (shortActivityTwo w Gamma label)
  long_word : ∀ w label side i, i < longCount k →
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (longCarrierCode Gamma k hGamma side i) ≈
      endpointActivity w Gamma label *
        indexedPayerAt k
          (shortActivityOne w Gamma label)
          (shortActivityTwo w Gamma label)
          (qProd (indexValues (longCount k)
            (evenLongActivity w Gamma label)))
          (qProd (indexValues (longCount k)
            (oddLongActivity w Gamma label)))
          side i (evenLongActivity w Gamma label)
            (oddLongActivity w Gamma label)

/-- The ordered-ear word invariant discharges the full normalization record.
All nonnegativity fields follow from the substrate activity theorem. -/
def CanonicalEarWordGeometry.normalization
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)} {k : Nat}
    {hGamma : Gamma.length = ambientCount k}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    (geom : CanonicalEarWordGeometry qP b1 b2 Gamma k hGamma entry) :
    UniformLongArmNormalization qP b1 b2 Gamma k hGamma entry where
  common := fun w label => endpointActivity w Gamma label
  a1 := fun w label => shortActivityOne w Gamma label
  a2 := fun w label => shortActivityTwo w Gamma label
  evenAt := fun w label => evenLongActivity w Gamma label
  oddAt := fun w label => oddLongActivity w Gamma label
  source_eqv := geom.source_word
  short_eqv := geom.short_word
  long_eqv := geom.long_word
  common_nonneg := by
    intro w hw label
    exact Q'.mul_nonneg _ _
      (activity_nonneg hw (polyAt Gamma 0) label)
      (activity_nonneg hw (polyAt Gamma 3) label)
  a1_nonneg := by
    intro w hw label
    exact activity_nonneg hw (polyAt Gamma 1) label
  a2_nonneg := by
    intro w hw label
    exact activity_nonneg hw (polyAt Gamma 2) label
  even_nonneg := by
    intro w hw label i _
    exact activity_nonneg hw (polyAt Gamma (4 + 2 * i)) label
  odd_nonneg := by
    intro w hw label i _
    exact activity_nonneg hw (polyAt Gamma (5 + 2 * i)) label

def CanonicalEarWordGeometry.paidBlock
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)} {k : Nat}
    {hGamma : Gamma.length = ambientCount k}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    (geom : CanonicalEarWordGeometry qP b1 b2 Gamma k hGamma entry) :
    PaidResidualBlock qP b1 b2 Gamma entry :=
  uniformPaidResidualBlock geom.normalization

#print axioms CanonicalEarWordGeometry.normalization
#print axioms CanonicalEarWordGeometry.paidBlock

end YMGap.Continuum.XiExceptionalGeneralLongArmGeometry
