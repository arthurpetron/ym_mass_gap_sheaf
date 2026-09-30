/-
# Constructive gauge-polynomial completion in the SAME full-action carrier

Each witness is an original fullData Cauchy representative whose polynomial
terms satisfy the existing Invariant predicate for EVERY vertex-tag map.
Arithmetic, supplied diagonal limits and the actual completed block
conditional projection construct such witnesses with explicit moduli.

No new ambient completion is introduced. This is the represented completion
of those gauge polynomials, not a proved characterization as the fixed space
of an unconstructed completed gauge action. No useful covariance bound,
nonconstant excitation, scaling limit or physical mass is supplied here.
-/

import YMGap.Continuum.GNSRepresentedSector
import YMGap.Continuum.BF4ExactSlabGaugeConditionalApproximation
import YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
import YMGap.Continuum.BF4ExactSlabFullActionScalar

namespace YMGap.Continuum.BF4ExactSlabGaugeRepresentedCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSRepresentedSector
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabVertexGaugeAction
open YMGap.Continuum.BF4ExactSlabGaugeConditionalApproximation
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK

/-- All existing common-auxiliary vertex tags, on ORIGINAL polynomials. -/
def GaugePolynomial (p : (F).V) : Prop :=
  ∀ tags : Z4Vertex → Option (Fin 3), Invariant extent tags p.val

/-- Data inside the existing full-action completion, not an alternate space. -/
abbrev Witness (x : GNSCompletionSpace F) :=
  Representative F (GaugePolynomial hw0 hw1 K extent hK) x

def ofPolynomial (p : (F).V) (hp : GaugePolynomial hw0 hw1 K extent hK p) :
    Witness hw0 hw1 K extent hK (embedV F p) := Representative.ofDense p hp

theorem polynomial_zero : GaugePolynomial hw0 hw1 K extent hK (F).zero :=
  fun tags => (Invariant.one extent tags).smul 0

theorem polynomial_add (p q : (F).V)
    (hp : GaugePolynomial hw0 hw1 K extent hK p)
    (hq : GaugePolynomial hw0 hw1 K extent hK q) :
    GaugePolynomial hw0 hw1 K extent hK ((F).add p q) :=
  fun tags => (hp tags).add (hq tags)

theorem polynomial_neg (p : (F).V) (hp : GaugePolynomial hw0 hw1 K extent hK p) :
    GaugePolynomial hw0 hw1 K extent hK ((F).neg p) :=
  fun tags => (hp tags).smul (-1)

theorem polynomial_smul (c : Q') (p : (F).V)
    (hp : GaugePolynomial hw0 hw1 K extent hK p) :
    GaugePolynomial hw0 hw1 K extent hK ((F).smul c p) :=
  fun tags => (hp tags).smul c

def zero : Witness hw0 hw1 K extent hK (embedV F (F).zero) :=
  ofPolynomial hw0 hw1 K extent hK _ (polynomial_zero hw0 hw1 K extent hK)

def constant : Witness hw0 hw1 K extent hK
    (embedV F ⟨polyOne, supported_one _⟩) :=
  ofPolynomial hw0 hw1 K extent hK _ (fun tags => Invariant.one extent tags)

def add {x y : GNSCompletionSpace F}
    (a : Witness hw0 hw1 K extent hK x) (b : Witness hw0 hw1 K extent hK y) :
    Witness hw0 hw1 K extent hK ((F).cAdd x y) :=
  a.add (polynomial_add hw0 hw1 K extent hK) b

def sub {x y : GNSCompletionSpace F}
    (a : Witness hw0 hw1 K extent hK x) (b : Witness hw0 hw1 K extent hK y) :
    Witness hw0 hw1 K extent hK ((F).cSub x y) :=
  a.sub (polynomial_add hw0 hw1 K extent hK) (polynomial_neg hw0 hw1 K extent hK) b

def scale (c : Q') {x : GNSCompletionSpace F} (a : Witness hw0 hw1 K extent hK x) :
    Witness hw0 hw1 K extent hK ((S).cSmul c x) :=
  GNSRepresentedSector.smul S _ (polynomial_smul hw0 hw1 K extent hK) c a

/-- Supplied invariant representatives and a Cauchy modulus yield an explicit
invariant diagonal in the SAME completion; no choice from membership proofs. -/
def limit (X : GeneralCompletionCauchy F)
    (hX : ∀ n m, GaugePolynomial hw0 hw1 K extent hK ((X.pt n).seq m)) :
    Witness hw0 hw1 K extent hK (Quotient.mk (cauchySetoid F) X.lim) :=
  Representative.limit X hX

/-- The actual completed block conditional projection preserves witnessed
gauge-polynomial completion, for every finite physical block. -/
def block (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    {x : GNSCompletionSpace F} (a : Witness hw0 hw1 K extent hK x) :
    Witness hw0 hw1 K extent hK
      (conditionalProjection hw0 hw1 K extent hK links hl x) :=
  a.map (conditionalDenseMap hw0 hw1 K extent hK links hl)
    (fun p hp n tags => conditionalRep_invariant hw0 hw1 K extent hK links hl tags p (hp tags) n)

#print axioms GaugePolynomial
#print axioms ofPolynomial
#print axioms polynomial_zero
#print axioms polynomial_add
#print axioms polynomial_neg
#print axioms polynomial_smul
#print axioms zero
#print axioms constant
#print axioms add
#print axioms sub
#print axioms scale
#print axioms limit
#print axioms block

end YMGap.Continuum.BF4ExactSlabGaugeRepresentedCompletion
