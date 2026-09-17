/-
# Arbitrary finite endpoint-compatible gauge words

A starting vertex and a finite list of (oriented link value, next vertex)
pairs carry the whole path as data. No vertex, link, endpoint or ordering is
selected from an existence assertion. Each factor is the existing polynomial
quaternion; reverse traversal uses its quaternion conjugate and swaps the
gauge endpoints, as proved by orientedGaugeLink_pin.

Adjacent vertex gauges telescope in the existing arbitrary-insertion Haar
relation, without commuting Hamilton factors or discarding spectators. A
closed word consequently preserves its scalar holonomy and every character.
This extends the algebraic four-edge cancellation to arbitrary word length.

The physical lattice placement and actual temporal-ledger substitution are
separate consumers. No claim of full observable coverage, representation in
the spatial union, or continuum OS/QFT reconstruction is made here.
-/

import YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

namespace YMGap.Continuum.SU2QuaternionHaarGaugeWord

set_option autoImplicit false

open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

/-- The value of a forward (false) or reversed (true) physical link. -/
def orientedValue : Bool → PolyQuaternion → PolyQuaternion
  | false, q => q
  | true, q => PolyQuaternion.conj q

/-- Reverse traversal starts at the raw link's finish, so its gauge endpoints
are swapped BEFORE taking the conjugate of the transformed raw value. -/
def orientedGaugeLink : Bool → PolyQuaternion → PolyQuaternion → PolyQuaternion → PolyQuaternion
  | false, start, q, finish => gaugeLink start q finish
  | true, start, q, finish => PolyQuaternion.conj (gaugeLink finish q start)

theorem orientedGaugeLink_pin (reverse : Bool) (start q finish : PolyQuaternion) :
    PolyQuaternionCoeffEqv (orientedGaugeLink reverse start q finish)
      (gaugeLink start (orientedValue reverse q) finish) := by
  cases reverse with
  | false => exact PolyQuaternionCoeffEqv.refl _
  | true => exact gaugeLink_conj finish q start

/-- Every intermediate and terminal vertex is explicitly stored in the list. -/
def finish {V : Type} (start : V) : List (PolyQuaternion × V) → V
  | [] => start
  | edge :: rest => finish edge.2 rest

/-- The original ordered, right-associated product of the supplied oriented values. -/
def word {V : Type} : List (PolyQuaternion × V) → PolyQuaternion
  | [] => PolyQuaternion.one
  | edge :: rest => PolyQuaternion.mul edge.1 (word rest)

/-- The same ordered path with the same shared vertex gauge at each junction. -/
def gaugeWord {V : Type} (gauge : V → PolyQuaternion) (start : V) :
    List (PolyQuaternion × V) → PolyQuaternion
  | [] => PolyQuaternion.one
  | edge :: rest => PolyQuaternion.mul (gaugeLink (gauge start) edge.1 (gauge edge.2))
      (gaugeWord gauge edge.2 rest)

private theorem haar_symm {blocks : Nat} {p q : PolyQuaternion}
    (h : PolyQuaternionHaarCarrierEqv blocks p q) : PolyQuaternionHaarCarrierEqv blocks q p :=
  ⟨HaarCarrierEqv.symm h.scalar, HaarCarrierEqv.symm h.iPart,
    HaarCarrierEqv.symm h.jPart, HaarCarrierEqv.symm h.kPart⟩

/-- All internal gauges cancel; only the supplied starting and ending gauges remain.
Unit norms are used through the full Haar ideal, not independent-link assumptions. -/
theorem gauge_word {V : Type} {blocks : Nat} (gauge : V → PolyQuaternion)
    (gaugeUnit : ∀ v, HaarCarrierEqv blocks (polyQuaternionNorm (gauge v)) polyOne)
    (start : V) (edges : List (PolyQuaternion × V)) :
    PolyQuaternionHaarCarrierEqv blocks (gaugeWord gauge start edges)
      (gaugeLink (gauge start) (word edges) (gauge (finish start edges))) := by
  induction edges generalizing start with
  | nil =>
      have h : PolyQuaternionHaarCarrierEqv blocks
          (gaugeLink (gauge start) PolyQuaternion.one (gauge start)) PolyQuaternion.one :=
        (PolyQuaternionHaarCarrierEqv.of_coeff
          ((PolyQuaternionCoeffEqv.mul_one (PolyQuaternion.conj (gauge start))).mul
            (PolyQuaternionCoeffEqv.refl (gauge start)))).trans
          (haarUnit_conj_mul (gaugeUnit start))
      exact haar_symm h
  | cons edge rest ih =>
      exact ((PolyQuaternionHaarCarrierEqv.refl blocks
        (gaugeLink (gauge start) edge.1 (gauge edge.2))).mul (ih edge.2)).trans
        (gaugeLink_compose (gaugeUnit edge.2) (gauge start) edge.1 (word rest)
          (gauge (finish edge.2 rest)))

/-- Closed endpoint data removes the last conjugation from the actual scalar word. -/
theorem closed_scalar {V : Type} {blocks : Nat} (gauge : V → PolyQuaternion)
    (gaugeUnit : ∀ v, HaarCarrierEqv blocks (polyQuaternionNorm (gauge v)) polyOne)
    (start : V) (edges : List (PolyQuaternion × V)) (closed : finish start edges = start) :
    HaarCarrierEqv blocks (gaugeWord gauge start edges).scalar (word edges).scalar := by
  have h := gauge_word gauge gaugeUnit start edges
  rw [closed] at h
  exact HaarCarrierEqv.trans h.scalar (gaugeLink_closed_scalar (gaugeUnit start) (word edges))

/-- All representation degrees, retaining arbitrary spectator insertions. -/
theorem closed_character {V : Type} {blocks : Nat} (gauge : V → PolyQuaternion)
    (gaugeUnit : ∀ v, HaarCarrierEqv blocks (polyQuaternionNorm (gauge v)) polyOne)
    (start : V) (edges : List (PolyQuaternion × V))
    (closed : finish start edges = start) (spin : Nat) :
    HaarCarrierEqv blocks
      (characterPolynomial (gaugeWord gauge start edges).scalar spin)
      (characterPolynomial (word edges).scalar spin) :=
  character_haar_congr (closed_scalar gauge gaugeUnit start edges closed) spin

#print axioms orientedValue
#print axioms orientedGaugeLink
#print axioms orientedGaugeLink_pin
#print axioms finish
#print axioms word
#print axioms gaugeWord
#print axioms gauge_word
#print axioms closed_scalar
#print axioms closed_character

end YMGap.Continuum.SU2QuaternionHaarGaugeWord
