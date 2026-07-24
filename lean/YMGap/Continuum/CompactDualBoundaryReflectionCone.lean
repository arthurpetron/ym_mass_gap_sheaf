/-
# Compact-dual boundary state and rational reflection cone

This module is the structural/algebraic CD-1 step following
`CompactDualPinnedPhysicalData`.

For one reflected interface, Schur orthogonality identifies the intertwiner
channel with the representation label.  A finite boundary state is therefore
an actual `CharacterPacket` at the physical cutoff, and its interface
amplitude is the corresponding packet coefficient.  No independent
intertwiner tensor or reparameterized observable is introduced.

Using the exact rational packet weight `w^(4 C₂(s))`, this module constructs:

* the rational reflected pairing of two finite boundary packets;
* its diagonal self-Gram, a finite rational sum of squares;
* a Type-level reflection-cone certificate for every boundary state;
* the exact `CReal.Equiv` bridge from that rational Gram to the existing
  `ReflectionPositivity.diagReflForm`;
* the pinned specialization whose packet is definitionally the observable in
  `CompactDualPhysicalData` and whose constructive-real form is definitionally
  the already defined `CompactDualPhysicalData.reflectionForm`.

## Honest remaining interface

This closes the rational-`w` one-interface boundary cone.  It does not identify
the result with `ReflectionPositivity.reflSchwinger t ht`, whose weights are
the constructive-real exponentials `exp (-t C₂(s))`.  Such an identification
still needs either an exact coordinate witness or an explicit approximation
modulus comparing `ofQ'(w^(4 C₂(s)))` with `exp (-t C₂(s))`.

No block map, reflection-cone preservation under blocking, overlap remainder,
contraction estimate, or continuum statement is constructed here.

## Axiom gate

Definitions, finite rational sums, sum-of-squares positivity, and the existing
constructive-real setoid algebra only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or `noncomputable` declaration is used.
-/

import YMGap.Continuum.CompactDualPinnedPhysicalData
import YMGap.Continuum.CRealContinuumAlg
import YMGap.RG.TonelliFactor

namespace YMGap.Continuum.CompactDualBoundaryReflectionCone

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.CompactDualPinnedPhysicalData
open YMGap.Continuum.CompactDualPinnedPhysicalData.CompactDualPhysicalData
open YMGap.Continuum.SU2CharacterVacuumHaar

/-! ## Finite one-interface boundary packets -/

/-- A representation mode crossing the selected finite reflected interface. -/
abbrev BoundaryMode (D : CompactDualPhysicalData) :=
  Fin (D.cutoff + 1)

/-- A finite compact-dual boundary state at the exact physical cutoff.

The packet itself is the coefficient-bearing state.  In the one-interface
Schur basis, no additional recoupling/intertwiner choice is present. -/
structure DualBoundaryState (D : CompactDualPhysicalData) : Type where
  packet : CharacterPacket D.cutoff

namespace DualBoundaryState

/-- The finite Schur-channel amplitude of a boundary state. -/
def intertwinerAmplitude {D : CompactDualPhysicalData}
    (B : DualBoundaryState D) (mode : BoundaryMode D) : Q' :=
  B.packet.coeff mode

/-- Extend the finite Schur-channel amplitudes by zero outside the cutoff. -/
def coefficient {D : CompactDualPhysicalData}
    (B : DualBoundaryState D) (s : Nat) : Q' :=
  coeffAt B.packet s

/-- The physical boundary state selected by `D`; its packet is definitionally
the same observable packet already pinned into the RG state. -/
def pinned (D : CompactDualPhysicalData) : DualBoundaryState D where
  packet := D.observable

@[simp] theorem pinned_packet (D : CompactDualPhysicalData) :
    (pinned D).packet = D.observable :=
  rfl

@[simp] theorem pinned_coefficient (D : CompactDualPhysicalData) (s : Nat) :
    (pinned D).coefficient s = D.reflectedCoefficients s :=
  rfl

/-! ## Rational Schur pairing and self-Gram -/

/-- The exact rational Schur pairing
`Σ_{s≤K} left_s right_s w^(4 C₂(s))`. -/
def rationalReflectedPairing {D : CompactDualPhysicalData}
    (left right : DualBoundaryState D) : Q' :=
  finSum
    (fun s =>
      (left.coefficient s * right.coefficient s) *
        D.reflectionWeightQ s)
    (D.cutoff + 1)

/-- The rational reflected self-Gram of a finite boundary state. -/
def rationalReflectedGram {D : CompactDualPhysicalData}
    (B : DualBoundaryState D) : Q' :=
  rationalReflectedPairing B B

/-- Each diagonal Gram summand is nonnegative: it is a rational square times
the nonnegative rational heat-kernel weight from the same physical datum. -/
theorem rationalReflectedGramTerm_nonnegative
    {D : CompactDualPhysicalData} (B : DualBoundaryState D) (s : Nat) :
    (0 : Q') ≤
      (B.coefficient s * B.coefficient s) * D.reflectionWeightQ s :=
  Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg (B.coefficient s))
    (RGTransport.qpow_nonneg
      D.coupling D.coupling_nonnegative (RGTransport.c4 s))

/-- The rational reflected self-Gram is a finite sum of squares with
nonnegative weights, hence nonnegative for every boundary packet. -/
theorem rationalReflectedGram_nonnegative
    {D : CompactDualPhysicalData} (B : DualBoundaryState D) :
    (0 : Q') ≤ rationalReflectedGram B := by
  exact YMGap.RG.finSum_nonneg _
    (rationalReflectedGramTerm_nonnegative B) (D.cutoff + 1)

/-! ## Exact bridge to the existing diagonal reflection form -/

/-- The existing constructive-real diagonal reflection form applied to an
arbitrary boundary packet at the pinned coupling/cutoff. -/
def boundaryReflectionForm {D : CompactDualPhysicalData}
    (B : DualBoundaryState D) : CReal :=
  ReflectionPositivity.diagReflForm
    D.reflectionWeight B.coefficient (D.cutoff + 1)

/-- A finite sum of embedded rationals is setoid-equivalent to the embedding
of the exact rational finite sum. -/
theorem csum_ofQ'_finSum (g : Nat → Q') (N : Nat) :
    CReal.Equiv
      (CReal.csum (fun s => CReal.ofQ' (g s)) N)
      (CReal.ofQ' (finSum g N)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  rw [CReal.csum_approx]
  exact Q'.eqv_refl _

/-- The embedded rational Schur Gram is exactly the existing
constructive-real diagonal reflection form, modulo the repository's
constructive-real setoid equivalence. -/
theorem rationalReflectedGram_equiv_boundaryReflectionForm
    {D : CompactDualPhysicalData} (B : DualBoundaryState D) :
    CReal.Equiv
      (CReal.ofQ' (rationalReflectedGram B))
      (boundaryReflectionForm B) := by
  let term : Nat → Q' :=
    fun s => (B.coefficient s * B.coefficient s) * D.reflectionWeightQ s
  refine CReal.Equiv.trans
    (CReal.Equiv.symm (csum_ofQ'_finSum term (D.cutoff + 1))) ?_
  exact CRealContinuumAlg.csum_congr
    (fun s =>
      CRealAlg.ofQ'_mul
        (B.coefficient s * B.coefficient s)
        (D.reflectionWeightQ s))
    (D.cutoff + 1)

/-- The constructive-real boundary form is nonnegative for every finite
boundary packet.  This is the existing Schur-diagonal SOS theorem with the
exact rational physical weights. -/
theorem boundaryReflectionForm_nonnegative
    {D : CompactDualPhysicalData} (B : DualBoundaryState D) :
    ExpPos.geRat (boundaryReflectionForm B) 0 :=
  ReflectionPositivity.diagReflForm_nonneg
    D.reflectionWeight D.reflectionWeight_nonneg
    B.coefficient (D.cutoff + 1)

/-! ## Type-level reflection-cone certificate and pinned specialization -/

/-- A constructive certificate that one finite boundary state lies in the
rational Schur reflection cone and that its rational Gram is the same
constructive-real object as the existing diagonal reflection form.

The certificate is indexed by the actual `D` and `B`; it carries no substitute
coupling, cutoff, packet, weight family, or Gram value. -/
structure ReflectionConeCertificate
    {D : CompactDualPhysicalData} (B : DualBoundaryState D) : Type where
  rationalNonnegative :
    (0 : Q') ≤ rationalReflectedGram B
  embeddedGramEquiv :
    CReal.Equiv
      (CReal.ofQ' (rationalReflectedGram B))
      (boundaryReflectionForm B)
  constructiveRealNonnegative :
    ExpPos.geRat (boundaryReflectionForm B) 0

/-- Every finite one-interface boundary state has a constructive rational
Schur reflection-cone certificate. -/
def reflectionConeCertificate
    {D : CompactDualPhysicalData} (B : DualBoundaryState D) :
    ReflectionConeCertificate B where
  rationalNonnegative := rationalReflectedGram_nonnegative B
  embeddedGramEquiv := rationalReflectedGram_equiv_boundaryReflectionForm B
  constructiveRealNonnegative := boundaryReflectionForm_nonnegative B

/-- The pinned one-interface form is definitionally the existing
`CompactDualPhysicalData.reflectionForm`. -/
theorem pinned_boundaryReflectionForm_eq_existing
    (D : CompactDualPhysicalData) :
    boundaryReflectionForm (pinned D) = D.reflectionForm :=
  rfl

/-- Consequently, the embedded rational self-Gram of the actual pinned
observable is setoid-equivalent to the existing diagonal reflection form. -/
theorem pinned_rationalReflectedGram_equiv_existing
    (D : CompactDualPhysicalData) :
    CReal.Equiv
      (CReal.ofQ' (rationalReflectedGram (pinned D)))
      D.reflectionForm := by
  exact rationalReflectedGram_equiv_boundaryReflectionForm (pinned D)

/-- The physical observable selected by `D` carries the canonical Type-level
reflection-cone certificate. -/
def pinnedReflectionConeCertificate (D : CompactDualPhysicalData) :
    ReflectionConeCertificate (pinned D) :=
  reflectionConeCertificate (pinned D)

end DualBoundaryState

#print axioms DualBoundaryState.pinned_coefficient
#print axioms DualBoundaryState.rationalReflectedGramTerm_nonnegative
#print axioms DualBoundaryState.rationalReflectedGram_nonnegative
#print axioms DualBoundaryState.csum_ofQ'_finSum
#print axioms DualBoundaryState.rationalReflectedGram_equiv_boundaryReflectionForm
#print axioms DualBoundaryState.boundaryReflectionForm_nonnegative
#print axioms DualBoundaryState.reflectionConeCertificate
#print axioms DualBoundaryState.pinned_boundaryReflectionForm_eq_existing
#print axioms DualBoundaryState.pinned_rationalReflectedGram_equiv_existing
#print axioms DualBoundaryState.pinnedReflectionConeCertificate

end YMGap.Continuum.CompactDualBoundaryReflectionCone
