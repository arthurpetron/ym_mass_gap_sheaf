/-
# Explicit CReal convergence certificates

`CReal.ConvergesTo` is intentionally a proposition: it says that a sequence
eventually approximates a limit.  A continuum construction needs the data that
make this statement usable, namely a term-stage modulus and an approximation
stage modulus.  This module keeps those moduli in a `Type`-level certificate
and only then projects to the existing propositional convergence interface.

The certificate is deliberately stronger than `CReal.ConvergesTo`: one
approximation threshold works for every term beyond the term-stage.  That
strength is useful when a finite observable estimate is transported through a
cutoff or volume limit.  No limit, uniformity, or continuum object is inferred
without supplying the corresponding fields.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Constructive.CRealAbs

namespace YMGap.Constructive

set_option autoImplicit false

namespace CReal

/-! ## A witness-bearing strengthening of `ConvergesTo` -/

/-- A convergence witness with executable term and approximation moduli.

`modulus ε` selects a term stage after which the estimate holds, while
`approximationModulus ε` selects one approximation stage that works uniformly
for every later term.  The latter is intentionally independent of the term
index: it is the shape needed for a certificate to survive a discrete-to-
continuous passage without reopening a hidden existential.
-/
structure ExplicitConvergenceCertificate
    (s : Nat → CReal) (limit : CReal) : Type 1 where
  modulus : Q' → Nat
  approximationModulus : Q' → Nat
  bound : ∀ ε : Q', (0 : Q') < ε →
    ∀ N : Nat, modulus ε ≤ N →
      ∀ n : Nat, approximationModulus ε ≤ n →
        (s N).approx n ≤ limit.approx n + ε ∧
          limit.approx n ≤ (s N).approx n + ε

namespace ExplicitConvergenceCertificate

/-- Forgetting the explicit moduli yields the repository's existing
propositional convergence statement.  The witness is constructed directly;
no choice is used to recover either threshold. -/
def toConvergesTo
    {s : Nat → CReal} {limit : CReal}
    (certificate : ExplicitConvergenceCertificate s limit) :
    CReal.ConvergesTo s limit := by
  intro ε hε
  refine ⟨certificate.modulus ε, fun N hN =>
    ⟨certificate.approximationModulus ε, fun n hn =>
      certificate.bound ε hε N hN n hn⟩⟩

end ExplicitConvergenceCertificate

end CReal

end YMGap.Constructive

/-! ## Axiom-dependency gate -/

#print axioms
  YMGap.Constructive.CReal.ExplicitConvergenceCertificate.toConvergesTo
