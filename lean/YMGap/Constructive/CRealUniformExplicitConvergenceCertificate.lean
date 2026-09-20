/-
# Uniform explicit CReal convergence certificates

Pointwise convergence certificates do not by themselves provide one modulus
for a family of cutoffs, volumes, couplings, or lattice spacings.  This file
records that distinction in the type: `P` is the explicitly chosen range of
admissible parameters, and the certificate stores one common term modulus and
one common approximation modulus for every `p : P`.

The compiler from `UniformModCauchyEv` requires the outer and inner Cauchy
moduli to agree with those common functions.  It therefore preserves, rather
than infers, parameter uniformity.  No parameter range, physical estimate,
continuum limit, or Clay conclusion is manufactured here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Constructive.CRealModCauchyExplicitConvergenceCertificate

namespace YMGap.Constructive

set_option autoImplicit false

namespace CReal

/-! ## A named parameter range with common moduli -/

/-- A convergence witness uniform over the explicitly supplied parameter type
`P`.  The type `P` is the parameter range; no hidden quantifier over a larger
cutoff, volume, or spacing domain is present. -/
structure UniformExplicitConvergenceCertificate
    (P : Type)
    (s : P → Nat → CReal)
    (limit : P → CReal) : Type 1 where
  modulus : Q' → Nat
  approximationModulus : Q' → Nat → Nat
  bound : ∀ p : P, ∀ ε : Q', (0 : Q') < ε →
    ∀ N : Nat, modulus ε ≤ N →
      ∀ n : Nat, approximationModulus ε N ≤ n →
        (s p N).approx n ≤ (limit p).approx n + ε ∧
          (limit p).approx n ≤ (s p N).approx n + ε

namespace UniformExplicitConvergenceCertificate

/-- Forgetting the common moduli yields pointwise propositional convergence,
without extracting any witness. -/
def toConvergesTo
    {P : Type}
    {s : P → Nat → CReal}
    {limit : P → CReal}
    (certificate : UniformExplicitConvergenceCertificate P s limit)
    (p : P) :
    CReal.ConvergesTo (s p) (limit p) := by
  intro ε hε
  refine ⟨certificate.modulus ε, fun N hN =>
    ⟨certificate.approximationModulus ε N, fun n hn =>
      certificate.bound p ε hε N hN n hn⟩⟩

end UniformExplicitConvergenceCertificate

/-- An eventual-outer Cauchy family whose outer and inner moduli are common
across the explicitly named parameter range.  The eventual approximation
threshold may still depend on the parameter and the pair of terms. -/
structure UniformModCauchyEv
    (P : Type)
    (s : P → Nat → CReal) : Type 1 where
  M : Q' → Nat
  reg : Nat → Q' → Nat
  certificate : ∀ p : P, ModCauchyEv (s p)
  modulus_eq : ∀ p : P, ∀ ε : Q',
    (certificate p).M ε = M ε
  regularity_eq : ∀ p : P, ∀ i : Nat, ∀ ε : Q',
    (certificate p).reg i ε = reg i ε

/-! ## The witness-preserving family compiler -/

/-- Compile common-modulus eventual Cauchy data into one explicit family
certificate.  The limit at each parameter is the diagonal completion of that
parameter's supplied Cauchy witness. -/
def UniformModCauchyEv.toExplicitConvergenceCertificate
    {P : Type}
    {s : P → Nat → CReal}
    (c : UniformModCauchyEv P s) :
    UniformExplicitConvergenceCertificate P s
      (fun p => completeLimitCauchy (s p) (c.certificate p)) where
  modulus := fun ε => c.M (HalfPow.half * (HalfPow.half * ε))
  approximationModulus := fun ε N =>
    max (c.reg N (HalfPow.half * (HalfPow.half * ε)))
      (HalfPow.half * (HalfPow.half * ε)).den
  bound := by
    intro p ε hε N hN n hn
    let pointwise :=
      ModCauchyEv.toExplicitConvergenceCertificate (c.certificate p)
    let q : Q' := HalfPow.half * (HalfPow.half * ε)
    have hM : (c.certificate p).M q ≤ N := by
      rw [c.modulus_eq p q]
      exact hN
    have happrox :
        max ((c.certificate p).reg N q) q.den ≤ n := by
      rw [c.regularity_eq p N q]
      exact hn
    exact pointwise.bound ε hε N hM n happrox

end CReal

end YMGap.Constructive

/-! ## Dependency gate -/

#print axioms
  YMGap.Constructive.CReal.UniformExplicitConvergenceCertificate.toConvergesTo
#print axioms
  YMGap.Constructive.CReal.UniformModCauchyEv.toExplicitConvergenceCertificate
