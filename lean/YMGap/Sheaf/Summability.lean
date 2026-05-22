/-
The summability-certificate presheaf 𝒮_k (abstract scaffold).

Math statement (formal/sheaf-framework.tex §4, Definition 4.1):

    𝒮_k(U, X) = { (ρ, K) : a Kotecký–Preiss datum at (U, X) }.

For Milestone 2.1 we capture only the *structure* of a KP
certificate: a pair (ρ, K) in some value type `V`, together with a
proof of the regime-specific KP inequality (which inequality
exactly — small-field, large-field, overlap — is pinned in
Milestones 3.1–3.3).  The inequality predicate is an abstract
parameter `P : V → V → Prop`.

This file does NOT close the KP inequality for any concrete polymer
activity; that is the job of 3.1–3.3 (per AGENTS.md Rule 5).  It
provides the witness-bearing structure used by Sheaf.Gluing's
`Compatible` predicate.

Mirror: `formal/sheaf-framework.tex` Definition 4.1, Remark 4.2.
-/

import YMGap.Sheaf.Site

namespace YMGap.Sheaf

/-! ## KP certificate

A Kotecký–Preiss certificate is a pair (ρ, K) in some value type
`V`, plus a proof of the regime-specific KP inequality.  We
parametrize over `V` and the inequality predicate `P : V → V → Prop`
so the structure is regime-agnostic. -/

/-- A Kotecký–Preiss certificate carrying:

  * `rho : V` — the exponential decay rate witness,
  * `K : V` — the amplitude witness,
  * `satisfies : P rho K` — proof of the regime's KP inequality.

The predicate `P` is a parameter; concrete `P`s are supplied by
Milestones 3.1–3.3 for the small-field, large-field, and overlap
regimes respectively. -/
structure KPCertificate (V : Type) (P : V → V → Prop) where
  /-- Exponential decay rate. -/
  rho       : V
  /-- Amplitude. -/
  K         : V
  /-- KP inequality holds for this (ρ, K). -/
  satisfies : P rho K

namespace KPCertificate

variable {V : Type} {P : V → V → Prop}

/-- Trivial restriction: a KP certificate over `(U, X)` is also a
KP certificate over any sub-object of the site once the inequality
predicate is regime-fixed.  Since `P` is a parameter here, the
restriction is the identity — this file's role is to fix signatures
only. -/
def restrict (c : KPCertificate V P) : KPCertificate V P := c

end KPCertificate

end YMGap.Sheaf
