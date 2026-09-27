/-
# No positive-time extinction under witnessed dyadic continuity

The square and self-adjointness laws of time maps at 2^-n identify a
correlator with the squared norm at the next half-time. A zero endpoint
correlator therefore annihilates every later dyadic image. An explicit
continuity modulus and separated squared distance force the source to be zero.

These are conditional theorems about actual maps, not a new frontier bundle
or a construction of continuum time. Applying them to a lattice scaling limit
still requires the SAME-theory endpoint pairing pin and the dyadic maps and
continuity. Integer-time extinction alone does not supply those hypotheses.
-/

import YMGap.Continuum.GNSTransferMetric

namespace YMGap.Continuum.DyadicTimeNonextinction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient

section Abstract

variable {V : Type} (zero : V) (B : V → V → RC) (S : Nat → V → V)
  (square : ∀ n x, S n x = S (n+1) (S (n+1) x))
  (selfAdjoint : ∀ n x y, B (S n x) y = B x (S n y))

include square selfAdjoint

/-- Only the actual same-carrier square law is used; there is no spectral
theorem, choice of an eigenvector, or arbitrary dyadic interpolation. -/
theorem halfTime_norm (n : Nat) (x : V) :
    B (S (n+1) x) (S (n+1) x) = B x (S n x) := by
  rw [selfAdjoint, ← square]

variable (zero_right : ∀ x, B x zero = RCzero)
  (norm_zero : ∀ x, B x x = RCzero → x = zero)

include zero_right norm_zero

/-- Vanishing propagates to every smaller positive dyadic time. -/
theorem dyadic_images_zero (x : V) (h : B x (S 0 x) = RCzero) (n : Nat) :
    S (n+1) x = zero := by
  induction n with
  | zero =>
      exact norm_zero _ ((halfTime_norm B S square selfAdjoint 0 x).trans h)
  | succ n ih =>
      apply norm_zero
      rw [halfTime_norm B S square selfAdjoint (n+1) x, ih, zero_right]

/-- Continuity is witnessed data at this vector. The proof samples the
explicit index `modulus epsilon + 1`, where the dyadic image is already zero. -/
theorem eq_zero_of_endpoint_zero
    (dist : V → V → RC)
    (separated : ∀ x y, (∀ epsilon : Q', (0 : Q') < epsilon →
      RCle (dist x y) (Quotient.mk crealSetoid (ofQ' epsilon))) → x = y)
    (x : V) (modulus : Q' → Nat)
    (continuous : ∀ epsilon : Q', (0 : Q') < epsilon → ∀ n,
      modulus epsilon ≤ n →
      RCle (dist x (S n x)) (Quotient.mk crealSetoid (ofQ' epsilon)))
    (h : B x (S 0 x) = RCzero) : x = zero := by
  apply separated
  intro epsilon he
  have hnear := continuous epsilon he (modulus epsilon+1) (Nat.le_succ _)
  rw [dyadic_images_zero zero B S square selfAdjoint zero_right norm_zero x h
    (modulus epsilon)] at hnear
  exact hnear

/-- A supplied zero scalar limit is usable only through an exact pin to
THIS endpoint autocorrelation. Neither the pin nor time maps are constructed. -/
theorem eq_zero_of_zero_limit_pin
    (dist : V → V → RC)
    (separated : ∀ x y, (∀ epsilon : Q', (0 : Q') < epsilon →
      RCle (dist x y) (Quotient.mk crealSetoid (ofQ' epsilon))) → x = y)
    (x : V) (modulus : Q' → Nat)
    (continuous : ∀ epsilon : Q', (0 : Q') < epsilon → ∀ n,
      modulus epsilon ≤ n →
      RCle (dist x (S n x)) (Quotient.mk crealSetoid (ofQ' epsilon)))
    (limit : CReal) (limit_zero : Equiv limit czero)
    (pin : Quotient.mk crealSetoid limit = B x (S 0 x)) : x = zero :=
  eq_zero_of_endpoint_zero zero B S square selfAdjoint zero_right norm_zero
    dist separated x modulus continuous (pin.symm.trans (Quotient.sound limit_zero))

end Abstract

section CompletedGNS

variable (D : GNSData)

private theorem completed_norm_zero (x : GNSCompletionSpace D)
    (h : D.cinnerCompl x x = RCzero) : x = embedV D D.zero := by
  have hz : RCsub RCzero RCzero = RCzero :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.add_neg_self_eqv 0))
  apply GNSDenseCompletionLaws.eq_of_distance_le_zero
  rw [D.cinnerCompl_cSub_left, D.cinnerCompl_embedZero_left,
    D.cinnerCompl_comm x (D.cSub x (embedV D D.zero)), D.cinnerCompl_cSub_left,
    D.cinnerCompl_embedZero_left, h, hz, hz]
  exact RCle_refl _

/-- The separation and positive-definiteness inputs are proved for the
existing GNS completion. This can be a reflected datum when legitimately
constructed; it is not an identification of an ordinary GNS form with OS. -/
theorem completed_eq_zero_of_endpoint_zero
    (time : Nat → GNSCompletionSpace D → GNSCompletionSpace D)
    (time_square : ∀ n x, time n x = time (n+1) (time (n+1) x))
    (time_selfAdjoint : ∀ n x y, D.cinnerCompl (time n x) y =
      D.cinnerCompl x (time n y))
    (x : GNSCompletionSpace D) (modulus : Q' → Nat)
    (continuous : ∀ epsilon : Q', (0 : Q') < epsilon → ∀ n,
      modulus epsilon ≤ n →
      RCle (GNSTransferMetric.distanceSq D x (time n x))
        (Quotient.mk crealSetoid (ofQ' epsilon)))
    (h : D.cinnerCompl x (time 0 x) = RCzero) : x = embedV D D.zero :=
  eq_zero_of_endpoint_zero (embedV D D.zero) D.cinnerCompl time time_square time_selfAdjoint
    D.cinnerCompl_embedZero_right (completed_norm_zero D)
    (GNSTransferMetric.distanceSq D) (GNSTransferMetric.eq_of_forall_small D)
    x modulus continuous h

end CompletedGNS

end YMGap.Continuum.DyadicTimeNonextinction

#print axioms YMGap.Continuum.DyadicTimeNonextinction.halfTime_norm
#print axioms YMGap.Continuum.DyadicTimeNonextinction.dyadic_images_zero
#print axioms YMGap.Continuum.DyadicTimeNonextinction.eq_zero_of_endpoint_zero
#print axioms YMGap.Continuum.DyadicTimeNonextinction.eq_zero_of_zero_limit_pin
#print axioms YMGap.Continuum.DyadicTimeNonextinction.completed_eq_zero_of_endpoint_zero
