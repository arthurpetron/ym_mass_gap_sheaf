/-
# Exact period of the cyclic coordinate rotation

The coordinate motion separated from the fresh-output heat step is the
one-block cyclic rotation.  Its `n`th iterate is therefore the identity on
the actual `n`-block polynomial carrier.
-/

import YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation

namespace YMGap.Continuum.SU2QuaternionCyclicRotationPeriod

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionBlockReversal
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

def rotateIterate (n : Nat) : Nat → RatPoly → RatPoly
  | 0, p => p
  | m+1, p => cycleRotation n (rotateIterate n m p)

theorem rotateIterate_supported (n : Nat) : ∀ (m : Nat) {p : RatPoly},
    SupportedQuaternionBlocks n p →
      SupportedQuaternionBlocks n (rotateIterate n m p)
  | 0, _, hp => hp
  | m+1, _, _ =>
      reindex_supported (reverseBlocks n)
        (reindexQuaternionPolynomial (reverseTailBlocks n)
          (rotateIterate n m _))

theorem cycle_source (n i : Nat) (_hn : 0 < n) (hi : i < n) :
    (reverseTailBlocks n).map ((reverseBlocks n).map i) = (i+1) % n := by
  by_cases hlast : i+1 = n
  · have hi' : n-1-i = 0 := by omega
    rw [show (reverseBlocks n).map i=0 by simp [reverseBlocks, hi']]
    simp [reverseTailBlocks, hlast]
  · have hlt : i+1 < n := by omega
    have hr : n-1-i ≠ 0 := by omega
    rw [show (reverseBlocks n).map i=n-1-i by rfl]
    simp [reverseTailBlocks, hr, Nat.mod_eq_of_lt hlt]
    omega

private def rotateMonomial (n : Nat) : Nat → List Nat → List Nat
  | 0, monomial => monomial
  | m+1, monomial =>
      reindexQuaternionExponents (reverseBlocks n)
        (reindexQuaternionExponents (reverseTailBlocks n)
          (rotateMonomial n m monomial))

private theorem rotateIterate_map (n : Nat) : ∀ (m : Nat) (p : RatPoly),
    rotateIterate n m p = p.map (fun t => (rotateMonomial n m t.1, t.2))
  | 0, p => by simp [rotateIterate, rotateMonomial]
  | m+1, p => by
      rw [rotateIterate, rotateIterate_map n m p]
      simp only [cycleRotation, reindexQuaternionPolynomial, List.map_map]
      rfl

private theorem rotateMonomial_exponent (n : Nat) (hn : 0 < n) :
    ∀ (m : Nat) (monomial : List Nat) (j : Nat), j < 4*n →
      exponentAt (rotateMonomial n m monomial) j =
        exponentAt monomial (4*((j/4+m)%n)+j%4)
  | 0, monomial, j, hj => by
      simp only [rotateMonomial, Nat.add_zero, Nat.mod_eq_of_lt (by omega : j/4<n)]
      rw [show 4*(j/4)+j%4=j by omega]
  | m+1, monomial, j, hj => by
      rw [rotateMonomial]
      rw [exponentAt_reindexQuaternionExponents (reverseBlocks n) _ hj]
      have hb : j/4 < n := by omega
      have hrb := (reverseBlocks n).map_lt (j/4) hb
      have hc : 4*(reverseBlocks n).map (j/4)+j%4 < 4*n := by omega
      rw [exponentAt_reindexQuaternionExponents (reverseTailBlocks n) _ hc]
      rw [show (4*(reverseBlocks n).map (j/4)+j%4)/4 =
          (reverseBlocks n).map (j/4) by omega,
        show (4*(reverseBlocks n).map (j/4)+j%4)%4=j%4 by omega]
      rw [cycle_source n (j/4) hn hb]
      have hs : 4*((j/4+1)%n)+j%4 < 4*n := by
        have := Nat.mod_lt (j/4+1) hn
        omega
      rw [rotateMonomial_exponent n hn m monomial _ hs]
      have hblock : (4*((j/4+1)%n)+j%4)/4 = (j/4+1)%n := by omega
      have hcomponent : (4*((j/4+1)%n)+j%4)%4=j%4 := by omega
      rw [hblock, hcomponent]
      have he : (((j/4+1)%n)+m)%n = (j/4+(m+1))%n := by
        rw [Nat.add_mod ((j/4+1)%n) m, Nat.mod_mod, ← Nat.add_mod]
        exact congrArg (fun k => k % n) (by omega)
      rw [he]

private theorem rotateMonomial_period_prefix (n : Nat) (hn : 0 < n)
    (monomial : List Nat) (j : Nat) (hj : j < 4*n) :
    exponentAt (rotateMonomial n n monomial) j = exponentAt monomial j := by
  rw [rotateMonomial_exponent n hn n monomial j hj]
  have hb : j/4 < n := by omega
  simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hb]
  rw [show 4*(j/4)+j%4=j by omega]

theorem rotateIterate_period_prefix (n : Nat) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv n (rotateIterate n n p) p := by
  cases n with
  | zero =>
      exact QuaternionPrefixPolynomialEqv.refl 0 p
  | succ n =>
      rw [rotateIterate_map]
      induction p with
      | nil => exact .nil
      | cons t ts ih =>
          apply QuaternionPrefixPolynomialEqv.cons
          · exact ⟨Q'.eqv_refl _, fun j hj =>
              rotateMonomial_period_prefix (n+1) (by omega) t.1 j hj⟩
          · exact ih

theorem rotateIterate_period_carrier (n : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p) :
    HaarCarrierEqv n (rotateIterate n n p) p :=
  carrierOfPrefix (rotateIterate_supported n n hp) hp
    (rotateIterate_period_prefix n p)

end YMGap.Continuum.SU2QuaternionCyclicRotationPeriod

#print axioms YMGap.Continuum.SU2QuaternionCyclicRotationPeriod.rotateIterate
#print axioms YMGap.Continuum.SU2QuaternionCyclicRotationPeriod.rotateIterate_supported
#print axioms YMGap.Continuum.SU2QuaternionCyclicRotationPeriod.cycle_source
#print axioms YMGap.Continuum.SU2QuaternionCyclicRotationPeriod.rotateIterate_period_prefix
#print axioms YMGap.Continuum.SU2QuaternionCyclicRotationPeriod.rotateIterate_period_carrier
