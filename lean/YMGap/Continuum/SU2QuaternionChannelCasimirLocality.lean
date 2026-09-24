/-
# Locality and list algebra for the literal active Casimir

This module exposes the six-plane form of the block operator, proves that an
independent block contributes zero, and reduces a full block partition to its
active sublist before the channel Casimir-square contraction is applied.
-/

import YMGap.Continuum.SU2QuaternionChannelCasimirSquare

namespace YMGap.Continuum.SU2QuaternionChannelCasimirLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare

local infix:50 " ≈ " => Q'.eqv

/-- The list definition of one block Casimir is the ordinary six-plane sum. -/
theorem blockAngularLaplacian_eq_six (block : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (blockAngularLaplacian block p)
      (six fun i j => blockAngularDerivative block i j
        (blockAngularDerivative block i j p)) := by
  unfold blockAngularLaplacian six
  exact (RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.refl _).add
    ((RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)))))

private theorem secondDerivative_independent_zero (block i j : Nat)
    (hi : i < 4) (hj : j < 4) (p : RatPoly)
    (hp : QuaternionBlockIndependent block p) :
    RatPolyCoeffEqv
      (blockAngularDerivative block i j
        (blockAngularDerivative block i j p)) polyZero := by
  have hfirst := angularDerivative_blockIndependent_zero hi hj hp
  exact (angularDerivative_congr (4*block+i) (4*block+j) hfirst).trans
    (angularDerivative_blockIndependent_zero hi hj
      (quaternionBlockIndependent_polyZero block))

/-- A block Casimir annihilates a polynomial independent of that block. -/
theorem blockAngularLaplacian_independent_zero (block : Nat) (p : RatPoly)
    (hp : QuaternionBlockIndependent block p) :
    RatPolyCoeffEqv (blockAngularLaplacian block p) polyZero := by
  refine (blockAngularLaplacian_eq_six block p).trans ?_
  unfold six
  exact (secondDerivative_independent_zero block 0 1 (by decide) (by decide) p hp).add
    ((secondDerivative_independent_zero block 0 2 (by decide) (by decide) p hp).add
      ((secondDerivative_independent_zero block 0 3 (by decide) (by decide) p hp).add
        ((secondDerivative_independent_zero block 1 2 (by decide) (by decide) p hp).add
          ((secondDerivative_independent_zero block 1 3 (by decide) (by decide) p hp).add
            (secondDerivative_independent_zero block 2 3 (by decide) (by decide) p hp)))))

/-- The active Casimir respects concatenation at coefficient equality. -/
theorem activeCasimirPolynomial_append (first second : List Nat) (p : RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial (first ++ second) p)
      (polyAdd (activeCasimirPolynomial first p)
        (activeCasimirPolynomial second p)) := by
  unfold activeCasimirPolynomial
  rw [List.map_append]
  exact (RatPolyCoeffEqv.polySum_append _ _).symm

private theorem polySum_map_perm (f : Nat → RatPoly) {first second : List Nat}
    (h : first.Perm second) :
    RatPolyCoeffEqv (polySum (first.map f)) (polySum (second.map f)) := by
  induction h with
  | nil => exact RatPolyCoeffEqv.refl polyZero
  | cons x h ih => exact (RatPolyCoeffEqv.refl (f x)).add ih
  | swap x y rest =>
      change RatPolyCoeffEqv
        (polyAdd (f y) (polyAdd (f x) (polySum (rest.map f))))
        (polyAdd (f x) (polyAdd (f y) (polySum (rest.map f))))
      exact (RatPolyCoeffEqv.add_assoc _ _ _).symm.trans
        (((RatPolyCoeffEqv.add_comm (f y) (f x)).add
          (RatPolyCoeffEqv.refl _)).trans
            (RatPolyCoeffEqv.add_assoc _ _ _))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Permuting the block list does not change the active Casimir polynomial. -/
theorem activeCasimirPolynomial_perm {first second : List Nat}
    (h : first.Perm second) (p : RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial first p)
      (activeCasimirPolynomial second p) := by
  exact polySum_map_perm (fun block => polyNeg (blockAngularLaplacian block p)) h

private theorem activeCasimirPolynomial_independent_zero : ∀ passive : List Nat,
    ∀ p : RatPoly, (∀ block, block ∈ passive → QuaternionBlockIndependent block p) →
      RatPolyCoeffEqv (activeCasimirPolynomial passive p) polyZero
  | [], _, _ => RatPolyCoeffEqv.refl polyZero
  | block::rest, p, hp => by
      change RatPolyCoeffEqv
        (polyAdd (polyNeg (blockAngularLaplacian block p))
          (activeCasimirPolynomial rest p)) polyZero
      exact ((RatPolyCoeffEqv.neg (blockAngularLaplacian_independent_zero block p
        (hp block List.mem_cons_self))).add
          (activeCasimirPolynomial_independent_zero rest p
            (fun i hi => hp i (List.mem_cons_of_mem block hi)))).trans
        (RatPolyCoeffEqv.add_zero polyZero)

/-- If `passive ++ active` covers all blocks and the source is independent of
the passive blocks, the full literal Casimir reduces to the active list. -/
theorem activeCasimirPolynomial_range_eq_active (n : Nat)
    (passive active : List Nat)
    (hcover : (passive ++ active).Perm (List.range n))
    (p : RatPoly)
    (hpassive : ∀ block, block ∈ passive → QuaternionBlockIndependent block p) :
    RatPolyCoeffEqv (activeCasimirPolynomial (List.range n) p)
      (activeCasimirPolynomial active p) := by
  exact (activeCasimirPolynomial_perm hcover.symm p).trans
    ((activeCasimirPolynomial_append passive active p).trans
      (((activeCasimirPolynomial_independent_zero passive p hpassive).add
        (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _)))

end YMGap.Continuum.SU2QuaternionChannelCasimirLocality

#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirLocality.blockAngularLaplacian_eq_six
#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirLocality.blockAngularLaplacian_independent_zero
#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirLocality.activeCasimirPolynomial_append
#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirLocality.activeCasimirPolynomial_perm
#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirLocality.activeCasimirPolynomial_range_eq_active
