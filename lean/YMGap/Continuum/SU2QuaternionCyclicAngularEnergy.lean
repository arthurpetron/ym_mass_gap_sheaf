/-
# Angular energy transported by cyclic coordinate rotation

The cyclic coordinate motion carries the energy at block `b` to the original
energy at block `(b+m) % n` after `m` steps.  This is an exact finite-Haar
identity and uses no raw polynomial equality across padded presentations.
-/

import YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
import YMGap.Continuum.SU2QuaternionAngularReindex

namespace YMGap.Continuum.SU2QuaternionCyclicAngularEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionBlockReversal
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
open YMGap.Continuum.QuaternionHaarAngularCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem one_rotation_block_energy (n b : Nat) (hn : 0 < n) (hb : b < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    quaternionHaar n (blockAngularSquare b (cycleRotation n p)) ≈
      quaternionHaar n (blockAngularSquare ((b+1)%n) p) := by
  let tailReindexed := reindexQuaternionPolynomial (reverseTailBlocks n) p
  have htail : SupportedQuaternionBlocks n tailReindexed := reindex_supported _ _
  have houter := reindex_blockAngularSquare_haar (reverseBlocks n) hb tailReindexed
  have hb' := (reverseBlocks n).map_lt b hb
  have hinner := reindex_blockAngularSquare_haar (reverseTailBlocks n) hb' p
  have houterChange := quaternionHaar_reindex (reverseBlocks n)
    (blockAngularSquare ((reverseBlocks n).map b) tailReindexed)
    (blockAngularSquare_supported hb' htail)
  have hinnerChange := quaternionHaar_reindex (reverseTailBlocks n)
    (blockAngularSquare ((reverseTailBlocks n).map ((reverseBlocks n).map b)) p)
    (blockAngularSquare_supported
      ((reverseTailBlocks n).map_lt _ hb') hp)
  have hsource := cycle_source n b hn hb
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm houter)
    (Q'.eqv_trans _ _ _ houterChange
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hinner)
        (Q'.eqv_trans _ _ _ hinnerChange
          (Q'.eqv_of_eq (congrArg (fun block =>
            quaternionHaar n (blockAngularSquare block p)) hsource)))))

theorem rotateIterate_blockAngularSquare_haar (n : Nat) (hn : 0 < n) :
    ∀ (m b : Nat), b < n → ∀ (p : RatPoly), SupportedQuaternionBlocks n p →
      quaternionHaar n (blockAngularSquare b (rotateIterate n m p)) ≈
        quaternionHaar n (blockAngularSquare ((b+m)%n) p)
  | 0, b, hb, _, _ => by
      rw [Nat.add_zero, Nat.mod_eq_of_lt hb]
      exact Q'.eqv_refl _
  | m+1, b, hb, p, hp => by
      have hstep := one_rotation_block_energy n b hn hb
        (rotateIterate n m p) (rotateIterate_supported n m hp)
      have hnext : (b+1)%n < n := Nat.mod_lt _ hn
      have hind := rotateIterate_blockAngularSquare_haar n hn m ((b+1)%n)
        hnext p hp
      exact Q'.eqv_trans _ _ _ hstep
        (Q'.eqv_trans _ _ _ hind
          (Q'.eqv_of_eq (congrArg (fun block =>
            quaternionHaar n (blockAngularSquare block p)) (by
              rw [Nat.add_mod ((b+1)%n) m, Nat.mod_mod, ← Nat.add_mod]
              congr 1
              omega))))

theorem rotateIterate_headAngularSquare_haar (n : Nat) (hn : 0 < n)
    (m : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    quaternionHaar n (blockAngularSquare 0 (rotateIterate n m p)) ≈
      quaternionHaar n (blockAngularSquare (m%n) p) := by
  simpa only [Nat.zero_add] using
    rotateIterate_blockAngularSquare_haar n hn m 0 hn p hp

theorem rotateIterate_headAngularSquare_haar_of_lt (n : Nat) (hn : 0 < n)
    (m : Nat) (hm : m < n) (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    quaternionHaar n (blockAngularSquare 0 (rotateIterate n m p)) ≈
      quaternionHaar n (blockAngularSquare m p) := by
  exact Q'.eqv_trans _ _ _ (rotateIterate_headAngularSquare_haar n hn m p hp)
    (Q'.eqv_of_eq (congrArg (fun block =>
      quaternionHaar n (blockAngularSquare block p)) (Nat.mod_eq_of_lt hm)))

end YMGap.Continuum.SU2QuaternionCyclicAngularEnergy

#print axioms YMGap.Continuum.SU2QuaternionCyclicAngularEnergy.rotateIterate_blockAngularSquare_haar
#print axioms YMGap.Continuum.SU2QuaternionCyclicAngularEnergy.rotateIterate_headAngularSquare_haar
#print axioms YMGap.Continuum.SU2QuaternionCyclicAngularEnergy.rotateIterate_headAngularSquare_haar_of_lt
