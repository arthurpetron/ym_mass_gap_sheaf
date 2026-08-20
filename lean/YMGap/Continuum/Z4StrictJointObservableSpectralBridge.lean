/-
# Same-object bridge from strict-cylinder clustering to spectral support

The finite clustering theorem does not by itself identify an abstract
spectral model.  This module records the missing object-level obligation:
one fixed positive spectral model must represent the very same centered
strict-cylinder moments at every integer time, along a cofinal admissible
family of ambient boxes.

Once that identity is supplied, no norm-relative one-step estimate is
needed.  The existing constructive moment argument forces every coupled live
eigenvalue below the common rate `anchorEffectiveRatio^2 < 1`.  Additional
full-support and unused-tail hypotheses package the result as a located
spectral gap.

This file proves the implication; it does not manufacture the spectral
realization contract.
-/

import YMGap.Continuum.Z4StrictJointObservableGeometricClustering
import YMGap.Continuum.ClusteringImpliesGap

namespace YMGap.Continuum.Z4StrictJointObservableSpectralBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.LocatedSpectralGap
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockObservableCovariance
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrictJointObservableGeometricClustering

local infix:50 " ≈ " => Q'.eqv

/-- A spectral model representing the same centered strict-cylinder moments.

The radius may grow with time, but the spectral model, roots, and observable
are fixed.  This prevents an unrelated per-time or per-volume model from
being substituted into the moment argument. -/
structure StrictObservableSpectralRealization
    (base : Nat) (roots : List (List Nat))
    (coefficient : List Bool → Q') : Type where
  rootsCanonical : ∀ root, root ∈ roots →
    root ∈ canonicalSurfacePolymers base
  model : SpectralModel
  radius : Nat → Nat
  admissible : ∀ shift,
    strictQueryBase (base + (shift + shift)) ≤ radius shift
  moment_eqv : ∀ shift,
    corr model shift ≈
      anchorTwoBlockObservableCovariance
        (strictJointDoubledTimeLowerRootAtoms
          (admissible shift) rootsCanonical)
        (strictJointDoubledTimeUpperRootAtoms
          (admissible shift) rootsCanonical)
        coefficient coefficient

def StrictObservableSpectralRealization.prefactor
    {base : Nat} {roots : List (List Nat)}
    {coefficient : List Bool → Q'}
    (_realization : StrictObservableSpectralRealization
      base roots coefficient) : Q' :=
  strictObservablePositivePrefactor roots.length
    (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace roots.length)
    coefficient coefficient

theorem StrictObservableSpectralRealization.prefactor_pos
    {base : Nat} {roots : List (List Nat)}
    {coefficient : List Bool → Q'}
    (realization : StrictObservableSpectralRealization
      base roots coefficient) :
    (0 : Q') < realization.prefactor :=
  strictObservablePositivePrefactor_pos roots.length
    (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace roots.length)
    coefficient coefficient

/-- Same-object clustering: the represented spectral moment inherits the
common geometric envelope from the literal canonical polymer covariance. -/
theorem StrictObservableSpectralRealization.corr_le_geometric
    {base : Nat} {roots : List (List Nat)}
    {coefficient : List Bool → Q'}
    (realization : StrictObservableSpectralRealization
      base roots coefficient) (shift : Nat) :
    corr realization.model shift ≤
      realization.prefactor * anchorDoubledTimeRate ^ shift := by
  have hmoment := realization.moment_eqv shift
  have habs := strictDoubledTimeObservableCovariance_abs_le_geometric
    (realization.admissible shift) realization.rootsCanonical
    coefficient coefficient
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hmoment)
    (Q'.le_trans' _ _ _
      (Q'.le_abs_self
        (anchorTwoBlockObservableCovariance
          (strictJointDoubledTimeLowerRootAtoms
            (realization.admissible shift) realization.rootsCanonical)
          (strictJointDoubledTimeUpperRootAtoms
            (realization.admissible shift) realization.rootsCanonical)
          coefficient coefficient))
      habs)

/-- The load-bearing spectral conclusion: every live mode to which the fixed
observable couples has eigenvalue at most the common rate below one. -/
theorem StrictObservableSpectralRealization.coupled_eigen_le_rate
    {base : Nat} {roots : List (List Nat)}
    {coefficient : List Bool → Q'}
    (realization : StrictObservableSpectralRealization
      base roots coefficient) :
    ∀ i, i < realization.model.k →
      (0 : Q') < realization.model.w i →
      realization.model.lam i ≤ anchorDoubledTimeRate := by
  exact clustering_implies_coupled_le
    realization.model realization.prefactor anchorDoubledTimeRate
    realization.prefactor_pos anchorDoubledTimeRate_pos
    realization.corr_le_geometric

/-- If the chosen observable couples to every live mode and the total
sequence convention bounds unused slots, the same moment theorem yields a
genuine located gap for the represented finite spectral model. -/
def StrictObservableSpectralRealization.toLocatedSpectralGap
    {base : Nat} {roots : List (List Nat)}
    {coefficient : List Bool → Q'}
    (realization : StrictObservableSpectralRealization
      base roots coefficient)
    (liveCoupling : ∀ i, i < realization.model.k →
      (0 : Q') < realization.model.w i)
    (unusedTail : ∀ i, realization.model.k ≤ i →
      realization.model.lam i ≤ anchorDoubledTimeRate) :
    LocatedSpectralGap realization.model :=
  clustering_implies_located
    realization.model realization.prefactor anchorDoubledTimeRate
    realization.prefactor_pos anchorDoubledTimeRate_pos
    anchorDoubledTimeRate_lt_one realization.corr_le_geometric
    liveCoupling unusedTail

#print axioms StrictObservableSpectralRealization.corr_le_geometric
#print axioms StrictObservableSpectralRealization.coupled_eigen_le_rate
#print axioms StrictObservableSpectralRealization.toLocatedSpectralGap

end YMGap.Continuum.Z4StrictJointObservableSpectralBridge
