/-
# Finite moment ratio inequality for the actual OWN-centered torus source

The existing cluster/log-convexity consumer now receives proved positive-link
support, actual weighted time-pair additivity and the SAME covariance identity.
There are no abstract `hsup`, `hshift` or `hcov` assumptions in this theorem.

Scope: fixed strong coupling betaS, finite Taylor-Wilson cutoff K, physical
spatial roots and the range 2*X+1 <= M. The rate is (6/7)^2 and the prefactor
contains the actual partition Z. This is a finite response inequality, not a
constructed torus transfer, an every-vector bound or a continuum mass gap.
-/

import YMGap.Continuum.SU2TorusCenteredPositiveSupport
import YMGap.Continuum.SU2TorusCenteredPairShift

namespace YMGap.Continuum.SU2TorusCenteredFiniteRatio

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plane dirsOf)
open YMGap.Continuum.SU2TorusCenteredCovarianceRP (tau response hcov)
open YMGap.Continuum.SU2TorusCenteredPositiveSupport (hsup)
open YMGap.Continuum.SU2TorusCenteredPairShift (hshift)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusGapCond (E)
open YMGap.Continuum.SU2WilsonTrunc (Cw)
open YMGap.Continuum.PolymerLatticeDecay (lam)

/-- The finite cluster ratio consumer on its actual OWN-centered torus family.
No support, translation or covariance identification is assumed. -/
theorem actual_torus_ratio {M : Nat} (hM : 1 ≤ M) (K b c d : Nat)
    (plane : Z4Plane) (hb : b < 2 * M) (hc : c < 2 * M) (hd : d < 2 * M)
    (hsp : isT (dirsOf plane).1 = false) (X : Nat) (hX : 2 * X + 1 ≤ M)
    (k e : Nat) (hke : k + e ≤ X) :
    E (response hM K b c d plane) (k + 1) ^ e *
        E (response hM K b c d plane) k ≤
      SU2ClusterBridge.Z K (M := M) * (Cw * lam) * (lam * lam) ^ (k + e) *
        E (response hM K b c d plane) k ^ e :=
  SU2ClusterBridge.torus_gap_bridge hM K b c d plane hsp
    (tau M K b c d plane) (response hM K b c d plane) X hX
    (hsup hM K b c d plane hb hc hd hsp X hX)
    (hshift hM K b c d plane hb hc hd hsp X hX)
    (hcov hM K b c d plane hb hc hd hsp X hX) k e hke

end YMGap.Continuum.SU2TorusCenteredFiniteRatio

#print axioms YMGap.Continuum.SU2TorusCenteredFiniteRatio.actual_torus_ratio
