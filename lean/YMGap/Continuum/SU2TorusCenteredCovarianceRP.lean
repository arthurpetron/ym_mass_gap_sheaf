/-
# The actual finite torus RP response is the OWN-centered covariance

At time one take the spatial plaquette character, centered at its OWN mean
for the same torus Wilson weight. At lag n use the translated root, again
centered at its OWN mean. Reflection and the checked finite covariance
identity prove the exact `hcov` input of `SU2ClusterBridge.torus_gap_bridge`.

All roots are physical: spatial coordinates are below 2M and n+1 ≤ M.
This is at the existing fixed betaS and finite K. Positive-link support and
the pairing shift law are proved in the named companion leaves; their finite
ratio consumer does not construct a transfer or continuum mass gap.
-/

import YMGap.Continuum.SU2TorusRPOwnMeanReflection
import YMGap.Continuum.SU2ClusterBridge

namespace YMGap.Continuum.SU2TorusCenteredCovarianceRP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq Z4Plane dirsOf)
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2HaarAlgebra (PE pe_haar pe_mulR)
open YMGap.Continuum.SU2WilsonCenteredCovariance
  (weight centeredCharacter centered_covariance)
open YMGap.Continuum.SU2TorusRPOwnMeanReflection (theta_centeredCharacter)
open YMGap.Continuum.SU2TorusRPCSShape (rpB)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPPlaqSplit (mem_tp)
open YMGap.Continuum.SU2TimeShift (shv vs)
open YMGap.Continuum.SU2LinkDecaySharpInst (betaS)

local infix:50 " ≈ " => Q'.eqv

/-- The physical spatial root at time one. -/
def root (b c d : Nat) (plane : Z4Plane) : Z4Plaq := ((1, b, c, d), plane)

/-- Actual translated roots, each centered at its OWN mean for the SAME weight. -/
def tau (M K b c d : Nat) (plane : Z4Plane) (n : Nat) : RatPoly :=
  centeredCharacter (torusLinks (2 * M)) (2 * M) K (torusPlaquettes (2 * M))
    (shv (2 * M) n (root b c d plane))

/-- The actual RP pairing with the time-one source. -/
def response {M : Nat} (hM : 1 ≤ M) (K b c d : Nat) (plane : Z4Plane)
    (n : Nat) : Q' := rpB hM betaS K (tau M K b c d plane 0) (tau M K b c d plane n)

variable {M : Nat} (hM : 1 ≤ M) (K b c d : Nat) (plane : Z4Plane)

include hM in
theorem tau_zero : tau M K b c d plane 0 =
    centeredCharacter (torusLinks (2 * M)) (2 * M) K (torusPlaquettes (2 * M))
      (root b c d plane) := by
  change centeredCharacter (torusLinks (2 * M)) (2 * M) K (torusPlaquettes (2 * M))
    (((1 + 0) % (2 * M), b, c, d), plane) =
      centeredCharacter (torusLinks (2 * M)) (2 * M) K (torusPlaquettes (2 * M))
        ((1, b, c, d), plane)
  rw [Nat.add_zero, Nat.mod_eq_of_lt (show 1 < 2 * M by omega)]

/-- Exact `hcov` on physical roots; no translated-mean identity is assumed. -/
theorem response_covariance (hb : b < 2 * M) (hc : c < 2 * M) (hd : d < 2 * M)
    (hsp : isT (dirsOf plane).1 = false) (n : Nat) (hn : n + 1 ≤ M) :
    response hM K b c d plane n ≈
      SU2ClusterBridge.Z K (M := M) * SU2ClusterBridge.cov K b c d plane n (M := M) := by
  let Ls := torusLinks (2 * M)
  let Ps := torusPlaquettes (2 * M)
  let p := root b c d plane
  let q := shv (2 * M) n p
  have hp : p ∈ Ps := by
    apply (mem_tp p).mpr
    change 1 < 2 * M ∧ b < 2 * M ∧ c < 2 * M ∧ d < 2 * M
    exact ⟨by omega, hb, hc, hd⟩
  have hm : mir M p = ((0, b, c, d), plane) := by
    unfold p root mir
    rw [hsp]
    rfl
  have hq : q = ((1 + n, b, c, d), plane) := by
    change (((1 + n) % (2 * M), b, c, d), plane) = ((1 + n, b, c, d), plane)
    rw [Nat.mod_eq_of_lt (show 1 + n < 2 * M by omega)]
  have hmp : mir M p ∈ Ps := by
    rw [hm]
    apply (mem_tp _).mpr
    change 0 < 2 * M ∧ b < 2 * M ∧ c < 2 * M ∧ d < 2 * M
    exact ⟨by omega, hb, hc, hd⟩
  have hqp : q ∈ Ps := by
    rw [hq]
    apply (mem_tp _).mpr
    change 1 + n < 2 * M ∧ b < 2 * M ∧ c < 2 * M ∧ d < 2 * M
    exact ⟨by omega, hb, hc, hd⟩
  have hne : mir M p ≠ q := by
    rw [hm, hq]
    intro he
    have ht := congrArg (fun r : Z4Plaq => r.1.1) he
    change 0 = 1 + n at ht
    omega
  have htheta : PE Ls.length
      (YMGap.Continuum.SU2TorusRPObs.thetaT hM (centeredCharacter Ls (2 * M) K Ps p))
      (centeredCharacter Ls (2 * M) K Ps (mir M p)) :=
    theta_centeredCharacter hM K p hp hsp
  have he := pe_haar Ls.length
    (pe_mulR Ls.length (weight Ls (2 * M) K Ps)
      (pe_mulR Ls.length (centeredCharacter Ls (2 * M) K Ps q) htheta))
  have hcov := centered_covariance Ls (2 * M) K Ps (mir M p) q
    (torusPlaquettes_nodup _) hmp hqp hne (SU2ClusterBridge.Z_pos hM K)
  unfold response
  rw [tau_zero hM K b c d plane]
  exact Q'.eqv_trans _ _ _ he hcov

/-- The existing cluster bridge's entire `hcov` argument in its finite range. -/
theorem hcov (hb : b < 2 * M) (hc : c < 2 * M) (hd : d < 2 * M)
    (hsp : isT (dirsOf plane).1 = false) (X : Nat) (hX : 2 * X + 1 ≤ M) :
    ∀ n, n ≤ 2 * X → response hM K b c d plane n ≈
      SU2ClusterBridge.Z K (M := M) * SU2ClusterBridge.cov K b c d plane n (M := M) :=
  fun n hn => response_covariance hM K b c d plane hb hc hd hsp n (by omega)

end YMGap.Continuum.SU2TorusCenteredCovarianceRP

#print axioms YMGap.Continuum.SU2TorusCenteredCovarianceRP.response_covariance
#print axioms YMGap.Continuum.SU2TorusCenteredCovarianceRP.hcov
