/-
# Time additivity of the actual centered finite torus RP pairing

Reflect the first OWN-centered root and translate both physical roots by x.
The reflected root at time 1+x lands at time zero, while the second root at
time 1+y lands at time 1+x+y. The complete Wilson weight and the OWN means
are transported by the existing weighted-pair translation theorem.

This supplies the actual `hshift` consumer of `SU2ClusterBridge.torus_gap_bridge`
in the finite physical range. Positive-half support is proved in its companion
leaf; a torus transfer, physical scaling and the continuum/Clay target stay open.
-/

import YMGap.Continuum.SU2TorusCenteredCovarianceRP
import YMGap.Continuum.SU2TorusOwnMeanTimeShift

namespace YMGap.Continuum.SU2TorusCenteredPairShift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq Z4Plane dirsOf)
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (pe_haar pe_mulR)
open YMGap.Continuum.SU2WilsonCenteredCovariance (weight centeredCharacter)
open YMGap.Continuum.SU2TorusRPOwnMeanReflection (theta_centeredCharacter)
open YMGap.Continuum.SU2TorusOwnMeanTimeShift (centered_pair_moment_timeShift)
open YMGap.Continuum.SU2TorusCenteredCovarianceRP (root tau response tau_zero)
open YMGap.Continuum.SU2TorusRPCSShape (rpB)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPGeom (rt rv)
open YMGap.Continuum.SU2TorusRPPlaqSplit (mem_tp)
open YMGap.Continuum.SU2TorusRPSym (mir_box)
open YMGap.Continuum.SU2TorusLinksTimeShift (shv_mem_torusPlaquettes)
open YMGap.Continuum.SU2TimeShift (shv vs)
open YMGap.Continuum.SU2LinkDecaySharpInst (betaS)

local infix:50 " ≈ " => Q'.eqv

variable {M : Nat} (hM : 1 ≤ M) (K b c d : Nat) (plane : Z4Plane)

local notation "Ls" => torusLinks (2 * M)
local notation "Ps" => torusPlaquettes (2 * M)
local notation "C" => centeredCharacter Ls (2 * M) K Ps
local notation "W" => weight Ls (2 * M) K Ps

/-- Two actual periodic root translations add their time parameters. -/
theorem shift_root_add (x y : Nat) :
    shv (2 * M) x (shv (2 * M) y (root b c d plane)) =
      shv (2 * M) (x + y) (root b c d plane) := by
  change ((((1 + y) % (2 * M) + x) % (2 * M), b, c, d), plane) =
    (((1 + (x + y)) % (2 * M), b, c, d), plane)
  rw [Nat.mod_add_mod]
  have he : 1 + y + x = 1 + (x + y) := by omega
  rw [he]

include hM in
/-- Translating the reflected time-(1+x) spatial root by x returns the
literal reflected time-one root. The finite-range guard prevents wrapping
before the explicit reflection formula is applied. -/
theorem shift_mirror_root (hsp : isT (dirsOf plane).1 = false)
    (x : Nat) (hx : x + 1 ≤ M) :
    shv (2 * M) x (mir M (shv (2 * M) x (root b c d plane))) =
      mir M (root b c d plane) := by
  have hp : shv (2 * M) x (root b c d plane) = ((1 + x, b, c, d), plane) := by
    change (((1 + x) % (2 * M), b, c, d), plane) = ((1 + x, b, c, d), plane)
    rw [Nat.mod_eq_of_lt (show 1 + x < 2 * M by omega)]
  have hm : mir M (root b c d plane) = ((0, b, c, d), plane) := by
    unfold root mir
    rw [hsp]
    rfl
  rw [hp, hm]
  unfold mir
  rw [hsp]
  change (((rt M (1 + x) + x) % (2 * M), b, c, d), plane) =
    ((0, b, c, d), plane)
  cases x with
  | zero => simp [rt]
  | succ x =>
      rw [rt, if_neg (show 1 + (x + 1) ≠ 0 by omega),
        if_neg (show 1 + (x + 1) ≠ 1 by omega)]
      have he : 2 * M + 1 - (1 + (x + 1)) + (x + 1) = 2 * M := by omega
      rw [he, Nat.mod_self]

private theorem rpB_centered (p : Z4Plaq) (hp : p ∈ Ps)
    (hsp : isT (dirsOf p.2).1 = false) (q : Z4Plaq) :
    rpB hM betaS K (C p) (C q) ≈
      quaternionHaar (Ls).length (polyMul (polyMul (C (mir M p)) (C q)) W) :=
  pe_haar _ (pe_mulR _ W (pe_mulR _ (C q)
    (theta_centeredCharacter hM K p hp hsp)))

/-- Actual time additivity of the OWN-centered RP pairing for physical
spatial roots; reflection and translation invariance are proved inputs. -/
theorem pairing_shift (hb : b < 2 * M) (hc : c < 2 * M) (hd : d < 2 * M)
    (hsp : isT (dirsOf plane).1 = false) (x y : Nat) (hxy : x + y + 1 ≤ M) :
    rpB hM betaS K (tau M K b c d plane x) (tau M K b c d plane y) ≈
      response hM K b c d plane (x + y) := by
  have hp : root b c d plane ∈ Ps := by
    apply (mem_tp _).mpr
    change 1 < 2 * M ∧ b < 2 * M ∧ c < 2 * M ∧ d < 2 * M
    exact ⟨by omega, hb, hc, hd⟩
  have hpx := shv_mem_torusPlaquettes (show 0 < 2 * M by omega) x _ hp
  have hpy := shv_mem_torusPlaquettes (show 0 < 2 * M by omega) y _ hp
  have hmx : mir M (shv (2 * M) x (root b c d plane)) ∈ Ps :=
    (mem_tp _).mpr (mir_box hM _ ((mem_tp _).mp hpx))
  have href := rpB_centered hM K (shv (2 * M) x (root b c d plane)) hpx hsp
    (shv (2 * M) y (root b c d plane))
  have hpair := centered_pair_moment_timeShift hM K x
    (mir M (shv (2 * M) x (root b c d plane))) hmx
    (shv (2 * M) y (root b c d plane)) hpy
  rw [shift_mirror_root hM b c d plane hsp x (by omega),
    shift_root_add b c d plane x y] at hpair
  have hresponse := rpB_centered hM K (root b c d plane) hp hsp
    (shv (2 * M) (x + y) (root b c d plane))
  unfold response
  rw [tau_zero hM K b c d plane]
  exact Q'.eqv_trans _ _ _ href
    (Q'.eqv_trans _ _ _ hpair (Q'.eqv_symm hresponse))

/-- The exact finite-range `hshift` argument of `torus_gap_bridge`. -/
theorem hshift (hb : b < 2 * M) (hc : c < 2 * M) (hd : d < 2 * M)
    (hsp : isT (dirsOf plane).1 = false) (X : Nat) (hX : 2 * X + 1 ≤ M) :
    ∀ x y, x ≤ X → y ≤ X →
      rpB hM betaS K (tau M K b c d plane x) (tau M K b c d plane y) ≈
        response hM K b c d plane (x + y) :=
  fun x y hx hy => pairing_shift hM K b c d plane hb hc hd hsp x y (by omega)

end YMGap.Continuum.SU2TorusCenteredPairShift

#print axioms YMGap.Continuum.SU2TorusCenteredPairShift.shift_root_add
#print axioms YMGap.Continuum.SU2TorusCenteredPairShift.shift_mirror_root
#print axioms YMGap.Continuum.SU2TorusCenteredPairShift.pairing_shift
#print axioms YMGap.Continuum.SU2TorusCenteredPairShift.hshift
