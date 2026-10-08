/-
# Normalised-covariance form of the finite torus ratio inequality (volume-uniform constant)

`actual_torus_ratio` (SU2TorusCenteredFiniteRatio) bounds `E(k) = response(2k)` with prefactor `Z·(Cw·λ)`, where
`Z` is the unnormalised torus partition function.  Since `response n ≈ Z · cov n` (`hcov`), this file states the
same inequality for the normalised covariance `Ê(k) := cov(2k) = E(k)/Z`, cancelling `Z^{e+1} > 0`:

  `Ê(k+1)^e · Ê(k) ≤ (Cw·λ) · (λ²)^{k+e} · Ê(k)^e`,   `λ = 6/7`.

The constant `Cw·λ` contains no `Z`: it is uniform in K and in the volume (M).  Nothing is carried beyond the
range `2X+1 ≤ M`, the in-box root (`b,c,d < 2M`) and a spatial plane.
Scope: one spatial plaquette at time 1, strong coupling β_S = 1/(2·10¹²), Wilson `T_K` at fixed K (constants
uniform in K and volume), also true for U(1), not gap evidence.  This is a finite response inequality, not a
transfer operator, an every-vector bound or a mass gap.
-/

import YMGap.Continuum.SU2TorusCenteredFiniteRatio
import YMGap.Continuum.HeatKernelConvGen

namespace YMGap.Continuum.SU2TorusNormalizedRatio

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plane dirsOf)
open YMGap.Continuum.SU2TorusCenteredCovarianceRP (response hcov)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusGapCond (E pow_two_mul)
open YMGap.Continuum.SU2WilsonTrunc (Cw)
open YMGap.Continuum.PolymerLatticeDecay (lam)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

theorem pow_congr {a b : Q'} (h : a ≈ b) : ∀ n : Nat, a ^ n ≈ b ^ n
  | 0 => Q'.eqv_refl 1
  | n + 1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a b _ h) (Q'.mul_eqv_congr_left b _ _ (pow_congr h n))

theorem mul_pow (a b : Q') : ∀ n : Nat, (a * b) ^ n ≈ a ^ n * b ^ n
  | 0 => (by decide : (1 : Q') ≈ 1 * 1)
  | n + 1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (a * b) _ _ (mul_pow a b n))
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
        (fun | 0 => a | 1 => b | 2 => a ^ n | _ => b ^ n))

/-- The normalised covariance `Ê(m) = cov(2m)` (`= E(m)/Z` by `hcov`). -/
abbrev Ehat {M : Nat} (K b c d : Nat) (plane : Z4Plane) (m : Nat) : Q' :=
  SU2ClusterBridge.cov K b c d plane (2 * m) (M := M)

/-- **Normalised finite torus ratio inequality (PROVED).**  Constant `Cw·λ`, with no `Z`, so it is uniform
in K and volume.  Rate `(6/7)²` per step.  One spatial plaquette, strong coupling β_S, U(1)-true, not gap
evidence. -/
theorem normalized_torus_ratio {M : Nat} (hM : 1 ≤ M) (K b c d : Nat)
    (plane : Z4Plane) (hb : b < 2 * M) (hc : c < 2 * M) (hd : d < 2 * M)
    (hsp : isT (dirsOf plane).1 = false) (X : Nat) (hX : 2 * X + 1 ≤ M)
    (k e : Nat) (hke : k + e ≤ X) :
    Ehat (M := M) K b c d plane (k + 1) ^ e * Ehat (M := M) K b c d plane k ≤
      (Cw * lam) * (lam * lam) ^ (k + e) * Ehat (M := M) K b c d plane k ^ e := by
  cases e with
  | zero =>
    have hcd := SU2ClusterBridge.cov_decay hM K b c d plane hsp (2 * k) (by omega)
    have hpin : Cw * lam ^ (2 * k + 1) ≈ (Cw * lam) * (lam * lam) ^ (k + 0) * 1 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left Cw _ _ (Q'.mul_eqv_congr_left lam _ _ (pow_two_mul lam k)))
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.const 1)) (by decide)
          (fun | 0 => Cw | 1 => lam | _ => (lam * lam) ^ k))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self _) (Q'.le_trans' _ _ _ hcd (Q'.le_of_eqv hpin))
  | succ e =>
    have h := SU2TorusCenteredFiniteRatio.actual_torus_ratio hM K b c d plane hb hc hd hsp X hX k (e + 1) hke
    have hcv := hcov hM K b c d plane hb hc hd hsp X hX
    unfold E at h
    have hE1 := hcv (2 * (k + 1)) (by omega)
    have hE0 := hcv (2 * k) (by omega)
    have hZ := SU2ClusterBridge.Z_pos hM K
    have hZp : (0 : Q') < SU2ClusterBridge.Z K (M := M) * SU2ClusterBridge.Z K (M := M) ^ (e + 1) :=
      Q'.mul_pos hZ (SU2ClusterBridge.pow_pos' hZ _)
    apply HKConvGen.mul_le_mul_left_cancel hZp
    have hL := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (pow_congr hE1 (e + 1)))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hE0)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (mul_pow _ _ (e + 1)))
          (poly_identity_of_normal_eq (.mul (.mul (.var 3) (.var 1)) (.mul (.var 0) (.var 2)))
            (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) (by decide)
            (fun | 0 => SU2ClusterBridge.Z K (M := M) | 1 => Ehat (M := M) K b c d plane (k + 1) ^ (e + 1)
                 | 2 => Ehat (M := M) K b c d plane k | _ => SU2ClusterBridge.Z K (M := M) ^ (e + 1)))))
    have hR := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (pow_congr hE0 (e + 1)))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (mul_pow _ _ (e + 1)))
        (poly_identity_of_normal_eq (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.var 4)))
          (.mul (.mul (.var 0) (.var 3)) (.mul (.mul (.var 1) (.var 2)) (.var 4))) (by decide)
          (fun | 0 => SU2ClusterBridge.Z K (M := M) | 1 => Cw * lam | 2 => (lam * lam) ^ (k + (e + 1))
               | 3 => SU2ClusterBridge.Z K (M := M) ^ (e + 1) | _ => Ehat (M := M) K b c d plane k ^ (e + 1))))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hR))

end YMGap.Continuum.SU2TorusNormalizedRatio
