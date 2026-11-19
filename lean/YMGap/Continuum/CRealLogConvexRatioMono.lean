/-
# CReal log-convex ratio monotonicity under PosEv (Nat-lemma-only)

Additive port of `SU2LogConvexGap.ratio_mono` to eventual `CReal` order.
Strict positivity is `PosEv` (not mere nonnegativity): zeros cannot be
cancelled, so the inductive step uses `leEv_cancel_mul_right_posEv`.

Nat side-conditions use `Nat.add_assoc` / `Nat.le_of_succ_le` only (no tactic Nat automation).
Mathlib-free; U(1)-true as pure CReal arithmetic; not gap evidence.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity
import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.CRealLogConvexRatioMono

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TuranPositivity (PosEv geRat_zero_of_posEv)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (leEv_cancel_mul_right_posEv)

/-- Cross-multiplied log-convexity on `0..L` in eventual order. -/
def LogConvexEv (G : Nat → CReal) (L : Nat) : Prop :=
  ∀ j, j + 2 ≤ L → leEv (mul (G (j + 1)) (G (j + 1))) (mul (G j) (G (j + 2)))

/-- Strict positivity (`PosEv`) on `0..L`. -/
def PosEvSeq (G : Nat → CReal) (L : Nat) : Prop :=
  ∀ j, j ≤ L → PosEv (G j)

theorem nn {G : Nat → CReal} {L : Nat} (hp : PosEvSeq G L) {j : Nat}
    (hj : j ≤ L) : leEv czero (G j) :=
  geRat_zero_of_posEv (hp j hj)

private theorem hyp_as_add_two {i d L : Nat} (h : i + (d + 1) + 1 ≤ L) :
    i + d + 2 ≤ L := by
  have e : i + (d + 1) + 1 = i + d + 2 := by
    have e1 : i + (d + 1) = i + d + 1 := Nat.add_assoc i d 1
    rw [e1]
  exact e ▸ h

private theorem hyp_as_add_one {i d L : Nat} (h : i + (d + 1) + 1 ≤ L) :
    i + d + 1 ≤ L :=
  Nat.le_of_succ_le (hyp_as_add_two (i := i) (d := d) h)

private theorem le_succ_add_of_hyp {i d L : Nat} (h : i + (d + 1) + 1 ≤ L) :
    i + 1 ≤ L :=
  Nat.le_trans (Nat.le_add_right (i + 1) (d + 1)) (by
    have e : i + 1 + (d + 1) = i + (d + 1) + 1 := by
      rw [Nat.add_assoc i 1 (d + 1), Nat.add_comm 1 (d + 1), ← Nat.add_assoc]
    exact e ▸ h)

private theorem equiv_sw (a c : CReal) :
    Equiv (mul c (mul a c)) (mul a (mul c c)) :=
  SumOfSquares.Equiv_of_approx_eqv fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 0)))
      (.mul (.var 1) (.mul (.var 0) (.var 0)))
      (by decide) (fun | 0 => c.approx n | _ => a.approx n)

private theorem equiv_mul_comm (a b : CReal) :
    Equiv (mul a b) (mul b a) :=
  SumOfSquares.Equiv_of_approx_eqv fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 0))
      (by decide) (fun | 0 => a.approx n | _ => b.approx n)

private theorem equiv_mul_assoc (a b c : CReal) :
    Equiv (mul (mul a b) c) (mul a (mul b c)) :=
  SumOfSquares.Equiv_of_approx_eqv fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => a.approx n | 1 => b.approx n | _ => c.approx n)

private theorem equiv_mid (gi c gid2 : CReal) :
    Equiv (mul (mul gi c) gid2) (mul c (mul gi gid2)) :=
  SumOfSquares.Equiv_of_approx_eqv fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide)
      (fun | 0 => gi.approx n | 1 => c.approx n | _ => gid2.approx n)

private theorem le_e {a b c : CReal} (h : leEv a b) (e : Equiv b c) : leEv a c :=
  leEv_trans h (CReal.leEv_of_equiv e)

private theorem e_le {a b c : CReal} (e : Equiv a b) (h : leEv b c) : leEv a c :=
  leEv_trans (CReal.leEv_of_equiv e) h

/-- **Ratios do not decrease under `PosEv` (Nat-lemma-only).** -/
theorem ratio_mono {G : Nat → CReal} {L : Nat}
    (hp : PosEvSeq G L) (hc : LogConvexEv G L) (i : Nat) :
    ∀ d, i + d + 1 ≤ L →
      leEv (mul (G (i + 1)) (G (i + d))) (mul (G i) (G (i + d + 1)))
  | 0, _ => CReal.leEv_of_equiv (equiv_mul_comm _ _)
  | d + 1, h => by
    have ih := ratio_mono hp hc i d (hyp_as_add_one (i := i) (d := d) h)
    have cs := hc (i + d) (hyp_as_add_two (i := i) (d := d) h)
    have hcp : PosEv (G (i + d + 1)) :=
      hp (i + d + 1) (hyp_as_add_one (i := i) (d := d) h)
    let a := G (i + 1)
    let c := G (i + d + 1)
    let gi := G i
    let gid := G (i + d)
    let gid2 := G (i + d + 2)
    have step : leEv (mul c (mul a c)) (mul c (mul gi gid2)) := by
      refine e_le (equiv_sw a c) ?_
      refine leEv_trans
        (CReal.leEv_mul_nonneg_left
          (nn hp (le_succ_add_of_hyp (i := i) (d := d) h)) cs) ?_
      refine e_le (Equiv.symm (equiv_mul_assoc a gid gid2)) ?_
      have hx : leEv (mul (mul a gid) gid2) (mul (mul gi c) gid2) := by
        have hy : leEv (mul gid2 (mul a gid)) (mul gid2 (mul gi c)) :=
          CReal.leEv_mul_nonneg_left
            (nn hp (hyp_as_add_two (i := i) (d := d) h)) ih
        exact e_le (equiv_mul_comm _ _) (le_e hy (equiv_mul_comm _ _))
      exact leEv_trans hx (CReal.leEv_of_equiv (equiv_mid gi c gid2))
    have step' : leEv (mul (mul a c) c) (mul (mul gi gid2) c) := by
      refine e_le (Equiv.symm (equiv_mul_comm _ _)) ?_
      exact le_e step (equiv_mul_comm _ _)
    exact leEv_cancel_mul_right_posEv hcp step'

/-- Unbounded form. -/
def LogConvexEvInf (G : Nat → CReal) : Prop :=
  ∀ j, leEv (mul (G (j + 1)) (G (j + 1))) (mul (G j) (G (j + 2)))

def PosEvInf (G : Nat → CReal) : Prop :=
  ∀ j, PosEv (G j)

theorem ratio_mono_inf {G : Nat → CReal} (hp : PosEvInf G) (hc : LogConvexEvInf G)
    (i d : Nat) :
    leEv (mul (G (i + 1)) (G (i + d))) (mul (G i) (G (i + d + 1))) :=
  ratio_mono (fun j _ => hp j) (fun j _ => hc j) i d (Nat.le_refl _)

end YMGap.Continuum.CRealLogConvexRatioMono

/-! ## Axiom audit -/

#print axioms YMGap.Continuum.CRealLogConvexRatioMono.ratio_mono
#print axioms YMGap.Continuum.CRealLogConvexRatioMono.ratio_mono_inf
