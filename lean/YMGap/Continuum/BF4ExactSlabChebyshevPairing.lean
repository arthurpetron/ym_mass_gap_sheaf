/-
# Exact Chebyshev pairing before the original cone reaches the test

For the SAME full-action completion and B=S* S, the first component of the
existing coupled recurrence is T_n(c B-I). Before its sixteen-per-degree
cone reaches a localized test y, its pairing is exactly

  <T_n(c B-I)x,y> = T_n(c-1) <x,y>.

Normalization by the positive rational T_n(c-1) therefore preserves the
original pairing. This is an equality, with no contraction or decay input.
The conditional-sweep count is not physical time. Useful contraction of
the actual rescaled auxiliary vectors and continuum scaling remain open.
-/

import YMGap.Continuum.BF4ExactSlabChebyshevCone
import YMGap.Continuum.ChebyshevBound

namespace YMGap.Continuum.BF4ExactSlabChebyshevPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabBalancedCone
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabChebyshevCone
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private theorem scale_one (v : RC) : RCscale 1 v = v := by
  refine Quotient.inductionOn v ?_
  intro V
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.one_mul_eqv (V.approx n)))

private theorem scale_sub_one (c : Q') (v : RC) :
    RCsub (RCscale c v) v = RCscale (c + (-(1 : Q'))) v := by
  refine Quotient.inductionOn v ?_
  intro V
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.neg (.var 1)))
      (.mul (.add (.var 0) (.neg (.const 1))) (.var 1))
      (by decide) (fun | 0 => c | _ => V.approx n)))

private theorem scale_recurrence (z a b : Q') (v : RC) :
    RCsub (RCadd (RCscale z (RCscale a v)) (RCscale z (RCscale a v)))
      (RCscale b v) = RCscale (((2 : Q') * z) * a + (-b)) v := by
  refine Quotient.inductionOn v ?_
  intro V
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 3)))
        (.mul (.var 0) (.mul (.var 1) (.var 3))))
        (.neg (.mul (.var 2) (.var 3))))
      (.mul (.add (.mul (.mul (.const 2) (.var 0)) (.var 1))
        (.neg (.var 2))) (.var 3))
      (by decide) (fun | 0 => z | 1 => a | 2 => b | _ => V.approx n)))

private theorem scale_cancel (t : Q') (ht : (0 : Q') < t) (v : RC) :
    RCscale (Q'.recipPos t ht) (RCscale t v) = v := by
  refine Quotient.inductionOn v ?_
  intro V
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv t ht)))
        (Q'.one_mul_eqv (V.approx n)))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK

private theorem scalar_pair (c : Q') (x y : GNSCompletionSpace F) :
    (F).cinnerCompl ((S).cSmul c x) y = RCscale c ((F).cinnerCompl x y) :=
  (S).cinnerCompl_cSmul_left c x y

/-- One affine step has its exact scalar effect on a separated pairing. -/
theorem affine_cone_pairing (c : Q') (support testSupport : List Z4Link)
    (x y : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x)
    (hy : Localized hw0 hw1 K extent hK testSupport y)
    (hsep : LinksDisjoint (grow extent 16 support) testSupport) :
    (F).cinnerCompl (affine hw0 hw1 K extent hK c x) y =
      RCscale (c + (-(1 : Q'))) ((F).cinnerCompl x y) := by
  unfold affine
  rw [(F).cinnerCompl_cSub_left, scalar_pair,
    balanced_cone_pairing hw0 hw1 K extent hK support testSupport x y hx hy hsep,
    scale_sub_one]

/-- The actual coupled first component has the literal Chebyshev scalar
pairing at every order, provided its degree-n cone misses the test. -/
theorem coupled_cone_pairing (c : Q') (n : Nat)
    (support testSupport : List Z4Link) (x y : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x)
    (hy : Localized hw0 hw1 K extent hK testSupport y)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    (F).cinnerCompl (coupled hw0 hw1 K extent hK c x n).1 y =
      RCscale (Cheb.T n (c + (-(1 : Q')))) ((F).cinnerCompl x y) := by
  let Claim (k : Nat) : Prop :=
    LinksDisjoint (grow extent (16*k) support) testSupport →
    (F).cinnerCompl (coupled hw0 hw1 K extent hK c x k).1 y =
      RCscale (Cheb.T k (c + (-(1 : Q')))) ((F).cinnerCompl x y)
  have hzero : Claim 0 := by
    intro _
    exact (scale_one ((F).cinnerCompl x y)).symm
  have hone : Claim 1 := by
    intro h
    change (F).cinnerCompl
      (GNSChebyshevRecurrence.first (affine hw0 hw1 K extent hK c) x 1) y = _
    rw [GNSChebyshevRecurrence.first_one _ (affine_selfAdjoint hw0 hw1 K extent hK c)]
    exact affine_cone_pairing hw0 hw1 K extent hK c support testSupport x y hx hy h
  have hstep (k : Nat) (hk : Claim k) (hks : Claim (k+1)) : Claim (k+2) := by
    intro h
    have hs (j : Nat) (hj : j ≤ k+2) :
        LinksDisjoint (grow extent (16*j) support) testSupport := by
      intro i hi hit
      exact h i (grow_mono_steps extent (16*j) (16*(k+2)) support
        (by omega) i hi) hit
    have hl := coupled_first_localized hw0 hw1 K extent hK c (k+1) support x hx
    have hnext : LinksDisjoint
        (grow extent 16 (grow extent (16*(k+1)) support)) testSupport := by
      rw [← grow_add]
      have he : 16*(k+1)+16 = 16*(k+2) := by omega
      rwa [he]
    have ha := affine_cone_pairing hw0 hw1 K extent hK c
      (grow extent (16*(k+1)) support) testSupport
      (coupled hw0 hw1 K extent hK c x (k+1)).1 y hl hy hnext
    change (F).cinnerCompl (coupled hw0 hw1 K extent hK c x (k+2)).1 y = _
    rw [coupled_first_recurrence, (F).cinnerCompl_cSub_left,
      (F).cinnerCompl_cAdd_left, ha, hks (hs (k+1) (by omega)),
      hk (hs k (by omega)), scale_recurrence, Cheb.T_succ_succ]
  have hall : ∀ k, Claim k ∧ Claim (k+1) := by
    intro k
    induction k with
    | zero => exact ⟨hzero, hone⟩
    | succ k ih => exact ⟨ih.2, hstep k ih.1 ih.2⟩
  exact (hall n).1 hsep

/-- Computed normalization of the actual polynomial state. Only scalar
positivity is needed to form it; no rescaled operator bound is assumed. -/
def normalizedFirst (c : Q') (n : Nat)
    (ht : (0 : Q') < Cheb.T n (c + (-(1 : Q'))))
    (x : GNSCompletionSpace F) : GNSCompletionSpace F :=
  (S).cSmul (Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht)
    (coupled hw0 hw1 K extent hK c x n).1

/-- Normalization preserves the SAME pairing exactly before cone/test
contact. This theorem by itself gives neither a norm bound nor decay. -/
theorem normalizedFirst_pairing (c : Q') (n : Nat)
    (ht : (0 : Q') < Cheb.T n (c + (-(1 : Q'))))
    (support testSupport : List Z4Link) (x y : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x)
    (hy : Localized hw0 hw1 K extent hK testSupport y)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    (F).cinnerCompl (normalizedFirst hw0 hw1 K extent hK c n ht x) y =
      (F).cinnerCompl x y := by
  unfold normalizedFirst
  rw [scalar_pair, coupled_cone_pairing hw0 hw1 K extent hK c n
    support testSupport x y hx hy hsep, scale_cancel]

#print axioms affine_cone_pairing
#print axioms coupled_cone_pairing
#print axioms normalizedFirst
#print axioms normalizedFirst_pairing

end YMGap.Continuum.BF4ExactSlabChebyshevPairing
