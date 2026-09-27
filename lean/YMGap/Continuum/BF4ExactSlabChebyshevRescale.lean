/-
# Single-auxiliary-vector test for a rescaled original balanced sweep

The affine norm identity is on the existing completed full-action carrier.
The reverse-energy inequality below is an explicit hypothesis on one vector;
this module does not produce it, a centered coercivity estimate, or a gap.
-/

import YMGap.Continuum.BF4ExactSlabChebyshevPairing

namespace YMGap.Continuum.BF4ExactSlabChebyshevRescale

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabChebyshevPairing

private theorem scalar_expansion (c : Q') (a b d : RC) :
    RCsub (RCsub (RCscale c (RCscale c a)) (RCscale c b))
      (RCsub (RCscale c b) d) =
    RCsub (RCadd d (RCscale c (RCscale c a)))
      (RCscale c (RCscale 2 b)) := by
  refine Quotient.inductionOn₃ a b d ?_
  intro A B D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.var 0) (.mul (.var 0) (.var 1)))
          (.neg (.mul (.var 0) (.var 2))))
        (.neg (.add (.mul (.var 0) (.var 2)) (.neg (.var 3)))))
      (.add
        (.add (.var 3) (.mul (.var 0) (.mul (.var 0) (.var 1))))
        (.neg (.mul (.var 0) (.mul (.const 2) (.var 2)))))
      (by decide)
      (fun | 0 => c | 1 => A.approx n | 2 => B.approx n | _ => D.approx n)))

private theorem scaled_sub_norm (S : SmulGNSData) (c : Q')
    (b x : GNSCompletionSpace S.toGNSData) :
    normSq (S.toGNSData.cSub (S.cSmul c b) x) =
      RCsub (RCadd (normSq x) (RCscale c (RCscale c (normSq b))))
        (RCscale c (RCscale 2 (S.toGNSData.cinnerCompl b x))) := by
  let D := S.toGNSData
  have he (u v : GNSCompletionSpace D) : normSq (D.cSub u v) =
      RCsub (RCsub (normSq u) (D.cinnerCompl u v))
        (RCsub (D.cinnerCompl u v) (normSq v)) := by
    unfold normSq
    rw [D.cinnerCompl_cSub_left, D.cinnerCompl_comm u (D.cSub u v),
      D.cinnerCompl_cSub_left, D.cinnerCompl_comm v (D.cSub u v),
      D.cinnerCompl_cSub_left, D.cinnerCompl_comm v u]
  rw [he]
  unfold normSq
  rw [S.cinnerCompl_cSmul_left, S.cinnerCompl_cSmul_right,
    S.cinnerCompl_cSmul_left]
  exact scalar_expansion c _ _ _

private theorem sub_bound (a b z : RC) (h : RCle a b) :
    RCle (RCsub (RCadd z a) b) z := by
  have hh := RCadd_le_add
    (RCadd_le_add (RCle_refl z) h)
    (RCle_refl (RCneg b))
  have he (u v : RC) : RCsub (RCadd u v) v = u := by
    refine Quotient.inductionOn₂ u v ?_
    intro U V
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
        (by decide) (fun | 0 => U.approx n | _ => V.approx n)))
  change RCle _ (RCsub (RCadd z b) b) at hh
  rwa [he] at hh

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK
local notation "B" => Family.balanced (projections hw0 hw1 K extent hK) (schedule extent)
local notation "W" => Family.sweep (projections hw0 hw1 K extent hK) (schedule extent)

private theorem scalar_norm (c : Q') (x : GNSCompletionSpace F) :
    normSq ((S).cSmul c x) = RCscale c (RCscale c (normSq x)) := by
  calc
    normSq ((S).cSmul c x) =
        RCscale c ((F).cinnerCompl x ((S).cSmul c x)) :=
      (S).cinnerCompl_cSmul_left c x ((S).cSmul c x)
    _ = RCscale c (RCscale c (normSq x)) :=
      congrArg (RCscale c) ((S).cinnerCompl_cSmul_right c x x)

/-- Exact affine squared norm on the original full-action completion. -/
theorem affine_norm_expansion (c : Q') (u : GNSCompletionSpace F) :
    normSq (affine hw0 hw1 K extent hK c u) =
      RCsub (RCadd (normSq u) (RCscale c (RCscale c (normSq (B u)))))
        (RCscale c (RCscale 2 (normSq (W u)))) := by
  have he := scaled_sub_norm S c (B u) u
  change normSq (affine hw0 hw1 K extent hK c u) =
    RCsub (RCadd (normSq u) (RCscale c (RCscale c (normSq (B u)))))
      (RCscale c (RCscale 2 ((F).cinnerCompl (B u) u))) at he
  rw [(P).balanced_pairing] at he
  exact he

/-- One genuine reverse-energy comparison suffices to contract the affine
rescaling at this ONE vector. It is not asserted for arbitrary centered data. -/
theorem affine_norm_of_reverse_energy (c : Q') (hc : (0 : Q') ≤ c)
    (u : GNSCompletionSpace F)
    (hrev : RCle (RCscale c (normSq (B u)))
      (RCscale 2 (normSq (W u)))) :
    RCle (normSq (affine hw0 hw1 K extent hK c u)) (normSq u) := by
  rw [affine_norm_expansion]
  exact sub_bound _ _ _ (RCscale_mono hc hrev)

/-- The coupled first component needs the reverse-energy estimate only at
its actual auxiliary second component. No global invariant-sector premise is
introduced or discharged here. -/
theorem coupled_first_norm_from_reverse_energy (c : Q') (hc : (0 : Q') ≤ c)
    (x : GNSCompletionSpace F) (n : Nat)
    (hrev : let u := (coupled hw0 hw1 K extent hK c x n).2
      RCle (RCscale c (normSq (B u))) (RCscale 2 (normSq (W u)))) :
    RCle (normSq (coupled hw0 hw1 K extent hK c x n).1) (normSq x) :=
  GNSChebyshevEnergy.state_norm_le _
    (affine_selfAdjoint hw0 hw1 K extent hK c) x n
    (affine_norm_of_reverse_energy hw0 hw1 K extent hK c hc _ hrev)

/-- The SAME normalized vector used in the covariance pin has squared
norm bounded by the squared reciprocal Chebyshev value, conditional only
on the displayed actual auxiliary-vector estimate. -/
theorem normalizedFirst_norm_from_reverse_energy (c : Q') (hc : (0 : Q') ≤ c)
    (x : GNSCompletionSpace F) (n : Nat)
    (ht : (0 : Q') < Cheb.T n (c + (-(1 : Q'))))
    (hrev : let u := (coupled hw0 hw1 K extent hK c x n).2
      RCle (RCscale c (normSq (B u))) (RCscale 2 (normSq (W u)))) :
    RCle (normSq (normalizedFirst hw0 hw1 K extent hK c n ht x))
      (RCscale (Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht)
        (RCscale (Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht) (normSq x))) := by
  have hb := coupled_first_norm_from_reverse_energy hw0 hw1 K extent hK c hc x n hrev
  have hr : (0 : Q') ≤ Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht :=
    Q'.le_of_lt (Q'.recipPos_pos _ ht)
  have he : normSq (normalizedFirst hw0 hw1 K extent hK c n ht x) =
      RCscale (Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht)
        (RCscale (Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht)
          (normSq (coupled hw0 hw1 K extent hK c x n).1)) :=
    scalar_norm hw0 hw1 K extent hK _ _
  rw [he]
  exact RCscale_mono hr (RCscale_mono hr hb)

#print axioms affine_norm_expansion
#print axioms affine_norm_of_reverse_energy
#print axioms coupled_first_norm_from_reverse_energy
#print axioms normalizedFirst_norm_from_reverse_energy

end YMGap.Continuum.BF4ExactSlabChebyshevRescale
