/-
# Completed rational recoupling of the four-valent SU(2) intertwiner

The invariant pairing relation `C + A = B` changes coefficient charts from
the basis `(A,B)` to `(B,C)`.  In the orthogonal coordinates of
`SU2FourValentIntertwinerGNSCompleted` the change of chart is

    R(s,d) = ((s-d)/2, (3s+d)/2).

This file proves constructively that `R` preserves the exact weighted form
`3 s^2 + d^2`, descends it to the GNS completion, and proves norm preservation
there.  The nonlinear cancellation identity is discharged by the existing
kernel-checked reflective `Q'` polynomial normaliser; the factor `1/2` is the
literal exact rational, not a floating-point input.

Honest scope: this is the first nontrivial recoupling move (four fundamental
legs).  Coherence for arbitrary labels and arbitrary recoupling trees remains
the finite-graph compatibility residual.
-/

import YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2FourValentRecouplingCompleted

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted

local infix:50 " ≈ " => Q'.eqv

/-! ## Reflective polynomial certificates -/

private def normPolyLeft : RingNormaliser.PolyExpr :=
  let s := RingNormaliser.PolyExpr.var 0
  let d := RingNormaliser.PolyExpr.var 1
  let p := RingNormaliser.PolyExpr.add s (.neg d)
  let q := RingNormaliser.PolyExpr.add (.mul (.const 3) s) d
  .add (.mul (.const 3) (.mul p p)) (.mul q q)

private def normPolyRight : RingNormaliser.PolyExpr :=
  let s := RingNormaliser.PolyExpr.var 0
  let d := RingNormaliser.PolyExpr.var 1
  .mul (.const 4)
    (.add (.mul (.const 3) (.mul s s)) (.mul d d))

private theorem normPoly_normal :
    RingNormaliser.normalize normPolyLeft =
      RingNormaliser.normalize normPolyRight := by decide

private theorem recoupling_cleared_norm (s d : Q') :
    3 * ((s + (-d)) * (s + (-d))) +
        (3 * s + d) * (3 * s + d) ≈
      4 * (3 * (s * s) + d * d) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    normPolyLeft normPolyRight normPoly_normal
    (fun | 0 => s | _ => d)
  simpa [normPolyLeft, normPolyRight, RingNormaliser.eval] using h

private def factorPolyLeft : RingNormaliser.PolyExpr :=
  let h := RingNormaliser.PolyExpr.var 0
  let s := RingNormaliser.PolyExpr.var 1
  let d := RingNormaliser.PolyExpr.var 2
  let p := RingNormaliser.PolyExpr.add s (.neg d)
  let q := RingNormaliser.PolyExpr.add (.mul (.const 3) s) d
  .add (.mul (.const 3) (.mul (.mul h p) (.mul h p)))
    (.mul (.mul h q) (.mul h q))

private def factorPolyRight : RingNormaliser.PolyExpr :=
  let h := RingNormaliser.PolyExpr.var 0
  let s := RingNormaliser.PolyExpr.var 1
  let d := RingNormaliser.PolyExpr.var 2
  let p := RingNormaliser.PolyExpr.add s (.neg d)
  let q := RingNormaliser.PolyExpr.add (.mul (.const 3) s) d
  .mul (.mul h h)
    (.add (.mul (.const 3) (.mul p p)) (.mul q q))

private theorem factorPoly_normal :
    RingNormaliser.normalize factorPolyLeft =
      RingNormaliser.normalize factorPolyRight := by decide

private theorem recoupling_factor_regroup (h s d : Q') :
    3 * ((h * (s + (-d))) * (h * (s + (-d)))) +
        (h * (3 * s + d)) * (h * (3 * s + d)) ≈
      (h * h) *
        (3 * ((s + (-d)) * (s + (-d))) +
          (3 * s + d) * (3 * s + d)) := by
  have hp := RingNormaliser.poly_identity_of_normal_eq
    factorPolyLeft factorPolyRight factorPoly_normal
    (fun | 0 => h | 1 => s | _ => d)
  simpa [factorPolyLeft, factorPolyRight, RingNormaliser.eval] using hp

private def subFirstLeft : RingNormaliser.PolyExpr :=
  let a := RingNormaliser.PolyExpr.var 0
  let b := RingNormaliser.PolyExpr.var 1
  let c := RingNormaliser.PolyExpr.var 2
  let d := RingNormaliser.PolyExpr.var 3
  let h := RingNormaliser.PolyExpr.var 4
  .mul h (.add (.add a (.neg c)) (.neg (.add b (.neg d))))

private def subFirstRight : RingNormaliser.PolyExpr :=
  let a := RingNormaliser.PolyExpr.var 0
  let b := RingNormaliser.PolyExpr.var 1
  let c := RingNormaliser.PolyExpr.var 2
  let d := RingNormaliser.PolyExpr.var 3
  let h := RingNormaliser.PolyExpr.var 4
  .add (.mul h (.add a (.neg b)))
    (.neg (.mul h (.add c (.neg d))))

private def subSecondLeft : RingNormaliser.PolyExpr :=
  let a := RingNormaliser.PolyExpr.var 0
  let b := RingNormaliser.PolyExpr.var 1
  let c := RingNormaliser.PolyExpr.var 2
  let d := RingNormaliser.PolyExpr.var 3
  let h := RingNormaliser.PolyExpr.var 4
  .mul h (.add (.mul (.const 3) (.add a (.neg c))) (.add b (.neg d)))

private def subSecondRight : RingNormaliser.PolyExpr :=
  let a := RingNormaliser.PolyExpr.var 0
  let b := RingNormaliser.PolyExpr.var 1
  let c := RingNormaliser.PolyExpr.var 2
  let d := RingNormaliser.PolyExpr.var 3
  let h := RingNormaliser.PolyExpr.var 4
  .add (.mul h (.add (.mul (.const 3) a) b))
    (.neg (.mul h (.add (.mul (.const 3) c) d)))

private theorem subFirst_normal :
    RingNormaliser.normalize subFirstLeft =
      RingNormaliser.normalize subFirstRight := by decide

private theorem subSecond_normal :
    RingNormaliser.normalize subSecondLeft =
      RingNormaliser.normalize subSecondRight := by decide

private theorem recoupling_sub_first
    (a b c d h : Q') :
    h * ((a + (-c)) + (-(b + (-d)))) ≈
      h * (a + (-b)) + (-(h * (c + (-d)))) := by
  have hp := RingNormaliser.poly_identity_of_normal_eq
    subFirstLeft subFirstRight subFirst_normal
    (fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => h)
  simpa [subFirstLeft, subFirstRight, RingNormaliser.eval] using hp

private theorem recoupling_sub_second
    (a b c d h : Q') :
    h * (3 * (a + (-c)) + (b + (-d))) ≈
      h * (3 * a + b) + (-(h * (3 * c + d))) := by
  have hp := RingNormaliser.poly_identity_of_normal_eq
    subSecondLeft subSecondRight subSecond_normal
    (fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => h)
  simpa [subSecondLeft, subSecondRight, RingNormaliser.eval] using hp

/-! ## Dense recoupling isometry -/

def half : Q' := Q'.mkPos 1 2 (by decide)

theorem half_square_four : (half * half) * 4 ≈ 1 := by decide

def intertwinerRecoupling (a : Q' × Q') : Q' × Q' :=
  (half * (a.1 + (-a.2)), half * (3 * a.1 + a.2))

theorem intertwinerRecoupling_map_veq {a b : Q' × Q'}
    (h : intertwinerGNS.veq a b) :
    intertwinerGNS.veq (intertwinerRecoupling a)
      (intertwinerRecoupling b) :=
  ⟨Q'.mul_eqv_congr_left half _ _
      (QPoly.q_add_congr h.1 (Q'.neg_eqv_congr _ _ h.2)),
    Q'.mul_eqv_congr_left half _ _
      (QPoly.q_add_congr
        (Q'.mul_eqv_congr_left 3 _ _ h.1) h.2)⟩

theorem intertwinerRecoupling_map_sub (a b : Q' × Q') :
    intertwinerGNS.veq
      (intertwinerRecoupling (intertwinerGNS.sub a b))
      (intertwinerGNS.sub
        (intertwinerRecoupling a) (intertwinerRecoupling b)) := by
  change
    half * ((a.1 + (-b.1)) + (-(a.2 + (-b.2)))) ≈
        half * (a.1 + (-a.2)) + (-(half * (b.1 + (-b.2)))) ∧
      half * (3 * (a.1 + (-b.1)) + (a.2 + (-b.2))) ≈
        half * (3 * a.1 + a.2) + (-(half * (3 * b.1 + b.2)))
  exact ⟨recoupling_sub_first a.1 a.2 b.1 b.2 half,
    recoupling_sub_second a.1 a.2 b.1 b.2 half⟩

private theorem recoupling_raw_regroup (s d : Q') :
    3 * ((half * (s + (-d))) * (half * (s + (-d)))) +
        (half * (3 * s + d)) * (half * (3 * s + d)) ≈
      (half * half) *
        (3 * ((s + (-d)) * (s + (-d))) +
          (3 * s + d) * (3 * s + d)) := by
  exact recoupling_factor_regroup half s d

theorem intertwinerRecoupling_norm (a : Q' × Q') :
    intertwinerGNS.B (intertwinerRecoupling a) (intertwinerRecoupling a) ≈
      intertwinerGNS.B a a := by
  change
    3 * ((half * (a.1 + (-a.2))) * (half * (a.1 + (-a.2)))) +
        1 * ((half * (3 * a.1 + a.2)) * (half * (3 * a.1 + a.2))) ≈
      3 * (a.1 * a.1) + 1 * (a.2 * a.2)
  refine Q'.eqv_trans _
    (3 * ((half * (a.1 + (-a.2))) * (half * (a.1 + (-a.2)))) +
      (half * (3 * a.1 + a.2)) * (half * (3 * a.1 + a.2))) _
    (QPoly.q_add_congr (Q'.eqv_refl _) (Q'.one_mul_eqv _)) ?_
  refine Q'.eqv_trans _
    ((half * half) *
      (3 * ((a.1 + (-a.2)) * (a.1 + (-a.2))) +
        (3 * a.1 + a.2) * (3 * a.1 + a.2))) _
    (recoupling_raw_regroup a.1 a.2) ?_
  refine Q'.eqv_trans _
    ((half * half) * (4 * (3 * (a.1 * a.1) + a.2 * a.2))) _
    (Q'.mul_eqv_congr_left (half * half) _ _
      (recoupling_cleared_norm a.1 a.2)) ?_
  refine Q'.eqv_trans _
    (((half * half) * 4) * (3 * (a.1 * a.1) + a.2 * a.2)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (half * half) 4 _)) ?_
  refine Q'.eqv_trans _
    (1 * (3 * (a.1 * a.1) + a.2 * a.2)) _
    (Q'.mul_eqv_congr_right _ _ _ half_square_four) ?_
  refine Q'.eqv_trans _
    (3 * (a.1 * a.1) + a.2 * a.2) _ (Q'.one_mul_eqv _) ?_
  exact Q'.eqv_symm
    (QPoly.q_add_congr (Q'.eqv_refl _) (Q'.one_mul_eqv _))

theorem intertwinerRecoupling_distSq_eqv (a b : Q' × Q') :
    intertwinerGNS.distSqQ
        (intertwinerRecoupling a) (intertwinerRecoupling b) ≈
      intertwinerGNS.distSqQ a b := by
  have hsub := intertwinerRecoupling_map_sub a b
  refine Q'.eqv_trans _
    (intertwinerGNS.B
      (intertwinerRecoupling (intertwinerGNS.sub a b))
      (intertwinerRecoupling (intertwinerGNS.sub a b))) _ ?_ ?_
  · exact Q'.eqv_symm (intertwinerGNS.B_diag_congr hsub)
  · exact intertwinerRecoupling_norm (intertwinerGNS.sub a b)

theorem intertwinerRecoupling_distSq_contraction (a b : Q' × Q') :
    intertwinerGNS.distSqQ
        (intertwinerRecoupling a) (intertwinerRecoupling b) ≤
      intertwinerGNS.distSqQ a b :=
  Q'.le_of_eqv (intertwinerRecoupling_distSq_eqv a b)

/-! ## Descent to the constructive completion -/

def applyRecouplingCauchy
    (x : CauchyGNS intertwinerGNS) : CauchyGNS intertwinerGNS where
  seq := fun n => intertwinerRecoupling (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _
      (intertwinerRecoupling_distSq_contraction (x.seq p) (x.seq q))
      (x.isCauchy epsilon hepsilon p q hp hq)

theorem applyRecouplingCauchy_null {x y : CauchyGNS intertwinerGNS}
    (h : CauchyNull intertwinerGNS x y) :
    CauchyNull intertwinerGNS
      (applyRecouplingCauchy x) (applyRecouplingCauchy y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (intertwinerRecoupling_distSq_contraction (x.seq n) (y.seq n)) (hN n hn)⟩

def completedIntertwinerRecoupling :
    GNSCompletionSpace intertwinerGNS → GNSCompletionSpace intertwinerGNS :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid intertwinerGNS)
      (applyRecouplingCauchy x))
    (fun _ _ h => Quotient.sound (applyRecouplingCauchy_null h))

theorem completedIntertwinerRecoupling_embed (a : Q' × Q') :
    completedIntertwinerRecoupling (embedV intertwinerGNS a) =
      embedV intertwinerGNS (intertwinerRecoupling a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

theorem completedIntertwinerRecoupling_norm
    (x : GNSCompletionSpace intertwinerGNS) :
    intertwinerGNS.cinnerCompl
        (completedIntertwinerRecoupling x) (completedIntertwinerRecoupling x) =
      intertwinerGNS.cinnerCompl x x := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (intertwinerGNS.cInnerSeq
        (applyRecouplingCauchy u) (applyRecouplingCauchy u) n))
    (bSeq := fun n => CReal.ofQ' (intertwinerGNS.cInnerSeq u u n))
    (fun n => PositiveTimeCompression.lifted_eqv
      (intertwinerRecoupling_norm (u.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem completed_pairingA_recouples :
    completedIntertwinerRecoupling
        (embedV intertwinerGNS pairingACoord) =
      embedV intertwinerGNS ((0, 2) : Q' × Q') := by
  refine Eq.trans (completedIntertwinerRecoupling_embed pairingACoord) ?_
  apply Quotient.sound
  have hv : intertwinerGNS.veq
      (intertwinerRecoupling pairingACoord) ((0, 2) : Q' × Q') := by
    change half * (1 + (-1)) ≈ 0 ∧ half * (3 * 1 + 1) ≈ 2
    unfold half
    exact ⟨by decide, by decide⟩
  exact embed_null_of_rad intertwinerGNS
    (rad_of_veq intertwinerGNS hv)

theorem completed_pairingB_recouples :
    completedIntertwinerRecoupling
        (embedV intertwinerGNS pairingBCoord) =
      embedV intertwinerGNS pairingACoord := by
  refine Eq.trans (completedIntertwinerRecoupling_embed pairingBCoord) ?_
  apply Quotient.sound
  have hv : intertwinerGNS.veq
      (intertwinerRecoupling pairingBCoord) pairingACoord := by
    change half * (1 + (-(-1))) ≈ 1 ∧ half * (3 * 1 + (-1)) ≈ 1
    unfold half
    exact ⟨by decide, by decide⟩
  exact embed_null_of_rad intertwinerGNS
    (rad_of_veq intertwinerGNS hv)

end YMGap.Continuum.SU2FourValentRecouplingCompleted

#print axioms YMGap.Continuum.SU2FourValentRecouplingCompleted.recoupling_cleared_norm
#print axioms YMGap.Continuum.SU2FourValentRecouplingCompleted.intertwinerRecoupling_map_sub
#print axioms YMGap.Continuum.SU2FourValentRecouplingCompleted.intertwinerRecoupling_norm
#print axioms YMGap.Continuum.SU2FourValentRecouplingCompleted.intertwinerRecoupling_distSq_eqv
#print axioms YMGap.Continuum.SU2FourValentRecouplingCompleted.completedIntertwinerRecoupling
#print axioms YMGap.Continuum.SU2FourValentRecouplingCompleted.completedIntertwinerRecoupling_norm
#print axioms YMGap.Continuum.SU2FourValentRecouplingCompleted.completed_pairingA_recouples
#print axioms YMGap.Continuum.SU2FourValentRecouplingCompleted.completed_pairingB_recouples
