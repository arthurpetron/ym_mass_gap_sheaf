/-
# Dyadic time for the SAME original all-nome Wilson transfer

Iterate the constructed compatible roots on a supplied dyadic mesh. Their
square law gives exact refinement, so equivalent mesh presentations descend
to the existing nonnegative dyadic-time quotient. One time unit is exactly
the ORIGINAL T(1), not a two-step or other-carrier replacement.

The action is positive, symmetric, linear and contractive on the original
completion. No continuity at zero, real-time extension, generator identity,
physical time calibration or continuum conclusion is asserted. In particular,
the original boundary kernel has not been discarded.
-/

import YMGap.Constructive.NonnegativeDyadicTime
import YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "R" => root hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Supplied mesh depth and step count compute a finite iteration of actual roots. -/
def meshAction (depth : Nat) : Nat → V → V
  | 0,x => x
  | n+1,x => R depth (meshAction depth n x)

theorem mesh_add (depth m n : Nat) (x : V) :
    meshAction hw0 hw1 depth (m+n) x =
      meshAction hw0 hw1 depth m (meshAction hw0 hw1 depth n x) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.succ_add,meshAction,meshAction,ih]

private theorem mesh_commutes_root (depth n : Nat) (x : V) :
    meshAction hw0 hw1 depth n (R depth x) = R depth (meshAction hw0 hw1 depth n x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (R depth) ih

theorem mesh_symmetric (depth n : Nat) (x y : V) :
    B (meshAction hw0 hw1 depth n x) y = B x (meshAction hw0 hw1 depth n y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      change B (R depth (meshAction hw0 hw1 depth n x)) y =
        B x (R depth (meshAction hw0 hw1 depth n y))
      rw [root_symmetric,ih,mesh_commutes_root]

theorem mesh_norm_bound (depth n : Nat) (x : V) :
    RCle (B (meshAction hw0 hw1 depth n x) (meshAction hw0 hw1 depth n x)) (B x x) := by
  induction n with
  | zero => exact RCle_refl _
  | succ n ih => exact RCle_trans (root_norm_bound hw0 hw1 depth _) ih

/-- Two finer steps equal one coarser step on every original completed state. -/
theorem mesh_double (depth n : Nat) (x : V) :
    meshAction hw0 hw1 (depth+1) (n+n) x = meshAction hw0 hw1 depth n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show (n+1)+(n+1)=((n+n)+1)+1 by omega,
        meshAction,meshAction,root_square,ih]
      rfl

theorem mesh_refinement (depth extra n : Nat) (x : V) :
    meshAction hw0 hw1 (depth+extra) (n*2^extra) x = meshAction hw0 hw1 depth n x := by
  induction extra with
  | zero => rw [Nat.add_zero,Nat.pow_zero,Nat.mul_one]
  | succ extra ih =>
      rw [Nat.pow_succ,← Nat.mul_assoc,Nat.mul_two]
      change meshAction hw0 hw1 ((depth+extra)+1) (n*2^extra+n*2^extra) x = _
      rw [mesh_double,ih]

theorem mesh_nonnegative (depth n : Nat) (x : V) :
    RCnonneg (B (meshAction hw0 hw1 depth n x) x) := by
  rw [← mesh_double hw0 hw1 depth n x,mesh_add,mesh_symmetric]
  exact completedInner_nonnegative hw0 hw1 _

theorem mesh_original (n : Nat) (x : V) : meshAction hw0 hw1 0 n x = T n x := by
  induction n with
  | zero => exact (completedTime_zero hw0 hw1 x).symm
  | succ n ih =>
      rw [meshAction,root_zero_depth,ih,← completedTime_add,Nat.add_comm 1 n]

/-- Compare equal dyadic times at the sum of their supplied mesh depths. -/
theorem mesh_congr {p q : MeshPoint} (h : Equivalent p q) (x : V) :
    meshAction hw0 hw1 p.depth p.steps x = meshAction hw0 hw1 q.depth q.steps x := by
  calc
    meshAction hw0 hw1 p.depth p.steps x =
        meshAction hw0 hw1 (p.depth+q.depth) (p.steps*2^q.depth) x :=
      (mesh_refinement hw0 hw1 p.depth q.depth p.steps x).symm
    _ = meshAction hw0 hw1 (q.depth+p.depth) (q.steps*2^p.depth) x := by
      rw [h,Nat.add_comm p.depth q.depth]
    _ = meshAction hw0 hw1 q.depth q.steps x :=
      mesh_refinement hw0 hw1 q.depth p.depth q.steps x

/-- Representation-independent dyadic time on the SAME original completion. -/
def action (t : Time) (x : V) : V :=
  Quotient.lift (fun p => meshAction hw0 hw1 p.depth p.steps x)
    (fun _ _ h => mesh_congr hw0 hw1 h x) t

theorem action_embed (p : MeshPoint) (x : V) :
    action hw0 hw1 (embed p) x = meshAction hw0 hw1 p.depth p.steps x := rfl

theorem action_add (s t : Time) (x : V) :
    action hw0 hw1 (add s t) x = action hw0 hw1 s (action hw0 hw1 t x) := by
  refine Quotient.inductionOn₂ s t ?_
  intro p q
  change meshAction hw0 hw1 (p.depth+q.depth) (p.steps*2^q.depth+q.steps*2^p.depth) x =
    meshAction hw0 hw1 p.depth p.steps (meshAction hw0 hw1 q.depth q.steps x)
  rw [mesh_add,mesh_refinement]
  have h := mesh_refinement hw0 hw1 q.depth p.depth q.steps x
  rw [Nat.add_comm q.depth p.depth] at h
  rw [h]

theorem action_zero (x : V) : action hw0 hw1 zero x = x := rfl

/-- Integer time agrees with the ORIGINAL geometric-time semigroup, including T(1). -/
theorem action_whole (n : Nat) (x : V) : action hw0 hw1 (whole n) x = T n x :=
  mesh_original hw0 hw1 n x

theorem action_root (depth : Nat) (x : V) : action hw0 hw1 (embed ⟨depth,1⟩) x = R depth x := rfl

theorem action_symmetric (t : Time) (x y : V) :
    B (action hw0 hw1 t x) y = B x (action hw0 hw1 t y) := by
  refine Quotient.inductionOn t ?_
  intro p
  exact mesh_symmetric hw0 hw1 p.depth p.steps x y

theorem action_nonnegative (t : Time) (x : V) : RCnonneg (B (action hw0 hw1 t x) x) := by
  refine Quotient.inductionOn t ?_
  intro p
  exact mesh_nonnegative hw0 hw1 p.depth p.steps x

theorem action_norm_bound (t : Time) (x : V) :
    RCle (B (action hw0 hw1 t x) (action hw0 hw1 t x)) (B x x) := by
  refine Quotient.inductionOn t ?_
  intro p
  exact mesh_norm_bound hw0 hw1 p.depth p.steps x

theorem action_add_state (t : Time) (x y : V) :
    action hw0 hw1 t (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (action hw0 hw1 t x) (action hw0 hw1 t y) := by
  refine Quotient.inductionOn t ?_
  intro p
  change meshAction hw0 hw1 p.depth p.steps (completedAdd hw0 hw1 x y) =
    completedAdd hw0 hw1 (meshAction hw0 hw1 p.depth p.steps x) (meshAction hw0 hw1 p.depth p.steps y)
  induction p.steps with
  | zero => rfl
  | succ n ih => rw [meshAction,ih,root_add]; rfl

theorem action_smul (t : Time) (c : Q') (x : V) :
    action hw0 hw1 t (completedSmul hw0 hw1 c x) = completedSmul hw0 hw1 c (action hw0 hw1 t x) := by
  refine Quotient.inductionOn t ?_
  intro p
  change meshAction hw0 hw1 p.depth p.steps (completedSmul hw0 hw1 c x) =
    completedSmul hw0 hw1 c (meshAction hw0 hw1 p.depth p.steps x)
  induction p.steps with
  | zero => rfl
  | succ n ih => rw [meshAction,ih,root_smul]; rfl

theorem action_realSmul (t : Time) (s : CReal) (cs : QCauchy s.approx) (x : V) :
    action hw0 hw1 t (completedRealSmul hw0 hw1 s cs x) =
      completedRealSmul hw0 hw1 s cs (action hw0 hw1 t x) := by
  refine Quotient.inductionOn t ?_
  intro p
  change meshAction hw0 hw1 p.depth p.steps (completedRealSmul hw0 hw1 s cs x) =
    completedRealSmul hw0 hw1 s cs (meshAction hw0 hw1 p.depth p.steps x)
  induction p.steps with
  | zero => rfl
  | succ n ih => rw [meshAction,ih,root_realSmul]; rfl

theorem action_sub (t : Time) (x y : V) :
    action hw0 hw1 t (completedSub hw0 hw1 x y) =
      completedSub hw0 hw1 (action hw0 hw1 t x) (action hw0 hw1 t y) := by
  refine Quotient.inductionOn t ?_
  intro p
  change meshAction hw0 hw1 p.depth p.steps (completedSub hw0 hw1 x y) =
    completedSub hw0 hw1 (meshAction hw0 hw1 p.depth p.steps x) (meshAction hw0 hw1 p.depth p.steps y)
  induction p.steps with
  | zero => rfl
  | succ n ih => rw [meshAction,ih,root_sub]; rfl

theorem action_distance_bound (t : Time) (x y : V) :
    RCle (completedDist hw0 hw1 (action hw0 hw1 t x) (action hw0 hw1 t y))
      (completedDist hw0 hw1 x y) := by
  unfold completedDist
  rw [← action_sub]
  exact action_norm_bound hw0 hw1 t (completedSub hw0 hw1 x y)

theorem action_doubled_pairing (t : Time) (x y : V) :
    B (action hw0 hw1 (add t t) x) y = B (action hw0 hw1 t x) (action hw0 hw1 t y) := by
  rw [action_add,action_symmetric]

#print axioms meshAction
#print axioms mesh_refinement
#print axioms action
#print axioms action_add
#print axioms action_zero
#print axioms action_whole
#print axioms action_root
#print axioms action_symmetric
#print axioms action_nonnegative
#print axioms action_norm_bound
#print axioms action_add_state
#print axioms action_smul
#print axioms action_realSmul
#print axioms action_sub
#print axioms action_distance_bound
#print axioms action_doubled_pairing

end YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
