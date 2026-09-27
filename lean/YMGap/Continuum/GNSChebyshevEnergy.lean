/-
# Coupled Chebyshev energy on the existing completed carrier

For a self-adjoint X use U'=T+XU and T'=XU'-U. The exact invariant
||T||^2+||U||^2-||XU||^2 yields a norm bound whenever X contracts the
auxiliary state. No spectral theorem, scalar extension or finite-dimensional
replacement is used. Accelerated decay for a rescaled original balanced
sweep still requires strict centered control and scalar/cone joins.
-/

import YMGap.Continuum.GNSProjectionSweep
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.GNSChebyshevEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.RingNormaliser

private theorem scalar_step (a b c d e : RC) :
    RCsub (RCadd
      (RCsub (RCsub a (RCadd b c)) (RCsub (RCadd b c) d))
      (RCadd (RCadd e b) (RCadd b c))) a = RCsub (RCadd e d) c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  refine Quotient.inductionOn₂ d e ?_
  intro D E
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add
        (.add (.add (.var 0) (.neg (.add (.var 1) (.var 2))))
          (.neg (.add (.add (.var 1) (.var 2)) (.neg (.var 3)))))
        (.add (.add (.var 4) (.var 1)) (.add (.var 1) (.var 2)))) (.neg (.var 0)))
      (.add (.add (.var 4) (.var 3)) (.neg (.var 2))) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n
           | 3 => D.approx n | _ => E.approx n)))

private theorem scalar_base (a : RC) : RCsub (RCadd a RCzero) RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.const 0)) (.neg (.const 0))) (.var 0)
      (by decide) (fun _ => A.approx n)))

private theorem scalar_bound (a b c : RC) (h : RCle c b) :
    RCle a (RCsub (RCadd a b) c) := by
  have hleft : RCadd (RCsub a c) c = a := by
    refine Quotient.inductionOn₂ a c ?_
    intro A C
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.sub_add_cancel_eqv _ _))
  have hright : RCadd (RCsub a c) b = RCsub (RCadd a b) c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro A B C
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 2))) (.var 1))
        (.add (.add (.var 0) (.var 1)) (.neg (.var 2))) (by decide)
        (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))
  have hs := RCadd_le_add (RCle_refl (RCsub a c)) h
  rwa [hleft, hright] at hs

variable {D : GNSData} (X : GNSCompletionSpace D → GNSCompletionSpace D)

/-- The coupled recurrence uses only addition, subtraction and the SAME X. -/
def step (t u : GNSCompletionSpace D) :
    GNSCompletionSpace D × GNSCompletionSpace D :=
  let v := D.cAdd t (X u)
  (D.cSub (X v) u, v)

def state (x : GNSCompletionSpace D) : Nat →
    GNSCompletionSpace D × GNSCompletionSpace D
  | 0 => (x, embedV D D.zero)
  | n+1 => step X (state x n).1 (state x n).2

def energy (t u : GNSCompletionSpace D) : RC :=
  RCsub (RCadd (normSq t) (normSq u)) (normSq (X u))

variable (hsa : ∀ x y, D.cinnerCompl (X x) y = D.cinnerCompl x (X y))

private theorem norm_add (x y : GNSCompletionSpace D) :
    normSq (D.cAdd x y) =
      RCadd (RCadd (normSq x) (D.cinnerCompl x y))
        (RCadd (D.cinnerCompl x y) (normSq y)) := by
  unfold normSq
  rw [D.cinnerCompl_cAdd_left, D.cinnerCompl_cAdd_right,
    D.cinnerCompl_cAdd_right, D.cinnerCompl_comm y x]

private theorem norm_sub (x y : GNSCompletionSpace D) :
    normSq (D.cSub x y) =
      RCsub (RCsub (normSq x) (D.cinnerCompl x y))
        (RCsub (D.cinnerCompl x y) (normSq y)) := by
  unfold normSq
  rw [D.cinnerCompl_cSub_left, D.cinnerCompl_comm x (D.cSub x y),
    D.cinnerCompl_cSub_left, D.cinnerCompl_comm y (D.cSub x y),
    D.cinnerCompl_cSub_left, D.cinnerCompl_comm y x]

include hsa

/-- Exact cancellation of the signed cross terms. No contraction premise. -/
theorem step_energy (t u : GNSCompletionSpace D) :
    energy X (step X t u).1 (step X t u).2 = energy X t u := by
  dsimp only [step, energy]
  rw [norm_sub, hsa, D.cinnerCompl_cAdd_left, norm_add]
  exact scalar_step _ _ _ _ _

/-- The coupled energy equals the original squared norm at EVERY order. -/
theorem state_energy (x : GNSCompletionSpace D) (n : Nat) :
    energy X (state X x n).1 (state X x n).2 = normSq x := by
  induction n with
  | zero =>
    have hz : normSq (embedV D D.zero) = RCzero := D.cinnerCompl_embedZero_left _
    have hxz : normSq (X (embedV D D.zero)) = RCzero := by
      unfold normSq
      rw [hsa, D.cinnerCompl_embedZero_left]
    change RCsub (RCadd (normSq x) (normSq (embedV D D.zero)))
      (normSq (X (embedV D D.zero))) = normSq x
    rw [hz, hxz, scalar_base]
  | succ n ih => exact (step_energy X hsa _ _).trans ih

/-- Only contraction of this auxiliary state is needed for the norm bound. -/
theorem state_norm_le (x : GNSCompletionSpace D) (n : Nat)
    (hc : RCle (normSq (X (state X x n).2)) (normSq (state X x n).2)) :
    RCle (normSq (state X x n).1) (normSq x) := by
  have h := scalar_bound (normSq (state X x n).1) (normSq (state X x n).2)
    (normSq (X (state X x n).2)) hc
  change RCle _ (energy X (state X x n).1 (state X x n).2) at h
  rwa [state_energy X hsa] at h

omit hsa in
/-- The two actual states stay in any supplied invariant additive sector. -/
theorem state_mem (E : GNSCompletionSpace D → Prop)
    (hzero : E (embedV D D.zero))
    (hadd : ∀ a b, E a → E b → E (D.cAdd a b))
    (hsub : ∀ a b, E a → E b → E (D.cSub a b))
    (hop : ∀ a, E a → E (X a)) (x : GNSCompletionSpace D) (hx : E x)
    (n : Nat) : E (state X x n).1 ∧ E (state X x n).2 := by
  induction n with
  | zero => exact ⟨hx, hzero⟩
  | succ n ih =>
    have hv := hadd _ _ ih.1 (hop _ ih.2)
    exact ⟨hsub _ _ (hop _ hv) ih.2, hv⟩

/-- Sector-only contraction suffices; no bound on the vacuum is required. -/
theorem state_norm_le_on (E : GNSCompletionSpace D → Prop)
    (hzero : E (embedV D D.zero))
    (hadd : ∀ a b, E a → E b → E (D.cAdd a b))
    (hsub : ∀ a b, E a → E b → E (D.cSub a b))
    (hop : ∀ a, E a → E (X a))
    (hc : ∀ a, E a → RCle (normSq (X a)) (normSq a))
    (x : GNSCompletionSpace D) (hx : E x) (n : Nat) :
    RCle (normSq (state X x n).1) (normSq x) :=
  state_norm_le X hsa x n
    (hc _ (state_mem X E hzero hadd hsub hop x hx n).2)

#print axioms state
#print axioms step_energy
#print axioms state_energy
#print axioms state_norm_le
#print axioms state_mem
#print axioms state_norm_le_on

end YMGap.Continuum.GNSChebyshevEnergy
