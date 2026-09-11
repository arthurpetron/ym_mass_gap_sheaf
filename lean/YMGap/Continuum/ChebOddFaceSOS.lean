/-
# Odd Chebyshev half-angle sum of squares over `Q'`

This file isolates the polynomial identity behind the odd character channel.
For

    C₀(x) = 1,
    Cₖ₊₁(x) = Uₖ₊₁(x) - Uₖ(x),

we prove, constructively and at every order,

    1 + T₂ₖ₊₁(x) ≃ (1 + x) Cₖ(x)².

The proof is entirely internal to the rational Chebyshev algebra.  Its two
structural ingredients are the adjacent-`U` determinant invariant

    Uₖ₊₁² + Uₖ² - 2x Uₖ₊₁Uₖ = 1

and the already-proved fusion rule, whose top-term difference gives

    U₂ₖ₊₃ = Uₖ₊₁Uₖ₊₂ - UₖUₖ₊₁.

Together with `2Tₙ = Uₙ-Uₙ₋₂`, these turn the odd half-angle identity into a
finite commutative-ring calculation.  We also sum the identity and telescope
the odd first-kind modes, obtaining

    (2m+2) + U₂ₘ₊₁(x)
      ≃ 2 * sum (k <= m), (1+x) Cₖ(x)².

# Axiom gate

No `Classical`, no choice, no `sorry`/`admit`, no custom axiom, and no
`native_decide`.  The only finite objects are structurally recursive `Nat`
sums.
-/

import YMGap.Continuum.ChebOrthoMatrix
import YMGap.Constructive.ExpAddConv
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ChebOddFaceSOS

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebOrthoMatrix
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The odd half-angle feature -/

/-- The odd half-angle Chebyshev feature.  The base case implements the
constructive convention `U_{-1}=0`, hence `C₀=U₀-U_{-1}=1`. -/
def C : Nat → Q' → Q'
  | 0, _ => 1
  | k + 1, x => U (k + 1) x + (-(U k x))

@[simp] theorem C_zero (x : Q') : C 0 x = 1 := rfl

@[simp] theorem C_succ (k : Nat) (x : Q') :
    C (k + 1) x = U (k + 1) x + (-(U k x)) := rfl

/-! ## 1b. Reflected polynomial kernels

The following identities genuinely need distributivity and cancellation.  We
route them through the repository's proved reflective ring normaliser instead
of expanding the raw numerator/denominator representation of `Q'`. -/

private def psub (a b : PolyExpr) : PolyExpr := .add a (.neg b)
private def psq (a : PolyExpr) : PolyExpr := .mul a a

private def detSeedLHS : PolyExpr :=
  let d : PolyExpr := .var 0
  .add (.add (psq d) (psq (.const 1)))
    (.neg (.mul (.mul d d) (.const 1)))

private def detSeedRHS : PolyExpr := .const 1

private theorem detSeed_normal :
    normalize detSeedLHS = normalize detSeedRHS := by decide

private theorem det_seed_ring (d : Q') :
    ((d * d + (1 : Q') * (1 : Q')) + (-((d * d) * (1 : Q')))) ≈
      (1 : Q') := by
  have h := poly_identity_of_normal_eq detSeedLHS detSeedRHS detSeed_normal
    (fun _ => d)
  simpa [eval, detSeedLHS, detSeedRHS, psq, RingNormaliser.qpow] using h

private def detStepLHS : PolyExpr :=
  let d : PolyExpr := .var 0
  let A : PolyExpr := .var 1
  let B : PolyExpr := .var 2
  let C : PolyExpr := psub (.mul d A) B
  .add (.add (psq C) (psq A)) (.neg (.mul (.mul d C) A))

private def detStepRHS : PolyExpr :=
  let d : PolyExpr := .var 0
  let A : PolyExpr := .var 1
  let B : PolyExpr := .var 2
  .add (.add (psq A) (psq B)) (.neg (.mul (.mul d A) B))

private theorem detStep_normal :
    normalize detStepLHS = normalize detStepRHS := by decide

private theorem det_step_ring (d A B : Q') :
    ((((d * A + (-B)) * (d * A + (-B))) + A * A)
        + (-((d * (d * A + (-B))) * A))) ≈
      ((A * A + B * B) + (-((d * A) * B))) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then d else if r = 1 then A else B
  have h := poly_identity_of_normal_eq detStepLHS detStepRHS detStep_normal ρ
  simpa [eval, detStepLHS, detStepRHS, psub, psq, RingNormaliser.qpow, ρ] using h

private def oddDiffLHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let A : PolyExpr := .var 1
  let B : PolyExpr := .var 2
  let dx : PolyExpr := .mul (.const 2) x
  let E : PolyExpr := psub (.mul dx A) B
  let D : PolyExpr := psub (.mul dx B) A
  psub (psub (.mul A E) (.mul B A))
    (psub (.mul B A) (.mul D B))

private def oddDiffRHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let A : PolyExpr := .var 1
  let B : PolyExpr := .var 2
  .mul (.const 2)
    (psub (.mul x (.add (psq A) (psq B)))
      (.mul (.const 2) (.mul A B)))

private theorem oddDiff_normal :
    normalize oddDiffLHS = normalize oddDiffRHS := by decide

private theorem odd_difference_ring (x A B : Q') :
    ((A * (((2 : Q') * x) * A + (-B)) + (-(B * A)))
        + (-(B * A + (-((((2 : Q') * x) * B + (-A)) * B))))) ≈
      (2 : Q') *
        (x * (A * A + B * B) + (-((2 : Q') * (A * B)))) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then x else if r = 1 then A else B
  have h := poly_identity_of_normal_eq oddDiffLHS oddDiffRHS oddDiff_normal ρ
  simpa [eval, oddDiffLHS, oddDiffRHS, psub, psq, RingNormaliser.qpow, ρ] using h

private def oddOneLHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let dx : PolyExpr := .mul (.const 2) x
  .add (.const 1) (psub (.mul dx (psub (.mul dx x) (.const 1))) x)

private def oddOneRHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let C1 : PolyExpr := psub (.mul (.const 2) x) (.const 1)
  .mul (.add (.const 1) x) (psq C1)

private theorem oddOne_normal :
    normalize oddOneLHS = normalize oddOneRHS := by decide

private theorem odd_one_ring (x : Q') :
    (1 : Q') +
        (((2 : Q') * x) * (((2 : Q') * x) * x + (-(1 : Q'))) + (-x)) ≈
      ((1 : Q') + x) *
        ((((2 : Q') * x + (-(1 : Q'))) *
          ((2 : Q') * x + (-(1 : Q'))))) := by
  have h := poly_identity_of_normal_eq oddOneLHS oddOneRHS oddOne_normal
    (fun _ => x)
  simpa [eval, oddOneLHS, oddOneRHS, psub, psq, RingNormaliser.qpow] using h

private def halfCoreLHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let A : PolyExpr := .var 1
  let B : PolyExpr := .var 2
  let squares : PolyExpr := .add (psq A) (psq B)
  let invariant : PolyExpr :=
    psub squares (.mul (.mul (.mul (.const 2) x) A) B)
  let oddPart : PolyExpr :=
    psub (.mul x squares) (.mul (.const 2) (.mul A B))
  .add invariant oddPart

private def halfCoreRHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let A : PolyExpr := .var 1
  let B : PolyExpr := .var 2
  .mul (.add (.const 1) x) (psq (psub A B))

private theorem halfCore_normal :
    normalize halfCoreLHS = normalize halfCoreRHS := by decide

private theorem half_core_ring (x A B : Q') :
    (((A * A + B * B) + (-((((2 : Q') * x) * A) * B)))
        + (x * (A * A + B * B) + (-((2 : Q') * (A * B))))) ≈
      ((1 : Q') + x) * ((A + (-B)) * (A + (-B))) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then x else if r = 1 then A else B
  have h := poly_identity_of_normal_eq halfCoreLHS halfCoreRHS halfCore_normal ρ
  simpa [eval, halfCoreLHS, halfCoreRHS, psub, psq, RingNormaliser.qpow, ρ] using h

/-! Small additive cancellations used outside the reflected polynomial core. -/

private theorem add_add_neg_left (a b : Q') : (a + b) + (-a) ≈ b := by
  calc
    (a + b) + (-a) ≈ a + (b + (-a)) := Q'.add_assoc_eqv _ _ _
    _ ≈ a + ((-a) + b) :=
      Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
    _ ≈ (a + (-a)) + b := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    _ ≈ (0 : Q') + b :=
      Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv a)
    _ ≈ b := by rw [Q'.zero_add']; exact Q'.eqv_refl _

private theorem add_middle_neg_left (a b : Q') : a + (b + (-a)) ≈ b := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv a b (-a))) (add_add_neg_left a b)

private theorem add_neg_sub_self (a b : Q') : a + (-(a + (-b))) ≈ b := by
  calc
    a + (-(a + (-b))) ≈ a + ((-a) + (-(-b))) :=
      Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_eqv a (-b))
    _ ≈ a + ((-a) + b) :=
      Q'.add_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv b))
    _ ≈ (a + (-a)) + b := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    _ ≈ (0 : Q') + b :=
      Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv a)
    _ ≈ b := by rw [Q'.zero_add']; exact Q'.eqv_refl _

/-! ## 2. Two elementary all-order Chebyshev identities -/

/-- `2 T_{k+2} = U_{k+2}-U_k`, obtained by rearranging the proved bounded
recurrence `U_{k+2}=U_k+2T_{k+2}`. -/
theorem two_mul_T_as_Udiff (k : Nat) (x : Q') :
    (2 : Q') * T (k + 2) x ≈ U (k + 2) x + (-(U k x)) := by
  have h := ChebU.Ushift k x
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_comm_eqv (U k x) ((2 : Q') * T (k + 2) x))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (U k x))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- The adjacent-`U` determinant invariant
`U_{n+1}^2+U_n^2-(2x)U_{n+1}U_n = 1`.  It is proved directly from the
second-kind recurrence; no trigonometric or root representation is used. -/
theorem adjacentU_determinant (n : Nat) (x : Q') :
    ((U (n + 1) x * U (n + 1) x + U n x * U n x)
      + (-((((2 : Q') * x) * U (n + 1) x) * U n x))) ≈ (1 : Q') := by
  induction n with
  | zero =>
      rw [U_one, U_zero]
      exact det_seed_ring ((2 : Q') * x)
  | succ k ih =>
      rw [U_succ_succ k x]
      refine Q'.eqv_trans _
        ((U (k + 1) x * U (k + 1) x + U k x * U k x)
          + (-((((2 : Q') * x) * U (k + 1) x) * U k x))) _ ?_ ih
      exact det_step_ring ((2 : Q') * x) (U (k + 1) x) (U k x)

/-! ## 3. The top boundary of the `U`-fusion sum -/

/-- The top-term difference of two adjacent fusion rows:
`U_{2n+3}=U_{n+1}U_{n+2}-U_nU_{n+1}`. -/
theorem oddU_boundary (n : Nat) (x : Q') :
    U (2 * n + 3) x ≈
      U (n + 1) x * U (n + 2) x + (-(U n x * U (n + 1) x)) := by
  have htop0 := fusion_ge x (n + 1) (n + 2) (by omega)
  have htop : U (n + 1) x * U (n + 2) x ≈ FS 1 (n + 1) x := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
    simpa only [show n + 2 - (n + 1) = 1 by omega] using htop0
  have hbot0 := fusion_ge x n (n + 1) (by omega)
  have hbot : U n x * U (n + 1) x ≈ FS 1 n x := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
    simpa only [show n + 1 - n = 1 by omega] using hbot0
  have hFS : FS 1 (n + 1) x = FS 1 n x + U (2 * n + 3) x := by
    unfold FS
    change
      finSum (fun r => U (1 + 2 * r) x) (n + 1) + U (1 + 2 * (n + 1)) x =
        finSum (fun r => U (1 + 2 * r) x) (n + 1) + U (2 * n + 3) x
    congr 2
    omega
  refine Q'.eqv_symm ?_
  calc
    U (n + 1) x * U (n + 2) x + (-(U n x * U (n + 1) x))
        ≈ FS 1 (n + 1) x + (-(FS 1 n x)) :=
          Cheb.add_eqv_congr _ _ _ _ htop (Q'.neg_eqv_congr _ _ hbot)
    _ ≈ (FS 1 n x + U (2 * n + 3) x) + (-(FS 1 n x)) := by
          exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_of_eq hFS)
    _ ≈ U (2 * n + 3) x := add_add_neg_left _ _

/-- Backward form of the `U` recurrence:
`U_n=(2x)U_{n+1}-U_{n+2}`. -/
theorem U_backwards (n : Nat) (x : Q') :
    U n x ≈ ((2 : Q') * x) * U (n + 1) x + (-(U (n + 2) x)) := by
  refine Q'.eqv_symm ?_
  calc
    ((2 : Q') * x) * U (n + 1) x + (-(U (n + 2) x))
        ≈ ((2 : Q') * x) * U (n + 1) x
            + (-(((2 : Q') * x) * U (n + 1) x + (-(U n x)))) := by
          exact Q'.add_eqv_congr_left _ _ _
            (Q'.neg_eqv_congr _ _ (Q'.eqv_of_eq (U_succ_succ n x)))
    _ ≈ U n x := add_neg_sub_self _ _

/-- The abstract ring calculation converting two adjacent odd fusion
boundaries to the quadratic expression used by the half-angle square. -/
private theorem odd_difference_atoms (x A B D E : Q')
    (hE : E ≈ ((2 : Q') * x) * A + (-B))
    (hD : D ≈ ((2 : Q') * x) * B + (-A)) :
    ((A * E + (-(B * A))) + (-(B * A + (-(D * B))))) ≈
      (2 : Q') *
        (x * (A * A + B * B) + (-((2 : Q') * (A * B)))) := by
  have htop : A * E + (-(B * A)) ≈
      A * (((2 : Q') * x) * A + (-B)) + (-(B * A)) :=
    Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left A _ _ hE)
  have hbot : B * A + (-(D * B)) ≈
      B * A + (-((((2 : Q') * x) * B + (-A)) * B)) :=
    Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ B hD))
  refine Q'.eqv_trans _
    ((A * (((2 : Q') * x) * A + (-B)) + (-(B * A)))
      + (-(B * A + (-((((2 : Q') * x) * B + (-A)) * B))))) _ ?_ ?_
  · exact Cheb.add_eqv_congr _ _ _ _ htop (Q'.neg_eqv_congr _ _ hbot)
  · exact odd_difference_ring x A B

/-! ## 4. Pointwise odd half-angle SOS -/

/-- **Odd Chebyshev half-angle square.**  For every `k` and rational `x`,
`1+T_{2k+1}(x) = (1+x)(U_k(x)-U_{k-1}(x))^2`, with `C_0=1`. -/
theorem one_add_T_odd_eq_sos (k : Nat) (x : Q') :
    (1 : Q') + T (2 * k + 1) x ≈
      ((1 : Q') + x) * (C k x * C k x) := by
  rcases k with _ | k
  · rw [C_zero, T_one]
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ (((1 : Q') + x) * (1 : Q')) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv (1 : Q'))
    · exact Q'.mul_one_eqv ((1 : Q') + x)
  · rcases k with _ | n
    · rw [C_succ, U_one, U_zero]
      rw [show 2 * (0 + 1) + 1 = 3 by omega]
      rw [T_succ_succ 1 x, T_succ_succ 0 x, T_one, T_zero]
      exact odd_one_ring x
    · let A : Q' := U (n + 2) x
      let B : Q' := U (n + 1) x
      let D : Q' := U n x
      let E : Q' := U (n + 3) x
      have hE : E ≈ ((2 : Q') * x) * A + (-B) := by
        dsimp only [E, A, B]
        exact Q'.eqv_of_eq (U_succ_succ (n + 1) x)
      have hD : D ≈ ((2 : Q') * x) * B + (-A) := by
        dsimp only [D, B, A]
        exact U_backwards n x
      have hInv :
          ((A * A + B * B) + (-((((2 : Q') * x) * A) * B))) ≈ (1 : Q') := by
        dsimp only [A, B]
        exact adjacentU_determinant (n + 1) x
      have htop : U (2 * (n + 2) + 1) x ≈
          A * E + (-(B * A)) := by
        dsimp only [A, B, E]
        have hidx0 : 2 * (n + 1) + 3 = 2 * (n + 2) + 1 := by omega
        have hidx1 : n + 1 + 1 = n + 2 := by omega
        have hidx2 : n + 1 + 2 = n + 3 := by omega
        simpa only [hidx0, hidx1, hidx2] using oddU_boundary (n + 1) x
      have hbot : U (2 * n + 3) x ≈
          B * A + (-(D * B)) := by
        dsimp only [A, B, D]
        exact oddU_boundary n x
      have hTwoT :
          (2 : Q') * T (2 * (n + 2) + 1) x ≈
            U (2 * (n + 2) + 1) x + (-(U (2 * n + 3) x)) := by
        have hidx : 2 * n + 3 + 2 = 2 * (n + 2) + 1 := by omega
        simpa only [hidx] using two_mul_T_as_Udiff (2 * n + 3) x
      have hOdd :
          (2 : Q') * T (2 * (n + 2) + 1) x ≈
            (2 : Q') *
              (x * (A * A + B * B) + (-((2 : Q') * (A * B)))) := by
        refine Q'.eqv_trans _ _ _ hTwoT ?_
        refine Q'.eqv_trans _
          ((A * E + (-(B * A))) + (-(B * A + (-(D * B))))) _ ?_ ?_
        · exact Cheb.add_eqv_congr _ _ _ _ htop (Q'.neg_eqv_congr _ _ hbot)
        · exact odd_difference_atoms x A B D E hE hD
      have hCore :
          (1 : Q') +
              (x * (A * A + B * B) + (-((2 : Q') * (A * B)))) ≈
            ((1 : Q') + x) * ((A + (-B)) * (A + (-B))) := by
        refine Q'.eqv_trans _
          (((A * A + B * B) + (-((((2 : Q') * x) * A) * B)))
            + (x * (A * A + B * B) + (-((2 : Q') * (A * B))))) _ ?_ ?_
        · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hInv)
        · exact half_core_ring x A B
      have hDouble :
          (2 : Q') * ((1 : Q') + T (2 * (n + 2) + 1) x) ≈
            (2 : Q') *
              (((1 : Q') + x) * ((A + (-B)) * (A + (-B)))) := by
        calc
          (2 : Q') * ((1 : Q') + T (2 * (n + 2) + 1) x)
              ≈ (2 : Q') + (2 : Q') * T (2 * (n + 2) + 1) x := by
                refine Q'.eqv_trans _
                  ((2 : Q') * (1 : Q') +
                    (2 : Q') * T (2 * (n + 2) + 1) x) _
                  (Q'.mul_add_eqv _ _ _) ?_
                exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv (2 : Q'))
          _ ≈ (2 : Q') +
                (2 : Q') *
                  (x * (A * A + B * B) + (-((2 : Q') * (A * B)))) :=
              Q'.add_eqv_congr_left _ _ _ hOdd
          _ ≈ (2 : Q') *
                ((1 : Q') +
                  (x * (A * A + B * B) + (-((2 : Q') * (A * B))))) := by
              refine Q'.eqv_trans _
                ((2 : Q') * (1 : Q') +
                  (2 : Q') *
                    (x * (A * A + B * B) + (-((2 : Q') * (A * B))))) _ ?_ ?_
              · exact Q'.add_eqv_congr_right _ _ _
                  (Q'.eqv_symm (Q'.mul_one_eqv (2 : Q')))
              · exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
          _ ≈ (2 : Q') *
                (((1 : Q') + x) * ((A + (-B)) * (A + (-B)))) :=
              Q'.mul_eqv_congr_left _ _ _ hCore
      have hcancel := Q'.mul_left_cancel_of_pos
        (by decide : (0 : Q') < (2 : Q')) hDouble
      dsimp only [A, B] at hcancel
      simpa only [C_succ] using hcancel

/-! ## 5. Summed odd SOS and the `U_{2m+1}` telescope -/

/-- The sum of the odd first-kind modes through `2m+1`. -/
def oddTSum (m : Nat) (x : Q') : Q' :=
  finSum (fun k => T (2 * k + 1) x) (m + 1)

/-- Twice the odd first-kind sum telescopes to one second-kind mode:
`2 sum_{k<=m} T_{2k+1}=U_{2m+1}`. -/
theorem two_mul_oddTSum (m : Nat) (x : Q') :
    (2 : Q') * oddTSum m x ≈ U (2 * m + 1) x := by
  induction m with
  | zero =>
      unfold oddTSum
      rw [finSum_succ, finSum_zero, T_one, U_one]
      rw [Q'.zero_add']
      exact Q'.eqv_refl _
  | succ n ih =>
      have hnew : (2 : Q') * T (2 * n + 3) x ≈
          U (2 * n + 3) x + (-(U (2 * n + 1) x)) := by
        have hidx : 2 * n + 1 + 2 = 2 * n + 3 := by omega
        simpa only [hidx] using two_mul_T_as_Udiff (2 * n + 1) x
      unfold oddTSum at ih ⊢
      rw [finSum_succ]
      refine Q'.eqv_trans _
        ((2 : Q') * finSum (fun k => T (2 * k + 1) x) (n + 1)
          + (2 : Q') * T (2 * n + 3) x) _ ?_ ?_
      · exact Q'.mul_add_eqv _ _ _
      · refine Q'.eqv_trans _
          (U (2 * n + 1) x +
            (U (2 * n + 3) x + (-(U (2 * n + 1) x)))) _ ?_ ?_
        · exact Cheb.add_eqv_congr _ _ _ _ ih hnew
        · exact add_middle_neg_left _ _

/-- The finite odd SOS through level `m`. -/
def oddSOSSum (m : Nat) (x : Q') : Q' :=
  finSum (fun k => ((1 : Q') + x) * (C k x * C k x)) (m + 1)

private theorem finSum_one_eqv_ofNat : ∀ n : Nat,
    finSum (fun _ => (1 : Q')) n ≈ Q'.ofNat n
  | 0 => by decide
  | n + 1 => by
      refine Q'.eqv_trans _ (Q'.ofNat n + (1 : Q')) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ (finSum_one_eqv_ofNat n)
      · exact Q'.eqv_symm (Q'.ofNat_add_eqv n 1)

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a * b)).den : Int) = 1 := rfl
  show ((a * b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
      = (((a : Nat) : Int) * ((b : Nat) : Int)) *
        ((Q'.ofNat (a * b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

/-- **Summed odd Chebyshev SOS.**  The pointwise half-angle squares sum to
`(2m+2)+U_{2m+1}` after the odd-`T` telescope. -/
theorem odd_sos_sum (m : Nat) (x : Q') :
    Q'.ofNat (2 * m + 2) + U (2 * m + 1) x ≈
      (2 : Q') * oddSOSSum m x := by
  have hsos : oddSOSSum m x ≈
      finSum (fun k => (1 : Q') + T (2 * k + 1) x) (m + 1) := by
    unfold oddSOSSum
    exact finSum_eqv_congr _ _
      (fun k => Q'.eqv_symm (one_add_T_odd_eq_sos k x)) (m + 1)
  have hsplit :
      finSum (fun k => (1 : Q') + T (2 * k + 1) x) (m + 1) ≈
        finSum (fun _ => (1 : Q')) (m + 1) + oddTSum m x := by
    unfold oddTSum
    exact finSum_add (fun _ => (1 : Q')) (fun k => T (2 * k + 1) x) (m + 1)
  have hNat : (2 : Q') * Q'.ofNat (m + 1) ≈ Q'.ofNat (2 * m + 2) := by
    have h := Q'.eqv_symm (ofNat_mul_eqv 2 (m + 1))
    have hidx : 2 * (m + 1) = 2 * m + 2 := by omega
    simpa only [hidx] using h
  refine Q'.eqv_symm ?_
  calc
    (2 : Q') * oddSOSSum m x
        ≈ (2 : Q') *
            finSum (fun k => (1 : Q') + T (2 * k + 1) x) (m + 1) :=
          Q'.mul_eqv_congr_left _ _ _ hsos
    _ ≈ (2 : Q') *
          (finSum (fun _ => (1 : Q')) (m + 1) + oddTSum m x) :=
        Q'.mul_eqv_congr_left _ _ _ hsplit
    _ ≈ (2 : Q') * (Q'.ofNat (m + 1) + oddTSum m x) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_right _ _ _ (finSum_one_eqv_ofNat (m + 1)))
    _ ≈ (2 : Q') * Q'.ofNat (m + 1) + (2 : Q') * oddTSum m x := by
        exact Q'.mul_add_eqv _ _ _
    _ ≈ Q'.ofNat (2 * m + 2) + U (2 * m + 1) x :=
        Cheb.add_eqv_congr _ _ _ _ hNat (two_mul_oddTSum m x)

end YMGap.Continuum.ChebOddFaceSOS

#print axioms YMGap.Continuum.ChebOddFaceSOS.adjacentU_determinant
#print axioms YMGap.Continuum.ChebOddFaceSOS.oddU_boundary
#print axioms YMGap.Continuum.ChebOddFaceSOS.one_add_T_odd_eq_sos
#print axioms YMGap.Continuum.ChebOddFaceSOS.odd_sos_sum
