/-
# Boundary-aware substitution into the one-Omega commutator

The abstract polynomial certificate for commuting first-pair exchange past one
inner Cayley contraction uses affine predecessor coefficients.  Natural-number
truncation changes those coefficients at the two second-coordinate faces.
This file performs the substitution on the whole physical box, treating the
two faces separately and using the polynomial certificate in the interior.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaExchangeCommutator

namespace YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCommutator
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast]; ac_rfl))

/-- First-pair exchange acting on the first two indices of a three-index
coefficient array. -/
def firstPairExchange3 (a b : Nat)
    (x : Nat → Nat → Nat → Q') (i j l : Nat) : Q' :=
  pairExchange a b (fun u v => x u v l) i j

/-- The split-coefficient form of one inner Cayley lift.  On natural
coefficients it is equivalent to the composite-coefficient transvectant
recurrence. -/
def omegaLiftSplit (b c : Nat)
    (x : Nat → Nat → Nat → Q') (i j l : Nat) : Q' :=
  (Q'.ofNat j * Q'.ofNat (c - l)) * x i (j - 1) l +
    -((Q'.ofNat (b - j) * Q'.ofNat l) * x i j (l - 1))

/-- The four shifted values left after commuting first-pair exchange through
one inner Cayley lift. -/
def omegaExchangeCorrection (a b c : Nat)
    (x : Nat → Nat → Nat → Q') (i j l : Nat) : Q' :=
  (Q'.ofNat i * Q'.ofNat (b - j)) *
      (Q'.ofNat (c - l) * x (i - 1) j l +
        Q'.ofNat l * x i j (l - 1)) +
    -((Q'.ofNat (a - i) * Q'.ofNat j) *
      (Q'.ofNat (c - l) * x i (j - 1) l +
        Q'.ofNat l * x (i + 1) (j - 1) (l - 1)))

/-! ## Polynomial substitution infrastructure -/

private theorem mul_eqv_congr' {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eval_env_congr (e : PolyExpr) (ρ σ : Nat → Q')
    (h : ∀ n, ρ n ≈ σ n) : eval ρ e ≈ eval σ e := by
  induction e with
  | const z => exact Q'.eqv_refl _
  | var n => exact h n
  | add p q hp hq => exact Q'.add_eqv_congr' hp hq
  | mul p q hp hq => exact mul_eqv_congr' hp hq
  | neg p hp => exact Q'.neg_eqv_congr _ _ hp
  | pow p n hp => exact qpow_eqv_congr hp n

private def pv (n : Nat) : PolyExpr := .var n
private def pc (n : Int) : PolyExpr := .const n
private def pa (x y : PolyExpr) : PolyExpr := .add x y
private def pm (x y : PolyExpr) : PolyExpr := .mul x y
private def pn (x : PolyExpr) : PolyExpr := .neg x
private def ps (x y : PolyExpr) : PolyExpr := pa x (pn y)

/- Variable order: `A,I,J,B,C,L,x1,...,x6,Jm,Bp,Jp,Bm`. -/
private def omegaBase : PolyExpr :=
  ps (pm (pm (pv 2) (pv 4)) (pv 8))
    (pm (pm (pv 3) (pv 5)) (pv 9))

private def omegaExpandedLHSExpr : PolyExpr :=
  pa
    (pm (pm (pv 0) (pv 2))
      (ps
        (ps (pm (pm (pv 12) (pv 4)) (pv 6))
          (pm (pm (pv 13) (pv 5)) (pv 7)))
        omegaBase))
    (pm (pm (pv 1) (pv 3))
      (ps
        (ps (pm (pm (pv 14) (pv 4)) (pv 10))
          (pm (pm (pv 15) (pv 5)) (pv 11)))
        omegaBase))

private def omegaExpandedRHSExpr : PolyExpr :=
  pa
    (ps
      (pm (pm (pv 2) (pv 4))
        (pa
          (pm (pm (pv 0) (pv 12)) (ps (pv 6) (pv 8)))
          (pm (pm (pv 1) (pv 3)) (ps (pv 10) (pv 8)))))
      (pm (pm (pv 3) (pv 5))
        (pa
          (pm (pm (pv 0) (pv 2)) (ps (pv 7) (pv 9)))
          (pm (pm (pv 1) (pv 15)) (ps (pv 11) (pv 9))))))
    (ps
      (pm (pm (pv 1) (pv 3))
        (pa (pm (pv 4) (pv 10)) (pm (pv 5) (pv 9))))
      (pm (pm (pv 0) (pv 2))
        (pa (pm (pv 4) (pv 8)) (pm (pv 5) (pv 7)))))

private def omegaBaseEnv
    (A I J B C L x1 x2 x3 x4 x5 x6 : Q') : Nat → Q' := fun n =>
  if n = 0 then A else if n = 1 then I else if n = 2 then J else
  if n = 3 then B else if n = 4 then C else if n = 5 then L else
  if n = 6 then x1 else if n = 7 then x2 else if n = 8 then x3 else
  if n = 9 then x4 else if n = 10 then x5 else x6

private def omegaEnv (base : Nat → Q')
    (Jm Bp Jp Bm : Q') : Nat → Q' := fun n =>
  if n = 12 then Jm else if n = 13 then Bp else
  if n = 14 then Jp else if n = 15 then Bm else base n

private theorem omega_eval_congr (e : PolyExpr)
    (base base' : Nat → Q')
    (Jm Bp Jp Bm Jm' Bp' Jp' Bm' : Q')
    (hbase : ∀ n, base n ≈ base' n)
    (hJm : Jm ≈ Jm') (hBp : Bp ≈ Bp')
    (hJp : Jp ≈ Jp') (hBm : Bm ≈ Bm') :
    eval (omegaEnv base Jm Bp Jp Bm) e ≈
      eval (omegaEnv base' Jm' Bp' Jp' Bm') e := by
  apply eval_env_congr
  intro n
  unfold omegaEnv
  by_cases h12 : n = 12
  · simp only [h12, if_pos]; exact hJm
  · simp only [h12]
    by_cases h13 : n = 13
    · simp only [h13, if_pos]; exact hBp
    · simp only [h13]
      by_cases h14 : n = 14
      · simp only [h14, if_pos]; exact hJp
      · simp only [h14]
        by_cases h15 : n = 15
        · simp only [h15, if_pos]; exact hBm
        · simp only [h15]; exact hbase n

private theorem ofNat_pred_eqv (n : Nat) (hn : 0 < n) :
    Q'.ofNat (n - 1) ≈ Q'.ofNat n + -(1 : Q') := by
  change ((n - 1 : Nat) : Int) * (1 : Int) =
    ((n : Int) * (1 : Int) + (-1 : Int) * (1 : Int)) * (1 : Int)
  omega

/-! ## Interior substitution and the two face certificates -/

private theorem omega_exchange_interior_substitution
    (A I J B C L Jm Bp Jp Bm x1 x2 x3 x4 x5 x6 : Q')
    (hJm : Jm ≈ J + -(1 : Q')) (hBp : Bp ≈ B + 1)
    (hJp : Jp ≈ J + 1) (hBm : Bm ≈ B + -(1 : Q')) :
    eval (omegaEnv (omegaBaseEnv A I J B C L x1 x2 x3 x4 x5 x6)
        Jm Bp Jp Bm) omegaExpandedLHSExpr ≈
      eval (omegaEnv (omegaBaseEnv A I J B C L x1 x2 x3 x4 x5 x6)
        Jm Bp Jp Bm) omegaExpandedRHSExpr := by
  let base := omegaBaseEnv A I J B C L x1 x2 x3 x4 x5 x6
  have hbase : ∀ n, base n ≈ base n := fun n => Q'.eqv_refl _
  have hleft := omega_eval_congr omegaExpandedLHSExpr base base
    Jm Bp Jp Bm (J + -1) (B + 1) (J + 1) (B + -1)
    hbase hJm hBp hJp hBm
  have hright := omega_eval_congr omegaExpandedRHSExpr base base
    Jm Bp Jp Bm (J + -1) (B + 1) (J + 1) (B + -1)
    hbase hJm hBp hJp hBm
  have hring := omega_exchange_commutator_ring
    A I J B C L x1 x2 x3 x4 x5 x6
  have hring' :
      eval (omegaEnv base (J + -1) (B + 1) (J + 1) (B + -1))
          omegaExpandedLHSExpr ≈
        eval (omegaEnv base (J + -1) (B + 1) (J + 1) (B + -1))
          omegaExpandedRHSExpr := by
    simpa [base, omegaExpandedLHSExpr, omegaExpandedRHSExpr, omegaBase,
      omegaEnv, omegaBaseEnv, pv, pa, pm, pn, ps, eval] using hring
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hring' (Q'.eqv_symm hright))

private def lowerFaceLHS : PolyExpr :=
  pm (pm (pv 0) (pa (pv 1) (pc 1)))
    (ps
      (ps (pm (pv 2) (pv 5)) (pm (pm (pv 1) (pv 3)) (pv 6)))
      (pn (pm (pm (pa (pv 1) (pc 1)) (pv 3)) (pv 4))))

private def lowerFaceRHS : PolyExpr :=
  pa
    (pn (pm (pm (pa (pv 1) (pc 1)) (pv 3))
      (pm (pm (pv 0) (pv 1)) (ps (pv 6) (pv 4)))))
    (pm (pm (pv 0) (pa (pv 1) (pc 1)))
      (pa (pm (pv 2) (pv 5)) (pm (pv 3) (pv 4))))

private theorem lowerFace_normal :
    normalize lowerFaceLHS = normalize lowerFaceRHS := by decide

private theorem lower_face_ring (I M C L x4 x5 x6 : Q') :
    (I * (M + 1)) *
        (((C * x5 + -((M * L) * x6))) +
          -(-(((M + 1) * L) * x4))) ≈
      -(((M + 1) * L) * ((I * M) * (x6 + -x4))) +
        (I * (M + 1)) * (C * x5 + L * x4) := by
  let ρ : Nat → Q' := fun n =>
    if n = 0 then I else if n = 1 then M else if n = 2 then C else
    if n = 3 then L else if n = 4 then x4 else if n = 5 then x5 else x6
  have h := poly_identity_of_normal_eq lowerFaceLHS lowerFaceRHS
    lowerFace_normal ρ
  simpa [lowerFaceLHS, lowerFaceRHS, pv, pc, pa, pm, pn, ps, eval, ρ] using h

private def lowerRawLHS : PolyExpr :=
  pm (pm (pv 0) (pv 1))
    (ps
      (ps (pm (pv 3) (pv 6)) (pm (pm (pv 2) (pv 4)) (pv 7)))
      (pn (pm (pm (pv 1) (pv 4)) (pv 5))))

private def lowerRawRHS : PolyExpr :=
  pa
    (pn (pm (pm (pv 1) (pv 4))
      (pm (pm (pv 0) (pv 2)) (ps (pv 7) (pv 5)))))
    (pm (pm (pv 0) (pv 1))
      (pa (pm (pv 3) (pv 6)) (pm (pv 4) (pv 5))))

private def lowerRawEnv (I B M C L x4 x5 x6 : Q') : Nat → Q' := fun n =>
  if n = 0 then I else if n = 1 then B else if n = 2 then M else
  if n = 3 then C else if n = 4 then L else if n = 5 then x4 else
  if n = 6 then x5 else x6

private theorem lower_face_substitution
    (I B M C L x4 x5 x6 : Q') (hB : B ≈ M + 1) :
    (I * B) *
        (((C * x5 + -((M * L) * x6))) + -(-((B * L) * x4))) ≈
      -((B * L) * ((I * M) * (x6 + -x4))) +
        (I * B) * (C * x5 + L * x4) := by
  let ρ := lowerRawEnv I B M C L x4 x5 x6
  let σ := lowerRawEnv I (M + 1) M C L x4 x5 x6
  have henv : ∀ n, ρ n ≈ σ n := by
    intro n
    by_cases h1 : n = 1
    · subst n
      simpa [ρ, σ, lowerRawEnv] using hB
    · unfold ρ σ lowerRawEnv
      simp only [h1]
      exact Q'.eqv_refl _
  have hL := eval_env_congr lowerRawLHS ρ σ henv
  have hR := eval_env_congr lowerRawRHS ρ σ henv
  have hring := lower_face_ring I M C L x4 x5 x6
  have hL' :
      (I * B) *
          (((C * x5 + -((M * L) * x6))) + -(-((B * L) * x4))) ≈
        (I * (M + 1)) *
          (((C * x5 + -((M * L) * x6))) +
            -(-(((M + 1) * L) * x4))) := by
    simpa [ρ, σ, lowerRawEnv, lowerRawLHS, pv, pa, pm, pn, ps, eval]
      using hL
  have hR' :
      -((B * L) * ((I * M) * (x6 + -x4))) +
          (I * B) * (C * x5 + L * x4) ≈
        -(((M + 1) * L) * ((I * M) * (x6 + -x4))) +
          (I * (M + 1)) * (C * x5 + L * x4) := by
    simpa [ρ, σ, lowerRawEnv, lowerRawRHS, pv, pa, pm, pn, ps, eval]
      using hR
  exact Q'.eqv_trans _ _ _ hL'
    (Q'.eqv_trans _ _ _ hring (Q'.eqv_symm hR'))

private def upperFaceLHS : PolyExpr :=
  pm (pm (pv 0) (pa (pv 1) (pc 1)))
    (ps
      (ps (pm (pm (pv 1) (pv 2)) (pv 4)) (pm (pv 3) (pv 5)))
      (pm (pm (pa (pv 1) (pc 1)) (pv 2)) (pv 6)))

private def upperFaceRHS : PolyExpr :=
  pa
    (pm (pm (pa (pv 1) (pc 1)) (pv 2))
      (pm (pm (pv 0) (pv 1)) (ps (pv 4) (pv 6))))
    (pn (pm (pm (pv 0) (pa (pv 1) (pc 1)))
      (pa (pm (pv 2) (pv 6)) (pm (pv 3) (pv 5)))))

private theorem upperFace_normal :
    normalize upperFaceLHS = normalize upperFaceRHS := by decide

private theorem upper_face_ring (A M C L x1 x2 x3 : Q') :
    (A * (M + 1)) *
        (((M * C) * x1 + -(L * x2)) +
          -(((M + 1) * C) * x3)) ≈
      ((M + 1) * C) * ((A * M) * (x1 + -x3)) +
        -((A * (M + 1)) * (C * x3 + L * x2)) := by
  let ρ : Nat → Q' := fun n =>
    if n = 0 then A else if n = 1 then M else if n = 2 then C else
    if n = 3 then L else if n = 4 then x1 else if n = 5 then x2 else x3
  have h := poly_identity_of_normal_eq upperFaceLHS upperFaceRHS
    upperFace_normal ρ
  simpa [upperFaceLHS, upperFaceRHS, pv, pc, pa, pm, pn, ps, eval, ρ] using h

private def upperRawLHS : PolyExpr :=
  pm (pm (pv 0) (pv 1))
    (ps
      (ps (pm (pm (pv 2) (pv 3)) (pv 5)) (pm (pv 4) (pv 6)))
      (pm (pm (pv 1) (pv 3)) (pv 7)))

private def upperRawRHS : PolyExpr :=
  pa
    (pm (pm (pv 1) (pv 3))
      (pm (pm (pv 0) (pv 2)) (ps (pv 5) (pv 7))))
    (pn (pm (pm (pv 0) (pv 1))
      (pa (pm (pv 3) (pv 7)) (pm (pv 4) (pv 6)))))

private def upperRawEnv (A J M C L x1 x2 x3 : Q') : Nat → Q' := fun n =>
  if n = 0 then A else if n = 1 then J else if n = 2 then M else
  if n = 3 then C else if n = 4 then L else if n = 5 then x1 else
  if n = 6 then x2 else x3

private theorem upper_face_substitution
    (A J M C L x1 x2 x3 : Q') (hJ : J ≈ M + 1) :
    (A * J) *
        ((((M * C) * x1 + -(L * x2))) + -((J * C) * x3)) ≈
      (J * C) * ((A * M) * (x1 + -x3)) +
        -((A * J) * (C * x3 + L * x2)) := by
  let ρ := upperRawEnv A J M C L x1 x2 x3
  let σ := upperRawEnv A (M + 1) M C L x1 x2 x3
  have henv : ∀ n, ρ n ≈ σ n := by
    intro n
    by_cases h1 : n = 1
    · subst n
      simpa [ρ, σ, upperRawEnv] using hJ
    · unfold ρ σ upperRawEnv
      simp only [h1]
      exact Q'.eqv_refl _
  have hL := eval_env_congr upperRawLHS ρ σ henv
  have hR := eval_env_congr upperRawRHS ρ σ henv
  have hring := upper_face_ring A M C L x1 x2 x3
  have hL' :
      (A * J) *
          ((((M * C) * x1 + -(L * x2))) + -((J * C) * x3)) ≈
        (A * (M + 1)) *
          ((((M * C) * x1 + -(L * x2))) + -(((M + 1) * C) * x3)) := by
    simpa [ρ, σ, upperRawEnv, upperRawLHS, pv, pa, pm, pn, ps, eval]
      using hL
  have hR' :
      (J * C) * ((A * M) * (x1 + -x3)) +
          -((A * J) * (C * x3 + L * x2)) ≈
        ((M + 1) * C) * ((A * M) * (x1 + -x3)) +
          -((A * (M + 1)) * (C * x3 + L * x2)) := by
    simpa [ρ, σ, upperRawEnv, upperRawRHS, pv, pa, pm, pn, ps, eval]
      using hR
  exact Q'.eqv_trans _ _ _ hL'
    (Q'.eqv_trans _ _ _ hring (Q'.eqv_symm hR'))

/- The following substitutions retain the zero-scaled boundary branches
literally.  This makes their statements definitionally match the unfolded
finite-box operator, while the reflective normalizer discards those branches
only inside its proved soundness theorem. -/

private def polySubst (σ : Nat → PolyExpr) : PolyExpr → PolyExpr
  | .const z => .const z
  | .var n => σ n
  | .add p q => .add (polySubst σ p) (polySubst σ q)
  | .mul p q => .mul (polySubst σ p) (polySubst σ q)
  | .neg p => .neg (polySubst σ p)
  | .pow p n => .pow (polySubst σ p) n

private def lowerFullMap : Nat → PolyExpr := fun n =>
  if n = 0 then pv 0 else if n = 1 then pv 1 else
  if n = 2 then pc 0 else if n = 3 then pa (pv 2) (pc 1) else
  if n = 4 then pv 3 else if n = 5 then pv 4 else
  if n = 6 then pv 5 else if n = 7 then pv 6 else
  if n = 8 then pv 7 else if n = 9 then pv 8 else
  if n = 10 then pv 9 else if n = 11 then pv 10 else
  if n = 12 then pc 0 else if n = 13 then pa (pv 2) (pc 1) else
  if n = 14 then pc 1 else pv 2

private def lowerFullLHS : PolyExpr :=
  polySubst lowerFullMap omegaExpandedLHSExpr

private def lowerFullRHS : PolyExpr :=
  polySubst lowerFullMap omegaExpandedRHSExpr

private theorem lowerFull_normal :
    normalize lowerFullLHS = normalize lowerFullRHS := by decide

private theorem lower_full_ring
    (A I M C L x1 x2 x3 x4 x5 x6 : Q') :
    eval (omegaEnv
        (omegaBaseEnv A I 0 (M + 1) C L x1 x2 x3 x4 x5 x6)
        0 (M + 1) 1 M) omegaExpandedLHSExpr ≈
      eval (omegaEnv
        (omegaBaseEnv A I 0 (M + 1) C L x1 x2 x3 x4 x5 x6)
        0 (M + 1) 1 M) omegaExpandedRHSExpr := by
  let ρ : Nat → Q' := fun n =>
    if n = 0 then A else if n = 1 then I else if n = 2 then M else
    if n = 3 then C else if n = 4 then L else if n = 5 then x1 else
    if n = 6 then x2 else if n = 7 then x3 else if n = 8 then x4 else
    if n = 9 then x5 else x6
  have h := poly_identity_of_normal_eq lowerFullLHS lowerFullRHS
    lowerFull_normal ρ
  simpa [lowerFullLHS, lowerFullRHS, polySubst, lowerFullMap,
    omegaExpandedLHSExpr, omegaExpandedRHSExpr, omegaBase, omegaEnv,
    omegaBaseEnv, pv, pc, pa, pm, pn, ps, eval, ρ] using h

private theorem lower_full_substitution
    (A I B M C L x1 x2 x3 x4 x5 x6 : Q') (hB : B ≈ M + 1) :
    eval (omegaEnv
        (omegaBaseEnv A I 0 B C L x1 x2 x3 x4 x5 x6)
        0 B 1 M) omegaExpandedLHSExpr ≈
      eval (omegaEnv
        (omegaBaseEnv A I 0 B C L x1 x2 x3 x4 x5 x6)
        0 B 1 M) omegaExpandedRHSExpr := by
  let base := omegaBaseEnv A I 0 B C L x1 x2 x3 x4 x5 x6
  let base' := omegaBaseEnv A I 0 (M + 1) C L x1 x2 x3 x4 x5 x6
  have hbase : ∀ n, base n ≈ base' n := by
    intro n
    by_cases h3 : n = 3
    · subst n
      simpa [base, base', omegaBaseEnv] using hB
    · unfold base base' omegaBaseEnv
      simp only [h3]
      exact Q'.eqv_refl _
  have hL := omega_eval_congr omegaExpandedLHSExpr base base'
    0 B 1 M 0 (M + 1) 1 M hbase
    (Q'.eqv_refl _) hB (Q'.eqv_refl _) (Q'.eqv_refl _)
  have hR := omega_eval_congr omegaExpandedRHSExpr base base'
    0 B 1 M 0 (M + 1) 1 M hbase
    (Q'.eqv_refl _) hB (Q'.eqv_refl _) (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hL
    (Q'.eqv_trans _ _ _
      (lower_full_ring A I M C L x1 x2 x3 x4 x5 x6)
      (Q'.eqv_symm hR))

private def upperFullMap : Nat → PolyExpr := fun n =>
  if n = 0 then pv 0 else if n = 1 then pv 1 else
  if n = 2 then pa (pv 2) (pc 1) else if n = 3 then pc 0 else
  if n = 4 then pv 3 else if n = 5 then pv 4 else
  if n = 6 then pv 5 else if n = 7 then pv 6 else
  if n = 8 then pv 7 else if n = 9 then pv 8 else
  if n = 10 then pv 9 else if n = 11 then pv 10 else
  if n = 12 then pv 2 else if n = 13 then pc 1 else
  if n = 14 then pv 11 else pc 0

private def upperFullLHS : PolyExpr :=
  polySubst upperFullMap omegaExpandedLHSExpr

private def upperFullRHS : PolyExpr :=
  polySubst upperFullMap omegaExpandedRHSExpr

private theorem upperFull_normal :
    normalize upperFullLHS = normalize upperFullRHS := by decide

private theorem upper_full_ring
    (A I M C L x1 x2 x3 x4 x5 x6 P : Q') :
    eval (omegaEnv
        (omegaBaseEnv A I (M + 1) 0 C L x1 x2 x3 x4 x5 x6)
        M 1 P 0) omegaExpandedLHSExpr ≈
      eval (omegaEnv
        (omegaBaseEnv A I (M + 1) 0 C L x1 x2 x3 x4 x5 x6)
        M 1 P 0) omegaExpandedRHSExpr := by
  let ρ : Nat → Q' := fun n =>
    if n = 0 then A else if n = 1 then I else if n = 2 then M else
    if n = 3 then C else if n = 4 then L else if n = 5 then x1 else
    if n = 6 then x2 else if n = 7 then x3 else if n = 8 then x4 else
    if n = 9 then x5 else if n = 10 then x6 else P
  have h := poly_identity_of_normal_eq upperFullLHS upperFullRHS
    upperFull_normal ρ
  simpa [upperFullLHS, upperFullRHS, polySubst, upperFullMap,
    omegaExpandedLHSExpr, omegaExpandedRHSExpr, omegaBase, omegaEnv,
    omegaBaseEnv, pv, pc, pa, pm, pn, ps, eval, ρ] using h

private theorem upper_full_substitution
    (A I J M C L x1 x2 x3 x4 x5 x6 P : Q') (hJ : J ≈ M + 1) :
    eval (omegaEnv
        (omegaBaseEnv A I J 0 C L x1 x2 x3 x4 x5 x6)
        M 1 P 0) omegaExpandedLHSExpr ≈
      eval (omegaEnv
        (omegaBaseEnv A I J 0 C L x1 x2 x3 x4 x5 x6)
        M 1 P 0) omegaExpandedRHSExpr := by
  let base := omegaBaseEnv A I J 0 C L x1 x2 x3 x4 x5 x6
  let base' := omegaBaseEnv A I (M + 1) 0 C L x1 x2 x3 x4 x5 x6
  have hbase : ∀ n, base n ≈ base' n := by
    intro n
    by_cases h2 : n = 2
    · subst n
      simpa [base, base', omegaBaseEnv] using hJ
    · unfold base base' omegaBaseEnv
      simp only [h2]
      exact Q'.eqv_refl _
  have hL := omega_eval_congr omegaExpandedLHSExpr base base'
    M 1 P 0 M 1 P 0 hbase
    (Q'.eqv_refl _) (Q'.eqv_refl _) (Q'.eqv_refl _) (Q'.eqv_refl _)
  have hR := omega_eval_congr omegaExpandedRHSExpr base base'
    M 1 P 0 M 1 P 0 hbase
    (Q'.eqv_refl _) (Q'.eqv_refl _) (Q'.eqv_refl _) (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hL
    (Q'.eqv_trans _ _ _
      (upper_full_ring A I M C L x1 x2 x3 x4 x5 x6 P)
      (Q'.eqv_symm hR))

private def zeroFullMap : Nat → PolyExpr := fun n =>
  if n = 0 then pv 0 else if n = 1 then pv 1 else
  if n = 2 then pc 0 else if n = 3 then pc 0 else
  if n = 4 then pv 2 else if n = 5 then pv 3 else
  if n = 6 then pv 4 else if n = 7 then pv 5 else
  if n = 8 then pv 6 else if n = 9 then pv 7 else
  if n = 10 then pv 8 else if n = 11 then pv 9 else
  if n = 12 then pc 0 else if n = 13 then pc 0 else
  if n = 14 then pc 1 else pc 0

private def zeroFullLHS : PolyExpr :=
  polySubst zeroFullMap omegaExpandedLHSExpr

private def zeroFullRHS : PolyExpr :=
  polySubst zeroFullMap omegaExpandedRHSExpr

private theorem zeroFull_normal :
    normalize zeroFullLHS = normalize zeroFullRHS := by decide

private theorem zero_full_ring
    (A I C L x1 x2 x3 x4 x5 x6 : Q') :
    eval (omegaEnv
        (omegaBaseEnv A I 0 0 C L x1 x2 x3 x4 x5 x6)
        0 0 1 0) omegaExpandedLHSExpr ≈
      eval (omegaEnv
        (omegaBaseEnv A I 0 0 C L x1 x2 x3 x4 x5 x6)
        0 0 1 0) omegaExpandedRHSExpr := by
  let ρ : Nat → Q' := fun n =>
    if n = 0 then A else if n = 1 then I else if n = 2 then C else
    if n = 3 then L else if n = 4 then x1 else if n = 5 then x2 else
    if n = 6 then x3 else if n = 7 then x4 else if n = 8 then x5 else x6
  have h := poly_identity_of_normal_eq zeroFullLHS zeroFullRHS
    zeroFull_normal ρ
  simpa [zeroFullLHS, zeroFullRHS, polySubst, zeroFullMap,
    omegaExpandedLHSExpr, omegaExpandedRHSExpr, omegaBase, omegaEnv,
    omegaBaseEnv, pv, pc, pa, pm, pn, ps, eval, ρ] using h

/- At the lower face, the predecessor-successor identity
`(j-1)+1=j` is false.  Its only occurrence is under the zero lift
coefficient, so the exact finite-box expression needs one additional,
independent coordinate `y5`. -/

private def lowerBoundaryBase : PolyExpr :=
  ps (pm (pm (pc 0) (pv 4)) (pv 8))
    (pm (pm (pv 2) (pv 5)) (pv 9))

private def lowerBoundaryRawLHS : PolyExpr :=
  pa
    (pm (pm (pv 0) (pc 0))
      (ps
        (ps (pm (pm (pc 0) (pv 4)) (pv 6))
          (pm (pm (pv 2) (pv 5)) (pv 7)))
        lowerBoundaryBase))
    (pm (pm (pv 1) (pv 2))
      (ps
        (ps (pm (pm (pc 1) (pv 4)) (pv 10))
          (pm (pm (pv 3) (pv 5)) (pv 11)))
        lowerBoundaryBase))

private def lowerBoundaryRawRHS : PolyExpr :=
  pa
    (ps
      (pm (pm (pc 0) (pv 4))
        (pa
          (pm (pm (pv 0) (pc 0)) (ps (pv 6) (pv 8)))
          (pm (pm (pv 1) (pv 3)) (ps (pv 12) (pv 8)))))
      (pm (pm (pv 2) (pv 5))
        (pa
          (pm (pm (pv 0) (pc 0)) (ps (pv 7) (pv 9)))
          (pm (pm (pv 1) (pv 3)) (ps (pv 11) (pv 9))))))
    (ps
      (pm (pm (pv 1) (pv 2))
        (pa (pm (pv 4) (pv 10)) (pm (pv 5) (pv 9))))
      (pm (pm (pv 0) (pc 0))
        (pa (pm (pv 4) (pv 8)) (pm (pv 5) (pv 7)))))

private def lowerBoundaryMap : Nat → PolyExpr := fun n =>
  if n = 0 then pv 0 else if n = 1 then pv 1 else
  if n = 2 then pa (pv 2) (pc 1) else if n = 3 then pv 2 else
  if n = 4 then pv 3 else if n = 5 then pv 4 else
  if n = 6 then pv 5 else if n = 7 then pv 6 else
  if n = 8 then pv 7 else if n = 9 then pv 8 else
  if n = 10 then pv 9 else if n = 11 then pv 10 else pv 11

private def lowerBoundaryLHS : PolyExpr :=
  polySubst lowerBoundaryMap lowerBoundaryRawLHS

private def lowerBoundaryRHS : PolyExpr :=
  polySubst lowerBoundaryMap lowerBoundaryRawRHS

private theorem lowerBoundary_normal :
    normalize lowerBoundaryLHS = normalize lowerBoundaryRHS := by decide

private def lowerBoundaryRawEnv
    (A I B M C L x1 x2 x3 x4 x5 x6 y5 : Q') : Nat → Q' := fun n =>
  if n = 0 then A else if n = 1 then I else if n = 2 then B else
  if n = 3 then M else if n = 4 then C else if n = 5 then L else
  if n = 6 then x1 else if n = 7 then x2 else if n = 8 then x3 else
  if n = 9 then x4 else if n = 10 then x5 else if n = 11 then x6 else y5

private theorem lower_boundary_ring
    (A I M C L x1 x2 x3 x4 x5 x6 y5 : Q') :
    eval (lowerBoundaryRawEnv A I (M + 1) M C L
        x1 x2 x3 x4 x5 x6 y5) lowerBoundaryRawLHS ≈
      eval (lowerBoundaryRawEnv A I (M + 1) M C L
        x1 x2 x3 x4 x5 x6 y5) lowerBoundaryRawRHS := by
  let ρ : Nat → Q' := fun n =>
    if n = 0 then A else if n = 1 then I else if n = 2 then M else
    if n = 3 then C else if n = 4 then L else if n = 5 then x1 else
    if n = 6 then x2 else if n = 7 then x3 else if n = 8 then x4 else
    if n = 9 then x5 else if n = 10 then x6 else y5
  have h := poly_identity_of_normal_eq lowerBoundaryLHS lowerBoundaryRHS
    lowerBoundary_normal ρ
  simpa [lowerBoundaryLHS, lowerBoundaryRHS, polySubst, lowerBoundaryMap,
    lowerBoundaryRawLHS, lowerBoundaryRawRHS, lowerBoundaryBase,
    lowerBoundaryRawEnv, pv, pc, pa, pm, pn, ps, eval, ρ] using h

private theorem lower_boundary_substitution
    (A I B M C L x1 x2 x3 x4 x5 x6 y5 : Q') (hB : B ≈ M + 1) :
    eval (lowerBoundaryRawEnv A I B M C L
        x1 x2 x3 x4 x5 x6 y5) lowerBoundaryRawLHS ≈
      eval (lowerBoundaryRawEnv A I B M C L
        x1 x2 x3 x4 x5 x6 y5) lowerBoundaryRawRHS := by
  let ρ := lowerBoundaryRawEnv A I B M C L x1 x2 x3 x4 x5 x6 y5
  let σ := lowerBoundaryRawEnv A I (M + 1) M C L x1 x2 x3 x4 x5 x6 y5
  have henv : ∀ n, ρ n ≈ σ n := by
    intro n
    by_cases h2 : n = 2
    · subst n
      simpa [ρ, σ, lowerBoundaryRawEnv] using hB
    · unfold ρ σ lowerBoundaryRawEnv
      simp only [h2]
      exact Q'.eqv_refl _
  have hL := eval_env_congr lowerBoundaryRawLHS ρ σ henv
  have hR := eval_env_congr lowerBoundaryRawRHS ρ σ henv
  exact Q'.eqv_trans _ _ _ hL
    (Q'.eqv_trans _ _ _
      (lower_boundary_ring A I M C L x1 x2 x3 x4 x5 x6 y5)
      (Q'.eqv_symm hR))

private def lowerBoundaryZeroMap : Nat → PolyExpr := fun n =>
  if n = 0 then pv 0 else if n = 1 then pv 1 else
  if n = 2 then pc 0 else if n = 3 then pc 0 else
  if n = 4 then pv 2 else if n = 5 then pv 3 else
  if n = 6 then pv 4 else if n = 7 then pv 5 else
  if n = 8 then pv 6 else if n = 9 then pv 7 else
  if n = 10 then pv 8 else if n = 11 then pv 9 else pv 10

private def lowerBoundaryZeroLHS : PolyExpr :=
  polySubst lowerBoundaryZeroMap lowerBoundaryRawLHS

private def lowerBoundaryZeroRHS : PolyExpr :=
  polySubst lowerBoundaryZeroMap lowerBoundaryRawRHS

private theorem lowerBoundaryZero_normal :
    normalize lowerBoundaryZeroLHS = normalize lowerBoundaryZeroRHS := by decide

private theorem lower_boundary_zero_ring
    (A I C L x1 x2 x3 x4 x5 x6 y5 : Q') :
    eval (lowerBoundaryRawEnv A I 0 0 C L
        x1 x2 x3 x4 x5 x6 y5) lowerBoundaryRawLHS ≈
      eval (lowerBoundaryRawEnv A I 0 0 C L
        x1 x2 x3 x4 x5 x6 y5) lowerBoundaryRawRHS := by
  let ρ : Nat → Q' := fun n =>
    if n = 0 then A else if n = 1 then I else if n = 2 then C else
    if n = 3 then L else if n = 4 then x1 else if n = 5 then x2 else
    if n = 6 then x3 else if n = 7 then x4 else if n = 8 then x5 else
    if n = 9 then x6 else y5
  have h := poly_identity_of_normal_eq lowerBoundaryZeroLHS lowerBoundaryZeroRHS
    lowerBoundaryZero_normal ρ
  simpa [lowerBoundaryZeroLHS, lowerBoundaryZeroRHS, polySubst,
    lowerBoundaryZeroMap, lowerBoundaryRawLHS, lowerBoundaryRawRHS,
    lowerBoundaryBase, lowerBoundaryRawEnv, pv, pc, pa, pm, pn, ps, eval, ρ]
    using h

/-- **Full-box one-Omega commutator.**  The first-pair exchange at degree
`(a,b)` commutes through the Cayley lift from degree `(a,b-1)`, up to the
explicit four-term correction.  The theorem includes both truncated-natural
faces `j=0` and `j=b`. -/
theorem firstPairExchange3_omegaLiftSplit {a b c i j l : Nat}
    (x : Nat → Nat → Nat → Q') (hj : j ≤ b) :
    firstPairExchange3 a b (omegaLiftSplit b c x) i j l ≈
      omegaLiftSplit b c (firstPairExchange3 a (b - 1) x) i j l +
        omegaExchangeCorrection a b c x i j l := by
  by_cases hj0 : j = 0
  · subst j
    by_cases hb0 : b = 0
    · subst b
      have h := lower_boundary_zero_ring
        (Q'.ofNat (a - i)) (Q'.ofNat i) (Q'.ofNat (c - l))
        (Q'.ofNat l)
        (x (i + 1) 0 l) (x (i + 1) 0 (l - 1))
        (x i 0 l) (x i 0 (l - 1))
        (x (i - 1) 0 l) (x (i - 1) 1 (l - 1)) (x (i - 1) 1 l)
      simpa [firstPairExchange3, omegaLiftSplit, omegaExchangeCorrection,
        pairExchange, lowerBoundaryRawLHS, lowerBoundaryRawRHS,
        lowerBoundaryBase, lowerBoundaryRawEnv, pv, pc, pa, pm, pn, ps, eval,
        show Q'.ofNat 0 = (0 : Q') from rfl,
        show Q'.ofNat 1 = (1 : Q') from rfl,
        show Q'.ofInt 0 = (0 : Q') from rfl,
        show Q'.ofInt 1 = (1 : Q') from rfl] using h
    · have hbpos : 0 < b := by omega
      have hbpredsucc : b - 1 + 1 = b := by omega
      have hB : Q'.ofNat b ≈ Q'.ofNat (b - 1) + 1 := by
        simpa only [hbpredsucc] using Q'.ofNat_add_eqv (b - 1) 1
      have h := lower_boundary_substitution
        (Q'.ofNat (a - i)) (Q'.ofNat i) (Q'.ofNat b)
        (Q'.ofNat (b - 1)) (Q'.ofNat (c - l)) (Q'.ofNat l)
        (x (i + 1) 0 l) (x (i + 1) 0 (l - 1))
        (x i 0 l) (x i 0 (l - 1))
        (x (i - 1) 0 l) (x (i - 1) 1 (l - 1)) (x (i - 1) 1 l) hB
      simpa [firstPairExchange3, omegaLiftSplit, omegaExchangeCorrection,
        pairExchange, lowerBoundaryRawLHS, lowerBoundaryRawRHS,
        lowerBoundaryBase, lowerBoundaryRawEnv, pv, pc, pa, pm, pn, ps, eval,
        show b - (0 + 1) = b - 1 by omega,
        show Q'.ofNat 0 = (0 : Q') from rfl,
        show Q'.ofNat 1 = (1 : Q') from rfl,
        show Q'.ofInt 0 = (0 : Q') from rfl,
        show Q'.ofInt 1 = (1 : Q') from rfl] using h
  · by_cases hjb : j = b
    · subst j
      have hbpos : 0 < b := by omega
      have hbpredsucc : b - 1 + 1 = b := by omega
      have hJ : Q'.ofNat b ≈ Q'.ofNat (b - 1) + 1 := by
        simpa only [hbpredsucc] using Q'.ofNat_add_eqv (b - 1) 1
      have h := upper_full_substitution
        (Q'.ofNat (a - i)) (Q'.ofNat i) (Q'.ofNat b)
        (Q'.ofNat (b - 1)) (Q'.ofNat (c - l)) (Q'.ofNat l)
        (x (i + 1) (b - 2) l) (x (i + 1) (b - 1) (l - 1))
        (x i (b - 1) l) (x i b (l - 1))
        (x (i - 1) b l) (x (i - 1) (b + 1) (l - 1))
        (Q'.ofNat (b + 1)) hJ
      simpa [firstPairExchange3, omegaLiftSplit, omegaExchangeCorrection,
        pairExchange, omegaExpandedLHSExpr, omegaExpandedRHSExpr, omegaBase,
        omegaEnv, omegaBaseEnv, pv, pa, pm, pn, ps, eval,
        show b - b = 0 by omega,
        show b - 1 - (b - 1) = 0 by omega,
        show b - (b + 1) = 0 by omega,
        show b - 1 - b = 0 by omega,
        show b - (b - 1) = 1 by omega,
        show b - 1 + 1 = b by omega,
        show 1 + (b - 1) = b by omega,
        show Q'.ofNat 0 = (0 : Q') from rfl,
        show Q'.ofNat 1 = (1 : Q') from rfl] using h
    · have hjpos : 0 < j := by omega
      have hjlt : j < b := by omega
      have hjpred : b - (j - 1) = b - j + 1 := by omega
      have hjsucc : b - (j + 1) = b - j - 1 := by omega
      have hredpred : b - 1 - (j - 1) = b - j := by omega
      have hredhere : b - 1 - j = b - j - 1 := by omega
      have hjm1 : j - 1 + 1 = j := by omega
      have hjp1m1 : j + 1 - 1 = j := by omega
      have hjm1m1 : j - 1 - 1 = j - 2 := by omega
      have hJm := ofNat_pred_eqv j hjpos
      have hBp : Q'.ofNat (b - j + 1) ≈ Q'.ofNat (b - j) + 1 :=
        Q'.ofNat_add_eqv (b - j) 1
      have hJp : Q'.ofNat (j + 1) ≈ Q'.ofNat j + 1 :=
        Q'.ofNat_add_eqv j 1
      have hBm := ofNat_pred_eqv (b - j) (by omega)
      have h := omega_exchange_interior_substitution
        (Q'.ofNat (a - i)) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat (b - j)) (Q'.ofNat (c - l)) (Q'.ofNat l)
        (Q'.ofNat (j - 1)) (Q'.ofNat (b - j + 1))
        (Q'.ofNat (j + 1)) (Q'.ofNat (b - j - 1))
        (x (i + 1) (j - 2) l)
        (x (i + 1) (j - 1) (l - 1))
        (x i (j - 1) l) (x i j (l - 1))
        (x (i - 1) j l) (x (i - 1) (j + 1) (l - 1))
        hJm hBp hJp hBm
      simpa [firstPairExchange3, omegaLiftSplit, omegaExchangeCorrection,
        pairExchange, omegaExpandedLHSExpr, omegaExpandedRHSExpr, omegaBase,
        omegaEnv, omegaBaseEnv, pv, pa, pm, pn, ps, eval,
        hjpred, hjsucc, hredpred, hredhere, hjm1, hjp1m1, hjm1m1] using h

end YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution.firstPairExchange3_omegaLiftSplit
