/-
# Discharging the two PURE-ALGEBRA residuals of the √-weighted FTC
# antiderivative identity: `UDClosure` and `BAssembly`

The companion module `ChebOrthoWeightedFTC` reduces the even-order Chebyshev-`U`
orthogonality antiderivative identity

    `(1−x²)·B_e′ − x·B_e ≈ −2·(1−x²)·U_e`     (`Bderiv_identity`)

to THREE residuals: the derivative relation `UDClosure` (all orders), the clean
two-term Chebyshev difference `TdiffClosure` (PROVED there, as
`TdiffClosure_proved`), and the denominator-clearing assembly `BAssembly`.

This module discharges the two remaining PURE-ALGEBRA residuals UNCONDITIONALLY:

  * **`udClosure : ChebOrthoWeightedFTC.UDClosure`** — the Dirichlet-kernel
    derivative relation `(1−x²)·U_n′ ≈ x·U_n − (n+1)·T_{n+1}` at ALL orders.
    Base cases `UD_zero`/`UD_one` are proved in the companion; here we supply the
    2-step inductive step `UD_step : UD n → UD (n+1) → UD (n+2)` and the all-order
    packager `UD_all`.  The step collapses, after substituting the two induction
    hypotheses and the closed `U`/`T`-recurrences, to the crux relation
    `x·T_{n+2} − T_{n+1} ≈ −(1−x²)·U_{n+1}` — exactly the `Tcombo_abstract`
    combination of the proved ladder relation `linRel_all` and the shift identity
    `ChebU.Tshift`.

  * **`bAssembly : ChebOrthoWeightedFTC.BAssembly`** — the denominator-clearing
    ring rearrangement.  `B_e` and `B_e′` carry the `mkPos`-scaled `1/e`,
    `1/(e+2)` quotient terms; the `ofNat e`, `ofNat (e+2)` coefficients in the two
    `UD` instances clear them exactly, via the cancellation lemma
    `CRealMul.ofNatMul_mkPos_eqv` (`ofNat M · (a.num/(a.den·M)) ≈ a`).

  * **`Bderiv_identity_uncond`** — the antiderivative identity
    `(1−x²)·B_e′ − x·B_e ≈ −2·(1−x²)·U_e`, now UNCONDITIONAL (compose
    `Bderiv_identity` with `udClosure`, `TdiffClosure_proved`, `bAssembly`).

## What is PROVED here (axiom-clean, π-free)

  * `UD_step` / `UD_pair` / `UD_all` ⇒ `udClosure` — the U-derivative relation at
    ALL orders, by 2-step induction; the inductive step is a genuine `Q'`-ring
    `calc` over the proved ladder/shift/recurrence atoms.
  * `bAssembly` — the denominator-clearing assembly.
  * `Bderiv_identity_uncond` — the unconditional antiderivative identity.

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot: `[propext]` /
`[propext, Quot.sound]`.
-/

import YMGap.Continuum.ChebOrthoWeightedFTC

namespace YMGap.Continuum.ChebUDClosure

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebOrthoWeightedFTC

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## Small additive-group `Q'` helpers (reused throughout the `calc` chains). -/

/-- `a + (-a) ≈ 0`. -/
theorem add_neg_self (a : Q') : a + (-a) ≈ (0 : Q') := Q'.add_neg_self_eqv a

/-- `(-a) + a ≈ 0`. -/
theorem neg_add_self (a : Q') : (-a) + a ≈ (0 : Q') := Q'.neg_add_self_eqv a

/-- Negation-flip of a difference: from `(a + (-b)) ≈ P` conclude
`(b + (-a)) ≈ (-P)`. -/
theorem flip_neg_of_sub {a b P : Q'} (h : (a + (-b)) ≈ P) : (b + (-a)) ≈ (-P) := by
  calc b + (-a)
      ≈ (-a) + b := Q'.add_comm_eqv _ _
    _ ≈ (-a) + (-(-b)) := Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.neg_neg_eqv b))
    _ ≈ -(a + (-b)) := Q'.eqv_symm (Cheb.neg_add_eqv a (-b))
    _ ≈ (-P) := Q'.neg_eqv_congr _ _ h

/-! ## The crux relation `x·T_{n+2} − T_{n+1} ≈ −(1−x²)·U_{n+1}`

This is the single Chebyshev relation the inductive `UD` step collapses to.
It is the negation of the `Tcombo_abstract` combination of the proved ladder
relation `linRel_all` (`U_{n+1} ≈ T_{n+1} + x·U_n`) and the shift identity
`ChebU.Tshift` (`T_{n+2} ≈ x·U_{n+1} − U_n`). -/

/-- **The crux relation.**  `x·T_{n+2}(x) − T_{n+1}(x) ≈ −(1−x²)·U_{n+1}(x)`. -/
theorem crux (n : Nat) (x : Q') :
    (x * Cheb.T (n+2) x + (-(Cheb.T (n+1) x)))
      ≈ (-((1 + (-(x*x))) * Cheb.U (n+1) x)) := by
  -- ladder (B): U_{n+1} ≈ T_{n+1} + x·U_n
  obtain ⟨_hA, hB⟩ := Cheb.linRel_all n x
  -- hT1 : T_{n+1} ≈ U_{n+1} + (−(x·U_n))
  have hT1 : Cheb.T (n+1) x ≈ (Cheb.U (n+1) x + (-(x * Cheb.U n x))) :=
    ChebOrthoWeightedFTC.sub_of_add_eqv hB
  -- hT2 : T_{n+2} ≈ x·U_{n+1} + (−(U_n))
  have hT2 : Cheb.T (n+2) x ≈ (x * Cheb.U (n+1) x + (-(Cheb.U n x))) :=
    ChebU.Tshift n x
  -- Tcombo: T_{n+1} − x·T_{n+2} ≈ (1−x²)·U_{n+1}
  have hcombo : (Cheb.T (n+1) x + (-(x * Cheb.T (n+2) x)))
      ≈ ((1 + (-(x*x))) * Cheb.U (n+1) x) :=
    ChebOrthoWeightedFTC.Tcombo_abstract x (Cheb.U n x) (Cheb.U (n+1) x)
      (Cheb.T (n+1) x) (Cheb.T (n+2) x) hT1 hT2
  -- flip the sign
  exact flip_neg_of_sub hcombo

/-! ## Additive-group regrouping helpers for the inductive step. -/

/-- `-(a + (-b)) ≈ (-a) + b`. -/
theorem neg_sub (a b : Q') : (-(a + (-b))) ≈ ((-a) + b) :=
  Q'.eqv_trans _ _ _ (Cheb.neg_add_eqv a (-b))
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv b))

/-- `(a + b) + c ≈ (a + c) + b` (swap last two through the bracket). -/
theorem add_right_comm3 (a b c : Q') : (a + b) + c ≈ (a + c) + b :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b c)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv b c))
      (Q'.eqv_symm (Q'.add_assoc_eqv a c b)))

/-- `(a·b)·c ≈ b·(a·c)` — pull `b` out front. -/
theorem mul_left_comm3 (a b c : Q') : (a * b) * c ≈ b * (a * c) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a b))
    (Q'.mul_assoc_eqv b a c)

/-- `a·(b·c) ≈ b·(a·c)` — swap the two outer factors. -/
theorem mul_swap_outer (a b c : Q') : a * (b * c) ≈ b * (a * c) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) (mul_left_comm3 a b c)

/-- `2·(a·b) ≈ a·(2·b)` (specialisation used to move the leading `2`). -/
theorem two_mul_swap (a b : Q') : (2:Q') * (a * b) ≈ a * ((2:Q') * b) :=
  mul_swap_outer (2:Q') a b

/-! ## The crux, doubled: `−((2x)·T_{n+2}) + 2·T_{n+1} ≈ 2·((1−x²)·U_{n+1})`. -/

/-- The doubled crux: `(−((2x)·T_{n+2})) + 2·T_{n+1} ≈ 2·((1−x²)·U_{n+1})`. -/
theorem crux2 (n : Nat) (x : Q') :
    ((-(((2:Q')*x) * Cheb.T (n+2) x)) + (2:Q') * Cheb.T (n+1) x)
      ≈ ((2:Q') * ((1 + (-(x*x))) * Cheb.U (n+1) x)) := by
  have hc := crux n x  -- x·Tn2 + (-Tn1) ≈ -(c·Un1)
  -- (-(x·Tn2)) + Tn1 ≈ c·Un1
  have hstep : ((-(x * Cheb.T (n+2) x)) + Cheb.T (n+1) x)
      ≈ ((1 + (-(x*x))) * Cheb.U (n+1) x) := by
    calc (-(x * Cheb.T (n+2) x)) + Cheb.T (n+1) x
        ≈ (-(x * Cheb.T (n+2) x + (-(Cheb.T (n+1) x)))) :=
          Q'.eqv_symm (neg_sub (x * Cheb.T (n+2) x) (Cheb.T (n+1) x))
      _ ≈ (-(-((1 + (-(x*x))) * Cheb.U (n+1) x))) := Q'.neg_eqv_congr _ _ hc
      _ ≈ ((1 + (-(x*x))) * Cheb.U (n+1) x) := Q'.neg_neg_eqv _
  -- now multiply by 2 and reassociate the (2x) factor
  calc (-(((2:Q')*x) * Cheb.T (n+2) x)) + (2:Q') * Cheb.T (n+1) x
      ≈ (-((2:Q') * (x * Cheb.T (n+2) x))) + (2:Q') * Cheb.T (n+1) x :=
        Q'.add_eqv_congr_right _ _ _
          (Q'.neg_eqv_congr _ _ (Q'.mul_assoc_eqv (2:Q') x (Cheb.T (n+2) x)))
    _ ≈ ((2:Q') * (-(x * Cheb.T (n+2) x))) + (2:Q') * Cheb.T (n+1) x :=
        Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.mul_neg_eqv (2:Q') (x * Cheb.T (n+2) x)))
    _ ≈ (2:Q') * ((-(x * Cheb.T (n+2) x)) + Cheb.T (n+1) x) :=
        Q'.eqv_symm (Q'.mul_add_eqv (2:Q') (-(x * Cheb.T (n+2) x)) (Cheb.T (n+1) x))
    _ ≈ (2:Q') * ((1 + (-(x*x))) * Cheb.U (n+1) x) :=
        Q'.mul_eqv_congr_left _ _ _ hstep

/-! ## The abstract coefficient-collapse `★`

`(2·cU) + (−(e2·W)) + e1·T ≈ (−(e3·W)) + e3·T`, given the doubled crux
`(−W) + 2·T ≈ 2·cU` and the coefficient relations `e3 ≈ e2 + 1`, `e3 ≈ e1 + 2`.
Pure `Q'` additive/distributive algebra. -/

theorem step_collapse (cU W T e1 e2 e3 : Q')
    (hC : ((-W) + (2:Q')*T) ≈ ((2:Q')*cU))
    (h32 : e3 ≈ (e2 + (1:Q')))
    (h31 : e3 ≈ (e1 + (2:Q'))) :
    (((2:Q')*cU + (-(e2*W))) + e1*T)
      ≈ ((-(e3*W)) + e3*T) := by
  -- Expand the RHS using the two coefficient decompositions.
  have hW : (-(e3*W)) ≈ ((-(e2*W)) + (-W)) := by
    calc (-(e3*W))
        ≈ (-((e2 + (1:Q'))*W)) := Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ h32)
      _ ≈ (-(e2*W + (1:Q')*W)) := Q'.neg_eqv_congr _ _ (Cheb.add_mul_eqv e2 (1:Q') W)
      _ ≈ (-(e2*W + W)) :=
          Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv W))
      _ ≈ ((-(e2*W)) + (-W)) := Cheb.neg_add_eqv (e2*W) W
  have hT : (e3*T) ≈ (e1*T + (2:Q')*T) := by
    calc (e3*T)
        ≈ ((e1 + (2:Q'))*T) := Q'.mul_eqv_congr_right _ _ _ h31
      _ ≈ (e1*T + (2:Q')*T) := Cheb.add_mul_eqv e1 (2:Q') T
  -- RHS ≈ ((-(e2·W)) + (-W)) + (e1·T + 2·T)
  have hRHS : ((-(e3*W)) + e3*T)
      ≈ (((-(e2*W)) + (-W)) + (e1*T + (2:Q')*T)) :=
    Cheb.add_eqv_congr _ _ _ _ hW hT
  -- Now massage that into the LHS.
  -- ((-(e2W)) + (-W)) + (e1T + 2T)
  --   ≈ ((-(e2W)) + e1T) + ((-W) + 2T)        (swap inner)
  --   ≈ ((-(e2W)) + e1T) + (2cU)              (hC)
  --   ≈ (2cU + (-(e2W))) + e1T                (regroup)
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hRHS)
  calc (((2:Q')*cU + (-(e2*W))) + e1*T)
      ≈ ((2:Q')*cU + ((-(e2*W)) + e1*T)) := Q'.add_assoc_eqv _ _ _
    _ ≈ (((-(e2*W)) + e1*T) + (2:Q')*cU) := Q'.add_comm_eqv _ _
    _ ≈ (((-(e2*W)) + e1*T) + ((-W) + (2:Q')*T)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hC)
    _ ≈ (((-(e2*W)) + (-W)) + (e1*T + (2:Q')*T)) :=
        Q'.add_swap_inner (-(e2*W)) (e1*T) (-W) ((2:Q')*T)

/-! ## The abstract `L ≈ R` identity for the inductive step

`L` is `(1−x²)·U_{n+2}′` after distributing `(1−x²)` and substituting the two
induction hypotheses; `R` is `x·U_{n+2} − (n+3)·T_{n+3}` after the `U`/`T`
recurrences.  Both reduce to a common shape and collapse via `step_collapse`. -/

theorem step_LR (x Un Un1 Tn1 Tn2 cU e1 e2 e3 : Q')
    (hC : ((-(((2:Q')*x)*Tn2)) + (2:Q')*Tn1) ≈ ((2:Q')*cU))
    (h32 : e3 ≈ (e2 + (1:Q')))
    (h31 : e3 ≈ (e1 + (2:Q'))) :
    ( (2:Q')*cU
        + ( ((2:Q')*x) * (x*Un1 + (-(e2*Tn2)))
            + (-(x*Un + (-(e1*Tn1)))) ) )
      ≈ ( x * (((2:Q')*x)*Un1 + (-Un))
            + (-(e3 * (((2:Q')*x)*Tn2 + (-Tn1)))) ) := by
  -- Write `A := (2x)·(x·Un1)`, `W := (2x)·Tn2`, `B := x·Un` inline.
  -- LHS reduction:  L ≈ (A + (-B)) + ((2cU + (-(e2·W))) + e1·T)
  have hM : ((2:Q')*x) * (x*Un1 + (-(e2*Tn2)))
      ≈ (((2:Q')*x)*(x*Un1) + (-(e2*(((2:Q')*x)*Tn2)))) := by
    calc ((2:Q')*x) * (x*Un1 + (-(e2*Tn2)))
        ≈ ((2:Q')*x)*(x*Un1) + ((2:Q')*x)*(-(e2*Tn2)) :=
          Q'.mul_add_eqv _ _ _
      _ ≈ ((2:Q')*x)*(x*Un1) + (-(((2:Q')*x)*(e2*Tn2))) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv ((2:Q')*x) (e2*Tn2))
      _ ≈ ((2:Q')*x)*(x*Un1) + (-(e2*(((2:Q')*x)*Tn2))) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (mul_swap_outer ((2:Q')*x) e2 Tn2))
  have hN : (-(x*Un + (-(e1*Tn1)))) ≈ ((-(x*Un)) + e1*Tn1) := neg_sub (x*Un) (e1*Tn1)
  have hLred : ( (2:Q')*cU
        + ( ((2:Q')*x) * (x*Un1 + (-(e2*Tn2))) + (-(x*Un + (-(e1*Tn1)))) ) )
      ≈ ((((2:Q')*x)*(x*Un1) + (-(x*Un)))
            + (((2:Q')*cU + (-(e2*(((2:Q')*x)*Tn2)))) + e1*Tn1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Cheb.add_eqv_congr _ _ _ _ hM hN)) ?_
    calc (2:Q')*cU + ((((2:Q')*x)*(x*Un1) + (-(e2*(((2:Q')*x)*Tn2)))) + ((-(x*Un)) + e1*Tn1))
        ≈ (2:Q')*cU + ((((2:Q')*x)*(x*Un1) + (-(x*Un))) + ((-(e2*(((2:Q')*x)*Tn2))) + e1*Tn1)) :=
          Q'.add_eqv_congr_left _ _ _
            (Q'.add_swap_inner (((2:Q')*x)*(x*Un1)) (-(e2*(((2:Q')*x)*Tn2))) (-(x*Un)) (e1*Tn1))
      _ ≈ ((((2:Q')*x)*(x*Un1) + (-(x*Un))) + ((-(e2*(((2:Q')*x)*Tn2))) + e1*Tn1)) + (2:Q')*cU :=
          Q'.add_comm_eqv _ _
      _ ≈ (((2:Q')*x)*(x*Un1) + (-(x*Un)))
            + (((-(e2*(((2:Q')*x)*Tn2))) + e1*Tn1) + (2:Q')*cU) := Q'.add_assoc_eqv _ _ _
      _ ≈ (((2:Q')*x)*(x*Un1) + (-(x*Un)))
            + ((2:Q')*cU + ((-(e2*(((2:Q')*x)*Tn2))) + e1*Tn1)) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
      _ ≈ (((2:Q')*x)*(x*Un1) + (-(x*Un)))
            + (((2:Q')*cU + (-(e2*(((2:Q')*x)*Tn2)))) + e1*Tn1) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
  -- RHS reduction:  R ≈ (A + (-B)) + ((-(e3·W)) + e3·T)
  have hRred : ( x * (((2:Q')*x)*Un1 + (-Un))
            + (-(e3 * (((2:Q')*x)*Tn2 + (-Tn1)))) )
      ≈ ((((2:Q')*x)*(x*Un1) + (-(x*Un)))
            + ((-(e3*(((2:Q')*x)*Tn2))) + e3*Tn1)) := by
    refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
    · -- x·((2x)·Un1 + (-Un)) ≈ A + (-B)
      calc x * (((2:Q')*x)*Un1 + (-Un))
          ≈ x*(((2:Q')*x)*Un1) + x*(-Un) := Q'.mul_add_eqv _ _ _
        _ ≈ ((2:Q')*x)*(x*Un1) + x*(-Un) :=
            Q'.add_eqv_congr_right _ _ _ (mul_swap_outer x ((2:Q')*x) Un1)
        _ ≈ ((2:Q')*x)*(x*Un1) + (-(x*Un)) :=
            Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv x Un)
    · -- (-(e3·((2x)Tn2 + (-Tn1)))) ≈ (-(e3·W)) + e3·Tn1
      calc (-(e3 * (((2:Q')*x)*Tn2 + (-Tn1))))
          ≈ (-(e3*(((2:Q')*x)*Tn2) + e3*(-Tn1))) :=
            Q'.neg_eqv_congr _ _ (Q'.mul_add_eqv e3 (((2:Q')*x)*Tn2) (-Tn1))
        _ ≈ (-(e3*(((2:Q')*x)*Tn2) + (-(e3*Tn1)))) :=
            Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv e3 Tn1))
        _ ≈ ((-(e3*(((2:Q')*x)*Tn2))) + e3*Tn1) := neg_sub (e3*(((2:Q')*x)*Tn2)) (e3*Tn1)
  -- collapse the brackets and chain
  have hcoll :
      (((2:Q')*cU + (-(e2*(((2:Q')*x)*Tn2)))) + e1*Tn1)
        ≈ ((-(e3*(((2:Q')*x)*Tn2))) + e3*Tn1) :=
    step_collapse cU (((2:Q')*x)*Tn2) Tn1 e1 e2 e3 hC h32 h31
  refine Q'.eqv_trans _ _ _ hLred ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hcoll) ?_
  exact Q'.eqv_symm hRred

/-! ## Coefficient relations `ofNat (n+3) ≈ ofNat (n+2) + 1` etc. -/

/-- `ofNat (n+3) ≈ ofNat (n+2) + 1`. -/
theorem ofNat_n3_eq_n2 (n : Nat) :
    Q'.ofNat (n+3) ≈ (Q'.ofNat (n+2) + (1:Q')) := by
  have h : Q'.ofNat (n+2) + (1:Q') ≈ Q'.ofNat (n+3) := by
    rw [ChebU.one_eq_ofNat]
    exact Q'.eqv_trans _ _ _ (ChebU.ofNat_add_eqv (n+2) 1) (by
      have : n + 2 + 1 = n + 3 := by omega
      rw [this]; exact Q'.eqv_refl _)
  exact Q'.eqv_symm h

/-- `ofNat (n+3) ≈ ofNat (n+1) + 2`. -/
theorem ofNat_n3_eq_n1 (n : Nat) :
    Q'.ofNat (n+3) ≈ (Q'.ofNat (n+1) + (2:Q')) := by
  have h : Q'.ofNat (n+1) + (2:Q') ≈ Q'.ofNat (n+3) := by
    rw [ChebU.two_eq_ofNat]
    exact Q'.eqv_trans _ _ _ (ChebU.ofNat_add_eqv (n+1) 2) (by
      have : n + 1 + 2 = n + 3 := by omega
      rw [this]; exact Q'.eqv_refl _)
  exact Q'.eqv_symm h

/-! ## The inductive step `UD n → UD (n+1) → UD (n+2)` -/

/-- **The 2-step inductive step of the derivative relation.**  From the two
induction hypotheses `UD n`, `UD (n+1)` (substituting `(1−x²)·U_n′`,
`(1−x²)·U_{n+1}′`) and the closed `U`/`T`-recurrences, `UD (n+2)` follows; the
residual collapses (via `step_LR`/`step_collapse`) to the crux relation
`x·T_{n+2} − T_{n+1} ≈ −(1−x²)·U_{n+1}` (`crux2`). -/
theorem UD_step (n : Nat) (x : Q')
    (ih0 : ChebOrthoWeightedFTC.UD n x) (ih1 : ChebOrthoWeightedFTC.UD (n+1) x) :
    ChebOrthoWeightedFTC.UD (n+2) x := by
  -- unfold the goal
  show ((1 + (-(x*x))) * ChebOrthoWeightedFTC.Uderiv (n+2) x)
      ≈ (x * Cheb.U (n+2) x + (-(Q'.ofNat (n+2+1) * Cheb.T (n+2+1) x)))
  -- the two IHs (note (n)+1 = n+1 indices on the RHS)
  have hIH0 : ((1 + (-(x*x))) * ChebOrthoWeightedFTC.Uderiv n x)
      ≈ (x * Cheb.U n x + (-(Q'.ofNat (n+1) * Cheb.T (n+1) x))) := ih0
  have hIH1 : ((1 + (-(x*x))) * ChebOrthoWeightedFTC.Uderiv (n+1) x)
      ≈ (x * Cheb.U (n+1) x + (-(Q'.ofNat (n+2) * Cheb.T (n+2) x))) := ih1
  -- LHS reduction:  (1−x²)·U_{n+2}′ ≈ L
  have hL : ((1 + (-(x*x))) * ChebOrthoWeightedFTC.Uderiv (n+2) x)
      ≈ ( (2:Q')*((1 + (-(x*x)))*Cheb.U (n+1) x)
          + ( ((2:Q')*x) * (x*Cheb.U (n+1) x + (-(Q'.ofNat (n+2)*Cheb.T (n+2) x)))
              + (-(x*Cheb.U n x + (-(Q'.ofNat (n+1)*Cheb.T (n+1) x)))) ) ) := by
    rw [ChebOrthoWeightedFTC.Uderiv_succ_succ]
    -- (1−x²)·(2·U(n+1) + ((2x)·dn1 + (-dn)))
    calc (1 + (-(x*x))) *
            ((2:Q') * Cheb.U (n+1) x
              + (((2:Q')*x) * ChebOrthoWeightedFTC.Uderiv (n+1) x
                  + (-(ChebOrthoWeightedFTC.Uderiv n x))))
        ≈ (1 + (-(x*x)))*((2:Q') * Cheb.U (n+1) x)
            + (1 + (-(x*x)))*(((2:Q')*x) * ChebOrthoWeightedFTC.Uderiv (n+1) x
                  + (-(ChebOrthoWeightedFTC.Uderiv n x))) :=
          Q'.mul_add_eqv _ _ _
      _ ≈ (2:Q')*((1 + (-(x*x)))*Cheb.U (n+1) x)
            + (1 + (-(x*x)))*(((2:Q')*x) * ChebOrthoWeightedFTC.Uderiv (n+1) x
                  + (-(ChebOrthoWeightedFTC.Uderiv n x))) :=
          Q'.add_eqv_congr_right _ _ _ (mul_swap_outer (1 + (-(x*x))) (2:Q') (Cheb.U (n+1) x))
      _ ≈ (2:Q')*((1 + (-(x*x)))*Cheb.U (n+1) x)
            + ( (1 + (-(x*x)))*(((2:Q')*x) * ChebOrthoWeightedFTC.Uderiv (n+1) x)
                + (1 + (-(x*x)))*(-(ChebOrthoWeightedFTC.Uderiv n x)) ) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.mul_add_eqv _ _ _)
      _ ≈ (2:Q')*((1 + (-(x*x)))*Cheb.U (n+1) x)
            + ( ((2:Q')*x)*((1 + (-(x*x))) * ChebOrthoWeightedFTC.Uderiv (n+1) x)
                + (-((1 + (-(x*x)))*ChebOrthoWeightedFTC.Uderiv n x)) ) :=
          Q'.add_eqv_congr_left _ _ _
            (Cheb.add_eqv_congr _ _ _ _
              (mul_swap_outer (1 + (-(x*x))) ((2:Q')*x) (ChebOrthoWeightedFTC.Uderiv (n+1) x))
              (Q'.mul_neg_eqv (1 + (-(x*x))) (ChebOrthoWeightedFTC.Uderiv n x)))
      _ ≈ ( (2:Q')*((1 + (-(x*x)))*Cheb.U (n+1) x)
            + ( ((2:Q')*x) * (x*Cheb.U (n+1) x + (-(Q'.ofNat (n+2)*Cheb.T (n+2) x)))
                + (-(x*Cheb.U n x + (-(Q'.ofNat (n+1)*Cheb.T (n+1) x)))) ) ) :=
          Q'.add_eqv_congr_left _ _ _
            (Cheb.add_eqv_congr _ _ _ _
              (Q'.mul_eqv_congr_left _ _ _ hIH1)
              (Q'.neg_eqv_congr _ _ hIH0))
  -- RHS reduction:  x·U(n+2) − ofNat(n+3)·T(n+3) ≈ R
  have hR : (x * Cheb.U (n+2) x + (-(Q'.ofNat (n+2+1) * Cheb.T (n+2+1) x)))
      ≈ ( x * (((2:Q')*x)*Cheb.U (n+1) x + (-(Cheb.U n x)))
            + (-(Q'.ofNat (n+2+1) * (((2:Q')*x)*Cheb.T (n+2) x + (-(Cheb.T (n+1) x))))) ) :=
    Q'.eqv_refl _
  -- now apply step_LR with the right coefficients (e3 = ofNat (n+3))
  have hn3 : n + 2 + 1 = n + 3 := by omega
  rw [hn3] at hR ⊢
  refine Q'.eqv_trans _ _ _ hL ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hR)
  exact step_LR x (Cheb.U n x) (Cheb.U (n+1) x) (Cheb.T (n+1) x) (Cheb.T (n+2) x)
    ((1 + (-(x*x)))*Cheb.U (n+1) x) (Q'.ofNat (n+1)) (Q'.ofNat (n+2)) (Q'.ofNat (n+3))
    (crux2 n x) (ofNat_n3_eq_n2 n) (ofNat_n3_eq_n1 n)

/-! ## All-order closure of the derivative relation -/

/-- Two-step induction packager: `UD n ∧ UD (n+1)` for all `n`.  Base cases
`UD_zero`/`UD_one` from the companion module; step from `UD_step`. -/
theorem UD_pair (x : Q') :
    ∀ n, ChebOrthoWeightedFTC.UD n x ∧ ChebOrthoWeightedFTC.UD (n+1) x := by
  intro n
  induction n with
  | zero => exact ⟨ChebOrthoWeightedFTC.UD_zero x, ChebOrthoWeightedFTC.UD_one x⟩
  | succ k ih =>
      obtain ⟨hk, hk1⟩ := ih
      exact ⟨hk1, UD_step k x hk hk1⟩

/-- The derivative relation `UD n` at every order. -/
theorem UD_all (n : Nat) (x : Q') : ChebOrthoWeightedFTC.UD n x := (UD_pair x n).1

/-- **`udClosure : UDClosure` — the U-derivative relation at ALL orders,
UNCONDITIONAL.**  `(1−x²)·U_n′(x) ≈ x·U_n(x) − (n+1)·T_{n+1}(x)`, π-free. -/
theorem udClosure : ChebOrthoWeightedFTC.UDClosure := fun n x => UD_all n x

/-! ## Denominator-clearing algebra for `BAssembly`

`B_e` and `B_e′` carry `mkPos`-scaled `1/e`, `1/(e+2)` quotient terms.  The two
`UD` instances carry the `ofNat e`, `ofNat (e+2)` coefficients that clear them.
The bridge is the scaling lemma `mkPos a.num (a.den·d) ≈ a·(1/d)` together with
`ofNat d · (1/d) ≈ 1`. -/

/-- `mkPos a.num (a.den·d) ≈ a · mkPos 1 d` — the `mkPos` quotient as an explicit
product with `1/d`. -/
theorem mkPosScale_eqv (a : Q') (d : Nat)
    (hd : 0 < a.den * d) (he : 0 < d) :
    (Q'.mkPos a.num (a.den * d) hd) ≈ (a * Q'.mkPos 1 d he) := by
  show (Q'.mkPos a.num (a.den * d) hd).num * ((a * Q'.mkPos 1 d he).den : Int)
      = (a * Q'.mkPos 1 d he).num * ((Q'.mkPos a.num (a.den * d) hd).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den, Q'.mul_den_cast, Q'.mkPos_den,
      show (a * Q'.mkPos 1 d he).num = a.num * 1 from rfl,
      Int.mul_one, Int.natCast_mul]

/-- `ofNat d · (1/d) ≈ 1` for `d > 0`. -/
theorem ofNat_mul_invPos (d : Nat) (he : 0 < d) :
    (Q'.ofNat d * Q'.mkPos 1 d he) ≈ (1 : Q') := by
  show (Q'.ofNat d * Q'.mkPos 1 d he).num * ((1:Q').den : Int)
      = (1:Q').num * ((Q'.ofNat d * Q'.mkPos 1 d he).den : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_den]
  show (Int.ofNat d * 1) * ((1:Q').den : Int)
      = (1:Q').num * (((Q'.ofNat d).den : Int) * (d : Int))
  show (Int.ofNat d * 1) * 1 = 1 * (1 * (d : Int))
  rw [Int.ofNat_eq_natCast]
  omega

/-- **Per-term denominator-clearing reduction.**  Given the `UD`-shaped relation
`(1−x²)·D ≈ x·V − (ofNat d)·S`, the scaled-by-`1/d` version holds:
`(1−x²)·(D/d) ≈ x·(V/d) − S`.  (Here `D/d := mkPos D.num (D.den·d)`.) -/
theorem term_reduce (x D V S : Q') (d : Nat)
    (hd : 0 < D.den * d) (hd2 : 0 < V.den * d) (he : 0 < d)
    (hUD : ((1 + (-(x*x))) * D) ≈ (x * V + (-(Q'.ofNat d * S)))) :
    ((1 + (-(x*x))) * Q'.mkPos D.num (D.den * d) hd)
      ≈ (x * Q'.mkPos V.num (V.den * d) hd2 + (-S)) := by
  -- δ := 1/d
  -- (1−x²)·(D/d) ≈ ((1−x²)·D)·δ ≈ (x·V − (ofNat d)·S)·δ
  calc (1 + (-(x*x))) * Q'.mkPos D.num (D.den * d) hd
      ≈ (1 + (-(x*x))) * (D * Q'.mkPos 1 d he) :=
        Q'.mul_eqv_congr_left _ _ _ (mkPosScale_eqv D d hd he)
    _ ≈ ((1 + (-(x*x))) * D) * Q'.mkPos 1 d he :=
        Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    _ ≈ (x * V + (-(Q'.ofNat d * S))) * Q'.mkPos 1 d he :=
        Q'.mul_eqv_congr_right _ _ _ hUD
    _ ≈ (x * V) * Q'.mkPos 1 d he + (-(Q'.ofNat d * S)) * Q'.mkPos 1 d he :=
        Cheb.add_mul_eqv _ _ _
    _ ≈ x * (V * Q'.mkPos 1 d he) + (-(Q'.ofNat d * S)) * Q'.mkPos 1 d he :=
        Q'.add_eqv_congr_right _ _ _ (Q'.mul_assoc_eqv _ _ _)
    _ ≈ x * Q'.mkPos V.num (V.den * d) hd2 + (-(Q'.ofNat d * S)) * Q'.mkPos 1 d he :=
        Q'.add_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (mkPosScale_eqv V d hd2 he)))
    _ ≈ x * Q'.mkPos V.num (V.den * d) hd2 + (-((Q'.ofNat d * S) * Q'.mkPos 1 d he)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv (Q'.ofNat d * S) (Q'.mkPos 1 d he))
    _ ≈ x * Q'.mkPos V.num (V.den * d) hd2 + (-S) := by
        refine Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ ?_)
        -- (ofNat d · S)·δ ≈ S·(ofNat d · δ) ≈ S·1 ≈ S
        calc (Q'.ofNat d * S) * Q'.mkPos 1 d he
            ≈ (S * Q'.ofNat d) * Q'.mkPos 1 d he :=
              Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (Q'.ofNat d) S)
          _ ≈ S * (Q'.ofNat d * Q'.mkPos 1 d he) := Q'.mul_assoc_eqv _ _ _
          _ ≈ S * (1 : Q') := Q'.mul_eqv_congr_left _ _ _ (ofNat_mul_invPos d he)
          _ ≈ S := Q'.mul_one_eqv S

/-- **The abstract `Bident` assembly.**  From the two per-term reductions
`(1−x²)·bm ≈ x·gm − Sm`, `(1−x²)·bp ≈ x·gp − Sp` and the two-term difference
`Sp − Sm ≈ Target`, conclude
`(1−x²)·(bm − bp) − x·(gm − gp) ≈ Target`.  Pure `Q'` additive algebra. -/
theorem bident_assemble (x bm bp gm gp Sm Sp Target : Q')
    (hb1 : ((1 + (-(x*x))) * bm) ≈ (x * gm + (-Sm)))
    (hb2 : ((1 + (-(x*x))) * bp) ≈ (x * gp + (-Sp)))
    (hTd : (Sp + (-Sm)) ≈ Target) :
    ((1 + (-(x*x))) * (bm + (-bp)) + (-(x * (gm + (-gp))))) ≈ Target := by
  -- (1−x²)·(bm − bp) ≈ (x·gm − Sm) + (−(x·gp − Sp))
  have hLeft : ((1 + (-(x*x))) * (bm + (-bp)))
      ≈ ((x * gm + (-Sm)) + (-(x * gp + (-Sp)))) := by
    calc (1 + (-(x*x))) * (bm + (-bp))
        ≈ (1 + (-(x*x)))*bm + (1 + (-(x*x)))*(-bp) := Q'.mul_add_eqv _ _ _
      _ ≈ (1 + (-(x*x)))*bm + (-((1 + (-(x*x)))*bp)) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv _ _)
      _ ≈ (x * gm + (-Sm)) + (-(x * gp + (-Sp))) :=
          Cheb.add_eqv_congr _ _ _ _ hb1 (Q'.neg_eqv_congr _ _ hb2)
  -- −(x·(gm − gp)) ≈ (−(x·gm)) + x·gp
  have hRight : (-(x * (gm + (-gp)))) ≈ ((-(x * gm)) + x * gp) := by
    calc (-(x * (gm + (-gp))))
        ≈ (-(x*gm + x*(-gp))) := Q'.neg_eqv_congr _ _ (Q'.mul_add_eqv _ _ _)
      _ ≈ (-(x*gm + (-(x*gp)))) :=
          Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv x gp))
      _ ≈ ((-(x*gm)) + x*gp) := neg_sub (x*gm) (x*gp)
  -- combine and cancel
  refine Q'.eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hLeft hRight) ?_
  -- ((x·gm + (-Sm)) + (-(x·gp + (-Sp)))) + ((-(x·gm)) + x·gp) ≈ Target
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left _ _ _ (neg_sub (x*gp) Sp))) ?_
  -- now: ((x·gm + (-Sm)) + ((-(x·gp)) + Sp)) + ((-(x·gm)) + x·gp) ≈ Target
  -- collect cancelling pairs (x·gm)/(−x·gm) and (−x·gp)/(x·gp); left (−Sm)+Sp
  calc (((x*gm + (-Sm)) + ((-(x*gp)) + Sp)) + ((-(x*gm)) + x*gp))
      ≈ (((x*gm + (-Sm)) + ((-(x*gp)) + Sp)) + (x*gp + (-(x*gm)))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
    _ ≈ ((x*gm + (-Sm)) + (((-(x*gp)) + Sp) + (x*gp + (-(x*gm))))) := Q'.add_assoc_eqv _ _ _
    _ ≈ ((x*gm + (-Sm)) + (((-(x*gp)) + x*gp) + (Sp + (-(x*gm))))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_swap_inner (-(x*gp)) Sp (x*gp) (-(x*gm)))
    _ ≈ ((x*gm + (-Sm)) + ((0:Q') + (Sp + (-(x*gm))))) :=
        Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_right _ _ _ (Q'.neg_add_self_eqv (x*gp)))
    _ ≈ ((x*gm + (-Sm)) + (Sp + (-(x*gm)))) := by
        refine Q'.add_eqv_congr_left _ _ _ ?_
        rw [Q'.zero_add']; exact Q'.eqv_refl _
    _ ≈ ((x*gm + (-Sm)) + ((-(x*gm)) + Sp)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
    _ ≈ ((x*gm + (-(x*gm))) + ((-Sm) + Sp)) :=
        Q'.add_swap_inner (x*gm) (-Sm) (-(x*gm)) Sp
    _ ≈ ((0:Q') + ((-Sm) + Sp)) :=
        Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv (x*gm))
    _ ≈ ((-Sm) + Sp) := by rw [Q'.zero_add']; exact Q'.eqv_refl _
    _ ≈ (Sp + (-Sm)) := Q'.add_comm_eqv _ _
    _ ≈ Target := hTd

/-! ## `bAssembly : BAssembly` — the denominator-clearing assembly, UNCONDITIONAL -/

/-- **`bAssembly : BAssembly`.**  The antiderivative-assembly ring rearrangement,
clearing the `1/e`, `1/(e+2)` `mkPos` denominators of `Gbracket`/`Bderiv` against
the `ofNat e`, `ofNat (e+2)` coefficients of the two `UD` instances.  π-free,
UNCONDITIONAL. -/
theorem bAssembly : ChebOrthoWeightedFTC.BAssembly := by
  intro e he he2 x hUDm hUDp hTd
  -- write e = m+2 so that e-1 = m+1, e+1 = m+3, e+2 = m+4 reduce.
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 2 := ⟨e - 2, by omega⟩
  -- per-term reduction at d = e = m+2 (the `bm`/`gm` term)
  have hd1 : 0 < (ChebOrthoWeightedFTC.Uderiv (m+1) x).den * (m+2) :=
    Nat.mul_pos (ChebOrthoWeightedFTC.Uderiv (m+1) x).den_pos (by omega)
  have hd1g : 0 < (Cheb.U (m+1) x).den * (m+2) :=
    Nat.mul_pos (Cheb.U (m+1) x).den_pos (by omega)
  have hterm1 :
      ((1 + (-(x*x))) * Q'.mkPos (ChebOrthoWeightedFTC.Uderiv (m+1) x).num
            ((ChebOrthoWeightedFTC.Uderiv (m+1) x).den * (m+2)) hd1)
        ≈ (x * Q'.mkPos (Cheb.U (m+1) x).num ((Cheb.U (m+1) x).den * (m+2)) hd1g
            + (-(Cheb.T (m+2) x))) :=
    term_reduce x (ChebOrthoWeightedFTC.Uderiv (m+1) x) (Cheb.U (m+1) x) (Cheb.T (m+2) x)
      (m+2) hd1 hd1g (by omega) hUDm
  -- per-term reduction at d = e+2 = m+4 (the `bp`/`gp` term)
  have hd2 : 0 < (ChebOrthoWeightedFTC.Uderiv (m+3) x).den * (m+4) :=
    Nat.mul_pos (ChebOrthoWeightedFTC.Uderiv (m+3) x).den_pos (by omega)
  have hd2g : 0 < (Cheb.U (m+3) x).den * (m+4) :=
    Nat.mul_pos (Cheb.U (m+3) x).den_pos (by omega)
  have hterm2 :
      ((1 + (-(x*x))) * Q'.mkPos (ChebOrthoWeightedFTC.Uderiv (m+3) x).num
            ((ChebOrthoWeightedFTC.Uderiv (m+3) x).den * (m+4)) hd2)
        ≈ (x * Q'.mkPos (Cheb.U (m+3) x).num ((Cheb.U (m+3) x).den * (m+4)) hd2g
            + (-(Cheb.T (m+4) x))) :=
    term_reduce x (ChebOrthoWeightedFTC.Uderiv (m+3) x) (Cheb.U (m+3) x) (Cheb.T (m+4) x)
      (m+4) hd2 hd2g (by omega) hUDp
  -- Tdiff (m+2):  T(m+4) − T(m+2) ≈ −2·(1−x²)·U(m+2)
  have hTd' : (Cheb.T (m+4) x + (-(Cheb.T (m+2) x)))
      ≈ (-(((1:Q') + (1:Q')) * ((1 + (-(x*x))) * Cheb.U (m+2) x))) := hTd
  -- assemble Bident (m+2)
  show ((1 + (-(x*x))) * ChebOrthoWeightedFTC.Bderiv (m+2) he x
        + (-(x * ChebOrthoOffDiag.Gbracket (m+2) he x)))
      ≈ (-(((1:Q') + (1:Q')) * ((1 + (-(x*x))) * Cheb.U (m+2) x)))
  exact bident_assemble x
    (Q'.mkPos (ChebOrthoWeightedFTC.Uderiv (m+1) x).num
        ((ChebOrthoWeightedFTC.Uderiv (m+1) x).den * (m+2)) hd1)
    (Q'.mkPos (ChebOrthoWeightedFTC.Uderiv (m+3) x).num
        ((ChebOrthoWeightedFTC.Uderiv (m+3) x).den * (m+4)) hd2)
    (Q'.mkPos (Cheb.U (m+1) x).num ((Cheb.U (m+1) x).den * (m+2)) hd1g)
    (Q'.mkPos (Cheb.U (m+3) x).num ((Cheb.U (m+3) x).den * (m+4)) hd2g)
    (Cheb.T (m+2) x) (Cheb.T (m+4) x)
    (-(((1:Q') + (1:Q')) * ((1 + (-(x*x))) * Cheb.U (m+2) x)))
    hterm1 hterm2 hTd'

/-! ## The UNCONDITIONAL antiderivative identity -/

/-- **`Bderiv_identity_uncond` — the polynomial antiderivative identity,
UNCONDITIONAL.**  For every `e ≥ 2`,
`(1−x²)·B_e′(x) − x·B_e(x) ≈ −2·(1−x²)·U_e(x)` — the certificate that
`Gval e = ½·√(1−x²)·B_e` is the antiderivative of `f_e = U_e·√(1−x²)`.  Composes
the companion `Bderiv_identity` with the now-proved `udClosure`,
`TdiffClosure_proved` and `bAssembly`.  π-free, UNCONDITIONAL. -/
theorem Bderiv_identity_uncond (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (x : Q') :
    ChebOrthoWeightedFTC.Bident e he x :=
  ChebOrthoWeightedFTC.Bderiv_identity udClosure
    ChebOrthoWeightedFTC.TdiffClosure_proved bAssembly e he he2 x

end YMGap.Continuum.ChebUDClosure

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content, π-free).**
  * `crux` / `crux2` — the single Chebyshev relation the inductive `UD` step
    collapses to: `x·T_{n+2} − T_{n+1} ≈ −(1−x²)·U_{n+1}` (and its doubled form),
    from `Tcombo_abstract` over the proved ladder relation `linRel_all` and the
    shift identity `ChebU.Tshift`.
  * `step_collapse` / `step_LR` — the abstract `Q'`-ring `calc` lemmas isolating
    the inductive-step coefficient collapse and the `L ≈ R` reduction.
  * `UD_step` — the 2-step inductive step `UD n → UD (n+1) → UD (n+2)`, a genuine
    multivariate `Q'`-ring `calc` over the closed `U`/`T`-recurrences, the two
    induction hypotheses, and the crux relation.
  * `UD_pair` / `UD_all` ⇒ **`udClosure : UDClosure`** — the Dirichlet-kernel
    derivative relation `(1−x²)·U_n′ ≈ x·U_n − (n+1)·T_{n+1}` at ALL orders,
    UNCONDITIONAL (base cases from the companion module).
  * `mkPosScale_eqv` / `ofNat_mul_invPos` / `term_reduce` / `bident_assemble` —
    the denominator-clearing algebra: `mkPos a.num (a.den·d) ≈ a·(1/d)`,
    `ofNat d·(1/d) ≈ 1`, the per-term reduction `(1−x²)·(D/d) ≈ x·(V/d) − S`, and
    the abstract assembly.
  * **`bAssembly : BAssembly`** — the denominator-clearing assembly rearrangement,
    UNCONDITIONAL.
  * **`Bderiv_identity_uncond`** — the polynomial antiderivative identity
    `(1−x²)·B_e′ − x·B_e ≈ −2·(1−x²)·U_e` at all `e ≥ 2`, now UNCONDITIONAL
    (composes the companion `Bderiv_identity` with `udClosure`,
    `TdiffClosure_proved`, `bAssembly`).

**NAMED-open (NOT addressed here; left in the companion module).**
  * `ChebOrthoWeightedFTC.WeightedFTCEstimate` — the constructive √-weighted FTC
    ESTIMATE (the only ANALYTIC, vs algebraic, residual): the per-cell increment
    bound summed `→ 0`.  This module discharges ONLY the two PURE-ALGEBRA
    residuals (`UDClosure`, `BAssembly`); the analytic estimate is untouched.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` not used. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebUDClosure.crux
#print axioms YMGap.Continuum.ChebUDClosure.crux2
#print axioms YMGap.Continuum.ChebUDClosure.step_collapse
#print axioms YMGap.Continuum.ChebUDClosure.step_LR
#print axioms YMGap.Continuum.ChebUDClosure.UD_step
#print axioms YMGap.Continuum.ChebUDClosure.UD_all
#print axioms YMGap.Continuum.ChebUDClosure.udClosure
#print axioms YMGap.Continuum.ChebUDClosure.mkPosScale_eqv
#print axioms YMGap.Continuum.ChebUDClosure.ofNat_mul_invPos
#print axioms YMGap.Continuum.ChebUDClosure.term_reduce
#print axioms YMGap.Continuum.ChebUDClosure.bident_assemble
#print axioms YMGap.Continuum.ChebUDClosure.bAssembly
#print axioms YMGap.Continuum.ChebUDClosure.Bderiv_identity_uncond
