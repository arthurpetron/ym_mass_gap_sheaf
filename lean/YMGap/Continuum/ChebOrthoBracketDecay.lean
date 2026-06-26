/-
# The bracket BOUNDARY-DECAY estimate and the closed radical leg.

This module supplies the ONE missing input behind the radical leg — the
boundary-decay bound `|x_k·B_e(x_k)| ≤ (1 − x_k²)·Cbd(e)` (the bracket factor
carries an extra `oms = 1 − x_k²` factor near the boundary) — and feeds it through
the PROVED antisymmetric reduction to close
`ChebOrthoLegAssembly.EventualRadLegRemainder e he`.

## The boundary-decay identity

`Bderiv_identity_uncond` (`Bident`) reads `(1−x²)·B_e′ − x·B_e ≈ −2(1−x²)·U_e`.
Rearranged at the node `x = x_k` it gives the EXACT identity
  `x_k·B0 ≈ oms·(B_e′(x_k) + 2·U_e(x_k))`,   `oms = 1 − x_k²`,
hence the boundary-decay value bound
  `|x_k·B0| ≤ oms·Cbd(e)`,   `Cbd(e) = Bbound e + 2(e+1)`,
using `|B_e′| ≤ Bbound e` (`Bderiv_abs_le`) and `|U_e| ≤ e+1` (`absU_le`).  The
extra `oms ~ jdist/M` factor is exactly what closes the cross-multiplication that
fails under the crude `|B0| ≤ 2`.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `xB_eq` — the EXACT `Q'` identity `x_k·B0 ≈ oms·(B_e′ + 2·U_e)`.
  * `xB_abs_le` / `c2_abs_le_tight` — `|x_k·B0| ≤ oms·Cbd(e)`, `|c2| ≤ δ·oms·Cbd(e)`.
  * `antisymmTarget_tight_AbsLeRat` — the retightened antisymmetric bound.
  * `antisymmQuot'_le_quarter` — the cross-multiplication `antisymmQuot' ≤ ¼·gradedRate`.
  * `eventualAntisymmRate` ⇒ `eventualRadLegRemainder` — closes the radical leg.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide`/`ac_rfl` only on
closed/`Nat`-AC goals.  Axiom-gate at the foot.
-/

import YMGap.Continuum.ChebOrthoRadLegProof

set_option maxHeartbeats 4000000

namespace YMGap.Continuum.ChebOrthoBracketDecay

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.ChebOrthoGraded (jdist jdist_pos)
open YMGap.Continuum.ChebOrthoGradedClose (AbsLeRat)
open YMGap.Continuum.ChebOrthoCancelDiv
open YMGap.Continuum.ChebOrthoMidpointEst (isqrt isqrt_ge isqrt_sq_le isqrt_pos)
open YMGap.Continuum.ChebOrthoTightModulus
  (subSecondQuot_tight twoDeltaSq subSecondQuot_tight_le_recip twoDeltaSq_le)
open YMGap.Continuum.ChebOrthoRadLegProof

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 0. The boundary-decay value identity and bound -/

/-- The boundary-decay bracket constant `Cbd(e) = Bbound e + 2(e+1)`. -/
def Cbd (e : Nat) : Nat := ChebOrthoLegAssembly.Bbound e + 2 * (e + 1)

/-- **Abstract boundary-decay rearrangement.**  For rationals `oms x G Bd Uc` with
`oms ≈ 1 + (−x²)` and the bracket identity `(1+(−x²))·Bd + (−(x·G)) ≈ −((1+1)·((1+(−x²))·Uc))`,
we get `x·G ≈ oms·(Bd + (1+1)·Uc)`.  Pure `Q'`-ring. -/
theorem xB_eq_abstract (oms x G Bd Uc : Q')
    (homs : oms ≈ (1 + (-(x * x))))
    (hBid : ((1 + (-(x * x))) * Bd + (-(x * G)))
            ≈ (-(((1:Q') + 1) * ((1 + (-(x * x))) * Uc)))) :
    (x * G) ≈ (oms * (Bd + ((1:Q') + 1) * Uc)) := by
  have hstep : (x * G) ≈ ((1 + (-(x * x))) * Bd + ((1:Q') + 1) * ((1 + (-(x * x))) * Uc)) := by
    have h1 : ((1 + (-(x * x))) * Bd + (-(x * G))) + (x * G)
        ≈ (-(((1:Q') + 1) * ((1 + (-(x * x))) * Uc))) + (x * G) :=
      Q'.add_eqv_congr' hBid (Q'.eqv_refl _)
    have hL : ((1 + (-(x * x))) * Bd + (-(x * G))) + (x * G) ≈ ((1 + (-(x * x))) * Bd) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv (x * G))) ?_
      exact QPoly.q_add_zero_eqv _
    have h2 : ((1 + (-(x * x))) * Bd)
        ≈ ((-(((1:Q') + 1) * ((1 + (-(x * x))) * Uc))) + (x * G)) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm hL) h1
    have h3 : ((1 + (-(x * x))) * Bd) + (((1:Q') + 1) * ((1 + (-(x * x))) * Uc))
        ≈ ((-(((1:Q') + 1) * ((1 + (-(x * x))) * Uc))) + (x * G))
            + (((1:Q') + 1) * ((1 + (-(x * x))) * Uc)) :=
      Q'.add_eqv_congr' h2 (Q'.eqv_refl _)
    have hR : ((-(((1:Q') + 1) * ((1 + (-(x * x))) * Uc))) + (x * G))
            + (((1:Q') + 1) * ((1 + (-(x * x))) * Uc))
        ≈ (x * G) := by
      generalize hP : (((1:Q') + 1) * ((1 + (-(x * x))) * Uc)) = P
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv P (-P) (x * G))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.add_neg_self_eqv P) (Q'.eqv_refl (x * G))) ?_
      exact QPoly.q_zero_add_eqv _
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ h3 hR)
  refine Q'.eqv_trans _ _ _ hstep ?_
  -- (1+1)·(A·Uc) ≈ A·((1+1)·Uc)
  have hpull : (((1:Q') + 1) * ((1 + (-(x * x))) * Uc))
      ≈ ((1 + (-(x * x))) * (((1:Q') + 1) * Uc)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv ((1:Q')+1) (1 + (-(x * x))) Uc)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv ((1:Q')+1) (1 + (-(x * x))))) ?_
    exact Q'.mul_assoc_eqv (1 + (-(x * x))) ((1:Q')+1) Uc
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hpull) ?_
  -- A·Bd + A·((1+1)·Uc) ≈ A·(Bd + (1+1)·Uc) ≈ oms·(...)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv (1 + (-(x * x))) Bd (((1:Q')+1)*Uc))) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm homs)

/-- **The EXACT boundary-decay identity** at the node, instantiating `xB_eq_abstract`. -/
theorem xB_eq (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    (xk M hM k * B0 e he M hM k)
      ≈ (oneMinusSqNode M k hM hk
          * (ChebOrthoWeightedFTC.Bderiv e he (xk M hM k)
              + ((1:Q') + 1) * Cheb.U e (xk M hM k))) :=
  xB_eq_abstract (oneMinusSqNode M k hM hk) (xk M hM k)
    (ChebOrthoOffDiag.Gbracket e he (xk M hM k))
    (ChebOrthoWeightedFTC.Bderiv e he (xk M hM k))
    (Cheb.U e (xk M hM k))
    (ChebOrthoLeadingModel.oms_eq_oneSubSq M k hM hk)
    (ChebUDClosure.Bderiv_identity_uncond e he he2 (xk M hM k))

/-- **The boundary-decay value bound** `|x_k·B0| ≤ oms·Cbd(e)`, two-sided.
`x_k·B0 = oms·(B_e′ + 2·U_e)`, `|B_e′| ≤ Bbound e`, `|U_e| ≤ e+1`, `oms ≥ 0`. -/
theorem xB_abs_le (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    (xk M hM k * B0 e he M hM k) ≤ oneMinusSqNode M k hM hk * Q'.ofNat (Cbd e)
      ∧ (-(xk M hM k * B0 e he M hM k)) ≤ oneMinusSqNode M k hM hk * Q'.ofNat (Cbd e) := by
  -- box bounds on x
  have hx1 : xk M hM k ≤ (1 : Q') := RiemannSOS.node_hi M hM k hk
  have hxm1 : (-(1 : Q')) ≤ xk M hM k := RiemannSOS.node_lo M hM k
  -- |Bderiv| ≤ Bbound, |U| ≤ e+1
  obtain ⟨hBplo, hBphi⟩ := ChebOrthoLegAssembly.Bderiv_abs_le e he (xk M hM k) hx1 hxm1
  obtain ⟨hUhi, hUlo⟩ := ChebU.absU_le e (xk M hM k) hx1 hxm1
  -- inner factor V := Bderiv + (1+1)·U is two-sided bounded by ofNat (Cbd e)
  -- bound (1+1)·U two-sidedly by ofNat (2(e+1))
  have h2Uhi : (((1:Q')+1) * Cheb.U e (xk M hM k)) ≤ Q'.ofNat (2 * (e + 1)) := by
    -- (1+1)·U ≤ 2·ofNat(e+1) = ofNat(2(e+1))
    obtain ⟨_, hh⟩ := ChebOrthoLegAssembly.mul_abs_le
      (u := ((1:Q')+1)) (v := Cheb.U e (xk M hM k)) (B := ((1:Q')+1)) (d := Q'.ofNat (e + 1))
      (by decide) (ChebOrthoLegAssembly.ofNat_nonneg _)
      (by
        refine Q'.le_trans' _ (0:Q') _ ?_ (by decide)
        refine Q'.le_trans' _ (-(0:Q')) _ (Q'.neg_le_neg (by decide)) (Q'.le_of_eqv (by decide)))
      (Q'.le_refl' _) hUlo hUhi
    refine Q'.le_trans' _ _ _ hh (Q'.le_of_eqv ?_)
    -- (1+1)·ofNat(e+1) ≈ ofNat(2(e+1))
    show (((1:Q')+1) * Q'.ofNat (e + 1)).num * ((Q'.ofNat (2 * (e + 1))).den : Int)
        = (Q'.ofNat (2 * (e + 1))).num * ((((1:Q')+1) * Q'.ofNat (e + 1)).den : Int)
    rw [Q'.mul_den_cast,
      show (((1:Q')+1) * Q'.ofNat (e + 1)).num = ((1:Q')+1).num * (Q'.ofNat (e + 1)).num from rfl]
    have hn : ((1:Q')+1).num = 2 := by decide
    have hd : (((1:Q')+1).den : Int) = 1 := by decide
    have hcn : (Q'.ofNat (e + 1)).num = ((e + 1 : Nat) : Int) := rfl
    have hcd : ((Q'.ofNat (e + 1)).den : Int) = 1 := rfl
    have hon : (Q'.ofNat (2 * (e + 1))).num = ((2 * (e + 1) : Nat) : Int) := rfl
    have hod : ((Q'.ofNat (2 * (e + 1))).den : Int) = 1 := rfl
    rw [hn, hd, hcn, hcd, hon, hod]; push_cast; omega
  have h2Ulo : (-(((1:Q')+1) * Cheb.U e (xk M hM k))) ≤ Q'.ofNat (2 * (e + 1)) := by
    obtain ⟨hh, _⟩ := ChebOrthoLegAssembly.mul_abs_le
      (u := ((1:Q')+1)) (v := Cheb.U e (xk M hM k)) (B := ((1:Q')+1)) (d := Q'.ofNat (e + 1))
      (by decide) (ChebOrthoLegAssembly.ofNat_nonneg _)
      (by
        refine Q'.le_trans' _ (0:Q') _ ?_ (by decide)
        refine Q'.le_trans' _ (-(0:Q')) _ (Q'.neg_le_neg (by decide)) (Q'.le_of_eqv (by decide)))
      (Q'.le_refl' _) hUlo hUhi
    -- hh : −((1+1)·ofNat(e+1)) ≤ (1+1)·U  ⟹  −((1+1)·U) ≤ (1+1)·ofNat(e+1) ≈ ofNat(2(e+1))
    have hh' : (-(((1:Q')+1) * Cheb.U e (xk M hM k))) ≤ (((1:Q')+1) * Q'.ofNat (e + 1)) := by
      have := Q'.neg_le_neg hh
      refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv (Q'.neg_neg_eqv _))
    refine Q'.le_trans' _ _ _ hh' (Q'.le_of_eqv ?_)
    show (((1:Q')+1) * Q'.ofNat (e + 1)).num * ((Q'.ofNat (2 * (e + 1))).den : Int)
        = (Q'.ofNat (2 * (e + 1))).num * ((((1:Q')+1) * Q'.ofNat (e + 1)).den : Int)
    rw [Q'.mul_den_cast,
      show (((1:Q')+1) * Q'.ofNat (e + 1)).num = ((1:Q')+1).num * (Q'.ofNat (e + 1)).num from rfl]
    have hn : ((1:Q')+1).num = 2 := by decide
    have hd : (((1:Q')+1).den : Int) = 1 := by decide
    have hcn : (Q'.ofNat (e + 1)).num = ((e + 1 : Nat) : Int) := rfl
    have hcd : ((Q'.ofNat (e + 1)).den : Int) = 1 := rfl
    have hon : (Q'.ofNat (2 * (e + 1))).num = ((2 * (e + 1) : Nat) : Int) := rfl
    have hod : ((Q'.ofNat (2 * (e + 1))).den : Int) = 1 := rfl
    rw [hn, hd, hcn, hcd, hon, hod]; push_cast; omega
  -- V = ChebOrthoWeightedFTC.Bderiv e he (xk M hM k) + (1+1)·U is two-sided bounded by ofNat (Cbd e) = ofNat(Bbound e) + ofNat(2(e+1))
  have hVhi : (ChebOrthoWeightedFTC.Bderiv e he (xk M hM k) + ((1:Q')+1) * Cheb.U e (xk M hM k)) ≤ Q'.ofNat (Cbd e) := by
    have hsum := Q'.add_le_add hBphi h2Uhi
    refine Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)
    -- ofNat(Bbound) + ofNat(2(e+1)) ≈ ofNat(Cbd)
    show (Q'.ofNat (ChebOrthoLegAssembly.Bbound e) + Q'.ofNat (2 * (e + 1))).num
          * ((Q'.ofNat (Cbd e)).den : Int)
        = (Q'.ofNat (Cbd e)).num
          * ((Q'.ofNat (ChebOrthoLegAssembly.Bbound e) + Q'.ofNat (2 * (e + 1))).den : Int)
    rw [Q'.add_den_cast]
    have h1 : (Q'.ofNat (ChebOrthoLegAssembly.Bbound e) + Q'.ofNat (2 * (e + 1))).num
        = (ChebOrthoLegAssembly.Bbound e : Int) * 1 + (2 * (e + 1) : Nat) * 1 := rfl
    rw [h1]
    have hon : (Q'.ofNat (Cbd e)).num = ((Cbd e : Nat) : Int) := rfl
    have hod : ((Q'.ofNat (Cbd e)).den : Int) = 1 := rfl
    rw [hon, hod]
    show ((ChebOrthoLegAssembly.Bbound e : Int) * 1 + (2 * (e + 1) : Nat) * 1) * (1 : Int)
        = ((Cbd e : Nat) : Int) * (((1 : Nat) : Int) * ((1 : Nat) : Int))
    show _ = ((ChebOrthoLegAssembly.Bbound e + 2 * (e + 1) : Nat) : Int) * _
    push_cast; omega
  have hVlo : (-(ChebOrthoWeightedFTC.Bderiv e he (xk M hM k) + ((1:Q')+1) * Cheb.U e (xk M hM k))) ≤ Q'.ofNat (Cbd e) := by
    -- −(ChebOrthoWeightedFTC.Bderiv e he (xk M hM k) + 2U) = (−ChebOrthoWeightedFTC.Bderiv e he (xk M hM k)) + (−(2U)) ; both ≤ resp. bounds
    have hnBp : (-ChebOrthoWeightedFTC.Bderiv e he (xk M hM k)) ≤ Q'.ofNat (ChebOrthoLegAssembly.Bbound e) := by
      have := Q'.neg_le_neg hBplo
      refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv (Q'.neg_neg_eqv _))
    have hsum := Q'.add_le_add hnBp h2Ulo
    -- (−ChebOrthoWeightedFTC.Bderiv e he (xk M hM k)) + (−(2U)) ≈ −(ChebOrthoWeightedFTC.Bderiv e he (xk M hM k) + 2U)
    have hneg : (-(ChebOrthoWeightedFTC.Bderiv e he (xk M hM k) + ((1:Q')+1) * Cheb.U e (xk M hM k))) ≈ ((-ChebOrthoWeightedFTC.Bderiv e he (xk M hM k)) + (-(((1:Q')+1) * Cheb.U e (xk M hM k)))) :=
      Q'.neg_add_eqv (ChebOrthoWeightedFTC.Bderiv e he (xk M hM k)) (((1:Q')+1) * Cheb.U e (xk M hM k))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hneg) ?_
    refine Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)
    show (Q'.ofNat (ChebOrthoLegAssembly.Bbound e) + Q'.ofNat (2 * (e + 1))).num
          * ((Q'.ofNat (Cbd e)).den : Int)
        = (Q'.ofNat (Cbd e)).num
          * ((Q'.ofNat (ChebOrthoLegAssembly.Bbound e) + Q'.ofNat (2 * (e + 1))).den : Int)
    rw [Q'.add_den_cast]
    have h1 : (Q'.ofNat (ChebOrthoLegAssembly.Bbound e) + Q'.ofNat (2 * (e + 1))).num
        = (ChebOrthoLegAssembly.Bbound e : Int) * 1 + (2 * (e + 1) : Nat) * 1 := rfl
    rw [h1]
    have hon : (Q'.ofNat (Cbd e)).num = ((Cbd e : Nat) : Int) := rfl
    have hod : ((Q'.ofNat (Cbd e)).den : Int) = 1 := rfl
    rw [hon, hod]
    show ((ChebOrthoLegAssembly.Bbound e : Int) * 1 + (2 * (e + 1) : Nat) * 1) * (1 : Int)
        = ((Cbd e : Nat) : Int) * (((1 : Nat) : Int) * ((1 : Nat) : Int))
    show _ = ((ChebOrthoLegAssembly.Bbound e + 2 * (e + 1) : Nat) : Int) * _
    push_cast; omega
  -- oms ≥ 0
  have homs0 : (0 : Q') ≤ oneMinusSqNode M k hM hk :=
    Q'.le_of_lt (oneMinusSqNode_pos hM hk)
  have hCbd0 : (0 : Q') ≤ Q'.ofNat (Cbd e) := ChebOrthoLegAssembly.ofNat_nonneg _
  -- product bound:  −(oms·Cbd) ≤ oms·V ≤ oms·Cbd
  obtain ⟨hplo, hphi⟩ := ChebOrthoLegAssembly.mul_abs_le
    (u := oneMinusSqNode M k hM hk) (v := ChebOrthoWeightedFTC.Bderiv e he (xk M hM k) + ((1:Q')+1) * Cheb.U e (xk M hM k))
    (B := oneMinusSqNode M k hM hk) (d := Q'.ofNat (Cbd e))
    homs0 hCbd0
    (by
      refine Q'.le_trans' _ (0:Q') _ ?_ homs0
      refine Q'.le_trans' _ (-(0:Q')) _ (Q'.neg_le_neg homs0) (Q'.le_of_eqv (by decide)))
    (Q'.le_refl' _)
    (by
      -- −d ≤ v  from  hVlo : −v ≤ d
      have h1 := Q'.neg_le_neg hVlo
      exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
    hVhi
  -- transfer along xB_eq:  x·B0 ≈ oms·V
  have hxBeq := xB_eq e he he2 M hM k hk
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hxBeq) hphi
  · refine Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.ge_of_eqv hxBeq)) ?_
    -- −(oms·V) ≤ oms·Cbd
    have h1 : (-(oneMinusSqNode M k hM hk * (ChebOrthoWeightedFTC.Bderiv e he (xk M hM k) + ((1:Q')+1) * Cheb.U e (xk M hM k))))
        ≤ (-(-(oneMinusSqNode M k hM hk * Q'.ofNat (Cbd e)))) := Q'.neg_le_neg hplo
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv _))

/-! ## 0b. Integer-√ lower bound and reciprocal antitone (cross-mult helpers) -/

/-- `m < (isqrtAux fuel m + 1)²` whenever `m < (fuel+1)²`. -/
theorem isqrtAux_ub : ∀ (fuel m : Nat), m < (fuel + 1) * (fuel + 1)
    → m < (ChebOrthoMidpointEst.isqrtAux fuel m + 1) * (ChebOrthoMidpointEst.isqrtAux fuel m + 1) := by
  intro fuel
  induction fuel with
  | zero => intro m hm; simpa [ChebOrthoMidpointEst.isqrtAux] using hm
  | succ f ih =>
    intro m hm
    unfold ChebOrthoMidpointEst.isqrtAux
    by_cases h : (f + 1) * (f + 1) ≤ m
    · rw [if_pos h]; exact hm
    · rw [if_neg h]
      have : m < (f + 1) * (f + 1) := by omega
      exact ih m this

/-- **`m < (isqrt m + 1)²`** — the integer-√ strict upper companion to `isqrt_sq_le`. -/
theorem isqrt_ub (m : Nat) : m < (isqrt m + 1) * (isqrt m + 1) := by
  refine isqrtAux_ub m m ?_
  -- m < (m+1)²
  have : m ≤ m * m + 2 * m := by
    have : m ≤ m * m + m := by
      rcases Nat.eq_zero_or_pos m with h0 | hp
      · omega
      · have : m ≤ m * m := Nat.le_mul_of_pos_left m hp; omega
    omega
  have hexp : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  omega

/-- **`m ≤ 4·(isqrt m)²`** — the integer-√ LOWER bound (denominator direction). -/
theorem isqrt_lower (m : Nat) : m ≤ 4 * (isqrt m * isqrt m) := by
  have hub := isqrt_ub m
  -- (isqrt m + 1)² = isqrt² + 2·isqrt + 1 ≤ 4·isqrt²  when isqrt ≥ 1, else m = 0
  rcases Nat.eq_zero_or_pos (isqrt m) with h0 | hp
  · -- isqrt m = 0 ⟹ (from isqrt_ub) m < 1 ⟹ m = 0
    rw [h0] at hub; simp at hub; omega
  · have hexp : (isqrt m + 1) * (isqrt m + 1) = isqrt m * isqrt m + 2 * isqrt m + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    have h1 : 2 * isqrt m ≤ 2 * (isqrt m * isqrt m) := by
      have : isqrt m ≤ isqrt m * isqrt m := Nat.le_mul_of_pos_left _ hp
      omega
    have h2 : (1 : Nat) ≤ isqrt m * isqrt m := Nat.one_le_iff_ne_zero.mpr (by
      intro hc; rw [Nat.mul_eq_zero] at hc; omega)
    omega

/-- **`recipPos` is antitone**: `b ≤ a` (both `> 0`) ⟹ `recipPos a ≤ recipPos b`. -/
theorem recipPos_antitone {a b : Q'} (ha : (0:Q') < a) (hb : (0:Q') < b) (hba : b ≤ a) :
    Q'.recipPos a ha ≤ Q'.recipPos b hb := by
  show (Q'.recipPos a ha).num * ((Q'.recipPos b hb).den : Int)
      ≤ (Q'.recipPos b hb).num * ((Q'.recipPos a ha).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_den, Q'.recipPos_num, Q'.recipPos_den]
  -- a.den·b.num ≤ b.den·a.num  from  hba : b ≤ a (b.num·a.den ≤ a.num·b.den)
  have hh : b.num * (a.den : Int) ≤ a.num * (b.den : Int) := hba
  -- goal: (a.den)·b.num ≤ b.den·a.num
  have e1 : (a.den : Int) * b.num = b.num * (a.den : Int) := Int.mul_comm _ _
  have e2 : (b.den : Int) * a.num = a.num * (b.den : Int) := Int.mul_comm _ _
  rw [e1, e2]; exact hh

/-- **`omsNum M k ≤ 4·jdist·M`** (Int) — the key boundary cancellation:
`1 − x_k² = (2(M−k)−1)(2k+1)/M² ≲ 4·jdist/M`.  Factor `omsNum = (M−A)(M+A)`
(`A = 2k+1−M`), `M−A = 2(M−k)−1`, `M+A = 2k+1`, then `(M−k)(k+1) ≤ jdist·M`
(one factor is `jdist = min(k+1, M−k) ≤ M`, the other `≤ M`). -/
theorem omsNum_le (M k : Nat) (hk0 : 0 < k) (hkn : k < M) :
    omsNum M k ≤ 4 * (jdist M k : Int) * (M : Int) := by
  have hk' : (k : Int) < (M : Int) := by exact_mod_cast hkn
  have hfac : omsNum M k
      = ((M : Int) - (2 * (k : Int) + 1 - (M : Int)))
        * ((M : Int) + (2 * (k : Int) + 1 - (M : Int))) :=
    SemicircleIntegral.int_sq_diff_factor (M : Int) (2 * (k : Int) + 1 - (M : Int))
  -- M − A = 2M − 2k − 1, M + A = 2k + 1
  have hMA : (M : Int) - (2 * (k : Int) + 1 - (M : Int)) = 2 * (M : Int) - 2 * (k : Int) - 1 := by omega
  have hPA : (M : Int) + (2 * (k : Int) + 1 - (M : Int)) = 2 * (k : Int) + 1 := by omega
  rw [hMA, hPA] at hfac
  -- (2M−2k−1) ≤ 2·(M−k) and (2k+1) ≤ 2·(k+1), both nonneg ⟹ product ≤ 4·(M−k)·(k+1)
  -- then 4·(M−k)·(k+1) ≤ 4·jdist·M
  -- bound the product
  have h1 : (2 * (M : Int) - 2 * (k : Int) - 1) ≤ 2 * ((M : Int) - (k : Int)) := by omega
  have h1nn : (0 : Int) ≤ 2 * (M : Int) - 2 * (k : Int) - 1 := by omega
  have h2nn : (0 : Int) ≤ 2 * (k : Int) + 1 := by omega
  have hprod : (2 * (M : Int) - 2 * (k : Int) - 1) * (2 * (k : Int) + 1)
      ≤ (2 * ((M : Int) - (k : Int))) * (2 * ((k : Int) + 1)) := by
    refine Int.le_trans (Int.mul_le_mul_of_nonneg_right h1 h2nn) ?_
    refine Int.mul_le_mul_of_nonneg_left ?_ (by omega)
    omega
  rw [hfac]
  refine Int.le_trans hprod ?_
  -- 4·(M−k)·(k+1) ≤ 4·jdist·M  ⟺  (M−k)·(k+1) ≤ jdist·M
  -- (2(M−k))·(2(k+1)) = 4·(M−k)·(k+1)
  have hrw : (2 * ((M : Int) - (k : Int))) * (2 * ((k : Int) + 1))
      = 4 * (((M : Int) - (k : Int)) * ((k : Int) + 1)) := by
    generalize ((M : Int) - (k : Int)) = X
    generalize ((k : Int) + 1) = Y
    -- (2X)*(2Y) = 2*(X*(2*Y)) = 2*((X*2)*Y) = 2*((2*X)*Y) = 2*(2*(X*Y)) = (2*2)*(X*Y) = 4*(X*Y)
    calc (2 * X) * (2 * Y)
        = 2 * (X * (2 * Y)) := Int.mul_assoc 2 X (2 * Y)
      _ = 2 * ((X * 2) * Y) := by rw [Int.mul_assoc]
      _ = 2 * ((2 * X) * Y) := by rw [Int.mul_comm X 2]
      _ = 2 * (2 * (X * Y)) := by rw [Int.mul_assoc]
      _ = (2 * 2) * (X * Y) := (Int.mul_assoc 2 2 (X * Y)).symm
      _ = 4 * (X * Y) := congrArg (· * (X * Y)) (by decide)
  rw [hrw]
  -- 4·((M−k)(k+1)) ≤ 4·jdist·M  ⟸  (M−k)(k+1) ≤ jdist·M
  have hkey : ((M : Int) - (k : Int)) * ((k : Int) + 1) ≤ (jdist M k : Int) * (M : Int) := by
    rcases Nat.le_total (k + 1) (M - k) with hle | hle
    · -- jdist = k+1
      have hj : jdist M k = k + 1 := by
        show Nat.min (k + 1) (M - k) = k + 1; exact Nat.min_eq_left hle
      rw [hj]
      have hMk : ((M : Int) - (k : Int)) ≤ (M : Int) := by omega
      have hcast : (((k + 1 : Nat)) : Int) = (k : Int) + 1 := by push_cast; rfl
      rw [hcast, Int.mul_comm ((k:Int)+1) (M:Int)]
      exact Int.mul_le_mul_of_nonneg_right hMk (by omega)
    · -- jdist = M−k
      have hj : jdist M k = M - k := by
        show Nat.min (k + 1) (M - k) = M - k; exact Nat.min_eq_right hle
      rw [hj]
      have hcast : (((M - k : Nat)) : Int) = (M : Int) - (k : Int) := by
        have hkM : k ≤ M := by omega
        omega
      rw [hcast]
      have hkM : (k : Int) + 1 ≤ (M : Int) := by omega
      exact Int.mul_le_mul_of_nonneg_left hkM (by omega)
  -- multiply by 4
  have h4 : (0 : Int) ≤ 4 := by omega
  refine Int.le_trans (Int.mul_le_mul_of_nonneg_left hkey h4) ?_
  -- 4·(jdist·M) = 4·jdist·M
  rw [← Int.mul_assoc]
  exact Int.le_refl _

/-! ## 1. The TIGHT scalar bound `|c2| ≤ δ·oms·Cbd` -/

/-- The tight scalar value bound `c2Bd = δ·(oms·Cbd(e))`. -/
def c2Bd (e : Nat) (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) : Q' :=
  ChebOrthoLegProof.delta M hM * (oneMinusSqNode M k hM hk * Q'.ofNat (Cbd e))

theorem c2Bd_nonneg (e : Nat) (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    (0 : Q') ≤ c2Bd e M hM k hk := by
  refine Q'.mul_nonneg _ _ ?_ ?_
  · show (0 : Q') ≤ Q'.mkPos 1 M hM; rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
  · exact Q'.mul_nonneg _ _ (Q'.le_of_lt (oneMinusSqNode_pos hM hk)) (ChebOrthoLegAssembly.ofNat_nonneg _)

/-- **The TIGHT scalar bound** `|c2| ≤ δ·oms·Cbd(e)`.  `c2 = δ·(x_k·B0)`,
`|x_k·B0| ≤ oms·Cbd(e)` (`xB_abs_le`), `δ ≥ 0`. -/
theorem c2_abs_le_tight (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    c2 e he M hM k ≤ c2Bd e M hM k hk ∧ (-(c2 e he M hM k)) ≤ c2Bd e M hM k hk := by
  obtain ⟨hhi, hlo⟩ := xB_abs_le e he he2 M hM k hk
  have hd0 : (0 : Q') ≤ ChebOrthoLegProof.delta M hM := by
    show (0 : Q') ≤ Q'.mkPos 1 M hM; rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
  have hoc0 : (0 : Q') ≤ oneMinusSqNode M k hM hk * Q'.ofNat (Cbd e) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (oneMinusSqNode_pos hM hk)) (ChebOrthoLegAssembly.ofNat_nonneg _)
  -- −d ≤ x_k·B0  from  hlo : −(x_k·B0) ≤ d
  have hlo' : (-(oneMinusSqNode M k hM hk * Q'.ofNat (Cbd e))) ≤ (xk M hM k * B0 e he M hM k) := by
    have h1 := Q'.neg_le_neg hlo
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  obtain ⟨hclo, hchi⟩ := ChebOrthoLegAssembly.mul_abs_le
    (u := ChebOrthoLegProof.delta M hM) (v := xk M hM k * B0 e he M hM k)
    (B := ChebOrthoLegProof.delta M hM) (d := oneMinusSqNode M k hM hk * Q'.ofNat (Cbd e))
    hd0 hoc0
    (by
      refine Q'.le_trans' _ (0:Q') _ ?_ hd0
      refine Q'.le_trans' _ (-(0:Q')) _ (Q'.neg_le_neg hd0) (Q'.le_of_eqv (by decide)))
    (Q'.le_refl' _) hlo' hhi
  -- c2 = δ·(x_k·B0)  (definitional), c2Bd = δ·(oms·Cbd)
  refine ⟨?_, ?_⟩
  · exact hchi
  · -- −c2 = −(δ·(x_k·B0)) ≤ δ·(oms·Cbd) = c2Bd  from hclo
    show (-(ChebOrthoLegProof.delta M hM * (xk M hM k * B0 e he M hM k))) ≤ c2Bd e M hM k hk
    have h1 : (-(ChebOrthoLegProof.delta M hM * (xk M hM k * B0 e he M hM k)))
        ≤ (-(-(ChebOrthoLegProof.delta M hM * (oneMinusSqNode M k hM hk * Q'.ofNat (Cbd e))))) :=
      Q'.neg_le_neg hclo
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv _))

/-- **`c2Bd ≤ mkPos (4·Cbd·j) (M·M)`** — the boundary-decay scalar majorant
`δ·oms·Cbd ≤ 4·Cbd·j/M²` via `omsNum ≤ 4jM`.  `c2Bd` num `= omsNum·Cbd`, den `= M³`. -/
theorem c2Bd_le (e : Nat) (M : Nat) (hM : 0 < M) (k : Nat) (hk0 : 0 < k) (hkn : k < M) :
    c2Bd e M hM k hkn
      ≤ Q'.mkPos (4 * (Cbd e : Int) * (jdist M k : Int)) (M * M) (Nat.mul_pos hM hM) := by
  -- c2Bd num = omsNum·Cbd, den = M·(M·M)
  have hc2num : (c2Bd e M hM k hkn).num = omsNum M k * (Cbd e : Int) := by
    show (ChebOrthoLegProof.delta M hM
        * (oneMinusSqNode M k hM hkn * Q'.ofNat (Cbd e))).num = _
    show (ChebOrthoLegProof.delta M hM).num
        * ((oneMinusSqNode M k hM hkn).num * (Q'.ofNat (Cbd e)).num) = _
    show (Q'.mkPos 1 M hM).num
        * ((Q'.mkPos (omsNum M k) (omsDen M) (omsDen_pos hM)).num * (Cbd e : Int)) = _
    rw [Q'.mkPos_num, Q'.mkPos_num, Int.one_mul]
  have hc2den : ((c2Bd e M hM k hkn).den : Int) = (M : Int) * ((M : Int) * (M : Int)) := by
    show ((ChebOrthoLegProof.delta M hM
        * (oneMinusSqNode M k hM hkn * Q'.ofNat (Cbd e))).den : Int) = _
    rw [Q'.mul_den_cast, Q'.mul_den_cast]
    show ((Q'.mkPos 1 M hM).den : Int)
        * (((Q'.mkPos (omsNum M k) (omsDen M) (omsDen_pos hM)).den : Int) * ((Q'.ofNat (Cbd e)).den : Int)) = _
    rw [Q'.mkPos_den, Q'.mkPos_den]
    show (M : Int) * (((omsDen M : Nat) : Int) * 1) = _
    have homsden : ((omsDen M : Nat) : Int) = (M : Int) * (M : Int) := by
      show (((M * M : Nat)) : Int) = _; push_cast; rfl
    rw [homsden, Int.mul_one]
  -- cross-mult:  c2Bd.num · target.den ≤ target.num · c2Bd.den
  show (c2Bd e M hM k hkn).num
        * ((Q'.mkPos (4 * (Cbd e : Int) * (jdist M k : Int)) (M * M) (Nat.mul_pos hM hM)).den : Int)
      ≤ (Q'.mkPos (4 * (Cbd e : Int) * (jdist M k : Int)) (M * M) (Nat.mul_pos hM hM)).num
        * ((c2Bd e M hM k hkn).den : Int)
  rw [hc2num, hc2den, Q'.mkPos_num, Q'.mkPos_den]
  have hMMcast : ((M * M : Nat) : Int) = (M : Int) * (M : Int) := by push_cast; rfl
  rw [hMMcast]
  -- (omsNum·Cbd)·(M·M) ≤ (4·Cbd·j)·(M·(M·M))
  have homs := omsNum_le M k hk0 hkn
  -- omsNum·Cbd ≤ (4·j·M)·Cbd
  have hCbd0 : (0 : Int) ≤ (Cbd e : Int) := Int.natCast_nonneg _
  have hMM0 : (0 : Int) ≤ (M : Int) * (M : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hstep1 : omsNum M k * (Cbd e : Int) ≤ (4 * (jdist M k : Int) * (M : Int)) * (Cbd e : Int) :=
    Int.mul_le_mul_of_nonneg_right homs hCbd0
  have hstep2 : (omsNum M k * (Cbd e : Int)) * ((M : Int) * (M : Int))
      ≤ ((4 * (jdist M k : Int) * (M : Int)) * (Cbd e : Int)) * ((M : Int) * (M : Int)) :=
    Int.mul_le_mul_of_nonneg_right hstep1 hMM0
  refine Int.le_trans hstep2 ?_
  -- ((4·j·M)·Cbd)·(M·M) = (4·Cbd·j)·(M·(M·M))  : Nat AC after casting
  have h4cast : (4 : Int) = ((4 : Nat) : Int) := by decide
  have hLfold : ((4 * (jdist M k : Int) * (M : Int)) * (Cbd e : Int)) * ((M : Int) * (M : Int))
      = (((4 * jdist M k * M) * Cbd e * (M * M) : Nat) : Int) := by
    rw [h4cast, ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul,
        ← Int.natCast_mul]
  have hRfold : (4 * (Cbd e : Int) * (jdist M k : Int)) * ((M : Int) * ((M : Int) * (M : Int)))
      = (((4 * Cbd e * jdist M k) * (M * (M * M)) : Nat) : Int) := by
    rw [h4cast, ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul,
        ← Int.natCast_mul]
  rw [hLfold, hRfold]
  have hnat : (4 * jdist M k * M) * Cbd e * (M * M) = (4 * Cbd e * jdist M k) * (M * (M * M)) := by
    ac_rfl
  rw [hnat]; exact Int.le_refl _

/-! ## 2. The retightened antisymmetric bound -/

/-- The retightened antisymmetric quotient `antisymmQuot' = (c2Bd · symmQuot_sqrt) · (1/antisymmL)`. -/
def antisymmQuot' (e : Nat) (M k : Nat) (hM : 0 < M) (hkn : k < M) (hj : 2 ≤ jdist M k) : Q' :=
  (c2Bd e M hM k hkn * symmQuot_sqrt M k hM hkn)
    * Q'.recipPos (antisymmL M k hM) (antisymmL_pos M k hM hkn hj)

theorem antisymmQuot'_nonneg (e : Nat) (M k : Nat) (hM : 0 < M) (hkn : k < M) (hj : 2 ≤ jdist M k) :
    (0 : Q') ≤ antisymmQuot' e M k hM hkn hj := by
  refine Q'.mul_nonneg _ _ ?_ (Q'.le_of_lt (Q'.recipPos_pos _ _))
  exact Q'.mul_nonneg _ _ (c2Bd_nonneg e M hM k hkn) (symmQuot_sqrt_nonneg M k hM hkn)

/-- **THE RETIGHTENED ANTISYMMETRIC SECOND-DIFFERENCE BOUND.**  Mirrors
`antisymmSecondDiff_AbsLeRat` with `c2Abs → c2Bd` (the boundary-decay numerator
`|c2| ≤ δ·oms·Cbd`).  Via `div_of_mul_ge` with the EXACT numerator reduction
`antisymm_numer`, the tight bound `c2_abs_le_tight`, `symmSecondDiff_sqrt_AbsLeRat`,
and `antisymmS_lower`. -/
theorem antisymmTarget_tight_AbsLeRat (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) :
    AbsLeRat (antisymmTarget e he M hM k hkn) (antisymmQuot' e M k hM hkn hj) := by
  obtain ⟨hc2hi, hc2lo⟩ := c2_abs_le_tight e he he2 M hM k hkn
  have hsymm : AbsLeRat (ChebOrthoTightModulus.symmD M hM k) (symmQuot_sqrt M k hM hkn) :=
    symmSecondDiff_sqrt_AbsLeRat M hM k hk0 hkn hk1n
  have hnumK : AbsLeRat (CReal.mul (CReal.ofQ' (c2 e he M hM k)) (ChebOrthoTightModulus.symmD M hM k))
      (c2Bd e M hM k hkn * symmQuot_sqrt M k hM hkn) :=
    ChebOrthoLegProof.AbsLeRat.ofQ'_smul hsymm hc2hi hc2lo (c2Bd_nonneg e M hM k hkn)
      (symmQuot_sqrt_nonneg M k hM hkn)
  have hDSK : AbsLeRat (CReal.mul (antisymmTarget e he M hM k hkn) (antisymmS M hM k))
      (c2Bd e M hM k hkn * symmQuot_sqrt M k hM hkn) :=
    ChebOrthoCancelDiv.AbsLeRat.of_equiv (antisymm_numer e he M hM k hk0 hkn hk1n) hnumK
  refine ChebOrthoCancelDiv.AbsLeRat.div_of_mul_ge
    (D := antisymmTarget e he M hM k hkn) (S := antisymmS M hM k)
    (K := c2Bd e M hM k hkn * symmQuot_sqrt M k hM hkn)
    (L := antisymmL M k hM)
    (KL := antisymmQuot' e M k hM hkn hj)
    hDSK
    (antisymmS_lower M hM k hk0 hkn hj)
    (antisymmL_pos M k hM hkn hj)
    (antisymmQuot'_nonneg e M k hM hkn hj)
    ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (c2Bd e M hM k hkn * symmQuot_sqrt M k hM hkn)
      (Q'.recipPos (antisymmL M k hM) (antisymmL_pos M k hM hkn hj))
      (antisymmL M k hM)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (Q'.mul_recipPos_eqv (antisymmL M k hM) (antisymmL_pos M k hM hkn hj)))) ?_
  exact Q'.mul_one_eqv _

/-! ## 3. The cross-multiplication `antisymmQuot' ≤ ¼·gradedRate` -/

/-- `K = 2·subSecondQuot_tight + 2δ² ≤ mkPos 22 (M·j)`. -/
theorem K_le (M : Nat) (hM : 0 < M) (k : Nat) (hkn : k < M) (hk1n : k + 1 < M) :
    ((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
      ≤ Q'.mkPos 22 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn)) := by
  have hsub := subSecondQuot_tight_le_recip M hM k hkn hk1n
  have htwo := twoDeltaSq_le M k hM hkn
  -- 2·subSecondQuot ≤ mkPos 10(Mj)+mkPos10(Mj) ≈ mkPos 20 (Mj)
  have hsum2 : (subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn)
      ≤ (Q'.mkPos 10 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))
          + Q'.mkPos 10 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))) :=
    Q'.add_le_add hsub hsub
  have hsum3 : ((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
      ≤ ((Q'.mkPos 10 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))
          + Q'.mkPos 10 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn)))
        + Q'.mkPos 2 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))) :=
    Q'.add_le_add hsum2 htwo
  refine Q'.le_trans' _ _ _ hsum3 (Q'.le_of_eqv ?_)
  -- (mkPos10 + mkPos10) + mkPos2 ≈ mkPos 20 + mkPos 2 ≈ mkPos 22
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (SemicircleIntegral.mkPos_add_same_den 10 10 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn)))) ?_
  refine Q'.eqv_trans _ _ _
    (SemicircleIntegral.mkPos_add_same_den 20 2 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))) ?_
  -- mkPos (20+2) (Mj) = mkPos 22 (Mj)
  exact Q'.eqv_refl _

/-- `mkPos (isqrt(jM)) M ≤ twoOmsSqrtLb` (with equality: both have value `isqrt(jM)/M`). -/
theorem isqrtOverM_le_twoOmsSqrtLb (M k : Nat) (hM : 0 < M) (hkn : k < M) :
    Q'.mkPos (isqrt (jdist M k * M) : Int) M hM ≤ twoOmsSqrtLb M k hM := by
  -- twoOmsSqrtLb = omsSqrtLb + omsSqrtLb, omsSqrtLb = mkPos (isqrt(jM)) (2M)
  show (Q'.mkPos (isqrt (jdist M k * M) : Int) M hM).num * ((twoOmsSqrtLb M k hM).den : Int)
      ≤ (twoOmsSqrtLb M k hM).num * ((Q'.mkPos (isqrt (jdist M k * M) : Int) M hM).den : Int)
  have hTn : (twoOmsSqrtLb M k hM).num
      = (isqrt (jdist M k * M) : Int) * ((2 * M : Nat) : Int)
        + (isqrt (jdist M k * M) : Int) * ((2 * M : Nat) : Int) := by
    show (omsSqrtLb M k hM + omsSqrtLb M k hM).num = _
    show (omsSqrtLb M k hM).num * ((omsSqrtLb M k hM).den : Int)
        + (omsSqrtLb M k hM).num * ((omsSqrtLb M k hM).den : Int) = _
    show (Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) _).num
          * ((Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) _).den : Int)
        + (Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) _).num
          * ((Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) _).den : Int) = _
    rw [Q'.mkPos_num, Q'.mkPos_den]
  have hTd : ((twoOmsSqrtLb M k hM).den : Int) = ((2 * M : Nat) : Int) * ((2 * M : Nat) : Int) := by
    show ((omsSqrtLb M k hM + omsSqrtLb M k hM).den : Int) = _
    rw [Q'.add_den_cast]
    show ((omsSqrtLb M k hM).den : Int) * ((omsSqrtLb M k hM).den : Int) = _
    show ((Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) _).den : Int)
        * ((Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) _).den : Int) = _
    rw [Q'.mkPos_den]
  rw [hTn, hTd, Q'.mkPos_num, Q'.mkPos_den]
  -- isqrt·((2M)·(2M)) ≤ (isqrt·(2M) + isqrt·(2M))·M  : equality, via generic Int AC helper
  generalize (isqrt (jdist M k * M) : Int) = s
  have h2Mc : ((2 * M : Nat) : Int) = 2 * (M : Int) := by push_cast; rfl
  rw [h2Mc]
  generalize (M : Int) = m
  -- s*(2m*(2m)) = (s*(2m)+s*(2m))*m   (both = 4 s m²); prove equality then le_refl
  have heq : s * (2 * m * (2 * m)) = (s * (2 * m) + s * (2 * m)) * m := by
    -- RHS = (s*(2m))*m + (s*(2m))*m = s*((2m)*m) + s*((2m)*m) = s*((2m)*m + (2m)*m)
    rw [Int.add_mul, Int.mul_assoc s (2 * m) m, ← Int.mul_add s ((2 * m) * m) ((2 * m) * m)]
    refine congrArg (s * ·) ?_
    -- 2m*(2m) = (2m)*m + (2m)*m
    -- LHS: (2*m)*(2*m), second factor 2*m = m+m
    rw [show (2 * m : Int) * (2 * m) = (2 * m) * (m + m) from by rw [← Int.two_mul]]
    rw [Int.mul_add]
  rw [heq]; exact Int.le_refl _

/-- **`symmQuot_sqrt ≤ mkPos 22 (j·isqrt(jM))`** — the √-scale majorant
`~ 22/(j·√(jM))`.  `K ≤ 22/(Mj)`, `recipPos(2·omsSqrtLb) ≤ M/isqrt(jM)`. -/
theorem symmQuot_sqrt_le (M : Nat) (hM : 0 < M) (k : Nat) (hkn : k < M) (hk1n : k + 1 < M) :
    symmQuot_sqrt M k hM hkn
      ≤ Q'.mkPos 22 (jdist M k * isqrt (jdist M k * M))
          (Nat.mul_pos (jdist_pos hkn) (isqrt_pos (Nat.mul_pos (jdist_pos hkn) hM))) := by
  have hjM : 0 < jdist M k * M := Nat.mul_pos (jdist_pos hkn) hM
  have hisqM : 0 < isqrt (jdist M k * M) := isqrt_pos hjM
  have hmkpos : (0 : Q') < Q'.mkPos (isqrt (jdist M k * M) : Int) M hM := by
    show (0:Int) * _ < _ * (1:Int)
    rw [Int.zero_mul, Int.mul_one, Q'.mkPos_num]; exact_mod_cast hisqM
  -- recipPos(twoOmsSqrtLb) ≤ recipPos(mkPos (isqrt jM) M) = mkPos M (isqrt jM)
  have hrec : Q'.recipPos (twoOmsSqrtLb M k hM) (twoOmsSqrtLb_pos M k hM hkn)
      ≤ Q'.recipPos (Q'.mkPos (isqrt (jdist M k * M) : Int) M hM) hmkpos :=
    recipPos_antitone _ _ (isqrtOverM_le_twoOmsSqrtLb M k hM hkn)
  have hrecLe : Q'.recipPos (Q'.mkPos (isqrt (jdist M k * M) : Int) M hM) hmkpos
      ≤ Q'.mkPos (M : Int) (isqrt (jdist M k * M)) hisqM := by
    have hrn : (Q'.recipPos (Q'.mkPos (isqrt (jdist M k * M) : Int) M hM) hmkpos).num = (M : Int) := by
      rw [Q'.recipPos_num, Q'.mkPos_den]
    have hrd : ((Q'.recipPos (Q'.mkPos (isqrt (jdist M k * M) : Int) M hM) hmkpos).den : Int)
        = (isqrt (jdist M k * M) : Int) := by
      rw [Q'.recipPos_den, Q'.mkPos_num]
    show (Q'.recipPos (Q'.mkPos (isqrt (jdist M k * M) : Int) M hM) hmkpos).num
          * ((Q'.mkPos (M : Int) (isqrt (jdist M k * M)) hisqM).den : Int)
        ≤ (Q'.mkPos (M : Int) (isqrt (jdist M k * M)) hisqM).num
          * ((Q'.recipPos (Q'.mkPos (isqrt (jdist M k * M) : Int) M hM) hmkpos).den : Int)
    rw [hrn, hrd, Q'.mkPos_num, Q'.mkPos_den]
    -- M·(isqrt jM) ≤ M·(isqrt jM)
    have hc : ((isqrt (jdist M k * M) : Nat) : Int) = (isqrt (jdist M k * M) : Int) := rfl
    rw [hc]; exact Int.le_refl _
  -- symmQuot_sqrt = K · recipPos(twoOmsSqrtLb) ≤ mkPos 22(Mj) · mkPos M (isqrt jM)
  have hKnonneg : (0 : Q') ≤ Q'.mkPos 22 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn)) := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
  have hrecnonneg : (0 : Q') ≤ Q'.recipPos (twoOmsSqrtLb M k hM) (twoOmsSqrtLb_pos M k hM hkn) :=
    Q'.le_of_lt (Q'.recipPos_pos _ _)
  -- symmQuot_sqrt = K · recipPos
  show (((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
      * Q'.recipPos (twoOmsSqrtLb M k hM) (twoOmsSqrtLb_pos M k hM hkn))
      ≤ _
  -- bound K, then recip
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (K_le M hM k hkn hk1n) hrecnonneg) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hrec hKnonneg) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hrecLe hKnonneg) ?_
  -- mkPos 22(Mj) · mkPos M (isqrt jM) ≈ mkPos (22·M) (Mj·isqrt) ≤ mkPos 22 (j·isqrt)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ChebOrthoLegProof.mkPos_mul_mkPos 22 (M : Int) (M * jdist M k)
      (isqrt (jdist M k * M)) (Nat.mul_pos hM (jdist_pos hkn)) hisqM)) ?_
  -- mkPos (22·M) ((Mj)·isqrt) ≤ mkPos 22 (j·isqrt)  : cross-mult 22M·(j·isqrt) ≤ 22·((Mj)·isqrt)
  refine ChebOrthoLegProof.mkPos_le_mkPos _ _ ?_
  -- (22*M)·(j·isqrt) ≤ 22·((M*j)*isqrt)
  have hcast : (22 * (M : Int)) * ((jdist M k * isqrt (jdist M k * M) : Nat) : Int)
      = (22 : Int) * (((M * jdist M k) * isqrt (jdist M k * M) : Nat) : Int) := by
    rw [show (22 * (M : Int)) = (((22 * M : Nat)) : Int) from by rw [Int.natCast_mul]; rfl]
    rw [show ((jdist M k * isqrt (jdist M k * M) : Nat) : Int)
          = ((jdist M k : Nat) : Int) * ((isqrt (jdist M k * M) : Nat) : Int) from by rw [Int.natCast_mul]]
    rw [show (((M * jdist M k) * isqrt (jdist M k * M) : Nat) : Int)
          = (((M * jdist M k : Nat)) : Int) * ((isqrt (jdist M k * M) : Nat) : Int) from by rw [Int.natCast_mul]]
    rw [show (((M * jdist M k : Nat)) : Int) = (M : Int) * (jdist M k : Int) from by rw [Int.natCast_mul]]
    rw [show (((22 * M : Nat)) : Int) = (22 : Int) * (M : Int) from by rw [Int.natCast_mul]; rfl]
    -- (22*M)·(j·isqrt) = 22·((M*j)·isqrt)
    generalize (M : Int) = m
    generalize (jdist M k : Int) = j
    generalize ((isqrt (jdist M k * M) : Nat) : Int) = s
    -- (22*m)*(j*s) = 22*((m*j)*s)
    rw [Int.mul_assoc 22 m (j * s)]
    refine congrArg (22 * ·) ?_
    exact (Int.mul_assoc m j s).symm
  rw [hcast]; exact Int.le_refl _

/-- The radical-leg threshold `M0R e = (2816·Cbd e)²`. -/
def M0R (e : Nat) : Nat := (2816 * Cbd e) * (2816 * Cbd e)

/-- **The core Nat cross-multiplication.**  `704·Cbd·⌊√M⌋·j² ≤ cRateNum·a²·b`,
`a = ⌊√(jM)⌋`, `b = ⌊√(4(j−1)j)⌋`, for `M ≥ M0R e`, `j ≥ 2`.  Uses `jM ≤ 4a²`
(`isqrt_lower`), `j ≤ b` (`isqrt_ge`, `j² ≤ 4(j−1)j` ⟺ `4 ≤ 3j`), and the threshold
`2816·Cbd ≤ ⌊√M⌋`. -/
theorem keyNat (e M k : Nat) (hM : 0 < M) (hkn : k < M) (hj : 2 ≤ jdist M k) (hthr : M0R e ≤ M) :
    704 * Cbd e * isqrt M * (jdist M k * jdist M k)
      ≤ ChebOrthoMidpointCore.cRateNum e
        * (isqrt (jdist M k * M) * isqrt (jdist M k * M))
        * isqrt (4 * (jdist M k - 1) * jdist M k) := by
  have hjpos : 0 < jdist M k := jdist_pos hkn
  -- b ≥ j
  have hb : jdist M k ≤ isqrt (4 * (jdist M k - 1) * jdist M k) := by
    refine isqrt_ge ?_
    -- j² ≤ 4(j−1)j  ⟺  j ≤ 4(j−1)  (j>0)  ⟺  4 ≤ 3j (j≥2)
    have : jdist M k * jdist M k ≤ 4 * (jdist M k - 1) * jdist M k := by
      refine Nat.mul_le_mul_right _ ?_
      -- j ≤ 4·(j−1)  for j ≥ 2
      omega
    exact this
  -- jM ≤ 4·a²
  have ha : jdist M k * M ≤ 4 * (isqrt (jdist M k * M) * isqrt (jdist M k * M)) :=
    isqrt_lower (jdist M k * M)
  -- isqrt M ≥ 2816·Cbd
  have hisM : 2816 * Cbd e ≤ isqrt M := by
    refine isqrt_ge ?_
    have : M0R e = (2816 * Cbd e) * (2816 * Cbd e) := rfl
    omega
  have hsqM : isqrt M * isqrt M ≤ M := isqrt_sq_le M
  have hcn1 : 1 ≤ ChebOrthoMidpointCore.cRateNum e := by
    unfold ChebOrthoMidpointCore.cRateNum; omega
  -- (1)  cRateNum·M ≥ 2816·Cbd·isqrt M
  have step1 : 2816 * Cbd e * isqrt M ≤ ChebOrthoMidpointCore.cRateNum e * M := by
    have h1 : 2816 * Cbd e * isqrt M ≤ isqrt M * isqrt M := Nat.mul_le_mul_right _ hisM
    have h2 : isqrt M * isqrt M ≤ M := hsqM
    have h3 : M ≤ ChebOrthoMidpointCore.cRateNum e * M := by
      calc M = 1 * M := (Nat.one_mul _).symm
        _ ≤ ChebOrthoMidpointCore.cRateNum e * M := Nat.mul_le_mul_right _ hcn1
    exact Nat.le_trans (Nat.le_trans h1 h2) h3
  -- (2)  cRateNum·jM ≥ 2816·Cbd·isqrt M·j   (·j)
  have step2 : (2816 * Cbd e * isqrt M) * jdist M k ≤ (ChebOrthoMidpointCore.cRateNum e * M) * jdist M k :=
    Nat.mul_le_mul_right _ step1
  -- (3)  cRateNum·(4a²) ≥ cRateNum·jM
  have step3 : ChebOrthoMidpointCore.cRateNum e * (jdist M k * M)
      ≤ ChebOrthoMidpointCore.cRateNum e * (4 * (isqrt (jdist M k * M) * isqrt (jdist M k * M))) :=
    Nat.mul_le_mul_left _ ha
  -- combine (2)+(3):  2816·Cbd·isqrt M·j ≤ cRateNum·jM ≤ cRateNum·4a²
  -- first rearrange (2) RHS = cRateNum·(M·j) = cRateNum·(j·M)
  have step2' : (2816 * Cbd e * isqrt M) * jdist M k ≤ ChebOrthoMidpointCore.cRateNum e * (jdist M k * M) := by
    refine Nat.le_trans step2 ?_
    have heq : (ChebOrthoMidpointCore.cRateNum e * M) * jdist M k
        = ChebOrthoMidpointCore.cRateNum e * (jdist M k * M) := by ac_rfl
    rw [heq]; exact Nat.le_refl _
  have step4 : (2816 * Cbd e * isqrt M) * jdist M k
      ≤ ChebOrthoMidpointCore.cRateNum e * (4 * (isqrt (jdist M k * M) * isqrt (jdist M k * M))) :=
    Nat.le_trans step2' step3
  -- step4:  2816·Cbd·isqrt M·j ≤ cRateNum·(4·a²)
  -- (·j):  (2816·Cbd·isqrt M·j)·j ≤ (cRateNum·(4·a²))·j
  have step5 : ((2816 * Cbd e * isqrt M) * jdist M k) * jdist M k
      ≤ (ChebOrthoMidpointCore.cRateNum e * (4 * (isqrt (jdist M k * M) * isqrt (jdist M k * M)))) * jdist M k :=
    Nat.mul_le_mul_right _ step4
  -- replace the final ·j by ·b (b ≥ j)
  have step6 : (ChebOrthoMidpointCore.cRateNum e * (4 * (isqrt (jdist M k * M) * isqrt (jdist M k * M)))) * jdist M k
      ≤ (ChebOrthoMidpointCore.cRateNum e * (4 * (isqrt (jdist M k * M) * isqrt (jdist M k * M)))) * isqrt (4 * (jdist M k - 1) * jdist M k) :=
    Nat.mul_le_mul_left _ hb
  -- so:  2816·Cbd·isqrt M·j² ≤ cRateNum·(4·a²)·b = 4·(cRateNum·a²·b) ; divide by 4
  have hmain : 4 * (704 * Cbd e * isqrt M * (jdist M k * jdist M k))
      ≤ 4 * (ChebOrthoMidpointCore.cRateNum e
            * (isqrt (jdist M k * M) * isqrt (jdist M k * M))
            * isqrt (4 * (jdist M k - 1) * jdist M k)) := by
    have hL : 4 * (704 * Cbd e * isqrt M * (jdist M k * jdist M k))
        = ((2816 * Cbd e * isqrt M) * jdist M k) * jdist M k := by ac_rfl
    have hR : 4 * (ChebOrthoMidpointCore.cRateNum e
            * (isqrt (jdist M k * M) * isqrt (jdist M k * M))
            * isqrt (4 * (jdist M k - 1) * jdist M k))
        = (ChebOrthoMidpointCore.cRateNum e * (4 * (isqrt (jdist M k * M) * isqrt (jdist M k * M)))) * isqrt (4 * (jdist M k - 1) * jdist M k) := by ac_rfl
    rw [hL, hR]
    exact Nat.le_trans step5 step6
  exact Nat.le_of_mul_le_mul_left hmain (by omega)

/-- `mkPos (a·b) (2M²) ≤ antisymmL` (equality: `antisymmL = omsSqrtLb·recipWitness`). -/
theorem lbAntisymmL_le (M k : Nat) (hM : 0 < M) (hkn : k < M) :
    Q'.mkPos ((isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
        (2 * M * M) (Nat.mul_pos (Nat.mul_pos (by decide : (0:Nat) < 2) hM) hM)
      ≤ antisymmL M k hM := by
  -- antisymmL = omsSqrtLb · recipWitness
  have hAn : (antisymmL M k hM).num
      = (isqrt (jdist M k * M) : Int) * ((isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) := by
    show (omsSqrtLb M k hM * ChebOrthoInterior.recipWitness M (jdist M k) hM).num = _
    show (omsSqrtLb M k hM).num * (ChebOrthoInterior.recipWitness M (jdist M k) hM).num = _
    show (Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) _).num
        * (Q'.mkPos ((isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) M hM).num = _
    rw [Q'.mkPos_num, Q'.mkPos_num]
  have hAd : ((antisymmL M k hM).den : Int) = ((2 * M : Nat) : Int) * (M : Int) := by
    show ((omsSqrtLb M k hM * ChebOrthoInterior.recipWitness M (jdist M k) hM).den : Int) = _
    rw [Q'.mul_den_cast]
    show ((omsSqrtLb M k hM).den : Int) * ((ChebOrthoInterior.recipWitness M (jdist M k) hM).den : Int) = _
    show ((Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) _).den : Int)
        * ((Q'.mkPos ((isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) M hM).den : Int) = _
    rw [Q'.mkPos_den, Q'.mkPos_den]
  show (Q'.mkPos ((isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
          (2 * M * M) _).num * ((antisymmL M k hM).den : Int)
      ≤ (antisymmL M k hM).num
        * ((Q'.mkPos ((isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
            (2 * M * M) _).den : Int)
  rw [hAn, hAd, Q'.mkPos_num, Q'.mkPos_den]
  -- (a·b)·((2M)·M) ≤ (a·b')·((2M·M))  : equality
  have hcastL : ((isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
      = (isqrt (jdist M k * M) : Int) * ((isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) := by
    rw [Int.natCast_mul]
  have h2Mc : ((2 * M : Nat) : Int) = 2 * (M : Int) := by push_cast; rfl
  have h2MMc : ((2 * M * M : Nat) : Int) = 2 * (M : Int) * (M : Int) := by push_cast; rfl
  rw [hcastL, h2Mc, h2MMc]
  -- (a·b)·(2M·M) ≤ (a·b)·(2M·M)
  generalize (isqrt (jdist M k * M) : Int) = a
  generalize ((isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) = b
  generalize (M : Int) = m
  -- (a*b)*(2m*m) ≤ (a*b)*(2*m*m)
  have : (2 * m * m) = 2 * m * m := rfl
  exact Int.le_refl _

/-- **`recipPos(antisymmL) ≤ mkPos (2M²) (a·b)`** — `a·b = isqrt(jM)·isqrt(4(j−1)j)`. -/
theorem recipAntisymmL_le (M k : Nat) (hM : 0 < M) (hkn : k < M) (hj : 2 ≤ jdist M k) :
    Q'.recipPos (antisymmL M k hM) (antisymmL_pos M k hM hkn hj)
      ≤ Q'.mkPos (2 * M * M : Int)
          (isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k))
          (Nat.mul_pos (isqrt_pos (Nat.mul_pos (jdist_pos hkn) hM))
            (isqrt_pos (by
              have hjpos := jdist_pos hkn
              have : 0 < 4 * (jdist M k - 1) * jdist M k := by
                have : 0 < jdist M k - 1 := by omega
                exact Nat.mul_pos (Nat.mul_pos (by omega) this) hjpos
              exact this))) := by
  have habpos : 0 < isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k) :=
    Nat.mul_pos (isqrt_pos (Nat.mul_pos (jdist_pos hkn) hM))
      (isqrt_pos (by
        have hjpos := jdist_pos hkn
        have : 0 < jdist M k - 1 := by omega
        exact Nat.mul_pos (Nat.mul_pos (by omega) this) hjpos))
  have hlbpos : (0 : Q') < Q'.mkPos
      ((isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
      (2 * M * M) (Nat.mul_pos (Nat.mul_pos (by decide : (0:Nat) < 2) hM) hM) := by
    show (0:Int) * _ < _ * (1:Int)
    rw [Int.zero_mul, Int.mul_one, Q'.mkPos_num]; exact_mod_cast habpos
  -- recipPos(antisymmL) ≤ recipPos(lb)
  have hanti := recipPos_antitone (antisymmL_pos M k hM hkn hj) hlbpos (lbAntisymmL_le M k hM hkn)
  refine Q'.le_trans' _ _ _ hanti ?_
  -- recipPos(mkPos (a·b) (2M²)) ≤ mkPos (2M²) (a·b)
  have hrn : (Q'.recipPos (Q'.mkPos ((isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
        (2 * M * M) (Nat.mul_pos (Nat.mul_pos (by decide : (0:Nat) < 2) hM) hM)) hlbpos).num = ((2 * M * M : Nat) : Int) := by
    rw [Q'.recipPos_num, Q'.mkPos_den]
  have hrd : ((Q'.recipPos (Q'.mkPos ((isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
        (2 * M * M) (Nat.mul_pos (Nat.mul_pos (by decide : (0:Nat) < 2) hM) hM)) hlbpos).den : Int)
      = ((isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) := by
    rw [Q'.recipPos_den, Q'.mkPos_num]
  show (Q'.recipPos (Q'.mkPos _ (2 * M * M) (Nat.mul_pos (Nat.mul_pos (by decide : (0:Nat) < 2) hM) hM)) hlbpos).num
        * ((Q'.mkPos (2 * M * M : Int) _ _).den : Int)
      ≤ (Q'.mkPos (2 * M * M : Int) _ _).num
        * ((Q'.recipPos (Q'.mkPos _ (2 * M * M) (Nat.mul_pos (Nat.mul_pos (by decide : (0:Nat) < 2) hM) hM)) hlbpos).den : Int)
  rw [hrn, hrd, Q'.mkPos_num, Q'.mkPos_den]
  -- (2M²)·(a·b) ≤ (2M²)·(a·b)   (note 2*M*M cast vs literal)
  have h2MMc : ((2 * M * M : Nat) : Int) = 2 * (M : Int) * (M : Int) := by push_cast; rfl
  rw [h2MMc]
  exact Int.le_refl _

/-- **THE CROSS-MULTIPLICATION** `antisymmQuot' ≤ ¼·gradedRate` for `M ≥ M0R e`.
Bounds each factor by its clean √-scale mkPos majorant (`c2Bd_le`, `symmQuot_sqrt_le`,
`recipAntisymmL_le`), folds the product to a single mkPos, and discharges the residual
Nat inequality `704·Cbd·⌊√M⌋·j² ≤ cRateNum·a²·b` (`keyNat`) — the boundary-decay factor
`oms ~ j/M` is what makes this hold near the boundary. -/
theorem antisymmQuot'_le_quarter (e M k : Nat) (hM : 0 < M) (hk0 : 0 < k) (hkn : k < M)
    (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) (hthr : M0R e ≤ M) :
    antisymmQuot' e M k hM hkn hj
      ≤ ChebOrthoLegProof.quarter * ChebOrthoGraded.gradedRate e M hM k := by
  have hjpos : 0 < jdist M k := jdist_pos hkn
  have hjMpos : 0 < jdist M k * M := Nat.mul_pos hjpos hM
  have haPos : 0 < isqrt (jdist M k * M) := isqrt_pos hjMpos
  have hbPos : 0 < isqrt (4 * (jdist M k - 1) * jdist M k) :=
    isqrt_pos (by
      have : 0 < jdist M k - 1 := by omega
      exact Nat.mul_pos (Nat.mul_pos (by omega) this) hjpos)
  have hc2nn := c2Bd_nonneg e M hM k hkn
  have hsqnn := symmQuot_sqrt_nonneg M k hM hkn
  have hrecnn : (0 : Q') ≤ Q'.recipPos (antisymmL M k hM) (antisymmL_pos M k hM hkn hj) :=
    Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hcbarnn : (0 : Q') ≤ Q'.mkPos (4 * (Cbd e : Int) * (jdist M k : Int)) (M * M) (Nat.mul_pos hM hM) := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    exact Int.mul_nonneg (Int.mul_nonneg (by decide) (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
  -- (1)  c2Bd·symmQuot_sqrt ≤ cbar·sbar
  have h1 : c2Bd e M hM k hkn * symmQuot_sqrt M k hM hkn
      ≤ Q'.mkPos (4 * (Cbd e : Int) * (jdist M k : Int)) (M * M) (Nat.mul_pos hM hM)
        * Q'.mkPos 22 (jdist M k * isqrt (jdist M k * M)) (Nat.mul_pos hjpos haPos) := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (c2Bd_le e M hM k hk0 hkn) hsqnn) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (symmQuot_sqrt_le M hM k hkn hk1n) hcbarnn
  -- (2)  (c2Bd·symmQuot_sqrt)·recipPos ≤ (cbar·sbar)·rbar
  have hcbarsbar_nn : (0 : Q')
      ≤ Q'.mkPos (4 * (Cbd e : Int) * (jdist M k : Int)) (M * M) (Nat.mul_pos hM hM)
        * Q'.mkPos 22 (jdist M k * isqrt (jdist M k * M)) (Nat.mul_pos hjpos haPos) := by
    refine Q'.mul_nonneg _ _ hcbarnn ?_
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
  have h2 : antisymmQuot' e M k hM hkn hj
      ≤ (Q'.mkPos (4 * (Cbd e : Int) * (jdist M k : Int)) (M * M) (Nat.mul_pos hM hM)
          * Q'.mkPos 22 (jdist M k * isqrt (jdist M k * M)) (Nat.mul_pos hjpos haPos))
        * Q'.mkPos (2 * M * M : Int)
            (isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k))
            (Nat.mul_pos haPos hbPos) := by
    show (c2Bd e M hM k hkn * symmQuot_sqrt M k hM hkn)
        * Q'.recipPos (antisymmL M k hM) (antisymmL_pos M k hM hkn hj) ≤ _
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h1 hrecnn) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (recipAntisymmL_le M k hM hkn hj) hcbarsbar_nn
  refine Q'.le_trans' _ _ _ h2 ?_
  -- fold (cbar·sbar)·rbar into one mkPos
  have hfold1 := ChebOrthoLegProof.mkPos_mul_mkPos (4 * (Cbd e : Int) * (jdist M k : Int)) 22
      (M * M) (jdist M k * isqrt (jdist M k * M)) (Nat.mul_pos hM hM) (Nat.mul_pos hjpos haPos)
  have hfold2 := ChebOrthoLegProof.mkPos_mul_mkPos
      ((4 * (Cbd e : Int) * (jdist M k : Int)) * 22) (2 * M * M : Int)
      ((M * M) * (jdist M k * isqrt (jdist M k * M)))
      (isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k))
      (Nat.mul_pos (Nat.mul_pos hM hM) (Nat.mul_pos hjpos haPos)) (Nat.mul_pos haPos hbPos)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hfold1) hfold2)) ?_
  -- ≤ ¼·gradedRate ≈ mkPos cRateNum (4·isqrt M·(j·j))
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (ChebOrthoLegProof.quarter_gradedRate_eqv e M k hM hkn))
  refine ChebOrthoLegProof.mkPos_le_mkPos _ _ ?_
  show ((4 * (Cbd e : Int) * (jdist M k : Int)) * 22) * (2 * M * M : Int)
        * ((4 * (ChebOrthoMidpointEst.isqrt M * (jdist M k * jdist M k)) : Nat) : Int)
      ≤ (ChebOrthoMidpointCore.cRateNum e : Int)
        * (((M * M) * (jdist M k * isqrt (jdist M k * M))
            * (isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k)) : Nat) : Int)
  have hLfold : ((4 * (Cbd e : Int) * (jdist M k : Int)) * 22) * (2 * M * M : Int)
        * ((4 * (ChebOrthoMidpointEst.isqrt M * (jdist M k * jdist M k)) : Nat) : Int)
      = (((4 * Cbd e * jdist M k) * 22 * (2 * M * M) * (4 * (isqrt M * (jdist M k * jdist M k))) : Nat) : Int) := by
    have h4 : (4 : Int) = ((4 : Nat) : Int) := by decide
    have h22 : (22 : Int) = ((22 : Nat) : Int) := by decide
    have h2c : (2 : Int) = ((2 : Nat) : Int) := by decide
    rw [h4, h22, h2c]
    rw [← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul,
        ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul]
  have hRfold : (ChebOrthoMidpointCore.cRateNum e : Int)
        * (((M * M) * (jdist M k * isqrt (jdist M k * M))
            * (isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k)) : Nat) : Int)
      = ((ChebOrthoMidpointCore.cRateNum e
            * ((M * M) * (jdist M k * isqrt (jdist M k * M))
              * (isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k))) : Nat) : Int) := by
    rw [← Int.natCast_mul]
  rw [hLfold, hRfold]
  refine Int.ofNat_le.mpr ?_
  have hkN := keyNat e M k hM hkn hj hthr
  have hLrw : (4 * Cbd e * jdist M k) * 22 * (2 * M * M) * (4 * (isqrt M * (jdist M k * jdist M k)))
      = (704 * Cbd e * isqrt M * (jdist M k * jdist M k)) * ((M * M) * jdist M k) := by ac_rfl
  have hRrw : ChebOrthoMidpointCore.cRateNum e
        * ((M * M) * (jdist M k * isqrt (jdist M k * M))
          * (isqrt (jdist M k * M) * isqrt (4 * (jdist M k - 1) * jdist M k)))
      = (ChebOrthoMidpointCore.cRateNum e
          * (isqrt (jdist M k * M) * isqrt (jdist M k * M))
          * isqrt (4 * (jdist M k - 1) * jdist M k)) * ((M * M) * jdist M k) := by ac_rfl
  rw [hLrw, hRrw]
  exact Nat.mul_le_mul_right _ hkN

/-! ## 4. The eventual antisymmetric rate and the closed radical leg -/

/-- **`EventualAntisymmRate e he`** — assembling `antisymmTarget_tight_AbsLeRat`
(boundary-decay numerator) with `antisymmQuot'_le_quarter`, witness `M0R e`. -/
theorem eventualAntisymmRate (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) :
    EventualAntisymmRate e he := by
  refine ⟨M0R e, fun N k hN hk1 hkN hk => ?_⟩
  have hM : 0 < N + 1 := Nat.succ_pos N
  have hk0 : 0 < k := hk1
  have hkn : k < N + 1 := hk
  have hk1n : k + 1 < N + 1 := by omega
  have hj : 2 ≤ jdist (N + 1) k := by
    show 2 ≤ Nat.min (k + 1) ((N + 1) - k)
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  exact ChebOrthoGradedClose.AbsLeRat.mono
    (antisymmTarget_tight_AbsLeRat e he he2 (N + 1) hM k hk0 hkn hk1n hj)
    (antisymmQuot'_le_quarter e (N + 1) k hM hk0 hkn hk1n hj hN)

/-- **THE RADICAL LEG IS CLOSED.**  `ChebOrthoLegAssembly.EventualRadLegRemainder e he`
for every even `e ≥ 2`, via the PROVED reduction `eventualRadLegRemainder_of_antisymmRate`
fed the now-PROVED `eventualAntisymmRate`. -/
theorem eventualRadLegRemainder (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) :
    ChebOrthoLegAssembly.EventualRadLegRemainder e he :=
  ChebOrthoRadLegProof.eventualRadLegRemainder_of_antisymmRate e he he2
    (eventualAntisymmRate e he he2)

end YMGap.Continuum.ChebOrthoBracketDecay

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.ChebOrthoBracketDecay.xB_eq
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.xB_abs_le
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.omsNum_le
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.c2_abs_le_tight
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.c2Bd_le
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.antisymmTarget_tight_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.isqrt_lower
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.recipPos_antitone
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.symmQuot_sqrt_le
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.keyNat
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.recipAntisymmL_le
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.antisymmQuot'_le_quarter
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.eventualAntisymmRate
#print axioms YMGap.Continuum.ChebOrthoBracketDecay.eventualRadLegRemainder
