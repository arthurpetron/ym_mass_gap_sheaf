/-
# P2′: torus RP, K → ∞ at EVERY rational β ≥ 0 (factorial Taylor tail; closed-inequality form)

**Label: Wilson-weight lattice scaffolding; also true for U(1); not gap evidence. No chart-closure claim.**
Additive. It extends `SU2TorusRPKTail` / `SU2TorusRPKCauchy`, which need strong coupling `2·256·β ≤ 1`, to all `β ≥ 0`.
It keeps the factorial `1/k!` in the Taylor coefficients, where those files used a geometric bound. Constructive:
explicit rational rates, an explicit decidable threshold `K₀(β)`, no `Classical`, no limit object.

With `u_k := a_k · 2^k · Lw^k = (β Lw)^k / k!` (`a_k = wilsonA β k = (β/2)^k/k!`):
* `u_succ`: `u_{k+1} = u_k · β Lw/(k+1)`; so `2 u_{m+1} ≤ u_m` once `2βLw ≤ m+1`.
* `ftsum_le`: `Σ_{i<j} u_{K+1+i} ≤ 2 u_{K+1}` for every `j`, as soon as `2βLw ≤ K+2`.
* **(a) `wtail_l1_factorial`**: `l1 (wtail x_p (wilsonA β) K j) ≤ 2·(β·256)^{K+1}·invFact(K+1)` for `2(β·256) ≤ K+2`.
* `l1_tk_all`: `l1 (T_K(U_p)) ≤ Λ(β) := 1 + Σ_{i<K₀} u_{i+1} + 2u_{K₀+1}` uniformly in `K`.
* **(b) `rpK_cauchy_all`**: `|rpB_{K+j} F G − rpB_K F G| ≤ l1(ΘF·G) · eb Λ (2u_{K+1}) |plaquettes|` for `K ≥ K₀`.
  `rpK_cauchy_all'` gives the full `RPKCauchy` predicate, with the crude rate `Λ` below `K₀`.
* **(c) `torus_rp_closed_all`, `torus_cs_closed_all`**: `SU2TorusRPKLimit.rp_closed` / `cs_closed` instantiated at
  the rates of (b). This gives RP and CS for the untruncated Wilson weight at every β, in closed-inequality form.

Scope: polynomial observables only (`PtSup`). General bounded observables would need Stone–Weierstrass, and that is not
ported. The rate is volume-dependent (`eb` grows with `|plaquettes|`). There is no CReal limit object and no site-seam
variant.
-/

import YMGap.Continuum.SU2TorusRPKCauchy

namespace YMGap.Continuum.SU2TorusRPKAllBeta

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly chiPow)
open YMGap.Continuum.SU2WilsonCoeffBounds (pow2)
open YMGap.Continuum.SU2WilsonActivity (wilsonA wilsonA_nonneg invS invS_pos half)
open YMGap.Continuum.SU2HaarL1Activity (l1 l1_nonneg l1_mul l1_add_le l1_smul)
open YMGap.Continuum.SU2TorusRPKTail (wtail wilsonPoly_add l1_chiPow l1_U_plaq mul_pow)
open YMGap.Continuum.SU2TorusRPKProd (eb haar_diff)
open YMGap.Continuum.SU2TorusRPCSShape (rpB PtSup)
open YMGap.Continuum.SU2TorusRPKLimit (RPKCauchy rp_closed cs_closed)
open YMGap.Continuum.SU2TorusRPKCauchy (xp tk_add)

local infix:50 " ≈ " => Q'.eqv
local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

/-! ## Factorial weights -/

/-- `1/k!`. -/
def invFact : Nat → Q'
  | 0 => 1
  | k + 1 => invFact k * invS k

theorem invFact_nonneg : ∀ k, (0 : Q') ≤ invFact k
  | 0 => by decide
  | k + 1 => Q'.mul_nonneg _ _ (invFact_nonneg k) (Q'.le_of_lt (invS_pos k))

theorem pow2_nonneg : ∀ k, (0 : Q') ≤ pow2 k
  | 0 => by decide
  | k + 1 => Q'.mul_nonneg _ _ (by decide) (pow2_nonneg k)

/-- `u_k = a_k · (2^k · Lw^k)`. -/
def u (β Lw : Q') (k : Nat) : Q' := wilsonA β k * (pow2 k * Lw ^ k)

variable {β Lw : Q'} (hβ : (0 : Q') ≤ β) (hL : (0 : Q') ≤ Lw)

include hβ hL in
theorem u_nonneg (k : Nat) : (0 : Q') ≤ u β Lw k :=
  Q'.mul_nonneg _ _ (wilsonA_nonneg hβ k) (Q'.mul_nonneg _ _ (pow2_nonneg k) (Q'.pow_nonneg _ hL k))

/-- `u_{k+1} = u_k · ((β Lw) · 1/(k+1))`. -/
theorem u_succ (k : Nat) : u β Lw (k + 1) ≈ u β Lw k * ((β * Lw) * invS k) := by
  let V := PolyExpr.var
  show (wilsonA β k * β * half * invS k) * ((2 * pow2 k) * (Lw * Lw ^ k)) ≈
    (wilsonA β k * (pow2 k * Lw ^ k)) * ((β * Lw) * invS k)
  have e : (wilsonA β k * β * half * invS k) * ((2 * pow2 k) * (Lw * Lw ^ k)) ≈
      ((wilsonA β k * (pow2 k * Lw ^ k)) * ((β * Lw) * invS k)) * (2 * half) :=
    poly_identity_of_normal_eq (V 0 * V 1 * V 2 * V 3 * (.const 2 * V 4 * (V 5 * V 6)))
      (V 0 * (V 4 * V 6) * (V 1 * V 5 * V 3) * (.const 2 * V 2)) (by decide)
      (fun | 0 => wilsonA β k | 1 => β | 2 => half | 3 => invS k | 4 => pow2 k | 5 => Lw | _ => Lw ^ k)
  exact Q'.eqv_trans _ _ _ e (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (by decide : (2 * half) ≈ 1))
    (Q'.mul_one_eqv _))

theorem ofNat_mul_invS (m : Nat) : (Q'.ofNat (m + 1) * invS m) ≈ 1 := by
  show (Q'.ofNat (m + 1) * invS m).num * ((1 : Q').den : Int) = (1 : Q').num * ((Q'.ofNat (m + 1) * invS m).den : Int)
  rw [Q'.mul_den_cast]
  show ((m + 1 : Nat) : Int) * 1 * 1 = 1 * (1 * ((m + 1 : Nat) : Int))
  rw [Int.mul_one, Int.mul_one, Int.one_mul, Int.one_mul]

theorem ofNat_le_ofNat {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  show (a : Int) * ((1 : Nat) : Int) ≤ (b : Int) * ((1 : Nat) : Int)
  exact Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr h) (Int.natCast_nonneg _)

include hβ hL in
/-- Ratio step: `2βLw ≤ m+1 ⟹ 2 u_{m+1} ≤ u_m`. -/
theorem u_ratio (m : Nat) (hm : 2 * (β * Lw) ≤ Q'.ofNat (m + 1)) : 2 * u β Lw (m + 1) ≤ u β Lw m := by
  let V := PolyExpr.var
  have hu := u_nonneg hβ hL m
  have hc : (2 * (β * Lw)) * invS m ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hm (Q'.le_of_lt (invS_pos m)))
      (Q'.le_of_eqv (ofNat_mul_invS m))
  have e : 2 * (u β Lw m * ((β * Lw) * invS m)) ≈ u β Lw m * ((2 * (β * Lw)) * invS m) :=
    poly_identity_of_normal_eq (.const 2 * (V 0 * (V 1 * V 2))) (V 0 * (.const 2 * V 1 * V 2)) (by decide)
      (fun | 0 => u β Lw m | 1 => β * Lw | _ => invS m)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (u_succ m))) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hc hu) (Q'.le_of_eqv (Q'.mul_one_eqv _))

/-! ## Factorial tail sums -/

/-- `Σ_{i<j} u_{K+1+i}`. -/
def ftsum (β Lw : Q') (K : Nat) : Nat → Q'
  | 0 => 0
  | j + 1 => ftsum β Lw K j + u β Lw (K + j + 1)

include hβ hL in
theorem ftsum_nonneg (K : Nat) : ∀ j, (0 : Q') ≤ ftsum β Lw K j
  | 0 => Q'.le_refl' 0
  | j + 1 => Q'.le_trans' _ _ _ (ftsum_nonneg K j) (Q'.add_le_self_of_nonneg _ _ (u_nonneg hβ hL _))

include hβ hL in
theorem ftsum_geo (K : Nat) (hK : 2 * (β * Lw) ≤ Q'.ofNat (K + 2)) :
    ∀ j, ftsum β Lw K j + 2 * u β Lw (K + j + 1) ≤ 2 * u β Lw (K + 1)
  | 0 => by
      show 0 + 2 * u β Lw (K + 0 + 1) ≤ 2 * u β Lw (K + 1)
      rw [Q'.zero_add']; exact Q'.le_refl' _
  | j + 1 => by
    let V := PolyExpr.var
    let t := u β Lw (K + j + 1)
    have hr : 2 * u β Lw (K + j + 1 + 1) ≤ t :=
      u_ratio hβ hL (K + j + 1) (Q'.le_trans' _ _ _ hK (ofNat_le_ofNat (by
        show K + 2 ≤ K + j + 1 + 1
        exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.le_add_right K j)))))
    have e2 : ftsum β Lw K j + (t + t) ≈ ftsum β Lw K j + 2 * t :=
      poly_identity_of_normal_eq (V 0 + (V 1 + V 1)) (V 0 + .const 2 * V 1) (by decide)
        (fun | 0 => ftsum β Lw K j | _ => t)
    have e1 : ftsum β Lw K (j + 1) + 2 * u β Lw (K + (j + 1) + 1) ≈
        ftsum β Lw K j + (t + 2 * u β Lw (K + j + 1 + 1)) :=
      Q'.add_assoc_eqv _ _ _
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (Q'.add_le_add_left _ _ _ hr)) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) (ftsum_geo K hK j)

include hβ hL in
theorem ftsum_le (K : Nat) (hK : 2 * (β * Lw) ≤ Q'.ofNat (K + 2)) (j : Nat) :
    ftsum β Lw K j ≤ 2 * u β Lw (K + 1) :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) (u_nonneg hβ hL _)))
    (ftsum_geo hβ hL K hK j)

/-- Splitting: `Σ_{i<K₀+d} u_{i+1} = Σ_{i<K₀} u_{i+1} + Σ_{i<d} u_{K₀+1+i}`. -/
theorem ftsum_split (K0 : Nat) : ∀ d, ftsum β Lw 0 (K0 + d) ≈ ftsum β Lw 0 K0 + ftsum β Lw K0 d
  | 0 => by
    show ftsum β Lw 0 K0 ≈ ftsum β Lw 0 K0 + 0
    rw [Q'.add_zero']; exact Q'.eqv_refl _
  | d + 1 => by
    show ftsum β Lw 0 (K0 + d) + u β Lw (0 + (K0 + d) + 1) ≈
      ftsum β Lw 0 K0 + (ftsum β Lw K0 d + u β Lw (K0 + d + 1))
    rw [Nat.zero_add]
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (ftsum_split K0 d)) (Q'.add_assoc_eqv _ _ _)

include hβ hL in
/-- Uniform bound `Σ_{i<K} u_{i+1} ≤ Σ_{i<K₀} u_{i+1} + 2u_{K₀+1}` for every `K`. -/
theorem ftsum_uniform (K0 : Nat) (hK0 : 2 * (β * Lw) ≤ Q'.ofNat (K0 + 2)) (K : Nat) :
    ftsum β Lw 0 K ≤ ftsum β Lw 0 K0 + 2 * u β Lw (K0 + 1) := by
  have h2u : (0 : Q') ≤ 2 * u β Lw (K0 + 1) := Q'.mul_nonneg _ _ (by decide) (u_nonneg hβ hL _)
  rcases Nat.le_total K K0 with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    refine Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (ftsum_nonneg hβ hL K d)) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (ftsum_split K d))) (Q'.add_le_self_of_nonneg _ _ h2u)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ftsum_split K0 d))
      (Q'.add_le_add_left _ _ _ (ftsum_le hβ hL K0 hK0 d))

/-! ## ℓ¹ bounds on the Taylor tail and the truncated weight -/

include hβ hL in
theorem l1_wtail_le_f (x : RatPoly) (hU : l1 (YMGap.Continuum.SU2CharacterSquareIdentity.U x 1) ≤ 2 * Lw) (K : Nat) :
    ∀ j, l1 (wtail x (wilsonA β) K j) ≤ ftsum β Lw K j
  | 0 => Q'.le_refl' 0
  | j + 1 => by
    let k := K + j + 1
    have ha := wilsonA_nonneg hβ k
    have hterm : l1 (polySmul (wilsonA β k) (chiPow x k)) ≤ u β Lw k := by
      refine Q'.le_trans' _ _ _ (l1_smul _ _) ?_
      rw [YMGap.Constructive.ExpNeg.abs_of_nonneg ha]
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ (l1_chiPow x hL hU k) ha
    exact Q'.le_trans' _ _ _ (l1_add_le _ _)
      (YMGap.Constructive.ExpNeg.add_le_add2 (l1_wtail_le_f x hU K j) hterm)

/-- `u_k = (β Lw)^k · 1/k!`. -/
theorem u_eq_pow_invFact : ∀ k, u β Lw k ≈ (β * Lw) ^ k * invFact k
  | 0 => by
      show (1 : Q') * (1 * 1) ≈ 1 * 1
      decide
  | k + 1 => by
    let V := PolyExpr.var
    refine Q'.eqv_trans _ _ _ (u_succ k) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (u_eq_pow_invFact k)) ?_
    show ((β * Lw) ^ k * invFact k) * ((β * Lw) * invS k) ≈ ((β * Lw) * (β * Lw) ^ k) * (invFact k * invS k)
    exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3)) (V 2 * V 0 * (V 1 * V 3)) (by decide)
      (fun | 0 => (β * Lw) ^ k | 1 => invFact k | 2 => β * Lw | _ => invS k)

/-- **(a) Factorial tail, every `β ≥ 0`:** `l1 (wtail) ≤ 2·(β·256)^{K+1}·invFact(K+1)` once `2(β·256) ≤ K+2`. -/
theorem wtail_l1_factorial {M : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K j : Nat)
    (hK : 2 * (β * Q'.ofNat 256) ≤ Q'.ofNat (K + 2)) (p : Z4Plaq) :
    l1 (wtail (xp M p) (wilsonA β) K j) ≤ 2 * ((β * Q'.ofNat 256) ^ (K + 1) * invFact (K + 1)) :=
  Q'.le_trans' _ _ _ (l1_wtail_le_f hβ (by decide) _ (l1_U_plaq _ _ p) K j)
    (Q'.le_trans' _ _ _ (ftsum_le hβ (by decide) K hK j)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (u_eq_pow_invFact (K + 1)))))

/-! ## Explicit threshold and uniform weight bound -/

/-- Canonical decidable threshold `K₀(β) := num(2·(β·256))` (for `β ≥ 0`). -/
def K0 (β : Q') : Nat := (2 * (β * Q'.ofNat 256)).num.toNat

theorem le_ofNat_num_toNat (q : Q') (hq : (0 : Q') ≤ q) : q ≤ Q'.ofNat q.num.toNat := by
  have hn : (0 : Int) ≤ q.num := (Q'.zero_le_iff_num_nonneg q).1 hq
  show q.num * ((1 : Nat) : Int) ≤ (q.num.toNat : Int) * (q.den : Int)
  rw [Int.toNat_of_nonneg hn]
  exact Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr (Q'.den_pos q)) hn

theorem K0_spec {β : Q'} (hβ : (0 : Q') ≤ β) : 2 * (β * Q'.ofNat 256) ≤ Q'.ofNat (K0 β + 2) :=
  Q'.le_trans' _ _ _ (le_ofNat_num_toNat _ (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hβ (by decide))))
    (ofNat_le_ofNat (Nat.le_add_right _ 2))

/-- Uniform per-plaquette bound `Λ(β) = 1 + Σ_{i<K₀} u_{i+1} + 2 u_{K₀+1}` (with `Lw = 256`). -/
def Λ (β : Q') : Q' := 1 + (ftsum β (Q'.ofNat 256) 0 (K0 β) + 2 * u β (Q'.ofNat 256) (K0 β + 1))

theorem Λ_nonneg {β : Q'} (hβ : (0 : Q') ≤ β) : (0 : Q') ≤ Λ β :=
  Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) (Q'.add_le_self_of_nonneg _ _
    (Q'.le_trans' _ _ _ (ftsum_nonneg hβ (by decide) 0 (K0 β))
      (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) (u_nonneg hβ (by decide) _)))))

variable {M : Nat} (hM : 1 ≤ M)

local notation "TKf" => YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks (2 * M)) (2 * M)

/-- `l1 (T_K(U_p)) ≤ Λ(β)` for every `K` and every `β ≥ 0`. -/
theorem l1_tk_all {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (p : Z4Plaq) : l1 (TKf β K p) ≤ Λ β := by
  have e : TKf β K p = TKf β (0 + K) p := by rw [Nat.zero_add]
  rw [e, tk_add]
  refine Q'.le_trans' _ _ _ (l1_add_le _ _) ?_
  have h0 : l1 (TKf β 0 p) ≤ 1 := by
    show l1 (polySmul 1 polyOne) ≤ 1
    decide
  have ht : l1 (wtail (xp M p) (wilsonA β) 0 K) ≤ ftsum β (Q'.ofNat 256) 0 (K0 β) + 2 * u β (Q'.ofNat 256) (K0 β + 1) :=
    Q'.le_trans' _ _ _ (l1_wtail_le_f hβ (by decide) _ (l1_U_plaq _ _ p) 0 K)
      (ftsum_uniform hβ (by decide) (K0 β) (K0_spec hβ) K)
  exact YMGap.Constructive.ExpNeg.add_le_add2 h0 ht

theorem le_zero_add (a : Q') : a ≤ 0 + a := by
  rw [Q'.zero_add']; exact Q'.le_refl' a

/-! ## (b) Cauchy rate at every β, (c) closed inequalities -/

/-- Tail rate `δ_K`: `2 u_{K+1}` from `K₀` on, the crude `Λ` below. -/
def δ (β : Q') (K : Nat) : Q' := if K0 β ≤ K then 2 * u β (Q'.ofNat 256) (K + 1) else Λ β

theorem δ_nonneg {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) : (0 : Q') ≤ δ β K := by
  unfold δ
  split
  · exact Q'.mul_nonneg _ _ (by decide) (u_nonneg hβ (by decide) _)
  · exact Λ_nonneg hβ

theorem l1_tail_δ {β : Q'} (hβ : (0 : Q') ≤ β) (K j : Nat) (p : Z4Plaq) :
    l1 (wtail (xp M p) (wilsonA β) K j) ≤ δ β K := by
  have hw := l1_wtail_le_f hβ (by decide) _ (l1_U_plaq (torusLinks (2 * M)) (2 * M) p) K j
  unfold δ
  split
  · rename_i h
    exact Q'.le_trans' _ _ _ hw (ftsum_le hβ (by decide) K (Q'.le_trans' _ _ _ (K0_spec hβ)
      (ofNat_le_ofNat (Nat.add_le_add_right h 2))) j)
  · -- crude: Σ_{i<j} u_{K+1+i} ≤ Σ_{i<K+j} u_{i+1} ≤ Λ
    have hs : ftsum β (Q'.ofNat 256) K j ≤ ftsum β (Q'.ofNat 256) 0 (K + j) :=
      Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (le_zero_add _)
        (Q'.add_le_add_right _ _ _ (ftsum_nonneg hβ (by decide) 0 K)))
        (Q'.le_of_eqv (Q'.eqv_symm (ftsum_split K j)))
    exact Q'.le_trans' _ _ _ hw (Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _
      (ftsum_uniform hβ (by decide) (K0 β) (K0_spec hβ) (K + j))
      (Q'.le_trans' _ _ _ (le_zero_add _)
        (Q'.add_le_add_right _ _ _ (by decide : (0 : Q') ≤ 1)))))

/-- **(b) `RPKCauchy` at every `β ≥ 0`** with rate `l1(ΘF·G) · eb Λ δ_K |plaquettes|`. The rate is
`2u_{K+1} = 2(256β)^{K+1}/(K+1)!` for `K ≥ K₀(β)`. -/
theorem rpK_cauchy_all' {β : Q'} (hβ : (0 : Q') ≤ β) (F G : RatPoly) :
    RPKCauchy hM β F G (fun K => l1 (polyMul (YMGap.Continuum.SU2TorusRPObs.thetaT hM F) G) *
      eb (Λ β) (δ β K) (torusPlaquettes (2 * M)).length) := fun K j => by
  have hprod : YMGap.Continuum.SU2HaarL1Activity.prodPoly (TKf β (K + j)) (torusPlaquettes (2 * M)) =
      YMGap.Continuum.SU2HaarL1Activity.prodPoly (fun q => polyAdd (TKf β K q) (wtail (xp M q) (wilsonA β) K j))
        (torusPlaquettes (2 * M)) := by
    rw [show TKf β (K + j) = fun q => polyAdd (TKf β K q) (wtail (xp M q) (wilsonA β) K j) from funext (tk_add K j)]
  show Q'.abs (YMGap.Continuum.BF4GeometricHaarMehlerProjection.quaternionHaar _
      (polyMul (polyMul (YMGap.Continuum.SU2TorusRPObs.thetaT hM F) G)
        (YMGap.Continuum.SU2HaarL1Activity.prodPoly (TKf β (K + j)) (torusPlaquettes (2 * M)))) + -_) ≤ _
  rw [hprod]
  exact haar_diff _ _ _ _ (Λ_nonneg hβ) (δ_nonneg hβ K) (l1_tk_all hβ K)
    (fun q => by rw [← tk_add]; exact l1_tk_all hβ (K + j) q) (l1_tail_δ hβ K j) _

/-- **(b), factorial form for `K ≥ K₀(β)`.** -/
theorem rpK_cauchy_all {β : Q'} (hβ : (0 : Q') ≤ β) (F G : RatPoly) (K j : Nat) (hK : K0 β ≤ K) :
    Q'.abs (rpB hM β (K + j) F G + -rpB hM β K F G) ≤
      l1 (polyMul (YMGap.Continuum.SU2TorusRPObs.thetaT hM F) G) *
        eb (Λ β) (2 * u β (Q'.ofNat 256) (K + 1)) (torusPlaquettes (2 * M)).length := by
  have h := rpK_cauchy_all' hM hβ F G K j
  unfold δ at h
  dsimp only at h
  rw [if_pos hK] at h
  exact h

/-- **(c) RP for the untruncated Wilson weight, every `β ≥ 0`, closed-inequality form.** If a rational `x` is
approximated by every truncation `rpB_K F F` within the rate `r K`, then `0 ≤ x + 2 r K` for all `K`. -/
theorem torus_rp_closed_all {β : Q'} (hβ : (0 : Q') ≤ β) {F : RatPoly} (hF : PtSup (M := M) F) {x : Q'}
    {r : Nat → Q'} (hr : ∀ K, (0 : Q') ≤ r K) (hx : ∀ K, Q'.abs (x + -rpB hM β K F F) ≤ r K) (K : Nat) :
    (0 : Q') ≤ (x + r K) + r K :=
  rp_closed hM hβ hF hr hx K

/-- **(c) CS for the untruncated Wilson weight, every `β ≥ 0`, closed-inequality form.** -/
theorem torus_cs_closed_all {β : Q'} (hβ : (0 : Q') ≤ β) {F G : RatPoly} (hF : PtSup (M := M) F)
    (hG : PtSup (M := M) G) {a b c : Q'} {r : Nat → Q'}
    (ha : ∀ K, Q'.abs (a * a + -(rpB hM β K F G * rpB hM β K F G)) ≤ r K)
    (hbc : ∀ K, Q'.abs (b * c + -(rpB hM β K F F * rpB hM β K G G)) ≤ r K) (K : Nat) :
    a * a ≤ (b * c + r K) + r K :=
  cs_closed hM hβ hF hG ha hbc K

end YMGap.Continuum.SU2TorusRPKAllBeta
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.invFact
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.invFact_nonneg
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.pow2_nonneg
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.u
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.u_nonneg
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.u_succ
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.ofNat_mul_invS
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.ofNat_le_ofNat
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.u_ratio
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.ftsum
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.ftsum_nonneg
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.ftsum_geo
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.ftsum_le
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.ftsum_split
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.ftsum_uniform
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.l1_wtail_le_f
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.u_eq_pow_invFact
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.wtail_l1_factorial
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.K0
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.le_ofNat_num_toNat
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.K0_spec
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.Λ
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.Λ_nonneg
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.l1_tk_all
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.le_zero_add
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.δ
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.δ_nonneg
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.l1_tail_δ
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.rpK_cauchy_all'
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.rpK_cauchy_all
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.torus_rp_closed_all
#print axioms YMGap.Continuum.SU2TorusRPKAllBeta.torus_cs_closed_all
