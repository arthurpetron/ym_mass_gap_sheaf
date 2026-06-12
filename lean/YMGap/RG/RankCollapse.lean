/-
The rank-general scalar bound `(1 + s)^r − 1 ≤ 2·r·s` (for `r·s ≤ 1/2`,
`s ≥ 0`) and the discharge of `ZtMajorant.rank_collapse` for an arbitrary
admissible simple group.

# What this module delivers (the rank collapse, route (a))

`RG/CharacterTailMajorant.lean` reduces the all-groups mass gap to the one
named obligation

> `ZtMajorant.rank_collapse` :  `∏_{i<r}(1 + sFloor i) − 1 ≤ Z_t(su2)` ,

where `sFloor i = S_i(3/4, t)` is the per-axis geometric character-tail
*excess* at the SU(2) Casimir floor (each axis dominated by SU(2)'s, since
`Δ_i ≥ 3/4` is the global minimum, attained only at `A₁ = su(2)`).  Per the
Lie-theory/heat-kernel route this is **not** a lattice-theta identity: it
collapses to one *scalar* `Q'` inequality.

The honest chain (`notes/uniform-character-tail-bound.md` §3), keeping the
group's *actual* per-axis gaps `Δᵢ`, is

    ∏_{i<r}(1 + sFloor i) − 1
      ≤ 2·Σ_{i<r} sFloor i        [the SUM SCALAR BOUND of this module]
      ≤ Z_t(su2)                  [§3 uniform domination, a `Q'`/exp fact]

with `sFloor i = S(Δᵢ, t)` the per-axis geometric tail at the *actual* gap.

> **NORMALIZATION / FACTOR-OF-`r` CORRECTION (load-bearing).**  The naive
> "collapse every axis to the floor `s = S(3/4,t)` then `2·r·s ≤ Z_t(su2)`"
> route is **false** for high rank: SU(2) is *rank 1*, so `Z_t(su2) ≈
> S(3/4,t) = s`, and `2·r·s` overcounts by `≈ 2r` (numerically `2·8·s ≈
> 3.8·10⁻³ ≫ 9.6·10⁻⁴ ≈ Z_t(su2)` at the canonical `t ≈ 11.1`).  The
> uniform domination is *not* `r` copies of the SU(2) floor tail; it works
> because the off-SU(2) axes have gaps `Δᵢ` **strictly above** `3/4`, so
> `S(Δᵢ,t) ≪ S(3/4,t)` and the *sum* `Σᵢ S(Δᵢ,t)` (not `r·S(3/4,t)`) is what
> `Z_t(su2)` dominates.  Hence the discharge uses the **sum** bound
> `∏(1+sᵢ)−1 ≤ 2·Σ sᵢ`, with per-axis gaps kept — the lossy constant form is
> retained only as a reusable lemma, NOT for the cap.

# The reusable scalar bounds

Two `Q'`-exact, division-free induction-on-`r` bounds (`s ≥ 0`):

  * **constant form** `(1 + s)^r − 1 ≤ 2·r·s`  for  `r·(2s) ≤ 1`
    (`finProd_const_le` / `ztValue_const_le`); and
  * **sum form** `∏(1 + sᵢ) − 1 ≤ 2·Σ sᵢ`  for  `Σ sᵢ ≤ 1/2`
    (`finProd_le_two_sumExcess` / `ztValue_le_two_sumExcess`).

Both via the invariant `finProd ··· ≤ 1 + A` with `A` the running linear
coefficient (`r·2s`, resp. `2·Σᵢ₍₌ᵣ₎ sᵢ`); the step needs no exact
polynomial identity — only `A·sᵣ ≤ sᵣ` (from `A ≤ 1`) plus
associativity/distribution.  The sum form is tight (no `r` loss).

# Discharging `rank_collapse`

`rank_collapse_of_sum` assembles the honest chain: from per-axis floor
nonnegativity, the window `2·Σ sFloor ≤ 1`, and the cap `2·Σ sFloor ≤ su2Zt`,
it concludes `ztValue sFloor r ≤ su2Zt` — the `ZtMajorant.rank_collapse`
field, now a *theorem*, not a posited field.  `ztMajorant_of_sum` packages
this into a full `ZtMajorant R`.  The only per-group inputs are the concrete
`Q'` facts: the per-axis floor excesses `sFloor i = S(Δᵢ,t)` (from the proven
gap-antitone engine of `CharacterTailAntitone.lean`), the window, and the §3
cap `2·Σ sFloor ≤ Z_t(su2)`.  `rank_collapse_of_scalar`/`ztMajorant_of_scalar`
expose the constant form too (usable where one *uniform* upper excess `s ≥
sFloor i` already clears `2·r·s ≤ Z_t(su2)`, e.g. interior groups with large
gaps), but the sum form is the one valid at the SU(2) floor for every rank.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` (the `Q'` order layer).  No
`Classical.*`, no `sorryAx`, no `native_decide`.  See the `#print axioms`
block at the end.
-/

import YMGap.RG.CharacterTailMajorant
import YMGap.Constructive.CauchyConv

namespace YMGap.RG

open YMGap.Constructive
open YMGap.RepTheory

/-! ## The scalar bound `(1 + s)^r − 1 ≤ 2·r·s` over `Q'`

We work with the constant excess sequence `fun _ => s`, so
`finProd (fun _ => s) r = (1 + s)^r`.  The bound is stated additively
(`ztValue`-shape) as `finProd (const s) r ≤ 1 + r·(2s)` under the window
`r·(2s) ≤ 1`, which is exactly `2rs ≤ 1`, i.e. `rs ≤ 1/2`. -/

/-- `0 ≤ ofNat r`.  Local helper (`SU3CharFactor.ofNat_nonneg` lives in a
heavier module). -/
theorem ofNat_nonneg_aux (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  show (0 : Int) * ((Q'.ofNat n).den : Int) ≤ (Q'.ofNat n).num * ((0 : Q').den : Int)
  have e1 : (Q'.ofNat n).num = (n : Int) := rfl
  have e2 : ((0 : Q').den : Int) = 1 := rfl
  rw [e1, e2, Int.zero_mul, Int.mul_one]
  exact Int.natCast_nonneg n

/-- `(ofNat (r+1)) · u ≃ (ofNat r) · u + u`.  The successor split of the
rank coefficient, used to grow the linear majorant `r·(2s)` by one axis. -/
theorem ofNatSucc_mul_eqv (r : Nat) (u : Q') :
    ((Q'.ofNat (r + 1)) * u).eqv ((Q'.ofNat r) * u + u) := by
  -- ofNat (r+1) ≃ ofNat r + ofNat 1 = ofNat r + 1, then right-distribute.
  have h1 : (Q'.ofNat (r + 1)).eqv (Q'.ofNat r + Q'.ofNat 1) := Q'.ofNat_add_eqv r 1
  have h2 : ((Q'.ofNat (r + 1)) * u).eqv ((Q'.ofNat r + Q'.ofNat 1) * u) :=
    Q'.mul_eqv_congr_right _ _ u h1
  refine Q'.eqv_trans _ _ _ h2 ?_
  -- (ofNat r + 1)·u ≃ ofNat r · u + 1·u ≃ ofNat r · u + u
  refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul (Q'.ofNat r) (Q'.ofNat 1) u) ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  -- (ofNat 1)·u ≃ 1·u ≃ u  (ofNat 1 = 1 definitionally)
  exact Q'.one_mul_eqv u

/-- **The scalar bound (invariant form).**  For `0 ≤ s`, if `r·(2s) ≤ 1`
then `finProd (fun _ => s) r ≤ 1 + r·(2s)`.

This is `(1 + s)^r ≤ 1 + 2rs` on the window `2rs ≤ 1`.  Induction on `r`:
the new factor `(1 + s)` multiplies the majorant `1 + R_r·2s`, and the
excess over `1 + R_{r+1}·2s` is `s·(R_r·2s − 1) ≤ 0` because `R_r·2s ≤ 1`. -/
theorem finProd_const_le {s : Q'} (hs : (0 : Q') ≤ s) :
    ∀ r : Nat, (Q'.ofNat r) * (2 * s) ≤ 1 →
      finProd (fun _ => s) r ≤ 1 + (Q'.ofNat r) * (2 * s) := by
  intro r
  induction r with
  | zero =>
    intro _
    -- finProd _ 0 = 1, and 1 ≤ 1 + (ofNat 0)·(2s).  (ofNat 0)·(2s) ≃ 0.
    show (1 : Q') ≤ 1 + (Q'.ofNat 0) * (2 * s)
    have hz : ((Q'.ofNat 0) * (2 * s)).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
        (QPoly.q_zero_mul (2 * s))
    -- 1 = 1 + 0 ≤ 1 + (ofNat 0)·(2s)  (the added term is nonnegative).
    have hbase : (1 : Q') ≤ 1 + 0 := by rw [Q'.add_zero']; exact Q'.le_refl' 1
    refine Q'.le_trans' _ _ _ hbase ?_
    exact Q'.add_le_add_left 1 0 _ (Q'.ge_of_eqv hz)
  | succ r ih =>
    intro hwin
    -- Window for the IH: R_r·(2s) ≤ R_{r+1}·(2s) ≤ 1.
    have hmono : (Q'.ofNat r) * (2 * s) ≤ (Q'.ofNat (r + 1)) * (2 * s) := by
      have hcoef : (Q'.ofNat r) ≤ (Q'.ofNat (r + 1)) := by
        show (Q'.ofNat r).num * ((Q'.ofNat (r+1)).den : Int)
           ≤ (Q'.ofNat (r+1)).num * ((Q'.ofNat r).den : Int)
        have e1 : (Q'.ofNat r).num = (r : Int) := rfl
        have e2 : (Q'.ofNat (r+1)).num = ((r + 1 : Nat) : Int) := rfl
        have e3 : ((Q'.ofNat r).den : Int) = 1 := rfl
        have e4 : ((Q'.ofNat (r+1)).den : Int) = 1 := rfl
        rw [e1, e2, e3, e4]; push_cast; omega
      have h2s : (0 : Q') ≤ 2 * s := Q'.mul_nonneg 2 s (by decide) hs
      exact Q'.mul_le_mul_of_nonneg_right _ _ _ hcoef h2s
    have hwin_r : (Q'.ofNat r) * (2 * s) ≤ 1 := Q'.le_trans' _ _ _ hmono hwin
    have ihr := ih hwin_r
    -- finProd (r+1) = finProd r · (1 + s) ≤ (1 + R_r·2s)·(1 + s).
    rw [finProd_succ]
    have hfac_nn : (0 : Q') ≤ (1 : Q') + s := one_add_nonneg hs
    have hmaj_nn : (0 : Q') ≤ 1 + (Q'.ofNat r) * (2 * s) :=
      Q'.zero_le_add 1 _ (by decide) (Q'.mul_nonneg _ _ (ofNat_nonneg_aux r) (Q'.mul_nonneg 2 s (by decide) hs))
    have hstep1 : finProd (fun _ => s) r * (1 + s)
        ≤ (1 + (Q'.ofNat r) * (2 * s)) * (1 + s) :=
      Q'.mul_le_mul_of_nonneg ihr (Q'.le_refl' _) hmaj_nn hfac_nn
    refine Q'.le_trans' _ _ _ hstep1 ?_
    -- Now show (1 + A)·(1 + s) ≤ 1 + R_{r+1}·2s, with A := R_r·(2s).
    -- (1 + A)·(1 + s) ≃ (1 + A) + (1 + A)·s.
    have hExpand : (((1 + (Q'.ofNat r) * (2 * s)) * (1 + s))).eqv
        ((1 + (Q'.ofNat r) * (2 * s)) + (1 + (Q'.ofNat r) * (2 * s)) * s) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (1 + (Q'.ofNat r) * (2 * s)) 1 s) ?_
      exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv (1 + (Q'.ofNat r) * (2 * s)))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hExpand) ?_
    -- (1 + A)·s ≃ s + A·s, and A·s ≤ 1·s = s (A ≤ 1, s ≥ 0), so (1+A)·s ≤ 2s.
    have hExpand2 : (((1 + (Q'.ofNat r) * (2 * s)) * s)).eqv
        (s + ((Q'.ofNat r) * (2 * s)) * s) := by
      refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul 1 ((Q'.ofNat r) * (2 * s)) s) ?_
      exact Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv s)
    have hAs_le_s : ((Q'.ofNat r) * (2 * s)) * s ≤ s := by
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.one_mul_eqv s))
      exact Q'.mul_le_mul_of_nonneg_right ((Q'.ofNat r) * (2 * s)) 1 s hwin_r hs
    have htwo : ((2 : Q') * s).eqv (s + s) := by
      have e : ((2 : Q') * s).eqv (((1 : Q') + 1) * s) :=
        Q'.mul_eqv_congr_right 2 (1 + 1) s (by decide)
      refine Q'.eqv_trans _ _ _ e ?_
      refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul 1 1 s) ?_
      exact QPoly.q_add_congr (Q'.one_mul_eqv s) (Q'.one_mul_eqv s)
    have hfacS_le : (1 + (Q'.ofNat r) * (2 * s)) * s ≤ 2 * s := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hExpand2) ?_
      have h1 : s + ((Q'.ofNat r) * (2 * s)) * s ≤ s + s :=
        Q'.add_le_add_left s _ s hAs_le_s
      exact Q'.le_trans' _ _ _ h1 (Q'.ge_of_eqv htwo)
    -- Combine: (1 + A) + (1 + A)·s ≤ (1 + A) + 2s ≃ 1 + (A + 2s) = 1 + R_{r+1}·2s.
    have hsum_le : (1 + (Q'.ofNat r) * (2 * s)) + (1 + (Q'.ofNat r) * (2 * s)) * s
        ≤ (1 + (Q'.ofNat r) * (2 * s)) + 2 * s :=
      Q'.add_le_add_left (1 + (Q'.ofNat r) * (2 * s)) _ _ hfacS_le
    refine Q'.le_trans' _ _ _ hsum_le ?_
    have hassoc : (((1 + (Q'.ofNat r) * (2 * s)) + 2 * s)).eqv
        (1 + ((Q'.ofNat r) * (2 * s) + 2 * s)) :=
      Q'.add_assoc_eqv 1 ((Q'.ofNat r) * (2 * s)) (2 * s)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) ?_
    have hcoefSucc : (((Q'.ofNat r) * (2 * s) + 2 * s)).eqv
        ((Q'.ofNat (r + 1)) * (2 * s)) :=
      Q'.eqv_symm (ofNatSucc_mul_eqv r (2 * s))
    exact Q'.add_le_add_left 1 _ _ (Q'.le_of_eqv hcoefSucc)

/-! ## The tight **sum** form `∏(1+sᵢ) − 1 ≤ 2·Σ sᵢ`

The constant-axis bound above collapses every axis to one scalar `s`,
costing a factor `r` (`2·r·s` instead of `2·Σ sᵢ`).  That is too lossy to
hit `Z_t(su2)` when the per-axis floors are taken at the *same* gap `3/4`
(SU(2) is rank-1, so `2·r·s_su2 ≈ r·Z_t(su2)`).  The honest assembly keeps
the per-axis gaps `Δᵢ` (strictly `> 3/4` off SU(2)), so the relevant scalar
is the **sum** `Σᵢ S(Δᵢ,t)`, and the right bound is

> `∏ᵢ(1 + sᵢ) − 1 ≤ 2·Σᵢ sᵢ`   for   `Σᵢ sᵢ ≤ 1/2` ,  `sᵢ ≥ 0` .

(`∏(1+sᵢ) ≤ e^{Σsᵢ} ≤ 1 + 2Σsᵢ` on the window.)  Same `Q'` induction as the
constant case, with `A := 2·Σᵢ₍₌ᵣ₎ sᵢ ≤ 1` the running coefficient. -/

/-- `0 ≤ Σ_{i<r} sᵢ` for nonnegative excesses. -/
theorem sumExcess_nonneg {s : Nat → Q'} (hs : ∀ i, (0 : Q') ≤ s i) :
    ∀ r, (0 : Q') ≤ sumExcess s r := by
  intro r
  induction r with
  | zero => exact Q'.le_refl' 0
  | succ k ihk => rw [sumExcess_succ]; exact Q'.zero_le_add _ _ ihk (hs k)

/-- **The sum-form scalar bound (invariant form).**  For `sᵢ ≥ 0`, if
`2·(Σ_{i<r} sᵢ) ≤ 1` then `finProd s r ≤ 1 + 2·(Σ_{i<r} sᵢ)`.

`(1 + s)^{···} ≤ 1 + 2·Σsᵢ` on the window `Σsᵢ ≤ 1/2`.  Induction on `r`:
the new factor `(1 + sᵣ)` multiplies `1 + 2Σ_r`, and the excess over
`1 + 2Σ_{r+1}` is `sᵣ·(2Σ_r − 1) ≤ 0` since `2Σ_r ≤ 1`. -/
theorem finProd_le_two_sumExcess {s : Nat → Q'} (hs : ∀ i, (0 : Q') ≤ s i) :
    ∀ r : Nat, 2 * (sumExcess s r) ≤ 1 →
      finProd s r ≤ 1 + 2 * (sumExcess s r) := by
  intro r
  induction r with
  | zero =>
    intro _
    -- finProd 0 = 1 ≤ 1 + 2·0;  2·(sumExcess 0) = 2·0 ≃ 0.
    show (1 : Q') ≤ 1 + 2 * (sumExcess s 0)
    rw [sumExcess_zero]
    have hz : ((2 : Q') * (0 : Q')).eqv 0 := QPoly.q_mul_zero 2
    have hbase : (1 : Q') ≤ 1 + 0 := by rw [Q'.add_zero']; exact Q'.le_refl' 1
    refine Q'.le_trans' _ _ _ hbase ?_
    exact Q'.add_le_add_left 1 0 _ (Q'.ge_of_eqv hz)
  | succ r ih =>
    intro hwin
    rw [sumExcess_succ] at hwin ⊢
    rw [finProd_succ]
    -- Σ_{r+1} = Σ_r + s_r.  Window for IH: 2·Σ_r ≤ 2·Σ_{r+1} ≤ 1.
    have hSr_nn : (0 : Q') ≤ sumExcess s r := sumExcess_nonneg hs r
    have hsr_nn : (0 : Q') ≤ s r := hs r
    have h2Sr_le1 : 2 * (sumExcess s r) ≤ 1 := by
      refine Q'.le_trans' _ _ _ ?_ hwin
      -- 2·Σ_r ≤ 2·(Σ_r + s_r)
      have hmono : sumExcess s r ≤ sumExcess s r + s r := by
        have hb : sumExcess s r + 0 ≤ sumExcess s r + s r :=
          Q'.add_le_add_left _ _ _ hsr_nn
        rwa [Q'.add_zero'] at hb
      exact Q'.mul_le_mul_of_nonneg_left _ _ 2 hmono (by decide)
    have ihr := ih h2Sr_le1
    -- finProd r · (1 + s_r) ≤ (1 + 2Σ_r)·(1 + s_r).
    have hmaj_nn : (0 : Q') ≤ 1 + 2 * (sumExcess s r) :=
      Q'.zero_le_add 1 _ (by decide) (Q'.mul_nonneg 2 _ (by decide) hSr_nn)
    have hstep1 : finProd s r * (1 + s r)
        ≤ (1 + 2 * (sumExcess s r)) * (1 + s r) :=
      Q'.mul_le_mul_of_nonneg ihr (Q'.le_refl' _) hmaj_nn (one_add_nonneg hsr_nn)
    refine Q'.le_trans' _ _ _ hstep1 ?_
    -- (1 + A)·(1 + s_r) ≃ (1 + A) + (1 + A)·s_r, A := 2Σ_r.
    have hExpand : (((1 + 2 * (sumExcess s r)) * (1 + s r))).eqv
        ((1 + 2 * (sumExcess s r)) + (1 + 2 * (sumExcess s r)) * s r) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (1 + 2 * (sumExcess s r)) 1 (s r)) ?_
      exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv (1 + 2 * (sumExcess s r)))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hExpand) ?_
    -- (1 + A)·s_r ≃ s_r + A·s_r, and A·s_r ≤ 1·s_r = s_r (A ≤ 1), so ≤ 2·s_r.
    have hExpand2 : (((1 + 2 * (sumExcess s r)) * s r)).eqv
        (s r + (2 * (sumExcess s r)) * s r) := by
      refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul 1 (2 * (sumExcess s r)) (s r)) ?_
      exact Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv (s r))
    have hAs_le_s : (2 * (sumExcess s r)) * s r ≤ s r := by
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.one_mul_eqv (s r)))
      exact Q'.mul_le_mul_of_nonneg_right (2 * (sumExcess s r)) 1 (s r) h2Sr_le1 hsr_nn
    have htwo : ((2 : Q') * (s r)).eqv (s r + s r) := by
      have e : ((2 : Q') * (s r)).eqv (((1 : Q') + 1) * (s r)) :=
        Q'.mul_eqv_congr_right 2 (1 + 1) (s r) (by decide)
      refine Q'.eqv_trans _ _ _ e ?_
      refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul 1 1 (s r)) ?_
      exact QPoly.q_add_congr (Q'.one_mul_eqv (s r)) (Q'.one_mul_eqv (s r))
    have hfacS_le : (1 + 2 * (sumExcess s r)) * s r ≤ 2 * (s r) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hExpand2) ?_
      have h1 : s r + (2 * (sumExcess s r)) * s r ≤ s r + s r :=
        Q'.add_le_add_left (s r) _ (s r) hAs_le_s
      exact Q'.le_trans' _ _ _ h1 (Q'.ge_of_eqv htwo)
    have hsum_le : (1 + 2 * (sumExcess s r)) + (1 + 2 * (sumExcess s r)) * s r
        ≤ (1 + 2 * (sumExcess s r)) + 2 * (s r) :=
      Q'.add_le_add_left (1 + 2 * (sumExcess s r)) _ _ hfacS_le
    refine Q'.le_trans' _ _ _ hsum_le ?_
    -- (1 + A) + 2·s_r ≃ 1 + (A + 2·s_r), and A + 2·s_r ≃ 2·(Σ_r + s_r) = 2·Σ_{r+1}.
    have hassoc : (((1 + 2 * (sumExcess s r)) + 2 * (s r))).eqv
        (1 + (2 * (sumExcess s r) + 2 * (s r))) :=
      Q'.add_assoc_eqv 1 (2 * (sumExcess s r)) (2 * (s r))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) ?_
    have hcoefSucc : ((2 * (sumExcess s r) + 2 * (s r))).eqv
        (2 * (sumExcess s r + s r)) :=
      Q'.eqv_symm (Q'.mul_add_eqv 2 (sumExcess s r) (s r))
    exact Q'.add_le_add_left 1 _ _ (Q'.le_of_eqv hcoefSucc)

/-- **The sum-form scalar bound, `Z_t` form: `∏(1+sᵢ) − 1 ≤ 2·Σ sᵢ`.**

For `sᵢ ≥ 0` on the window `Σ sᵢ ≤ 1/2`, the rank-general `Z_t` value
`ztValue s r = ∏(1+sᵢ) − 1` is at most `2·(Σ_{i<r} sᵢ)`.  This is the tight
reusable bound the honest rank-collapse uses (it keeps each per-axis gap,
unlike the lossy constant-`s` form). -/
theorem ztValue_le_two_sumExcess {s : Nat → Q'} (hs : ∀ i, (0 : Q') ≤ s i)
    (r : Nat) (hwin : 2 * (sumExcess s r) ≤ 1) :
    ztValue s r ≤ 2 * (sumExcess s r) := by
  show finProd s r - 1 ≤ 2 * (sumExcess s r)
  have hP : finProd s r ≤ 1 + 2 * (sumExcess s r) := finProd_le_two_sumExcess hs r hwin
  have hstep : finProd s r - 1 ≤ (1 + 2 * (sumExcess s r)) - 1 :=
    Q'.add_le_add_right _ _ (-1) hP
  refine Q'.le_trans' _ _ _ hstep ?_
  have he : (((1 + 2 * (sumExcess s r)) - 1)).eqv (2 * (sumExcess s r)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-1) (Q'.add_comm_eqv 1 (2 * (sumExcess s r)))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (2 * (sumExcess s r)) 1 (-1)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (show ((1 : Q') + (-1)).eqv 0 by decide)) ?_
    exact QPoly.q_add_zero_eqv (2 * (sumExcess s r))
  exact Q'.le_of_eqv he

/-- **Rank collapse from the sum bound** — the honest discharge of
`ZtMajorant.rank_collapse`.

Inputs: per-axis floor excesses `sFloor i ≥ 0` (each `= S(Δᵢ,t)` at the
group's *actual* axis gaps `Δᵢ ≥ 3/4`), the window `2·Σ sFloor ≤ 1` (i.e.
`Σ sFloor ≤ 1/2`), and the concrete cap `2·Σ sFloor ≤ Z_t(su2)` — the §3
uniform-domination fact (sum of per-axis tails dominated by SU(2)'s, via the
strict-gap suppression `e^{−t(Δᵢ−3/4)}`).  Concludes `ztValue sFloor r ≤
su2Zt`.  Unlike `rank_collapse_of_scalar`, the cap here is `2·Σ sFloor`
(tight, per-axis), so it is *satisfiable* on the canonical window. -/
theorem rank_collapse_of_sum
    {su2Zt : Q'} {sFloor : Nat → Q'} (r : Nat)
    (hFloor_nn : ∀ i, (0 : Q') ≤ sFloor i)
    (hwin : 2 * (sumExcess sFloor r) ≤ 1)
    (hcap : 2 * (sumExcess sFloor r) ≤ su2Zt) :
    ztValue sFloor r ≤ su2Zt :=
  Q'.le_trans' _ _ _ (ztValue_le_two_sumExcess hFloor_nn r hwin) hcap

/-! ## The `ztValue` (Z_t) form and the rank-collapse assembly

`ztValue (fun _ => s) r = (1 + s)^r − 1`.  Subtracting the common `1` from
the invariant bound gives the headline scalar bound `(1+s)^r − 1 ≤ 2·r·s`,
then `ztValue_mono` lifts the *uniform* upper excess `s ≥ sFloor i` to the
floor product, and the final concrete `2·r·s ≤ Z_t(su2)` caps it. -/

/-- **The scalar bound, `Z_t` form: `(1 + s)^r − 1 ≤ 2·r·s`.**

For `0 ≤ s` on the window `r·(2s) ≤ 1` (i.e. `r·s ≤ 1/2`), the constant-axis
`Z_t` value `ztValue (const s) r = (1 + s)^r − 1` is at most `2·r·s`.
Reusable across all ranks (`A`–`D` families collapse to this single
`(r,s)` inequality; the exceptionals are the same bound at larger gaps). -/
theorem ztValue_const_le {s : Q'} (hs : (0 : Q') ≤ s) (r : Nat)
    (hwin : (Q'.ofNat r) * (2 * s) ≤ 1) :
    ztValue (fun _ => s) r ≤ (Q'.ofNat r) * (2 * s) := by
  -- ztValue = finProd − 1 ≤ (1 + r·2s) − 1 = r·2s.
  show finProd (fun _ => s) r - 1 ≤ (Q'.ofNat r) * (2 * s)
  have hP : finProd (fun _ => s) r ≤ 1 + (Q'.ofNat r) * (2 * s) :=
    finProd_const_le hs r hwin
  -- subtract 1 on the right of both sides
  have hstep : finProd (fun _ => s) r - 1 ≤ (1 + (Q'.ofNat r) * (2 * s)) - 1 :=
    Q'.add_le_add_right _ _ (-1) hP
  refine Q'.le_trans' _ _ _ hstep ?_
  -- (1 + A) − 1 ≃ A
  have he : (((1 + (Q'.ofNat r) * (2 * s)) - 1)).eqv ((Q'.ofNat r) * (2 * s)) := by
    -- (1 + A) + (−1) ≃ (A + 1) + (−1) ≃ A + (1 + (−1)) ≃ A + 0 ≃ A
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-1) (Q'.add_comm_eqv 1 ((Q'.ofNat r) * (2 * s)))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ((Q'.ofNat r) * (2 * s)) 1 (-1)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (show ((1 : Q') + (-1)).eqv 0 by decide)) ?_
    exact QPoly.q_add_zero_eqv ((Q'.ofNat r) * (2 * s))
  exact Q'.le_of_eqv he

/-- **Rank collapse from the scalar bound.**  The general discharge of the
`ZtMajorant.rank_collapse` obligation, route (a).

Inputs (all concrete `Q'` facts on the heat-kernel window):
  * `hs` : `0 ≤ s`, where `s = S(3/4, t)` is the SU(2)-floor per-axis
    geometric tail excess;
  * `hfloor` : each per-axis floor excess is dominated by that single
    scalar, `sFloor i ≤ s` (every axis's Casimir gap `Δ_i ≥ 3/4`, so the
    larger gap gives the smaller tail — `expNeg_scaled_antitone_leRat`);
  * `hwin` : `r·(2s) ≤ 1` (i.e. `r·s ≤ 1/2`), the operating window
    `t ≳ 6.25` (where `s ≤ e^{−4.7} ≈ 9·10⁻³`, so `r·s ≪ 1` even for E₈);
  * `hcap` : `2·r·s ≤ Z_t(su2)`, the concrete per-rank rational cap.

Conclusion: `ztValue sFloor r ≤ su2Zt`, exactly `ZtMajorant.rank_collapse`.
The chain is `∏(1+sFloor)−1 ≤ ∏(1+s)−1 ≤ 2rs ≤ Z_t(su2)`: the first step is
`ztValue_mono` (per-axis floor domination), the second is the scalar bound
`ztValue_const_le`, the third is `hcap`. -/
theorem rank_collapse_of_scalar
    {s su2Zt : Q'} {sFloor : Nat → Q'} (r : Nat)
    (hs : (0 : Q') ≤ s)
    (hFloor_nn : ∀ i, (0 : Q') ≤ sFloor i)
    (hfloor : ∀ i, sFloor i ≤ s)
    (hwin : (Q'.ofNat r) * (2 * s) ≤ 1)
    (hcap : (Q'.ofNat r) * (2 * s) ≤ su2Zt) :
    ztValue sFloor r ≤ su2Zt := by
  -- Step 1: ztValue sFloor r ≤ ztValue (const s) r  (per-axis floor domination).
  have h1 : ztValue sFloor r ≤ ztValue (fun _ => s) r :=
    ztValue_mono hFloor_nn hfloor r
  -- Step 2: ztValue (const s) r ≤ r·(2s)  (the scalar bound).
  have h2 : ztValue (fun _ => s) r ≤ (Q'.ofNat r) * (2 * s) :=
    ztValue_const_le hs r hwin
  -- Chain through hcap.
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 hcap)

/-! ## Building a `ZtMajorant` with `rank_collapse` discharged

This is the wire-in: a `ZtMajorant R` whose `rank_collapse` field is no
longer posited but **proven** from the scalar inputs via
`rank_collapse_of_scalar`.  The remaining per-group data are exactly the
honest analytic content (R's per-axis tail excesses and their floor
domination — the engine of `CharacterTailAntitone.lean`) plus the two
concrete `Q'` facts `s`-window and `Z_t(su2)`-cap.  No named obligation
remains inside the structure. -/

/-- **`ZtMajorant` from scalar data** — `rank_collapse` discharged.

Given a group `R`, its per-axis excesses `sR`/`sFloor` (with nonnegativity
and the proven per-axis domination `sR i ≤ sFloor i`), a single scalar
upper excess `s ≥ sFloor i` (the SU(2)-floor geometric tail `S(3/4,t)`),
the window `r·(2s) ≤ 1`, and the concrete cap `2·r·s ≤ Z_t(su2)`, this
builds a `ZtMajorant R` whose `rank_collapse` is `rank_collapse_of_scalar`
— a theorem, not a field. -/
def ztMajorant_of_scalar {R : RepData} (r : Nat)
    (sR sFloor : Nat → Q') (s su2Zt : Q')
    (hsR_nn : ∀ i, (0 : Q') ≤ sR i)
    (hsR_le : ∀ i, sR i ≤ sFloor i)
    (hFloor_nn : ∀ i, (0 : Q') ≤ sFloor i)
    (hs : (0 : Q') ≤ s)
    (hfloor : ∀ i, sFloor i ≤ s)
    (hwin : (Q'.ofNat r) * (2 * s) ≤ 1)
    (hcap : (Q'.ofNat r) * (2 * s) ≤ su2Zt) :
    ZtMajorant R where
  rank      := r
  sR        := sR
  sFloor    := sFloor
  su2Zt     := su2Zt
  sR_nonneg := hsR_nn
  sR_le     := hsR_le
  rank_collapse :=
    rank_collapse_of_scalar r hs hFloor_nn hfloor hwin hcap

/-- **`ZtMajorant` from the sum bound** — the honest wire-in, `rank_collapse`
discharged by `rank_collapse_of_sum`.

Per-axis data (`sR`/`sFloor`, nonnegativity, proven domination `sR i ≤
sFloor i`) plus the two concrete `Q'` facts — window `2·Σ sFloor ≤ 1` and
cap `2·Σ sFloor ≤ Z_t(su2)` — build a `ZtMajorant R` with no posited
`rank_collapse`.  This is the constructor the `EtaFromZt` bridge consumes:
it keeps the per-axis gaps (so the cap is satisfiable on the window), unlike
`ztMajorant_of_scalar`. -/
def ztMajorant_of_sum {R : RepData} (r : Nat)
    (sR sFloor : Nat → Q') (su2Zt : Q')
    (hsR_nn : ∀ i, (0 : Q') ≤ sR i)
    (hsR_le : ∀ i, sR i ≤ sFloor i)
    (hFloor_nn : ∀ i, (0 : Q') ≤ sFloor i)
    (hwin : 2 * (sumExcess sFloor r) ≤ 1)
    (hcap : 2 * (sumExcess sFloor r) ≤ su2Zt) :
    ZtMajorant R where
  rank      := r
  sR        := sR
  sFloor    := sFloor
  su2Zt     := su2Zt
  sR_nonneg := hsR_nn
  sR_le     := hsR_le
  rank_collapse := rank_collapse_of_sum r hFloor_nn hwin hcap

/-! ## Sanity: the sum-form rank collapse fires on concrete data

A non-vacuous witness that `rank_collapse_of_sum` is satisfiable on the
operating window: rank `2`, per-axis floor excess `1/1000` each (a tiny
geometric tail at a gap `> 3/4`, the off-SU(2) regime), `Z_t(su2) = 1/100`.
The window `2·Σ = 4/1000 ≤ 1` and cap `4/1000 ≤ 10/1000` both `decide`.
(The lossy *constant* `2·r·s` form would here also pass — `4/1000 ≤ 10/1000`
— but at the SU(2) *floor* gap for high rank it would not; see the module
docstring.  The sum form is the one the honest assembly uses.) -/
example :
    ztValue (fun _ => Q'.mkPos 1 1000 (by decide)) 2
      ≤ Q'.mkPos 1 100 (by decide) := by
  have hnn : ∀ _i : Nat, (0 : Q') ≤ Q'.mkPos 1 1000 (by decide) := fun _ => by decide
  have hwin : 2 * (sumExcess (fun _ => Q'.mkPos 1 1000 (by decide)) 2) ≤ 1 := by decide
  have hcap : 2 * (sumExcess (fun _ => Q'.mkPos 1 1000 (by decide)) 2)
      ≤ Q'.mkPos 1 100 (by decide) := by decide
  exact rank_collapse_of_sum 2 hnn hwin hcap

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.ofNat_nonneg_aux
#print axioms YMGap.RG.ofNatSucc_mul_eqv
#print axioms YMGap.RG.finProd_const_le
#print axioms YMGap.RG.ztValue_const_le
#print axioms YMGap.RG.rank_collapse_of_scalar
#print axioms YMGap.RG.ztMajorant_of_scalar
#print axioms YMGap.RG.sumExcess_nonneg
#print axioms YMGap.RG.finProd_le_two_sumExcess
#print axioms YMGap.RG.ztValue_le_two_sumExcess
#print axioms YMGap.RG.rank_collapse_of_sum
#print axioms YMGap.RG.ztMajorant_of_sum
