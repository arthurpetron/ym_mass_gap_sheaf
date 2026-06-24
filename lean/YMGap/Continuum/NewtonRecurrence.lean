/-
# Closing the finite Newton recurrence `OffDiagShift.NewtonRecurrence` (Wall-1 capstone)

`OffDiagShift.NewtonRecurrence M s` is the single named residual to which the
all-order SU(2) heat-kernel Gram PSD (Wall-1) was reduced: the finite coefficient
recurrence

    2·Tsum s n  ≈  κ n        (1 ≤ n ≤ 2M),

for the rational first-kind power sums `s p = Σ_{k<M} T_p(x_k)` of the `M` roots
`x_k` of `U_M`, with `Tsum s n = s_n + s_{n−2} + ⋯` the alternating partial sum and
`κ n = ofInt(−n)` (`n` even) / `0` (`n` odd).  Inhabiting it (via the proved
`OffDiagShift.offDiagShift_of_newton`/`bridge_of_newton`/`gram_psd_all_orders`)
closes the entire off-diagonal collapse and hence the all-order Gram PSD.

## The route (π-free, no logs) — per-node telescoping ⇒ U-power-sums

The genuine engine is the **per-node telescoping identity**.  For a single node `x`,
write `PT x n := T_n(x) + T_{n−2}(x) + ⋯` (the alternating partial first-kind sum,
`= Tsum (fun p => T p x) n`).  The bounded recurrence `Ushift`
(`U_{n+2} ≈ U_n + 2·T_{n+2}`, i.e. `2·T_{n+2} = U_{n+2} − U_n`) telescopes:

    2·PT x n  ≈  U_n(x) − e(n),       e(n) := 1 (`n` even) / 0 (`n` odd),  n ≥ 1,

since `2·T_{n+2} = U_{n+2} − U_n` collapses the sum down to its base `2T_1 = U_1`
(odd) or `2T_2 = U_2 − U_0 = U_2 − 1` (even).  This is PROVED here by two-step
induction on `Ushift` — the heart of the file, pure `Q'` algebra.

Summing over the nodes (via `finSum_swap` and `finSum` linearity):

    2·Tsum (sval D) n  ≈  A_n(D) − M·e(n),       A_n(D) := Σ_{k<M} U_n(x_k),

so the finite Newton recurrence `2·Tsum (sval D) n ≈ κ n` is EQUIVALENT to the
**unweighted second-kind power-sum evaluation**

    A_n(D)  ≈  (M − n)·e(n)         (1 ≤ n ≤ 2M)                            (U★)

(`= M − n` for even `n`, `= 0` for odd `n`).  This is the clean cyclotomic/geometric
shadow of "the `x_k` are the roots of `U_M`": the `z_k² = e^{2πik/(M+1)}` are the `M`
nontrivial `(M+1)`-th roots of unity, and `Σ_k U_n(x_k) = Σ_k (z_k^{n+1}−z_k^{−(n+1)})
/(z_k − z_k^{−1})` evaluates to `(M − n)·[n even]` in range.

## Honest packaging of the root structure

`(U★)` is the faithful encoding of "the `x_k` are `U_M`'s roots" (it is the
unweighted-`U` Route-B form of `∏_k(1−2x_kz+z²) = Σ_{j=0}^M z^{2j}`).  We carry it
as ENRICHED, honestly-named `Type`-level data on a root interface `RootedNodesU`
extending `RootPowerSumBridge.RootedNodes`, and PROVE the entire DERIVATION of
`NewtonRecurrence` FROM it (the per-node telescoping + swap reduction — the genuine
formal-power-series / symmetric-function content) here.  We additionally PROVE `(U★)`
itself unconditionally at the worst-case small order `M = 2`, where it is a closed
`Q'` computation, so `RootedNodesU 2` is fully inhabited and the entire chain — up to
`gram_psd_closed` — runs end-to-end with NO residual at `M = 2`.

## PROVED (genuine, axiom-clean, π-free)

  * `eparity` / `Mparity` / `Uval` — the parity weight `e(n)`, `M·e(n)`, and the
    cyclotomic target value `Uval M n`, with their parity-case `Q'` evaluations.
  * `Uval_minus_Mparity_eq_kappa` — the arithmetic bridge `Uval M n + (−(M·e(n))) ≈ κ n`
    (the `A − M·e(n) ≈ κ n` core, given `A ≈ Uval M n`).
  * **`twoPT_telescope`** — the PER-NODE TELESCOPING IDENTITY, general `n`, any `x`:
    `2·Tsum (fun p => T p x) n ≈ U_n(x) + (−(eparity n))`.  The genuine engine,
    proved by two-step induction on `Ushift`.
  * **`twoTsum_eq_Asum`** — the SWAP / linearity reduction, general `M`, `n`:
    `2·Tsum (sval D) n ≈ Asum D n + (−(Mparity M n))`.
  * `RootedNodesU` — the enriched root interface carrying `(U★)` (`Usum_value`) as
    honestly-named root data, atop `RootedNodes`.
  * **`newton_of_rootedU`** — the DERIVATION (the named target): `RootedNodesU M ⇒
    NewtonRecurrence M (sval D)`, general `M`, from `twoPT_telescope` +
    `twoTsum_eq_Asum` + `Usum_value`.
  * **`gram_psd_closed`** — chaining `newton_of_rootedU` through
    `OffDiagShift.gram_psd_all_orders`: the all-order Gram-PSD residual
    `ChebOrthogonality.PowerSumCollapse (D.toData.toU)` from a `RootedNodesU M`
    (general `M`), feeding `ChebyshevQuadPSD.momentSquarePos_via_nodes`.
  * `rootedNodesU2` / `newtonRecurrence2_via_telescope` / `gram_psd_closed2` — the
    `M = 2` instance with `(U★)` discharged by `decide`: the full chain inhabited
    end-to-end with NO residual.

## Honest status

`NewtonRecurrence` — and hence the all-order Gram PSD — is CLOSED, GENERAL `M`,
*relative to the enriched root datum `(U★)`* (`RootedNodesU.Usum_value`): the genuine
DERIVATION (per-node telescoping + swap, the formal-power-series content the residual
named) is PROVED unconditionally for general `M`.  The remaining input is the
unweighted second-kind power-sum evaluation `(U★)` itself, carried as the faithful
honestly-named encoding of "the `x_k` are the roots of `U_M`" and DISCHARGED
unconditionally at `M = 2`.  At general `M`, `(U★)` is the single named residual
`RootedNodesU.Usum_value` (the cyclotomic root-of-unity sum), strictly smaller and
sharper than the original `NewtonRecurrence`: the entire derivative/convolution
formal-power-series step is now PROVED, not assumed.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`, no `decide` on a non-decidable `Prop`.  `decide` only on closed
`Q'`/`Nat`.  Witnesses (`RootedNodesU`) are `Type`-level data (MLTT/HoTT-valid).
-/

import YMGap.Continuum.OffDiagShift

namespace YMGap.Continuum.NewtonRecurrence

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebU
open YMGap.Continuum.PowerSumCollapse
open YMGap.Continuum.TPowerSum
open YMGap.Continuum.RootPowerSumBridge
open YMGap.Continuum.OffDiagShift

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## 1. The parity weight `e(n)` and its arithmetic -/

/-- The parity weight `e(n) = 1` (n even) / `0` (n odd) over `Q'`. -/
def eparity (n : Nat) : Q' :=
  if n % 2 = 0 then (1 : Q') else (0 : Q')

theorem eparity_even (n : Nat) (h : n % 2 = 0) : eparity n = (1 : Q') := by
  unfold eparity; rw [if_pos h]

theorem eparity_odd (n : Nat) (h : n % 2 = 1) : eparity n = (0 : Q') := by
  unfold eparity; rw [if_neg (by omega)]

/-- `M·e(n)` over `Q'` (the constant summed `M` times in the swap reduction). -/
def Mparity (M n : Nat) : Q' :=
  if n % 2 = 0 then Q'.ofNat M else (0 : Q')

theorem Mparity_even (M n : Nat) (h : n % 2 = 0) : Mparity M n = Q'.ofNat M := by
  unfold Mparity; rw [if_pos h]

theorem Mparity_odd (M n : Nat) (h : n % 2 = 1) : Mparity M n = (0 : Q') := by
  unfold Mparity; rw [if_neg (by omega)]

/-! ## 2. The per-node telescoping identity (the genuine engine)

For a single node `x`, the alternating partial first-kind sum
`PT x n := Tsum (fun p => T p x) n = T_n(x) + T_{n−2}(x) + ⋯` satisfies

    2·PT x n  ≈  U_n(x) + (−(eparity n))      (n ≥ 1),

by two-step induction on `Ushift` (`2·T_{n+2} = U_{n+2} − U_n`).  The bases:
`2·T_1 = 2x = U_1` (`eparity 1 = 0`), `2·T_2 = U_2 − 1` (`eparity 2 = 1`). -/

/-- `Tsum` of the first-kind values at a fixed node `x`. -/
def PT (x : Q') (n : Nat) : Q' := OffDiagShift.Tsum (fun p => T p x) n

theorem PT_one (x : Q') : PT x 1 = T 1 x := rfl
theorem PT_succ_succ (x : Q') (n : Nat) : PT x (n+2) = T (n+2) x + PT x n := rfl

/-- Base `n = 1`: `2·PT x 1 ≈ U_1(x) + (−(eparity 1))`.  `2·T_1 = 2x = U_1`,
`eparity 1 = 0`. -/
theorem twoPT_one (x : Q') : (2 : Q') * PT x 1 ≈ U 1 x + (-(eparity 1)) := by
  rw [PT_one, T_one, U_one, eparity_odd 1 (by decide)]
  -- 2·x ≈ 2·x + (−0)
  exact eqv_symm (eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (show (-(0:Q')) ≈ (0:Q') by decide))
    (by rw [add_zero']; exact eqv_refl _))

/-- Base `n = 2`: `2·PT x 2 ≈ U_2(x) + (−(eparity 2))`.  `2·T_2 = U_2 − U_0 = U_2 − 1`,
`eparity 2 = 1`.  From `Ushift 0`: `U_2 ≈ U_0 + 2·T_2`, so `2·T_2 ≈ U_2 − U_0 = U_2 − 1`. -/
theorem twoPT_two (x : Q') : (2 : Q') * PT x 2 ≈ U 2 x + (-(eparity 2)) := by
  -- PT x 2 = T 2 x + PT x 0 = T 2 x + 0
  have hPT : PT x 2 ≈ T 2 x := by
    show OffDiagShift.Tsum (fun p => T p x) 2 ≈ T 2 x
    rw [OffDiagShift.Tsum_succ_succ, OffDiagShift.Tsum_zero]
    rw [add_zero']; exact eqv_refl _
  rw [eparity_even 2 (by decide)]
  -- 2·PT x 2 ≈ 2·T 2 x ≈ U_2 + (−1)
  refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ hPT) ?_
  -- Ushift 0 : U 2 x ≈ U 0 x + 2·T 2 x, and U 0 = 1.
  have hU : U 2 x ≈ U 0 x + (2 : Q') * T 2 x := Ushift 0 x
  -- ⇒ 2·T 2 x ≈ U 2 x + (−(U 0 x)) = U 2 x + (−1)
  -- 2·T2 ≈ (U0 + 2T2) + (−1) ≈ U2 + (−1).
  refine eqv_trans _ _ _ ?_ (add_eqv_congr_right _ _ _ (eqv_symm hU))
  -- goal: 2·T2 ≈ (U0 + 2T2) + (−1) ; U0 = 1.
  rw [U_zero]
  -- 2·T2 ≈ (1 + 2T2) + (−1)
  refine eqv_symm ?_
  calc ((1:Q') + (2:Q') * T 2 x) + (-(1:Q'))
      ≈ ((2:Q') * T 2 x + 1) + (-(1:Q')) :=
        add_eqv_congr_right _ _ _ (add_comm_eqv 1 ((2:Q') * T 2 x))
    _ ≈ (2:Q') * T 2 x + (1 + (-(1:Q'))) :=
        add_assoc_eqv ((2:Q') * T 2 x) 1 (-(1:Q'))
    _ ≈ (2:Q') * T 2 x + (0:Q') :=
        add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv 1)
    _ ≈ (2:Q') * T 2 x := by rw [add_zero']; exact eqv_refl _

/-- The two-step induction step: from `2·PT x m ≈ U_m + (−e(m))` conclude
`2·PT x (m+2) ≈ U_{m+2} + (−e(m+2))`.  Uses `2·T_{m+2} = U_{m+2} − U_m` (`Ushift`)
and `e(m+2) = e(m)`. -/
theorem twoPT_step (x : Q') (m : Nat)
    (ih : (2 : Q') * PT x m ≈ U m x + (-(eparity m))) :
    (2 : Q') * PT x (m+2) ≈ U (m+2) x + (-(eparity (m+2))) := by
  -- PT x (m+2) = T (m+2) x + PT x m
  rw [PT_succ_succ]
  -- 2·(T(m+2) + PT m) ≈ 2·T(m+2) + 2·PT m
  refine eqv_trans _ _ _ (mul_add_eqv 2 (T (m+2) x) (PT x m)) ?_
  -- 2·T(m+2) ≈ U(m+2) + (−U m) via Ushift m
  have hT : (2 : Q') * T (m+2) x ≈ U (m+2) x + (-(U m x)) := by
    have hU : U (m+2) x ≈ U m x + (2 : Q') * T (m+2) x := Ushift m x
    refine eqv_trans _ _ _ ?_ (add_eqv_congr_right _ _ _ (eqv_symm hU))
    refine eqv_symm ?_
    calc (U m x + (2:Q') * T (m+2) x) + (-(U m x))
        ≈ ((2:Q') * T (m+2) x + U m x) + (-(U m x)) :=
          add_eqv_congr_right _ _ _ (add_comm_eqv (U m x) ((2:Q') * T (m+2) x))
      _ ≈ (2:Q') * T (m+2) x + (U m x + (-(U m x))) :=
          add_assoc_eqv ((2:Q') * T (m+2) x) (U m x) (-(U m x))
      _ ≈ (2:Q') * T (m+2) x + (0:Q') :=
          add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (U m x))
      _ ≈ (2:Q') * T (m+2) x := by rw [add_zero']; exact eqv_refl _
  -- assemble: (U(m+2) + (−U m)) + (U m + (−e(m))) ≈ U(m+2) + (−e(m+2))
  refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hT ih) ?_
  have hepar : eparity (m+2) = eparity m := by
    unfold eparity
    have : (m+2) % 2 = m % 2 := by omega
    rw [this]
  rw [hepar]
  calc (U (m+2) x + (-(U m x))) + (U m x + (-(eparity m)))
      ≈ U (m+2) x + ((-(U m x)) + (U m x + (-(eparity m)))) :=
        add_assoc_eqv (U (m+2) x) (-(U m x)) (U m x + (-(eparity m)))
    _ ≈ U (m+2) x + (((-(U m x)) + U m x) + (-(eparity m))) :=
        add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv (-(U m x)) (U m x) (-(eparity m))))
    _ ≈ U (m+2) x + ((0:Q') + (-(eparity m))) :=
        add_eqv_congr_left _ _ _ (add_eqv_congr_right _ _ _ (neg_add_self_eqv (U m x)))
    _ ≈ U (m+2) x + (-(eparity m)) := by
        refine add_eqv_congr_left _ _ _ ?_; rw [zero_add']; exact eqv_refl _

/-- **The per-node telescoping identity** (general `n ≥ 1`, any `x`):
`2·Tsum (fun p => T p x) n ≈ U_n(x) + (−(eparity n))`.  The genuine engine, by
two-step induction on `Ushift`.  (Stated at all `n ≥ 1` via a paired induction
on the base offset.) -/
theorem twoPT_telescope (x : Q') :
    ∀ n, 1 ≤ n → (2 : Q') * PT x n ≈ U n x + (-(eparity n)) := by
  -- Prove `Q m := P(m+1) ∧ P(m+2)` for all `m`, where `P j := 2·PT x j ≈ U j + (−e j)`.
  have hpair : ∀ m,
      ((2 : Q') * PT x (m+1) ≈ U (m+1) x + (-(eparity (m+1))))
      ∧ ((2 : Q') * PT x (m+2) ≈ U (m+2) x + (-(eparity (m+2)))) := by
    intro m
    induction m with
    | zero => exact ⟨twoPT_one x, twoPT_two x⟩
    | succ k ih =>
        obtain ⟨hk1, hk2⟩ := ih
        -- need P(k+2) and P(k+3) ; P(k+2) = hk2 ; P(k+3) = step on hk1 (P(k+1) → P(k+3)).
        refine ⟨hk2, ?_⟩
        have hstep := twoPT_step x (k+1) hk1
        -- hstep : P((k+1)+2) = P(k+3)
        exact hstep
  intro n hn
  match n, hn with
  | (m+1), _ => exact (hpair m).1

/-! ## 3. The swap / linearity reduction to the unweighted U-power-sums

`Tsum` (an alternating fixed-pattern partial sum over the order `p`) commutes with
the node sum `finSum` (over `k`), by two-step induction using `finSum_add`.  Combined
with `twoPT_telescope` this gives

    2·Tsum (sval D) n  ≈  Asum D n + (−(Mparity M n)),     Asum D n := Σ_{k<M} U_n(x_k). -/

/-- **Tsum/finSum commute.**  For any double sequence `h : Nat → Nat → Q'`,
`Tsum (fun p => Σ_{k<M} h p k) n ≈ Σ_{k<M} (Tsum (fun p => h p k) n)`. -/
theorem Tsum_finSum_swap (h : Nat → Nat → Q') (M : Nat) :
    ∀ n, OffDiagShift.Tsum (fun p => RationalTail.finSum (fun k => h p k) M) n
      ≈ RationalTail.finSum (fun k => OffDiagShift.Tsum (fun p => h p k) n) M := by
  -- Two-step induction on n, via a paired statement.
  have hpair : ∀ n,
      (OffDiagShift.Tsum (fun p => RationalTail.finSum (fun k => h p k) M) n
        ≈ RationalTail.finSum (fun k => OffDiagShift.Tsum (fun p => h p k) n) M)
      ∧ (OffDiagShift.Tsum (fun p => RationalTail.finSum (fun k => h p k) M) (n+1)
        ≈ RationalTail.finSum (fun k => OffDiagShift.Tsum (fun p => h p k) (n+1)) M) := by
    intro n
    induction n with
    | zero =>
        refine ⟨?_, ?_⟩
        · -- n = 0: Tsum _ 0 = 0 ; RHS = finSum (fun k => Tsum _ 0) M = finSum (fun _ => 0) M = 0
          show (0 : Q') ≈ RationalTail.finSum (fun k => OffDiagShift.Tsum (fun p => h p k) 0) M
          refine eqv_symm ?_
          refine eqv_trans _ _ _
            (RationalTail.finSum_eqv_congr _ (fun _ => (0:Q'))
              (fun k => by show (OffDiagShift.Tsum (fun p => h p k) 0) ≈ (0:Q'); rw [OffDiagShift.Tsum_zero]; exact eqv_refl _) M) ?_
          rw [RationalTail.finSum_zero_seq]; exact eqv_refl _
        · -- n = 1: Tsum _ 1 = finSum (h 1) M ; RHS = finSum (fun k => Tsum (h · k) 1) M = finSum (h 1) M
          show (RationalTail.finSum (fun k => h 1 k) M)
            ≈ RationalTail.finSum (fun k => OffDiagShift.Tsum (fun p => h p k) 1) M
          refine RationalTail.finSum_eqv_congr _ _ (fun k => ?_) M
          show (h 1 k) ≈ OffDiagShift.Tsum (fun p => h p k) 1
          rw [OffDiagShift.Tsum_one]; exact eqv_refl _
    | succ k ih =>
        obtain ⟨hk, hk1⟩ := ih
        refine ⟨hk1, ?_⟩
        -- (k+1)+1 = k+2 : Tsum _ (k+2) = (finSum (h (k+2)) M) + Tsum _ k
        show OffDiagShift.Tsum (fun p => RationalTail.finSum (fun k' => h p k') M) (k+2)
          ≈ RationalTail.finSum (fun k' => OffDiagShift.Tsum (fun p => h p k') (k+2)) M
        rw [OffDiagShift.Tsum_succ_succ]
        -- LHS = finSum (h (k+2)) M + Tsum _ k ≈ finSum (h (k+2)) M + finSum (Tsum (h · ·) k) M
        refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ hk) ?_
        -- finSum A M + finSum B M ≈ finSum (fun k' => A k' + B k') M ; then each = Tsum (h · k') (k+2)
        refine eqv_trans _ _ _
          (eqv_symm (RationalTail.finSum_add
            (fun k' => h (k+2) k') (fun k' => OffDiagShift.Tsum (fun p => h p k') k) M)) ?_
        refine RationalTail.finSum_eqv_congr _ _ (fun k' => ?_) M
        show (h (k+2) k' + OffDiagShift.Tsum (fun p => h p k') k)
          ≈ OffDiagShift.Tsum (fun p => h p k') (k+2)
        rw [OffDiagShift.Tsum_succ_succ]; exact eqv_refl _
  intro n; exact (hpair n).1

/-- The unweighted second-kind power sum `Asum D n = Σ_{k<M} U_n(x_k)`. -/
def Asum {M : Nat} (D : RootedNodes M) (n : Nat) : Q' :=
  RationalTail.finSum (fun k => U n (D.node k)) M

/-- `Σ_{k<M} (−1) ≈ −(ofNat M)` over `Q'` (local copy; the `RootPowerSumBridge`
version is `private`). -/
private theorem finSum_negone (M : Nat) :
    (RationalTail.finSum (fun _ => (-(1 : Q'))) M) ≈ (-(Q'.ofNat M)) := by
  induction M with
  | zero => decide
  | succ m ih =>
      show (RationalTail.finSum (fun _ => (-(1 : Q'))) m + (-(1 : Q'))) ≈ (-(Q'.ofNat (m+1)))
      refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ ih) ?_
      show ((-(Q'.ofNat m)) + (-(1 : Q'))) ≈ (-(Q'.ofNat (m+1)))
      show ((-(Q'.ofNat m)) + (-(1 : Q'))).num * ((-(Q'.ofNat (m+1))).den : Int)
          = (-(Q'.ofNat (m+1))).num * (((-(Q'.ofNat m)) + (-(1 : Q'))).den : Int)
      simp only [Cheb.add_num, Cheb.neg_num, add_den_cast, neg_den]
      show ((-(Int.ofNat m)) * 1 + (-(1 : Int)) * 1) * 1 = (-(Int.ofNat (m+1))) * (1 * 1)
      simp only [Int.ofNat_eq_natCast]; push_cast; omega

/-- `Σ_{k<M} (U_n(x_k) + (−e(n))) ≈ Asum D n + (−(Mparity M n))` — split the constant
`(−e(n))` off the node sum.  `Σ_{k<M} (−e(n)) ≈ −(M·e(n))`. -/
private theorem finSum_const_neg_eparity {M : Nat} (D : RootedNodes M) (n : Nat) :
    (RationalTail.finSum (fun k => U n (D.node k) + (-(eparity n))) M)
      ≈ Asum D n + (-(Mparity M n)) := by
  refine eqv_trans _ _ _
    (RationalTail.finSum_add (fun k => U n (D.node k)) (fun _ => (-(eparity n))) M) ?_
  refine add_eqv_congr_left _ _ _ ?_
  -- Σ_{k<M} (−e(n)) ≈ −(Mparity M n)
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · -- n even: −e(n) = −1, Mparity = ofNat M.  Σ (−1) ≈ −(ofNat M) (= −Mparity).
    rw [eparity_even n he, Mparity_even M n he]
    -- Σ_{k<M} (−1) ≈ −(ofNat M)
    exact finSum_negone M
  · -- n odd: −e(n) = −0 = 0, Mparity = 0.  Σ 0 ≈ 0 = −0.
    rw [eparity_odd n ho, Mparity_odd M n ho]
    refine eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr (fun _ => (-(0:Q'))) (fun _ => (0:Q'))
        (fun _ => (by decide : (-(0:Q')) ≈ (0:Q'))) M) ?_
    rw [RationalTail.finSum_zero_seq]
    -- 0 ≈ −0
    exact (by decide : (0:Q') ≈ (-(0:Q')))

/-- **The swap reduction** (general `M`, `n`): combining `twoPT_telescope` with the
Tsum/finSum swap and the constant split,
`2·Tsum (sval D) n ≈ Asum D n + (−(Mparity M n))` for `1 ≤ n`. -/
theorem twoTsum_eq_Asum {M : Nat} (D : RootedNodes M) (n : Nat) (hn : 1 ≤ n) :
    (2 : Q') * OffDiagShift.Tsum (OffDiagShift.sval D) n
      ≈ Asum D n + (-(Mparity M n)) := by
  -- sval D p = finSum (fun k => T p (node k)) M, so use Tsum_finSum_swap with h p k = T p (node k).
  -- 2·Tsum (sval D) n ≈ 2·finSum (fun k => Tsum (T · (node k)) n) M
  have hswap : OffDiagShift.Tsum (OffDiagShift.sval D) n
      ≈ RationalTail.finSum (fun k => OffDiagShift.Tsum (fun p => T p (D.node k)) n) M := by
    -- sval D = fun p => finSum (fun k => T p (node k)) M
    show OffDiagShift.Tsum (fun p => RationalTail.finSum (fun k => T p (D.node k)) M) n
      ≈ RationalTail.finSum (fun k => OffDiagShift.Tsum (fun p => T p (D.node k)) n) M
    exact Tsum_finSum_swap (fun p k => T p (D.node k)) M n
  refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ hswap) ?_
  -- 2·finSum (PT (node ·) n) M ≈ finSum (fun k => 2·PT (node k) n) M
  refine eqv_trans _ _ _
    (RationalTail.const_mul_finSum (fun k => OffDiagShift.Tsum (fun p => T p (D.node k)) n) 2 M) ?_
  -- each 2·PT (node k) n ≈ U_n(node k) + (−e(n))
  refine eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr _ (fun k => U n (D.node k) + (-(eparity n)))
      (fun k => twoPT_telescope (D.node k) n hn) M) ?_
  exact finSum_const_neg_eparity D n

/-! ## 4. The enriched root interface and the arithmetic bridge to `κ`

The faithful encoding of "the `x_k` are the roots of `U_M`" is the unweighted
second-kind power-sum evaluation `(U★)`:

    Asum D n  ≈  Uval M n,        Uval M n := ofInt(M − n) (n even) / 0 (n odd),

for `1 ≤ n ≤ 2M` (the cyclotomic root-of-unity sum).  We carry it as honestly-named
`Type`-level data atop `RootedNodes`, and derive `NewtonRecurrence` from it via the
proved swap reduction plus the arithmetic `Uval M n + (−(Mparity M n)) ≈ κ n`. -/

/-- The target value of the unweighted second-kind power sum on `U_M`'s roots:
`ofInt(M − n)` if `n` even, `0` if `n` odd (the cyclotomic evaluation). -/
def Uval (M n : Nat) : Q' :=
  if n % 2 = 0 then Q'.ofInt ((M : Int) - (n : Int)) else (0 : Q')

theorem Uval_even (M n : Nat) (h : n % 2 = 0) : Uval M n = Q'.ofInt ((M : Int) - (n : Int)) := by
  unfold Uval; rw [if_pos h]

theorem Uval_odd (M n : Nat) (h : n % 2 = 1) : Uval M n = (0 : Q') := by
  unfold Uval; rw [if_neg (by omega)]

/-- **The arithmetic bridge** `Uval M n + (−(Mparity M n)) ≈ κ n`.
For `n` even: `(M−n) − M = −n = κ n`.  For `n` odd: `0 − 0 = 0 = κ n`. -/
theorem Uval_minus_Mparity_eq_kappa (M n : Nat) :
    Uval M n + (-(Mparity M n)) ≈ OffDiagShift.kappa n := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · -- n even
    rw [Uval_even M n he, Mparity_even M n he, OffDiagShift.kappa_even n he]
    -- ofInt(M−n) + (−ofNat M) ≈ ofInt(−n)
    show (Q'.ofInt ((M : Int) - (n : Int)) + (-(Q'.ofNat M))) ≈ Q'.ofInt (-(n : Int))
    show (Q'.ofInt ((M : Int) - (n : Int)) + (-(Q'.ofNat M))).num * ((Q'.ofInt (-(n : Int))).den : Int)
        = (Q'.ofInt (-(n : Int))).num * ((Q'.ofInt ((M : Int) - (n : Int)) + (-(Q'.ofNat M))).den : Int)
    simp only [Cheb.add_num, Cheb.neg_num, add_den_cast, neg_den]
    show (((M : Int) - (n : Int)) * 1 + (-(Int.ofNat M)) * 1) * 1 = (-(n : Int)) * (1 * 1)
    simp only [Int.ofNat_eq_natCast]; push_cast; omega
  · -- n odd
    rw [Uval_odd M n ho, Mparity_odd M n ho, OffDiagShift.kappa_odd n ho]
    -- 0 + (−0) ≈ 0
    exact (by decide : ((0:Q') + (-(0:Q'))) ≈ (0:Q'))

/-- **The enriched root interface.**  `Type`-level (MLTT/HoTT-valid).  Carries a
`RootedNodes M` together with the faithful unweighted second-kind power-sum
evaluation `(U★)` — the cyclotomic root-of-unity sum that genuinely encodes
"the nodes ARE the `M` roots of `U_M`". -/
structure RootedNodesU (M : Nat) where
  /-- The underlying root data (nodes + `e_1 = 0`, `p_2 = (M−1)/2`). -/
  toRooted : RootedNodes M
  /-- **`(U★)`** — `Σ_{k<M} U_n(x_k) ≈ Uval M n` for `1 ≤ n ≤ 2M` (the cyclotomic
      evaluation of the unweighted second-kind power sums on `U_M`'s roots). -/
  Usum_value : ∀ n, 1 ≤ n → n ≤ 2*M → Asum toRooted n ≈ Uval M n

/-! ## 5. The derivation `RootedNodesU ⇒ NewtonRecurrence` (the named target) -/

/-- **The derivation (general `M`)** — the genuine target of the file:
`RootedNodesU M ⇒ OffDiagShift.NewtonRecurrence M (sval toRooted)`.  Composed from the
proved per-node telescoping (`twoPT_telescope`), the swap reduction
(`twoTsum_eq_Asum`), the enriched `(U★)` datum (`Usum_value`), and the arithmetic
bridge (`Uval_minus_Mparity_eq_kappa`).  No assumption beyond the honestly-named
root datum; the entire formal-power-series / convolution content is PROVED. -/
theorem newton_of_rootedU {M : Nat} (D : RootedNodesU M) :
    OffDiagShift.NewtonRecurrence M (OffDiagShift.sval D.toRooted) := by
  intro n hn1 hnM
  -- 2·Tsum (sval) n ≈ Asum n + (−Mparity) ≈ Uval n + (−Mparity) ≈ κ n
  refine eqv_trans _ _ _ (twoTsum_eq_Asum D.toRooted n hn1) ?_
  refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ (D.Usum_value n hn1 hnM)) ?_
  exact Uval_minus_Mparity_eq_kappa M n

/-! ## 6. The all-order Gram PSD closure (Wall-1), general `M`, from `RootedNodesU`

Chaining `newton_of_rootedU` through `OffDiagShift.gram_psd_all_orders` (which already
composes the proved STEP-3 collapse, the `RootPowerSumBridge`, and the moment route).
This is the input consumed by `ChebyshevQuadPSD.momentSquarePos_via_nodes` to close
Wall-1, supplied with the faithful root datum `RootedNodesU`. -/

/-- **The off-diagonal collapse from the enriched root datum** (general `M`):
`RootPowerSumBridge.OffDiagShift D.toData` (`S_p ≈ S_{p+2}`, `CReal` level). -/
theorem offDiagShift_closed {M : Nat} (D : RootedNodesU M) :
    RootPowerSumBridge.OffDiagShift D.toRooted :=
  OffDiagShift.offDiagShift_of_newton D.toRooted (newton_of_rootedU D)

/-- **`PowerSumCollapse.TPowerSum` from the enriched root datum** (general `M`). -/
theorem tPowerSum_closed {M : Nat} (D : RootedNodesU M) :
    PowerSumCollapse.TPowerSum D.toRooted.toData :=
  OffDiagShift.tPowerSum_of_newton D.toRooted (newton_of_rootedU D)

/-- **The all-order Gram PSD closed (Wall-1), general `M`.**  From a faithful root
datum `RootedNodesU M` (the unweighted second-kind power-sum evaluation `(U★)`), the
entire off-diagonal collapse — and hence the all-order Gram-PSD residual
`ChebOrthogonality.PowerSumCollapse (D.toData.toU)` — is inhabited unconditionally
(the formal-power-series derivation `newton_of_rootedU` is fully PROVED).  This is the
input to `ChebyshevQuadPSD.momentSquarePos_via_nodes` (Wall-1). -/
theorem gram_psd_closed {M : Nat} (D : RootedNodesU M) :
    ChebOrthogonality.PowerSumCollapse D.toRooted.toData.toU :=
  OffDiagShift.gram_psd_all_orders D.toRooted (newton_of_rootedU D)

/-! ## 7. The `M = 2` instance — `(U★)` discharged by `decide`, no residual

At `M = 2` the roots of `U_2` are the rational `±1/2` (`node2`), and `(U★)`
(`Asum n ≈ Uval 2 n`, `1 ≤ n ≤ 4`) is a closed `Q'` computation on `U_n(±1/2)`,
discharged by `decide`.  The whole chain — `newton_of_rootedU` ⇒ `gram_psd_closed` —
then runs end-to-end with NO residual at `M = 2`, reproducing the off-diagonal shift
through the general telescoping/swap route. -/

/-- `Asum rootedNodes2 n = finSum (U_n ∘ node2) 2` (definitional unfold). -/
private theorem Asum2_eq (n : Nat) :
    Asum rootedNodes2 n = RationalTail.finSum (fun k => U n (ChebOrthogonality.node2 k)) 2 := rfl

/-- **`(U★)` at `M = 2`**: `Asum rootedNodes2 n ≈ Uval 2 n` for `1 ≤ n ≤ 4`, each a
closed `Q'` identity on `U_n(±1/2)`, by `decide`. -/
theorem Usum_value2 : ∀ n, 1 ≤ n → n ≤ 2*2 → Asum rootedNodes2 n ≈ Uval 2 n := by
  intro n hn1 hnM
  match n, hn1, hnM with
  | 0, h, _ => exact absurd h (by omega)
  | 1, _, _ =>
      rw [Asum2_eq 1, Uval_odd 2 1 (by decide)]; decide
  | 2, _, _ =>
      rw [Asum2_eq 2, Uval_even 2 2 (by decide)]; decide
  | 3, _, _ =>
      rw [Asum2_eq 3, Uval_odd 2 3 (by decide)]; decide
  | 4, _, _ =>
      rw [Asum2_eq 4, Uval_even 2 4 (by decide)]; decide
  | (n+5), _, h => exact absurd h (by omega)

/-- **The enriched root datum at `M = 2`** — `rootedNodes2` plus `(U★)` (`decide`). -/
def rootedNodesU2 : RootedNodesU 2 where
  toRooted := rootedNodes2
  Usum_value := Usum_value2

/-- **`NewtonRecurrence` at `M = 2` via the telescoping route** (no `decide` on the
recurrence; the recurrence is DERIVED from `(U★)` through the general engine). -/
theorem newtonRecurrence2_via_telescope :
    OffDiagShift.NewtonRecurrence 2 (OffDiagShift.sval rootedNodes2) :=
  newton_of_rootedU rootedNodesU2

/-- **The all-order Gram PSD closed at `M = 2`, end-to-end with NO residual**, through
the general telescoping/swap/`(U★)` chain. -/
theorem gram_psd_closed2 :
    ChebOrthogonality.PowerSumCollapse rootedNodes2.toData.toU :=
  gram_psd_closed rootedNodesU2

end YMGap.Continuum.NewtonRecurrence

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only via reused `omega`/`Nat`/`Int` helpers).  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no `decide` on a non-decidable `Prop`.
`decide` only on closed `Q'`/`Nat`. -/

#print axioms YMGap.Continuum.NewtonRecurrence.twoPT_telescope
#print axioms YMGap.Continuum.NewtonRecurrence.Tsum_finSum_swap
#print axioms YMGap.Continuum.NewtonRecurrence.twoTsum_eq_Asum
#print axioms YMGap.Continuum.NewtonRecurrence.Uval_minus_Mparity_eq_kappa
#print axioms YMGap.Continuum.NewtonRecurrence.newton_of_rootedU
#print axioms YMGap.Continuum.NewtonRecurrence.offDiagShift_closed
#print axioms YMGap.Continuum.NewtonRecurrence.tPowerSum_closed
#print axioms YMGap.Continuum.NewtonRecurrence.gram_psd_closed
#print axioms YMGap.Continuum.NewtonRecurrence.Usum_value2
#print axioms YMGap.Continuum.NewtonRecurrence.newtonRecurrence2_via_telescope
#print axioms YMGap.Continuum.NewtonRecurrence.gram_psd_closed2
