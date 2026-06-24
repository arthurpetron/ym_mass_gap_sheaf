/-
# The off-diagonal first-kind power-sum collapse `S_p = S_{p+2}` (Wall-1, off-diagonal Newton step)

This module attacks `RootPowerSumBridge.OffDiagShift M D` — the off-diagonal half of
the first-kind power-sum bridge for the roots `x_1,…,x_M` of the second-kind
Chebyshev polynomial `U_M`:

    S_p = S_{p+2}   for 0 < p ≤ M−1,        S_j := Σ_{k=1}^M T_j(x_k).

Combined with the already-proved `S_0 = M` (`TPowerSum.Sj0_eq_M`) and `S_2 = −1`
(`RootPowerSumBridge.S2_eq_neg_one`, general `M`) this inhabits
`TPowerSum.RootPowerSumBridge`, hence `PowerSumCollapse.TPowerSum`, hence the full
discrete Chebyshev-U orthogonality, hence the ALL-ORDER SU(2) heat-kernel Gram PSD
(Wall-1), via `ChebyshevQuadPSD.momentSquarePos_via_nodes`.

## The worked (π-free, no logs) constructive route

STEP 1 — KEY PRODUCT IDENTITY.  `P(z) := ∏_{k=1}^M (1 − 2 x_k z + z²) = Σ_{j=0}^M z^{2j}`.
  From the factorization `U_M(w) = 2^M ∏_k (w − x_k)` and the proved
  `TPowerSum.Ugen` (`(z−w)·U_M((z+w)/2) = z^{M+1} − w^{M+1}` for `z·w = 1`):
  with `c = (z+z⁻¹)/2`, `∏_k(1−2x_kz+z²) = (2z)^M U_M(c)/2^M = z^M U_M(c)
  = (z^{2(M+1)}−1)/(z²−1) = Σ_{j=0}^M z^{2j}`.  We PROVE the single-variable shadow
  `z^M·U_M((z+z⁻¹)/2) = Σ_{j=0}^M z^{2j}` directly from `Ugen` (`prodIdentity_geom`),
  the genuine generating-function heart of the root structure.

STEP 2 — NEWTON RELATION ⇒ FINITE COEFFICIENT RECURRENCE.  Comparing `[z^n]` on the
  two sides of the (derivative) Newton relation `−z·P'(z) = 2·P(z)·Σ_{p≥1} S_p z^p`,
  with `[z^{2j}]P = 1` (`0 ≤ j ≤ M`, else 0), yields the FINITE recurrence

      2·(S_n + S_{n−2} + ⋯ + S_{1 or 2})  =  (n even ∧ n ≤ 2M ? −n : 0)   (1 ≤ n).

  We package this finite recurrence as the honestly-named predicate `NewtonRecurrence`
  on the rational power sums `s p = Σ_{k<M} T_p(x_k)` (its derivation from the product
  identity `P(z)=Σz^{2j}` — the formal-derivative / Cauchy-convolution coefficient
  comparison — is the single NAMED-open residual, `NewtonRecurrence`).

STEP 3 — THE COLLAPSE (PROVED, general `M`).  By strong induction, the finite
  recurrence forces `s_p = 0` for odd `p` and `s_p = −1` for even `p ≥ 2` (within
  the valid range): subtracting the recurrence at `n` and `n+2` (same parity) gives
  `s_{n+2} = 0` (odd) resp. `s_{n+2} = −1` (even).  Hence `s_p = s_{p+2}` for same
  parity, i.e. `OffDiagShift` — fully proved from `NewtonRecurrence` for general `M`.

## PROVED (genuine, axiom-clean, π-free)

  * `prodIdentity_cleared` / `prodIdentity_geom` — STEP 1, the KEY PRODUCT IDENTITY's
    single-variable shadow, proved from `TPowerSum.Ugen`: the cleared (cross-multiplied
    by `z²−1`, hence π-free and division-free for general `z·w ≈ 1`) form
    `(z²−1)·(z^M·U_M((z+w)·½)) ≈ z^{2(M+1)} − 1 ≈ (z²−1)·Σ_{j=0}^M z^{2j}`.  The
    uncleared `z^M·U_M = Σ z^{2j}` follows wherever `z² − 1` is invertible (the roots,
    `z = e^{iθ}`); the cleared identity is the genuine general-`z` content.
  * `Tsum` / `Tsum_succ_succ` — the finite alternating partial power-sum
    `s_n + s_{n−2} + ⋯`, the LHS of the Newton recurrence.
  * `sval_parity` — STEP 3, the power-sum values forced by `NewtonRecurrence`
    (`s_p = 0` odd, `s_p = −1` even, `1 ≤ p ≤ 2M`), general `M`.
  * `offDiagShift_of_newton` — STEP 3 capstone: `NewtonRecurrence ⇒ OffDiagShift`
    (`s_p = s_{p+2}`), general `M`, π-free.
  * `bridge_of_newton` / `tPowerSum_of_newton` — chaining `offDiagShift_of_newton`
    through `RootPowerSumBridge.bridge_of_offdiag` to `RootPowerSumBridge` and
    `PowerSumCollapse.TPowerSum` (general `M`), given `NewtonRecurrence`.
  * `gram_psd_all_orders` — the all-order Gram-PSD residual
    `ChebOrthogonality.PowerSumCollapse (D.toData.toU)` from `NewtonRecurrence`
    (general `M`), feeding `ChebyshevQuadPSD.momentSquarePos_via_nodes` (Wall-1).
  * `newtonRecurrence2` / `offDiagShift2_via_newton` — the `M = 2` instance,
    `NewtonRecurrence` discharged by `decide`, reproducing the off-diagonal shift
    through the general STEP-3 route.

## NAMED open (the precise residual)

  * `NewtonRecurrence M D` — STEP 2: the finite coefficient recurrence
    `2·Tsum s n ≈ (n even ∧ n≤2M ? ofInt(−n) : 0)`.  This is exactly the
    coefficient comparison of the derivative Newton relation `−zP' = 2PG` against the
    proved product identity `P(z)=Σz^{2j}`; closing it is the formal-derivative /
    finite-convolution lemma.  It is NAMED, not faked.  Given it, the entire
    off-diagonal collapse — and hence the all-order Gram PSD — closes for general `M`.

So the all-order Gram PSD (Wall-1) is **NOT closed** by this module: STEP 1 (the
genuine root/generating identity) and STEP 3 (the recurrence ⇒ collapse, general `M`)
are PROVED; the single bridge between them, STEP 2 (the derivative / convolution
coefficient comparison `NewtonRecurrence`), is the named residual, discharged
unconditionally at `M = 2`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`, no `decide` on a non-decidable `Prop`.  `decide` only on closed
`Q'`/`Nat`.  Witnesses are `Type`-level data (MLTT/HoTT-valid).
-/

import YMGap.Continuum.RootPowerSumBridge

namespace YMGap.Continuum.OffDiagShift

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebU
open YMGap.Continuum.PowerSumCollapse
open YMGap.Continuum.TPowerSum
open YMGap.Continuum.RootPowerSumBridge

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## STEP 1 — the KEY PRODUCT IDENTITY (single-variable shadow), proved from `Ugen`

The product `∏_k(1 − 2x_k z + z²)` over the roots of `U_M`, with `c = (z+z⁻¹)/2`,
equals `z^M·U_M(c) = Σ_{j=0}^M z^{2j}` (the Dirichlet kernel in `z²`).  We prove the
genuine generating-function heart `z^M·U_M((z+z⁻¹)/2) ≈ Σ_{j=0}^M z^{2j}` directly
from `TPowerSum.Ugen` and the geometric sum `(z²−1)·Σ_{j=0}^M z^{2j} = z^{2(M+1)}−1`.

We carry the rational inverse `w = z⁻¹` as a hypothesis `z·w ≈ 1` (so no division is
needed): set `c = (z+w)·½`.  Then `Ugen` gives `(z−w)·U_M(c) ≈ z^{M+1} − w^{M+1}`, and
multiplying by `z^M` and using `z·w ≈ 1` (so `z^M·w^{M+1} ≈ w`, `z^M·z^{M+1} ≈ z^{2M+1}`)
plus the geometric identity yields the result. -/

/-- The geometric partial sum `Σ_{j=0}^{M} z^{2j}` over `Q'`. -/
def geomEven (z : Q') : Nat → Q'
  | 0 => (1 : Q')
  | (m+1) => geomEven z m + z ^ (2*(m+1))

@[simp] theorem geomEven_zero (z : Q') : geomEven z 0 = 1 := rfl
theorem geomEven_succ (z : Q') (m : Nat) :
    geomEven z (m+1) = geomEven z m + z ^ (2*(m+1)) := rfl

/-- `z^a · z^b ≈ z^(a+b)`. -/
theorem zpow_add (z : Q') (a b : Nat) : z ^ a * z ^ b ≈ z ^ (a+b) := by
  induction b with
  | zero =>
      show z ^ a * z ^ 0 ≈ z ^ (a+0)
      rw [Q'.pow_zero]; exact mul_one_eqv (z ^ a)
  | succ m ih =>
      show z ^ a * z ^ (m+1) ≈ z ^ (a+(m+1))
      have he : a + (m+1) = (a+m) + 1 := by omega
      rw [Q'.pow_succ, he, Q'.pow_succ]
      -- z^a·(z·z^m) ≈ z·(z^a·z^m) ≈ z·z^(a+m)
      refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv (z^a) z (z^m))) ?_
      refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv (z^a) z)) ?_
      refine eqv_trans _ _ _ (mul_assoc_eqv z (z^a) (z^m)) ?_
      exact mul_eqv_congr_left _ _ _ ih

/-- **The geometric identity** `(z² + (−1))·(Σ_{j=0}^M z^{2j}) ≈ z^{2(M+1)} + (−1)`.
The telescoping `(z²−1)·Σ_{j=0}^M z^{2j} = z^{2(M+1)} − 1`. -/
theorem geom_telescope (z : Q') (M : Nat) :
    (z ^ 2 + (-(1 : Q'))) * geomEven z M ≈ z ^ (2*(M+1)) + (-(1 : Q')) := by
  induction M with
  | zero =>
      -- (z² − 1)·1 ≈ z² − 1
      show (z ^ 2 + (-(1 : Q'))) * geomEven z 0 ≈ z ^ (2*1) + (-(1 : Q'))
      rw [geomEven_zero]
      refine eqv_trans _ _ _ (mul_one_eqv _) ?_
      show z ^ 2 + (-(1 : Q')) ≈ z ^ (2*1) + (-(1 : Q'))
      have : (2*1 : Nat) = 2 := by decide
      rw [this]; exact eqv_refl _
  | succ m ih =>
      -- (z²−1)·(geom m + z^{2(m+1)}) = (z²−1)·geom m + (z²−1)·z^{2(m+1)}
      rw [geomEven_succ]
      refine eqv_trans _ _ _ (mul_add_eqv (z ^ 2 + (-(1 : Q'))) (geomEven z m) (z ^ (2*(m+1)))) ?_
      -- ≈ (z^{2(m+1)} − 1) + (z^{2(m+2)} − z^{2(m+1)})  ≈  z^{2(m+2)} − 1
      refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ ih) ?_
      -- second term: (z²−1)·z^{2(m+1)} ≈ z^{2(m+2)} + (−z^{2(m+1)})
      have hsec : (z ^ 2 + (-(1 : Q'))) * z ^ (2*(m+1))
          ≈ z ^ (2*(m+2)) + (-(z ^ (2*(m+1)))) := by
        refine eqv_trans _ _ _ (Cheb.add_mul_eqv (z ^ 2) (-(1:Q')) (z ^ (2*(m+1)))) ?_
        refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
        · -- z²·z^{2(m+1)} ≈ z^{2(m+2)}
          refine eqv_trans _ _ _ (zpow_add z 2 (2*(m+1))) ?_
          have he : (2 + 2*(m+1) : Nat) = 2*(m+2) := by omega
          rw [he]; exact eqv_refl _
        · -- (−1)·z^{2(m+1)} ≈ −z^{2(m+1)}
          exact eqv_trans _ _ _ (neg_mul_eqv 1 (z ^ (2*(m+1))))
            (neg_eqv_congr _ _ (one_mul_eqv (z ^ (2*(m+1)))))
      refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ hsec) ?_
      -- (z^{2(m+1)} + (−1)) + (z^{2(m+2)} + (−z^{2(m+1)})) ≈ z^{2(m+2)} + (−1)
      -- = z^{2(m+1)} − 1 + z^{2(m+2)} − z^{2(m+1)}  (the z^{2(m+1)} cancel)
      calc (z ^ (2*(m+1)) + (-(1 : Q'))) + (z ^ (2*(m+2)) + (-(z ^ (2*(m+1)))))
          ≈ ((-(1 : Q')) + z ^ (2*(m+1))) + (z ^ (2*(m+2)) + (-(z ^ (2*(m+1))))) :=
            add_eqv_congr_right _ _ _ (add_comm_eqv (z ^ (2*(m+1))) (-(1:Q')))
        _ ≈ (-(1 : Q')) + (z ^ (2*(m+1)) + (z ^ (2*(m+2)) + (-(z ^ (2*(m+1)))))) :=
            add_assoc_eqv (-(1:Q')) (z ^ (2*(m+1))) (z ^ (2*(m+2)) + (-(z ^ (2*(m+1)))))
        _ ≈ (-(1 : Q')) + (z ^ (2*(m+1)) + ((-(z ^ (2*(m+1)))) + z ^ (2*(m+2)))) :=
            add_eqv_congr_left _ _ _ (add_eqv_congr_left _ _ _
              (add_comm_eqv (z ^ (2*(m+2))) (-(z ^ (2*(m+1))))))
        _ ≈ (-(1 : Q')) + ((z ^ (2*(m+1)) + (-(z ^ (2*(m+1))))) + z ^ (2*(m+2))) :=
            add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv (z ^ (2*(m+1))) (-(z ^ (2*(m+1)))) (z ^ (2*(m+2)))))
        _ ≈ (-(1 : Q')) + ((0 : Q') + z ^ (2*(m+2))) :=
            add_eqv_congr_left _ _ _ (add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv (z ^ (2*(m+1)))))
        _ ≈ (-(1 : Q')) + z ^ (2*(m+2)) := by
            refine add_eqv_congr_left _ _ _ ?_; rw [zero_add']; exact eqv_refl _
        _ ≈ z ^ (2*(m+2)) + (-(1 : Q')) := add_comm_eqv (-(1:Q')) (z ^ (2*(m+2)))

/-! ### From `Ugen` to the product identity

`Ugen` gives `(z − w)·U_M(c) ≈ z^{M+1} − w^{M+1}` with `c = (z+w)·½`, `z·w ≈ 1`.
Multiply both sides by `(z + w)·z^M`?  No — the clean route is:
`(z² − 1) · [z^M U_M(c)]`.  Using `z·w ≈ 1`, `z^M·(z − w) = z^{M+1} − z^M·w`, and
`z^M·w ≈ z^{M−1}` … the bookkeeping is cleanest via the SQUARED variable.  We instead
prove the identity in its already-cleared geometric form:

    (z² − 1) · (z^M · U_M(c))  ≈  z^{2(M+1)} − 1,

from which `z^M U_M(c) ≈ Σ z^{2j}` follows by the geometric identity (both satisfy the
same cleared equation against the nonzero `z²−1`).  We provide the cleared identity
`prodIdentity_cleared` and, under the genuine factorization data, the named product
identity itself. -/

/-- `z·w ≈ 1` ⇒ `z^M · w ≈ z^(M−1)` for `M ≥ 1` (written `z^m·w ≈ z^m·w`, used at
`M = m+1`: `z^{m+1}·w = z^m·(z·w) ≈ z^m`). -/
private theorem zMw_cancel (z w : Q') (hzw : z * w ≈ (1 : Q')) (m : Nat) :
    z ^ (m+1) * w ≈ z ^ m := by
  -- z^{m+1}·w = (z·z^m)·w ≈ (z^m·z)·w ≈ z^m·(z·w) ≈ z^m·1 ≈ z^m
  rw [Q'.pow_succ]
  refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv z (z ^ m))) ?_
  refine eqv_trans _ _ _ (mul_assoc_eqv (z ^ m) z w) ?_
  refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ hzw) ?_
  exact mul_one_eqv (z ^ m)

/-- `z·w ≈ 1` ⇒ `z^n · w^n ≈ 1` (the product of inverses). -/
theorem zMpow_wMpow (z w : Q') (hzw : z * w ≈ (1 : Q')) (n : Nat) :
    z ^ n * w ^ n ≈ (1 : Q') := by
  induction n with
  | zero => show z ^ 0 * w ^ 0 ≈ (1:Q'); rw [Q'.pow_zero, Q'.pow_zero]; exact mul_one_eqv 1
  | succ n ih =>
      show z ^ (n+1) * w ^ (n+1) ≈ (1:Q')
      rw [Q'.pow_succ, Q'.pow_succ]
      -- (z·z^n)·(w·w^n) ≈ (z·w)·(z^n·w^n) ≈ 1·1 ≈ 1
      calc (z * z ^ n) * (w * w ^ n)
          ≈ z * (z ^ n * (w * w ^ n)) := mul_assoc_eqv z (z ^ n) (w * w ^ n)
        _ ≈ z * ((z ^ n * w) * w ^ n) := mul_eqv_congr_left _ _ _ (eqv_symm (mul_assoc_eqv (z ^ n) w (w ^ n)))
        _ ≈ z * ((w * z ^ n) * w ^ n) := mul_eqv_congr_left _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv (z ^ n) w))
        _ ≈ z * (w * (z ^ n * w ^ n)) := mul_eqv_congr_left _ _ _ (mul_assoc_eqv w (z ^ n) (w ^ n))
        _ ≈ (z * w) * (z ^ n * w ^ n) := eqv_symm (mul_assoc_eqv z w (z ^ n * w ^ n))
        _ ≈ (1 : Q') * (z ^ n * w ^ n) := mul_eqv_congr_right _ _ _ hzw
        _ ≈ z ^ n * w ^ n := one_mul_eqv (z ^ n * w ^ n)
        _ ≈ (1 : Q') := ih

/-- **The cleared product identity.**  For `z·w ≈ 1`, `c = (z+w)·½`,
`(z² + (−1))·(z^M·U_M(c)) ≈ z^{2(M+1)} + (−1)`.

Proof: multiply `Ugen` (`(z−w)·U_M(c) ≈ z^{M+1}−w^{M+1}`) by `z^{M+1}` and use the
cancellations `z^{M+1}·w^{M+1} ≈ 1`, `z^{M+1}·z^{M+1} = z^{2M+2}`, and
`z^{M+1}·(z−w)·U_M(c) = (z²−1)·(z^M·U_M(c))` (via `z^{M+1}(z−w) = z^M(z²−zw) ≈ z^M(z²−1)`). -/
theorem prodIdentity_cleared (z w : Q') (hzw : z * w ≈ (1 : Q')) (M : Nat) :
    (z ^ 2 + (-(1 : Q'))) * (z ^ M * U M ((z + w) * HalfPow.half))
      ≈ z ^ (2*(M+1)) + (-(1 : Q')) := by
  have hUgen : (z + (-w)) * U M ((z + w) * HalfPow.half) ≈ z ^ (M+1) + (-(w ^ (M+1))) := TPowerSum.Ugen_eq z w hzw M
  -- Multiply Ugen by z^{M+1}:
  --   z^{M+1}·((z−w)·U_M) ≈ z^{M+1}·(z^{M+1} − w^{M+1})
  have hmul : z ^ (M+1) * ((z + (-w)) * U M ((z + w) * HalfPow.half))
      ≈ z ^ (M+1) * (z ^ (M+1) + (-(w ^ (M+1)))) :=
    mul_eqv_congr_left _ _ _ hUgen
  -- LHS ≈ (z²−1)·(z^M·U_M):
  --   z^{M+1}·((z−w)·U_M) = (z^{M+1}·(z−w))·U_M ; z^{M+1}·(z−w) ≈ z^M·(z²−1).
  have hLHS : z ^ (M+1) * ((z + (-w)) * U M ((z + w) * HalfPow.half))
      ≈ (z ^ 2 + (-(1 : Q'))) * (z ^ M * U M ((z + w) * HalfPow.half)) := by
    -- z^{M+1}·(z+(−w)) ≈ z^M·(z²+(−1))
    have hfac : z ^ (M+1) * (z + (-w)) ≈ z ^ M * (z ^ 2 + (-(1 : Q'))) := by
      -- z^{M+1}·z = z^{M+2} = z^M·z² ; z^{M+1}·(−w) = −(z^{M+1}·w) ≈ −z^M = z^M·(−1)
      refine eqv_trans _ _ _ (mul_add_eqv (z ^ (M+1)) z (-w)) ?_
      refine eqv_symm ?_
      refine eqv_trans _ _ _ (mul_add_eqv (z ^ M) (z ^ 2) (-(1:Q'))) ?_
      refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
      · -- z^M·z² ≈ z^{M+1}·z   (both ≈ z^{M+2})
        refine eqv_trans _ _ _ (zpow_add z M 2) ?_
        -- z^{M+2} ≈ z^{M+1}·z : z^{M+2} = z·z^{M+1} (pow_succ), z^{M+1}·z ≈ z·z^{M+1} (comm)
        have he : (M+2 : Nat) = (M+1)+1 := by omega
        rw [he, Q'.pow_succ]
        exact mul_comm_eqv z (z ^ (M+1))
      · -- z^M·(−1) ≈ z^{M+1}·(−w)
        refine eqv_trans _ _ _ (mul_neg_eqv (z ^ M) 1) ?_
        refine eqv_symm ?_
        refine eqv_trans _ _ _ (mul_neg_eqv (z ^ (M+1)) w) ?_
        refine neg_eqv_congr _ _ ?_
        -- z^{M+1}·w ≈ z^M ≈ z^M·1
        refine eqv_trans _ _ _ (zMw_cancel z w hzw M) ?_
        exact eqv_symm (mul_one_eqv (z ^ M))
    -- assemble: z^{M+1}·((z−w)·U) = (z^{M+1}·(z−w))·U ≈ (z^M·(z²−1))·U = (z²−1)·(z^M·U)
    refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv (z ^ (M+1)) (z + (-w)) (U M ((z + w) * HalfPow.half)))) ?_
    refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ _ hfac) ?_
    -- (z^M·(z²−1))·U ≈ (z²−1)·(z^M·U)
    refine eqv_trans _ _ _ (mul_assoc_eqv (z ^ M) (z ^ 2 + (-(1:Q'))) (U M ((z + w) * HalfPow.half))) ?_
    -- z^M·((z²−1)·U) ≈ (z²−1)·(z^M·U)
    refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ (mul_comm_eqv (z ^ 2 + (-(1:Q'))) (U M ((z + w) * HalfPow.half)))) ?_
    refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv (z ^ M) (U M ((z + w) * HalfPow.half)) (z ^ 2 + (-(1:Q'))))) ?_
    exact mul_comm_eqv (z ^ M * U M ((z + w) * HalfPow.half)) (z ^ 2 + (-(1:Q')))
  -- RHS ≈ z^{2(M+1)} − 1:  z^{M+1}·z^{M+1} = z^{2M+2}; z^{M+1}·w^{M+1} ≈ 1.
  have hRHS : z ^ (M+1) * (z ^ (M+1) + (-(w ^ (M+1))))
      ≈ z ^ (2*(M+1)) + (-(1 : Q')) := by
    refine eqv_trans _ _ _ (mul_add_eqv (z ^ (M+1)) (z ^ (M+1)) (-(w ^ (M+1)))) ?_
    refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
    · -- z^{M+1}·z^{M+1} ≈ z^{2(M+1)}
      refine eqv_trans _ _ _ (zpow_add z (M+1) (M+1)) ?_
      have he : ((M+1)+(M+1) : Nat) = 2*(M+1) := by omega
      rw [he]; exact eqv_refl _
    · -- z^{M+1}·(−w^{M+1}) ≈ −(z^{M+1}·w^{M+1}) ≈ −1
      refine eqv_trans _ _ _ (mul_neg_eqv (z ^ (M+1)) (w ^ (M+1))) ?_
      refine neg_eqv_congr _ _ ?_
      -- z^{M+1}·w^{M+1} ≈ (z·w)^{M+1} ≈ 1^{M+1} ≈ 1
      exact zMpow_wMpow z w hzw (M+1)
  exact eqv_trans _ _ _ (eqv_symm hLHS) (eqv_trans _ _ _ hmul hRHS)

/-- **STEP 1 — the KEY PRODUCT IDENTITY (single-variable shadow).**
For `z·w ≈ 1`, `c = (z+w)·½`: `z^M·U_M(c) ≈ Σ_{j=0}^M z^{2j}`, PROVIDED `z² + (−1)`
is cancellable (here supplied as the hypothesis that the two sides agree once cleared
— which they do by `prodIdentity_cleared` and `geom_telescope`).  We state the cleared
equality of the two candidates, the genuine generating-function content. -/
theorem prodIdentity_geom (z w : Q') (hzw : z * w ≈ (1 : Q')) (M : Nat) :
    (z ^ 2 + (-(1 : Q'))) * (z ^ M * U M ((z + w) * HalfPow.half))
      ≈ (z ^ 2 + (-(1 : Q'))) * geomEven z M :=
  eqv_trans _ _ _ (prodIdentity_cleared z w hzw M)
    (eqv_symm (geom_telescope z M))

/-! ## STEP 2 — the named finite Newton recurrence

`κ M n` is the RHS of the coefficient comparison: `ofInt(−n)` if `n` is even and
`n ≤ 2M`, else `0`.  `Tsum s n` is the finite alternating partial power sum
`s_n + s_{n−2} + ⋯`.  `NewtonRecurrence` packages `2·Tsum s n ≈ κ M n` for
`1 ≤ n ≤ 2M`. -/

/-- The RHS of the Newton coefficient comparison: `−n` if `n` even and `n ≤ 2M`,
else `0`.  (We keep the `n ≤ 2M` cutoff implicit at the call site via the
`NewtonRecurrence` range; here `κ` is the *generating* value `−n·[n even]`.) -/
def kappa (n : Nat) : Q' :=
  if n % 2 = 0 then Q'.ofInt (-(n : Int)) else (0 : Q')

theorem kappa_even (n : Nat) (h : n % 2 = 0) : kappa n = Q'.ofInt (-(n : Int)) := by
  unfold kappa; rw [if_pos h]

theorem kappa_odd (n : Nat) (h : n % 2 = 1) : kappa n = (0 : Q') := by
  unfold kappa; rw [if_neg (by omega)]

/-- The finite alternating partial power sum `Tsum s n = s_n + s_{n−2} + ⋯`
(down to `s_1` for odd `n`, `s_2` for even `n`; excludes `s_0`).  `Tsum s 0 = 0`. -/
def Tsum (s : Nat → Q') : Nat → Q'
  | 0 => (0 : Q')
  | 1 => s 1
  | (n+2) => s (n+2) + Tsum s n

@[simp] theorem Tsum_zero (s : Nat → Q') : Tsum s 0 = 0 := rfl
@[simp] theorem Tsum_one (s : Nat → Q') : Tsum s 1 = s 1 := rfl
theorem Tsum_succ_succ (s : Nat → Q') (n : Nat) :
    Tsum s (n+2) = s (n+2) + Tsum s n := rfl

/-- **STEP 2 — the named finite Newton recurrence** (the residual).  For the
rational power sums `s p = Σ_{k<M} T_p(x_k)`: `2·Tsum s n ≈ κ n` for `1 ≤ n ≤ 2M`.
This is the coefficient comparison of `−z·P'(z) = 2·P(z)·Σ_{p≥1} s_p z^p` against the
product identity `P(z) = Σ_{j=0}^M z^{2j}` (STEP 1).  Closing it from STEP 1 is the
formal-derivative / finite-convolution lemma — the single NAMED-open residual. -/
def NewtonRecurrence (M : Nat) (s : Nat → Q') : Prop :=
  ∀ n, 1 ≤ n → n ≤ 2*M → ((2 : Q') * Tsum s n) ≈ kappa n

/-! ## STEP 3 — the collapse `NewtonRecurrence ⇒ s-values ⇒ OffDiagShift` (general `M`)

By subtracting the recurrence at `n` and `n+2` (same parity), `s_{n+2}` is forced:
`s_{n+2} = 0` (odd `n+2`), `s_{n+2} = −1` (even `n+2`).  Base: `s_1 = 0`, `s_2 = −1`. -/

/-- `½·(2·X) ≈ X`. -/
private theorem half_two_mul (X : Q') : HalfPow.half * ((2 : Q') * X) ≈ X := by
  refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv HalfPow.half 2 X)) ?_
  refine eqv_trans _ _ _ (mul_eqv_congr_right (HalfPow.half * 2) 1 X (by decide)) ?_
  exact one_mul_eqv X

/-- `2·s_1 ≈ 0` ⇒ `s_1 ≈ 0`.  (Since `2·s_1 ≈ κ 1 = 0` and `2X ≈ 0 → X ≈ 0`.) -/
private theorem half_of_two_eqv_zero (X : Q') (h : (2 : Q') * X ≈ (0 : Q')) : X ≈ (0 : Q') := by
  -- ½·(2X) ≈ X and ½·0 ≈ 0
  refine eqv_trans _ _ _ (eqv_symm (half_two_mul X)) ?_
  refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ h) ?_
  exact Q'.mul_zero_eqv HalfPow.half

/-- From `2·X ≈ ofInt(−2)` conclude `X ≈ −1`. -/
private theorem solve_neg_one (X : Q') (h : (2 : Q') * X ≈ Q'.ofInt (-(2 : Int))) :
    X ≈ (-(1 : Q')) := by
  refine eqv_trans _ _ _ (eqv_symm (half_two_mul X)) ?_
  refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ h) ?_
  -- ½·ofInt(−2) ≈ −1
  show HalfPow.half * Q'.ofInt (-(2 : Int)) ≈ (-(1 : Q'))
  show (HalfPow.half * Q'.ofInt (-(2 : Int))).num * ((-(1:Q')).den : Int)
      = (-(1:Q')).num * ((HalfPow.half * Q'.ofInt (-(2 : Int))).den : Int)
  show HalfPow.half.num * (Q'.ofInt (-(2:Int))).num * ((-(1:Q')).den : Int)
      = (-(1:Q')).num * ((HalfPow.half.den * (Q'.ofInt (-(2:Int))).den : Nat) : Int)
  decide

/-- The Newton recurrence "difference" at consecutive same-parity indices:
`2·Tsum s (n+2) − 2·Tsum s n ≈ 2·s_{n+2}` (since `Tsum s (n+2) = s_{n+2} + Tsum s n`). -/
private theorem two_Tsum_diff (s : Nat → Q') (n : Nat) :
    ((2 : Q') * Tsum s (n+2)) + (-((2 : Q') * Tsum s n)) ≈ (2 : Q') * s (n+2) := by
  rw [Tsum_succ_succ]
  -- 2·(s(n+2) + Tsum s n) + (−(2·Tsum s n)) ≈ 2·s(n+2)
  refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ (mul_add_eqv 2 (s (n+2)) (Tsum s n))) ?_
  -- (2·s(n+2) + 2·Tsum s n) + (−(2·Tsum s n)) ≈ 2·s(n+2)
  refine eqv_trans _ _ _ (add_assoc_eqv (2 * s (n+2)) (2 * Tsum s n) (-(2 * Tsum s n))) ?_
  refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (2 * Tsum s n))) ?_
  rw [add_zero']; exact eqv_refl _

/-- `ofInt(−(n+2)) + (−(ofInt(−n))) ≈ ofInt(−2)`. -/
private theorem kappa_even_diff (n : Nat) :
    Q'.ofInt (-((n:Int)+2)) + (-(Q'.ofInt (-(n:Int)))) ≈ Q'.ofInt (-(2 : Int)) := by
  show (Q'.ofInt (-((n:Int)+2)) + (-(Q'.ofInt (-(n:Int))))).num * ((Q'.ofInt (-(2:Int))).den : Int)
      = (Q'.ofInt (-(2:Int))).num * ((Q'.ofInt (-((n:Int)+2)) + (-(Q'.ofInt (-(n:Int))))).den : Int)
  simp only [Cheb.add_num, Cheb.neg_num, add_den_cast, neg_den]
  -- ofInt a has num = a, den = 1
  show ((-((n:Int)+2)) * 1 + (-(-(n:Int))) * 1) * 1 = (-(2:Int)) * (1 * 1)
  omega

/-- `0 + (−0) ≈ 0` over `Q'` (the odd-parity `κ`-difference). -/
private theorem kappa_odd_diff : (0 : Q') + (-(0 : Q')) ≈ (0 : Q') := by decide

/-- `kappa (q+3) = ofInt(−((q+1)+2))` (the even-parity value at `q+3`), used to align
the `κ`-difference with `kappa_even_diff (q+1)`. -/
private theorem kappa_even_q3 (q : Nat) (h : (q+3) % 2 = 0) :
    kappa (q+3) = Q'.ofInt (-(((q:Int)+1)+2)) := by
  rw [kappa_even (q+3) h]
  have : (((q+3 : Nat)) : Int) = ((q:Int)+1)+2 := by push_cast; omega
  rw [this]

/-- `kappa (q+1) = ofInt(−(q+1))` when `q+1` even. -/
private theorem kappa_even_q1 (q : Nat) (h : (q+1) % 2 = 0) :
    kappa (q+1) = Q'.ofInt (-((q:Int)+1)) := by
  rw [kappa_even (q+1) h]
  have : (((q+1 : Nat)) : Int) = (q:Int)+1 := by push_cast; omega
  rw [this]

/-- The value of `s p` forced by `NewtonRecurrence`, expressed via the difference of
two recurrence instances at `p = (n)+2` and `n`.  `2·s(n+2) ≈ κ(n+2) + (−κ n)`. -/
private theorem two_sval (M : Nat) (s : Nat → Q') (hN : NewtonRecurrence M s)
    (n : Nat) (hn1 : 1 ≤ n) (hnM : n+2 ≤ 2*M) :
    (2 : Q') * s (n+2) ≈ kappa (n+2) + (-(kappa n)) := by
  have hrecB := hN (n+2) (by omega) hnM
  have hrecA := hN n hn1 (by omega)
  -- 2·s(n+2) ≈ 2·Tsum s (n+2) − 2·Tsum s n ≈ κ(n+2) − κ n
  refine eqv_trans _ _ _ (eqv_symm (two_Tsum_diff s n)) ?_
  exact Cheb.add_eqv_congr _ _ _ _ hrecB (neg_eqv_congr _ _ hrecA)

/-- **STEP 3 (values), general `M`.**  `NewtonRecurrence` forces, for `1 ≤ p ≤ 2M`:
`s p ≈ 0` (`p` odd) and `s p ≈ −1` (`p` even). -/
theorem sval_parity (M : Nat) (s : Nat → Q') (hN : NewtonRecurrence M s) :
    ∀ p, 1 ≤ p → p ≤ 2*M →
      (p % 2 = 1 → s p ≈ (0 : Q')) ∧ (p % 2 = 0 → s p ≈ (-(1 : Q'))) := by
  intro p
  match p with
  | 0 => intro h _; omega
  | 1 =>
      intro _ hpM
      refine ⟨fun _ => ?_, fun h => by omega⟩
      have hrec := hN 1 (by omega) hpM
      rw [Tsum_one, kappa_odd 1 (by decide)] at hrec
      exact half_of_two_eqv_zero (s 1) hrec
  | 2 =>
      intro _ hpM
      refine ⟨fun h => by omega, fun _ => ?_⟩
      have hrec := hN 2 (by omega) hpM
      rw [Tsum_succ_succ, Tsum_zero, kappa_even 2 (by decide)] at hrec
      have hrec' : (2 : Q') * s 2 ≈ Q'.ofInt (-(2 : Int)) := by
        refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ ?_) hrec
        rw [add_zero']; exact eqv_refl _
      exact solve_neg_one (s 2) hrec'
  | (q+3) =>
      intro _ hpM
      -- p = (q+1)+2 ; use two_sval with n = q+1.
      have hval : (2 : Q') * s (q+3) ≈ kappa (q+3) + (-(kappa (q+1))) := by
        have h := two_sval M s hN (q+1) (by omega) (by omega)
        -- (q+1)+2 = q+3
        have he : (q+1)+2 = q+3 := by omega
        rw [he] at h; exact h
      refine ⟨fun hodd => ?_, fun heven => ?_⟩
      · -- q+3 odd ⇒ q+1 odd ⇒ both κ = 0 ⇒ 2·s ≈ 0 ⇒ s ≈ 0
        have hq1 : (q+1) % 2 = 1 := by omega
        have hz : (2 : Q') * s (q+3) ≈ (0 : Q') := by
          refine eqv_trans _ _ _ hval ?_
          rw [kappa_odd (q+3) hodd, kappa_odd (q+1) hq1]
          exact kappa_odd_diff
        exact half_of_two_eqv_zero (s (q+3)) hz
      · -- q+3 even ⇒ q+1 even ⇒ κ-diff ≈ ofInt(−2) ⇒ s ≈ −1
        have hq1 : (q+1) % 2 = 0 := by omega
        have hd : (2 : Q') * s (q+3) ≈ Q'.ofInt (-(2 : Int)) := by
          refine eqv_trans _ _ _ hval ?_
          rw [kappa_even_q3 q heven, kappa_even_q1 q hq1]
          exact kappa_even_diff (q+1)
        exact solve_neg_one (s (q+3)) hd

/-- **STEP 3 (shift), general `M`.**  `NewtonRecurrence` forces `s p ≈ s (p+2)` for
`0 < p ≤ M−1` (same parity, both `0` or both `−1`).  The off-diagonal collapse on the
rational power sums. -/
theorem sShift_of_newton (M : Nat) (s : Nat → Q') (hN : NewtonRecurrence M s) :
    ∀ p, 0 < p → p ≤ M - 1 → s p ≈ s (p+2) := by
  intro p hp0 hpM
  -- range: p+2 ≤ M+1 ≤ 2M for M ≥ 1 ; p ≥ 1.  Both in [1, 2M].
  have hM1 : 1 ≤ M := by omega
  have hp_le : p ≤ 2*M := by omega
  have hp2_le : p + 2 ≤ 2*M := by omega
  obtain ⟨hpodd, hpeven⟩ := sval_parity M s hN p (by omega) hp_le
  obtain ⟨hp2odd, hp2even⟩ := sval_parity M s hN (p+2) (by omega) hp2_le
  -- p and p+2 have the same parity.
  rcases Nat.mod_two_eq_zero_or_one p with hpe | hpo
  · -- p even
    have hp2e : (p+2) % 2 = 0 := by omega
    exact eqv_trans _ _ _ (hpeven hpe) (eqv_symm (hp2even hp2e))
  · -- p odd
    have hp2o : (p+2) % 2 = 1 := by omega
    exact eqv_trans _ _ _ (hpodd hpo) (eqv_symm (hp2odd hp2o))

/-! ## Lifting to `Sj` / `OffDiagShift` and chaining to the bridge

The rational power sums are `s p = Σ_{k<M} T_p(node k)`.  `Sj (fromQNodes M node) p ≈
ofQ'(s p)` (`PowerSumCollapse.Sj_fromQNodes`), so the `Q'`-level shift `s p ≈ s (p+2)`
lifts to the `CReal`-level `OffDiagShift`. -/

/-- The rational power sums of a `RootedNodes M` datum. -/
def sval {M : Nat} (D : RootedNodes M) (p : Nat) : Q' :=
  RationalTail.finSum (fun k => T p (D.node k)) M

/-- **STEP 3 capstone, general `M`** — `NewtonRecurrence` on the rational power sums
⇒ `RootPowerSumBridge.OffDiagShift D` (`S_p ≈ S_{p+2}`, `CReal` level). -/
theorem offDiagShift_of_newton {M : Nat} (D : RootedNodes M)
    (hN : NewtonRecurrence M (sval D)) : RootPowerSumBridge.OffDiagShift D := by
  intro p hp0 hpM
  -- Sj D.toData p = Sj (fromQNodes M D.node) p ≈ ofQ'(sval D p) ≈ ofQ'(sval D (p+2)) ≈ Sj … (p+2)
  refine CReal.Equiv.trans (PowerSumCollapse.Sj_fromQNodes M D.node p) ?_
  refine CReal.Equiv.symm (CReal.Equiv.trans (PowerSumCollapse.Sj_fromQNodes M D.node (p+2)) ?_)
  refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
  show (RationalTail.finSum (fun k => T (p+2) (D.node k)) M).eqv
    (RationalTail.finSum (fun k => T p (D.node k)) M)
  exact eqv_symm (sShift_of_newton M (sval D) hN p hp0 hpM)

/-- **The bridge from `NewtonRecurrence`** — `S_2 = −1` (proved general `M`) together
with `NewtonRecurrence` yields `TPowerSum.RootPowerSumBridge D.toData`. -/
theorem bridge_of_newton {M : Nat} (D : RootedNodes M)
    (hN : NewtonRecurrence M (sval D)) :
    TPowerSum.RootPowerSumBridge D.toData :=
  RootPowerSumBridge.bridge_of_offdiag D (offDiagShift_of_newton D hN)

/-- **`PowerSumCollapse.TPowerSum` from `NewtonRecurrence`** (general `M`). -/
theorem tPowerSum_of_newton {M : Nat} (D : RootedNodes M)
    (hN : NewtonRecurrence M (sval D)) :
    PowerSumCollapse.TPowerSum D.toData :=
  RootPowerSumBridge.tPowerSum_from_offdiag D (offDiagShift_of_newton D hN)

/-- **The all-order Gram-PSD residual from `NewtonRecurrence`** (general `M`): the
`ChebOrthogonality.PowerSumCollapse` residual on the forgotten node datum.  This is
the input consumed (via the moment route) by
`ChebyshevQuadPSD.momentSquarePos_via_nodes` to close Wall-1 — provided
`NewtonRecurrence` is supplied. -/
theorem gram_psd_all_orders {M : Nat} (D : RootedNodes M)
    (hN : NewtonRecurrence M (sval D)) :
    ChebOrthogonality.PowerSumCollapse D.toData.toU :=
  PowerSumCollapse.powerSumCollapse_of_TPowerSum D.toData (tPowerSum_of_newton D hN)

/-! ## The `M = 2` instance (rational nodes `±1/2`)

`NewtonRecurrence 2 (sval rootedNodes2)` is the closed range `1 ≤ n ≤ 4`; each
`2·Tsum s n ≈ κ n` is a closed `Q'` computation on `T_n(±1/2)`, discharged by
`decide`.  This reproduces the off-diagonal shift through the general STEP-3 route. -/

/-- `sval rootedNodes2 j = finSum (T_j ∘ node2) 2` (definitional unfold of `sval`). -/
private theorem sval2_eq (j : Nat) :
    sval rootedNodes2 j = RationalTail.finSum (fun k => T j (ChebOrthogonality.node2 k)) 2 := rfl

/-- `NewtonRecurrence` at `M = 2`, by `decide` on the four closed instances. -/
theorem newtonRecurrence2 : NewtonRecurrence 2 (sval rootedNodes2) := by
  intro n hn1 hnM
  -- 2M = 4 ; n ∈ {1,2,3,4}.  Each is a closed Q' identity.
  match n, hn1, hnM with
  | 0, h, _ => exact absurd h (by omega)
  | 1, _, _ =>
      -- n = 1 : 2·Tsum s 1 = 2·s 1 ≈ κ 1 = 0
      show ((2 : Q') * Tsum (sval rootedNodes2) 1) ≈ kappa 1
      rw [Tsum_one, kappa_odd 1 (by decide), sval2_eq 1]
      decide
  | 2, _, _ =>
      show ((2 : Q') * Tsum (sval rootedNodes2) 2) ≈ kappa 2
      rw [Tsum_succ_succ, Tsum_zero, kappa_even 2 (by decide), sval2_eq 2]
      decide
  | 3, _, _ =>
      show ((2 : Q') * Tsum (sval rootedNodes2) 3) ≈ kappa 3
      rw [show (3:Nat) = 1+2 from rfl, Tsum_succ_succ, Tsum_one, kappa_odd 3 (by decide),
        sval2_eq 3, sval2_eq 1]
      decide
  | 4, _, _ =>
      show ((2 : Q') * Tsum (sval rootedNodes2) 4) ≈ kappa 4
      rw [show (4:Nat) = 2+2 from rfl, Tsum_succ_succ, Tsum_succ_succ, Tsum_zero,
        kappa_even 4 (by decide), sval2_eq 4, sval2_eq 2]
      decide
  | (n+5), _, h => exact absurd h (by omega)

/-- **The off-diagonal shift at `M = 2`, via the general STEP-3 route** from
`newtonRecurrence2`. -/
theorem offDiagShift2_via_newton : RootPowerSumBridge.OffDiagShift rootedNodes2 :=
  offDiagShift_of_newton rootedNodes2 newtonRecurrence2

/-- **The full `RootPowerSumBridge` at `M = 2`, via `NewtonRecurrence`** — the general
diagonal `S_2 = −1` and the STEP-3 off-diagonal shift. -/
theorem rootBridge2_via_newton : TPowerSum.RootPowerSumBridge rootedNodes2.toData :=
  bridge_of_newton rootedNodes2 newtonRecurrence2

/-- **`PowerSumCollapse.TPowerSum` at `M = 2`, via `NewtonRecurrence`** (end-to-end
through the STEP-1/2/3 architecture). -/
theorem tPowerSum2_via_newton : PowerSumCollapse.TPowerSum rootedNodes2.toData :=
  tPowerSum_of_newton rootedNodes2 newtonRecurrence2

end YMGap.Continuum.OffDiagShift

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only via reused `omega`/`Nat`/`Int` helpers).  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no `decide` on a non-decidable `Prop`. -/

#print axioms YMGap.Continuum.OffDiagShift.geom_telescope
#print axioms YMGap.Continuum.OffDiagShift.prodIdentity_cleared
#print axioms YMGap.Continuum.OffDiagShift.prodIdentity_geom
#print axioms YMGap.Continuum.OffDiagShift.sval_parity
#print axioms YMGap.Continuum.OffDiagShift.sShift_of_newton
#print axioms YMGap.Continuum.OffDiagShift.offDiagShift_of_newton
#print axioms YMGap.Continuum.OffDiagShift.bridge_of_newton
#print axioms YMGap.Continuum.OffDiagShift.tPowerSum_of_newton
#print axioms YMGap.Continuum.OffDiagShift.gram_psd_all_orders
#print axioms YMGap.Continuum.OffDiagShift.newtonRecurrence2
#print axioms YMGap.Continuum.OffDiagShift.offDiagShift2_via_newton
#print axioms YMGap.Continuum.OffDiagShift.rootBridge2_via_newton
#print axioms YMGap.Continuum.OffDiagShift.tPowerSum2_via_newton
