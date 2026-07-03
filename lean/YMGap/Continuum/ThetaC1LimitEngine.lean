/-
# The CReal-truncation C¹-limit engine (`fdDerivDataC_of_unif_M`)

This module supplies the reusable analytic engine that turns a family of
already-`CReal` truncation finite-difference derivatives `FDDerivDataC F_M d_M θ`
— together with a uniform-in-`M` finite-difference modulus, pointwise convergence
`F_M → Flim`, and derivative convergence `d_M → dlim` — into a single
`FDDerivDataC Flim dlim θ` for the `CReal` limit `Flim`.

It is the `CReal`/`leRat`-level mirror of `TsumDeriv.fdDeriv_of_unif` (the `Q'`
Bishop C¹-uniform-limit theorem).  The genuine analytic content — the four-piece
telescope, the `q/4` bookkeeping, and the infinitesimal cancellation — is REUSED
verbatim from the already-closed `Q'` engine through:

* `TsumDeriv.fdRem_telescope` — the four-piece telescoping identity over `Q'`;
* `TsumDeriv.four_q_eqv` — the `(((q|h|+q|h|)+q|h|)+q|h|) ≈ ε|h|` bookkeeping;
* `TsumDeriv.fdRemC_approx` — `(fdRemC F d θ h).approx n = fdRem …` (index-wise);
* `CReal.leRat_add`, `CReal.leRat_of_equiv`, `CReal.leRat_mono` — the `leRat` layer;
* `CReal.abs_equiv_congr`, `SumOfSquares.Equiv_of_approx_eqv` — the setoid bridge.

The five new primitives are all small and index-wise:

* `leRat_abs_add` — the triangle inequality at the `leRat` layer (load-bearing);
* `leRat_abs_mul_ofQ'` — the `P4` scaler `|d·(ofQ' h)| ≤ |d|·|h|` (division-free,
  via `CReal.exists_mul_le`);
* `leRat_abs_sub_comm` — the `P3` sign flip `|x⊖y| = |y⊖x|` at `leRat`;
* `fdRemC_telescope` — the `CReal.Equiv` telescope, reducing index-wise to
  `TsumDeriv.fdRem_telescope`;
* `C1InputsC` — the bundled `CReal` engine hypotheses.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

Every declaration reports `[propext]` / `[propext, Quot.sound]` only.  No
`Classical.*`, no `native_decide`, no `sorry`, no custom axiom.  All witnesses are
`Type`-level data.
-/

import YMGap.Continuum.TsumDeriv
import YMGap.Constructive.CRealExp
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.ThetaC1LimitEngine

open YMGap.Constructive

/-! ## H1–H3 : the three small `leRat` primitives -/

/-- **`leRat` transfers along an index-wise `≤`.**  If `u.approx n ≤ w.approx n`
for every `n` and `leRat w b`, then `leRat u b`.  (The trivial monotonicity used to
lift the triangle inequality from the `add`-of-abs to the `abs`-of-add.) -/
theorem leRat_of_approx_le {u w : CReal} {b : Q'}
    (hle : ∀ n, u.approx n ≤ w.approx n) (hw : CReal.leRat w b) :
    CReal.leRat u b := by
  intro ε hε
  obtain ⟨N, hN⟩ := hw ε hε
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (hle n) (hN n hn)⟩

/-- **H1 — the triangle inequality at the `leRat` layer.**  From `|x|`'s limit
`≤ a` and `|y|`'s limit `≤ b`, `|x + y|`'s limit is `≤ a + b`.  Index-wise the
`Q'` triangle inequality `|x_n + y_n| ≤ |x_n| + |y_n|` puts `abs (add x y)`
below `add (abs x) (abs y)`, then `leRat_add` sums the two rational bounds. -/
theorem leRat_abs_add {x y : CReal} {a b : Q'}
    (hx : CReal.leRat (CReal.abs x) a) (hy : CReal.leRat (CReal.abs y) b) :
    CReal.leRat (CReal.abs (CReal.add x y)) (a + b) := by
  refine leRat_of_approx_le
    (u := CReal.abs (CReal.add x y))
    (w := CReal.add (CReal.abs x) (CReal.abs y)) ?_ (CReal.leRat_add hx hy)
  intro n
  -- (abs (add x y)).approx n = Q'.abs (x_n + y_n) ≤ Q'.abs x_n + Q'.abs y_n
  --   = (add (abs x) (abs y)).approx n
  show Q'.abs (x.approx n + y.approx n)
      ≤ Q'.abs (x.approx n) + Q'.abs (y.approx n)
  exact Q'.abs_add_le' (x.approx n) (y.approx n)

/-- **H2 — the `P4` scaler.**  From `|x|`'s limit `≤ a` and `0 < |h|`,
`|x · (ofQ' h)|`'s limit is `≤ a · |h|`.  Division-free: `CReal.exists_mul_le`
supplies `s > 0` with `|h|·s ≤ tol`, and index-wise
`|x_n · h| ≤ |x_n|·|h| ≤ (a+s)·|h| = a·|h| + s·|h| ≤ a·|h| + tol`. -/
theorem leRat_abs_mul_ofQ' {x : CReal} {a h : Q'}
    (hx : CReal.leRat (CReal.abs x) a) (hh : (0 : Q') < Q'.abs h) :
    CReal.leRat (CReal.abs (CReal.mul x (CReal.ofQ' h))) (a * Q'.abs h) := by
  intro tol htol
  obtain ⟨s, hs_pos, hs⟩ := CReal.exists_mul_le (Q'.le_of_lt hh) htol  -- |h|·s ≤ tol
  obtain ⟨N, hN⟩ := hx s hs_pos                                        -- |x_n| ≤ a + s
  refine ⟨N, fun n hn => ?_⟩
  -- goal: (abs (mul x (ofQ' h))).approx n ≤ a·|h| + tol, i.e. |x_n · h| ≤ …
  have h1 : Q'.abs (x.approx n * h) ≤ Q'.abs (x.approx n) * Q'.abs h :=
    ExpNeg.abs_mul_le (x.approx n) h
  have h2 : Q'.abs (x.approx n) * Q'.abs h ≤ (a + s) * Q'.abs h :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (hN n hn) (Q'.abs_nonneg h)
  have h3 : ((a + s) * Q'.abs h).eqv (a * Q'.abs h + s * Q'.abs h) :=
    Q'.add_mul_eqv a s (Q'.abs h)
  have h4 : s * Q'.abs h ≤ tol :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv s (Q'.abs h))) hs
  have h5 : a * Q'.abs h + s * Q'.abs h ≤ a * Q'.abs h + tol :=
    Q'.add_le_add_left (a * Q'.abs h) (s * Q'.abs h) tol h4
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ h2 (Q'.le_trans' _ _ _ (Q'.le_of_eqv h3) h5))

/-- **H3 — the `P3` sign flip.**  `|x ⊖ y|` and `|y ⊖ x|` have the same limit, so a
`leRat` on one transfers to the other.  Index-wise this is `Q'.abs_sub_comm`. -/
theorem leRat_abs_sub_comm {x y : CReal} {c : Q'}
    (h : CReal.leRat (CReal.abs (CReal.add x (CReal.neg y))) c) :
    CReal.leRat (CReal.abs (CReal.add y (CReal.neg x))) c := by
  refine CReal.leRat_of_equiv ?_ h
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  -- (abs (add y (neg x))).approx n = Q'.abs (y_n + -x_n) ≈ Q'.abs (x_n + -y_n)
  show (Q'.abs (y.approx n + -(x.approx n))).eqv (Q'.abs (x.approx n + -(y.approx n)))
  exact ExpNeg.abs_sub_comm (y.approx n) (x.approx n)

/-! ## H4 : the `CReal.Equiv` four-piece telescope -/

/-- **H4 — the `CReal` four-piece telescoping identity.**  The `CReal` analogue of
`TsumDeriv.fdRem_telescope`: at every approximation index `n` both sides reduce
(index-wise, all `rfl`) to the `Q'` telescope of the `n`-th approximations, so
`SumOfSquares.Equiv_of_approx_eqv` delivers the full `Equiv`.

    fdRemC Flim dlim θ h  ≈
      ((( (Flim(θ+h) ⊖ F_M(θ+h))            -- P1
            + fdRemC (F_M) (d_M) θ h )        -- P2
          + (F_M θ ⊖ Flim θ))                 -- P3
        + (d_M ⊖ dlim)·(ofQ' h))              -- P4
-/
theorem fdRemC_telescope (Flim : Q' → CReal) (F : Nat → Q' → CReal)
    (d : Nat → CReal) (dlim : CReal) (θ h : Q') (M : Nat) :
    CReal.Equiv (TsumDeriv.fdRemC Flim dlim θ h)
      (CReal.add
        (CReal.add
          (CReal.add (CReal.add (Flim (θ + h)) (CReal.neg (F M (θ + h))))
                     (TsumDeriv.fdRemC (F M) (d M) θ h))
          (CReal.add (F M θ) (CReal.neg (Flim θ))))
        (CReal.mul (CReal.add (d M) (CReal.neg dlim)) (CReal.ofQ' h))) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  -- both sides' n-th approx reduce (rfl) to the Q' telescope of the n-th approxes
  exact TsumDeriv.fdRem_telescope (fun t => (Flim t).approx n)
    (fun M t => (F M t).approx n) (fun M _ => (d M).approx n)
    (fun _ => dlim.approx n) θ h M

/-! ## H5 : the bundled `CReal` engine hypotheses -/

/-- **H5 — `CReal` engine inputs.**  The `CReal` analogue of `TsumDeriv.C1Inputs`.
`fdboundC` is the honest uniform-in-`M` finite-difference modulus (the source of
the per-`M` `FDDerivDataC F_M d_M θ`, exactly as the `Q'` engine takes the family's
common modulus `fdbound`).  `conv` is uniform in the evaluation point `p`, so a
single `Ncut` covers both `θ` and `θ+h`. -/
structure C1InputsC (F : Nat → Q' → CReal) (Flim : Q' → CReal)
    (d : Nat → CReal) (dlim : CReal) (θ : Q') : Type where
  /-- The pointwise (uniform-in-point) convergence modulus `F_M → Flim`. -/
  Ncut : Q' → Nat
  /-- Past `Ncut ε`, `Flim p ⊖ F_M p` has limit `≤ ε`, at EVERY point `p`. -/
  conv : ∀ ε : Q', (0 : Q') < ε → ∀ M : Nat, Ncut ε ≤ M → ∀ p : Q',
    CReal.leRat (CReal.abs (CReal.add (Flim p) (CReal.neg (F M p)))) ε
  /-- The derivative-convergence modulus `d_M → dlim`. -/
  Mg : Q' → Nat
  /-- Past `Mg ε`, `d_M ⊖ dlim` has limit `≤ ε`. -/
  dconv : ∀ ε : Q', (0 : Q') < ε → ∀ M : Nat, Mg ε ≤ M →
    CReal.leRat (CReal.abs (CReal.add (d M) (CReal.neg dlim))) ε
  /-- The common finite-difference modulus (family equicontinuity at `θ`). -/
  delStar : Q' → Q'
  /-- `delStar` is positive for positive tolerance. -/
  delStar_pos : ∀ ε : Q', (0 : Q') < ε → (0 : Q') < delStar ε
  /-- The stage past which the common modulus is valid. -/
  mStar : Q' → Nat
  /-- For `M ≥ mStar ε'`, `F_M` has the cleared `CReal` finite-difference bound
  with `delStar`, uniformly in `M`. -/
  fdboundC : ∀ ε' : Q', (0 : Q') < ε' → ∀ M : Nat, mStar ε' ≤ M →
    ∀ h : Q', (0 : Q') < Q'.abs h → Q'.abs h ≤ delStar ε' →
      CReal.leRat (CReal.abs (TsumDeriv.fdRemC (F M) (d M) θ h)) (ε' * Q'.abs h)

/-! ## Main : the CReal-truncation C¹-limit engine -/

/-- **THE CReal-TRUNCATION C¹-LIMIT ENGINE (constructive, data-carrying, CLOSED).**

From `C1InputsC`, the `CReal` limit `Flim` has `CReal`-valued finite-difference
derivative `dlim` at `θ`, with explicit modulus `δ ε := delStar (ε/4)`.  The proof
is the direct `leRat` port of `TsumDeriv.fdDeriv_of_unif`: pick `M` past `mStar`,
`Mg`, and the (single, uniform-in-point) `Ncut`; the four pieces are each
`≤ (ε/4)·|h|`, summed by the `leRat` triangle inequality, transported onto
`fdRemC Flim dlim θ h` through the `CReal.Equiv` telescope, and folded to `ε·|h|`
by the `q/4` bookkeeping. -/
def fdDerivDataC_of_unif_M {F : Nat → Q' → CReal} {Flim : Q' → CReal}
    {d : Nat → CReal} {dlim : CReal} {θ : Q'}
    (H : C1InputsC F Flim d dlim θ) : TsumDeriv.FDDerivDataC Flim dlim θ where
  δ ε := H.delStar (HalfPow.half * (HalfPow.half * ε))
  δ_pos ε hε := H.delStar_pos _
    (ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε))
  bound := by
    intro ε hε h hhpos hhle
    let q : Q' := HalfPow.half * (HalfPow.half * ε)
    have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
    have hqh_pos : (0 : Q') < q * Q'.abs h := TsumDeriv.Q'.mul_pos' hqpos hhpos
    -- the stage M past all three moduli
    let Mlevel : Nat :=
      max (H.mStar q) (max (H.Mg q) (H.Ncut (q * Q'.abs h)))
    have hMstar : H.mStar q ≤ Mlevel := Nat.le_max_left _ _
    have hMg : H.Mg q ≤ Mlevel :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hNcut : H.Ncut (q * Q'.abs h) ≤ Mlevel :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    -- P1: |Flim(θ+h) ⊖ F_M(θ+h)| limit ≤ q·|h|
    have hP1 : CReal.leRat
        (CReal.abs (CReal.add (Flim (θ + h)) (CReal.neg (F Mlevel (θ + h)))))
        (q * Q'.abs h) :=
      H.conv (q * Q'.abs h) hqh_pos Mlevel hNcut (θ + h)
    -- P2: the M-th cleared CReal finite-difference remainder
    have hP2 : CReal.leRat
        (CReal.abs (TsumDeriv.fdRemC (F Mlevel) (d Mlevel) θ h)) (q * Q'.abs h) :=
      H.fdboundC q hqpos Mlevel hMstar h hhpos hhle
    -- P3: |F_M θ ⊖ Flim θ| limit ≤ q·|h|  (sign-flipped conv at θ)
    have hP3 : CReal.leRat
        (CReal.abs (CReal.add (F Mlevel θ) (CReal.neg (Flim θ)))) (q * Q'.abs h) :=
      leRat_abs_sub_comm (H.conv (q * Q'.abs h) hqh_pos Mlevel hNcut θ)
    -- P4: |(d_M ⊖ dlim)·(ofQ' h)| limit ≤ q·|h|
    have hP4 : CReal.leRat
        (CReal.abs (CReal.mul (CReal.add (d Mlevel) (CReal.neg dlim)) (CReal.ofQ' h)))
        (q * Q'.abs h) :=
      leRat_abs_mul_ofQ' (H.dconv q hqpos Mlevel hMg) hhpos
    -- combine the four pieces via the leRat triangle inequality
    have hsum12 := leRat_abs_add hP1 hP2
    have hsum123 := leRat_abs_add hsum12 hP3
    have hsum1234 := leRat_abs_add hsum123 hP4
    -- transport onto fdRemC Flim dlim θ h via the CReal.Equiv telescope
    have htel := fdRemC_telescope Flim F d dlim θ h Mlevel
    have hgoal : CReal.leRat (CReal.abs (TsumDeriv.fdRemC Flim dlim θ h))
        (((q * Q'.abs h + q * Q'.abs h) + q * Q'.abs h) + q * Q'.abs h) :=
      CReal.leRat_of_equiv (CReal.abs_equiv_congr htel) hsum1234
    -- fold the four-term rational bound down to ε·|h|
    exact CReal.leRat_mono hgoal (Q'.le_of_eqv (TsumDeriv.four_q_eqv ε h))

end YMGap.Continuum.ThetaC1LimitEngine

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaC1LimitEngine.leRat_of_approx_le
#print axioms YMGap.Continuum.ThetaC1LimitEngine.leRat_abs_add
#print axioms YMGap.Continuum.ThetaC1LimitEngine.leRat_abs_mul_ofQ'
#print axioms YMGap.Continuum.ThetaC1LimitEngine.leRat_abs_sub_comm
#print axioms YMGap.Continuum.ThetaC1LimitEngine.fdRemC_telescope
#print axioms YMGap.Continuum.ThetaC1LimitEngine.fdDerivDataC_of_unif_M
