/-
Closing core ④'s last carried residual: inhabiting `SpectralDiffBound` from the
standard OS / Peter–Weyl spectral data plus a per-mode Bernstein uniform-Cauchy
datum.

# What this module delivers (GREEN, from named Type-level inputs)

`Continuum/PolyImageDistCertClose.lean` reduced the `PolyImageDistCert` residual
of the continuous functional calculus to ONE finite-mode datum
`SpectralDiffBound SL LT pseq xc` (its `rcbound` + `vanish` fields feed, through
the already-GREEN `polyImageDistCertOfSpectralDiffBound`, into
`polyImageCauchyOfCert` / `img`).  This module BUILDS that datum from the honest
carried remainder, bundled as `SpectralDiffInputs`:

  * **`SQ`** — the scalar-square laws (consumed by `polyApplyLinCauchy_diff`);
  * **`Br`** — the finite diagonal spectral resolution of the FORMED operator;
  * **`PN`** — the per-pair diagonal Parseval carrier (only `.normDiag` is used;
    the uniform bound `M` / `supBound` are supplied here as the finite spectral
    max `specMaxAux`, NOT taken from `PN`);
  * **`Umode`** — the per-mode `SpectralUnifCauchy` (the Bernstein/Weierstrass
    uniform-Cauchy modulus at each resolved eigenvalue `Br.lam i`);
  * **`V` / `hV`** — the fixed per-point self-inner bound
    `⟨⟦xc⟧,⟦xc⟧⟩ ≤ V` (resolving the constant-vs-‖x‖² mismatch).

Everything downstream of `SpectralDiffInputs` is PROVED here:

  * **`rcbound`** — the difference-form self-inner bound.  Chain: the difference
    identity (`polyApplyLinCauchy_diff`) → diagonal Parseval (`PN.normDiag`) →
    the diagonal polynomial norm bound (`polyNormBound`, at the finite spectral
    max `Msp = specMaxAux (dN …) Br.k`) → fold in `‖x‖²` via `RCscale_mono` and
    the per-point bound `hV` → the constant `M2` rewrite `s·⟦ofQ' V⟧ = ⟦ofQ'(s·V)⟧`.
  * **`vanish`** — the uniform vanishing.  With `δ ε` an Archimedean split
    (`deltaOf`, `δ·δ·V ≤ ε`), each squared spectral gap `dN … i` is `≤ (δ ε)²`
    by the per-mode two-sided Bernstein bound fed through `M1` (sq-of-abs), so the
    finite max `Msp ≤ (δ ε)²` and `Bq = Msp·V ≤ ε`.

# Honest scope — the carried Type-level residual

`SpectralDiffInputs` is the exact standard OS / Peter–Weyl spectral data (the
diagonal resolution + arbitrary-`P` Parseval `normDiag`, and the per-mode
Bernstein `SpectralUnifCauchy`), together with the one per-point norm bound.
None of these is provable at this abstraction level; they are the honest inputs.
Nothing downstream is faked.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.PolyImageDistCertClose
import YMGap.Continuum.ContinuousFunctionalCalculusForm

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.ContinuousTransferCalculus
open YMGap.Continuum.ContinuousFunctionalCalculusForm
open YMGap.Continuum.ContinuousFCCarrierLimit
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.WilsonContinuousFC
open YMGap.Continuum.PolyImageCauchySupplier
open YMGap.Continuum.PolyImageDistCertClose

namespace YMGap.Continuum.SpectralDiffBoundClose

/-! ## 1. Two micro-lemmas -/

/-- **M2 — the constant `RCscale` rewrite.**  `s·⟦ofQ' V⟧ = ⟦ofQ'(s·V)⟧`, via
`RCscale_mk` and the multiplicativity of `ofQ'`. -/
theorem RCscale_ofQ' (s v : Q') :
    CReal.RCscale s (Quotient.mk CReal.crealSetoid (CReal.ofQ' v))
      = Quotient.mk CReal.crealSetoid (CReal.ofQ' (s * v)) := by
  rw [CReal.RCscale_mk]
  exact Quotient.sound (CReal.Equiv.symm (CRealAlg.ofQ'_mul s v))

/-! ## 2. The `Nat`-valued running maximum (the vanishing modulus fold) -/

/-- Running `Nat`-maximum of `f 0, …, f (n−1)` (`0` for the empty prefix). -/
def natMaxAux (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.max (natMaxAux f n) (f n)

/-- Every entry of the prefix is at or below the running maximum. -/
theorem natMaxAux_ge (f : Nat → Nat) :
    ∀ N i, i < N → f i ≤ natMaxAux f N
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | N + 1, i, hi => by
      show f i ≤ Nat.max (natMaxAux f N) (f N)
      rcases Nat.lt_or_ge i N with h | h
      · exact Nat.le_trans (natMaxAux_ge f N i h) (Nat.le_max_left _ _)
      · have hiN : i = N := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) h
        subst hiN; exact Nat.le_max_right _ _

/-! ## 3. The Archimedean `δ`-selector with `δ·δ·V ≤ ε` -/

/-- `δ ε := ε · recip(ε + (V + 1))`.  Manifestly positive, `≤ 1`, and `δ²·V ≤ ε`. -/
def deltaOf (V ε : Q') : Q' := ε * Q'.recip (ε + (V + 1))

theorem deltaOf_pos (V ε : Q') (hε : (0 : Q') < ε) : (0 : Q') < deltaOf V ε :=
  Q'.mul_pos hε (Q'.recip_pos _)

theorem deltaOf_le_one (V ε : Q') (hε : (0 : Q') < ε) (hV0 : (0 : Q') ≤ V) :
    deltaOf V ε ≤ (1 : Q') := by
  have hVp1 : (0 : Q') ≤ V + 1 :=
    Q'.le_trans' 0 V (V + 1) hV0 (Q'.add_le_self_of_nonneg V 1 (by decide))
  have hw : (0 : Q') < ε + (V + 1) := Q'.pos_add_nonneg hε hVp1
  have hεw : ε ≤ ε + (V + 1) := Q'.add_le_self_of_nonneg ε (V + 1) hVp1
  have step : ε * Q'.recip (ε + (V + 1)) ≤ (ε + (V + 1)) * Q'.recip (ε + (V + 1)) :=
    Q'.mul_le_mul_of_nonneg_right ε (ε + (V + 1)) (Q'.recip (ε + (V + 1))) hεw
      (Q'.le_of_lt (Q'.recip_pos _))
  exact le_of_le_eqv step (Q'.mul_recip_eqv (ε + (V + 1)) hw)

theorem deltaOf_sq_mul_le (V ε : Q') (hε : (0 : Q') < ε) (hV0 : (0 : Q') ≤ V) :
    deltaOf V ε * deltaOf V ε * V ≤ ε := by
  have hVp1 : (0 : Q') ≤ V + 1 :=
    Q'.le_trans' 0 V (V + 1) hV0 (Q'.add_le_self_of_nonneg V 1 (by decide))
  have hw : (0 : Q') < ε + (V + 1) := Q'.pos_add_nonneg hε hVp1
  have hδ0 : (0 : Q') ≤ deltaOf V ε := Q'.le_of_lt (deltaOf_pos V ε hε)
  have hδ1 : deltaOf V ε ≤ 1 := deltaOf_le_one V ε hε hV0
  -- `δ·δ ≤ δ`.
  have hsq_le : deltaOf V ε * deltaOf V ε ≤ deltaOf V ε := by
    have s1 : deltaOf V ε * deltaOf V ε ≤ deltaOf V ε * 1 :=
      Q'.mul_le_mul_of_nonneg_left (deltaOf V ε) 1 (deltaOf V ε) hδ1 hδ0
    exact le_of_le_eqv s1 (Q'.mul_one_eqv (deltaOf V ε))
  -- `(δ·δ)·V ≤ δ·V`.
  have hstep1 : deltaOf V ε * deltaOf V ε * V ≤ deltaOf V ε * V :=
    Q'.mul_le_mul_of_nonneg_right (deltaOf V ε * deltaOf V ε) (deltaOf V ε) V hsq_le hV0
  -- `V ≤ ε + (V + 1)`.
  have hVw : V ≤ ε + (V + 1) := by
    have hVle : V ≤ V + 1 := Q'.add_le_self_of_nonneg V 1 (by decide)
    have h1w : V + 1 ≤ ε + (V + 1) :=
      le_of_le_eqv (Q'.add_le_self_of_nonneg (V + 1) ε (Q'.le_of_lt hε))
        (Q'.add_comm_eqv (V + 1) ε)
    exact Q'.le_trans' V (V + 1) (ε + (V + 1)) hVle h1w
  -- `recip w · V ≤ 1`.
  have hrwV : Q'.recip (ε + (V + 1)) * V ≤ 1 := by
    have hle : Q'.recip (ε + (V + 1)) * V ≤ Q'.recip (ε + (V + 1)) * (ε + (V + 1)) :=
      Q'.mul_le_mul_of_nonneg_left V (ε + (V + 1)) (Q'.recip (ε + (V + 1))) hVw
        (Q'.le_of_lt (Q'.recip_pos _))
    have hrw1 : (Q'.recip (ε + (V + 1)) * (ε + (V + 1))).eqv 1 :=
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.recip (ε + (V + 1))) (ε + (V + 1)))
        (Q'.mul_recip_eqv (ε + (V + 1)) hw)
    exact le_of_le_eqv hle hrw1
  -- `δ·V ≤ ε`.
  have hδV : deltaOf V ε * V ≤ ε := by
    have eassoc : (ε * Q'.recip (ε + (V + 1)) * V).eqv
        (ε * (Q'.recip (ε + (V + 1)) * V)) :=
      Q'.mul_assoc_eqv ε (Q'.recip (ε + (V + 1))) V
    have hle2 : ε * (Q'.recip (ε + (V + 1)) * V) ≤ ε * 1 :=
      Q'.mul_le_mul_of_nonneg_left (Q'.recip (ε + (V + 1)) * V) 1 ε hrwV (Q'.le_of_lt hε)
    have hle3 : ε * (Q'.recip (ε + (V + 1)) * V) ≤ ε :=
      le_of_le_eqv hle2 (Q'.mul_one_eqv ε)
    exact le_of_eqv_le eassoc hle3
  exact Q'.le_trans' _ _ _ hstep1 hδV

/-! ## 4. The spectral symbol data `lamN` / `dN` and its finite max -/

section SpectralData

variable {D : GNSData} {H : CompleteGNSHilbert D} {G : SpectralGapData H}

/-- The `Nat`-indexed eigenvalue reader (`0` off the resolved range). -/
def lamN (Br : DiagResolution G) (j : Nat) : Q' :=
  if h : j < Br.k then Br.lam ⟨j, h⟩ else 0

theorem lamN_at (Br : DiagResolution G) (j : Nat) (hj : j < Br.k) :
    lamN Br j = Br.lam ⟨j, hj⟩ := by
  show (if h : j < Br.k then Br.lam ⟨j, h⟩ else (0 : Q')) = Br.lam ⟨j, hj⟩
  rw [dif_pos hj]

/-- The `Nat`-indexed squared spectral gap `p(λⱼ)²` (`0` off the range). -/
def dN (Br : DiagResolution G) (r : QPoly.Poly) (j : Nat) : Q' :=
  QPoly.eval r (lamN Br j) * QPoly.eval r (lamN Br j)

theorem dN_at (Br : DiagResolution G) (r : QPoly.Poly) (i : Fin Br.k) :
    dN Br r i.val = QPoly.eval r (Br.lam i) * QPoly.eval r (Br.lam i) := by
  show QPoly.eval r (lamN Br i.val) * QPoly.eval r (lamN Br i.val)
      = QPoly.eval r (Br.lam i) * QPoly.eval r (Br.lam i)
  rw [lamN_at Br i.val i.isLt]

theorem dN_at' (Br : DiagResolution G) (r : QPoly.Poly) (j : Nat) (hj : j < Br.k) :
    dN Br r j = QPoly.eval r (Br.lam ⟨j, hj⟩) * QPoly.eval r (Br.lam ⟨j, hj⟩) := by
  show QPoly.eval r (lamN Br j) * QPoly.eval r (lamN Br j)
      = QPoly.eval r (Br.lam ⟨j, hj⟩) * QPoly.eval r (Br.lam ⟨j, hj⟩)
  rw [lamN_at Br j hj]

theorem dN_nonneg (Br : DiagResolution G) (r : QPoly.Poly) (j : Nat) :
    (0 : Q') ≤ dN Br r j :=
  SumOfSquares.q_mul_self_nonneg _

/-- The per-mode Bernstein modulus fold (`0` off the resolved range). -/
def gmod (Br : DiagResolution G) {pseq : Nat → QPoly.Poly}
    (U : ∀ i : Fin Br.k, SpectralUnifCauchy pseq (Br.lam i)) (δ : Q') (j : Nat) : Nat :=
  if h : j < Br.k then (U ⟨j, h⟩).Nmod δ else 0

theorem gmod_at (Br : DiagResolution G) {pseq : Nat → QPoly.Poly}
    (U : ∀ i : Fin Br.k, SpectralUnifCauchy pseq (Br.lam i)) (δ : Q') (j : Nat)
    (hj : j < Br.k) :
    gmod Br U δ j = (U ⟨j, hj⟩).Nmod δ := by
  show (if h : j < Br.k then (U ⟨j, h⟩).Nmod δ else 0) = (U ⟨j, hj⟩).Nmod δ
  rw [dif_pos hj]

end SpectralData

/-! ## 5. The carried spectral-difference inputs -/

/-- **The honest carried Type-level remainder.**  The standard OS / Peter–Weyl
spectral data (`Br`, `PN.normDiag`), the per-mode Bernstein uniform-Cauchy datum
(`Umode`), and the one per-point self-inner bound (`V`, `hV`). -/
structure SpectralDiffInputs (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData) : Type where
  /-- Scalar-square laws (for the difference identity). -/
  SQ : ScalarSquareLaws SL
  /-- The located spectral model and gap. -/
  model : SpectralModel
  gap : LocatedSpectralGap model
  /-- The finite diagonal spectral resolution of the FORMED operator. -/
  Br : DiagResolution
    (spectralGapDataOfL SL.toSmulGNSData LT.toAdditiveTransferOperator model gap)
  /-- The per-pair diagonal Parseval carrier (only `.normDiag` is consumed). -/
  PN : ∀ p q : Nat, PolyNormData SL.toSmulGNSData LT.toAdditiveTransferOperator
    model gap Br (QPoly.psub (pseq p) (pseq q))
  /-- The per-mode Bernstein uniform-Cauchy modulus at each `Br.lam i`. -/
  Umode : ∀ i : Fin Br.k, SpectralUnifCauchy pseq (Br.lam i)
  /-- The fixed rational self-inner bound. -/
  V : Q'
  hV0 : (0 : Q') ≤ V
  /-- `⟨⟦xc⟧,⟦xc⟧⟩ ≤ V` in `RC`-order. -/
  hV : CReal.RCle
    (SL.toGNSData.cinnerCompl (Quotient.mk (cauchySetoid SL.toGNSData) xc)
                              (Quotient.mk (cauchySetoid SL.toGNSData) xc))
    (Quotient.mk CReal.crealSetoid (CReal.ofQ' V))

/-! ## 6. Inhabiting `SpectralDiffBound` -/

/-- **The builder.**  From `SpectralDiffInputs`, inhabit `SpectralDiffBound`:
`rcbound` from the `polyNormBound → RCscale_mono → M2` chain at the finite
spectral max, `vanish` from the per-mode Bernstein bound through `M1`. -/
def spectralDiffBoundOfInputs (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData)
    (inputs : SpectralDiffInputs SL LT pseq xc) :
    SpectralDiffBound SL LT pseq xc where
  Bq := fun p q =>
    specMaxAux (dN inputs.Br (QPoly.psub (pseq p) (pseq q))) inputs.Br.k * inputs.V
  mod := fun ε =>
    natMaxAux (gmod inputs.Br inputs.Umode (deltaOf inputs.V ε)) inputs.Br.k
  rcbound := by
    intro p q
    -- Difference identity: `imgDiff = polyApply (psub …) ⟦xc⟧`.
    have hid : imgDiff SL LT pseq xc p q
        = polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator
            (QPoly.psub (pseq p) (pseq q))
            (Quotient.mk (cauchySetoid SL.toGNSData) xc) :=
      polyApplyLinCauchy_diff SL inputs.SQ LT pseq xc p q
    rw [hid, (inputs.PN p q).normDiag (Quotient.mk (cauchySetoid SL.toGNSData) xc)]
    -- The finite spectral max is an upper bound for each resolved square.
    have hlist := (specMaxAux_le_iff (dN inputs.Br (QPoly.psub (pseq p) (pseq q)))
      (specMaxAux (dN inputs.Br (QPoly.psub (pseq p) (pseq q))) inputs.Br.k)
      inputs.Br.k).mp (Q'.le_refl' _)
    have hM : ∀ i : Fin inputs.Br.k,
        QPoly.eval (QPoly.psub (pseq p) (pseq q)) (inputs.Br.lam i)
          * QPoly.eval (QPoly.psub (pseq p) (pseq q)) (inputs.Br.lam i)
        ≤ specMaxAux (dN inputs.Br (QPoly.psub (pseq p) (pseq q))) inputs.Br.k := by
      intro i
      have h := hlist.2 i.val i.isLt
      rw [dN_at inputs.Br (QPoly.psub (pseq p) (pseq q)) i] at h
      exact h
    -- Diagonal polynomial norm bound at the spectral max.
    have hPNB := polyNormBound inputs.Br (QPoly.psub (pseq p) (pseq q))
      (specMaxAux (dN inputs.Br (QPoly.psub (pseq p) (pseq q))) inputs.Br.k) hM
      (Quotient.mk (cauchySetoid SL.toGNSData) xc)
    -- Fold in ‖x‖² via the per-point bound `hV`.
    have hMsp_nn : (0 : Q') ≤
        specMaxAux (dN inputs.Br (QPoly.psub (pseq p) (pseq q))) inputs.Br.k :=
      specMaxAux_nonneg (dN inputs.Br (QPoly.psub (pseq p) (pseq q)))
        (fun j => dN_nonneg inputs.Br (QPoly.psub (pseq p) (pseq q)) j) inputs.Br.k
    have hfold := CReal.RCscale_mono hMsp_nn inputs.hV
    have hchain := CReal.RCle_trans hPNB hfold
    rw [RCscale_ofQ'
      (specMaxAux (dN inputs.Br (QPoly.psub (pseq p) (pseq q))) inputs.Br.k) inputs.V]
      at hchain
    exact hchain
  vanish := by
    intro ε hε p q hp hq
    have hδpos : (0 : Q') < deltaOf inputs.V ε := deltaOf_pos inputs.V ε hε
    -- `Msp ≤ (δ ε)²`.
    have hMsp : specMaxAux (dN inputs.Br (QPoly.psub (pseq p) (pseq q))) inputs.Br.k
        ≤ deltaOf inputs.V ε * deltaOf inputs.V ε :=
      (specMaxAux_le_iff (dN inputs.Br (QPoly.psub (pseq p) (pseq q)))
        (deltaOf inputs.V ε * deltaOf inputs.V ε) inputs.Br.k).mpr
        ⟨SumOfSquares.q_mul_self_nonneg _, by
          intro j hj
          -- Per-mode two-sided Bernstein bound at `Br.lam ⟨j,hj⟩`.
          have hNp : (inputs.Umode ⟨j, hj⟩).Nmod (deltaOf inputs.V ε) ≤ p := by
            have hge := natMaxAux_ge
              (gmod inputs.Br inputs.Umode (deltaOf inputs.V ε)) inputs.Br.k j hj
            rw [gmod_at inputs.Br inputs.Umode (deltaOf inputs.V ε) j hj] at hge
            exact Nat.le_trans hge hp
          have hNq : (inputs.Umode ⟨j, hj⟩).Nmod (deltaOf inputs.V ε) ≤ q := by
            have hge := natMaxAux_ge
              (gmod inputs.Br inputs.Umode (deltaOf inputs.V ε)) inputs.Br.k j hj
            rw [gmod_at inputs.Br inputs.Umode (deltaOf inputs.V ε) j hj] at hge
            exact Nat.le_trans hge hq
          have hcau := (inputs.Umode ⟨j, hj⟩).cauchy (deltaOf inputs.V ε) hδpos p q hNp hNq
          -- Two-sided bound on the difference-polynomial value.
          have hU : QPoly.eval (pseq p) (inputs.Br.lam ⟨j, hj⟩)
              + -(QPoly.eval (pseq q) (inputs.Br.lam ⟨j, hj⟩)) ≤ deltaOf inputs.V ε :=
            Q'.sub_le_of_le_add hcau.1
          have hL : -(deltaOf inputs.V ε)
              ≤ QPoly.eval (pseq p) (inputs.Br.lam ⟨j, hj⟩)
                  + -(QPoly.eval (pseq q) (inputs.Br.lam ⟨j, hj⟩)) :=
            Q'.neg_le_sub_of_le_add hcau.2
          have hdeqv := QPoly.eval_psub (pseq p) (pseq q) (inputs.Br.lam ⟨j, hj⟩)
          have edU : QPoly.eval (QPoly.psub (pseq p) (pseq q)) (inputs.Br.lam ⟨j, hj⟩)
              ≤ deltaOf inputs.V ε := le_of_eqv_le hdeqv hU
          have edL : -(deltaOf inputs.V ε)
              ≤ QPoly.eval (QPoly.psub (pseq p) (pseq q)) (inputs.Br.lam ⟨j, hj⟩) :=
            le_of_le_eqv hL (Q'.eqv_symm hdeqv)
          have hsq := Q'.mul_le_of_bounds (Q'.le_of_lt hδpos) (Q'.le_of_lt hδpos)
            edL edU edL edU
          rw [dN_at' inputs.Br (QPoly.psub (pseq p) (pseq q)) j hj]
          exact hsq⟩
    -- `Bq = Msp·V ≤ (δ ε)²·V ≤ ε`.
    have h2 : specMaxAux (dN inputs.Br (QPoly.psub (pseq p) (pseq q))) inputs.Br.k
          * inputs.V
        ≤ (deltaOf inputs.V ε * deltaOf inputs.V ε) * inputs.V :=
      Q'.mul_le_mul_of_nonneg_right _ _ inputs.V hMsp inputs.hV0
    have h3 : (deltaOf inputs.V ε * deltaOf inputs.V ε) * inputs.V ≤ ε :=
      deltaOf_sq_mul_le inputs.V ε hε inputs.hV0
    exact Q'.le_trans' _ _ _ h2 h3

/-! ## 7. Assembly — the retired `PolyImageDistCert` and the point supplier -/

/-- **The `PolyImageDistCert` for the fixed representative `xc`.** -/
def polyImageDistCertClosed (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData)
    (inputs : SpectralDiffInputs SL LT pseq xc) :
    PolyImageDistCert SL LT pseq xc :=
  polyImageDistCertOfSpectralDiffBound SL LT pseq xc
    (spectralDiffBoundOfInputs SL LT pseq xc inputs)

/-- **The choice-free point-cert at `⟦xc⟧`** (carries its own representative). -/
def polyImagePointCertClosed (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData)
    (inputs : SpectralDiffInputs SL LT pseq xc) :
    PolyImagePointCert SL LT pseq (Quotient.mk (cauchySetoid SL.toGNSData) xc) where
  xrep := xc
  hrep := rfl
  dist := polyImageDistCertClosed SL LT pseq xc inputs

/-- **The retired `img` datum at `⟦xc⟧`** — the `PolyImageCauchy` supplier for the
polynomial-image sequence, with the distance modulus now GREEN from the carried
spectral data.  This closes the last carried residual of core ④ at the fixed
representative. -/
def polyImageCauchyClosed (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData)
    (inputs : SpectralDiffInputs SL LT pseq xc) :
    PolyImageCauchy SL LT.toAdditiveTransferOperator pseq
      (Quotient.mk (cauchySetoid SL.toGNSData) xc) :=
  polyImageCauchyOfCert SL LT pseq xc (polyImageDistCertClosed SL LT pseq xc inputs)

end YMGap.Continuum.SpectralDiffBoundClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SpectralDiffBoundClose.RCscale_ofQ'
#print axioms YMGap.Continuum.SpectralDiffBoundClose.natMaxAux_ge
#print axioms YMGap.Continuum.SpectralDiffBoundClose.deltaOf_sq_mul_le
#print axioms YMGap.Continuum.SpectralDiffBoundClose.spectralDiffBoundOfInputs
#print axioms YMGap.Continuum.SpectralDiffBoundClose.polyImageDistCertClosed
#print axioms YMGap.Continuum.SpectralDiffBoundClose.polyImagePointCertClosed
#print axioms YMGap.Continuum.SpectralDiffBoundClose.polyImageCauchyClosed
