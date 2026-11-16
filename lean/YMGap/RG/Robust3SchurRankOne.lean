import YMGap.RG.Robust3SpacingHeatKernel

/-!
# Robust3: `hschur`/`hafδ` from spectral data via the rank-one Schur budget (task2n (A), abstract form)

Numerics task2n (`results/task2n_hafdelta.md` §1) argues that, under the meta-identification of the repo carrier
with the KS transfer matrix, the least admissible Schur defect is `δ_min = max(0, 1 − (1−ρ_F⁴)/(1−ρ_C²))`, attained
by the rank-one `Φ(y) = ‖y‖·v_C`. This file proves the **carrier-level abstract core** of that argument:

* `SchurBudget f c δ := f ≤ δ + (1−δ)·c` (rational form of `δ ≥ δ_min` with `f ≈ ρ_F⁴`, `c ≈ ρ_C²`);
* `schur_of_spectral`: if the fine two-step factor is `f` (`WilsonVacuumSqTwoStepFactor`, i.e. `‖T_F(2)y‖² ≤ f‖y‖²`),
  the coarse image attains `c` (`c‖y‖² ≤ ‖T_C(1)Φy‖²`), and `SchurBudget f c δ`, then the repo's
  `SchurDecomposition … δ Φ (schurSlack …)` holds (D := the explicit slack, `D ≥ 0`);
* `budget_eps`: the constructive-real norm caveat. A rank-one `Φ` needs the real `‖y‖`; a rational approximation
  (or an approximate `v_C`) only gives `c = c₀ − ε`. The budget then costs exactly `(1−δ)·ε ≤ ε`;
* `robust3_physical_floor_spectral_HK` / `robust3_physical_floor_lmax_HK`: the final theorem with `D`, `hschur`
  (and, in the `lmax` form, `δ`, `hd0`, `hd1`, `hcross`, `hafδ`) replaced by `hfine`, `hcoarse`, `hbudget`.
  In the `lmax` form `hbudget_OPEN n` is the rational form of `ℓ_n ≤ ℓ_max(n)` (allowance `1/64` for `n < 6`,
  `afGap²/10` for `n ≥ 6`).

NOT proved here: the existence of a rank-one `Φ` on the completed carrier (needs a scalar action of the constructive
real `‖y‖` on `VacuumComplement`, which the repo does not provide), the spectral facts `f ≤ ρ_F⁴`, `c ≥ ρ_C²−ε`, the
TM identification, and the link `δ_min = 0 ⇔ ℓ ≤ 1` (needs `exp`). All remain OPEN hypotheses. `DyadicRGStep` (SC)
`w_f² ≤ w_c` is only the strong-coupling-model analogue of `ℓ ≤ 1`; it is not used. Additive; nothing existing changed.
-/

namespace YMGap.RG.Robust3SchurRankOne

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement completedTime)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
  (WilsonVacuumSqTwoStepFactor vacuumSq_implies_twoStepFactor latticeMarginOf)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation (relative_comparison_iff_dissipation)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afA afGap_pos afGap_lt_one)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate)
open YMGap.RG.RelativeDissipationScaleChain (SchurDecomposition inv)
open YMGap.RG.DyadicCrossoverInstance (eDy)
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule r3Nome)
open YMGap.RG.Robust3UndershootPhysicalUnits (r3P)
open YMGap.RG.Robust3UndershootCrossoverInstance (etaR3)
open YMGap.RG.Robust3SpacingHeatKernel
  (hposHK hspacingHK_win hspacingHK_off robust3_physical_floor_noMargin_HK)

/-! ## 1. Rational budget and the ε cost -/

/-- Rational Schur budget `f ≤ δ + (1−δ)·c`: with `f = ρ_F⁴`, `c = ρ_C²` this is exactly `δ ≥ δ_min`. -/
def SchurBudget (f c δ : Q') : Prop := f ≤ δ + ((1 : Q') - δ) * c

/-- **ε cost (PROVED).** If the coarse attainment is only `c₀ − ε` (rational approximation of `‖y‖` or of `v_C`),
the budget still holds provided `f + (1−δ)ε ≤ δ + (1−δ)c₀`, i.e. at an extra cost `(1−δ)ε ≤ ε`. -/
theorem budget_eps (f c0 eps δ : Q')
    (h : f + ((1 : Q') - δ) * eps ≤ δ + ((1 : Q') - δ) * c0) :
    SchurBudget f (c0 - eps) δ := by
  have h1 := Q'.add_le_add_right _ _ (-(((1 : Q') - δ) * eps)) h
  have e1 : f.eqv (f + ((1 : Q') - δ) * eps + -(((1 : Q') - δ) * eps)) :=
    poly_identity_of_normal_eq (.var 0)
      (.add (.add (.var 0) (.mul (.add (.const 1) (.neg (.var 1))) (.var 2)))
        (.neg (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))))
      (by decide) (fun | 0 => f | 1 => δ | _ => eps)
  have e2 : (δ + ((1 : Q') - δ) * c0 + -(((1 : Q') - δ) * eps)).eqv
      (δ + ((1 : Q') - δ) * (c0 - eps)) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 1) (.mul (.add (.const 1) (.neg (.var 1))) (.var 3)))
        (.neg (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))))
      (.add (.var 1) (.mul (.add (.const 1) (.neg (.var 1))) (.add (.var 3) (.neg (.var 2)))))
      (by decide) (fun | 0 => f | 1 => δ | 2 => eps | _ => c0)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv e2))

/-! ## 2. Real-valued (RC) core -/

private theorem scale_split (δ c : Q') (A : RC) :
    RCscale (δ + ((1 : Q') - δ) * c) A = RCadd (RCscale δ A) (RCscale ((1 : Q') - δ) (RCscale c A)) := by
  refine Quotient.inductionOn A ?_
  intro a
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.mul (.add (.const 1) (.neg (.var 0))) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => δ | 1 => c | _ => a.approx n)))

/-- **Relative comparison from the budget (PROVED).** `F ≤ fA`, `cA ≤ C`, `A ≥ 0`, budget ⇒ `F ≤ δA + (1−δ)C`. -/
theorem rel_of_budget (A F C : RC) (f c δ : Q') (hδ1 : δ ≤ (1 : Q')) (hA : RCnonneg A)
    (hF : RCle F (RCscale f A)) (hC : RCle (RCscale c A) C) (hb : SchurBudget f c δ) :
    RCle F (RCadd (RCscale δ A) (RCscale ((1 : Q') - δ) C)) := by
  have h1 := RCle_trans hF (RCscale_mono_scalar hb hA)
  rw [scale_split] at h1
  exact RCle_trans h1 (RCadd_le_add (RCle_refl _) (RCscale_mono (Q'.sub_nonneg_of_le hδ1) hC))

/-- The explicit Schur slack `D := (A−F) − (1−δ)(A−C)`. -/
def slack (A F C : RC) (δ : Q') : RC := RCsub (RCsub A F) (RCscale ((1 : Q') - δ) (RCsub A C))

private theorem add_sub_cancel' (Z X : RC) : Z = RCadd X (RCsub Z X) := by
  refine Quotient.inductionOn₂ Z X ?_
  intro z x
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.var 0) (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => z.approx n | _ => x.approx n)))

private theorem add_neg_zero (X : RC) : RCadd X (RCneg X) = RCzero := by
  refine Quotient.inductionOn X ?_
  intro x
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (x.approx n)))

private theorem nonneg_sub {X Z : RC} (h : RCle X Z) : RCnonneg (RCsub Z X) := by
  have hh := RCadd_le_add h (RCle_refl (RCneg X))
  rw [add_neg_zero] at hh
  exact hh

/-- **Slack decomposition (PROVED).** The relative comparison gives `D ≥ 0` and the exact Schur identity. -/
theorem slack_dec (A F C : RC) (δ : Q')
    (h : RCle F (RCadd (RCscale δ A) (RCscale ((1 : Q') - δ) C))) :
    RCnonneg (slack A F C δ) ∧
      RCsub A F = RCadd (RCscale ((1 : Q') - δ) (RCsub A C)) (slack A F C δ) :=
  ⟨nonneg_sub ((relative_comparison_iff_dissipation δ A F C).mp h), add_sub_cancel' _ _⟩

/-! ## 3. Carrier form on the repo's `SchurDecomposition` -/

section Carrier
variable {wF wC : Q'} (hwF0 : (0 : Q') < wF) (hwF1 : wF < (1 : Q'))
  (hwC0 : (0 : Q') < wC) (hwC1 : wC < (1 : Q'))

/-- Carrier slack `D y := (‖y‖² − ‖T_F(2)y‖²) − (1−δ)(‖y‖² − ‖T_C(1)Φy‖²)`. -/
def schurSlack (widthF widthC : Nat) (δ : Q')
    (Phi : VacuumComplement hwF0 hwF1 (width := widthF) → VacuumComplement hwC0 hwC1 (width := widthC))
    (y : VacuumComplement hwF0 hwF1 (width := widthF)) : RC :=
  slack (completedInner hwF0 hwF1 y.val y.val)
    (completedInner hwF0 hwF1 (completedTime hwF0 hwF1 2 y.val) (completedTime hwF0 hwF1 2 y.val))
    (completedInner hwC0 hwC1 (completedTime hwC0 hwC1 1 (Phi y).val) (completedTime hwC0 hwC1 1 (Phi y).val)) δ

/-- **Schur decomposition from spectral data (PROVED, given the OPEN inputs).**
`hfine`: fine two-step factor `f`; `hcoarse`: coarse attainment `c`; `hb`: `SchurBudget f c δ`. -/
theorem schur_of_spectral (widthF widthC : Nat) (δ f c : Q')
    (Phi : VacuumComplement hwF0 hwF1 (width := widthF) → VacuumComplement hwC0 hwC1 (width := widthC))
    (hδ1 : δ ≤ (1 : Q')) (hfine : WilsonVacuumSqTwoStepFactor hwF0 hwF1 widthF f)
    (hcoarse : ∀ y : VacuumComplement hwF0 hwF1 (width := widthF),
      RCle (RCscale c (completedInner hwF0 hwF1 y.val y.val))
        (completedInner hwC0 hwC1 (completedTime hwC0 hwC1 1 (Phi y).val) (completedTime hwC0 hwC1 1 (Phi y).val)))
    (hb : SchurBudget f c δ) :
    SchurDecomposition hwF0 hwF1 hwC0 hwC1 widthF widthC δ Phi
      (schurSlack hwF0 hwF1 hwC0 hwC1 widthF widthC δ Phi) := fun y =>
  slack_dec _ _ _ δ (rel_of_budget _ _ _ f c δ hδ1
    (YMGap.Continuum.BF4WilsonAllNomeCompletedInner.completedInner_nonnegative hwF0 hwF1 y.val)
    (hfine y) (hcoarse y) hb)

/-- Variant with the fine input as a one-step contraction at rate `rF` (`f = rF⁴`). -/
theorem schur_of_spectral_rate (widthF widthC : Nat) (δ rF c : Q')
    (Phi : VacuumComplement hwF0 hwF1 (width := widthF) → VacuumComplement hwC0 hwC1 (width := widthC))
    (hδ1 : δ ≤ (1 : Q')) (hF : WilsonVacuumSqContraction hwF0 hwF1 widthF rF)
    (hcoarse : ∀ y : VacuumComplement hwF0 hwF1 (width := widthF),
      RCle (RCscale c (completedInner hwF0 hwF1 y.val y.val))
        (completedInner hwC0 hwC1 (completedTime hwC0 hwC1 1 (Phi y).val) (completedTime hwC0 hwC1 1 (Phi y).val)))
    (hb : SchurBudget (rF * rF * (rF * rF)) c δ) :
    SchurDecomposition hwF0 hwF1 hwC0 hwC1 widthF widthC δ Phi
      (schurSlack hwF0 hwF1 hwC0 hwC1 widthF widthC δ Phi) :=
  schur_of_spectral hwF0 hwF1 hwC0 hwC1 widthF widthC δ _ c Phi hδ1
    (vacuumSq_implies_twoStepFactor rF hF) hcoarse hb

end Carrier

/-! ## 4. The final theorem with `hschur` replaced by spectral data -/

/-- **`robust3_physical_floor_noMargin_HK` from spectral data (PROVED reduction).** `D` and `hschur_OPEN` are
replaced by `f, c` with `hfine_OPEN` (fine two-step factor), `hcoarse_OPEN` (coarse attainment, `c = ρ_C² − ε` in
the rank-one reading) and `hbudget_OPEN : SchurBudget (f n) (c n) (δ n)`. -/
theorem robust3_physical_floor_spectral_HK :
    let ns := robust3UndershootSchedule
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaR3 n)
      (_hafδ_OPEN : ∀ n, 6 ≤ n →
        delta n ≤ Q'.mkPos 1 10 (by decide) * (afGap (0+n) * afGap (0+n)))
      (Phi : ∀ n, VacuumComplement (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
          (width := width (0+n+1)) →
        VacuumComplement (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (width := width (0+n)))
      (_hupper_OPEN : ∀ n y, RCle
        (completedInner (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (Phi n y).val (Phi n y).val)
        (completedInner (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1)) y.val y.val))
      (f c : Nat → Q')
      (_hfine_OPEN : ∀ n, WilsonVacuumSqTwoStepFactor (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
        (width (0+n+1)) (f n))
      (_hcoarse_OPEN : ∀ n y, RCle
        (RCscale (c n) (completedInner (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1)) y.val y.val))
        (completedInner (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n))
          (completedTime (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) 1 (Phi n y).val)
          (completedTime (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) 1 (Phi n y).val)))
      (_hbudget_OPEN : ∀ n, SchurBudget (f n) (c n) (delta n))
      (aHK : Q' → Q') (lo hi : Nat) (_hpos : hposHK aHK)
      (_hwin_MC : hspacingHK_win aHK lo hi) (_hoff_OPEN : hspacingHK_off aHK lo hi)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * aHK (r3Nome n) ≤
        (r3P * aHK (r3Nome 0)) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi hupper f c hfine hcoarse hbud aHK lo hi hp hw ho n =>
    robust3_physical_floor_noMargin_HK width delta hd0 hd1 hcross hafδ Phi
      (fun k => schurSlack _ _ _ _ (width (0+k+1)) (width (0+k)) (delta k) (Phi k)) hupper
      (fun k => schur_of_spectral _ _ _ _ _ _ (delta k) (f k) (c k) (Phi k) (hd1 k) (hfine k)
        (hcoarse k) (hbud k))
      aHK lo hi hp hw ho n

/-- The `hcross`/`hafδ` caps as a δ schedule: `1/64` for `n < 6`, `afGap(n)²/10` for `n ≥ 6`. -/
def capDelta (n : Nat) : Q' :=
  if n < 6 then etaR3 n else Q'.mkPos 1 10 (by decide) * (afGap (0+n) * afGap (0+n))

theorem capDelta_nonneg (n : Nat) : (0 : Q') ≤ capDelta n := by
  unfold capDelta
  by_cases h : n < 6
  · rw [if_pos h]; exact (by decide : (0 : Q') ≤ Q'.mkPos 1 64 (by decide))
  · rw [if_neg h]
    have hg := Q'.le_of_lt (afGap_pos (0+n))
    exact Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hg hg)

theorem capDelta_le_one (n : Nat) : capDelta n ≤ (1 : Q') := by
  unfold capDelta
  by_cases h : n < 6
  · rw [if_pos h]; exact (by decide : Q'.mkPos 1 64 (by decide) ≤ (1 : Q'))
  · rw [if_neg h]
    have hg0 := Q'.le_of_lt (afGap_pos (0+n))
    have hg1 := Q'.le_of_lt (afGap_lt_one (0+n))
    have hsq : afGap (0+n) * afGap (0+n) ≤ (1 : Q') * 1 :=
      Q'.mul_le_mul_of_nonneg hg1 hg1 (by decide) hg0
    have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 1 10 (by decide)) hsq (by decide)
    exact Q'.le_trans' _ _ _ h2 (by decide)

/-- **`hafδ` follows from `ℓ ≤ ℓ_max` plus spectral data (PROVED reduction).** With `δ := capDelta`, the binders
`δ, hd0, hd1, hcross, hafδ, D, hschur` are all discharged; `hbudget_OPEN n : SchurBudget (f n) (c n) (capDelta n)` is
the rational form of `ℓ_n ≤ ℓ_max(n)` (task2n §1). -/
theorem robust3_physical_floor_lmax_HK :
    let ns := robust3UndershootSchedule
    ∀ (width : Nat → Nat)
      (Phi : ∀ n, VacuumComplement (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
          (width := width (0+n+1)) →
        VacuumComplement (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (width := width (0+n)))
      (_hupper_OPEN : ∀ n y, RCle
        (completedInner (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (Phi n y).val (Phi n y).val)
        (completedInner (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1)) y.val y.val))
      (f c : Nat → Q')
      (_hfine_OPEN : ∀ n, WilsonVacuumSqTwoStepFactor (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
        (width (0+n+1)) (f n))
      (_hcoarse_OPEN : ∀ n y, RCle
        (RCscale (c n) (completedInner (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1)) y.val y.val))
        (completedInner (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n))
          (completedTime (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) 1 (Phi n y).val)
          (completedTime (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) 1 (Phi n y).val)))
      (_hbudget_OPEN : ∀ n, SchurBudget (f n) (c n) (capDelta n))
      (aHK : Q' → Q') (lo hi : Nat) (_hpos : hposHK aHK)
      (_hwin_MC : hspacingHK_win aHK lo hi) (_hoff_OPEN : hspacingHK_off aHK lo hi)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * aHK (r3Nome n) ≤
        (r3P * aHK (r3Nome 0)) * latticeMarginOf (relativeRate timeRate capDelta) n :=
  fun width Phi hupper f c hfine hcoarse hbud aHK lo hi hp hw ho n =>
    robust3_physical_floor_spectral_HK width capDelta capDelta_nonneg capDelta_le_one
      (fun k hk => by unfold capDelta; rw [if_pos hk]; exact Q'.le_refl' _)
      (fun k hk => by unfold capDelta; rw [if_neg (Nat.not_lt.mpr hk)]; exact Q'.le_refl' _)
      Phi hupper f c hfine hcoarse hbud aHK lo hi hp hw ho n

end YMGap.RG.Robust3SchurRankOne
