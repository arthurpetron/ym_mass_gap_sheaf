/-
# `MooreOsgoodB2`: discharging the angle-continuity leg (B2) of the arctan↔trig atom

`ArctanCompositionTail` factors the load-bearing arctan↔trig atom into two
`ConvergesTo` legs of the SAME diagonal sequence `M ↦ colLimSin M`:

* **(B2)** `MooreOsgoodInterchange` — `ConvergesTo colLimSin (sinCat5 d)` (and the
  cosine twin): the iterated column limit equals the genuine constructive `sinC`
  of the arctan angle.  Its sole nontrivial hypothesis, the *uniform row tail*
  `sinRowTail`/`cosRowTail`, is already proved in `ArctanCompositionTail`; what is
  left is the **diagonal-index (`MhatE`/`RhatE`) bookkeeping** of the
  `completeLimitCauchy` backbone.
* **(B1)** `CompositionIdentity` — the transcendental Cauchy-product rearrangement.

This module **discharges (B2) in full**, i.e. it inhabits `MooreOsgoodInterchange d`
for every antitone-modulus datum `d : At5Modulus`.  Consequently `atom_of_legs`
reduces the whole arctan↔trig atom to (B1) `CompositionIdentity` alone — the sole
remaining transcendental residual of the bridge.

## The proof, in one paragraph

Fix `ε > 0`; write `q := ½ε`, `τ := q·⅓`.  Convergence stage `Nstage :=
trigModulus 1 q` (so the uniform row tail applies past `M`), approximation
threshold `Napx := max M (max (Mw τ) q.den)`.  For `n ≥ Napx` the whole content is
the **reach** step

    Mw τ ≤ MhatE n            (`hMwmono ∘ M_le_MhatE`),

which turns "`n` large" into "the diagonal ANGLE index `MhatE n` is past `Mw τ`",
so the antitone `at5` modulus gives `|θ_n − θ_{MhatE n}| ≤ τ`.  Then:

* **leg A** (angle change `n ↦ MhatE n` at fixed truncation `M`): the trig
  partial-sum Lipschitz bound `sinPartialDiff_le` with constant `sinSumBound ≤ 3`
  turns the `τ` angle gap into a `q` value gap;
* **leg B** (truncation change `M ↦ RhatE n` at fixed angle `MhatE n`): the uniform
  row tail `sinRowTail` (valid for EVERY angle, in particular `θ_{MhatE n}`) gives a
  `q` gap since `M ≥ Nstage`.

Pivoting on `sinPartial θ_{MhatE n} M` and padding `q + q ≤ ε` closes the two-sided
bound.  No `abs`/triangle machinery — additive two-sided chaining, exactly the
`q`-collapse of `convergesTo_completeLimitCauchy`, here with two `q`-steps.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, `native_decide`,
`sorry`, or custom `axiom`.  The interchange witnesses are `Type`-level
`ConvergesTo` data; the sole residual (`CompositionIdentity`) is imported, never
manufactured.
-/

import YMGap.Continuum.ArctanCompositionTail

namespace YMGap.Continuum.MooreOsgoodB2

open YMGap.Constructive
open YMGap.Continuum.ArctanSeriesTrigBridge
open YMGap.Continuum.ArctanCompositionTail
open YMGap.Constructive.HalfPow

/-! ## 1. The underlying sequence / completion datum behind `sinCat5` / `cosCat5`

`sinCat5 d = CRealTrig.sinC … = completeLimitCauchy (sSeqS d) (sMCS d)`
definitionally; likewise for cosine.  We name the pieces so the diagonal indices
`MhatE`/`RhatE` and the completion backbone lemmas apply on the nose. -/

/-- The angle-indexed sine sequence `k ↦ sinNN θ_k`. -/
def sSeqS (d : At5Modulus) : Nat → CReal :=
  fun k => Trig.sinNN (Pi.at5.approx k) (at5_pos k)

/-- The angle-indexed cosine sequence `k ↦ cosNN θ_k`. -/
def cSeqS (d : At5Modulus) : Nat → CReal :=
  fun k => Trig.cosNN (Pi.at5.approx k) (at5_pos k)

/-- The eventual-outer modulus datum backing `sinCat5 d`. -/
def sMCS (d : At5Modulus) : CReal.ModCauchyEv (sSeqS d) :=
  CRealTrig.sinCMC Pi.at5 at5_pos at5_le1 d.Mw d.hMw d.hMwmono

/-- The eventual-outer modulus datum backing `cosCat5 d`. -/
def cMCS (d : At5Modulus) : CReal.ModCauchyEv (cSeqS d) :=
  CRealTrig.cosCMC Pi.at5 at5_pos at5_le1 d.Mw d.hMw d.hMwmono

/-- The diagonal ANGLE index (outer running-max modulus). -/
def MhatS (d : At5Modulus) (n : Nat) : Nat := CReal.MhatE (sSeqS d) (sMCS d) n
/-- The diagonal TRUNCATION index (inner index-absorbing modulus). -/
def RhatS (d : At5Modulus) (n : Nat) : Nat := CReal.RhatE (sSeqS d) (sMCS d) n
/-- Cosine diagonal ANGLE index. -/
def cMhatS (d : At5Modulus) (n : Nat) : Nat := CReal.MhatE (cSeqS d) (cMCS d) n
/-- Cosine diagonal TRUNCATION index. -/
def cRhatS (d : At5Modulus) (n : Nat) : Nat := CReal.RhatE (cSeqS d) (cMCS d) n

/-- **The diagonal approx-value of `sinCat5`** — pure `rfl` unfolding of
`completeLimitCauchy_approx ∘ sinNN_approx`. -/
theorem sinCat5_approx (d : At5Modulus) (n : Nat) :
    (sinCat5 d).approx n
      = Trig.sinPartial (Pi.at5.approx (MhatS d n)) (RhatS d n) := rfl

/-- **The diagonal approx-value of `cosCat5`.** -/
theorem cosCat5_approx (d : At5Modulus) (n : Nat) :
    (cosCat5 d).approx n
      = Trig.cosPartial (Pi.at5.approx (cMhatS d n)) (cRhatS d n) := rfl

/-! ## 2. The Moore–Osgood interchange, sine leg -/

/-- **(B2) sine.**  `ConvergesTo (fun M => colLimSin M) (sinCat5 d)`.  Two-sided
additive chaining `legA` (angle change, `sinPartialDiff_le`) + `legB` (truncation
change, `sinRowTail`) pivoted on `sinPartial θ_{MhatE n} M`, with `q + q ≤ ε`. -/
theorem interSin (d : At5Modulus) :
    CReal.ConvergesTo (fun M => colLimSin M) (sinCat5 d) := by
  intro ε hε
  have hqpos : (0 : Q') < half * ε := ExpNeg.half_mul_pos ε hε
  have hτpos : (0 : Q') < half * ε * Q'.mkPos 1 3 (by decide) := ExpNeg.third_pos hqpos
  have hτnn : (0 : Q') ≤ half * ε * Q'.mkPos 1 3 (by decide) := Q'.le_of_lt hτpos
  refine ⟨Trig.trigModulus 1 (half * ε), fun M hMstage => ?_⟩
  refine ⟨max M (max (d.Mw (half * ε * Q'.mkPos 1 3 (by decide))) (half * ε).den),
    fun n hn => ?_⟩
  -- unpack the approximation threshold
  have hMn : M ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hrest : max (d.Mw (half * ε * Q'.mkPos 1 3 (by decide))) (half * ε).den ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hMwτn : d.Mw (half * ε * Q'.mkPos 1 3 (by decide)) ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hrest
  have hqdenn : (half * ε).den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hrest
  -- (Lemma A) the diagonal-index reach: `Mw τ ≤ MhatS d n`
  have hinv : Q'.invSucc n ≤ half * ε :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hqdenn)
      (HalfPow.invSucc_den_le (half * ε) hqpos)
  have hmk : (0 : Q') ≤ Q'.mkPos 1 3 (by decide) := Q'.le_of_lt (Q'.invSucc_pos 2)
  have hτ' : Q'.invSucc n * Q'.mkPos 1 3 (by decide)
      ≤ half * ε * Q'.mkPos 1 3 (by decide) :=
    Q'.mul_le_mul_of_nonneg_right (Q'.invSucc n) (half * ε) (Q'.mkPos 1 3 (by decide)) hinv hmk
  have reach : d.Mw (half * ε * Q'.mkPos 1 3 (by decide)) ≤ MhatS d n :=
    Nat.le_trans
      (d.hMwmono (half * ε * Q'.mkPos 1 3 (by decide))
        (Q'.invSucc n * Q'.mkPos 1 3 (by decide))
        (ExpNeg.third_pos (Q'.invSucc_pos n)) hτ')
      (CReal.M_le_MhatE (sSeqS d) (sMCS d) n)
  -- the angle gap `|θ_n − θ_{MhatS d n}| ≤ τ`
  have angle := d.hMw (half * ε * Q'.mkPos 1 3 (by decide)) hτpos n (MhatS d n) hMwτn reach
  -- (leg A) angle change `n ↦ MhatS d n` at fixed truncation `M`
  have legA_abs : Q'.abs (Trig.sinPartial (Pi.at5.approx n) M
      + -(Trig.sinPartial (Pi.at5.approx (MhatS d n)) M)) ≤ half * ε :=
    Q'.le_trans' _ _ _
      (CRealTrig.sinPartialDiff_le (at5_pos n) (at5_le1 n)
        (at5_pos (MhatS d n)) (at5_le1 (MhatS d n)) hτnn angle.1 angle.2 M)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (CRealTrig.sinSumBound_le_three M) hτnn)
        (Q'.le_of_eqv (ExpNeg.third_mul_three (half * ε))))
  have legA1 : Trig.sinPartial (Pi.at5.approx n) M
      ≤ Trig.sinPartial (Pi.at5.approx (MhatS d n)) M + half * ε :=
    ExpNeg.le_add_of_abs_sub_le legA_abs
  have legA2 : Trig.sinPartial (Pi.at5.approx (MhatS d n)) M
      ≤ Trig.sinPartial (Pi.at5.approx n) M + half * ε :=
    ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm
        (Trig.sinPartial (Pi.at5.approx (MhatS d n)) M)
        (Trig.sinPartial (Pi.at5.approx n) M))) legA_abs)
  -- (leg B) truncation change `M ↦ RhatS d n` at fixed angle `MhatS d n`
  have hRn : M ≤ RhatS d n := Nat.le_trans hMn (CReal.k_le_RhatE (sSeqS d) (sMCS d) n)
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hRn
  have legB := sinRowTail (half * ε) hqpos M hMstage (MhatS d n) e
  rw [← he] at legB
  -- (assembly) pivot on `sinPartial θ_{MhatS d n} M`, pad `q + q ≤ ε`
  have h2q : ∀ w : Q', (w + half * ε) + half * ε ≤ w + ε := by
    intro w
    have hqqε : half * ε + half * ε ≤ ε := Q'.le_of_eqv (ExpNeg.two_halves ε)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv w (half * ε) (half * ε)))
      (Q'.add_le_add_left w (half * ε + half * ε) ε hqqε)
  refine ⟨?_, ?_⟩
  · show Trig.sinPartial (Pi.at5.approx n) M
        ≤ Trig.sinPartial (Pi.at5.approx (MhatS d n)) (RhatS d n) + ε
    have step : Trig.sinPartial (Pi.at5.approx n) M
        ≤ (Trig.sinPartial (Pi.at5.approx (MhatS d n)) (RhatS d n) + half * ε) + half * ε :=
      Q'.le_trans' _ _ _ legA1 (Q'.add_le_add_right _ _ (half * ε) legB.2)
    exact Q'.le_trans' _ _ _ step
      (h2q (Trig.sinPartial (Pi.at5.approx (MhatS d n)) (RhatS d n)))
  · show Trig.sinPartial (Pi.at5.approx (MhatS d n)) (RhatS d n)
        ≤ Trig.sinPartial (Pi.at5.approx n) M + ε
    have step : Trig.sinPartial (Pi.at5.approx (MhatS d n)) (RhatS d n)
        ≤ (Trig.sinPartial (Pi.at5.approx n) M + half * ε) + half * ε :=
      Q'.le_trans' _ _ _ legB.1 (Q'.add_le_add_right _ _ (half * ε) legA2)
    exact Q'.le_trans' _ _ _ step (h2q (Trig.sinPartial (Pi.at5.approx n) M))

/-! ## 3. The Moore–Osgood interchange, cosine leg (character-for-character twin) -/

/-- **(B2) cosine.**  `ConvergesTo (fun M => colLimCos M) (cosCat5 d)`. -/
theorem interCos (d : At5Modulus) :
    CReal.ConvergesTo (fun M => colLimCos M) (cosCat5 d) := by
  intro ε hε
  have hqpos : (0 : Q') < half * ε := ExpNeg.half_mul_pos ε hε
  have hτpos : (0 : Q') < half * ε * Q'.mkPos 1 3 (by decide) := ExpNeg.third_pos hqpos
  have hτnn : (0 : Q') ≤ half * ε * Q'.mkPos 1 3 (by decide) := Q'.le_of_lt hτpos
  refine ⟨Trig.trigModulus 1 (half * ε), fun M hMstage => ?_⟩
  refine ⟨max M (max (d.Mw (half * ε * Q'.mkPos 1 3 (by decide))) (half * ε).den),
    fun n hn => ?_⟩
  have hMn : M ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hrest : max (d.Mw (half * ε * Q'.mkPos 1 3 (by decide))) (half * ε).den ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hMwτn : d.Mw (half * ε * Q'.mkPos 1 3 (by decide)) ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hrest
  have hqdenn : (half * ε).den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hrest
  have hinv : Q'.invSucc n ≤ half * ε :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hqdenn)
      (HalfPow.invSucc_den_le (half * ε) hqpos)
  have hmk : (0 : Q') ≤ Q'.mkPos 1 3 (by decide) := Q'.le_of_lt (Q'.invSucc_pos 2)
  have hτ' : Q'.invSucc n * Q'.mkPos 1 3 (by decide)
      ≤ half * ε * Q'.mkPos 1 3 (by decide) :=
    Q'.mul_le_mul_of_nonneg_right (Q'.invSucc n) (half * ε) (Q'.mkPos 1 3 (by decide)) hinv hmk
  have reach : d.Mw (half * ε * Q'.mkPos 1 3 (by decide)) ≤ cMhatS d n :=
    Nat.le_trans
      (d.hMwmono (half * ε * Q'.mkPos 1 3 (by decide))
        (Q'.invSucc n * Q'.mkPos 1 3 (by decide))
        (ExpNeg.third_pos (Q'.invSucc_pos n)) hτ')
      (CReal.M_le_MhatE (cSeqS d) (cMCS d) n)
  have angle := d.hMw (half * ε * Q'.mkPos 1 3 (by decide)) hτpos n (cMhatS d n) hMwτn reach
  have legA_abs : Q'.abs (Trig.cosPartial (Pi.at5.approx n) M
      + -(Trig.cosPartial (Pi.at5.approx (cMhatS d n)) M)) ≤ half * ε :=
    Q'.le_trans' _ _ _
      (CRealTrig.cosPartialDiff_le (at5_pos n) (at5_le1 n)
        (at5_pos (cMhatS d n)) (at5_le1 (cMhatS d n)) hτnn angle.1 angle.2 M)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (CRealTrig.cosSumBound_le_three M) hτnn)
        (Q'.le_of_eqv (ExpNeg.third_mul_three (half * ε))))
  have legA1 : Trig.cosPartial (Pi.at5.approx n) M
      ≤ Trig.cosPartial (Pi.at5.approx (cMhatS d n)) M + half * ε :=
    ExpNeg.le_add_of_abs_sub_le legA_abs
  have legA2 : Trig.cosPartial (Pi.at5.approx (cMhatS d n)) M
      ≤ Trig.cosPartial (Pi.at5.approx n) M + half * ε :=
    ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm
        (Trig.cosPartial (Pi.at5.approx (cMhatS d n)) M)
        (Trig.cosPartial (Pi.at5.approx n) M))) legA_abs)
  have hRn : M ≤ cRhatS d n := Nat.le_trans hMn (CReal.k_le_RhatE (cSeqS d) (cMCS d) n)
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hRn
  have legB := cosRowTail (half * ε) hqpos M hMstage (cMhatS d n) e
  rw [← he] at legB
  have h2q : ∀ w : Q', (w + half * ε) + half * ε ≤ w + ε := by
    intro w
    have hqqε : half * ε + half * ε ≤ ε := Q'.le_of_eqv (ExpNeg.two_halves ε)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv w (half * ε) (half * ε)))
      (Q'.add_le_add_left w (half * ε + half * ε) ε hqqε)
  refine ⟨?_, ?_⟩
  · show Trig.cosPartial (Pi.at5.approx n) M
        ≤ Trig.cosPartial (Pi.at5.approx (cMhatS d n)) (cRhatS d n) + ε
    have step : Trig.cosPartial (Pi.at5.approx n) M
        ≤ (Trig.cosPartial (Pi.at5.approx (cMhatS d n)) (cRhatS d n) + half * ε) + half * ε :=
      Q'.le_trans' _ _ _ legA1 (Q'.add_le_add_right _ _ (half * ε) legB.2)
    exact Q'.le_trans' _ _ _ step
      (h2q (Trig.cosPartial (Pi.at5.approx (cMhatS d n)) (cRhatS d n)))
  · show Trig.cosPartial (Pi.at5.approx (cMhatS d n)) (cRhatS d n)
        ≤ Trig.cosPartial (Pi.at5.approx n) M + ε
    have step : Trig.cosPartial (Pi.at5.approx (cMhatS d n)) (cRhatS d n)
        ≤ (Trig.cosPartial (Pi.at5.approx n) M + half * ε) + half * ε :=
      Q'.le_trans' _ _ _ legB.1 (Q'.add_le_add_right _ _ (half * ε) legA2)
    exact Q'.le_trans' _ _ _ step (h2q (Trig.cosPartial (Pi.at5.approx n) M))

/-! ## 4. Discharging the interchange structure and the atom reduction -/

/-- **(B2) discharged.**  The Moore–Osgood interchange is inhabited for every
antitone-modulus datum `d`. -/
def mooreOsgood (d : At5Modulus) : MooreOsgoodInterchange d where
  interSin := interSin d
  interCos := interCos d

/-- **Atom reduced to (B1).**  With (B2) discharged unconditionally, the whole
arctan↔trig atom `ArctanTrigConverges` follows from the composition identity
`CompositionIdentity` alone — the sole remaining transcendental residual. -/
theorem atom_of_composition (d : At5Modulus) (b1 : CompositionIdentity) :
    ArctanTrigConverges :=
  atom_of_legs d b1 (mooreOsgood d)

/-- **Value identities reduced to (B1).**  Likewise the `sval`/`cval` value
identities follow from `CompositionIdentity` alone. -/
def valueIdentity_of_composition (d : At5Modulus) (b1 : CompositionIdentity) :
    ArctanValueIdentity.ValueIdentityResidual d :=
  valueIdentityResidual_of d b1 (mooreOsgood d)

end YMGap.Continuum.MooreOsgoodB2

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MooreOsgoodB2.sinCat5_approx
#print axioms YMGap.Continuum.MooreOsgoodB2.cosCat5_approx
#print axioms YMGap.Continuum.MooreOsgoodB2.interSin
#print axioms YMGap.Continuum.MooreOsgoodB2.interCos
#print axioms YMGap.Continuum.MooreOsgoodB2.mooreOsgood
#print axioms YMGap.Continuum.MooreOsgoodB2.atom_of_composition
#print axioms YMGap.Continuum.MooreOsgoodB2.valueIdentity_of_composition
