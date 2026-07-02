/-
Bernstein stage datum — inhabiting `StageData F` from a monotone vanishing
modulus, making `bernsteinSpectralCauchyOfStage` unconditional.

# GENUINELY PROVED here (`[propext]`/`[propext, Quot.sound]` only)

  * `qCeilNat_mono` — **the load-bearing new primitive.**  Monotonicity of the
    rational ceiling `q ≤ r → qCeilNat q ≤ qCeilNat r` (as `Nat ≤ Nat`), reduced
    to `Nat` floor-division monotonicity from the cross-multiplied `q ≤ r`.  This
    lifts the `Q'`-order reciprocal-antitone plumbing to the `Nat`-valued stage.
  * `qCeilNat_pos_of_pos` — `0 < q → 0 < qCeilNat q` (trivial).
  * `MonotoneOmegaVanishing F` — the **new Type-level input** (drop-in upgrade of
    `OmegaVanishing`): a *monotone* `δ`-selector.  The monotone field is exactly
    what a bare `OmegaVanishing` cannot supply (`CtsMod.ω` is non-monotone), so it
    must be given as data.
  * `bernsteinStageData : MonotoneOmegaVanishing F → StageData F` — the builder.
    Every `StageData` field is discharged: `stage`/`delta` from the selector,
    `stage_antitone` from `qCeilNat_mono` applied to the antitone budget `B`, and
    `recip_small` from the Archimedean `q_le_qCeilNat` collapse (unconditional).
  * `bernsteinSpectralCauchyOfMOV` — the final wrap: `SpectralUnifCauchy` for the
    Bernstein `QPoly` sequence, UNCONDITIONAL given a `MonotoneOmegaVanishing F`.

The stage argument uses `stage ε := qCeilNat (B ε) + 1`; the trailing `+1`
guarantees `stage_pos` structurally (no non-degeneracy hypothesis on `F.bound`),
while `qCeilNat_mono` + the `+1` still yield `stage_antitone`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorryAx`, no custom `axiom`.
-/

import YMGap.Continuum.BernsteinModulusClose
import YMGap.Continuum.SemicircleConvClosed

namespace YMGap.Continuum.BernsteinStageData

open YMGap.Constructive
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinModulusClose
open YMGap.Continuum.SemicircleConvClosed

/-! ## 1. Small `Q'`/`Nat` primitives -/

/-- **`ofNat` monotonicity** (inlined cross-multiplication, avoiding the
`WeylCharacterBound` import): `m ≤ n → ofNat m ≤ ofNat n`. -/
theorem ofNat_le_ofNat {m n : Nat} (h : m ≤ n) : Q'.ofNat m ≤ Q'.ofNat n := by
  show (Q'.ofNat m).num * ((Q'.ofNat n).den : Int)
      ≤ (Q'.ofNat n).num * ((Q'.ofNat m).den : Int)
  have hnm : (Q'.ofNat m).num = (m : Int) := rfl
  have hnn : (Q'.ofNat n).num = (n : Int) := rfl
  have hdm : ((Q'.ofNat m).den : Int) = 1 := rfl
  have hdn : ((Q'.ofNat n).den : Int) = 1 := rfl
  rw [hnm, hnn, hdm, hdn, Int.mul_one, Int.mul_one]
  exact_mod_cast h

/-- **Reciprocal is antitone on the positives** (local copy): for `0 < a ≤ b`,
`recip b ≤ recip a`.  Cross-multiplying and using `recip_num`/`recip_den`, with
both numerators positive (so the `max 1 _` clamps are inert), reduces to
`b.den·a.num ≤ a.den·b.num`, exactly `a ≤ b` cross-multiplied. -/
theorem recip_antitone {a b : Q'} (ha : (0 : Q') < a) (hab : a ≤ b) :
    Q'.recip b ≤ Q'.recip a := by
  have hanum : 0 < a.num := Q'.num_pos_of_pos ha
  have hbnum : 0 < b.num := by
    have e2 : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := hab
    have hda : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
    have hdb : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
    have hlhs : 0 < a.num * (b.den : Int) := Int.mul_pos hanum hdb
    have hrhs : 0 < b.num * (a.den : Int) := Int.lt_of_lt_of_le hlhs e2
    rcases Int.lt_or_le 0 b.num with hpos | hnp
    · exact hpos
    · exfalso
      have hle : b.num * (a.den : Int) ≤ 0 * (a.den : Int) :=
        Int.mul_le_mul_of_nonneg_right hnp (Int.le_of_lt hda)
      rw [Int.zero_mul] at hle
      omega
  show (Q'.recip b).num * ((Q'.recip a).den : Int)
     ≤ (Q'.recip a).num * ((Q'.recip b).den : Int)
  rw [Q'.recip_num, Q'.recip_num]
  have hda : ((Q'.recip a).den : Int) = a.num := by
    rw [Q'.recip_den]
    have : max 1 a.num.toNat = a.num.toNat := by omega
    rw [this]; exact Int.toNat_of_nonneg (Int.le_of_lt hanum)
  have hdb : ((Q'.recip b).den : Int) = b.num := by
    rw [Q'.recip_den]
    have : max 1 b.num.toNat = b.num.toNat := by omega
    rw [this]; exact Int.toNat_of_nonneg (Int.le_of_lt hbnum)
  rw [hda, hdb]
  have hle : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := hab
  rw [Int.mul_comm (b.den : Int) a.num, Int.mul_comm (a.den : Int) b.num]
  exact hle

/-- Nat floor-division monotonicity from a cross-multiplied bound:
for positive `b, d`, `a·d ≤ c·b → a / b ≤ c / d`. -/
theorem nat_div_le_div_of_cross {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  rw [Nat.le_div_iff_mul_le hd]
  have hdiv : a / b * b ≤ a := Nat.div_mul_le_self a b
  have hstep : (a / b * d) * b ≤ c * b := by
    have he : (a / b * d) * b = (a / b * b) * d := by rw [Nat.mul_right_comm]
    rw [he]
    exact Nat.le_trans (Nat.mul_le_mul_right d hdiv) h
  exact Nat.le_of_mul_le_mul_right hstep hb

/-- **`qCeilNat` is monotone.**  `q ≤ r → qCeilNat q ≤ qCeilNat r`.  On `0 < q.num`
both branches reduce to `Nat` floor-division monotonicity of the cross-multiplied
`q ≤ r`; the `¬ 0 < q.num` branch is `0 ≤ _`. -/
theorem qCeilNat_mono {q r : Q'} (h : q ≤ r) : qCeilNat q ≤ qCeilNat r := by
  unfold SemicircleConvClosed.qCeilNat
  by_cases hq : 0 < q.num
  · rw [if_pos hq]
    have hInt : q.num * (r.den : Int) ≤ r.num * (q.den : Int) := h
    have hr : 0 < r.num := by
      have hqd : (0 : Int) < (q.den : Int) := by exact_mod_cast q.den_pos
      have hrd : (0 : Int) < (r.den : Int) := by exact_mod_cast r.den_pos
      have hlhs : 0 < q.num * (r.den : Int) := Int.mul_pos hq hrd
      have hrhs : 0 < r.num * (q.den : Int) := Int.lt_of_lt_of_le hlhs hInt
      rcases Int.lt_or_le 0 r.num with hpos | hnp
      · exact hpos
      · exfalso
        have hle0 : r.num * (q.den : Int) ≤ 0 * (q.den : Int) :=
          Int.mul_le_mul_of_nonneg_right hnp (Int.le_of_lt hqd)
        rw [Int.zero_mul] at hle0
        omega
    rw [if_pos hr]
    have hqt : (q.num.toNat : Int) = q.num := Int.toNat_of_nonneg (Int.le_of_lt hq)
    have hrt : (r.num.toNat : Int) = r.num := Int.toNat_of_nonneg (Int.le_of_lt hr)
    have hNat : q.num.toNat * r.den ≤ r.num.toNat * q.den := by
      have hI : (q.num.toNat : Int) * (r.den : Int)
          ≤ (r.num.toNat : Int) * (q.den : Int) := by
        rw [hqt, hrt]; exact hInt
      exact_mod_cast hI
    exact Nat.add_le_add_right (nat_div_le_div_of_cross q.den_pos r.den_pos hNat) 1
  · rw [if_neg hq]
    exact Nat.zero_le _

/-- **`qCeilNat` is positive on the positives.**  `0 < q → 0 < qCeilNat q`. -/
theorem qCeilNat_pos_of_pos {q : Q'} (hq : (0 : Q') < q) : 0 < qCeilNat q := by
  have hnum : 0 < q.num := Q'.num_pos_of_pos hq
  unfold SemicircleConvClosed.qCeilNat
  rw [if_pos hnum]
  exact Nat.succ_pos _

/-! ## 2. The monotone vanishing modulus input -/

/-- **Residual input (Type-level).**  A *monotone* vanishing modulus: a
non-decreasing, positive selector `δ` with `ω(δ ε) ≤ ε`.  This upgrades
`OmegaVanishing` by the `mono` field — the exact data `stage_antitone` requires
(`CtsMod.ω` is non-monotone, so monotonicity of the threshold cannot be
recovered from a bare selector and must be supplied). -/
structure MonotoneOmegaVanishing (F : CtsMod) where
  delta : Q' → Q'
  mono  : ∀ a b : Q', a ≤ b → delta a ≤ delta b
  pos   : ∀ ε : Q', (0 : Q') < ε → (0 : Q') < delta ε
  small : ∀ ε : Q', (0 : Q') < ε → F.ω (delta ε) ≤ ε

/-! ## 3. The stage budget `C ε`, `B ε` and its monotonicity -/

/-- The ε-constant prefactor `C ε = 2M · recip(δ²) · recip(4)`. -/
def Cexpr (X d : Q') : Q' :=
  X * Q'.recip (d * d) * Q'.recip (Q'.ofNat 4)

/-- The stage budget `B ε = C ε · recip(½ε)`; the `qCeilNat` argument. -/
def Bexpr (X d he : Q') : Q' :=
  Cexpr X d * Q'.recip he

/-- `0 ≤ C ε` for `0 ≤ X`. -/
theorem Cexpr_nonneg (X d : Q') (hX : (0 : Q') ≤ X) : (0 : Q') ≤ Cexpr X d := by
  unfold Cexpr
  have h1 : (0 : Q') ≤ X * Q'.recip (d * d) :=
    Q'.mul_nonneg _ _ hX (Q'.le_of_lt (Q'.recip_pos _))
  exact Q'.mul_nonneg _ _ h1 (Q'.le_of_lt (Q'.recip_pos _))

/-- **`C` is antitone in the selector.**  For `0 ≤ X`, `0 < da ≤ db`,
`C db ≤ C da` (larger `δ` ⇒ smaller `recip(δ²)`). -/
theorem Cexpr_antitone (X da db : Q') (hX : (0 : Q') ≤ X)
    (hda : (0 : Q') < da) (hdab : da ≤ db) : Cexpr X db ≤ Cexpr X da := by
  unfold Cexpr
  have hda_nn : (0 : Q') ≤ da := Q'.le_of_lt hda
  have hdb_nn : (0 : Q') ≤ db := Q'.le_trans' 0 da db hda_nn hdab
  have hsq : da * da ≤ db * db := Q'.mul_le_mul_of_nonneg hdab hdab hdb_nn hda_nn
  have hdda : (0 : Q') < da * da := Q'.mul_pos hda hda
  have hrec : Q'.recip (db * db) ≤ Q'.recip (da * da) := recip_antitone hdda hsq
  have h1 : X * Q'.recip (db * db) ≤ X * Q'.recip (da * da) :=
    Q'.mul_le_mul_of_nonneg_left (Q'.recip (db * db)) (Q'.recip (da * da)) X hrec hX
  exact Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recip (Q'.ofNat 4)) h1
    (Q'.le_of_lt (Q'.recip_pos _))

/-- **`B` is antitone.**  For `0 ≤ X`, `0 < da ≤ db`, `0 < hea ≤ heb`,
`B db heb ≤ B da hea` (product of two antitone nonnegatives). -/
theorem Bexpr_antitone (X da db hea heb : Q') (hX : (0 : Q') ≤ X)
    (hda : (0 : Q') < da) (hdab : da ≤ db)
    (hhea : (0 : Q') < hea) (hheab : hea ≤ heb) :
    Bexpr X db heb ≤ Bexpr X da hea := by
  unfold Bexpr
  have hC : Cexpr X db ≤ Cexpr X da := Cexpr_antitone X da db hX hda hdab
  have hCa_nn : (0 : Q') ≤ Cexpr X da := Cexpr_nonneg X da hX
  have hrhe : Q'.recip heb ≤ Q'.recip hea := recip_antitone hhea hheab
  have hrheb_nn : (0 : Q') ≤ Q'.recip heb := Q'.le_of_lt (Q'.recip_pos _)
  exact Q'.mul_le_mul_of_nonneg hC hrhe hCa_nn hrheb_nn

/-! ## 4. The Archimedean reciprocal-tail collapse -/

/-- **The `recip_small` core.**  Given `B ε ≤ ofNat n` (the Archimedean threshold)
the reciprocal tail collapses: `2M·recip(δ²)·recip(n)·recip(4) ≤ ½ε`.  Proof:
multiply `C ε·recip(½ε) ≤ ofNat n` on the right by `(½ε)·recip(n) ≥ 0`, collapse
both `recip`-cancellations, then reassociate the target (swap `recip(n)`/`recip(4)`). -/
theorem recipSmall_core (X d he : Q') (_hd : (0 : Q') < d) (hhe : (0 : Q') < he)
    (n : Nat) (hn : 0 < n) (hBn : Bexpr X d he ≤ Q'.ofNat n) :
    X * Q'.recip (d * d) * Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat 4) ≤ he := by
  have hn' : (0 : Q') < Q'.ofNat n := ofNat_pos n hn
  have hw_nn : (0 : Q') ≤ he * Q'.recip (Q'.ofNat n) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hhe) (Q'.le_of_lt (Q'.recip_pos _))
  have hmul : (Cexpr X d * Q'.recip he) * (he * Q'.recip (Q'.ofNat n))
              ≤ Q'.ofNat n * (he * Q'.recip (Q'.ofNat n)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hBn hw_nn
  have hrhe_he : (Q'.recip he * he).eqv 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.recip he) he) (Q'.mul_recip_eqv he hhe)
  have lhs_eqv : ((Cexpr X d * Q'.recip he) * (he * Q'.recip (Q'.ofNat n))).eqv
                  (Cexpr X d * Q'.recip (Q'.ofNat n)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Cexpr X d) (Q'.recip he) (he * Q'.recip (Q'.ofNat n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Cexpr X d) _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.recip he) he (Q'.recip (Q'.ofNat n))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Cexpr X d) _ _
        (Q'.mul_eqv_congr_right (Q'.recip he * he) 1 (Q'.recip (Q'.ofNat n)) hrhe_he)) ?_
    exact Q'.mul_eqv_congr_left (Cexpr X d) _ _ (Q'.one_mul_eqv (Q'.recip (Q'.ofNat n)))
  have hn_rn : (Q'.ofNat n * Q'.recip (Q'.ofNat n)).eqv 1 :=
    Q'.mul_recip_eqv (Q'.ofNat n) hn'
  have rhs_eqv : (Q'.ofNat n * (he * Q'.recip (Q'.ofNat n))).eqv he := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _
        (Q'.mul_comm_eqv he (Q'.recip (Q'.ofNat n)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat n) (Q'.recip (Q'.ofNat n)) he)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat n * Q'.recip (Q'.ofNat n)) 1 he hn_rn) ?_
    exact Q'.one_mul_eqv he
  have stepA : Cexpr X d * Q'.recip (Q'.ofNat n) ≤ he :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm lhs_eqv))
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv rhs_eqv))
  have target_eqv :
      ((X * Q'.recip (d * d)) * Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat 4)).eqv
        (Cexpr X d * Q'.recip (Q'.ofNat n)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (X * Q'.recip (d * d)) (Q'.recip (Q'.ofNat n))
        (Q'.recip (Q'.ofNat 4))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (X * Q'.recip (d * d)) _ _
        (Q'.mul_comm_eqv (Q'.recip (Q'.ofNat n)) (Q'.recip (Q'.ofNat 4)))) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (X * Q'.recip (d * d)) (Q'.recip (Q'.ofNat 4))
        (Q'.recip (Q'.ofNat n)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv target_eqv) stepA

/-! ## 5. The `StageData` builder and the unconditional wrap -/

/-- **The builder.**  `MonotoneOmegaVanishing F → StageData F`.  `stage ε` is the
`qCeilNat` of the antitone budget `B ε`, plus one (for structural positivity);
`delta ε := δ(½ε)`.  Each field is discharged by §1–§4. -/
def bernsteinStageData (F : CtsMod) (MOV : MonotoneOmegaVanishing F) :
    StageData F where
  stage := fun ε =>
    qCeilNat (Bexpr (2 * F.bound) (MOV.delta (HalfPow.half * ε)) (HalfPow.half * ε)) + 1
  stage_pos := by
    intro ε _
    exact Nat.succ_pos _
  stage_antitone := by
    intro a b ha hab
    apply Nat.succ_le_succ
    apply qCeilNat_mono
    have hX : (0 : Q') ≤ 2 * F.bound :=
      Q'.mul_nonneg 2 F.bound (by decide) (bound_nonneg F)
    have hha : (0 : Q') < HalfPow.half * a := ExpNeg.half_mul_pos a ha
    have hab_half : HalfPow.half * a ≤ HalfPow.half * b :=
      Q'.mul_le_mul_of_nonneg_left a b HalfPow.half hab HalfPow.half_nonneg
    have hda : (0 : Q') < MOV.delta (HalfPow.half * a) := MOV.pos _ hha
    have hdab : MOV.delta (HalfPow.half * a) ≤ MOV.delta (HalfPow.half * b) :=
      MOV.mono _ _ hab_half
    exact Bexpr_antitone (2 * F.bound) _ _ _ _ hX hda hdab hha hab_half
  delta := fun ε => MOV.delta (HalfPow.half * ε)
  delta_pos := by
    intro ε hε
    exact MOV.pos _ (ExpNeg.half_mul_pos ε hε)
  omega_small := by
    intro ε hε
    exact MOV.small _ (ExpNeg.half_mul_pos ε hε)
  recip_small := by
    intro ε hε n hstage
    have hstage' :
        qCeilNat (Bexpr (2 * F.bound) (MOV.delta (HalfPow.half * ε))
            (HalfPow.half * ε)) + 1 ≤ n := hstage
    have hn : 0 < n := by omega
    have hq_le :
        qCeilNat (Bexpr (2 * F.bound) (MOV.delta (HalfPow.half * ε))
            (HalfPow.half * ε)) ≤ n := by omega
    have hBn :
        Bexpr (2 * F.bound) (MOV.delta (HalfPow.half * ε)) (HalfPow.half * ε)
          ≤ Q'.ofNat n :=
      Q'.le_trans' _ _ _ (q_le_qCeilNat _) (ofNat_le_ofNat hq_le)
    have hhe : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
    have hd : (0 : Q') < MOV.delta (HalfPow.half * ε) := MOV.pos _ hhe
    exact recipSmall_core (2 * F.bound) (MOV.delta (HalfPow.half * ε))
      (HalfPow.half * ε) hd hhe n hn hBn

/-- **The final wrap.**  `SpectralUnifCauchy` for the Bernstein `QPoly` sequence,
UNCONDITIONAL given a `MonotoneOmegaVanishing F`. -/
def bernsteinSpectralCauchyOfMOV (F : CtsMod) (MOV : MonotoneOmegaVanishing F)
    (lam : Q') (h0 : (0 : Q') ≤ lam) (h1 : lam ≤ 1) :=
  bernsteinSpectralCauchyOfStage F (bernsteinStageData F MOV) lam h0 h1

end YMGap.Continuum.BernsteinStageData

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BernsteinStageData.qCeilNat_mono
#print axioms YMGap.Continuum.BernsteinStageData.qCeilNat_pos_of_pos
#print axioms YMGap.Continuum.BernsteinStageData.recipSmall_core
#print axioms YMGap.Continuum.BernsteinStageData.bernsteinStageData
#print axioms YMGap.Continuum.BernsteinStageData.bernsteinSpectralCauchyOfMOV
