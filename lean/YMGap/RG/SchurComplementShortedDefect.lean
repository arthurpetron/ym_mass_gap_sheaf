/-
# Variational Schur-Complement / Shorted-Operator Gluing Defect and Multiplicative RG Descent

**Labels: Linear-algebraic / variational RG descent infrastructure (`V4` / `V2`, following Hayakawa
`2610.23695`, Lemma 2.4, Lemma 3.7, Proposition 3.10, and Theorem 5.2). The 4D weak-coupling
non-abelian subspace Gram-loss bound `θ̄_j ≤ c0 / side_j` (`side_j · θ̄_j ≤ c0`) remains the OPEN
Clay-level dimensional-transmutation input. NOT a proof of the open conjecture.**

* **Lemma 2.4 & Remark 2.5:** Minimizing `E(b, y) = ⟨b, L b⟩_I + ⟨y - h b, T(y - h b)⟩_Y` over `y ∈ Y`
  at fixed readout `b ∈ I` yields `E^eff(b) = ⟨b, L b⟩_I` with `0 ≤ E^eff(b) ≤ E(b, y)` and `E^eff(b) ≤ Q(b)`.
* **Lemma 3.7 (`D_τ ≥ 0`):** Evaluating `E_τ(f) = ∑_a ω_a E_ν(r_a f)` at a parent minimizer relaxes
  the common-parent constraint to independent child minimizers, so `Δ_τ(b) := E_τ^eff(b) - ∑_a ω_a E_ν^eff(R_a b) ≥ 0`.
* **Prop. 3.10 & Thm. 5.2:** Dropping `D_τ ≥ 0` at each scale avoids additive `∑ 2^j eff_j` blowup and
  leaves the clean multiplicative retention factor `∏_k (1 - θ̄_k)`.
* **Bridges:** Exports `ShortedGramLossContractionCertificate.toScaleDependentContractionCertificate` /
  `toUniformContractionCertificate` (`GroupedContractionDoor`) and proves that `side_j · θ̄_j ≤ c0`
  with `D_j ≥ 0` inhabits `ScaleDependentShiftedH1Conjecture tr c0`.
-/

import YMGap.RG.ScaleDependentGroupedContraction
import YMGap.Continuum.BF4WilsonAllNomeScaleDependentContractionInterface

namespace YMGap.RG.SchurComplementShortedDefect

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal YMGap.RG.StableDynamics
open YMGap.RG.ScaleDependentGroupedContraction
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (DyadicSmoothedTrajectory)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
  (ShiftedAnchorPackage NomeScheduleAFCalibrated)
open YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate
  (PathFacesPadded paddedNondegFloor paddedNondegFloor_pos)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
  (afA afKappa afC afHalf afPaddedZeroMomentumTrajectory)
open YMGap.Continuum.BF4WilsonAllNomeScaleDependentContractionInterface
  (PathScaleDependentShiftedContraction ScaleDependentShiftedH1Conjecture
   conjecture_closes_padded_shifted_anchor afPadded_closed_by_conjecture)

universe u v
local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Rational ring helpers -/

private theorem q_sub_cancel_add (a b : Q') : a ≈ b + (a - b) :=
  poly_identity_of_normal_eq (.var 0)
    (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (by decide) (fun | 0 => a | _ => b)

private theorem q_sub_nonneg_of_le {a b : Q'} (h : b ≤ a) : (0 : Q') ≤ a - b := by
  have h1 : b + -b ≤ a + -b := Q'.add_le_add_right b a (-b) h
  have h0 : (0 : Q') ≈ b + -b :=
    poly_identity_of_normal_eq (.const 0) (.add (.var 0) (.neg (.var 0))) (by decide) (fun _ => b)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h0) h1

private theorem q_one_sub_le_one {x : Q'} (hx : (0 : Q') ≤ x) : (1 : Q') - x ≤ 1 := by
  have h1 : (1 : Q') - x ≤ ((1 : Q') - x) + x := Q'.add_le_self_of_nonneg ((1 : Q') - x) x hx
  have h2 : ((1 : Q') - x) + x ≈ (1 : Q') :=
    poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (.var 0) (by decide) (fun | 0 => (1 : Q') | _ => x)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2)

private theorem q_one_sub_sub_eqv (x : Q') : (1 : Q') - ((1 : Q') - x) ≈ x :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))) (.var 1) (by decide)
    (fun | 0 => (1 : Q') | _ => x)

private theorem q_one_sub_lt_one {x : Q'} (hx : (0 : Q') < x) : (1 : Q') - x < (1 : Q') := by
  have hxnum : (0 : Int) < x.num := by
    have h0 : (0 : Int) * (x.den : Int) < x.num * (1 : Int) := hx
    rw [Int.zero_mul, Int.mul_one] at h0; exact h0
  show ((1 : Q') + -x).num * ((1 : Q').den : Int) < (1 : Q').num * (((1 : Q') + -x).den : Int)
  rw [Q'.add_den_cast (1 : Q') (-x)]
  have hnum : ((1 : Q') + -x).num = (1 : Int) * (x.den : Int) + (-x.num) * (1 : Int) := rfl
  have hden1 : ((1 : Q').den : Int) = 1 := rfl
  have hnum1 : (1 : Q').num = 1 := rfl
  have hdenx : ((-x).den : Int) = (x.den : Int) := rfl
  rw [hnum, hden1, hnum1, hdenx]
  simp only [Int.one_mul, Int.mul_one]
  have hlt := Int.add_lt_add_left (Int.neg_neg_of_pos hxnum) (x.den : Int)
  rw [Int.add_zero] at hlt; exact hlt

/-! ## 1. Schur complement and shorted-operator decomposition (Hayakawa Lemma 2.4 & Remark 2.5) -/

/-- Block quadratic energy `E(b, y) = ⟨b, L b⟩_I + ⟨y - h b, T(y - h b)⟩_Y` on readout space `I`
and internal space `Y` (Hayakawa `2610.23695`, Lemma 2.4 & Remark 2.5). -/
structure SchurBlockEnergy (I Y : Type) where
  Qform : I → Q'
  Lform : I → Q'
  response : I → Y
  zeroY : Y
  Tcost : Y → Y → Q'
  energy : I → Y → Q'
  Lform_nonneg : ∀ b, (0 : Q') ≤ Lform b
  Tcost_nonneg : ∀ y y', (0 : Q') ≤ Tcost y y'
  Tcost_diag_zero : ∀ y, Tcost y y ≈ 0
  energy_decomp : ∀ b y, (energy b y).eqv (Lform b + Tcost y (response b))
  compression_at_zero : ∀ b, (Qform b).eqv (energy b zeroY)

namespace SchurBlockEnergy
variable {I Y : Type} (S : SchurBlockEnergy I Y)
/-- **Hayakawa Lemma 2.4 (Variational lower bound):** `Lform b ≤ energy b y` for all `y ∈ Y`. -/
theorem schur_le_energy (b : I) (y : Y) : S.Lform b ≤ S.energy b y :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (S.Lform b) _ (S.Tcost_nonneg y (S.response b)))
    (Q'.ge_of_eqv (S.energy_decomp b y))
/-- **Hayakawa Lemma 2.4 (Minimizing response attainment):** `energy b (response b) ≈ Lform b`. -/
theorem schur_attained_at_response (b : I) :
    (S.energy b (S.response b)).eqv (S.Lform b) :=
  Q'.eqv_trans _ _ _ (S.energy_decomp b (S.response b))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (S.Lform b) _ 0 (S.Tcost_diag_zero (S.response b)))
      (QPoly.q_add_zero_eqv (S.Lform b)))
/-- **Hayakawa Remark 2.5, Eq. (13) (`0 ⪯ Short_Π(A)|_I = L ⪯ Q`):** Elimination lowers energy
relative to naive `y = 0` compression while preserving nonnegativity. -/
theorem shorted_le_compression (b : I) :
    (0 : Q') ≤ S.Lform b ∧ S.Lform b ≤ S.Qform b :=
  ⟨S.Lform_nonneg b,
    Q'.le_trans' _ _ _ (S.schur_le_energy b S.zeroY) (Q'.ge_of_eqv (S.compression_at_zero b))⟩
end SchurBlockEnergy

/-! ## 2. One-step localization and nonnegative gluing defect `D_τ ≥ 0` (Hayakawa Lemma 3.7) -/

/-- Weighted branch sum `∑_{a ∈ branches} ω_a · f(a, b)` for one-step localization. -/
def branchWeightedSum {α I : Type} (w : α → Q') (f : α → I → Q') : List α → I → Q'
  | [], _ => 0
  | a :: as, b => w a * f a b + branchWeightedSum w f as b
/-- **Gluing defect `Δ_τ(b) = ⟨b, D_τ b⟩_τ`** (Hayakawa Eq. (30)). -/
def gluingDefect {α I : Type} (parentEff : I → Q') (w : α → Q')
    (childEff : α → I → Q') (branches : List α) (b : I) : Q' :=
  parentEff b - branchWeightedSum w childEff branches b

theorem branchWeightedSum_le {α I : Type} (w : α → Q') (f g : α → I → Q')
    (hw : ∀ a, (0 : Q') ≤ w a) (hfg : ∀ a b, f a b ≤ g a b) :
    ∀ (branches : List α) (b : I),
      branchWeightedSum w f branches b ≤ branchWeightedSum w g branches b
  | [], _ => Q'.le_refl' 0
  | a :: as, b =>
      Q'.add_le_add
        (Q'.mul_le_mul_of_nonneg_left (f a b) (g a b) (w a) (hfg a b) (hw a))
        (branchWeightedSum_le w f g hw hfg as b)
/-- **One-step variational localization data (Hayakawa Lemma 3.7, Eqs. (26)–(27)).** -/
structure VariationalLocalizationStep (α I : Type) where
  branches : List α
  weight : α → Q'
  parentEff : I → Q'
  parentBranchEnergy : α → I → Q'
  childEff : α → I → Q'
  weight_nonneg : ∀ a, (0 : Q') ≤ weight a
  energy_assembly : ∀ b, (parentEff b).eqv (branchWeightedSum weight parentBranchEnergy branches b)
  child_variational_le : ∀ a b, childEff a b ≤ parentBranchEnergy a b

namespace VariationalLocalizationStep
variable {α I : Type} (L : VariationalLocalizationStep α I)

def assembledChild (b : I) : Q' := branchWeightedSum L.weight L.childEff L.branches b
def defect (b : I) : Q' := gluingDefect L.parentEff L.weight L.childEff L.branches b
/-- **Hayakawa Lemma 3.7, Eq. (28):** `E_τ^eff(b) ≈ ∑_a ω_a E_ν^eff(R_a b) + Δ_τ(b)`. -/
theorem effective_energy_decomp (b : I) :
    (L.parentEff b).eqv (L.assembledChild b + L.defect b) :=
  q_sub_cancel_add (L.parentEff b) (L.assembledChild b)
/-- **Hayakawa Lemma 3.7, Eq. (30) (`D_τ ⪰ 0`):** The gluing defect is nonnegative because
independent child minimizers relax the common-parent compatibility constraint. -/
theorem gluingDefect_nonneg (b : I) : (0 : Q') ≤ L.defect b := by
  have hsum := branchWeightedSum_le L.weight L.childEff L.parentBranchEnergy
    L.weight_nonneg L.child_variational_le L.branches b
  exact q_sub_nonneg_of_le (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (L.energy_assembly b)))
/-- **Dropping the nonnegative gluing defect (`assembledChild b ≤ parentEff b`).** -/
theorem drop_gluingDefect_lower_bound (b : I) : L.assembledChild b ≤ L.parentEff b :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (L.assembledChild b) _ (L.gluingDefect_nonneg b))
    (Q'.ge_of_eqv (L.effective_energy_decomp b))
end VariationalLocalizationStep

/-! ## 3. Multi-depth multiplicative retention without additive error blowup (Prop. 3.10 & Thm. 5.2) -/

/-- Per-step retention factor `1 - θ̄_k` from subspace Gram loss `θ̄_k` (Hayakawa Eq. (85)). -/
def retentionFactor (thetaBar : Nat → Q') (k : Nat) : Q' := (1 : Q') - thetaBar k
/-- Ordered product of retention factors `∏_{k=0}^{len-1} (1 - θ̄_{start+k})` (Hayakawa Eq. (84)). -/
def retentionProduct (thetaBar : Nat → Q') (start : Nat) : Nat → Q'
  | 0 => 1
  | len + 1 => retentionFactor thetaBar (start + len) * retentionProduct thetaBar start len

theorem retentionProduct_nonneg (thetaBar : Nat → Q')
    (h1 : ∀ n, thetaBar n ≤ (1 : Q')) (start : Nat) :
    ∀ len, (0 : Q') ≤ retentionProduct thetaBar start len
  | 0 => by change (0 : Q') ≤ 1; decide
  | len + 1 =>
      Q'.mul_nonneg _ _ (q_sub_nonneg_of_le (h1 (start + len)))
        (retentionProduct_nonneg thetaBar h1 start len)
/-- **Hayakawa Proposition 3.10 & Theorem 5.2 (Multiplicative spectral descent):**
When `(1 - θ̄_{start+k}) E_k + defect (start+k) ≤ E_{k+1}` with `θ̄_k ≤ 1` and `defect k ≥ 0`,
dropping `defect ≥ 0` at every step yields `(∏_{k < len} (1 - θ̄_{start+k})) · E_0 ≤ E_{len}`
with **zero additive error accumulation**. -/
theorem multiplicative_retention_of_nonneg_defect
    (thetaBar defect E : Nat → Q') (htheta1 : ∀ n, thetaBar n ≤ (1 : Q'))
    (hdef : ∀ n, (0 : Q') ≤ defect n) (start : Nat)
    (hstep : ∀ k, retentionFactor thetaBar (start + k) * E k + defect (start + k) ≤ E (k + 1)) :
    ∀ len, retentionProduct thetaBar start len * E 0 ≤ E len
  | 0 => Q'.le_of_eqv (Q'.one_mul_eqv (E 0))
  | len + 1 => by
      have hind := multiplicative_retention_of_nonneg_defect thetaBar defect E
        htheta1 hdef start hstep len
      have hr0 : (0 : Q') ≤ retentionFactor thetaBar (start + len) :=
        q_sub_nonneg_of_le (htheta1 (start + len))
      have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ hind hr0
      have hassoc := Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_assoc_eqv (retentionFactor thetaBar (start + len))
          (retentionProduct thetaBar start len) (E 0))) hmul
      have hdrop := Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg _ _ (hdef (start + len))) (hstep len)
      exact Q'.le_trans' _ _ _ hassoc hdrop

/-! ## 4. Connection to `ScaleDependentContractionCertificate` and `GroupedContractionDoor` -/

/-- Scale-dependent RG step whose discrepancy plus a nonnegative Schur gluing defect `defect n x y`
is bounded by `retentionFactor thetaBar n * distance x y`. -/
structure ShortedGramLossContractionCertificate (X : Type u) where
  distance : X → X → Q'
  Admissible : X → Type v
  step : Nat → X → X
  thetaBar : Nat → Q'
  defect : Nat → X → X → Q'
  thetaBarPos : ∀ n, (0 : Q') < thetaBar n
  thetaBarLeOne : ∀ n, thetaBar n ≤ (1 : Q')
  defectNonneg : ∀ n x y, (0 : Q') ≤ defect n x y
  distanceNonnegative : ∀ x y, (0 : Q') ≤ distance x y
  stepAdmissible : ∀ n x, Admissible x → Admissible (step n x)
  shortedStepBound : ∀ n x y, Admissible x → Admissible y →
    distance (step n x) (step n y) + defect n x y ≤ retentionFactor thetaBar n * distance x y

namespace ShortedGramLossContractionCertificate
/-- Dropping `0 ≤ defect n x y` gives the clean one-step contraction at rate `1 - θ̄_n`. -/
theorem step_contracts {X : Type u} (C : ShortedGramLossContractionCertificate.{u, v} X)
    (n : Nat) (x y : X) (hx : C.Admissible x) (hy : C.Admissible y) :
    C.distance (C.step n x) (C.step n y) ≤ retentionFactor C.thetaBar n * C.distance x y :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (C.distance (C.step n x) (C.step n y)) _ (C.defectNonneg n x y))
    (C.shortedStepBound n x y hx hy)
/-- Export a `ScaleDependentContractionCertificate` with rate `1 - θ̄_n`. -/
def toScaleDependentContractionCertificate {X : Type u}
    (C : ShortedGramLossContractionCertificate.{u, v} X) :
    ScaleDependentContractionCertificate.{u, v} X where
  distance := C.distance
  Admissible := C.Admissible
  step := C.step
  rate := retentionFactor C.thetaBar
  rateNonnegative n := q_sub_nonneg_of_le (C.thetaBarLeOne n)
  rateBelowOne n := q_one_sub_lt_one (C.thetaBarPos n)
  distanceNonnegative := C.distanceNonnegative
  stepAdmissible := C.stepAdmissible
  contracts := C.step_contracts
/-- The exported `rateProduct` agrees with `retentionProduct C.thetaBar`. -/
theorem rateProduct_eq_retentionProduct {X : Type u}
    (C : ShortedGramLossContractionCertificate.{u, v} X) (start : Nat) :
    ∀ len, C.toScaleDependentContractionCertificate.rateProduct start len =
      retentionProduct C.thetaBar start len
  | 0 => rfl
  | len + 1 => congrArg (retentionFactor C.thetaBar (start + len) * ·)
      (rateProduct_eq_retentionProduct C start len)
/-- Any grouped bound on `retentionProduct C.thetaBar` exports a `UniformContractionCertificate` via
`GroupedContractionDoor.toUniformContractionCertificate`. -/
def toUniformContractionCertificate {X : Type u}
    (C : ShortedGramLossContractionCertificate.{u, v} X)
    (groupLength : Nat → Nat) (macroRate : Q')
    (hmacro0 : (0 : Q') ≤ macroRate) (hmacro1 : macroRate < (1 : Q'))
    (hgroup : ∀ g, retentionProduct C.thetaBar (groupStart groupLength g) (groupLength g) ≤ macroRate) :
    UniformContractionCertificate.{u, v} X :=
  (GroupedContractionDoor.mk groupLength macroRate hmacro0 hmacro1 (fun g => by
    rw [rateProduct_eq_retentionProduct C]; exact hgroup g) :
    GroupedContractionDoor C.toScaleDependentContractionCertificate).toUniformContractionCertificate
end ShortedGramLossContractionCertificate

/-! ## 5. Connection to `ScaleDependentShiftedH1Conjecture` on `DyadicSmoothedTrajectory` -/

/-- Dropping a nonnegative `RC` gluing defect `0 ≤ D` from `A + D ≤ B` yields `A ≤ B`. -/
theorem rc_le_of_add_nonneg_le {A D B : RC} (hD : RCnonneg D) (h : RCle (RCadd A D) B) :
    RCle A B := by
  have h0 : RCle (RCadd A RCzero) (RCadd A D) := RCadd_le_add (RCle_refl A) hD
  have hA : RCadd A RCzero = A := by
    refine Quotient.inductionOn A ?_
    intro x
    exact Quotient.sound
      (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (x.approx n)))
  rw [hA] at h0; exact RCle_trans h0 h
/-- **Shorted-operator per-scale Gram-loss hypothesis (`OPEN` Clay input for 4D non-abelian YM).** -/
def PathShortedGramLossBound (tr : DyadicSmoothedTrajectory)
    (thetaBar : Nat → Q') (defect : Nat → RC) (c0 : Q') : Prop :=
  ∀ j, 1 ≤ j →
    (0 : Q') ≤ thetaBar j ∧
    RCnonneg (defect j) ∧
    RCle (RCadd (RCscale (retentionFactor thetaBar j) (tr.response j (side j))) (defect j))
      (tr.response j (side j + 1)) ∧
    Q'.ofNat (side j) * thetaBar j ≤ c0
/-- **Dropping `D_j ≥ 0` converts `PathShortedGramLossBound` into
`PathScaleDependentShiftedContraction`.** -/
theorem pathScaleDependentShiftedContraction_of_shortedGramLoss
    (tr : DyadicSmoothedTrajectory) (thetaBar : Nat → Q') (defect : Nat → RC) (c0 : Q')
    (H : PathShortedGramLossBound tr thetaBar defect c0) :
    PathScaleDependentShiftedContraction tr (retentionFactor thetaBar) c0 := by
  intro j hj
  rcases H j hj with ⟨hth0, hdef0, hstep, hscale⟩
  refine ⟨q_one_sub_le_one hth0, rc_le_of_add_nonneg_le hdef0 hstep, ?_⟩
  have heqv : (Q'.ofNat (side j) * ((1 : Q') - retentionFactor thetaBar j)).eqv
      (Q'.ofNat (side j) * thetaBar j) :=
    Q'.mul_eqv_congr_left (Q'.ofNat (side j)) _ _ (q_one_sub_sub_eqv (thetaBar j))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) hscale
/-- **Inhabiting `ScaleDependentShiftedH1Conjecture` from `PathShortedGramLossBound`.** -/
theorem shortedGramLoss_inhabits_conjecture
    (tr : DyadicSmoothedTrajectory) (thetaBar : Nat → Q') (defect : Nat → RC) (c0 : Q')
    (hc0 : (1 : Q') ≤ c0) (H : PathShortedGramLossBound tr thetaBar defect c0) :
    ScaleDependentShiftedH1Conjecture tr c0 :=
  ⟨hc0, ⟨retentionFactor thetaBar,
    pathScaleDependentShiftedContraction_of_shortedGramLoss tr thetaBar defect c0 H⟩⟩
/-- **Closing `ShiftedAnchorPackage` on any padded trajectory from `PathShortedGramLossBound`.** -/
theorem shortedGramLoss_closes_padded_shifted_anchor
    (tr : DyadicSmoothedTrajectory) (thetaBar : Nat → Q') (defect : Nat → RC)
    (c0 delta : Q') (a : Nat) (ha : 1 ≤ a) (hc0 : (1 : Q') ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta) (hpad : PathFacesPadded tr)
    (H : PathShortedGramLossBound tr thetaBar defect c0) :
    ShiftedAnchorPackage tr delta hdelta a
      (paddedNondegFloor tr) (paddedNondegFloor_pos tr) :=
  conjecture_closes_padded_shifted_anchor tr c0 delta a ha hdelta0 hdelta hcd hpad
    (shortedGramLoss_inhabits_conjecture tr thetaBar defect c0 hc0 H)
/-- **Concrete closure on `afPaddedZeroMomentumTrajectory` from `PathShortedGramLossBound`.** -/
theorem afPadded_closed_by_shortedGramLoss
    (thetaBar : Nat → Q') (defect : Nat → RC)
    (H : PathShortedGramLossBound afPaddedZeroMomentumTrajectory thetaBar defect (Q'.ofNat 2)) :
    NomeScheduleAFCalibrated afPaddedZeroMomentumTrajectory.schedule afA afKappa afC ∧
      ShiftedAnchorPackage afPaddedZeroMomentumTrajectory afHalf (by decide) 2
        (paddedNondegFloor afPaddedZeroMomentumTrajectory)
        (paddedNondegFloor_pos afPaddedZeroMomentumTrajectory) :=
  afPadded_closed_by_conjecture
    (shortedGramLoss_inhabits_conjecture afPaddedZeroMomentumTrajectory thetaBar defect
      (Q'.ofNat 2) (by decide) H)

end YMGap.RG.SchurComplementShortedDefect
