/-
`FusionBoxStrandCeilings` -- direct mass ceilings for the actual finite
Clebsch boxes at `wH = 1/2`.

The finite box is embedded, constructively and without assuming the still-open
strand *equality*, into the common-strand window

    sum_{p <= t} sum_{r <= N} c_(p+r) c_(t-p+r).

The embedding is a one-sided overcount.  Its proof expands the fusion
indicator with `fusionOK_strand`; for fixed `t`, the map

    (a,b) = (t-p+r,p+r)  |->  (p,r)

is injective.  A finite delta collapse proves the resulting sum inequality.
This is sufficient for upper bounds and does not claim the stronger A1
reindexing identity.

Round I's geometric coefficient engine bounds the common-strand tail by
`16/15` in every channel.  In a positive channel one of the two antidiagonal
legs is excited, so `PlaquetteActivity.coeffW_succ_ratio` improves that leg
from ratio `1/4` to `1/16`; the pair ratio is then `1/64`, and the tail is at
most `64/63`.  Composing these bounds with `evenFold` and `oddFold` yields the
actual ceilings

    boxSum wH N (2m)   <= (13/8) c_m^2,
    boxSum wH N (2m+1) <= (35/32) (2 c_m c_(m+1)).

Constructive contract: Mathlib-free `Nat`/`Q'`; no `Classical`,
`native_decide`, `sorry`, new axiom, or noncomputable declaration.
-/

import YMGap.Continuum.WHTailCeilingsClose
import YMGap.Continuum.PlaquetteActivity
import YMGap.Constructive.CharacterTail

namespace YMGap.Continuum.FusionBoxStrandCeilings

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionPositivity
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.MovingCutoff
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundG
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionCoreStepRoundI
open YMGap.Continuum.WHTailCeilingsClose

/-! ## 1. A finite injective strand overcount -/

/-- Delta selecting the strand point `(a,b)=(t-p+r,p+r)`. -/
def strandPointInd (a b t p r : Nat) : Q' :=
  if (a == (t - p) + r) && (b == p + r) then 1 else 0

theorem strandPointInd_nonneg (a b t p r : Nat) :
    (0 : Q') <= strandPointInd a b t p r := by
  unfold strandPointInd
  split <;> decide

/-- The selected strand point carries the actual common-strand heat weight. -/
def strandWindowKernel (w : Q') (a b t p r : Nat) : Q' :=
  strandPointInd a b t p r * ccT w t p r

theorem strandWindowKernel_nonneg {w : Q'} (hw0 : (0 : Q') <= w)
    (a b t p r : Nat) : (0 : Q') <= strandWindowKernel w a b t p r :=
  Q'.mul_nonneg _ _ (strandPointInd_nonneg a b t p r)
    (ccT_nonneg hw0 t p r)

/-- Constructive Boolean case split, kept explicit so the strand proof never
falls back to a proposition-level classical decidability instance. -/
private theorem bool_true_or_not_true (b : Bool) :
    b = true ∨ ¬ b = true := by
  cases b <;> simp

/-- The inner `r`-delta sum collapses at the explicitly supplied strand
coordinate. -/
theorem strandWindow_inner_collapse {w : Q'} {N a b t p r : Nat}
    (hb : b = p + r) (hr : r < N + 1) :
    (fsum (fun r' => strandWindowKernel w a b t p r') (N + 1)).eqv
      (strandWindowKernel w a b t p r) := by
  apply fsum_collapse
  intro r' hne
  unfold strandWindowKernel strandPointInd
  rcases bool_true_or_not_true
      ((a == (t - p) + r') && (b == p + r')) with hm | hm
  · have hm' := (Bool.and_eq_true _ _).mp hm
    have hb' : b = p + r' := beq_iff_eq.mp hm'.2
    exfalso
    omega
  · rw [if_neg hm]
    exact Q'.zero_mul_eqv _
  exact hr

/-- Every inner `r`-sum away from the supplied strand coordinate `p` is
zero. -/
theorem strandWindow_other_p_zero {w : Q'} {N a b t p q r p' : Nat}
    (ha : a = q + r) (hb : b = p + r) (ht : t = p + q)
    (hne : p' ≠ p) :
    (fsum (fun r' => strandWindowKernel w a b t p' r') (N + 1)).eqv 0 := by
  apply fsum_zero_below
  intro r' _
  unfold strandWindowKernel strandPointInd
  rcases bool_true_or_not_true
      ((a == (t - p') + r') && (b == p' + r')) with hm | hm
  · have hm' := (Bool.and_eq_true _ _).mp hm
    have ha' : a = (t - p') + r' := beq_iff_eq.mp hm'.1
    have hb' : b = p' + r' := beq_iff_eq.mp hm'.2
    exfalso
    omega
  · rw [if_neg hm]
    exact Q'.zero_mul_eqv _

/-- The outer `p`-delta sum collapses after the other-`p` vanishing lemma. -/
theorem strandWindow_outer_collapse {w : Q'} {N a b t p q r : Nat}
    (ha : a = q + r) (hb : b = p + r) (ht : t = p + q)
    (hp : p < t + 1) :
    (fsum (fun p' =>
      fsum (fun r' => strandWindowKernel w a b t p' r') (N + 1))
      (t + 1)).eqv
      (fsum (fun r' => strandWindowKernel w a b t p r') (N + 1)) := by
  apply fsum_collapse
  intro p' hne
  exact strandWindow_other_p_zero ha hb ht hne
  exact hp

/-- At the active strand point, the box kernel and window kernel agree. -/
theorem boxKer_eq_strandWindow_term {w : Q'} {a b t p q r : Nat}
    (hok : fusionOK a b t = true) (ha : a = q + r) (hb : b = p + r)
    (ht : t = p + q) :
    (boxKer w t a b).eqv (strandWindowKernel w a b t p r) := by
  have hq : t - p = q := by omega
  have hmatch :
      ((a == (t - p) + r) && (b == p + r)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor <;> omega
  have hind : strandPointInd a b t p r = 1 := by
    unfold strandPointInd
    rw [if_pos hmatch]
  unfold boxKer fusionInd strandWindowKernel ccT
  rw [if_pos hok, hind, hq, ha, hb]
  exact Q'.eqv_trans _ _ _
    (Q'.one_mul_eqv (coeffW w (q + r) * coeffW w (p + r)))
    (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (coeffW w (q + r)) (coeffW w (p + r)))
      (Q'.eqv_symm
        (Q'.one_mul_eqv (coeffW w (p + r) * coeffW w (q + r)))))

/-- Active-branch delta collapse with the strand witness supplied explicitly.
This diagnostic-strengthened statement isolates the finite injectivity step
from existential elimination in `fusionOK_strand`. -/
theorem boxKer_eq_strandWindow_of_strand {w : Q'} {N a b t p q r : Nat}
    (haN : a <= N) (hok : fusionOK a b t = true)
    (ha : a = q + r) (hb : b = p + r) (ht : t = p + q) :
    (boxKer w t a b).eqv
      (fsum (fun p => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
        (t + 1)) := by
  have hp : p < t + 1 := by omega
  have hr : r < N + 1 := by omega
  have hinner := strandWindow_inner_collapse
    (w := w) (a := a) (t := t) hb hr
  have houter := strandWindow_outer_collapse (w := w) (N := N) ha hb ht hp
  have hterm := boxKer_eq_strandWindow_term (w := w) hok ha hb ht
  exact Q'.eqv_trans _ _ _ hterm
    (Q'.eqv_symm (Q'.eqv_trans _ _ _ houter hinner))

/-- Active branch, now separated so its axiom dependencies can be audited. -/
theorem boxKer_eq_strandWindow_active {w : Q'} {N a b t : Nat}
    (haN : a <= N) (hok : fusionOK a b t = true) :
    (boxKer w t a b).eqv
      (fsum (fun p => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
        (t + 1)) := by
  obtain ⟨p, q, r, ha, hb, ht⟩ := (fusionOK_strand a b t).mp hok
  exact boxKer_eq_strandWindow_of_strand haN hok ha hb ht

/-- Inactive branch, separated from witness extraction and active collapse. -/
theorem boxKer_eq_strandWindow_inactive {w : Q'} {N a b t : Nat}
    (hok : ¬ fusionOK a b t = true) :
    (boxKer w t a b).eqv
      (fsum (fun p => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
        (t + 1)) := by
  have hzero :
      (fsum (fun p => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
        (t + 1)).eqv 0 := by
    apply fsum_zero_below
    intro p hp
    apply fsum_zero_below
    intro r _
    unfold strandWindowKernel strandPointInd
    rcases bool_true_or_not_true
        ((a == (t - p) + r) && (b == p + r)) with hm | hm
    · have hm' := (Bool.and_eq_true _ _).mp hm
      have ha : a = (t - p) + r := beq_iff_eq.mp hm'.1
      have hb : b = p + r := beq_iff_eq.mp hm'.2
      have htrue : fusionOK a b t = true :=
        (fusionOK_strand a b t).mpr
          ⟨p, t - p, r, ha, hb, by omega⟩
      exfalso
      exact hok htrue
    · rw [if_neg hm]
      exact Q'.zero_mul_eqv _
  unfold boxKer fusionInd
  rw [if_neg hok]
  exact Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv _)
    (Q'.eqv_symm hzero)

/-- On the finite cutoff square, one fusion kernel is exactly the finite sum
of its unique strand point.  This is the local injectivity statement used by
the one-sided overcount below. -/
theorem boxKer_eq_strandWindow {w : Q'} {N a b t : Nat}
    (haN : a <= N) :
    (boxKer w t a b).eqv
      (fsum (fun p => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
        (t + 1)) := by
  rcases bool_true_or_not_true (fusionOK a b t) with hok | hok
  · exact boxKer_eq_strandWindow_active haN hok
  · exact boxKer_eq_strandWindow_inactive hok

/-- The uniform rectangular common-strand majorant.  It deliberately retains
cutoff-inadmissible strand points, which is harmless for an upper bound. -/
def strandMajorant (w : Q') (N t : Nat) : Q' :=
  fsum (fun p => fsum (fun r => ccT w t p r) (N + 1)) (t + 1)

/-- For fixed `(p,r)`, the cutoff-square sum of strand deltas is at most its
single common-strand weight. -/
theorem strandBucket_le {w : Q'} (hw0 : (0 : Q') <= w)
    (N t p r : Nat) :
    fsum (fun a => fsum (fun b => strandWindowKernel w a b t p r) (N + 1))
        (N + 1) <= ccT w t p r := by
  by_cases haN : (t - p) + r <= N
  · by_cases hbN : p + r <= N
    · have haLt : (t - p) + r < N + 1 := by omega
      have hbLt : p + r < N + 1 := by omega
      have hinner :
          (fsum (fun b => strandWindowKernel w ((t - p) + r) b t p r)
            (N + 1)).eqv
            (strandWindowKernel w ((t - p) + r) (p + r) t p r) := by
        apply fsum_collapse
        intro b hne
        unfold strandWindowKernel strandPointInd
        rcases bool_true_or_not_true
            (((t - p) + r == (t - p) + r) && (b == p + r)) with hm | hm
        · have hm' := (Bool.and_eq_true _ _).mp hm
          exfalso
          exact hne (beq_iff_eq.mp hm'.2)
        · rw [if_neg hm]
          exact Q'.zero_mul_eqv _
        exact hbLt
      have houter :
          (fsum (fun a => fsum (fun b => strandWindowKernel w a b t p r) (N + 1))
            (N + 1)).eqv
            (fsum (fun b => strandWindowKernel w ((t - p) + r) b t p r)
              (N + 1)) := by
        apply fsum_collapse
        intro a hne
        apply fsum_zero_below
        intro b _
        unfold strandWindowKernel strandPointInd
        rcases bool_true_or_not_true
            ((a == (t - p) + r) && (b == p + r)) with hm | hm
        · have hm' := (Bool.and_eq_true _ _).mp hm
          exfalso
          exact hne (beq_iff_eq.mp hm'.1)
        · rw [if_neg hm]
          exact Q'.zero_mul_eqv _
        exact haLt
      have hmatch :
          (((t - p) + r == (t - p) + r) && (p + r == p + r)) = true := by
        exact (Bool.and_eq_true _ _).mpr
          ⟨beq_iff_eq.mpr rfl, beq_iff_eq.mpr rfl⟩
      have hind :
          strandPointInd ((t - p) + r) (p + r) t p r = 1 := by
        unfold strandPointInd
        rw [if_pos hmatch]
      have hterm :
          (strandWindowKernel w ((t - p) + r) (p + r) t p r).eqv
            (ccT w t p r) := by
        unfold strandWindowKernel
        rw [hind]
        exact Q'.one_mul_eqv _
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ houter (Q'.eqv_trans _ _ _ hinner hterm))
    · have hzero :
          (fsum (fun a => fsum (fun b => strandWindowKernel w a b t p r) (N + 1))
            (N + 1)).eqv 0 := by
        apply fsum_zero_below
        intro a _
        apply fsum_zero_below
        intro b hb
        unfold strandWindowKernel strandPointInd
        rcases bool_true_or_not_true
            ((a == (t - p) + r) && (b == p + r)) with hm | hm
        · have hm' := (Bool.and_eq_true _ _).mp hm
          have hb' : b = p + r := beq_iff_eq.mp hm'.2
          exfalso
          omega
        · rw [if_neg hm]
          exact Q'.zero_mul_eqv _
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero)
        (ccT_nonneg hw0 t p r)
  · have hzero :
        (fsum (fun a => fsum (fun b => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)).eqv 0 := by
      apply fsum_zero_below
      intro a ha
      apply fsum_zero_below
      intro b _
      unfold strandWindowKernel strandPointInd
      rcases bool_true_or_not_true
          ((a == (t - p) + r) && (b == p + r)) with hm | hm
      · have hm' := (Bool.and_eq_true _ _).mp hm
        have ha' : a = (t - p) + r := beq_iff_eq.mp hm'.1
        exfalso
        omega
      · rw [if_neg hm]
        exact Q'.zero_mul_eqv _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero)
      (ccT_nonneg hw0 t p r)

/-- The actual finite Clebsch box is bounded by the rectangular strand
majorant.  This proves only the direction required by the ceiling. -/
theorem boxSum_le_strandMajorant {w : Q'} (hw0 : (0 : Q') <= w)
    (N t : Nat) : boxSum w N t <= strandMajorant w N t := by
  have eexpand : (boxSum w N t).eqv
      (fsum (fun a => fsum (fun b =>
        fsum (fun p => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
          (t + 1)) (N + 1)) (N + 1)) := by
    unfold boxSum
    apply fsum_eqv_congr_lt
    intro a ha
    apply fsum_eqv_congr_lt
    intro b hb
    exact boxKer_eq_strandWindow (by omega)
  have eswap_bp :
      (fsum (fun a => fsum (fun b =>
        fsum (fun p => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
          (t + 1)) (N + 1)) (N + 1)).eqv
      (fsum (fun a => fsum (fun p =>
        fsum (fun b => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (t + 1)) (N + 1)) := by
    apply fsum_eqv_congr
    intro a
    exact fsum_swap
      (fun b p => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
      (N + 1) (t + 1)
  have eswap_ap :
      (fsum (fun a => fsum (fun p =>
        fsum (fun b => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (t + 1)) (N + 1)).eqv
      (fsum (fun p => fsum (fun a =>
        fsum (fun b => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)) (t + 1)) :=
    fsum_swap
      (fun a p => fsum (fun b =>
        fsum (fun r => strandWindowKernel w a b t p r) (N + 1)) (N + 1))
      (N + 1) (t + 1)
  have ereorder :
      (fsum (fun p => fsum (fun a =>
        fsum (fun b => fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)) (t + 1)).eqv
      (fsum (fun p => fsum (fun r =>
        fsum (fun a => fsum (fun b => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)) (t + 1)) := by
    apply fsum_eqv_congr
    intro p
    have ebr :
        (fsum (fun a => fsum (fun b =>
          fsum (fun r => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)).eqv
        (fsum (fun a => fsum (fun r =>
          fsum (fun b => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)) := by
      apply fsum_eqv_congr
      intro a
      exact fsum_swap (fun b r => strandWindowKernel w a b t p r)
        (N + 1) (N + 1)
    have ear :
        (fsum (fun a => fsum (fun r =>
          fsum (fun b => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)).eqv
        (fsum (fun r => fsum (fun a =>
          fsum (fun b => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)) :=
      fsum_swap
        (fun a r => fsum (fun b => strandWindowKernel w a b t p r) (N + 1))
        (N + 1) (N + 1)
    exact Q'.eqv_trans _ _ _ ebr ear
  have hbucket :
      fsum (fun p => fsum (fun r =>
        fsum (fun a => fsum (fun b => strandWindowKernel w a b t p r) (N + 1))
          (N + 1)) (N + 1)) (t + 1) <= strandMajorant w N t := by
    unfold strandMajorant
    apply fsum_mono_lt
    intro p hp
    apply fsum_mono_lt
    intro r _
    exact strandBucket_le hw0 N t p r
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ eexpand
      (Q'.eqv_trans _ _ _ eswap_bp (Q'.eqv_trans _ _ _ eswap_ap ereorder))))
    hbucket

/-! ## 2. Common-strand geometric tails -/

/-- Every rectangular strand tail is at most `16/15` times its zero strand. -/
theorem strandSlice_le_sixteen_fifteenths (N t p : Nat) :
    fsum (fun r => ccT wH t p r) (N + 1) <=
      qq1615 * ccT wH t p 0 := by
  have hmono : fsum (fun r => ccT wH t p r) (N + 1) <=
      fsum (fun r => geoPow qq16 r * ccT wH t p 0) (N + 1) :=
    fsum_mono (fun r => ccT_geo (by decide) (by decide) (by decide) t p r) (N + 1)
  have epull :
      (fsum (fun r => geoPow qq16 r * ccT wH t p 0) (N + 1)).eqv
        (fsum (geoPow qq16) (N + 1) * ccT wH t p 0) :=
    Q'.eqv_symm (fsum_mul_const (geoPow qq16) (ccT wH t p 0) (N + 1))
  have htail : fsum (geoPow qq16) (N + 1) * ccT wH t p 0 <=
      qq1615 * ccT wH t p 0 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (geoTail_le (N + 1))
      (ccT_nonneg (by decide) t p 0)
  exact Q'.le_trans' _ _ _ hmono
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv epull) htail)

/-- Consequently the whole rectangular majorant costs at most `16/15` times
the unshifted antidiagonal window. -/
theorem strandMajorant_le_sixteen_fifteenths (N t : Nat) :
    strandMajorant wH N t <= qq1615 * acN wH (t + 1) t := by
  unfold strandMajorant acN
  have hmono :
      fsum (fun p => fsum (fun r => ccT wH t p r) (N + 1)) (t + 1) <=
        fsum (fun p => qq1615 * ccT wH t p 0) (t + 1) :=
    fsum_mono (fun p => strandSlice_le_sixteen_fifteenths N t p) (t + 1)
  have epull :
      (fsum (fun p => qq1615 * ccT wH t p 0) (t + 1)).eqv
        (qq1615 * fsum (fun p => coeffW wH p * coeffW wH (t - p)) (t + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (fsum_const_mul qq1615 (fun p => ccT wH t p 0) (t + 1))) ?_
    apply Q'.mul_eqv_congr_left
    apply fsum_eqv_congr
    intro p
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv epull)

/-- The excited-leg ratio used in positive channels: from label `k>=1`, each
common shift costs at most `(1/16)^n`. -/
theorem excited_leg_geo (k : Nat) (hk : 1 <= k) : forall n,
    coeffW wH (k + n) <= geoPow qq16 n * coeffW wH k := by
  intro n
  induction n with
  | zero =>
      exact Q'.ge_of_eqv (Q'.one_mul_eqv (coeffW wH k))
  | succ n ih =>
      have hr := PlaquetteActivity.coeffW_succ_ratio
        (w := wH) (by decide) (by decide) (k + n) (by omega)
      have hratio : Q'.ofNat 2 * qpow wH 5 <= qq16 := by decide
      have hstep0 : coeffW wH (k + n + 1) <= qq16 * coeffW wH (k + n) :=
        Q'.le_trans' _ _ _ hr
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hratio
            (coeffW_nonneg (by decide) (k + n)))
      have hstep1 : qq16 * coeffW wH (k + n) <=
          qq16 * (geoPow qq16 n * coeffW wH k) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih (by decide)
      have e : (qq16 * (geoPow qq16 n * coeffW wH k)).eqv
          (geoPow qq16 (n + 1) * coeffW wH k) :=
        Q'.eqv_symm
          (Q'.mul_assoc_eqv qq16 (geoPow qq16 n) (coeffW wH k))
      show coeffW wH (k + (n + 1)) <=
        geoPow qq16 (n + 1) * coeffW wH k
      exact Q'.le_trans' _ _ _ hstep0
        (Q'.le_trans' _ _ _ hstep1 (Q'.le_of_eqv e))

abbrev qq64 : Q' := Q'.mkPos 1 64 (by decide)
abbrev qq6463 : Q' := Q'.mkPos 64 63 (by decide)

theorem geoPow_sixteen_quarter (n : Nat) :
    (geoPow qq16 n * geoPow qq4 n).eqv (geoPow qq64 n) := by
  induction n with
  | zero => decide
  | succ n ih =>
      refine Q'.eqv_trans _ _ _
        (mul_swap4 qq16 (geoPow qq16 n) qq4 (geoPow qq4 n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (qq16 * qq4) qq64
          (geoPow qq16 n * geoPow qq4 n) (by decide)) ?_
      exact Q'.mul_eqv_congr_left qq64 _ _ ih

/-- In a positive channel `t`, one antidiagonal leg starts at an excited
label.  Its `1/16` ratio times the other leg's `1/4` ratio gives `1/64`. -/
theorem ccT_geo_positive {t p : Nat} (ht : 1 <= t) (hp : p <= t) (r : Nat) :
    ccT wH t p r <= geoPow qq64 r * ccT wH t p 0 := by
  by_cases hpe : 1 <= p
  · have h1 := excited_leg_geo p hpe r
    have h2 := leg_geo (w := wH) (by decide) (by decide) (by decide) (t - p) r
    have hprod := prod_le_prod h1 h2
      (coeffW_nonneg (by decide) ((t - p) + r))
      (Q'.mul_nonneg _ _ (geoPow_nonneg (by decide) r)
        (coeffW_nonneg (by decide) p))
    have eswap := mul_swap4 (geoPow qq16 r) (coeffW wH p)
      (geoPow qq4 r) (coeffW wH (t - p))
    have epow :
        ((geoPow qq16 r * geoPow qq4 r) *
          (coeffW wH p * coeffW wH (t - p))).eqv
        (geoPow qq64 r * (coeffW wH p * coeffW wH (t - p))) :=
      Q'.mul_eqv_congr_right _ _ _ (geoPow_sixteen_quarter r)
    exact Q'.le_trans' _ _ _ hprod
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ eswap epow))
  · have hp0 : p = 0 := by omega
    have hq : 1 <= t - p := by omega
    have h1 := leg_geo (w := wH) (by decide) (by decide) (by decide) p r
    have h2 := excited_leg_geo (t - p) hq r
    have hprod := prod_le_prod h1 h2
      (coeffW_nonneg (by decide) ((t - p) + r))
      (Q'.mul_nonneg _ _ (geoPow_nonneg (by decide) r)
        (coeffW_nonneg (by decide) p))
    have eswap := mul_swap4 (geoPow qq4 r) (coeffW wH p)
      (geoPow qq16 r) (coeffW wH (t - p))
    have efactors : (geoPow qq4 r * geoPow qq16 r).eqv
        (geoPow qq16 r * geoPow qq4 r) := Q'.mul_comm_eqv _ _
    have epow :
        ((geoPow qq4 r * geoPow qq16 r) *
          (coeffW wH p * coeffW wH (t - p))).eqv
        (geoPow qq64 r * (coeffW wH p * coeffW wH (t - p))) :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ efactors)
        (Q'.mul_eqv_congr_right _ _ _ (geoPow_sixteen_quarter r))
    exact Q'.le_trans' _ _ _ hprod
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ eswap epow))

theorem geoTail_sixtyfour (M : Nat) : fsum (geoPow qq64) M <= qq6463 := by
  have h := CharacterTail.geom_series_le
    (geoPow qq64) (1 : Q') qq64 qq6463
    (by decide) (by decide) (by decide)
    (fun k => Q'.le_refl' (geoPow qq64 (k + 1)))
    (by decide) M
  rw [fsum_eq_finSum]
  exact h

theorem strandSlice_positive_le_sixtyfour_sixtythirds
    (N t p : Nat) (ht : 1 <= t) (hp : p <= t) :
    fsum (fun r => ccT wH t p r) (N + 1) <=
      qq6463 * ccT wH t p 0 := by
  have hmono : fsum (fun r => ccT wH t p r) (N + 1) <=
      fsum (fun r => geoPow qq64 r * ccT wH t p 0) (N + 1) :=
    fsum_mono (fun r => ccT_geo_positive ht hp r) (N + 1)
  have epull :
      (fsum (fun r => geoPow qq64 r * ccT wH t p 0) (N + 1)).eqv
        (fsum (geoPow qq64) (N + 1) * ccT wH t p 0) :=
    Q'.eqv_symm (fsum_mul_const (geoPow qq64) (ccT wH t p 0) (N + 1))
  have htail : fsum (geoPow qq64) (N + 1) * ccT wH t p 0 <=
      qq6463 * ccT wH t p 0 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (geoTail_sixtyfour (N + 1))
      (ccT_nonneg (by decide) t p 0)
  exact Q'.le_trans' _ _ _ hmono
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv epull) htail)

theorem strandMajorant_positive_le_sixtyfour_sixtythirds
    (N t : Nat) (ht : 1 <= t) :
    strandMajorant wH N t <= qq6463 * acN wH (t + 1) t := by
  unfold strandMajorant acN
  have hmono :
      fsum (fun p => fsum (fun r => ccT wH t p r) (N + 1)) (t + 1) <=
        fsum (fun p => qq6463 * ccT wH t p 0) (t + 1) :=
    fsum_mono_lt (t + 1) (fun p hp =>
      strandSlice_positive_le_sixtyfour_sixtythirds N t p ht (by omega))
  have epull :
      (fsum (fun p => qq6463 * ccT wH t p 0) (t + 1)).eqv
        (qq6463 * fsum (fun p => coeffW wH p * coeffW wH (t - p)) (t + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (fsum_const_mul qq6463 (fun p => ccT wH t p 0) (t + 1))) ?_
    apply Q'.mul_eqv_congr_left
    apply fsum_eqv_congr
    intro p
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv epull)

/-! ## 3. The exported actual-box ceilings -/

/-- Actual even-channel finite-box mass ceiling. -/
theorem boxSum_even_ceiling (N m : Nat) :
    boxSum wH N (2 * m) <= Q'.mkPos 13 8 (by decide) *
      (coeffW wH m * coeffW wH m) := by
  have hbox := boxSum_le_strandMajorant (w := wH) (by decide) N (2 * m)
  have htail := strandMajorant_le_sixteen_fifteenths N (2 * m)
  have hfold := evenFold m
  have hscale : qq1615 * acN wH (2 * m + 1) (2 * m) <=
      qq1615 * (Q'.mkPos 151 100 (by decide) *
        (coeffW wH m * coeffW wH m)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hfold (by decide)
  have hconst : qq1615 * Q'.mkPos 151 100 (by decide) <=
      Q'.mkPos 13 8 (by decide) := by decide
  have hlast : qq1615 * (Q'.mkPos 151 100 (by decide) *
        (coeffW wH m * coeffW wH m)) <=
      Q'.mkPos 13 8 (by decide) * (coeffW wH m * coeffW wH m) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv qq1615
        (Q'.mkPos 151 100 (by decide)) (coeffW wH m * coeffW wH m)))) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hconst
      (Q'.mul_nonneg _ _ (coeffW_nonneg (by decide) m)
        (coeffW_nonneg (by decide) m))
  exact Q'.le_trans' _ _ _ hbox
    (Q'.le_trans' _ _ _ htail (Q'.le_trans' _ _ _ hscale hlast))

/-- Actual odd-channel finite-box mass ceiling. -/
theorem boxSum_odd_ceiling (N m : Nat) :
    boxSum wH N (2 * m + 1) <= Q'.mkPos 35 32 (by decide) *
      (Q'.ofNat 2 * (coeffW wH m * coeffW wH (m + 1))) := by
  have hbox := boxSum_le_strandMajorant (w := wH) (by decide) N (2 * m + 1)
  have htail := strandMajorant_positive_le_sixtyfour_sixtythirds
    N (2 * m + 1) (by omega)
  have hfold := oddFold m
  have hscale : qq6463 * acN wH (2 * m + 2) (2 * m + 1) <=
      qq6463 * (Q'.mkPos 16 15 (by decide) *
        (Q'.ofNat 2 * (coeffW wH m * coeffW wH (m + 1)))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hfold (by decide)
  have hconst : qq6463 * Q'.mkPos 16 15 (by decide) <=
      Q'.mkPos 35 32 (by decide) := by decide
  have hlast : qq6463 * (Q'.mkPos 16 15 (by decide) *
        (Q'.ofNat 2 * (coeffW wH m * coeffW wH (m + 1)))) <=
      Q'.mkPos 35 32 (by decide) *
        (Q'.ofNat 2 * (coeffW wH m * coeffW wH (m + 1))) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv qq6463
        (Q'.mkPos 16 15 (by decide))
        (Q'.ofNat 2 * (coeffW wH m * coeffW wH (m + 1)))))) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hconst
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _ (coeffW_nonneg (by decide) m)
          (coeffW_nonneg (by decide) (m + 1))))
  exact Q'.le_trans' _ _ _ hbox
    (Q'.le_trans' _ _ _ htail (Q'.le_trans' _ _ _ hscale hlast))

end YMGap.Continuum.FusionBoxStrandCeilings

/-! ## Axiom gates -/

#print axioms YMGap.Continuum.FusionBoxStrandCeilings.strandWindow_inner_collapse
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.strandWindow_other_p_zero
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.strandWindow_outer_collapse
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.boxKer_eq_strandWindow_term
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.boxKer_eq_strandWindow_of_strand
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.boxKer_eq_strandWindow_active
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.boxKer_eq_strandWindow_inactive
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.boxKer_eq_strandWindow
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.boxSum_le_strandMajorant
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.strandMajorant_le_sixteen_fifteenths
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.ccT_geo_positive
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.strandMajorant_positive_le_sixtyfour_sixtythirds
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.boxSum_even_ceiling
#print axioms YMGap.Continuum.FusionBoxStrandCeilings.boxSum_odd_ceiling
