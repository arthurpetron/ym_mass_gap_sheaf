/-
Quantitative checkpoints for the signed harmonic chord budget.

The symmetric chord is intentionally not used at the sharp base scale: its
24/25 budget is false at k=0 although the exact compensated reserve holds.
The next scale is closed here in the exact downstream bridge signature.
-/

import YMGap.Continuum.HarmonicSignedChordBudgetBridge

namespace YMGap.Continuum.HarmonicSignedChordQuantitative

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicHalfEdgeDominance
open YMGap.Continuum.HarmonicSignedChordAbsorption
open YMGap.Continuum.HarmonicSignedChordBudgetBridge
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv
private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

def terminalDiagonalPrefix (k : Nat) : Q' :=
  coordNormSq (harmW k) (Ncut k - 1)

def terminalCoefficientTwoFloor (k : Nat) : Q' :=
  (twoInvSq k + twoInvSq k) *
    (harmonicD k * terminalDiagonalPrefix k)

/-- The terminal carrier pays at least the full coefficient-two diagonal
budget `4/(k+2)^2 · D · D_L`.  This is an unconditional quantitative
consequence of the proved harmonic half-edge dominance. -/
theorem terminalCoefficientTwoFloor_le_terminalReserve (k : Nat) :
    terminalCoefficientTwoFloor k ≤
      -(trapezoidNodeCumulative k (Ncut k - 1)) := by
  let L := Ncut k - 1
  let c := coeffW (harmW k)
  let D := harmonicD k
  let A := harmonicA k
  let DL := terminalDiagonalPrefix k
  let lam := twoInvSq k
  let X := adjCorr (harmW k) L + adjCorr (harmW k) L + oldAdj k L
  let F := (lam + lam) * (D * DL)
  have hN : 1 ≤ Ncut k := by
    unfold Ncut
    exact Nat.mul_pos (by omega) (by omega)
  have hLN : L + 1 = Ncut k := Nat.sub_add_cancel hN
  have hh := harmonic_halfEdge_full k (p := L) (Nat.le_refl L)
  have hcore : D * X ≤ (A + A) * DL := by
    dsimp [L] at hh
    simpa [profileD, profileA, halfEdgeNum, D, A, DL, X,
      terminalDiagonalPrefix, harmonicD, harmonicA, oldAdj, hLN] using hh
  have hadd := Q'.add_le_add_right _ _
    (-(((A + lam * D) + (A + lam * D)) * DL)) hcore
  have hleft :
      D * X + -(((A + lam * D) + (A + lam * D)) * DL) ≈
        trapezoidNodeCumulative k L := by
    unfold D A DL lam X L terminalDiagonalPrefix trapezoidNodeCumulative
    exact Q'.eqv_refl _
  have hright :
      (A + A) * DL + -(((A + lam * D) + (A + lam * D)) * DL) ≈
        -F := by
    let U := (A + A) * DL
    let V := (lam * D + lam * D) * DL
    have hB : ((A + lam * D) + (A + lam * D)) * DL ≈ U + V := by
      unfold U V
      ring_qeqv
    have hVF : V ≈ F := by
      unfold V F
      ring_qeqv
    refine Q'.eqv_trans _ (U + -(U + V)) _
      (Q'.add_eqv_congr_left U _ _ (Q'.neg_eqv_congr _ _ hB)) ?_
    refine Q'.eqv_trans _ (U + (-U + -V)) _
      (Q'.add_eqv_congr_left U _ _ (Q'.neg_add_eqv U V)) ?_
    refine Q'.eqv_trans _ ((U + -U) + -V) _
      (Q'.eqv_symm (Q'.add_assoc_eqv U (-U) (-V))) ?_
    refine Q'.eqv_trans _ ((0 : Q') + -V) _
      (Q'.add_eqv_congr_right _ _ (-V) (Q'.add_neg_self_eqv U)) ?_
    refine Q'.eqv_trans _ (-V) _ (q_zero_add_eqv (-V)) ?_
    exact Q'.neg_eqv_congr _ _ hVF
  have hTF : trapezoidNodeCumulative k L ≤ -F :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))
  have hneg := Q'.neg_le_neg hTF
  have hnn : -(-F) ≈ F := Q'.neg_neg_eqv F
  change F ≤ -(trapezoidNodeCumulative k L)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hnn) hneg

private theorem invSqTerm_le_oneNinth {k : Nat} (hk : 1 ≤ k) :
    invSqTerm 2 (by decide) k ≤ Q'.mkPos 1 9 (by decide) := by
  have h3 : 3 ≤ k + 2 := by omega
  have h9 : 9 ≤ (k + 2) * (k + 2) := by
    exact Nat.mul_le_mul h3 h3
  unfold invSqTerm unit
  show (Q'.mkPos 1 ((k + 2) * (k + 2)) (by omega)).num *
      ((Q'.mkPos 1 9 (by decide)).den : Int) ≤
    (Q'.mkPos 1 9 (by decide)).num *
      ((Q'.mkPos 1 ((k + 2) * (k + 2)) (by omega)).den : Int)
  simp only [Q'.mkPos_num, Q'.mkPos_den, Int.one_mul]
  exact_mod_cast h9

/-- From scale one onward, the missing terminal diagonal is at most one
ninth of the retained diagonal prefix.  Thus the retained prefix carries at
least nine tenths of the full harmonic norm. -/
theorem nine_harmonicD_le_ten_terminalDiagonalPrefix
    (k : Nat) (hk : 1 ≤ k) :
    Q'.ofNat 9 * harmonicD k ≤
      Q'.ofNat 10 * terminalDiagonalPrefix k := by
  let L := Ncut k - 1
  let e := coeffW (harmW k) (Ncut k) * coeffW (harmW k) (Ncut k)
  let DL := terminalDiagonalPrefix k
  have hN : 1 ≤ Ncut k := by
    unfold Ncut
    exact Nat.mul_pos (by omega) (by omega)
  have hLN : L + 1 = Ncut k := Nat.sub_add_cancel hN
  have hD : harmonicD k ≈ DL + e := by
    unfold harmonicD DL terminalDiagonalPrefix e
    rw [← hLN]
    exact AllWindowCorrDirichlet.coordNormSq_succ (harmW k) L
  have heU : e ≤ invSqTerm 2 (by decide) k := by
    unfold e
    exact coeffW_Ncut_sq_le_invSq k
  have hU9 := invSqTerm_le_oneNinth hk
  have he9 : e ≤ Q'.mkPos 1 9 (by decide) :=
    Q'.le_trans' _ _ _ heU hU9
  have hn9 : (0 : Q') ≤ Q'.ofNat 9 := by decide
  have h9e := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 9) he9 hn9
  have h9unit : Q'.ofNat 9 * Q'.mkPos 1 9 (by decide) ≈ (1 : Q') := by
    unfold Q'.ofNat
    show _ * (_ : Int) = _ * (_ : Int)
    decide
  have h9e1 : Q'.ofNat 9 * e ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ h9e (Q'.le_of_eqv h9unit)
  have h1DL : (1 : Q') ≤ DL := by
    unfold DL terminalDiagonalPrefix
    exact coordNormSq_ge_one (harmW_nonneg k) (Ncut k - 1)
  have h9eDL : Q'.ofNat 9 * e ≤ DL :=
    Q'.le_trans' _ _ _ h9e1 h1DL
  have hadd := Q'.add_le_add_left (Q'.ofNat 9 * DL)
    (Q'.ofNat 9 * e) DL h9eDL
  have hleft : Q'.ofNat 9 * harmonicD k ≈
      Q'.ofNat 9 * DL + Q'.ofNat 9 * e := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 9) _ _ hD) ?_
    exact Q'.mul_add_eqv _ _ _
  have hright : Q'.ofNat 9 * DL + DL ≈ Q'.ofNat 10 * DL := by
    have hnum : Q'.ofNat 10 ≈ Q'.ofNat 9 + (1 : Q') := by
      exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv 9 1)
        (Q'.add_eqv_congr_left _ _ _ (by decide))
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ DL hnum) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv DL)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

def signedChordMomentCore (k : Nat) : Q' :=
  Q'.mkPos 18 5 (by decide) *
    (invSqTerm 2 (by decide) k * (harmonicD k * harmonicD k))

def signedChordMomentCap (k : Nat) : Q' :=
  (Q'.mkPos 24 25 (by decide) * signedChordMomentCore k) +
    (Q'.mkPos 24 25 (by decide) * signedChordMomentCore k)

/-- The normalized moment core `18/5·D²/(k+2)²` fits inside the
terminal coefficient-two payment from every non-base scale onward. -/
theorem signedChordMomentCore_le_terminalCoefficientTwoFloor
    (k : Nat) (hk : 1 ≤ k) :
    signedChordMomentCore k ≤ terminalCoefficientTwoFloor k := by
  let D := harmonicD k
  let DL := terminalDiagonalPrefix k
  let u := invSqTerm 2 (by decide) k
  let scale := Q'.mkPos 2 5 (by decide) * u
  have h9 := nine_harmonicD_le_ten_terminalDiagonalPrefix k hk
  have hD0 : (0 : Q') ≤ D := Q'.le_of_lt (harmonicD_pos k)
  have hprod := Q'.mul_le_mul_of_nonneg_left _ _ D h9 hD0
  have hscale0 : (0 : Q') ≤ scale := by
    unfold scale
    exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) k)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ scale hprod hscale0
  have hleft : scale * (D * (Q'.ofNat 9 * D)) ≈ signedChordMomentCore k := by
    have hc : Q'.mkPos 2 5 (by decide) * Q'.ofNat 9 ≈
        Q'.mkPos 18 5 (by decide) := by decide
    refine Q'.eqv_trans _
      ((Q'.mkPos 2 5 (by decide) * Q'.ofNat 9) *
        (u * (D * D))) _ ?_ ?_
    · unfold scale
      ring_qeqv
    · unfold signedChordMomentCore D u
      exact Q'.mul_eqv_congr_right _ _ _ hc
  have hright : scale * (D * (Q'.ofNat 10 * DL)) ≈
      terminalCoefficientTwoFloor k := by
    have hc : Q'.mkPos 2 5 (by decide) * Q'.ofNat 10 ≈
        Q'.ofNat 4 := by decide
    have hfour : Q'.ofNat 4 ≈ Q'.ofNat 2 + Q'.ofNat 2 := by decide
    refine Q'.eqv_trans _
      ((Q'.mkPos 2 5 (by decide) * Q'.ofNat 10) *
        (u * (D * DL))) _ ?_ ?_
    · unfold scale
      ring_qeqv
    · refine Q'.eqv_trans _ (Q'.ofNat 4 * (u * (D * DL))) _
        (Q'.mul_eqv_congr_right _ _ _ hc) ?_
      refine Q'.eqv_trans _ ((Q'.ofNat 4 * u) * (D * DL)) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        (((Q'.ofNat 2 + Q'.ofNat 2) * u) * (D * DL)) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ u hfour)) ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat 2 * u + Q'.ofNat 2 * u) * (D * DL)) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.add_mul_eqv _ _ _)) ?_
      unfold terminalCoefficientTwoFloor twoInvSq D DL u
      exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-- The concrete moment cap is below the exact `24/25` signed-chord target.
Thus after the base-scale split the sole remaining estimate is the direct
upper bound of the signed chord plus two terminal corrections by
`signedChordMomentCap`. -/
theorem signedChordMomentCap_le_target (k : Nat) (hk : 1 ≤ k) :
    signedChordMomentCap k ≤
      (Q'.mkPos 24 25 (by decide) *
          (-(trapezoidNodeCumulative k (Ncut k - 1) *
            driftSqFactor k 0))) +
        (Q'.mkPos 24 25 (by decide) *
          (-(trapezoidNodeCumulative k (Ncut k - 1) *
            driftSqFactor k 0))) := by
  have hcore := signedChordMomentCore_le_terminalCoefficientTwoFloor k hk
  have hfloor := terminalCoefficientTwoFloor_le_terminalReserve k
  have hct : signedChordMomentCore k ≤
      -(trapezoidNodeCumulative k (Ncut k - 1)) :=
    Q'.le_trans' _ _ _ hcore hfloor
  have hc0 : (0 : Q') ≤ Q'.mkPos 24 25 (by decide) := by decide
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.mkPos 24 25 (by decide)) hct hc0
  have hadd := Q'.add_le_add hscaled hscaled
  have hG0 := driftSqFactor_zero_eqv k
  have htarget :
      (Q'.mkPos 24 25 (by decide) *
          (-(trapezoidNodeCumulative k (Ncut k - 1)))) +
        (Q'.mkPos 24 25 (by decide) *
          (-(trapezoidNodeCumulative k (Ncut k - 1)))) ≈
      (Q'.mkPos 24 25 (by decide) *
          (-(trapezoidNodeCumulative k (Ncut k - 1) *
            driftSqFactor k 0))) +
        (Q'.mkPos 24 25 (by decide) *
          (-(trapezoidNodeCumulative k (Ncut k - 1) *
            driftSqFactor k 0))) := by
    have hm : trapezoidNodeCumulative k (Ncut k - 1) *
        driftSqFactor k 0 ≈ trapezoidNodeCumulative k (Ncut k - 1) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hG0) (Q'.mul_one_eqv _)
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hm)))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hm)))
  unfold signedChordMomentCap
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv htarget)

/-! ## Lossless positive-tail moment form -/

def intervalSum (f : Nat → Q') (s n : Nat) : Q' :=
  fsum (fun j => f (s + j)) n

def harmonicChordWeight (k p : Nat) : Q' :=
  driftSqFactor k p *
    (unit (driftDen k) (driftDen_pos k) *
      (Q'.ofNat ((4 * p + 5) + 1) *
        ((1 : Q') + qpow (driftRatio k) (4 * p + 5))))

def harmonicChordGrowthFactor (k p : Nat) : Q' :=
  Q'.ofNat 2 +
    Q'.ofNat (4 * p + 6) * unit (driftDen k) (driftDen_pos k)

def harmonicChordCumulativeMajorant (k s n : Nat) : Q' :=
  harmonicChordGrowthFactor k (s + n) *
    (driftSqFactor k (s + n) + -(driftSqFactor k s))

private theorem one_le_qpow_here {r : Q'} (hr : (1 : Q') ≤ r) : ∀ n,
    (1 : Q') ≤ qpow r n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hp0 : (0 : Q') ≤ qpow r n :=
        qpow_nonneg r (Q'.le_trans' _ _ _ (by decide) hr) n
      have hm := Q'.mul_le_mul_of_nonneg_left _ _ (qpow r n) hr hp0
      exact Q'.le_trans' _ _ _ (one_le_qpow_here hr n)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) hm)

private theorem ofNat_le_geomSum_of_one_le {r : Q'} (hr : (1 : Q') ≤ r) :
    ∀ n, Q'.ofNat n ≤ HeatKernelRGStep.geomSum r n
  | 0 => by
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ Q'.ofNat_zero_eqv
        (Q'.eqv_refl _))
  | n + 1 => by
      have hadd := Q'.add_le_add
        (ofNat_le_geomSum_of_one_le hr n) (one_le_qpow_here hr n)
      have hleft : Q'.ofNat (n + 1) ≈ Q'.ofNat n + (1 : Q') := by
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hadd

private theorem qpow_mono_exp_of_one_le {r : Q'} (hr : (1 : Q') ≤ r)
    {a b : Nat} (hab : a ≤ b) : qpow r a ≤ qpow r b := by
  obtain ⟨d, hbd⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  subst b
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      have hp0 : (0 : Q') ≤ qpow r (a + d) :=
        qpow_nonneg r (Q'.le_trans' _ _ _ (by decide) hr) _
      have hm := Q'.mul_le_mul_of_nonneg_left _ _
        (qpow r (a + d)) hr hp0
      have hs : qpow r (a + d) ≤ qpow r (a + (d + 1)) := by
        have he : qpow r (a + (d + 1)) ≈ qpow r (a + d) * r := by
          rw [show a + (d + 1) = (a + d) + 1 by omega]
          exact Q'.eqv_refl _
        exact Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (Q'.mul_one_eqv _))
          (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.eqv_symm he)))
      exact Q'.le_trans' _ _ _ (ih (by omega)) hs

private theorem geomSum_le_ofNat_mul_qpow {r : Q'} (hr : (1 : Q') ≤ r) :
    ∀ n, HeatKernelRGStep.geomSum r n ≤ Q'.ofNat n * qpow r n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      have ih := geomSum_le_ofNat_mul_qpow hr n
      have hadd := Q'.add_le_add_right _ _ (qpow r n) ih
      have hcollect : Q'.ofNat n * qpow r n + qpow r n ≈
          Q'.ofNat (n + 1) * qpow r n := by
        have hn : Q'.ofNat (n + 1) ≈ Q'.ofNat n + (1 : Q') := by
          exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
            (Q'.add_eqv_congr_left _ _ _ (by decide))
        refine Q'.eqv_trans _
          (Q'.ofNat n * qpow r n + (1 : Q') * qpow r n) _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.one_mul_eqv _))) ?_
        refine Q'.eqv_trans _ ((Q'.ofNat n + (1 : Q')) * qpow r n) _
          (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
        exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hn)
      have hp := qpow_mono_exp_of_one_le hr
        (show n ≤ n + 1 by omega)
      have hn0 : (0 : Q') ≤ Q'.ofNat (n + 1) :=
        ExpNeg.ofNat_nonneg' _
      have hscale := Q'.mul_le_mul_of_nonneg_left _ _
        (Q'.ofNat (n + 1)) hp hn0
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect) hscale)

private theorem fsum_shift_cons_here (g : Nat → Q') : ∀ n,
    fsum g (n + 1) ≈ g 0 + fsum (fun i => g (i + 1)) n
  | 0 => by
      change (0 + g 0 : Q') ≈ g 0 + 0
      exact Q'.eqv_trans _ _ _ (q_zero_add_eqv _) (Q'.eqv_symm (q_add_zero_eqv _))
  | n + 1 => by
      rw [fsum_succ]
      refine Q'.eqv_trans _
        ((g 0 + fsum (fun i => g (i + 1)) n) + g (n + 1)) _
        (Q'.add_eqv_congr_right _ _ _ (fsum_shift_cons_here g n)) ?_
      exact Q'.add_assoc_eqv _ _ _

private theorem fsum_reverse_here (G : Nat → Q') : ∀ n,
    fsum (fun p => G (n - p)) (n + 1) ≈ fsum G (n + 1)
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      refine Q'.eqv_trans _ _ _
        (fsum_shift_cons_here (fun p => G ((n + 1) - p)) (n + 1)) ?_
      have hc : fsum (fun i => G ((n + 1) - (i + 1))) (n + 1) ≈
          fsum (fun i => G (n - i)) (n + 1) := by
        exact CubeRatioBounds.fsum_eqv_congr _ _
          (fun i => Q'.eqv_of_eq (congrArg G (by omega))) (n + 1)
      refine Q'.eqv_trans _
        (G (n + 1) + fsum (fun i => G (n - i)) (n + 1)) _
        (Q'.add_eqv_congr_left _ _ _ hc) ?_
      refine Q'.eqv_trans _ (G (n + 1) + fsum G (n + 1)) _
        (Q'.add_eqv_congr_left _ _ _ (fsum_reverse_here G n)) ?_
      rw [fsum_succ]
      exact Q'.add_comm_eqv _ _

private theorem fsum_const_here (c : Q') : ∀ n,
    fsum (fun _ => c) n ≈ Q'.ofNat n * c
  | 0 => by
      exact Q'.eqv_symm (Q'.eqv_trans _ ((0 : Q') * c) _
        (Q'.mul_eqv_congr_right _ _ c Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv c))
  | n + 1 => by
      rw [fsum_succ]
      refine Q'.eqv_trans _ (Q'.ofNat n * c + c) _
        (Q'.add_eqv_congr_right _ _ _ (fsum_const_here c n)) ?_
      have hn : Q'.ofNat (n + 1) ≈ Q'.ofNat n + (1 : Q') := by
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      refine Q'.eqv_trans _ (Q'.ofNat n * c + (1 : Q') * c) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv c))) ?_
      refine Q'.eqv_trans _ ((Q'.ofNat n + (1 : Q')) * c) _
        (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
      exact Q'.mul_eqv_congr_right _ _ c (Q'.eqv_symm hn)

private theorem fsum_qpow_eq_geomSum (r : Q') : ∀ n,
    fsum (qpow r) n ≈ HeatKernelRGStep.geomSum r n
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      rw [fsum_succ]
      change fsum (qpow r) n + qpow r n ≈
        HeatKernelRGStep.geomSum r n + qpow r n
      exact Q'.add_eqv_congr_right _ _ _ (fsum_qpow_eq_geomSum r n)

def harmonicEndpointPairGap (k n i : Nat) : Q' :=
  (qpow (driftRatio k) i + -(1 : Q')) *
    (qpow (driftRatio k) (n - 1 - i) + -(1 : Q'))

private theorem endpoint_pair_algebra (a b : Q') :
    (1 : Q') + a * b ≈
      (a + b) + (a + -(1 : Q')) * (b + -(1 : Q')) := by
  have hneg (x : Q') : x + -(1 : Q') ≈ -((1 : Q') + -x) := by
    have h : -((1 : Q') + -x) ≈ -(1 : Q') + x := by
      refine Q'.eqv_trans _ (-(1 : Q') + -(-x)) _
        (Q'.neg_add_eqv _ _) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv x)
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ h (Q'.add_comm_eqv _ _))
  have hprod : (a + -(1 : Q')) * (b + -(1 : Q')) ≈
      ((1 : Q') + -a) * ((1 : Q') + -b) := by
    refine Q'.eqv_trans _
      (-((1 : Q') + -a) * (b + -(1 : Q'))) _
      (Q'.mul_eqv_congr_right _ _ _ (hneg a)) ?_
    refine Q'.eqv_trans _
      (-((1 : Q') + -a) * -((1 : Q') + -b)) _
      (Q'.mul_eqv_congr_left _ _ _ (hneg b)) ?_
    refine Q'.eqv_trans _
      (-(((1 : Q') + -a) * -((1 : Q') + -b))) _
      (Q'.neg_mul_eqv _ _) ?_
    refine Q'.eqv_trans _
      (-(-(((1 : Q') + -a) * ((1 : Q') + -b)))) _
      (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv _ _)) ?_
    exact Q'.neg_neg_eqv _
  have hone :=
    BondMovingRetuneFix.oneSub_mul_oneSub a b
  have hgap : (a + -(1 : Q')) * (b + -(1 : Q')) ≈
      ((1 : Q') + -(a + b)) + a * b := by
    refine Q'.eqv_trans _ _ _ hprod ?_
    refine Q'.eqv_trans _ (((1 : Q') + -(b + a)) + b * a) _ hone ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left (1 : Q') _ _
        (Q'.neg_eqv_congr _ _ (Q'.add_comm_eqv b a)))
      (Q'.mul_comm_eqv b a)
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    ((a + b) + (((1 : Q') + -(a + b)) + a * b)) _
    (Q'.add_eqv_congr_left _ _ _ hgap) ?_
  refine Q'.eqv_trans _
    ((a + b) + ((-(a + b) + (1 : Q')) + a * b)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))) ?_
  refine Q'.eqv_trans _
    ((a + b) + (-(a + b) + ((1 : Q') + a * b))) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    (((a + b) + -(a + b)) + ((1 : Q') + a * b)) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + ((1 : Q') + a * b)) _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv _)) ?_
  exact q_zero_add_eqv _

private theorem endpoint_pair_decomposition
    (k n i : Nat) (hi : i < n) :
    (1 : Q') + qpow (driftRatio k) (n - 1) ≈
      (qpow (driftRatio k) i +
        qpow (driftRatio k) (n - 1 - i)) +
          harmonicEndpointPairGap k n i := by
  have hidx : i + (n - 1 - i) = n - 1 := by omega
  have hp : qpow (driftRatio k) (n - 1) ≈
      qpow (driftRatio k) i * qpow (driftRatio k) (n - 1 - i) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg (qpow (driftRatio k)) (Eq.symm hidx)))
      (HeatKernelRGStep.qpow_add _ _ _)
  unfold harmonicEndpointPairGap
  refine Q'.eqv_trans _
    ((1 : Q') +
      qpow (driftRatio k) i * qpow (driftRatio k) (n - 1 - i)) _
    (Q'.add_eqv_congr_left _ _ _ hp) ?_
  exact endpoint_pair_algebra _ _

def harmonicEndpointQuadraticCorrection (k n : Nat) : Q' :=
  Q'.ofNat n * Q'.ofNat n *
    (unit (driftDen k) (driftDen_pos k) *
      unit (driftDen k) (driftDen_pos k) *
        qpow (driftRatio k) (n - 1))

private theorem harmonicEndpointPairGap_le_correction
    (k n i : Nat) (hi : i < n) :
    harmonicEndpointPairGap k n i ≤
      harmonicEndpointQuadraticCorrection k n := by
  let r := driftRatio k
  let u := unit (driftDen k) (driftDen_pos k)
  let N := Q'.ofNat n
  let Si := HeatKernelRGStep.geomSum r i
  let Sj := HeatKernelRGStep.geomSum r (n - 1 - i)
  let Pi := qpow r i
  let Pj := qpow r (n - 1 - i)
  have hdi : qpow r i + -(1 : Q') ≈ u * Si := by
    unfold r u Si
    exact qpow_driftRatio_sub_one_eqv k i
  have hdj : qpow r (n - 1 - i) + -(1 : Q') ≈ u * Sj := by
    unfold r u Sj
    exact qpow_driftRatio_sub_one_eqv k (n - 1 - i)
  have hleft : harmonicEndpointPairGap k n i ≈ (u * Si) * (u * Sj) := by
    unfold harmonicEndpointPairGap
    refine Q'.eqv_trans _ ((u * Si) *
      (qpow (driftRatio k) (n - 1 - i) + -(1 : Q'))) _
      (Q'.mul_eqv_congr_right _ _ _ hdi) ?_
    exact Q'.mul_eqv_congr_left _ _ _ hdj
  have hSi0 : (0 : Q') ≤ Si := by
    unfold Si r
    exact HeatKernelRGStep.geomSum_nonneg
      (Q'.le_trans' _ _ _ (by decide) (one_le_driftRatio k)) _
  have hSj0 : (0 : Q') ≤ Sj := by
    unfold Sj r
    exact HeatKernelRGStep.geomSum_nonneg
      (Q'.le_trans' _ _ _ (by decide) (one_le_driftRatio k)) _
  have hPi0 : (0 : Q') ≤ Pi := by
    unfold Pi r
    exact qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _
  have hPj0 : (0 : Q') ≤ Pj := by
    unfold Pj r
    exact qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _
  have hNi : Q'.ofNat i ≤ N := by
    unfold N
    exact MovingCutoff.ofNat_le_ofNat' (by omega)
  have hNj : Q'.ofNat (n - 1 - i) ≤ N := by
    unfold N
    exact MovingCutoff.ofNat_le_ofNat' (by omega)
  have hSi : Si ≤ N * Pi := by
    have h0 := geomSum_le_ofNat_mul_qpow (one_le_driftRatio k) i
    have hs := Q'.mul_le_mul_of_nonneg_right _ _ Pi hNi hPi0
    unfold Si Pi r
    exact Q'.le_trans' _ _ _ h0 hs
  have hSj : Sj ≤ N * Pj := by
    have h0 := geomSum_le_ofNat_mul_qpow (one_le_driftRatio k) (n - 1 - i)
    have hs := Q'.mul_le_mul_of_nonneg_right _ _ Pj hNj hPj0
    unfold Sj Pj r
    exact Q'.le_trans' _ _ _ h0 hs
  have hu0 : (0 : Q') ≤ u := by
    unfold u
    exact unit_nonneg _ _
  have hui := Q'.mul_le_mul_of_nonneg_left _ _ u hSi hu0
  have huj := Q'.mul_le_mul_of_nonneg_left _ _ u hSj hu0
  have huSi0 : (0 : Q') ≤ u * Si := Q'.mul_nonneg _ _ hu0 hSi0
  have huNPi0 : (0 : Q') ≤ u * (N * Pi) := by
    exact Q'.mul_nonneg _ _ hu0
      (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) hPi0)
  have hprod1 := Q'.mul_le_mul_of_nonneg_right _ _ (u * Sj) hui
    (Q'.mul_nonneg _ _ hu0 hSj0)
  have hprod2 := Q'.mul_le_mul_of_nonneg_left _ _ (u * (N * Pi)) huj huNPi0
  have hprod : (u * Si) * (u * Sj) ≤
      (u * (N * Pi)) * (u * (N * Pj)) :=
    Q'.le_trans' _ _ _ hprod1 hprod2
  have hidx : i + (n - 1 - i) = n - 1 := by omega
  have hp : Pi * Pj ≈ qpow r (n - 1) := by
    unfold Pi Pj
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg (qpow r) (Eq.symm hidx)))
      (HeatKernelRGStep.qpow_add r i (n - 1 - i)))
  have hright : (u * (N * Pi)) * (u * (N * Pj)) ≈
      harmonicEndpointQuadraticCorrection k n := by
    dsimp [N, u]
    unfold harmonicEndpointQuadraticCorrection
    refine Q'.eqv_trans _
      (Q'.ofNat n * Q'.ofNat n *
        (unit (driftDen k) (driftDen_pos k) *
          unit (driftDen k) (driftDen_pos k) * (Pi * Pj))) _
      (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hp)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv hright))

/-- Second-order symmetric endpoint estimate.  Unlike the earlier
`2+n·u` factor, its excess above two is quadratic in the reciprocal drift
step; the proof is an exact finite pairing of the two endpoint increments. -/
theorem chord_endpoint_le_quadratic_geom (k n : Nat) :
    Q'.ofNat n *
        ((1 : Q') + qpow (driftRatio k) (n - 1)) ≤
      (Q'.ofNat 2 + harmonicEndpointQuadraticCorrection k n) *
        HeatKernelRGStep.geomSum (driftRatio k) n := by
  cases n with
  | zero =>
      have hL : Q'.ofNat 0 *
          ((1 : Q') + qpow (driftRatio k) (0 - 1)) ≈ (0 : Q') := by
        exact Q'.eqv_trans _ ((0 : Q') * _) _
          (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv _)
      have hR : (Q'.ofNat 2 + harmonicEndpointQuadraticCorrection k 0) *
          HeatKernelRGStep.geomSum (driftRatio k) 0 ≈ (0 : Q') :=
        Q'.mul_zero_eqv _
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
        (Q'.ge_of_eqv hR)
  | succ m =>
      let r := driftRatio k
      let S := HeatKernelRGStep.geomSum r (m + 1)
      let E := (1 : Q') + qpow r m
      let C := harmonicEndpointQuadraticCorrection k (m + 1)
      let gap := fun i => harmonicEndpointPairGap k (m + 1) i
      have hterm : ∀ i, i < m + 1 → E ≈
          (qpow r i + qpow r (m - i)) + gap i := by
        intro i hi
        unfold E gap r
        simpa using endpoint_pair_decomposition k (m + 1) i hi
      have hcongr := CubeRatioBounds.fsum_eqv_congr_lt
        (fun _ => E)
        (fun i => (qpow r i + qpow r (m - i)) + gap i)
        (m + 1) hterm
      have hconst := fsum_const_here E (m + 1)
      have hsplit1 := CubeRatioBounds.fsum_add
        (fun i => qpow r i + qpow r (m - i)) gap (m + 1)
      have hsplit2 := CubeRatioBounds.fsum_add
        (fun i => qpow r i) (fun i => qpow r (m - i)) (m + 1)
      have hrev := fsum_reverse_here (qpow r) m
      have hgeom : fsum (qpow r) (m + 1) ≈ S := by
        unfold S
        exact fsum_qpow_eq_geomSum r (m + 1)
      have hsumdec : Q'.ofNat (m + 1) * E ≈
          (S + S) + fsum gap (m + 1) := by
        refine Q'.eqv_trans _ (fsum (fun _ => E) (m + 1)) _
          (Q'.eqv_symm hconst) ?_
        refine Q'.eqv_trans _
          (fsum (fun i => (qpow r i + qpow r (m - i)) + gap i) (m + 1)) _
          hcongr ?_
        refine Q'.eqv_trans _
          (fsum (fun i => qpow r i + qpow r (m - i)) (m + 1) +
            fsum gap (m + 1)) _ hsplit1 ?_
        refine Q'.add_eqv_congr_right _ _ _ ?_
        refine Q'.eqv_trans _
          (fsum (fun i => qpow r i) (m + 1) +
            fsum (fun i => qpow r (m - i)) (m + 1)) _ hsplit2 ?_
        exact Q'.add_eqv_congr' hgeom (Q'.eqv_trans _ _ _ hrev hgeom)
      have hgap : fsum gap (m + 1) ≤ Q'.ofNat (m + 1) * C := by
        have hm := CubeRatioBounds.fsum_mono_lt (m + 1)
          (fun i hi => harmonicEndpointPairGap_le_correction k (m + 1) i hi)
        exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (fsum_const_here C (m + 1)))
      have hNS : Q'.ofNat (m + 1) ≤ S := by
        unfold S r
        exact ofNat_le_geomSum_of_one_le (one_le_driftRatio k) (m + 1)
      have hC0 : (0 : Q') ≤ C := by
        unfold C harmonicEndpointQuadraticCorrection
        exact Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) (ExpNeg.ofNat_nonneg' _))
          (Q'.mul_nonneg _ _
            (Q'.mul_nonneg _ _ (unit_nonneg _ _) (unit_nonneg _ _))
            (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _))
      have hNC := Q'.mul_le_mul_of_nonneg_right _ _ C hNS hC0
      have hgapS : fsum gap (m + 1) ≤ C * S :=
        Q'.le_trans' _ _ _ hgap
          (Q'.le_trans' _ _ _ hNC (Q'.le_of_eqv (Q'.mul_comm_eqv S C)))
      have hadd := Q'.add_le_add_left (S + S) _ _ hgapS
      have hright : (S + S) + C * S ≈ (Q'.ofNat 2 + C) * S := by
        have htwo : Q'.ofNat 2 * S ≈ S + S := by
          refine Q'.eqv_trans _ (((1 : Q') + (1 : Q')) * S) _
            (Q'.mul_eqv_congr_right _ _ S (by decide)) ?_
          refine Q'.eqv_trans _ ((1 : Q') * S + (1 : Q') * S) _
            (Q'.add_mul_eqv _ _ _) ?_
          exact Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)
        refine Q'.eqv_trans _ (Q'.ofNat 2 * S + C * S) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm htwo)) ?_
        exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
      dsimp [E, S, C, r] at hsumdec hright hadd ⊢
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsumdec)
        (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

def harmonicChordQuadraticFactor (k p : Nat) : Q' :=
  Q'.ofNat 2 + harmonicEndpointQuadraticCorrection k (4 * p + 6)

def harmonicChordQuadraticWeight (k p : Nat) : Q' :=
  harmonicChordQuadraticFactor k p *
    (driftSqFactor k (p + 1) + -(driftSqFactor k p))

def harmonicChordQuadraticCumulative (k s n : Nat) : Q' :=
  intervalSum (harmonicChordQuadraticWeight k) s n

def signedChordQuadraticNodeMoment (k s n : Nat) : Q' :=
  fsum (fun j =>
    trapezoidNodeCoeff k (s + j + 1) *
      harmonicChordQuadraticCumulative k s (j + 1)) n

/-- The symmetric harmonic chord has a genuinely second-order varying
growth carrier.  Its correction above factor two is quadratic in the drift
step, rather than the linear correction used by
`harmonicChordWeight_le_growthIncrement`. -/
theorem harmonicChordWeight_le_quadraticIncrement (k p : Nat) :
    harmonicChordWeight k p ≤ harmonicChordQuadraticWeight k p := by
  let G := driftSqFactor k p
  let u := unit (driftDen k) (driftDen_pos k)
  let n := 4 * p + 6
  let S := HeatKernelRGStep.geomSum (driftRatio k) n
  have hcore := chord_endpoint_le_quadratic_geom k n
  have hu0 : (0 : Q') ≤ u := unit_nonneg _ _
  have hG0 : (0 : Q') ≤ G := by
    unfold G driftSqFactor
    exact Q'.mul_nonneg _ _
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ u hcore hu0
  have hGu := Q'.mul_le_mul_of_nonneg_left _ _ G hu hG0
  have hleft : harmonicChordWeight k p ≈
      G * (u * (Q'.ofNat n *
        ((1 : Q') + qpow (driftRatio k) (n - 1)))) := by
    unfold harmonicChordWeight G u n
    rw [show 4 * p + 5 = 4 * p + 6 - 1 by omega]
    exact Q'.eqv_refl _
  have hinc := driftSqFactor_increment_geom_eqv k p
  have hright :
      G * (u * ((Q'.ofNat 2 +
          harmonicEndpointQuadraticCorrection k n) * S)) ≈
        harmonicChordQuadraticWeight k p := by
    have hrearr :
        G * (u * ((Q'.ofNat 2 +
            harmonicEndpointQuadraticCorrection k n) * S)) ≈
          (Q'.ofNat 2 + harmonicEndpointQuadraticCorrection k n) *
            (G * (u * S)) := by
      ring_qeqv
    refine Q'.eqv_trans _ _ _ hrearr ?_
    unfold harmonicChordQuadraticWeight harmonicChordQuadraticFactor n G u S
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hinc)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hGu (Q'.le_of_eqv hright))

/-- Exact first-scale audit of the second-order carrier: unlike the
linear-growth endpoint pull, the sharper varying carrier plus both terminal
corrections fits the symbolic cap at `k=5`.  This is a derived rational
checkpoint, not a measured constant. -/
theorem quadraticNodeMoment_cap_k5 :
    signedChordQuadraticNodeMoment 5 0 (Ncut 5 - 1) +
        (trapezoidTerminalCorrection 5 + trapezoidTerminalCorrection 5) ≤
      signedChordMomentCap 5 := by
  unfold signedChordQuadraticNodeMoment harmonicChordQuadraticCumulative
    harmonicChordQuadraticWeight harmonicChordQuadraticFactor
    harmonicEndpointQuadraticCorrection intervalSum signedChordMomentCap
    signedChordMomentCore trapezoidTerminalCorrection trapezoidNodeCoeff
    harmonicD harmonicA twoInvSq oldAdj oldDiag coordNormSq adjCorr
    driftSqFactor driftRatio driftDen harmW harmU oneSub unit invSqTerm
    coeffW dimQ c4 Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

private theorem qpow_driftRatio_eqv_one_add_geom (k n : Nat) :
    qpow (driftRatio k) n ≈
      (1 : Q') + unit (driftDen k) (driftDen_pos k) *
        HeatKernelRGStep.geomSum (driftRatio k) n := by
  have h := qpow_driftRatio_sub_one_eqv k n
  refine Q'.eqv_trans _
    ((qpow (driftRatio k) n + (-(1 : Q'))) + (1 : Q')) _ ?_ ?_
  · have hc : -(1 : Q') + (1 : Q') ≈ (0 : Q') := by
      exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
        (Q'.add_neg_self_eqv (1 : Q'))
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ hc) (q_add_zero_eqv _)
  · exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (1 : Q') h)
      (Q'.add_comm_eqv _ _)

private theorem qpow_pred_le_qpow_driftRatio (k n : Nat) :
    qpow (driftRatio k) (n - 1) ≤ qpow (driftRatio k) n := by
  cases n with
  | zero => exact Q'.le_refl' _
  | succ n =>
      have hp0 : (0 : Q') ≤ qpow (driftRatio k) n :=
        qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) n
      have hm := Q'.mul_le_mul_of_nonneg_left _ _
        (qpow (driftRatio k) n) (one_le_driftRatio k) hp0
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) hm

private theorem chord_endpoint_le_growth_geom (k n : Nat) :
    Q'.ofNat n *
        ((1 : Q') + qpow (driftRatio k) (n - 1)) ≤
      (Q'.ofNat 2 +
          Q'.ofNat n * unit (driftDen k) (driftDen_pos k)) *
        HeatKernelRGStep.geomSum (driftRatio k) n := by
  let N := Q'.ofNat n
  let u := unit (driftDen k) (driftDen_pos k)
  let S := HeatKernelRGStep.geomSum (driftRatio k) n
  let P := qpow (driftRatio k) (n - 1)
  have hNS : N ≤ S := ofNat_le_geomSum_of_one_le (one_le_driftRatio k) n
  have hPpow := qpow_pred_le_qpow_driftRatio k n
  have hpow : qpow (driftRatio k) n ≈ (1 : Q') + u * S := by
    unfold u S
    exact qpow_driftRatio_eqv_one_add_geom k n
  have hP : P ≤ (1 : Q') + u * S :=
    Q'.le_trans' _ _ _ hPpow (Q'.le_of_eqv hpow)
  have hN0 : (0 : Q') ≤ N := ExpNeg.ofNat_nonneg' n
  have hNP := Q'.mul_le_mul_of_nonneg_left _ _ N hP hN0
  have hadd := Q'.add_le_add hNS hNP
  have hleft : N * ((1 : Q') + P) ≈ N + N * P := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv N)
  have hSN : S + N ≤ S + S := Q'.add_le_add_left S _ _ hNS
  have hNS' := Q'.add_le_add_right _ _ (N * (u * S)) hSN
  have hexpand : S + N * ((1 : Q') + u * S) ≈
      (S + N) + N * (u * S) := by
    refine Q'.eqv_trans _
      (S + (N * (1 : Q') + N * (u * S))) _
      (Q'.add_eqv_congr_left S _ _ (Q'.mul_add_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ (S + (N + N * (u * S))) _
      (Q'.add_eqv_congr_left S _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv N))) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  have hmid : S + N * ((1 : Q') + u * S) ≤
      (S + S) + N * (u * S) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand) hNS'
  have hright : (S + S) + N * (u * S) ≈
      (Q'.ofNat 2 + N * u) * S := by
    have htwo : Q'.ofNat 2 ≈ (1 : Q') + (1 : Q') := by decide
    have htwoS : S + S ≈ Q'.ofNat 2 * S := by
      refine Q'.eqv_trans _ ((1 : Q') * S + (1 : Q') * S) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_symm (Q'.one_mul_eqv S))
          (Q'.eqv_symm (Q'.one_mul_eqv S))
      · refine Q'.eqv_trans _ (((1 : Q') + (1 : Q')) * S) _
          (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
        exact Q'.mul_eqv_congr_right _ _ S (Q'.eqv_symm htwo)
    have hNu : N * (u * S) ≈ (N * u) * S :=
      Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    refine Q'.eqv_trans _ (Q'.ofNat 2 * S + (N * u) * S) _
      (Q'.add_eqv_congr' htwoS hNu) ?_
    exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_trans' _ _ _ hmid (Q'.le_of_eqv hright)))

/-- The symmetric endpoint chord is at most a factor
`2+(4p+6)/((k+2)^2-1)` times the exact adjacent drift increment.  Unlike the
older next-cell bound, this factor tends to two in the active harmonic bulk. -/
theorem harmonicChordWeight_le_growthIncrement (k p : Nat) :
    harmonicChordWeight k p ≤
      harmonicChordGrowthFactor k p *
        (driftSqFactor k (p + 1) + -(driftSqFactor k p)) := by
  let G := driftSqFactor k p
  let u := unit (driftDen k) (driftDen_pos k)
  let n := 4 * p + 6
  let S := HeatKernelRGStep.geomSum (driftRatio k) n
  have hcore := chord_endpoint_le_growth_geom k n
  have hu0 : (0 : Q') ≤ u := unit_nonneg _ _
  have hG0 : (0 : Q') ≤ G := by
    unfold G driftSqFactor
    exact Q'.mul_nonneg _ _
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ u hcore hu0
  have hGu := Q'.mul_le_mul_of_nonneg_left _ _ G hu hG0
  have hleft : harmonicChordWeight k p ≈
      G * (u * (Q'.ofNat n *
        ((1 : Q') + qpow (driftRatio k) (n - 1)))) := by
    unfold harmonicChordWeight G u n
    rw [show 4 * p + 5 = 4 * p + 6 - 1 by omega]
    exact Q'.eqv_refl _
  have hright :
      G * (u * ((Q'.ofNat 2 + Q'.ofNat n * u) * S)) ≈
        harmonicChordGrowthFactor k p *
          (driftSqFactor k (p + 1) + -(driftSqFactor k p)) := by
    have hinc := driftSqFactor_increment_geom_eqv k p
    have hrearr :
        G * (u * ((Q'.ofNat 2 + Q'.ofNat n * u) * S)) ≈
          (Q'.ofNat 2 + Q'.ofNat n * u) * (G * (u * S)) := by
      ring_qeqv
    have hfac : harmonicChordGrowthFactor k p ≈
        Q'.ofNat 2 + Q'.ofNat n * u := by
      unfold harmonicChordGrowthFactor n u
      exact Q'.eqv_refl _
    refine Q'.eqv_trans _ _ _ hrearr ?_
    refine Q'.eqv_trans _
      (harmonicChordGrowthFactor k p * (G * (u * S))) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hfac)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hinc)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hGu (Q'.le_of_eqv hright))

private theorem harmonicChordGrowthFactor_mono {k a b : Nat} (hab : a ≤ b) :
    harmonicChordGrowthFactor k a ≤ harmonicChordGrowthFactor k b := by
  have hn : 4 * a + 6 ≤ 4 * b + 6 := by omega
  have hq : Q'.ofNat (4 * a + 6) ≤ Q'.ofNat (4 * b + 6) :=
    MovingCutoff.ofNat_le_ofNat' hn
  have hu0 : (0 : Q') ≤ unit (driftDen k) (driftDen_pos k) :=
    unit_nonneg _ _
  have hm := Q'.mul_le_mul_of_nonneg_right _ _
    (unit (driftDen k) (driftDen_pos k)) hq hu0
  exact Q'.add_le_add_left (Q'.ofNat 2) _ _ hm

private theorem sub_add_sub_cancel (a b c : Q') :
    (a + -b) + (c + -a) ≈ c + -b := by
  refine Q'.eqv_trans _ (a + (-b + (c + -a))) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (a + ((-b + c) + -a)) _
    (Q'.add_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))) ?_
  refine Q'.eqv_trans _ (a + ((c + -b) + -a)) _
    (Q'.add_eqv_congr_left a _ _
      (Q'.add_eqv_congr_right _ _ (-a) (Q'.add_comm_eqv _ _))) ?_
  refine Q'.eqv_trans _ ((a + (c + -b)) + -a) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ (((c + -b) + a) + -a) _
    (Q'.add_eqv_congr_right _ _ (-a) (Q'.add_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _ ((c + -b) + (a + -a)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ ((c + -b) + (0 : Q')) _
    (Q'.add_eqv_congr_left (c + -b) _ _ (Q'.add_neg_self_eqv a)) ?_
  exact q_add_zero_eqv _

private theorem interval_drift_increment_telescope (k s : Nat) : ∀ n,
    intervalSum
        (fun p => driftSqFactor k (p + 1) + -(driftSqFactor k p)) s n ≈
      driftSqFactor k (s + n) + -(driftSqFactor k s)
  | 0 => by
      unfold intervalSum
      simp only [fsum_zero, Nat.add_zero]
      exact Q'.eqv_symm (Q'.add_neg_self_eqv _)
  | n + 1 => by
      have ih := interval_drift_increment_telescope k s n
      have hidx : s + (n + 1) = (s + n) + 1 := by omega
      unfold intervalSum
      rw [fsum_succ]
      change
        intervalSum
            (fun p => driftSqFactor k (p + 1) + -(driftSqFactor k p)) s n +
            (driftSqFactor k (s + n + 1) + -(driftSqFactor k (s + n))) ≈
          driftSqFactor k (s + (n + 1)) + -(driftSqFactor k s)
      rw [hidx]
      refine Q'.eqv_trans _
        ((driftSqFactor k (s + n) + -(driftSqFactor k s)) +
          (driftSqFactor k (s + n + 1) +
            -(driftSqFactor k (s + n)))) _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      exact sub_add_sub_cancel
        (driftSqFactor k (s + n))
        (driftSqFactor k s)
        (driftSqFactor k (s + n + 1))

/-- The whole chord-weight prefix is controlled by one terminal growth
factor times the exact telescoped drift increment.  This retains the
bulk-asymptotic factor two and avoids the much coarser next-cell envelope. -/
theorem harmonicChordCumulative_le_majorant (k s n : Nat) :
    intervalSum (harmonicChordWeight k) s n ≤
      harmonicChordCumulativeMajorant k s n := by
  let M := harmonicChordGrowthFactor k (s + n)
  let d := fun p => driftSqFactor k (p + 1) + -(driftSqFactor k p)
  have hterm : ∀ j, j < n →
      harmonicChordWeight k (s + j) ≤ M * d (s + j) := by
    intro j hj
    have hw := harmonicChordWeight_le_growthIncrement k (s + j)
    have hfac : harmonicChordGrowthFactor k (s + j) ≤ M := by
      unfold M
      exact harmonicChordGrowthFactor_mono (by omega)
    have hd0 : (0 : Q') ≤ d (s + j) := by
      unfold d
      exact driftSqFactor_increment_nonneg k (s + j)
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ (d (s + j)) hfac hd0
    exact Q'.le_trans' _ _ _ hw hm
  have hsum := CubeRatioBounds.fsum_mono_lt n hterm
  have hpull :
      fsum (fun j => M * d (s + j)) n ≈ M * intervalSum d s n := by
    unfold intervalSum
    exact Q'.eqv_symm
      (CubeRatioBounds.fsum_const_mul M (fun j => d (s + j)) n)
  have htel := interval_drift_increment_telescope k s n
  have hM0 : (0 : Q') ≤ M := by
    unfold M harmonicChordGrowthFactor
    exact Q'.zero_le_add _ _ (ExpNeg.ofNat_nonneg' 2)
      (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _)
        (unit_nonneg _ _))
  have hscaled : M * intervalSum d s n ≤
      M * (driftSqFactor k (s + n) + -(driftSqFactor k s)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ M (Q'.le_of_eqv htel) hM0
  unfold intervalSum at hsum
  unfold harmonicChordCumulativeMajorant
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull) hscaled)

/-- The node moment obtained by replacing every cumulative chord prefix by
its single-endpoint majorant.  It is intentionally kept separate from the
sharper varying-factor growth moment below: the endpoint pull can spend too
much of the quantitative reserve. -/
def signedChordEndpointGrowthMoment (k s n : Nat) : Q' :=
  fsum (fun j =>
    trapezoidNodeCoeff k (s + j + 1) *
      harmonicChordCumulativeMajorant k s (j + 1)) n

/-- Exact fence: at the first requested uniform scale, the tempting
nodewise endpoint-majorant budget already exceeds the symbolic cap.  Thus
the varying growth factor must remain inside the cumulative sum; merely
combining `harmonicChordCumulative_le_majorant` termwise with node
coefficients cannot close the all-scale estimate. -/
theorem endpointGrowthMoment_cap_fails_k5 :
    ¬ (signedChordEndpointGrowthMoment 5 0 (Ncut 5 - 1) +
          (trapezoidTerminalCorrection 5 +
            trapezoidTerminalCorrection 5) ≤
        signedChordMomentCap 5) := by
  unfold signedChordEndpointGrowthMoment harmonicChordCumulativeMajorant
    harmonicChordGrowthFactor signedChordMomentCap signedChordMomentCore
    trapezoidTerminalCorrection trapezoidNodeCoeff harmonicD harmonicA
    twoInvSq oldAdj oldDiag coordNormSq adjCorr driftSqFactor driftRatio
    driftDen harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

def harmonicChordGrowthWeight (k p : Nat) : Q' :=
  harmonicChordGrowthFactor k p *
    (driftSqFactor k (p + 1) + -(driftSqFactor k p))

def harmonicChordGrowthCumulative (k s n : Nat) : Q' :=
  intervalSum (harmonicChordGrowthWeight k) s n

def harmonicChordRamp (k s n : Nat) : Q' :=
  intervalSum
    (fun p => driftSqFactor k (p + 1) + -(driftSqFactor k s)) s n

def signedChordGrowthNodeMoment (k s n : Nat) : Q' :=
  fsum (fun j =>
    trapezoidNodeCoeff k (s + j + 1) *
      harmonicChordGrowthCumulative k s (j + 1)) n

def signedChordRampNodeMoment (k s n : Nat) : Q' :=
  fsum (fun j =>
    trapezoidNodeCoeff k (s + j + 1) * harmonicChordRamp k s (j + 1)) n

def signedChordRampCarrier (k L s : Nat) : Q' :=
  intervalSum (fun p =>
    (trapezoidNodeCumulative k L + -(trapezoidNodeCumulative k p)) *
      (driftSqFactor k (p + 1) + -(driftSqFactor k s))) s (L - s)

/-- Endpoint growth moment with the exact Abel ramp payment restored. -/
def signedChordCorrectedEndpointMoment (k L s : Nat) : Q' :=
  signedChordEndpointGrowthMoment k s (L - s) +
    -((Q'.ofNat 4 * unit (driftDen k) (driftDen_pos k)) *
      signedChordRampCarrier k L s)

private theorem harmonicChordGrowthFactor_succ (k p : Nat) :
    harmonicChordGrowthFactor k (p + 1) ≈
      harmonicChordGrowthFactor k p +
        Q'.ofNat 4 * unit (driftDen k) (driftDen_pos k) := by
  have hn : 4 * (p + 1) + 6 = (4 * p + 6) + 4 := by omega
  unfold harmonicChordGrowthFactor
  rw [hn]
  refine Q'.eqv_trans _
    (Q'.ofNat 2 +
      (Q'.ofNat (4 * p + 6) + Q'.ofNat 4) *
        unit (driftDen k) (driftDen_pos k)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv _ _))
  · refine Q'.eqv_trans _
      (Q'.ofNat 2 +
        (Q'.ofNat (4 * p + 6) * unit (driftDen k) (driftDen_pos k) +
          Q'.ofNat 4 * unit (driftDen k) (driftDen_pos k))) _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_mul_eqv _ _ _)) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem weighted_ramp_step
    (H R a b X Y Z : Q')
    (h : H + b * R ≈ a * (X + -Y)) :
    (H + a * (Z + -X)) + b * (R + (Z + -Y)) ≈
      (a + b) * (Z + -Y) := by
  have hb : b * (R + (Z + -Y)) ≈ b * R + b * (Z + -Y) :=
    Q'.mul_add_eqv _ _ _
  refine Q'.eqv_trans _
    ((H + b * R) + (a * (Z + -X) + b * (Z + -Y))) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((H + a * (Z + -X)) + (b * R + b * (Z + -Y))) _
      (Q'.add_eqv_congr_left _ _ _ hb) ?_
    ring_qeqv
  · refine Q'.eqv_trans _
      (a * (X + -Y) + (a * (Z + -X) + b * (Z + -Y))) _
      (Q'.add_eqv_congr_right _ _ _ h) ?_
    refine Q'.eqv_trans _
      ((a * (X + -Y) + a * (Z + -X)) + b * (Z + -Y)) _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    have hcollapse :
        a * (X + -Y) + a * (Z + -X) ≈ a * (Z + -Y) := by
      refine Q'.eqv_trans _ (a * ((X + -Y) + (Z + -X))) _
        (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) ?_
      exact Q'.mul_eqv_congr_left a _ _ (sub_add_sub_cancel X Y Z)
    refine Q'.eqv_trans _
      (a * (Z + -Y) + b * (Z + -Y)) _
      (Q'.add_eqv_congr_right _ _ _ hcollapse) ?_
    exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)

/-- Exact summation-by-parts identity for the varying growth factor.  The
single-endpoint majorant equals the sharp varying-factor cumulative weight
plus the positive ramp generated by the constant factor increment `4u`.
The k=5 fence above shows that this ramp cannot be discarded. -/
theorem harmonicChordGrowthCumulative_add_ramp (k s : Nat) : ∀ n,
    harmonicChordGrowthCumulative k s n +
        (Q'.ofNat 4 * unit (driftDen k) (driftDen_pos k)) *
          harmonicChordRamp k s n ≈
      harmonicChordCumulativeMajorant k s n
  | 0 => by
      unfold harmonicChordGrowthCumulative harmonicChordRamp
        harmonicChordCumulativeMajorant intervalSum
      simp only [fsum_zero, Nat.add_zero]
      have hz : driftSqFactor k s + -(driftSqFactor k s) ≈ (0 : Q') :=
        Q'.add_neg_self_eqv _
      refine Q'.eqv_trans _ ((0 : Q') + (0 : Q')) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv _)
            (Q'.eqv_refl _))
      · refine Q'.eqv_trans _ (0 : Q') _ (by decide) ?_
        exact Q'.eqv_symm
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _))
  | n + 1 => by
      let p := s + n
      let a := harmonicChordGrowthFactor k p
      let b := Q'.ofNat 4 * unit (driftDen k) (driftDen_pos k)
      let X := driftSqFactor k p
      let Y := driftSqFactor k s
      let Z := driftSqFactor k (p + 1)
      have ih := harmonicChordGrowthCumulative_add_ramp k s n
      change
        (harmonicChordGrowthCumulative k s n +
            harmonicChordGrowthWeight k p) +
          b * (harmonicChordRamp k s n + (Z + -Y)) ≈
        harmonicChordGrowthFactor k (p + 1) * (Z + -Y)
      have hi : harmonicChordGrowthCumulative k s n +
          b * harmonicChordRamp k s n ≈ a * (X + -Y) := by
        unfold a X Y b p
        exact ih
      have hs := weighted_ramp_step
        (harmonicChordGrowthCumulative k s n)
        (harmonicChordRamp k s n) a b X Y Z hi
      have hw : harmonicChordGrowthWeight k p ≈ a * (Z + -X) := by
        unfold harmonicChordGrowthWeight a X Z
        exact Q'.eqv_refl _
      refine Q'.eqv_trans _
        ((harmonicChordGrowthCumulative k s n + a * (Z + -X)) +
          b * (harmonicChordRamp k s n + (Z + -Y))) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_left _ _ _ hw)) ?_
      refine Q'.eqv_trans _ ((a + b) * (Z + -Y)) _ hs ?_
      exact Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm (by
          unfold a b p
          exact harmonicChordGrowthFactor_succ k (s + n)))

def signedChordNodeMoment (k s n : Nat) : Q' :=
  fsum (fun j =>
    trapezoidNodeCoeff k (s + j + 1) *
      intervalSum (harmonicChordWeight k) s (j + 1)) n

private theorem fsum_mask_ge_eq_interval (f : Nat → Q') (s : Nat) : ∀ L,
    fsum (fun p => if s ≤ p then f p else (0 : Q')) L =
      intervalSum f s (L - s)
  | 0 => by
      simp [intervalSum, fsum]
  | L + 1 => by
      rw [fsum_succ, fsum_mask_ge_eq_interval f s L]
      by_cases hsL : s ≤ L
      · rw [if_pos hsL]
        have hsub : L + 1 - s = (L - s) + 1 := by omega
        rw [hsub]
        simp only [intervalSum, fsum_succ]
        have hi : s + (L - s) = L := by omega
        rw [hi]
      · rw [if_neg hsL]
        have hz : L - s = 0 := by omega
        have hz' : L + 1 - s = 0 := by omega
        simp only [hz, hz', intervalSum, fsum_zero, Q'.zero_add']

private theorem terminal_gap_weight_fubini
    (T q W : Nat → Q')
    (hstep : ∀ i, T (i + 1) ≈ T i + q (i + 1))
    (s : Nat) : ∀ n,
    intervalSum (fun p => (T (s + n) + -(T p)) * W p) s n ≈
      fsum (fun j => q (s + j + 1) * intervalSum W s (j + 1)) n
  | 0 => by
      exact Q'.eqv_refl _
  | n + 1 => by
      let L := s + n
      let qn := q (L + 1)
      let old := fun p => (T L + -(T p)) * W p
      let add := fun p => qn * W p
      have hterm : ∀ j,
          (T (s + (n + 1)) + -(T (s + j))) * W (s + j) ≈
            old (s + j) + add (s + j) := by
        intro j
        have hsuc : s + (n + 1) = L + 1 := by
          unfold L
          omega
        rw [hsuc]
        have hg : T (L + 1) + -(T (s + j)) ≈
            (T L + -(T (s + j))) + qn := by
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _ (hstep L)) ?_
          unfold qn
          ring_qeqv
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hg) ?_
        unfold old add
        exact Q'.add_mul_eqv _ _ _
      have hfirst :
          intervalSum
              (fun p => (T (s + (n + 1)) + -(T p)) * W p) s n ≈
            intervalSum (fun p => old p + add p) s n := by
        unfold intervalSum
        exact CubeRatioBounds.fsum_eqv_congr _ _ hterm n
      have hsplit : intervalSum (fun p => old p + add p) s n ≈
          intervalSum old s n + intervalSum add s n := by
        unfold intervalSum
        exact CubeRatioBounds.fsum_add
          (fun j => old (s + j)) (fun j => add (s + j)) n
      have haddsum : intervalSum add s n ≈
          qn * intervalSum W s n := by
        unfold intervalSum add
        exact Q'.eqv_symm
          (CubeRatioBounds.fsum_const_mul qn (fun j => W (s + j)) n)
      have hlastgap : T (s + (n + 1)) + -(T (s + n)) ≈ qn := by
        have hsuc : s + (n + 1) = L + 1 := by
          unfold L
          omega
        have hbase : s + n = L := rfl
        rw [hsuc, hbase]
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _ (hstep L)) ?_
        unfold qn
        have hc : T L + -(T L) ≈ (0 : Q') := Q'.add_neg_self_eqv _
        refine Q'.eqv_trans _ ((T L + -(T L)) + q (L + 1)) _
          (by ring_qeqv) ?_
        refine Q'.eqv_trans _ ((0 : Q') + q (L + 1)) _
          (Q'.add_eqv_congr_right _ _ _ hc) ?_
        exact q_zero_add_eqv _
      have hlast :
          (T (s + (n + 1)) + -(T (s + n))) * W (s + n) ≈
            qn * W (s + n) :=
        Q'.mul_eqv_congr_right _ _ _ hlastgap
      have ih := terminal_gap_weight_fubini T q W hstep s n
      have hprefixSucc : intervalSum W s (n + 1) =
          intervalSum W s n + W (s + n) := by
        rfl
      rw [show
        intervalSum
            (fun p => (T (s + (n + 1)) + -(T p)) * W p) s (n + 1) =
          intervalSum
              (fun p => (T (s + (n + 1)) + -(T p)) * W p) s n +
            (T (s + (n + 1)) + -(T (s + n))) * W (s + n) by rfl]
      rw [fsum_succ]
      refine Q'.eqv_trans _
        (intervalSum (fun p => old p + add p) s n +
          qn * W (s + n)) _
        (Q'.add_eqv_congr' hfirst hlast) ?_
      refine Q'.eqv_trans _
        ((intervalSum old s n + intervalSum add s n) +
          qn * W (s + n)) _
        (Q'.add_eqv_congr_right _ _ _ hsplit) ?_
      refine Q'.eqv_trans _
        ((intervalSum old s n + qn * intervalSum W s n) +
          qn * W (s + n)) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_left _ _ _ haddsum)) ?_
      refine Q'.eqv_trans _
        (intervalSum old s n +
          qn * intervalSum W s (n + 1)) _ (by
            rw [hprefixSucc]
            exact Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
              (Q'.add_eqv_congr_left _ _ _
                (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)))) ?_
      refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
      unfold old
      simpa using ih

/-- Exact triangular Fubini form of the signed chord.  It retains the global
normalization cancellation: node increments are paired with cumulative chord
weights, with no pointwise carrier or reserve hypothesis. -/
theorem signedChordSum_eq_nodeMoment (k L s : Nat) (hsL : s ≤ L) :
    signedChordSum k L s ≈ signedChordNodeMoment k s (L - s) := by
  let T := trapezoidNodeCumulative k
  let q := trapezoidNodeCoeff k
  let W := harmonicChordWeight k
  have hmask : signedChordSum k L s =
      intervalSum (fun p => (T L + -(T p)) * W p) s (L - s) := by
    unfold signedChordSum signedChordCell compensatedChordCell
    unfold T W harmonicChordWeight
    exact fsum_mask_ge_eq_interval _ s L
  have hSL : s + (L - s) = L := by omega
  have hf := terminal_gap_weight_fubini T q W
    (fun i => trapezoidNodeCumulative_succ_eq k i) s (L - s)
  rw [hSL] at hf
  rw [hmask]
  exact hf

/-- At an admissible terminal crossing, the sharp pointwise chord estimate
may be summed without pulling the varying growth factor to the endpoint.
The right side is still the exact triangular node moment of that varying
factor, so no further loss is introduced by the Fubini swap. -/
theorem signedChordNodeMoment_le_growthNodeMoment
    (k L s : Nat) (hsL : s ≤ L)
    (hboundary : (0 : Q') ≤ trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k s)) :
    signedChordNodeMoment k s (L - s) ≤
      signedChordGrowthNodeMoment k s (L - s) := by
  let T := trapezoidNodeCumulative k
  let q := trapezoidNodeCoeff k
  let W := harmonicChordWeight k
  let V := harmonicChordGrowthWeight k
  have hterm : ∀ j, j < L - s →
      (T L + -(T (s + j))) * W (s + j) ≤
        (T L + -(T (s + j))) * V (s + j) := by
    intro j hj
    have hgap : (0 : Q') ≤ T L + -(T (s + j)) := by
      unfold T
      exact terminal_carrier_gap_nonneg_from_split
        k L s hsL hboundary (by omega) (by omega)
    have hw : W (s + j) ≤ V (s + j) := by
      unfold W V harmonicChordGrowthWeight
      exact harmonicChordWeight_le_growthIncrement k (s + j)
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hw hgap
  have hsum :
      intervalSum (fun p => (T L + -(T p)) * W p) s (L - s) ≤
        intervalSum (fun p => (T L + -(T p)) * V p) s (L - s) := by
    unfold intervalSum
    exact CubeRatioBounds.fsum_mono_lt (L - s) hterm
  have hSL : s + (L - s) = L := by omega
  have hW := terminal_gap_weight_fubini T q W
    (fun i => trapezoidNodeCumulative_succ_eq k i) s (L - s)
  have hV := terminal_gap_weight_fubini T q V
    (fun i => trapezoidNodeCumulative_succ_eq k i) s (L - s)
  rw [hSL] at hW hV
  unfold signedChordNodeMoment signedChordGrowthNodeMoment
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hW)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hV))

/-- Lossless Fubini lift of the second-order chord carrier.  The factor
stays at its own cell throughout the double sum. -/
theorem signedChordNodeMoment_le_quadraticNodeMoment
    (k L s : Nat) (hsL : s ≤ L)
    (hboundary : (0 : Q') ≤ trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k s)) :
    signedChordNodeMoment k s (L - s) ≤
      signedChordQuadraticNodeMoment k s (L - s) := by
  let T := trapezoidNodeCumulative k
  let q := trapezoidNodeCoeff k
  let W := harmonicChordWeight k
  let V := harmonicChordQuadraticWeight k
  have hterm : ∀ j, j < L - s →
      (T L + -(T (s + j))) * W (s + j) ≤
        (T L + -(T (s + j))) * V (s + j) := by
    intro j hj
    have hgap : (0 : Q') ≤ T L + -(T (s + j)) := by
      unfold T
      exact terminal_carrier_gap_nonneg_from_split
        k L s hsL hboundary (by omega) (by omega)
    have hw : W (s + j) ≤ V (s + j) := by
      unfold W V
      exact harmonicChordWeight_le_quadraticIncrement k (s + j)
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hw hgap
  have hsum :
      intervalSum (fun p => (T L + -(T p)) * W p) s (L - s) ≤
        intervalSum (fun p => (T L + -(T p)) * V p) s (L - s) := by
    unfold intervalSum
    exact CubeRatioBounds.fsum_mono_lt (L - s) hterm
  have hSL : s + (L - s) = L := by omega
  have hW := terminal_gap_weight_fubini T q W
    (fun i => trapezoidNodeCumulative_succ_eq k i) s (L - s)
  have hV := terminal_gap_weight_fubini T q V
    (fun i => trapezoidNodeCumulative_succ_eq k i) s (L - s)
  rw [hSL] at hW hV
  unfold signedChordNodeMoment signedChordQuadraticNodeMoment
    harmonicChordQuadraticCumulative
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hW)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hV))

/-- Nodewise form of the exact weighted Abel identity.  The excess paid by
the endpoint pull is exactly `4/((k+2)^2-1)` times the ramp node moment; it
is not an artefact of either summation order. -/
theorem signedChordGrowthNodeMoment_add_ramp (k s n : Nat) :
    signedChordGrowthNodeMoment k s n +
        (Q'.ofNat 4 * unit (driftDen k) (driftDen_pos k)) *
          signedChordRampNodeMoment k s n ≈
      signedChordEndpointGrowthMoment k s n := by
  let b := Q'.ofNat 4 * unit (driftDen k) (driftDen_pos k)
  let q := fun j => trapezoidNodeCoeff k (s + j + 1)
  let G := fun j => harmonicChordGrowthCumulative k s (j + 1)
  let R := fun j => harmonicChordRamp k s (j + 1)
  let E := fun j => harmonicChordCumulativeMajorant k s (j + 1)
  have hterm : ∀ j, q j * G j + b * (q j * R j) ≈ q j * E j := by
    intro j
    have hc := harmonicChordGrowthCumulative_add_ramp k s (j + 1)
    have hrearr : q j * G j + b * (q j * R j) ≈
        q j * (G j + b * R j) := by
      ring_qeqv
    exact Q'.eqv_trans _ _ _ hrearr
      (Q'.mul_eqv_congr_left (q j) _ _ (by
        unfold G R E b
        exact hc))
  have hcongr := CubeRatioBounds.fsum_eqv_congr
    (fun j => q j * G j + b * (q j * R j))
    (fun j => q j * E j) hterm n
  have hsplit := CubeRatioBounds.fsum_add
    (fun j => q j * G j) (fun j => b * (q j * R j)) n
  have hpull := CubeRatioBounds.fsum_const_mul b (fun j => q j * R j) n
  unfold signedChordGrowthNodeMoment signedChordRampNodeMoment
    signedChordEndpointGrowthMoment
  change fsum (fun j => q j * G j) n +
      b * fsum (fun j => q j * R j) n ≈ fsum (fun j => q j * E j) n
  refine Q'.eqv_trans _
    (fsum (fun j => q j * G j) n +
      fsum (fun j => b * (q j * R j)) n) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ hpull
  · exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsplit) hcongr

private theorem driftSqFactor_mono {k a b : Nat} (hab : a ≤ b) :
    driftSqFactor k a ≤ driftSqFactor k b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      have hs : driftSqFactor k (a + d) ≤
          driftSqFactor k (a + d + 1) :=
        Q'.le_of_sub_nonneg (driftSqFactor_increment_nonneg k (a + d))
      exact Q'.le_trans' _ _ _ (ih (by omega)) hs

private theorem fsum_nonneg_here (f : Nat → Q') : ∀ n,
    (∀ j, j < n → (0 : Q') ≤ f j) → (0 : Q') ≤ fsum f n
  | 0, _ => Q'.le_refl' 0
  | n + 1, h => by
      rw [fsum_succ]
      exact Q'.zero_le_add _ _
        (fsum_nonneg_here f n (fun j hj => h j (by omega)))
        (h n (by omega))

/-- The ramp correction itself has a second lossless carrier form: it is
the positive-tail terminal gap paired with the drift distance from the
crossing.  This is the quantity that a sharp cap proof must retain from
the endpoint majorant instead of discarding merely by sign. -/
theorem signedChordRampCarrier_eq_nodeMoment
    (k L s : Nat) (hsL : s ≤ L) :
    signedChordRampCarrier k L s ≈
      signedChordRampNodeMoment k s (L - s) := by
  let T := trapezoidNodeCumulative k
  let q := trapezoidNodeCoeff k
  let W := fun p => driftSqFactor k (p + 1) + -(driftSqFactor k s)
  have hSL : s + (L - s) = L := by omega
  have hf := terminal_gap_weight_fubini T q W
    (fun i => trapezoidNodeCumulative_succ_eq k i) s (L - s)
  rw [hSL] at hf
  unfold signedChordRampCarrier signedChordRampNodeMoment harmonicChordRamp
  exact hf

/-- At an admissible crossing, the ramp payment is nonnegative term by
term in its carrier form.  Together with
`signedChordGrowthNodeMoment_add_ramp`, this locates the exact positive
correction that separates the viable varying-factor carrier from the
refuted endpoint pull. -/
theorem signedChordRampNodeMoment_nonneg
    (k L s : Nat) (hsL : s ≤ L)
    (hboundary : (0 : Q') ≤ trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k s)) :
    (0 : Q') ≤ signedChordRampNodeMoment k s (L - s) := by
  let f := fun j =>
    (trapezoidNodeCumulative k L +
        -(trapezoidNodeCumulative k (s + j))) *
      (driftSqFactor k (s + j + 1) + -(driftSqFactor k s))
  have hterm : ∀ j, j < L - s → (0 : Q') ≤ f j := by
    intro j hj
    have hgap := terminal_carrier_gap_nonneg_from_split
      k L s hsL hboundary (show s ≤ s + j by omega)
        (show s + j ≤ L by omega)
    have hdist : (0 : Q') ≤
        driftSqFactor k (s + j + 1) + -(driftSqFactor k s) :=
      Q'.sub_nonneg_of_le (driftSqFactor_mono (show s ≤ s + j + 1 by omega))
    exact Q'.mul_nonneg _ _ hgap hdist
  have hsum : (0 : Q') ≤ fsum f (L - s) :=
    fsum_nonneg_here f (L - s) hterm
  have he := signedChordRampCarrier_eq_nodeMoment k L s hsL
  unfold signedChordRampCarrier intervalSum at he
  change (0 : Q') ≤ fsum f (L - s) at hsum
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv he)

/-- Exact corrected endpoint carrier.  The varying-factor node moment is
not merely bounded by an endpoint expression: it equals the refuted
endpoint pull after subtracting the explicit positive-tail ramp carrier. -/
theorem signedChordGrowthNodeMoment_eq_correctedEndpoint
    (k L s : Nat) (hsL : s ≤ L) :
    signedChordGrowthNodeMoment k s (L - s) ≈
      signedChordCorrectedEndpointMoment k L s := by
  let b := Q'.ofNat 4 * unit (driftDen k) (driftDen_pos k)
  let G := signedChordGrowthNodeMoment k s (L - s)
  let R := signedChordRampNodeMoment k s (L - s)
  let C := signedChordRampCarrier k L s
  let E := signedChordEndpointGrowthMoment k s (L - s)
  have hnode : G + b * R ≈ E := by
    unfold G R E b
    exact signedChordGrowthNodeMoment_add_ramp k s (L - s)
  have hcarrier : C ≈ R := by
    unfold C R
    exact signedChordRampCarrier_eq_nodeMoment k L s hsL
  have hscale : b * C ≈ b * R :=
    Q'.mul_eqv_congr_left b _ _ hcarrier
  have hcancel : (G + b * R) + -(b * R) ≈ G := by
    refine Q'.eqv_trans _ (G + (b * R + -(b * R))) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ (G + (0 : Q')) _
      (Q'.add_eqv_congr_left G _ _ (Q'.add_neg_self_eqv (b * R))) ?_
    exact q_add_zero_eqv G
  unfold signedChordCorrectedEndpointMoment
  change G ≈ E + -(b * C)
  refine Q'.eqv_trans _ ((G + b * R) + -(b * R)) _
    (Q'.eqv_symm hcancel) ?_
  refine Q'.eqv_trans _ (E + -(b * R)) _
    (Q'.add_eqv_congr_right _ _ _ hnode) ?_
  exact Q'.add_eqv_congr_left E _ _
    (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hscale))

/-- The original positive-tail node moment is controlled by the corrected
endpoint carrier.  Unlike the uncorrected endpoint majorant, this theorem
retains exactly the ramp that the k=5 fence proves quantitatively necessary. -/
theorem signedChordNodeMoment_le_correctedEndpoint
    (k L s : Nat) (hsL : s ≤ L)
    (hboundary : (0 : Q') ≤ trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k s)) :
    signedChordNodeMoment k s (L - s) ≤
      signedChordCorrectedEndpointMoment k L s := by
  have hg := signedChordNodeMoment_le_growthNodeMoment
    k L s hsL hboundary
  have he := signedChordGrowthNodeMoment_eq_correctedEndpoint k L s hsL
  exact Q'.le_trans' _ _ _ hg (Q'.le_of_eqv he)

/-- The all-scale symmetric signed-chord budget is genuinely false at the
base scale.  This is why the exact theorem `compensated_reserve_k0`, rather
than the chord envelope, must start the induction. -/
theorem signedChord_twentyFourTwentyFive_fails_k0 :
    ¬ (
      signedChordSum 0 (Ncut 0 - 1) 0 +
          (trapezoidTerminalCorrection 0 + trapezoidTerminalCorrection 0) ≤
        (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative 0 (Ncut 0 - 1) *
              driftSqFactor 0 0))) +
          (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative 0 (Ncut 0 - 1) *
              driftSqFactor 0 0)))) := by
  unfold signedChordSum signedChordCell compensatedChordCell
    trapezoidTerminalCorrection trapezoidNodeCumulative harmonicD harmonicA
    twoInvSq oldAdj coordNormSq adjCorr driftSqFactor driftRatio driftDen
    harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

/-- At the first nontrivial scale the initial terminal gap is strictly
positive, so any admissible first-crossing index is definitionally zero. -/
theorem terminal_gap_k1_p0_not_nonpos :
    ¬ (
      trapezoidNodeCumulative 1 (Ncut 1 - 1) +
        -(trapezoidNodeCumulative 1 0) ≤ (0 : Q')) := by
  unfold trapezoidNodeCumulative harmonicD harmonicA twoInvSq oldAdj
    coordNormSq adjCorr harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    qpow Ncut fsum
  decide

/-- Exact `k=1` quantitative budget in the downstream signed-crossing
signature.  No measured constant enters: after the crossing is forced to
`s=0`, the claim is a closed rational computation. -/
theorem signedChord_twentyFourTwentyFive_k1
    (s : Nat) (hsL : s ≤ Ncut 1 - 1)
    (hfirst : ∀ p, p < s →
      trapezoidNodeCumulative 1 (Ncut 1 - 1) +
        -(trapezoidNodeCumulative 1 p) ≤ (0 : Q'))
    (_hboundary : (0 : Q') ≤
      trapezoidNodeCumulative 1 (Ncut 1 - 1) +
        -(trapezoidNodeCumulative 1 s)) :
    signedChordSum 1 (Ncut 1 - 1) s +
          (trapezoidTerminalCorrection 1 + trapezoidTerminalCorrection 1) ≤
        (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative 1 (Ncut 1 - 1) *
              driftSqFactor 1 0))) +
          (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative 1 (Ncut 1 - 1) *
              driftSqFactor 1 0))) := by
  have hs0 : s = 0 := by
    by_cases hzero : s = 0
    · exact hzero
    · have hpos : 0 < s := Nat.pos_of_ne_zero hzero
      have hf : False := terminal_gap_k1_p0_not_nonpos (hfirst 0 hpos)
      exact False.elim hf
  subst s
  unfold signedChordSum signedChordCell compensatedChordCell
    trapezoidTerminalCorrection trapezoidNodeCumulative harmonicD harmonicA
    twoInvSq oldAdj coordNormSq adjCorr driftSqFactor driftRatio driftDen
    harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

theorem terminal_gap_k2_p0_not_nonpos :
    ¬ (
      trapezoidNodeCumulative 2 (Ncut 2 - 1) +
        -(trapezoidNodeCumulative 2 0) ≤ (0 : Q')) := by
  unfold trapezoidNodeCumulative harmonicD harmonicA twoInvSq oldAdj
    coordNormSq adjCorr harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    qpow Ncut fsum
  decide

theorem signedChord_twentyFourTwentyFive_k2
    (s : Nat) (hsL : s ≤ Ncut 2 - 1)
    (hfirst : ∀ p, p < s →
      trapezoidNodeCumulative 2 (Ncut 2 - 1) +
        -(trapezoidNodeCumulative 2 p) ≤ (0 : Q'))
    (_hboundary : (0 : Q') ≤
      trapezoidNodeCumulative 2 (Ncut 2 - 1) +
        -(trapezoidNodeCumulative 2 s)) :
    signedChordSum 2 (Ncut 2 - 1) s +
          (trapezoidTerminalCorrection 2 + trapezoidTerminalCorrection 2) ≤
        (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative 2 (Ncut 2 - 1) *
              driftSqFactor 2 0))) +
          (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative 2 (Ncut 2 - 1) *
              driftSqFactor 2 0))) := by
  have hs0 : s = 0 := by
    by_cases hzero : s = 0
    · exact hzero
    · have hpos : 0 < s := Nat.pos_of_ne_zero hzero
      have hf : False := terminal_gap_k2_p0_not_nonpos (hfirst 0 hpos)
      exact False.elim hf
  subst s
  unfold signedChordSum signedChordCell compensatedChordCell
    trapezoidTerminalCorrection trapezoidNodeCumulative harmonicD harmonicA
    twoInvSq oldAdj coordNormSq adjCorr driftSqFactor driftRatio driftDen
    harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

theorem weightedTrapezoidResidual_nonpos_k1 :
    weightedTrapezoidResidual 1 ≤ (0 : Q') :=
  weightedTrapezoidResidual_nonpos_of_signed_crossing_budget 1
    signedChord_twentyFourTwentyFive_k1

theorem weightedTrapezoidResidual_nonpos_k2 :
    weightedTrapezoidResidual 2 ≤ (0 : Q') :=
  weightedTrapezoidResidual_nonpos_of_signed_crossing_budget 2
    signedChord_twentyFourTwentyFive_k2

theorem terminal_gap_k3_p0_not_nonpos :
    ¬ (
      trapezoidNodeCumulative 3 (Ncut 3 - 1) +
        -(trapezoidNodeCumulative 3 0) ≤ (0 : Q')) := by
  unfold trapezoidNodeCumulative harmonicD harmonicA twoInvSq oldAdj
    coordNormSq adjCorr harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    qpow Ncut fsum
  decide

theorem signedChord_twentyFourTwentyFive_k3
    (s : Nat) (hsL : s ≤ Ncut 3 - 1)
    (hfirst : ∀ p, p < s →
      trapezoidNodeCumulative 3 (Ncut 3 - 1) +
        -(trapezoidNodeCumulative 3 p) ≤ (0 : Q'))
    (_hboundary : (0 : Q') ≤
      trapezoidNodeCumulative 3 (Ncut 3 - 1) +
        -(trapezoidNodeCumulative 3 s)) :
    signedChordSum 3 (Ncut 3 - 1) s +
          (trapezoidTerminalCorrection 3 + trapezoidTerminalCorrection 3) ≤
        (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative 3 (Ncut 3 - 1) *
              driftSqFactor 3 0))) +
          (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative 3 (Ncut 3 - 1) *
              driftSqFactor 3 0))) := by
  have hs0 : s = 0 := by
    by_cases hzero : s = 0
    · exact hzero
    · have hpos : 0 < s := Nat.pos_of_ne_zero hzero
      have hf : False := terminal_gap_k3_p0_not_nonpos (hfirst 0 hpos)
      exact False.elim hf
  subst s
  unfold signedChordSum signedChordCell compensatedChordCell
    trapezoidTerminalCorrection trapezoidNodeCumulative harmonicD harmonicA
    twoInvSq oldAdj coordNormSq adjCorr driftSqFactor driftRatio driftDen
    harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

theorem weightedTrapezoidResidual_nonpos_k3 :
    weightedTrapezoidResidual 3 ≤ (0 : Q') :=
  weightedTrapezoidResidual_nonpos_of_signed_crossing_budget 3
    signedChord_twentyFourTwentyFive_k3

/-! ## First direct positive-tail moment checkpoint -/

theorem terminal_gap_k4_p0_not_nonpos :
    ¬ (
      trapezoidNodeCumulative 4 (Ncut 4 - 1) +
        -(trapezoidNodeCumulative 4 0) ≤ (0 : Q')) := by
  unfold trapezoidNodeCumulative harmonicD harmonicA twoInvSq oldAdj
    coordNormSq adjCorr harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    qpow Ncut fsum
  decide

/-- At the first scale beyond the earlier closed prefix, the lossless
Fubini node moment, including both terminal half-edge corrections, fits
directly inside the symbolic all-scale moment cap. -/
theorem signedChordNodeMoment_le_cap_k4
    (s : Nat) (hsL : s ≤ Ncut 4 - 1)
    (hfirst : ∀ p, p < s →
      trapezoidNodeCumulative 4 (Ncut 4 - 1) +
        -(trapezoidNodeCumulative 4 p) ≤ (0 : Q'))
    (_hboundary : (0 : Q') ≤
      trapezoidNodeCumulative 4 (Ncut 4 - 1) +
        -(trapezoidNodeCumulative 4 s)) :
    signedChordNodeMoment 4 s (Ncut 4 - 1 - s) +
        (trapezoidTerminalCorrection 4 +
          trapezoidTerminalCorrection 4) ≤
      signedChordMomentCap 4 := by
  have hs0 : s = 0 := by
    by_cases hzero : s = 0
    · exact hzero
    · have hpos : 0 < s := Nat.pos_of_ne_zero hzero
      have hf : False := terminal_gap_k4_p0_not_nonpos (hfirst 0 hpos)
      exact False.elim hf
  subst s
  unfold signedChordNodeMoment intervalSum harmonicChordWeight
    signedChordMomentCap signedChordMomentCore trapezoidTerminalCorrection
    trapezoidNodeCoeff harmonicD harmonicA twoInvSq oldAdj oldDiag
    coordNormSq adjCorr driftSqFactor driftRatio driftDen
    harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

/-- The exact `k=4` node-moment checkpoint feeds the signed crossing bridge
without re-expanding the original chord sum. -/
theorem signedChord_twentyFourTwentyFive_k4
    (s : Nat) (hsL : s ≤ Ncut 4 - 1)
    (hfirst : ∀ p, p < s →
      trapezoidNodeCumulative 4 (Ncut 4 - 1) +
        -(trapezoidNodeCumulative 4 p) ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤
      trapezoidNodeCumulative 4 (Ncut 4 - 1) +
        -(trapezoidNodeCumulative 4 s)) :
    signedChordSum 4 (Ncut 4 - 1) s +
          (trapezoidTerminalCorrection 4 + trapezoidTerminalCorrection 4) ≤
        (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative 4 (Ncut 4 - 1) *
              driftSqFactor 4 0))) +
          (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative 4 (Ncut 4 - 1) *
              driftSqFactor 4 0))) := by
  have hm := signedChordNodeMoment_le_cap_k4 s hsL hfirst hboundary
  have he := signedChordSum_eq_nodeMoment 4 (Ncut 4 - 1) s hsL
  have headd :
      signedChordSum 4 (Ncut 4 - 1) s +
          (trapezoidTerminalCorrection 4 + trapezoidTerminalCorrection 4) ≈
        signedChordNodeMoment 4 s (Ncut 4 - 1 - s) +
          (trapezoidTerminalCorrection 4 + trapezoidTerminalCorrection 4) :=
    Q'.add_eqv_congr_right _ _ _ he
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv headd)
    (Q'.le_trans' _ _ _ hm
      (signedChordMomentCap_le_target 4 (by decide)))

theorem weightedTrapezoidResidual_nonpos_k4 :
    weightedTrapezoidResidual 4 ≤ (0 : Q') :=
  weightedTrapezoidResidual_nonpos_of_signed_crossing_budget 4
    signedChord_twentyFourTwentyFive_k4

#print axioms signedChord_twentyFourTwentyFive_fails_k0
#print axioms signedChordSum_eq_nodeMoment
#print axioms harmonicChordWeight_le_growthIncrement
#print axioms harmonicChordCumulative_le_majorant
#print axioms endpointGrowthMoment_cap_fails_k5
#print axioms harmonicChordGrowthCumulative_add_ramp
#print axioms signedChordNodeMoment_le_growthNodeMoment
#print axioms signedChordGrowthNodeMoment_add_ramp
#print axioms signedChordRampCarrier_eq_nodeMoment
#print axioms signedChordRampNodeMoment_nonneg
#print axioms signedChordGrowthNodeMoment_eq_correctedEndpoint
#print axioms signedChordNodeMoment_le_correctedEndpoint
#print axioms chord_endpoint_le_quadratic_geom
#print axioms harmonicChordWeight_le_quadraticIncrement
#print axioms signedChordNodeMoment_le_quadraticNodeMoment
#print axioms quadraticNodeMoment_cap_k5
#print axioms terminalCoefficientTwoFloor_le_terminalReserve
#print axioms nine_harmonicD_le_ten_terminalDiagonalPrefix
#print axioms signedChordMomentCore_le_terminalCoefficientTwoFloor
#print axioms signedChordMomentCap_le_target
#print axioms terminal_gap_k1_p0_not_nonpos
#print axioms signedChord_twentyFourTwentyFive_k1
#print axioms terminal_gap_k2_p0_not_nonpos
#print axioms signedChord_twentyFourTwentyFive_k2
#print axioms weightedTrapezoidResidual_nonpos_k1
#print axioms weightedTrapezoidResidual_nonpos_k2
#print axioms terminal_gap_k3_p0_not_nonpos
#print axioms signedChord_twentyFourTwentyFive_k3
#print axioms weightedTrapezoidResidual_nonpos_k3
#print axioms terminal_gap_k4_p0_not_nonpos
#print axioms signedChordNodeMoment_le_cap_k4
#print axioms signedChord_twentyFourTwentyFive_k4
#print axioms weightedTrapezoidResidual_nonpos_k4

end YMGap.Continuum.HarmonicSignedChordQuantitative
