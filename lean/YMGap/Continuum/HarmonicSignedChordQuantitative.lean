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
