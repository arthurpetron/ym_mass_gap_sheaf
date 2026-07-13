/-
Harmonic specialization of the generic half-edge PF2 framework.

This downstream module deliberately imports the already-proved growing-anchor
tail estimate instead of changing the shared import graph of the carrier file.
-/

import YMGap.Continuum.HarmonicDriftAntisymmetry
import YMGap.Continuum.HarmonicGrowingAnchorPF2

namespace YMGap.Continuum.HarmonicHalfEdgeDominance

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.HarmonicBulkThetaTail
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicGrowingAnchorPF2
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

/-- The raw `1/8` growing-anchor multiplier, before weakening it to the
retune cube. -/
theorem growing_anchor_tail_eighth (k : Nat) :
    coeffW (harmW k) (growingAnchor k + 1) ≤
      Q'.mkPos 1 8 (by decide) * coeffW (harmW k) (growingAnchor k) := by
  have hratio := tailTerm_ratio_gen (harmW_nonneg k) (harmW_le_one k)
    1 (growingAnchor k) (growingAnchor k) (Nat.le_refl _)
  have hc0 := coeffW_nonneg (harmW_nonneg k) (growingAnchor k)
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ _
    (growing_anchor_multiplier_le_eighth k) hc0
  have hTL : coeffW (harmW k) (growingAnchor k + 1) ≈
      tailTerm (harmW k) 1 (growingAnchor k + 1) := by
    unfold tailTerm coeffW dimQ
    simp only [Nat.pow_one]
    exact Q'.eqv_refl _
  have hTR : tailTerm (harmW k) 1 (growingAnchor k) ≈
      coeffW (harmW k) (growingAnchor k) := by
    unfold tailTerm coeffW dimQ
    simp only [Nat.pow_one]
    exact Q'.eqv_refl _
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hTL)
    (Q'.le_trans' _ _ _ hratio ?_)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hTR)) hs

/-- PF2 propagates the exact `1/8` ratio to every later coefficient. -/
theorem tail_eighth_of_growing_anchor (k : Nat) {a : Nat}
    (ha : growingAnchor k ≤ a) :
    coeffW (harmW k) (a + 1) ≤
      Q'.mkPos 1 8 (by decide) * coeffW (harmW k) a := by
  by_cases heq : a = growingAnchor k
  · subst a
    exact growing_anchor_tail_eighth k
  · have hlt : growingAnchor k < a := Nat.lt_of_le_of_ne ha (Ne.symm heq)
    have hinj := shifted_ratio_injection (harmW_nonneg k) (harmW_le_one k)
      (harmW_pos k) (a := growingAnchor k) (N := a) hlt
    have hca0 := coeffW_nonneg (harmW_nonneg k) a
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _
      (growing_anchor_tail_eighth k) hca0
    have hchain :
        coeffW (harmW k) (growingAnchor k) * coeffW (harmW k) (a + 1) ≤
          coeffW (harmW k) (growingAnchor k) *
            (Q'.mkPos 1 8 (by decide) * coeffW (harmW k) a) := by
      refine Q'.le_trans' _ _ _ hinj ?_
      refine Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv ?_)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    exact Q'.le_of_mul_le_mul_left hchain
      (FusionResidualBound.coeffW_pos (harmW_pos k) (growingAnchor k))

/-- Except for the closed `k=0` endpoint, the growing anchor lies before the
last retained edge. -/
theorem growingAnchor_le_lastCutoff (k : Nat) :
    growingAnchor (k + 1) ≤ Ncut (k + 1) - 1 := by
  let m := k + 3
  have h2 : 2 ≤ k + 2 := by omega
  have hmul := Nat.mul_le_mul_right (k + 3) h2
  have hmul' : 2 * (k + 3) ≤ (k + 2) * (k + 3) := by
    simpa [Nat.mul_comm] using hmul
  have heq : (k + 3) * (k + 3) = (k + 2) * (k + 3) + (k + 3) := by
    rw [show k + 3 = (k + 2) + 1 by omega, Nat.add_mul]
    omega
  unfold growingAnchor Ncut
  rw [show k + 1 + 2 = k + 3 by omega]
  rw [heq]
  omega

/-- The terminal cross comparison follows from its cancellation-free local
form `halfEdgeNum_L*c_{L+1} ≤ c_L*D_L`. -/
theorem terminal_cross_of_local (c : Nat → Q') (L : Nat)
    (hc : (0 : Q') ≤ c (L + 1))
    (hlocal : halfEdgeNum c L * c (L + 1) ≤ c L * profileD c L) :
    halfEdgeNum c L * profileD c (L + 1) ≤
      (profileA c (L + 1) + profileA c (L + 1)) * profileD c L := by
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ (c (L + 1)) hlocal hc
  have hedge : halfEdgeNum c L * (c (L + 1) * c (L + 1)) ≤
      (c L * c (L + 1)) * profileD c L := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_assoc_eqv (halfEdgeNum c L) (c (L + 1)) (c (L + 1)))))
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (by ring_qeqv)))
  have hadd := Q'.add_le_add_left
    (halfEdgeNum c L * profileD c L) _ _ hedge
  have hL : halfEdgeNum c L * profileD c (L + 1) ≈
      halfEdgeNum c L * profileD c L +
        halfEdgeNum c L * (c (L + 1) * c (L + 1)) := by
    unfold profileD
    exact Q'.mul_add_eqv _ _ _
  have hR : (profileA c (L + 1) + profileA c (L + 1)) * profileD c L ≈
      halfEdgeNum c L * profileD c L +
        (c L * c (L + 1)) * profileD c L := by
    unfold halfEdgeNum profileA
    simp only [fsum_succ]
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hR))

/-- The quadratic-cutoff terminal gate for every noninitial harmonic scale.
The propagated `1/8` tail ratio pays the coarse `3D` half-edge numerator. -/
theorem harmonic_terminal_cross_succ (k : Nat) :
    let K := k + 1
    let c := coeffW (harmW K)
    let L := Ncut K - 1
    halfEdgeNum c L * profileD c (L + 1) ≤
      (profileA c (L + 1) + profileA c (L + 1)) * profileD c L := by
  dsimp only
  let K := k + 1
  let c := coeffW (harmW K)
  let L := Ncut K - 1
  have hN : 1 ≤ Ncut K := by
    unfold Ncut
    exact Nat.mul_pos (by omega) (by omega)
  have hLN : L + 1 = Ncut K := Nat.sub_add_cancel hN
  have hanchor : growingAnchor K ≤ L := by
    dsimp only [K, L]
    exact growingAnchor_le_lastCutoff k
  have hy : c (L + 1) ≤ Q'.mkPos 1 8 (by decide) * c L :=
    tail_eighth_of_growing_anchor K hanchor
  have hx0 : (0 : Q') ≤ c L := coeffW_nonneg (harmW_nonneg K) L
  have hy0 : (0 : Q') ≤ c (L + 1) := coeffW_nonneg (harmW_nonneg K) (L + 1)
  have hD0 : (0 : Q') ≤ profileD c L := by
    unfold profileD c
    exact fsum_nonneg (fun i => Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg K) i)
      (coeffW_nonneg (harmW_nonneg K) i)) (L + 1)
  have hA0 : (0 : Q') ≤ profileA c L := by
    unfold profileA c
    exact fsum_nonneg (fun i => Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg K) i)
      (coeffW_nonneg (harmW_nonneg K) (i + 1))) L
  have hAD : profileA c L ≤ profileD c L := by
    change adjCorr (harmW K) L ≤ coordNormSq (harmW K) L
    exact AllWindowCorrDirichlet.adjCorr_le_coordNormSq _ _
  have hyx : c (L + 1) ≤ c L := by
    have heighth : Q'.mkPos 1 8 (by decide) ≤ (1 : Q') := by decide
    have hs := Q'.mul_le_mul_of_nonneg_right _ _ (c L) heighth hx0
    exact Q'.le_trans' _ _ _ hy
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.one_mul_eqv _)))
  have hxxD : c L * c L ≤ profileD c L := by
    unfold profileD
    exact BondMovingMoment.fsum_term_le_of_nonneg
      (fun i => Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg K) i)
        (coeffW_nonneg (harmW_nonneg K) i)) L (L + 1) (by omega)
  have hedgeD : c L * c (L + 1) ≤ profileD c L := by
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ (c L) hyx hx0
    exact Q'.le_trans' _ _ _ hm hxxD
  have hH0 : (0 : Q') ≤ halfEdgeNum c L := by
    unfold halfEdgeNum
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _ hA0 hA0)
      (Q'.mul_nonneg _ _ hx0 hy0)
  have hH3 : halfEdgeNum c L ≤
      (profileD c L + profileD c L) + profileD c L := by
    unfold halfEdgeNum
    exact Q'.add_le_add (Q'.add_le_add hAD hAD) hedgeD
  have hstep1 := Q'.mul_le_mul_of_nonneg_right _ _ (c (L + 1)) hH3 hy0
  have h3D0 : (0 : Q') ≤ (profileD c L + profileD c L) + profileD c L :=
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hD0 hD0) hD0
  have hstep2 := Q'.mul_le_mul_of_nonneg_left _ _
    ((profileD c L + profileD c L) + profileD c L) hy h3D0
  have hscale :
      ((profileD c L + profileD c L) + profileD c L) *
          (Q'.mkPos 1 8 (by decide) * c L) ≤ c L * profileD c L := by
    have hconst : Q'.mkPos 3 8 (by decide) ≤ (1 : Q') := by decide
    have hprod0 : (0 : Q') ≤ profileD c L * c L :=
      Q'.mul_nonneg _ _ hD0 hx0
    have hs := Q'.mul_le_mul_of_nonneg_right _ _ (profileD c L * c L)
      hconst hprod0
    have hpre :
        ((profileD c L + profileD c L) + profileD c L) *
            (Q'.mkPos 1 8 (by decide) * c L) ≈
          (Q'.mkPos 1 8 (by decide) + Q'.mkPos 1 8 (by decide) +
            Q'.mkPos 1 8 (by decide)) * (profileD c L * c L) := by
      ring_qeqv
    have hconsteq :
        Q'.mkPos 1 8 (by decide) + Q'.mkPos 1 8 (by decide) +
            Q'.mkPos 1 8 (by decide) ≈ Q'.mkPos 3 8 (by decide) := by
      decide
    have hpre' := Q'.eqv_trans _ _ _ hpre
      (Q'.mul_eqv_congr_right _ _ (profileD c L * c L) hconsteq)
    have hpost : (1 : Q') * (profileD c L * c L) ≈ c L * profileD c L := by
      exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
        (Q'.mul_comm_eqv _ _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpre')
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hpost))
  have hlocal : halfEdgeNum c L * c (L + 1) ≤ c L * profileD c L :=
    Q'.le_trans' _ _ _ hstep1 (Q'.le_trans' _ _ _ hstep2 hscale)
  exact terminal_cross_of_local c L hy0 hlocal

theorem harmonic_terminal_cross_zero :
    let c := coeffW (harmW 0)
    let L := Ncut 0 - 1
    halfEdgeNum c L * profileD c (L + 1) ≤
      (profileA c (L + 1) + profileA c (L + 1)) * profileD c L := by
  unfold halfEdgeNum profileD profileA Ncut harmW harmU
    ReciprocalBernoulliUpper.oneSub unit coeffW dimQ c4 qpow fsum
  decide

/-! ## Smooth-cap propagation of every local half-edge step -/

/-- A base half-edge cap and the four-term smooth-cap monotonicity propagate
the cap through the whole profile.  Unlike bare PF2, the four-term condition
forbids an abrupt collapse of consecutive coefficient ratios. -/
theorem halfEdge_cap_invariant (c : Nat → Q')
    (hc0 : ∀ i, (0 : Q') ≤ c i)
    (hcp : ∀ i, (0 : Q') < c i)
    (hbase : halfEdgeNum c 0 * c 1 ≤ profileD c 0 * (c 0 + c 2))
    (hcap : ∀ i,
      (c i + c (i + 2)) * c (i + 2) ≤
        (c (i + 1) + c (i + 3)) * c (i + 1)) :
    ∀ i, halfEdgeNum c i * c (i + 1) ≤
      profileD c i * (c i + c (i + 2)) := by
  intro i
  induction i with
  | zero => exact hbase
  | succ i ih =>
      have hiz := Q'.mul_le_mul_of_nonneg_right _ _ (c (i + 2)) ih (hc0 (i + 2))
      have hcapD := Q'.mul_le_mul_of_nonneg_left _ _ (profileD c i)
        (hcap i) (by
          unfold profileD
          exact fsum_nonneg (fun j => Q'.mul_nonneg _ _ (hc0 j) (hc0 j)) (i + 1))
      have hchain :
          c (i + 1) * (halfEdgeNum c i * c (i + 2)) ≤
            c (i + 1) * (profileD c i * (c (i + 1) + c (i + 3))) := by
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv))
          (Q'.le_trans' _ _ _ hiz
            (Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv))
              (Q'.le_trans' _ _ _ hcapD (Q'.le_of_eqv (by ring_qeqv)))))
      have hold : halfEdgeNum c i * c (i + 2) ≤
          profileD c i * (c (i + 1) + c (i + 3)) :=
        Q'.le_of_mul_le_mul_left hchain (hcp (i + 1))
      have hnew0 := Q'.mul_le_mul_of_nonneg_left _ _ (c (i + 1))
        (hcap i) (hc0 (i + 1))
      have hnew :
          (c (i + 1) * (c i + c (i + 2))) * c (i + 2) ≤
            (c (i + 1) * c (i + 1)) * (c (i + 1) + c (i + 3)) := by
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv))
          (Q'.le_trans' _ _ _ hnew0 (Q'.le_of_eqv (by ring_qeqv)))
      have hadd := Q'.add_le_add hold hnew
      have hL : halfEdgeNum c (i + 1) * c (i + 2) ≈
          halfEdgeNum c i * c (i + 2) +
            (c (i + 1) * (c i + c (i + 2))) * c (i + 2) := by
        unfold halfEdgeNum profileA
        simp only [fsum_succ]
        rw [show i + 1 + 1 = i + 2 by omega]
        ring_qeqv
      have hR : profileD c (i + 1) * (c (i + 1) + c (i + 3)) ≈
          profileD c i * (c (i + 1) + c (i + 3)) +
            (c (i + 1) * c (i + 1)) * (c (i + 1) + c (i + 3)) := by
        unfold profileD
        exact Q'.add_mul_eqv _ _ _
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
        (Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hR))

theorem halfEdge_steps_of_smooth_cap (c : Nat → Q')
    (hc0 : ∀ i, (0 : Q') ≤ c i)
    (hcp : ∀ i, (0 : Q') < c i)
    (hbase : halfEdgeNum c 0 * c 1 ≤ profileD c 0 * (c 0 + c 2))
    (hcap : ∀ i,
      (c i + c (i + 2)) * c (i + 2) ≤
        (c (i + 1) + c (i + 3)) * c (i + 1))
    (i : Nat) :
    halfEdgeNum c i * profileD c (i + 1) ≤
      halfEdgeNum c (i + 1) * profileD c i := by
  have hinv := halfEdge_cap_invariant c hc0 hcp hbase hcap i
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (c (i + 1)) hinv (hc0 (i + 1))
  have hlocal :
      halfEdgeNum c i * (c (i + 1) * c (i + 1)) ≤
        profileD c i *
          (c i * c (i + 1) + c (i + 1) * c (i + 2)) := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv))
      (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (by ring_qeqv)))
  exact halfEdge_step_of_shifted_local c i hlocal

private theorem oneSub_oneSub_eqv (x : Q') :
    ((1 : Q') - ((1 : Q') - x)) ≈ x := by
  show ((1 : Q') + (-((1 : Q') + (-x)))) ≈ x
  have h1 : (-((1 : Q') + (-x))) ≈ ((-(1 : Q')) + x) :=
    Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (1 : Q') (-x))
      (Q'.add_eqv_congr_left (-(1 : Q')) _ _ (Q'.neg_neg_eqv x))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ _ h1) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-(1 : Q')) x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ x (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact q_zero_add_eqv x

/-- Reciprocal Bernoulli rewritten at a direct base `t` rather than the margin
`1-t`. -/
theorem base_pow_mul_bernDen_oneSub_le {t : Q'}
    (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ (1 : Q')) (n : Nat) :
    qpow t n * bernDen ((1 : Q') - t) n ≤ (1 : Q') := by
  let u := (1 : Q') - t
  have hu0 : (0 : Q') ≤ u := Q'.sub_nonneg_of_le ht1
  have hu1 : u ≤ (1 : Q') := BondMovingRetuneFix.oneSub_le_one ht0
  have h := oneSub_pow_mul_bernDen_le hu0 hu1 n
  have hp : qpow (oneSub u) n ≈ qpow t n := by
    exact BondMovingRelResidual.qpow_eqv_congr_base
      (oneSub_oneSub_eqv t) n
  have he : qpow (oneSub u) n * bernDen u n ≈
      qpow t n * bernDen ((1 : Q') - t) n :=
    Q'.mul_eqv_congr_right _ _ _ hp
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) h

private theorem bernThree_cancel (p t : Q') :
    p * bernDen ((1 : Q') - t) 3 + Q'.ofNat 3 * (p * t) ≈
      Q'.ofNat 4 * p := by
  let z := Q'.ofNat 3 * (p * t)
  have hinner : p * (Q'.ofNat 3 * ((1 : Q') - t)) ≈
      Q'.ofNat 3 * p + -z := by
    unfold z
    change p * (Q'.ofNat 3 * ((1 : Q') + -t)) ≈
      Q'.ofNat 3 * p + -(Q'.ofNat 3 * (p * t))
    have hraw : p * (Q'.ofNat 3 * ((1 : Q') + -t)) ≈
        Q'.ofNat 3 * p + -(p * (Q'.ofNat 3 * t)) := by
      ring_qeqv
    refine Q'.eqv_trans _ _ _ hraw ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (by ring_qeqv))
  have hfirst : p * bernDen ((1 : Q') - t) 3 ≈
      p + (Q'.ofNat 3 * p + -z) := by
    unfold bernDen
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv p 1
      (Q'.ofNat 3 * ((1 : Q') - t))) ?_
    exact Q'.add_eqv_congr' (Q'.mul_one_eqv p) hinner
  have hregroup : (p + (Q'.ofNat 3 * p + -z)) + z ≈
      (p + Q'.ofNat 3 * p) + (-z + z) := by
    ring_qeqv
  have hcancel : -z + z ≈ (0 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (Q'.add_neg_self_eqv z)
  have hfour : p + Q'.ofNat 3 * p ≈ Q'.ofNat 4 * p := by
    have hnum : Q'.ofNat 4 ≈ Q'.ofNat 1 + Q'.ofNat 3 := by
      exact Q'.eqv_trans _ _ _ (by decide)
        (Q'.eqv_symm (Q'.ofNat_add_eqv 1 3))
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ p hnum) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
    have hone : Q'.ofNat 1 * p ≈ p :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ p (by decide : Q'.ofNat 1 ≈ (1 : Q')))
        (Q'.one_mul_eqv p)
    exact Q'.add_eqv_congr_right _ _ (Q'.ofNat 3 * p)
      hone
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ z hfirst) ?_
  refine Q'.eqv_trans _ _ _ hregroup ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hcancel) ?_
  refine Q'.eqv_trans _ _ _ (q_add_zero_eqv _) hfour

theorem four_cube_le_one_add_three_fourth {t : Q'}
    (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ (1 : Q')) :
    Q'.ofNat 4 * qpow t 3 ≤
      (1 : Q') + Q'.ofNat 3 * qpow t 4 := by
  have hb := base_pow_mul_bernDen_oneSub_le ht0 ht1 3
  have hz0 : (0 : Q') ≤ Q'.ofNat 3 * qpow t 4 :=
    Q'.mul_nonneg _ _ (by decide) (qpow_nonneg t ht0 4)
  have hadd := Q'.add_le_add_right _ _ (Q'.ofNat 3 * qpow t 4) hb
  have hpow : qpow t 4 ≈ qpow t 3 * t := Q'.eqv_refl _
  have hL : qpow t 3 * bernDen ((1 : Q') - t) 3 +
      Q'.ofNat 3 * qpow t 4 ≈ Q'.ofNat 4 * qpow t 3 := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _ hpow)) ?_
    exact bernThree_cancel _ _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) hadd

/-- The Bernoulli carrier in the exact index arithmetic needed by the harmonic
four-coefficient cap.  The coefficient identity is
`(2i+5) + (i+1)(i+3) = (i+2)(i+4)`. -/
theorem smoothCap_bernCarrier {t : Q'}
    (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ (1 : Q')) (i : Nat) :
    qpow t (2 * i + 5) *
        ((1 : Q') + Q'.ofNat ((i + 2) * (i + 4)) * ((1 : Q') - t)) ≤
      (1 : Q') + Q'.ofNat ((i + 1) * (i + 3)) * ((1 : Q') - t) := by
  let P := 2 * i + 5
  let A := (i + 1) * (i + 3)
  let B := (i + 2) * (i + 4)
  let d := (1 : Q') - t
  have hd0 : (0 : Q') ≤ d := Q'.sub_nonneg_of_le ht1
  have hbern := base_pow_mul_bernDen_oneSub_le ht0 ht1 P
  have hpow := HeatKernelGap.qpow_le_one ht0 ht1 P
  have hAd0 : (0 : Q') ≤ Q'.ofNat A * d :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' A) hd0
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.ofNat A * d) hpow hAd0
  have hadd := Q'.add_le_add hbern hscaled
  have hPA : P + A = B := by
    unfold P A B
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    omega
  have hcoef : Q'.ofNat P + Q'.ofNat A ≈ Q'.ofNat B := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.ofNat_add_eqv P A))
      (Q'.eqv_of_eq (congrArg Q'.ofNat hPA))
  have hL : qpow t P * bernDen d P + qpow t P * (Q'.ofNat A * d) ≈
      qpow t P * ((1 : Q') + Q'.ofNat B * d) := by
    unfold bernDen
    refine Q'.eqv_trans _
      (qpow t P * ((1 : Q') + (Q'.ofNat P + Q'.ofNat A) * d)) _
      (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_left (qpow t P) _ _
      (Q'.add_eqv_congr_left (1 : Q') _ _
        (Q'.mul_eqv_congr_right _ _ d hcoef))
  have hR : (1 : Q') + (1 : Q') * (Q'.ofNat A * d) ≈
      (1 : Q') + Q'.ofNat A * d :=
    Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.one_mul_eqv _)
  change qpow t P * ((1 : Q') + Q'.ofNat B * d) ≤
    (1 : Q') + Q'.ofNat A * d
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hR))

/-- Addition-only rearrangement of `smoothCap_bernCarrier`.  It is deliberately
stated with the two reusable monomials `x=t^A`, `y=t^P`; no subtraction or
cancellation is used. -/
theorem smoothCap_algebraCarrier {t : Q'}
    (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ (1 : Q')) (i : Nat) :
    let A := (i + 1) * (i + 3)
    let B := (i + 2) * (i + 4)
    let P := 2 * i + 5
    let x := qpow t A
    let y := qpow t P
    Q'.ofNat A * (x * t) + ((1 : Q') + Q'.ofNat B) * (x * y) ≤
      ((1 : Q') + Q'.ofNat A) * x + Q'.ofNat B * ((x * y) * t) := by
  dsimp only
  let A := (i + 1) * (i + 3)
  let B := (i + 2) * (i + 4)
  let P := 2 * i + 5
  let x := qpow t A
  let y := qpow t P
  have h := smoothCap_bernCarrier ht0 ht1 i
  change y * ((1 : Q') + Q'.ofNat B * ((1 : Q') + (-t))) ≤
    (1 : Q') + Q'.ofNat A * ((1 : Q') + (-t)) at h
  have hx0 : (0 : Q') ≤ x := qpow_nonneg t ht0 A
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ x h hx0
  let z := Q'.ofNat A * (x * t) + Q'.ofNat B * ((x * y) * t)
  have hadd := Q'.add_le_add_right _ _ z hs
  have hL : x * (y * ((1 : Q') + Q'.ofNat B * ((1 : Q') + (-t)))) + z ≈
      Q'.ofNat A * (x * t) + ((1 : Q') + Q'.ofNat B) * (x * y) := by
    let a := Q'.ofNat A * (x * t)
    let u := x * y
    let v := Q'.ofNat B * u
    let q := Q'.ofNat B * (u * t)
    have he : x * (y * ((1 : Q') + Q'.ofNat B * ((1 : Q') + (-t)))) + z ≈
        ((u + v) + (-q)) + (a + q) := by
      dsimp only [z, a, u, v, q]
      ring_qeqv
    have hr : ((u + v) + (-q)) + (a + q) ≈
        (a + (u + v)) + ((-q) + q) := by
      ring_qeqv
    have hc : (-q) + q ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (Q'.add_neg_self_eqv q)
    refine Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ hr ?_)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (a + (u + v)) _ _ hc) ?_
    refine Q'.eqv_trans _ _ _ (q_add_zero_eqv _) ?_
    unfold a u v
    refine Q'.add_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _
      ((1 : Q') * (x * y) + Q'.ofNat B * (x * y)) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))) ?_
    exact Q'.eqv_symm (Q'.add_mul_eqv (1 : Q') (Q'.ofNat B) (x * y))
  have hR : x * ((1 : Q') + Q'.ofNat A * ((1 : Q') + (-t))) + z ≈
      ((1 : Q') + Q'.ofNat A) * x + Q'.ofNat B * ((x * y) * t) := by
    let a := Q'.ofNat A * (x * t)
    let u := x
    let v := Q'.ofNat A * x
    let q := Q'.ofNat B * ((x * y) * t)
    have he : x * ((1 : Q') + Q'.ofNat A * ((1 : Q') + (-t))) + z ≈
        ((u + v) + (-a)) + (a + q) := by
      dsimp only [z, a, u, v, q]
      ring_qeqv
    have hr : ((u + v) + (-a)) + (a + q) ≈
        ((u + v) + q) + ((-a) + a) := by
      ring_qeqv
    have hc : (-a) + a ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (Q'.add_neg_self_eqv a)
    refine Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ hr ?_)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left ((u + v) + q) _ _ hc) ?_
    refine Q'.eqv_trans _ _ _ (q_add_zero_eqv _) ?_
    unfold u v q
    refine Q'.add_eqv_congr_right _ _ _ ?_
    refine Q'.eqv_trans _ ((1 : Q') * x + Q'.ofNat A * x) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv x))) ?_
    exact Q'.eqv_symm (Q'.add_mul_eqv (1 : Q') (Q'.ofNat A) x)
  change Q'.ofNat A * (x * t) + ((1 : Q') + Q'.ofNat B) * (x * y) ≤
    ((1 : Q') + Q'.ofNat A) * x + Q'.ofNat B * ((x * y) * t)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hR))

private theorem coeffPair_sqbase (w : Q') (a b n : Nat)
    (hE : c4 a + c4 b = n + n) :
    coeffW w a * coeffW w b ≈
      Q'.ofNat ((a + 1) * (b + 1)) * qpow (w * w) n := by
  have hp : qpow w (c4 a + c4 b) ≈ qpow (w * w) n := by
    rw [hE]
    exact Q'.eqv_trans _ _ _ (HeatKernelRGStep.qpow_add w n n)
      (Q'.eqv_symm (FusionQuotientCollapse.qpow_mul_self w n))
  exact Q'.eqv_trans _ _ _
    (LaplaceMarginDeep.coeffW_mul_ofNat w a b)
    (Q'.mul_eqv_congr_left _ _ _ hp)

private theorem ofNat_succ_shape (n : Nat) :
    Q'.ofNat (n + 1) ≈ (1 : Q') + Q'.ofNat n := by
  refine Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.ofNat n) _ _
      (by decide : Q'.ofNat 1 ≈ (1 : Q'))) ?_
  exact Q'.add_comm_eqv _ _

/-- The harmonic coefficient profile satisfies the four-term smooth cap at
every index.  This is the local quantitative input needed by
`halfEdge_steps_of_smooth_cap`. -/
theorem harmonic_smooth_cap (k i : Nat) :
    let c := coeffW (harmW k)
    (c i + c (i + 2)) * c (i + 2) ≤
      (c (i + 1) + c (i + 3)) * c (i + 1) := by
  dsimp only
  let w := harmW k
  let t := w * w
  let A := (i + 1) * (i + 3)
  let B := (i + 2) * (i + 4)
  let P := 2 * i + 5
  let D := (i + 2) * (i + 2)
  let C := (i + 3) * (i + 3)
  let x := qpow t A
  let y := qpow t P
  have ht0 : (0 : Q') ≤ t := Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
  have ht1 : t ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_right _ _ w (harmW_le_one k)
      (harmW_nonneg k)
    exact Q'.le_trans' _ _ _ h
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv w)) (harmW_le_one k))
  have hcap := smoothCap_algebraCarrier ht0 ht1 i
  change Q'.ofNat A * (x * t) + ((1 : Q') + Q'.ofNat B) * (x * y) ≤
    ((1 : Q') + Q'.ofNat A) * x + Q'.ofNat B * ((x * y) * t) at hcap
  have hAD : A + 1 = D := by
    unfold A D
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    omega
  have hAB : A + P = B := by
    unfold A P B
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    omega
  have hBC : B + 1 = C := by
    unfold B C
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have hE02 : c4 i + c4 (i + 2) = D + D := by
    unfold c4 D
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have hE22 : c4 (i + 2) + c4 (i + 2) = B + B := by
    unfold c4 B
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have hE11 : c4 (i + 1) + c4 (i + 1) = A + A := by
    unfold c4 A
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have hE13 : c4 (i + 1) + c4 (i + 3) = C + C := by
    unfold c4 C
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have ep02 := coeffPair_sqbase w i (i + 2) D hE02
  have ep22 := coeffPair_sqbase w (i + 2) (i + 2) B hE22
  have ep11 := coeffPair_sqbase w (i + 1) (i + 1) A hE11
  have ep13 := coeffPair_sqbase w (i + 1) (i + 3) C hE13
  have hpD : qpow t D ≈ x * t := by
    rw [← hAD]
    exact Q'.eqv_refl _
  have hpB : qpow t B ≈ x * y := by
    rw [← hAB]
    exact HeatKernelRGStep.qpow_add t A P
  have hpC : qpow t C ≈ (x * y) * t := by
    rw [← hBC]
    exact Q'.mul_eqv_congr_right _ _ t hpB
  have hcoefD : Q'.ofNat D ≈ (1 : Q') + Q'.ofNat A := by
    rw [← hAD]
    exact ofNat_succ_shape A
  have hcoefC : Q'.ofNat C ≈ (1 : Q') + Q'.ofNat B := by
    rw [← hBC]
    exact ofNat_succ_shape B
  have eL : (coeffW w i + coeffW w (i + 2)) * coeffW w (i + 2) ≈
      Q'.ofNat A * (x * t) + ((1 : Q') + Q'.ofNat B) * (x * y) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · refine Q'.eqv_trans _ _ _ ep02 ?_
      exact Q'.mul_eqv_congr_left _ _ _ hpD
    · refine Q'.eqv_trans _ _ _ ep22 ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hcoefC) ?_
      exact Q'.mul_eqv_congr_left _ _ _ hpB
  have eR : (coeffW w (i + 1) + coeffW w (i + 3)) * coeffW w (i + 1) ≈
      ((1 : Q') + Q'.ofNat A) * x + Q'.ofNat B * ((x * y) * t) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · refine Q'.eqv_trans _ _ _ ep11 ?_
      exact Q'.mul_eqv_congr_right _ _ _ hcoefD
    · have ecomm : coeffW w (i + 3) * coeffW w (i + 1) ≈
          coeffW w (i + 1) * coeffW w (i + 3) := Q'.mul_comm_eqv _ _
      refine Q'.eqv_trans _ _ _ ecomm (Q'.eqv_trans _ _ _ ep13 ?_)
      exact Q'.mul_eqv_congr_left _ _ _ hpC
  change (coeffW w i + coeffW w (i + 2)) * coeffW w (i + 2) ≤
    (coeffW w (i + 1) + coeffW w (i + 3)) * coeffW w (i + 1)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL)
    (Q'.le_trans' _ _ _ hcap (Q'.ge_of_eqv eR))

theorem harmonic_base_cap (k : Nat) :
    let c := coeffW (harmW k)
    halfEdgeNum c 0 * c 1 ≤ profileD c 0 * (c 0 + c 2) := by
  dsimp only
  let w := harmW k
  let t := w * w
  have ht0 : (0 : Q') ≤ t := Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
  have ht1 : t ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_right _ _ w (harmW_le_one k)
      (harmW_nonneg k)
    exact Q'.le_trans' _ _ _ h
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv w)) (harmW_le_one k))
  have hcore := four_cube_le_one_add_three_fourth ht0 ht1
  have h3 : qpow t 3 ≈ qpow w 6 := by
    exact Q'.eqv_trans _ _ _
      (FusionQuotientCollapse.qpow_mul_self w 3)
      (Q'.eqv_symm (HeatKernelRGStep.qpow_add w 3 3))
  have h4 : qpow t 4 ≈ qpow w 8 := by
    exact Q'.eqv_trans _ _ _
      (FusionQuotientCollapse.qpow_mul_self w 4)
      (Q'.eqv_symm (HeatKernelRGStep.qpow_add w 4 4))
  have hc0 : coeffW w 0 = (1 : Q') := coeffW_zero w
  have hc1 : coeffW w 1 = Q'.ofNat 2 * qpow w 3 := rfl
  have hc2 : coeffW w 2 = Q'.ofNat 3 * qpow w 8 := rfl
  have h22 : Q'.ofNat 2 * Q'.ofNat 2 ≈ Q'.ofNat 4 := by decide
  have hp33 : qpow w 3 * qpow w 3 ≈ qpow w 6 :=
    Q'.eqv_symm (HeatKernelRGStep.qpow_add w 3 3)
  have hL : halfEdgeNum (coeffW w) 0 * coeffW w 1 ≈
      Q'.ofNat 4 * qpow t 3 := by
    simp only [halfEdgeNum, profileA, fsum_zero, hc0, hc1, Q'.zero_add']
    refine Q'.eqv_trans _
      ((Q'.ofNat 2 * qpow w 3) * (Q'.ofNat 2 * qpow w 3)) _ ?_ ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.one_mul_eqv (Q'.ofNat 2 * qpow w 3))
    refine Q'.eqv_trans _
      ((Q'.ofNat 2 * Q'.ofNat 2) * (qpow w 3 * qpow w 3)) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ h22) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hp33) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ (Q'.eqv_symm h3)
  have hR : profileD (coeffW w) 0 *
      (coeffW w 0 + coeffW w 2) ≈
      (1 : Q') + Q'.ofNat 3 * qpow t 4 := by
    simp only [profileD, fsum_succ, fsum_zero, hc0, hc2, Q'.zero_add']
    refine Q'.eqv_trans _ ((1 : Q') * ((1 : Q') + Q'.ofNat 3 * qpow w 8)) _ ?_ ?_
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (1 : Q'))
    refine Q'.eqv_trans _ ((1 : Q') + Q'.ofNat 3 * qpow w 8) _
      (Q'.one_mul_eqv _) ?_
    exact
      (Q'.add_eqv_congr_left (1 : Q') _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _ (Q'.eqv_symm h4)))
  change halfEdgeNum (coeffW w) 0 * coeffW w 1 ≤
    profileD (coeffW w) 0 * (coeffW w 0 + coeffW w 2)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hcore (Q'.ge_of_eqv hR))

/-- Every adjacent half-edge ratio step is monotone for the harmonic profile. -/
theorem harmonic_halfEdge_step (k i : Nat) :
    let c := coeffW (harmW k)
    halfEdgeNum c i * profileD c (i + 1) ≤
      halfEdgeNum c (i + 1) * profileD c i := by
  dsimp only
  exact halfEdge_steps_of_smooth_cap (coeffW (harmW k))
    (fun j => coeffW_nonneg (harmW_nonneg k) j)
    (fun j => FusionResidualBound.coeffW_pos (harmW_pos k) j)
    (harmonic_base_cap k) (harmonic_smooth_cap k) i

/-- Full finite-tail half-edge dominance at every harmonic scale.  The local
smooth-cap steps propagate to the final cutoff edge, where the independently
proved growing-anchor `1/8` tail closes the terminal comparison. -/
theorem harmonic_halfEdge_full (k : Nat) {p : Nat}
    (hp : p ≤ Ncut k - 1) :
    let c := coeffW (harmW k)
    let L := Ncut k - 1
    profileD c (L + 1) * halfEdgeNum c p ≤
      (profileA c (L + 1) + profileA c (L + 1)) * profileD c p := by
  dsimp only
  let c := coeffW (harmW k)
  let L := Ncut k - 1
  have hD : ∀ j, (0 : Q') < profileD c j := by
    intro j
    change (0 : Q') < coordNormSq (harmW k) j
    exact coordNormSq_pos (harmW_nonneg k) j
  have hstep : ∀ j, j < L →
      halfEdgeNum c j * profileD c (j + 1) ≤
        halfEdgeNum c (j + 1) * profileD c j := by
    intro j _
    exact harmonic_halfEdge_step k j
  have htail : halfEdgeNum c L * profileD c (L + 1) ≤
      (profileA c (L + 1) + profileA c (L + 1)) * profileD c L := by
    cases k with
    | zero => exact harmonic_terminal_cross_zero
    | succ k => exact harmonic_terminal_cross_succ k
  exact halfEdge_full_of_shiftedPF2 c L hD hstep htail hp

end YMGap.Continuum.HarmonicHalfEdgeDominance

#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.growing_anchor_tail_eighth
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.tail_eighth_of_growing_anchor
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.growingAnchor_le_lastCutoff
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.terminal_cross_of_local
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.harmonic_terminal_cross_succ
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.harmonic_terminal_cross_zero
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.halfEdge_cap_invariant
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.halfEdge_steps_of_smooth_cap
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.base_pow_mul_bernDen_oneSub_le
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.four_cube_le_one_add_three_fourth
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.smoothCap_bernCarrier
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.smoothCap_algebraCarrier
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.harmonic_smooth_cap
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.harmonic_base_cap
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.harmonic_halfEdge_step
#print axioms YMGap.Continuum.HarmonicHalfEdgeDominance.harmonic_halfEdge_full
