/-
Track 11.7-fusion / R4ad -- endpoint-spliced parity compiler.

The heat-matched parity automaton previously requested its two transition
laws on the whole support, including the macroscopic endpoint region now
proved directly.  This file supplies the missing proof-about-computation
principle: an alternating induction may use direct cells on a decidable
region and request a transition only when its target lies outside that
region.

Specializing the decidable region to the exact physical endpoint cover leaves
only off-cover odd/even transition atoms.  The resulting line-sum family
coarsens to the existing common physical carrier, so this reduction does not
change the canonical spectrum or the genuine BlockingStep.Phi trajectory.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier

namespace YMGap.Continuum.P2HalfTimeEndpointSplicedParityCompiler

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler
open YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier
open YMGap.Continuum.P2BlockCompatiblePhysicalFrontierStrictFromEight
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent
open YMGap.Continuum.P2HalfTimeParityStrandCompiler
open YMGap.Continuum.P2HalfTimeShiftTail
open YMGap.Continuum.P2RetunedParityStrandCompiler
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Abstract decidable-region alternating induction -/

/-- Alternating proof data after a decidable family of target cells has been
proved directly.  Transition laws are requested only outside that family. -/
structure AlternatingTailOutside
    (L R : Nat -> Q') (P : Nat -> Prop) (N : Nat) : Type where
  head : L 1 <= R 1
  direct : forall s, 1 <= s -> s < 2 * N -> P s -> L s <= R s
  oddStep : forall m, 2 * m + 3 < 2 * N -> ¬ P (2 * m + 3) ->
    R (2 * m + 1) * L (2 * m + 3) <=
      R (2 * m + 3) * L (2 * m + 1)
  evenBridge : forall m, 1 <= m -> 2 * m < 2 * N -> ¬ P (2 * m) ->
    R (2 * m - 1) * L (2 * m) <=
      R (2 * m) * L (2 * m - 1)

private theorem odd_tail_of_outside
    {L R : Nat -> Q'} {P : Nat -> Prop} [DecidablePred P] {N : Nat}
    (hLpos : forall s, s < 2 * N -> (0 : Q') < L s)
    (T : AlternatingTailOutside L R P N) :
    forall m, 2 * m + 1 < 2 * N -> L (2 * m + 1) <= R (2 * m + 1)
  | 0, _ => by
      simpa using T.head
  | m + 1, hsupport => by
      let prev := 2 * m + 1
      let next := 2 * m + 3
      have hprevSupport : prev < 2 * N := by
        dsimp only [prev]
        omega
      have hnextSupport : next < 2 * N := by
        dsimp only [next]
        omega
      by_cases hdirect : P next
      · have hnext := T.direct next (by omega) hnextSupport hdirect
        have hindex : 2 * (m + 1) + 1 = next := by
          dsimp only [next]
          omega
        simpa only [hindex] using hnext
      · have hprev : L prev <= R prev := by
          dsimp only [prev]
          exact odd_tail_of_outside hLpos T m (by omega)
        have hnextNonneg : (0 : Q') <= L next :=
          Q'.le_of_lt (hLpos next hnextSupport)
        have hscaled : L prev * L next <= R prev * L next :=
          Q'.mul_le_mul_of_nonneg_right _ _ _ hprev hnextNonneg
        have hcross : L prev * L next <= R next * L prev :=
          Q'.le_trans' _ _ _ hscaled (T.oddStep m (by omega) hdirect)
        have hreordered : L prev * L next <= L prev * R next :=
          Q'.le_trans' _ _ _ hcross
            (Q'.le_of_eqv (Q'.mul_comm_eqv (R next) (L prev)))
        have hnext : L next <= R next :=
          Q'.le_of_mul_le_mul_left hreordered (hLpos prev hprevSupport)
        have hindex : 2 * (m + 1) + 1 = next := by
          dsimp only [next]
          omega
        simpa only [hindex] using hnext

/-- Direct cells and off-region transitions together prove the complete
alternating tail.  This is the reusable program-induction theorem. -/
theorem tail_of_alternating_outside
    {L R : Nat -> Q'} {P : Nat -> Prop} [DecidablePred P] {N : Nat}
    (hLpos : forall s, s < 2 * N -> (0 : Q') < L s)
    (T : AlternatingTailOutside L R P N) :
    forall s, 1 <= s -> s < 2 * N -> L s <= R s := by
  intro s hs1 hsupport
  by_cases hdirect : P s
  · exact T.direct s hs1 hsupport hdirect
  · rcases Nat.mod_two_eq_zero_or_one s with heven | hodd
    · have hsEven : s = 2 * (s / 2) := by omega
      have hm1 : 1 <= s / 2 := by omega
      have hoddIndex : s - 1 = 2 * (s / 2 - 1) + 1 := by omega
      have hoddSupport : s - 1 < 2 * N := by omega
      have hprevOdd : L (s - 1) <= R (s - 1) := by
        rw [hoddIndex]
        exact odd_tail_of_outside hLpos T (s / 2 - 1) (by omega)
      have hleftNonneg : (0 : Q') <= L s :=
        Q'.le_of_lt (hLpos s hsupport)
      have hscaled : L s * L (s - 1) <= L s * R (s - 1) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hprevOdd hleftNonneg
      have hscaled' : L s * L (s - 1) <= R (s - 1) * L s :=
        Q'.le_trans' _ _ _ hscaled
          (Q'.le_of_eqv (Q'.mul_comm_eqv (L s) (R (s - 1))))
      have hbridge : R (s - 1) * L s <= R s * L (s - 1) := by
        rw [hsEven]
        exact T.evenBridge (s / 2) hm1 (by omega) (by
          simpa only [← hsEven] using hdirect)
      have hcross : L s * L (s - 1) <= R s * L (s - 1) :=
        Q'.le_trans' _ _ _ hscaled' hbridge
      have hreordered : L (s - 1) * L s <= L (s - 1) * R s :=
        Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_comm_eqv (L (s - 1)) (L s)))
          (Q'.le_trans' _ _ _ hcross
            (Q'.le_of_eqv (Q'.mul_comm_eqv (R s) (L (s - 1)))))
      exact Q'.le_of_mul_le_mul_left hreordered
        (hLpos (s - 1) hoddSupport)
    · have hsOdd : s = 2 * (s / 2) + 1 := by omega
      rw [hsOdd]
      exact odd_tail_of_outside hLpos T (s / 2) (by omega)

/-! ## 2. Pointwise reinsertion of the growing heat powers -/

private theorem halfTimeBox_oddStep_of_core
    {N : Nat} {w : Q'} (hw0 : (0 : Q') <= w) (m : Nat)
    (hcore :
      boxTailBase N w (2 * m + 1) * boxTailLeft N w (2 * m + 3) <=
        (qpow w 2 * boxTailBase N w (2 * m + 3)) *
          boxTailLeft N w (2 * m + 1)) :
    halfTimeBoxRight N w (2 * m + 1) * boxTailLeft N w (2 * m + 3) <=
      halfTimeBoxRight N w (2 * m + 3) * boxTailLeft N w (2 * m + 1) := by
  let e := (2 * m + 1) + 2
  let qe := qpow w e
  let q2 := qpow w 2
  let qnext := qpow w ((2 * m + 3) + 2)
  let Bprev := boxTailBase N w (2 * m + 1)
  let Bnext := boxTailBase N w (2 * m + 3)
  let Lprev := boxTailLeft N w (2 * m + 1)
  let Lnext := boxTailLeft N w (2 * m + 3)
  have hscaled : qe * (Bprev * Lnext) <=
      qe * ((q2 * Bnext) * Lprev) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcore (qpow_nonneg w hw0 e)
  have hexp : (2 * m + 3) + 2 = e + 2 := by omega
  have hpow : qe * q2 ≈ qnext := by
    dsimp only [qe, q2, qnext]
    rw [hexp]
    exact Q'.eqv_symm (qpow_add w e 2)
  have hleft : halfTimeBoxRight N w (2 * m + 1) * Lnext ≈
      qe * (Bprev * Lnext) := by
    unfold halfTimeBoxRight
    dsimp only [e, qe, Bprev]
    exact Q'.mul_assoc_eqv _ _ _
  have hright : qe * ((q2 * Bnext) * Lprev) ≈
      halfTimeBoxRight N w (2 * m + 3) * Lprev := by
    have hregroup : qe * ((q2 * Bnext) * Lprev) ≈
        ((qe * q2) * Bnext) * Lprev := by
      refine Q'.eqv_trans _ (qe * (q2 * Bnext) * Lprev) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv qe (q2 * Bnext) Lprev)) ?_
      exact Q'.mul_eqv_congr_right _ _ Lprev
        (Q'.eqv_symm (Q'.mul_assoc_eqv qe q2 Bnext))
    have hreplace : ((qe * q2) * Bnext) * Lprev ≈
        (qnext * Bnext) * Lprev :=
      Q'.mul_eqv_congr_right _ _ Lprev
        (Q'.mul_eqv_congr_right _ _ Bnext hpow)
    refine Q'.eqv_trans _ _ _ hregroup ?_
    refine Q'.eqv_trans _ _ _ hreplace ?_
    unfold halfTimeBoxRight
    dsimp only [qnext, Bnext]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

private theorem halfTimeBox_evenBridge_of_core
    {N : Nat} {w : Q'} (hw0 : (0 : Q') <= w) (m : Nat) (hm : 1 <= m)
    (hcore :
      boxTailBase N w (2 * m - 1) * boxTailLeft N w (2 * m) <=
        (w * boxTailBase N w (2 * m)) *
          boxTailLeft N w (2 * m - 1)) :
    halfTimeBoxRight N w (2 * m - 1) * boxTailLeft N w (2 * m) <=
      halfTimeBoxRight N w (2 * m) * boxTailLeft N w (2 * m - 1) := by
  let e := (2 * m - 1) + 2
  let qe := qpow w e
  let qnext := qpow w (2 * m + 2)
  let Bodd := boxTailBase N w (2 * m - 1)
  let Beven := boxTailBase N w (2 * m)
  let Lodd := boxTailLeft N w (2 * m - 1)
  let Leven := boxTailLeft N w (2 * m)
  have hscaled : qe * (Bodd * Leven) <= qe * ((w * Beven) * Lodd) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcore (qpow_nonneg w hw0 e)
  have hexp : 2 * m + 2 = e + 1 := by
    dsimp only [e]
    omega
  have hpow : qe * w ≈ qnext := by
    dsimp only [qe, qnext]
    rw [hexp]
    exact Q'.eqv_refl _
  have hleft : halfTimeBoxRight N w (2 * m - 1) * Leven ≈
      qe * (Bodd * Leven) := by
    unfold halfTimeBoxRight
    have hindex : 2 * m - 1 + 2 = e := by rfl
    rw [hindex]
    dsimp only [qe, Bodd]
    exact Q'.mul_assoc_eqv _ _ _
  have hright : qe * ((w * Beven) * Lodd) ≈
      halfTimeBoxRight N w (2 * m) * Lodd := by
    have hregroup : qe * ((w * Beven) * Lodd) ≈
        ((qe * w) * Beven) * Lodd := by
      refine Q'.eqv_trans _ (qe * (w * Beven) * Lodd) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv qe (w * Beven) Lodd)) ?_
      exact Q'.mul_eqv_congr_right _ _ Lodd
        (Q'.eqv_symm (Q'.mul_assoc_eqv qe w Beven))
    have hreplace : ((qe * w) * Beven) * Lodd ≈
        (qnext * Beven) * Lodd :=
      Q'.mul_eqv_congr_right _ _ Lodd
        (Q'.mul_eqv_congr_right _ _ Beven hpow)
    refine Q'.eqv_trans _ _ _ hregroup ?_
    refine Q'.eqv_trans _ _ _ hreplace ?_
    unfold halfTimeBoxRight
    dsimp only [qnext, Beven]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-! ## 3. Exact physical endpoint-cover predicate -/

def physicalEndpointCoverAt (k s : Nat) : Prop :=
  let N := blockNcut k
  let m := 2 * N - s
  2 * m <= N ∧ (m + 1) * (s + 2) <= physicalWeightDen k

instance physicalEndpointCoverAtDecidable (k s : Nat) :
    Decidable (physicalEndpointCoverAt k s) := by
  unfold physicalEndpointCoverAt
  infer_instance

theorem physical_halfTime_box_of_endpointCoverAt
    (k s : Nat) (hk : 4 <= k) (hs : 1 <= s)
    (hsN : s < 2 * blockNcut k) (hcover : physicalEndpointCoverAt k s) :
    boxTailLeft (blockNcut k) (blockWeight k) s <=
      halfTimeBoxRight (blockNcut k) (blockWeight k) s := by
  let N := blockNcut k
  let m := 2 * N - s
  have hm : 0 < m := by
    dsimp only [m, N]
    omega
  have hdepth : 2 * m <= N := by
    simpa only [physicalEndpointCoverAt, N, m] using hcover.1
  have hpay : (m + 1) * (2 * N - m + 2) <= physicalWeightDen k := by
    have hsEq : 2 * N - m = s := by
      dsimp only [m]
      omega
    simpa only [hsEq] using hcover.2
  have hbox := physical_halfTime_box_of_cover_from_four
    k m hk hm (by simpa only [N] using hdepth) (by
      simpa only [N] using hpay)
  unfold boxTailLeft halfTimeBoxRight boxTailBase
  simpa only [N, m,
    show 2 * blockNcut k - (2 * blockNcut k - s) = s by omega,
    show 2 * blockNcut k - (2 * blockNcut k - s) + 1 = s + 1 by omega,
    show 2 * blockNcut k - (2 * blockNcut k - s) + 2 = s + 2 by omega]
    using hbox

/-! ## 4. Off-cover transition frontier and line-sum compiler -/

structure BlockCompatibleP2HalfTimeOffCoverTransitionsFromFour : Type where
  odd : forall k m, 4 <= k -> 2 * m + 3 < 2 * blockNcut k ->
    ¬ physicalEndpointCoverAt k (2 * m + 3) ->
    physicalHalfTimeBoxOddTransitionAt k m
  even : forall k m, 4 <= k -> 1 <= m -> 2 * m < 2 * blockNcut k ->
    ¬ physicalEndpointCoverAt k (2 * m) ->
    physicalHalfTimeBoxEvenTransitionAt k m

def BlockCompatibleP2HalfTimeOffCoverTransitionsFromFour.toLineSumTail
    (T : BlockCompatibleP2HalfTimeOffCoverTransitionsFromFour) :
    BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => {
    tail := fun s hs hsN => by
      let A : AlternatingTailOutside
          (boxTailLeft (blockNcut k) (blockWeight k))
          (halfTimeBoxRight (blockNcut k) (blockWeight k))
          (physicalEndpointCoverAt k) (blockNcut k) := {
        head := physical_halfTime_box_head_from_four k hk
        direct := fun t ht htN hcover =>
          physical_halfTime_box_of_endpointCoverAt k t hk ht htN hcover
        oddStep := fun m hm houtside =>
          halfTimeBox_oddStep_of_core (blockWeight_nonneg k) m
            (physicalHalfTimeBoxOddTransitionAt_sound k m
              (T.odd k m hk hm houtside))
        evenBridge := fun m hm1 hm houtside =>
          halfTimeBox_evenBridge_of_core (blockWeight_nonneg k) m hm1
            (physicalHalfTimeBoxEvenTransitionAt_sound k m
              (T.even k m hk hm1 hm houtside))
      }
      have hbox := tail_of_alternating_outside
        (fun t ht => boxTailLeft_pos (blockWeight_pos k) t ht) A s hs hsN
      have eleft :
          dimQ s * lineSum (lagCorr (blockWeight k) (blockNcut k)) (s + 1) ≈
            boxTailLeft (blockNcut k) (blockWeight k) s := by
        unfold boxTailLeft
        exact Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (boxSum_eq_lineSum_lagCorr (blockWeight k) (blockNcut k) (s + 1)))
      have ebase :
          boxTailBase (blockNcut k) (blockWeight k) s ≈
            dimQ (s + 1) *
              lineSum (lagCorr (blockWeight k) (blockNcut k)) s := by
        unfold boxTailBase
        exact Q'.mul_eqv_congr_left _ _ _
          (boxSum_eq_lineSum_lagCorr (blockWeight k) (blockNcut k) s)
      have eright : halfTimeBoxRight (blockNcut k) (blockWeight k) s ≈
          qpow (blockWeight k) (s + 2) *
            (dimQ (s + 1) *
              lineSum (lagCorr (blockWeight k) (blockNcut k)) s) := by
        unfold halfTimeBoxRight
        exact Q'.mul_eqv_congr_left _ _ _ ebase
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
        (Q'.le_trans' _ _ _ hbox (Q'.le_of_eqv eright))
  }

def BlockCompatibleP2HalfTimeOffCoverTransitionsFromFour.toCoeffTailData
    (T : BlockCompatibleP2HalfTimeOffCoverTransitionsFromFour) :
    BlockCompatibleP2CoeffTailData :=
  (BlockCompatibleP2HalfTimeCoeffTailFromFour.mk fun k hk =>
    ((T.toLineSumTail).tail k hk).toCoeff).toAllScale

/-- The endpoint-spliced parity route lands in the same common physical
carrier as the full-local reserve route. -/
structure BlockCompatibleP2PhysicalEndpointSplicedParityFrontier : Type where
  coefficient : BlockCompatibleP2HalfTimeOffCoverTransitionsFromFour
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

def BlockCompatibleP2PhysicalEndpointSplicedParityFrontier.toCompiled
    (A : BlockCompatibleP2PhysicalEndpointSplicedParityFrontier) :
    BlockCompatibleP2PhysicalCompiledFrontier where
  coefficient := A.coefficient.toCoeffTailData
  theta := A.theta

end YMGap.Continuum.P2HalfTimeEndpointSplicedParityCompiler

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeEndpointSplicedParityCompiler.tail_of_alternating_outside
#print axioms YMGap.Continuum.P2HalfTimeEndpointSplicedParityCompiler.physical_halfTime_box_of_endpointCoverAt
#print axioms YMGap.Continuum.P2HalfTimeEndpointSplicedParityCompiler.BlockCompatibleP2HalfTimeOffCoverTransitionsFromFour.toLineSumTail
#print axioms YMGap.Continuum.P2HalfTimeEndpointSplicedParityCompiler.BlockCompatibleP2HalfTimeOffCoverTransitionsFromFour.toCoeffTailData
#print axioms YMGap.Continuum.P2HalfTimeEndpointSplicedParityCompiler.BlockCompatibleP2PhysicalEndpointSplicedParityFrontier.toCompiled
