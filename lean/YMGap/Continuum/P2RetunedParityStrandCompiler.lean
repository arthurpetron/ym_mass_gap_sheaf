/-
Track 11.7-fusion / R3g -- an alternating-strand compiler for the physical
two-fold coefficient tail.

The physical adjacent-tail slack is not monotone one cell at a time: its odd
and even rows interlace.  This module isolates the exact proof-by-computation
principle needed by that pattern.  For abstract positive left states `L_s`, an
odd head, a two-step comparison along the odd strand, and a comparison from
each following odd row back to the preceding even row imply `L_s <= R_s` on
the whole even support `s < 2*N`.

The specialization uses

  L_s = (s+1) g_{s+1},
  R_s = q^(2s+3) (s+2) g_s.

Thus the remaining analytic inputs are genuine parity interlacing laws, not a
renaming of the target cell inequalities.  Full Clebsch-support positivity is
used only to cancel the propagated left state.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatiblePhysicalBridge
import YMGap.Continuum.P2BlockCompatibleIntegralTailCertificate
import YMGap.Continuum.P2RetunedRatioCompiler
import YMGap.Continuum.SelfFusionLogConcave

namespace YMGap.Continuum.P2RetunedParityStrandCompiler

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatibleIntegralTailCertificate
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

/-! ## Abstract alternating-strand compiler -/

/-- Cross-multiplied certificate for an alternating family `L_s <= R_s` on
the support `1 <= s < 2*N`.  The odd strand advances by two.  Every even cell
is then obtained by comparing it with the already-proved preceding odd cell. -/
structure AlternatingTailStrands (L R : Nat -> Q') (N : Nat) : Type where
  head : L 1 <= R 1
  oddStep : forall m, 2 * m + 3 < 2 * N ->
    R (2 * m + 1) * L (2 * m + 3) <=
      R (2 * m + 3) * L (2 * m + 1)
  evenBridge : forall m, 1 <= m -> 2 * m < 2 * N ->
    R (2 * m - 1) * L (2 * m) <=
      R (2 * m) * L (2 * m - 1)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- Transport an alternating certificate across pointwise exact rational
identities.  This is used below to replace the physical coefficients by their
proved Clebsch-box reconstruction without changing the analytic obligations. -/
def alternatingTailStrands_of_eqv
    {L R L' R' : Nat -> Q'} {N : Nat}
    (hL : forall s, L s ≈ L' s) (hR : forall s, R s ≈ R' s)
    (T : AlternatingTailStrands L' R' N) :
    AlternatingTailStrands L R N where
  head :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (hL 1))
      (Q'.le_trans' _ _ _ T.head (Q'.ge_of_eqv (hR 1)))
  oddStep := fun m hm => by
    have hleft :
        R (2 * m + 1) * L (2 * m + 3) ≈
          R' (2 * m + 1) * L' (2 * m + 3) :=
      mul_eqv_both (hR _) (hL _)
    have hright :
        R (2 * m + 3) * L (2 * m + 1) ≈
          R' (2 * m + 3) * L' (2 * m + 1) :=
      mul_eqv_both (hR _) (hL _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (T.oddStep m hm) (Q'.ge_of_eqv hright))
  evenBridge := fun m hm1 hm => by
    have hleft :
        R (2 * m - 1) * L (2 * m) ≈
          R' (2 * m - 1) * L' (2 * m) :=
      mul_eqv_both (hR _) (hL _)
    have hright :
        R (2 * m) * L (2 * m - 1) ≈
          R' (2 * m) * L' (2 * m - 1) :=
      mul_eqv_both (hR _) (hL _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (T.evenBridge m hm1 hm)
        (Q'.ge_of_eqv hright))

private theorem odd_tail_of_strands {L R : Nat -> Q'} {N : Nat}
    (hLpos : forall s, s < 2 * N -> (0 : Q') < L s)
    (T : AlternatingTailStrands L R N) :
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
      have hprev : L prev <= R prev := by
        dsimp only [prev]
        exact odd_tail_of_strands hLpos T m (by omega)
      have hnextNonneg : (0 : Q') <= L next :=
        Q'.le_of_lt (hLpos next hnextSupport)
      have hscaled : L prev * L next <= R prev * L next :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hprev hnextNonneg
      have hcross : L prev * L next <= R next * L prev :=
        Q'.le_trans' _ _ _ hscaled (T.oddStep m (by omega))
      have hreordered : L prev * L next <= L prev * R next :=
        Q'.le_trans' _ _ _ hcross
          (Q'.le_of_eqv (Q'.mul_comm_eqv (R next) (L prev)))
      have hnext : L next <= R next :=
        Q'.le_of_mul_le_mul_left hreordered (hLpos prev hprevSupport)
      have hindex : 2 * (m + 1) + 1 = next := by
        dsimp only [next]
        omega
      simpa only [hindex] using hnext

/-- The alternating certificate compiles to every cell on the complete even
support.  This is the reusable computation theorem: an unbounded linear scan
is replaced by one head and two parity transition schemas. -/
theorem tail_of_alternating_strands {L R : Nat -> Q'} {N : Nat}
    (hLpos : forall s, s < 2 * N -> (0 : Q') < L s)
    (T : AlternatingTailStrands L R N) :
    forall s, 1 <= s -> s < 2 * N -> L s <= R s := by
  intro s hs1 hsupport
  rcases Nat.mod_two_eq_zero_or_one s with heven | hodd
  · have hsEven : s = 2 * (s / 2) := by omega
    have hm1 : 1 <= s / 2 := by omega
    have hoddIndex : s - 1 = 2 * (s / 2 - 1) + 1 := by omega
    have hoddSupport : s - 1 < 2 * N := by omega
    have hprevOdd : L (s - 1) <= R (s - 1) := by
      rw [hoddIndex]
      exact odd_tail_of_strands hLpos T (s / 2 - 1) (by omega)
    have hleftNonneg : (0 : Q') <= L s :=
      Q'.le_of_lt (hLpos s hsupport)
    have hscaled : L s * L (s - 1) <= L s * R (s - 1) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hprevOdd hleftNonneg
    have hscaled' : L s * L (s - 1) <= R (s - 1) * L s :=
      Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.mul_comm_eqv (L s) (R (s - 1))))
    have hbridge : R (s - 1) * L s <= R s * L (s - 1) := by
      rw [hsEven]
      exact T.evenBridge (s / 2) hm1 (by omega)
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
    exact odd_tail_of_strands hLpos T (s / 2) (by omega)

/-! ## Physical coefficient specialization -/

/-- Left state of the division-free physical adjacent-tail inequality. -/
def coeffTailLeft (N : Nat) (w : Q') (s : Nat) : Q' :=
  dimQ s * bondMovedCoeff N w 2 (s + 1)

/-- Unpowered right coefficient state.  The complete right state is the heat
power `q^(2s+3)` times this quantity. -/
def coeffTailBase (N : Nat) (w : Q') (s : Nat) : Q' :=
  dimQ (s + 1) * bondMovedCoeff N w 2 s

/-- Right state of the division-free physical adjacent-tail inequality. -/
def coeffTailRight (N : Nat) (w : Q') (s : Nat) : Q' :=
  qpow (p2RetunedWeight w) (2 * s + 3) *
    coeffTailBase N w s

/-- Parity-strand certificate in the physical bond-moved coordinates. -/
abbrev P2RetunedParityStrands (N : Nat) (w : Q') : Type :=
  AlternatingTailStrands (coeffTailLeft N w) (coeffTailRight N w) N

/-- Fixed-power form of the physical parity laws.  Compared with
`P2RetunedParityStrands`, the common growing factor `q^(2s+3)` has been
canceled.  Only `q^4` along the odd strand and `q^2` across an even/odd bridge
remain. -/
structure P2RetunedCoreParityStrands (N : Nat) (w : Q') : Type where
  head : coeffTailLeft N w 1 <= coeffTailRight N w 1
  oddStep : forall m, 2 * m + 3 < 2 * N ->
    coeffTailBase N w (2 * m + 1) *
        coeffTailLeft N w (2 * m + 3) <=
      (qpow (p2RetunedWeight w) 4 *
          coeffTailBase N w (2 * m + 3)) *
        coeffTailLeft N w (2 * m + 1)
  evenBridge : forall m, 1 <= m -> 2 * m < 2 * N ->
    coeffTailBase N w (2 * m - 1) *
        coeffTailLeft N w (2 * m) <=
      (qpow (p2RetunedWeight w) 2 *
          coeffTailBase N w (2 * m)) *
        coeffTailLeft N w (2 * m - 1)

/-- Reinsert the common heat power into the fixed-power core laws. -/
def parityStrands_of_core {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (T : P2RetunedCoreParityStrands N w) :
    P2RetunedParityStrands N w where
  head := T.head
  oddStep := fun m hm => by
    let q := p2RetunedWeight w
    let e := 2 * (2 * m + 1) + 3
    let qe := qpow q e
    let q4 := qpow q 4
    let qnext := qpow q (2 * (2 * m + 3) + 3)
    let Bprev := coeffTailBase N w (2 * m + 1)
    let Bnext := coeffTailBase N w (2 * m + 3)
    let Lprev := coeffTailLeft N w (2 * m + 1)
    let Lnext := coeffTailLeft N w (2 * m + 3)
    have hscaled : qe * (Bprev * Lnext) <=
        qe * ((q4 * Bnext) * Lprev) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (T.oddStep m hm)
        (qpow_nonneg q (p2RetunedWeight_nonneg hw0) e)
    have hexp : 2 * (2 * m + 3) + 3 = e + 4 := by
      dsimp only [e]
      omega
    have hpow : qe * q4 ≈ qnext := by
      dsimp only [qe, q4, qnext]
      rw [hexp]
      exact Q'.eqv_symm (HeatKernelRGStep.qpow_add q e 4)
    have hleft :
        coeffTailRight N w (2 * m + 1) * Lnext ≈
          qe * (Bprev * Lnext) := by
      unfold coeffTailRight
      dsimp only [q, e, qe, Bprev]
      exact Q'.mul_assoc_eqv _ _ _
    have hright : qe * ((q4 * Bnext) * Lprev) ≈
        coeffTailRight N w (2 * m + 3) * Lprev := by
      have hregroup : qe * ((q4 * Bnext) * Lprev) ≈
          ((qe * q4) * Bnext) * Lprev := by
        refine Q'.eqv_trans _ (qe * (q4 * Bnext) * Lprev) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv qe (q4 * Bnext) Lprev)) ?_
        exact Q'.mul_eqv_congr_right _ _ Lprev
          (Q'.eqv_symm (Q'.mul_assoc_eqv qe q4 Bnext))
      have hreplace : ((qe * q4) * Bnext) * Lprev ≈
          (qnext * Bnext) * Lprev :=
        Q'.mul_eqv_congr_right _ _ Lprev
          (Q'.mul_eqv_congr_right _ _ Bnext hpow)
      refine Q'.eqv_trans _ _ _ hregroup ?_
      refine Q'.eqv_trans _ _ _ hreplace ?_
      unfold coeffTailRight
      dsimp only [q, qnext, Bnext]
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
  evenBridge := fun m hm1 hm => by
    let q := p2RetunedWeight w
    let e := 2 * (2 * m - 1) + 3
    let qe := qpow q e
    let q2 := qpow q 2
    let qnext := qpow q (2 * (2 * m) + 3)
    let Bodd := coeffTailBase N w (2 * m - 1)
    let Beven := coeffTailBase N w (2 * m)
    let Lodd := coeffTailLeft N w (2 * m - 1)
    let Leven := coeffTailLeft N w (2 * m)
    have hscaled : qe * (Bodd * Leven) <=
        qe * ((q2 * Beven) * Lodd) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (T.evenBridge m hm1 hm)
        (qpow_nonneg q (p2RetunedWeight_nonneg hw0) e)
    have hexp : 2 * (2 * m) + 3 = e + 2 := by
      dsimp only [e]
      omega
    have hpow : qe * q2 ≈ qnext := by
      dsimp only [qe, q2, qnext]
      rw [hexp]
      exact Q'.eqv_symm (HeatKernelRGStep.qpow_add q e 2)
    have hleft :
        coeffTailRight N w (2 * m - 1) * Leven ≈
          qe * (Bodd * Leven) := by
      unfold coeffTailRight
      dsimp only [q, e, qe, Bodd]
      exact Q'.mul_assoc_eqv _ _ _
    have hright : qe * ((q2 * Beven) * Lodd) ≈
        coeffTailRight N w (2 * m) * Lodd := by
      have hregroup : qe * ((q2 * Beven) * Lodd) ≈
          ((qe * q2) * Beven) * Lodd := by
        refine Q'.eqv_trans _ (qe * (q2 * Beven) * Lodd) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv qe (q2 * Beven) Lodd)) ?_
        exact Q'.mul_eqv_congr_right _ _ Lodd
          (Q'.eqv_symm (Q'.mul_assoc_eqv qe q2 Beven))
      have hreplace : ((qe * q2) * Beven) * Lodd ≈
          (qnext * Beven) * Lodd :=
        Q'.mul_eqv_congr_right _ _ Lodd
          (Q'.mul_eqv_congr_right _ _ Beven hpow)
      refine Q'.eqv_trans _ _ _ hregroup ?_
      refine Q'.eqv_trans _ _ _ hreplace ?_
      unfold coeffTailRight
      dsimp only [q, qnext, Beven]
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-- Left state in exact weighted Clebsch-box coordinates. -/
def boxTailLeft (N : Nat) (w : Q') (s : Nat) : Q' :=
  dimQ s * boxSum w N (s + 1)

/-- Unpowered right state in exact weighted Clebsch-box coordinates. -/
def boxTailBase (N : Nat) (w : Q') (s : Nat) : Q' :=
  dimQ (s + 1) * boxSum w N s

/-- Right state in exact weighted Clebsch-box coordinates. -/
def boxTailRight (N : Nat) (w : Q') (s : Nat) : Q' :=
  qpow (p2RetunedWeight w) (2 * s + 3) *
    boxTailBase N w s

/-- The parity certificate expressed directly on the finite Clebsch box. -/
abbrev P2RetunedBoxParityStrands (N : Nat) (w : Q') : Type :=
  AlternatingTailStrands (boxTailLeft N w) (boxTailRight N w) N

/-- Fixed-power core laws stated directly on the weighted Clebsch box. -/
structure P2RetunedBoxCoreParityStrands (N : Nat) (w : Q') : Type where
  head : boxTailLeft N w 1 <= boxTailRight N w 1
  oddStep : forall m, 2 * m + 3 < 2 * N ->
    boxTailBase N w (2 * m + 1) *
        boxTailLeft N w (2 * m + 3) <=
      (qpow (p2RetunedWeight w) 4 *
          boxTailBase N w (2 * m + 3)) *
        boxTailLeft N w (2 * m + 1)
  evenBridge : forall m, 1 <= m -> 2 * m < 2 * N ->
    boxTailBase N w (2 * m - 1) *
        boxTailLeft N w (2 * m) <=
      (qpow (p2RetunedWeight w) 2 *
          boxTailBase N w (2 * m)) *
        boxTailLeft N w (2 * m - 1)

theorem coeffTailLeft_eqv_boxTailLeft (N : Nat) (w : Q') (s : Nat) :
    coeffTailLeft N w s ≈ boxTailLeft N w s := by
  unfold coeffTailLeft boxTailLeft
  exact Q'.mul_eqv_congr_left _ _ _ (bondMovedCoeff_eq_boxSum N (s + 1))

theorem coeffTailBase_eqv_boxTailBase (N : Nat) (w : Q') (s : Nat) :
    coeffTailBase N w s ≈ boxTailBase N w s := by
  unfold coeffTailBase boxTailBase
  exact Q'.mul_eqv_congr_left _ _ _ (bondMovedCoeff_eq_boxSum N s)

theorem coeffTailRight_eqv_boxTailRight (N : Nat) (w : Q') (s : Nat) :
    coeffTailRight N w s ≈ boxTailRight N w s := by
  unfold coeffTailRight boxTailRight
  exact Q'.mul_eqv_congr_left _ _ _
    (coeffTailBase_eqv_boxTailBase N w s)

/-- Exact reconstruction transports the fixed-power box laws to the physical
coefficient laws. -/
def coreParityStrands_of_box {N : Nat} {w : Q'}
    (T : P2RetunedBoxCoreParityStrands N w) :
    P2RetunedCoreParityStrands N w where
  head :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (coeffTailLeft_eqv_boxTailLeft N w 1))
      (Q'.le_trans' _ _ _ T.head
        (Q'.ge_of_eqv (coeffTailRight_eqv_boxTailRight N w 1)))
  oddStep := fun m hm => by
    have hleft :
        coeffTailBase N w (2 * m + 1) *
            coeffTailLeft N w (2 * m + 3) ≈
          boxTailBase N w (2 * m + 1) *
            boxTailLeft N w (2 * m + 3) :=
      mul_eqv_both (coeffTailBase_eqv_boxTailBase N w _)
        (coeffTailLeft_eqv_boxTailLeft N w _)
    have hright :
        (qpow (p2RetunedWeight w) 4 *
            coeffTailBase N w (2 * m + 3)) *
            coeffTailLeft N w (2 * m + 1) ≈
          (qpow (p2RetunedWeight w) 4 *
            boxTailBase N w (2 * m + 3)) *
            boxTailLeft N w (2 * m + 1) :=
      mul_eqv_both
        (Q'.mul_eqv_congr_left _ _ _
          (coeffTailBase_eqv_boxTailBase N w _))
        (coeffTailLeft_eqv_boxTailLeft N w _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (T.oddStep m hm) (Q'.ge_of_eqv hright))
  evenBridge := fun m hm1 hm => by
    have hleft :
        coeffTailBase N w (2 * m - 1) *
            coeffTailLeft N w (2 * m) ≈
          boxTailBase N w (2 * m - 1) *
            boxTailLeft N w (2 * m) :=
      mul_eqv_both (coeffTailBase_eqv_boxTailBase N w _)
        (coeffTailLeft_eqv_boxTailLeft N w _)
    have hright :
        (qpow (p2RetunedWeight w) 2 *
            coeffTailBase N w (2 * m)) *
            coeffTailLeft N w (2 * m - 1) ≈
          (qpow (p2RetunedWeight w) 2 *
            boxTailBase N w (2 * m)) *
            boxTailLeft N w (2 * m - 1) :=
      mul_eqv_both
        (Q'.mul_eqv_congr_left _ _ _
          (coeffTailBase_eqv_boxTailBase N w _))
        (coeffTailLeft_eqv_boxTailLeft N w _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (T.evenBridge m hm1 hm)
        (Q'.ge_of_eqv hright))

/-- Box core laws compile all the way to the growing-power physical parity
certificate. -/
def parityStrands_of_boxCore {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (T : P2RetunedBoxCoreParityStrands N w) :
    P2RetunedParityStrands N w :=
  parityStrands_of_core hw0 (coreParityStrands_of_box T)

/-- Exact Peter--Weyl reconstruction transports a box parity certificate to
the physical bond-moved spectrum. -/
def parityStrands_of_box {N : Nat} {w : Q'}
    (T : P2RetunedBoxParityStrands N w) :
    P2RetunedParityStrands N w :=
  alternatingTailStrands_of_eqv
    (coeffTailLeft_eqv_boxTailLeft N w)
    (coeffTailRight_eqv_boxTailRight N w) T

theorem coeffTailLeft_pos {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (s : Nat) (hs : s < 2 * N) :
    (0 : Q') < coeffTailLeft N w s := by
  unfold coeffTailLeft
  exact Q'.mul_pos (dimQ_pos s)
    (bondMovedCoeff_p2_pos_full_support hwpos (by omega))

/-- The parity-strand laws imply the exact division-free adjacent coefficient
tail on every supported mode. -/
def p2CoeffTailRatio_of_parityStrands {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (hw1 : w <= (1 : Q'))
    (T : P2RetunedParityStrands N w) :
    P2RetunedCoeffTailRatio N w (Q'.le_of_lt hwpos) hw1 where
  tail := fun s hs1 hsupport => by
    exact tail_of_alternating_strands
      (fun r hr => coeffTailLeft_pos hwpos r hr) T s hs1 hsupport

/-! ## Closed physical schedule family -/

/-- Schedule-wide parity interlacing is a strictly structured sufficient
condition for the all-cutoff coefficient data. -/
structure BlockCompatibleP2ParityStrandData : Type where
  strands : forall k,
    P2RetunedParityStrands (blockNcut k) (blockWeight k)

def BlockCompatibleP2ParityStrandData.toCoeffTailData
    (T : BlockCompatibleP2ParityStrandData) :
    BlockCompatibleP2CoeffTailData where
  coeffTailRatio := fun k =>
    p2CoeffTailRatio_of_parityStrands
      (blockWeight_pos k) (blockWeight_le_one k) (T.strands k)

/-- Schedule-wide predecessor stated entirely in weighted Clebsch-box
coordinates, ready for ballot/interlacing arguments. -/
structure BlockCompatibleP2BoxParityStrandData : Type where
  boxStrands : forall k,
    P2RetunedBoxParityStrands (blockNcut k) (blockWeight k)

def BlockCompatibleP2BoxParityStrandData.toParityStrandData
    (T : BlockCompatibleP2BoxParityStrandData) :
    BlockCompatibleP2ParityStrandData where
  strands := fun k => parityStrands_of_box (T.boxStrands k)

def BlockCompatibleP2BoxParityStrandData.toCoeffTailData
    (T : BlockCompatibleP2BoxParityStrandData) :
    BlockCompatibleP2CoeffTailData :=
  T.toParityStrandData.toCoeffTailData

/-- Strongest current analytic interface: fixed powers and exact weighted-box
coordinates at every physical scale. -/
structure BlockCompatibleP2BoxCoreParityStrandData : Type where
  boxCore : forall k,
    P2RetunedBoxCoreParityStrands (blockNcut k) (blockWeight k)

def BlockCompatibleP2BoxCoreParityStrandData.toCoeffTailData
    (T : BlockCompatibleP2BoxCoreParityStrandData) :
    BlockCompatibleP2CoeffTailData where
  coeffTailRatio := fun k =>
    p2CoeffTailRatio_of_parityStrands
      (blockWeight_pos k) (blockWeight_le_one k)
      (parityStrands_of_boxCore (blockWeight_nonneg k) (T.boxCore k))

/-- Honest post-prefix coefficient frontier.  The exact integral certificates
handle `k=0,1,2,3`; only the true fixed-power parity laws are requested from
`k=4` onward. -/
structure BlockCompatibleP2BoxCoreParityStrandFromFour : Type where
  boxCore : forall k, 4 <= k ->
    P2RetunedBoxCoreParityStrands (blockNcut k) (blockWeight k)

def BlockCompatibleP2BoxCoreParityStrandFromFour.toCoeffTailFromFour
    (T : BlockCompatibleP2BoxCoreParityStrandFromFour) :
    BlockCompatibleP2CoeffTailFromFour where
  tail := fun k hk =>
    p2CoeffTailRatio_of_parityStrands
      (blockWeight_pos k) (blockWeight_le_one k)
      (parityStrands_of_boxCore (blockWeight_nonneg k) (T.boxCore k hk))

def BlockCompatibleP2BoxCoreParityStrandFromFour.toCoeffTailData
    (T : BlockCompatibleP2BoxCoreParityStrandFromFour) :
    BlockCompatibleP2CoeffTailData :=
  T.toCoeffTailFromFour.toAllScale

#print axioms tail_of_alternating_strands
#print axioms alternatingTailStrands_of_eqv
#print axioms parityStrands_of_core
#print axioms coeffTailLeft_pos
#print axioms coreParityStrands_of_box
#print axioms parityStrands_of_box
#print axioms p2CoeffTailRatio_of_parityStrands
#print axioms BlockCompatibleP2ParityStrandData.toCoeffTailData
#print axioms BlockCompatibleP2BoxParityStrandData.toCoeffTailData
#print axioms BlockCompatibleP2BoxCoreParityStrandData.toCoeffTailData
#print axioms BlockCompatibleP2BoxCoreParityStrandFromFour.toCoeffTailData

end YMGap.Continuum.P2RetunedParityStrandCompiler
