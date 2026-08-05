/-
Track 11.7-fusion / R2d -- a reflected finite saddle-to-exponential certificate.

The repaired finite saddle form supplies a genuine, deterministic logarithm of
each rational fusion eigenvalue, but it does not by itself contain an effective
rate or a theorem identifying logarithm and exponential.  A global log/exp
inverse would be a large and unnecessary detour for the finite support window.

This module instead verifies a finite *separation certificate*.  At every mode
the untrusted certificate chooses one of two routes:

* check the desired rational shift directly; or
* check, at one explicit series depth, that failure of the shift would force the
  eigenvalue logarithm strictly outside the supplied saddle bound.

The second route is non-circular.  Its Boolean atoms mention only rational
partial sums, explicit geometric tail recurrences, and a separately reduced
logarithm of `rateP weff s`.  Soundness uses the existing artanh tail theorem and
the `FaithfulFiniteSaddleLogForm.estimate` field to contradict that separation.
Thus a Rust or Lean generator may choose depths and routes, while the kernel
checks only the selected finite atoms.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration is used.  Every load-bearing declaration is axiom-gated below.
-/

import YMGap.Continuum.RebasedBulkLocalizationBridge

namespace YMGap.Continuum.ReflectedSaddleExpCertificate

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.RebasedBulkShift
open YMGap.Continuum.RebasedExpShiftSupportReduction
open YMGap.Continuum.RebasedBulkLocalizationBridge

/-! ## 1. Explicit approximation tails for deterministic dyadic logarithms -/

/-- A two-sided, explicit tail bound around approximation `K`. -/
def ApproxTail (x : CReal) (K : Nat) (T : Q') : Prop :=
  forall n, K <= n ->
    x.approx n <= x.approx K + T /\ x.approx K <= x.approx n + T

/-- The zero real has zero tail. -/
theorem approxTail_zero (K : Nat) : ApproxTail CReal.czero K 0 := by
  intro n hn
  change (0 : Q') <= 0 + 0 /\ (0 : Q') <= 0 + 0
  exact ⟨by decide, by decide⟩

/-- Explicit tails add componentwise. -/
theorem ApproxTail.add {x y : CReal} {K : Nat} {Tx Ty : Q'}
    (hx : ApproxTail x K Tx) (hy : ApproxTail y K Ty) :
    ApproxTail (CReal.add x y) K (Tx + Ty) := by
  intro n hn
  obtain ⟨hx1, hx2⟩ := hx n hn
  obtain ⟨hy1, hy2⟩ := hy n hn
  constructor
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add hx1 hy1) ?_
    exact Q'.le_of_eqv
      (Q'.add_swap_inner (x.approx K) Tx (y.approx K) Ty)
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add hx2 hy2) ?_
    exact Q'.le_of_eqv
      (Q'.add_swap_inner (x.approx n) Tx (y.approx n) Ty)

/-- Negation preserves a symmetric tail budget. -/
theorem ApproxTail.neg {x : CReal} {K : Nat} {T : Q'}
    (hx : ApproxTail x K T) : ApproxTail (CReal.neg x) K T := by
  intro n hn
  obtain ⟨h1, h2⟩ := hx n hn
  exact ⟨Q'.neg_le_neg_add h2, Q'.neg_le_neg_add h1⟩

/-- Subtraction adds the two symmetric tail budgets. -/
theorem ApproxTail.sub {x y : CReal} {K : Nat} {Tx Ty : Q'}
    (hx : ApproxTail x K Tx) (hy : ApproxTail y K Ty) :
    ApproxTail (CReal.sub x y) K (Tx + Ty) :=
  hx.add hy.neg

/-- One artanh series has tail `H` whenever its geometric recurrence closes at
the chosen depth. -/
theorem artanh_approxTail (y : Q') (hy : Q'.abs y <= recipOdd 1)
    (K : Nat) (H : Q') (hH : (0 : Q') <= H)
    (hrec : termAbs y K + oneNinth * H <= H) :
    ApproxTail (artanh y hy) K H := by
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have htail : blockAbs y K d <= H :=
    blockAbs_le y hy H K hH hrec d
  exact
    ⟨Q'.le_trans' _ _ _ (block_upper y K d)
        (Q'.add_le_add_left (partialSum y K) (blockAbs y K d) H htail),
      Q'.le_trans' _ _ _ (block_lower y K d)
        (Q'.add_le_add_left (partialSum y (K + d)) (blockAbs y K d) H htail)⟩

/-- A doubled artanh logarithm has tail `H+H`. -/
theorem logRat_approxTail (m : Q') (hm1 : (0 : Q') < m + 1)
    (hy : Q'.abs (yOf m hm1) <= recipOdd 1)
    (K : Nat) (H : Q') (hH : (0 : Q') <= H)
    (hrec : termAbs (yOf m hm1) K + oneNinth * H <= H) :
    ApproxTail (logRat m hm1 hy) K (H + H) :=
  (artanh_approxTail (yOf m hm1) hy K H hH hrec).add
    (artanh_approxTail (yOf m hm1) hy K H hH hrec)

/-- Tail budget for `k` repeated copies of the doubled log-two series. -/
def natLogTwoTail : Nat -> Q' -> Q'
  | 0, _ => 0
  | k + 1, H => natLogTwoTail k H + (H + H)

/-- The repeated constructive `log 2` sum obeys its structural tail budget. -/
theorem natLogTwo_approxTail (K : Nat) (H : Q') (hH : (0 : Q') <= H)
    (hrec2 : termAbs (yOf (2 : Q') (by decide)) K + oneNinth * H <= H) :
    forall k, ApproxTail (natLogTwo k) K (natLogTwoTail k H)
  | 0 => approxTail_zero K
  | k + 1 =>
      (natLogTwo_approxTail K H hH hrec2 k).add
        (logRat_approxTail (2 : Q') (by decide) yOf_two_window K H hH hrec2)

/-- The explicit total tail budget of a dyadic logarithm. -/
def dyadicLogTailBudget {q : Q'} (red : DyadicLogReduction q) (H : Q') : Q' :=
  (natLogTwoTail red.up H + natLogTwoTail red.down H) + (H + H)

/-- **Deterministic dyadic-log tail theorem.**  The two rational recurrences
(one shared `log 2`, one mantissa) imply a uniform tail around the chosen depth.
This is the construction-specific replacement for a global log/exp inverse. -/
theorem dyadicLogValue_approxTail {q : Q'} (red : DyadicLogReduction q)
    (K : Nat) (H : Q') (hH : (0 : Q') <= H)
    (hrec2 : termAbs (yOf (2 : Q') (by decide)) K + oneNinth * H <= H)
    (hrecM : termAbs (yOf red.m red.hm1) K + oneNinth * H <= H) :
    ApproxTail (dyadicLogValue red) K (dyadicLogTailBudget red H) := by
  exact
    ((natLogTwo_approxTail K H hH hrec2 red.up).sub
      (natLogTwo_approxTail K H hH hrec2 red.down)).add
      (logRat_approxTail red.m red.hm1 red.hyb K H hH hrecM)

/-! ## 2. Rational consequence lemmas used by checker soundness -/

/-- A symmetric tail controls the absolute value after adding a fixed anchor. -/
theorem abs_add_anchor_le_of_tail {x xK a T D : Q'}
    (h1 : x <= xK + T) (h2 : xK <= x + T)
    (hK : Q'.abs (xK + a) + T <= D) :
    Q'.abs (x + a) <= D := by
  have hdiff : Q'.abs (x + -xK) <= T :=
    Q'.abs_le
      (Q'.neg_le_sub_of_le_add h2)
      (Q'.sub_le_of_le_add h1)
  have habs : Q'.abs (x + a) <= Q'.abs (xK + a) + Q'.abs (x + -xK) := by
    have h := Q'.abs_le_abs_add_abs_sub (x + a) (xK + a)
    refine Q'.le_trans' _ _ _ h ?_
    refine Q'.add_le_add_left _ _ _ (Q'.le_of_eqv ?_)
    refine Q'.abs_eqv_congr ?_
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (x + a) _ _ (Q'.neg_add_eqv xK a))
      (Q'.eqv_trans _ _ _ (Q'.add_swap_inner x a (-xK) (-a))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (x + -xK) (a + -a) 0
            (Q'.add_neg_self_eqv a))
          (QPoly.q_add_zero_eqv (x + -xK))))
  exact Q'.le_trans' _ _ _ habs
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hdiff) hK)

/-- Absolute residuals around the same anchor bound the log difference. -/
theorem sub_le_of_anchored_abs {x y a B D : Q'}
    (hx : Q'.abs (x + a) <= B) (hy : Q'.abs (y + a) <= D) :
    x + -y <= B + D := by
  have hsum : (x + a) + (-(y + a)) <= B + D :=
    Q'.add_le_add (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hx)
      (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) hy)
  have heq : ((x + a) + (-(y + a))).eqv (x + -y) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (x + a) _ _ (Q'.neg_add_eqv y a))
      (Q'.eqv_trans _ _ _ (Q'.add_swap_inner x a (-y) (-a))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (x + -y) (a + -a) 0
            (Q'.add_neg_self_eqv a))
          (QPoly.q_add_zero_eqv (x + -y))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hsum

/-- Strict positivity of `mu` rules out absorbing `mu` into `mu/2`. -/
theorem not_add_mu_le_add_half_mu (B mu : Q') (hmu : (0 : Q') < mu) :
    Not (B + mu <= B + HalfPow.half * mu) := by
  intro h
  have hmu_le : mu <= HalfPow.half * mu := by
    have hs := Q'.sub_le_of_le_add h
    have heq : ((B + mu) + -B).eqv mu := Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (B + mu) (mu + B) (-B) (Q'.add_comm_eqv B mu))
      (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv mu B (-B))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left mu (B + -B) 0 (Q'.add_neg_self_eqv B))
          (QPoly.q_add_zero_eqv mu)))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hs
  have hhalf_lt : HalfPow.half * mu < mu := by
    have hhalf : HalfPow.half < (1 : Q') := by decide
    have hmulLeft : mu * HalfPow.half < mu * (1 : Q') :=
      Q'.mul_lt_mul_of_pos_left hmu hhalf
    have hmul : HalfPow.half * mu < mu * (1 : Q') :=
      Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hmulLeft
    exact HeatKernelRGStep.lt_of_lt_of_le hmul
      (Q'.le_of_eqv (Q'.mul_one_eqv mu))
  exact ClusteringImpliesGap.lt_irrefl' mu
    (Q'.lt_of_le_of_lt hmu_le hhalf_lt)

/-! ## 3. The selected reflected mode certificate -/

/-- Untrusted data for one finite mode.  `direct=true` asks the kernel to check
the target rational shift.  `direct=false` asks it to check the cheaper
saddle-separation route at depth `K`. -/
structure ModeData {N : Nat} {w : Q'} {p : Nat}
    {h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (S : FaithfulFiniteSaddleLogForm N w p h0') (weff : Q')
    (s : Nat) (hs : s <= 2 * N) : Type where
  direct : Bool
  rateReduction : DyadicLogReduction (rateP weff s)
  K : Nat
  eigH : Q'
  rateH : Q'
  delta : Q'
  mu : Q'

/-- The selected Boolean atom for one mode.  The false route checks only
rational series approximations and tail recurrences. -/
def modeCheck {N : Nat} {w : Q'} {p : Nat}
    {h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (S : FaithfulFiniteSaddleLogForm N w p h0') (weff : Q')
    (s : Nat) (hs : s <= 2 * N) (D : ModeData S weff s hs) : Bool :=
  if D.direct then
    decide (fusionEig N w p s (h0' s) - rateP weff s <= q112)
  else
    decide (
      (0 : Q') <= D.eigH /\
      (0 : Q') <= D.rateH /\
      (0 : Q') < D.mu /\
      termAbs (yOf (2 : Q') (by decide)) D.K + oneNinth * D.eigH <= D.eigH /\
      termAbs (yOf (S.logReduction s hs).m (S.logReduction s hs).hm1) D.K +
        oneNinth * D.eigH <= D.eigH /\
      termAbs (yOf (2 : Q') (by decide)) D.K + oneNinth * D.rateH <= D.rateH /\
      termAbs (yOf D.rateReduction.m D.rateReduction.hm1) D.K +
        oneNinth * D.rateH <= D.rateH /\
      Q'.abs ((dyadicLogValue D.rateReduction).approx D.K +
          S.A * Q'.ofNat (c4 s)) + dyadicLogTailBudget D.rateReduction D.rateH <= D.delta /\
      (S.eta * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) + D.delta) + D.mu <=
        ((dyadicLogValue (S.logReduction s hs)).approx D.K +
            -((dyadicLogValue D.rateReduction).approx D.K)) +
          -(dyadicLogTailBudget (S.logReduction s hs) D.eigH +
            dyadicLogTailBudget D.rateReduction D.rateH)
    )

/-- **Selected-mode soundness.**  Either the direct rational atom succeeds, or
the reflected separation atoms contradict the faithful saddle estimate. -/
theorem modeCheck_sound {N : Nat} {w : Q'} {p : Nat}
    {h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (S : FaithfulFiniteSaddleLogForm N w p h0') (weff : Q')
    (s : Nat) (hs : s <= 2 * N) (D : ModeData S weff s hs)
    (hcheck : modeCheck S weff s hs D = true) :
    fusionEig N w p s (h0' s) - rateP weff s <= q112 := by
  unfold modeCheck at hcheck
  by_cases hd : D.direct = true
  · simp only [hd, ↓reduceIte] at hcheck
    exact of_decide_eq_true hcheck
  · have hdfalse : D.direct = false := by
      cases hv : D.direct with
      | false => rfl
      | true => exact False.elim (hd hv)
    simp only [hdfalse, Bool.false_eq_true, ↓reduceIte] at hcheck
    have hall := of_decide_eq_true hcheck
    rcases hall with
      ⟨heigH, hrateH, hmu, heigRec2, heigRecM, hrateRec2, hrateRecM,
        hrateAnchor, hseparate⟩
    let eigRed := S.logReduction s hs
    let eigLog := dyadicLogValue eigRed
    let rateLog := dyadicLogValue D.rateReduction
    let eigT := dyadicLogTailBudget eigRed D.eigH
    let rateT := dyadicLogTailBudget D.rateReduction D.rateH
    let c := Q'.ofNat (c4 s)
    let B := S.eta * (c * c)
    have heigTail : ApproxTail eigLog D.K eigT :=
      dyadicLogValue_approxTail eigRed D.K D.eigH heigH heigRec2 heigRecM
    have hrateTail : ApproxTail rateLog D.K rateT :=
      dyadicLogValue_approxTail D.rateReduction D.K D.rateH hrateH
        hrateRec2 hrateRecM
    have hhalfmu : (0 : Q') < HalfPow.half * D.mu :=
      ExpNeg.half_mul_pos D.mu hmu
    obtain ⟨M, hM⟩ := S.estimate s hs (HalfPow.half * D.mu) hhalfmu
    let n := max M D.K
    have hMn : M <= n := Nat.le_max_left _ _
    have hKn : D.K <= n := Nat.le_max_right _ _
    have hsaddle := hM n hMn
    have hsaddle' : Q'.abs (eigLog.approx n + S.A * c) <=
        B + HalfPow.half * D.mu := hsaddle
    obtain ⟨heigUp, heigDown⟩ := heigTail n hKn
    obtain ⟨hrateUp, hrateDown⟩ := hrateTail n hKn
    have hrateAbs : Q'.abs (rateLog.approx n + S.A * c) <= D.delta :=
      abs_add_anchor_le_of_tail hrateUp hrateDown hrateAnchor
    have hdiffUpper : eigLog.approx n + -(rateLog.approx n) <=
        (B + HalfPow.half * D.mu) + D.delta :=
      sub_le_of_anchored_abs hsaddle' hrateAbs
    have hdiffLower : (B + D.delta) + D.mu <=
        eigLog.approx n + -(rateLog.approx n) := by
      have htailLower :
          ((eigLog.approx D.K + -(rateLog.approx D.K)) + -(eigT + rateT)) <=
            eigLog.approx n + -(rateLog.approx n) := by
        have heigLow : eigLog.approx D.K + -eigT <= eigLog.approx n :=
          Q'.sub_le_of_le_add
            (Q'.le_trans' _ _ _ heigDown
              (Q'.le_of_eqv (Q'.add_comm_eqv (eigLog.approx n) eigT)))
        have hsum :
            (eigLog.approx D.K + -eigT) + -(rateLog.approx D.K + rateT) <=
              eigLog.approx n + -(rateLog.approx n) :=
          Q'.add_le_add heigLow (Q'.neg_le_neg hrateUp)
        have hdesiredMid :
            ((eigLog.approx D.K + -(rateLog.approx D.K)) + -(eigT + rateT)).eqv
              ((eigLog.approx D.K + -eigT) + (-(rateLog.approx D.K) + -rateT)) :=
          Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (eigLog.approx D.K + -(rateLog.approx D.K))
            (-(eigT + rateT)) ((-eigT) + (-rateT))
            (Q'.neg_add_eqv eigT rateT))
          (Q'.add_swap_inner (eigLog.approx D.K) (-(rateLog.approx D.K))
            (-eigT) (-rateT))
        have hsumMid :
            ((eigLog.approx D.K + -eigT) + -(rateLog.approx D.K + rateT)).eqv
              ((eigLog.approx D.K + -eigT) +
                (-(rateLog.approx D.K) + -rateT)) :=
          Q'.add_eqv_congr_left (eigLog.approx D.K + -eigT)
            (-(rateLog.approx D.K + rateT))
            (-(rateLog.approx D.K) + -rateT)
            (Q'.neg_add_eqv (rateLog.approx D.K) rateT)
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hdesiredMid (Q'.eqv_symm hsumMid))) hsum
      exact Q'.le_trans' _ _ _ hseparate htailLower
    have hbad : (B + D.delta) + D.mu <=
        (B + D.delta) + HalfPow.half * D.mu := by
      refine Q'.le_trans' _ _ _ hdiffLower
        (Q'.le_trans' _ _ _ hdiffUpper ?_)
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (B + HalfPow.half * D.mu) D.delta
            (D.delta + 0) (Q'.eqv_symm (QPoly.q_add_zero_eqv D.delta)))
          (Q'.eqv_trans _ _ _
            (Q'.add_swap_inner B (HalfPow.half * D.mu) D.delta 0)
            (Q'.add_eqv_congr_left (B + D.delta) (HalfPow.half * D.mu + 0)
              (HalfPow.half * D.mu) (QPoly.q_add_zero_eqv _))))
    exact False.elim ((not_add_mu_le_add_half_mu (B + D.delta) D.mu hmu) hbad)

/-! ## 4. One finite reflected scan and the saddle-to-exp compiler -/

/-- A complete finite reflected certificate.  `data` contains untrusted route
and approximation choices; `checked` is the single kernel-verified scan. -/
structure FiniteSaddleToExpCertificate {N : Nat} {w : Q'} {p : Nat}
    {h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (S : FaithfulFiniteSaddleLogForm N w p h0') (weff : Q') : Type where
  data : (s : Nat) -> (hs : s <= 2 * N) -> ModeData S weff s hs
  checked : (List.range (2 * N + 1)).all (fun s =>
    if hs : s <= 2 * N then modeCheck S weff s hs (data s hs) else false) = true

/-- **The finite faithful saddle-to-exp certificate compiler.**  A successful
selected scan supplies the exact `FiniteExpShiftBridge`; no global canonical
evaluation and no general log/exp inverse is used. -/
def finiteExpShiftBridge_of_certificate {N : Nat} {w : Q'} {p : Nat} {weff : Q'}
    {h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (S : FaithfulFiniteSaddleLogForm N w p h0')
    (C : FiniteSaddleToExpCertificate S weff) :
    FiniteExpShiftBridge N w p weff h0' where
  rebasedBulkShift := fun s hs => by
    have hmem : s ∈ List.range (2 * N + 1) := List.mem_range.mpr (by omega)
    have hrow := List.all_eq_true.mp C.checked s hmem
    simp only [dif_pos hs] at hrow
    exact modeCheck_sound S weff s hs (C.data s hs) hrow

/-- Compile the checked saddle certificate through the already-proved positive-
exponent support theorem to the historical all-mode exponential bridge. -/
def expShiftBridge_of_certificate {N : Nat} {w : Q'} {p : Nat} {weff : Q'}
    {h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (hp : 0 < p) (hweff0 : (0 : Q') <= weff)
    (S : FaithfulFiniteSaddleLogForm N w p h0')
    (C : FiniteSaddleToExpCertificate S weff) :
    ExpShiftBridge N w p weff h0' :=
  expShiftBridge_of_finite_pos hp hweff0
    (finiteExpShiftBridge_of_certificate S C)

/-- **End-to-end canonical constructor.**  Physical window data plus one checked
finite saddle certificate builds the reviewed `CanonicalBulkControl`.  The
finite analytic field is filled by the reflected compiler, and its infinite
tail is available through `CanonicalBulkControl.expShiftBridge`. -/
def canonicalBulkControl_of_certificate
    {N : Nat} {w : Q'} {p : Nat} {weff : Q'}
    {h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (hN : 1 <= N) (hp : 0 < p)
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (hnc : (1 : Q') - w <= q112)
    (hweff0 : (0 : Q') <= weff) (hweff1 : weff <= (1 : Q'))
    (S : FaithfulFiniteSaddleLogForm N w p h0')
    (C : FiniteSaddleToExpCertificate S weff) :
    CanonicalBulkControl N w p where
  hN := hN
  hp := hp
  hw0 := hw0
  hw1 := hw1
  hnc := hnc
  denomPos := h0'
  weff := weff
  hweff0 := hweff0
  hweff1 := hweff1
  finiteShift := finiteExpShiftBridge_of_certificate S C

end YMGap.Continuum.ReflectedSaddleExpCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.ReflectedSaddleExpCertificate.dyadicLogValue_approxTail
#print axioms YMGap.Continuum.ReflectedSaddleExpCertificate.abs_add_anchor_le_of_tail
#print axioms YMGap.Continuum.ReflectedSaddleExpCertificate.sub_le_of_anchored_abs
#print axioms YMGap.Continuum.ReflectedSaddleExpCertificate.not_add_mu_le_add_half_mu
#print axioms YMGap.Continuum.ReflectedSaddleExpCertificate.modeCheck_sound
#print axioms YMGap.Continuum.ReflectedSaddleExpCertificate.finiteExpShiftBridge_of_certificate
#print axioms YMGap.Continuum.ReflectedSaddleExpCertificate.expShiftBridge_of_certificate
#print axioms YMGap.Continuum.ReflectedSaddleExpCertificate.canonicalBulkControl_of_certificate
