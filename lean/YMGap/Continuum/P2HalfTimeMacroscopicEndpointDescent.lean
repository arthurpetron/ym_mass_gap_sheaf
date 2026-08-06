/-
Track 11.7-fusion / R4ab -- macroscopic physical endpoint descent.

The first ten half-time shells were previously supplied by ten separate
physical coefficient comparisons.  The schedule identity

    25 * D_k = 12 * (N_k + 1)^2

actually proves much more: whenever `N_k + 1 <= 2*j`, reciprocal Bernoulli
forces `coeffW w_k j <= coeffW w_k (j-1)`.  Thus the reversed endpoint
coefficient string is monotone through every depth `m` with `2*m <= N_k`.

Together with the semantic all-depth endpoint compiler and a variable-depth
Bernoulli floor, this gives the complete half-time cell whenever
`2*m <= N_k` and `(m+1)*(2*N_k-m+2) <= D_k`.  The simpler condition
`5*(m+1) <= N_k+1` remains as a convenient corollary.  Thus the proof removes
a macroscopic family of endpoint channels at every physical cutoff without a
shell table.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeTenthShell

namespace YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent

set_option maxHeartbeats 360000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler
open YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler
open YMGap.Continuum.P2HalfTimeEndpointSupportCompiler
open YMGap.Continuum.P2HalfTimePenultimateShell
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

private theorem ofNat_le_ofNat {a b : Nat} (h : a <= b) :
    Q'.ofNat a <= Q'.ofNat b := by
  show Int.ofNat a * (1 : Int) <= Int.ofNat b * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr h

/-! ## 1. Schedule-wide upper-half coefficient descent -/

/-- The exact physical cutoff identity pays the reciprocal-Bernoulli step at
every coefficient index in the upper half of the cutoff. -/
private theorem physical_margin_cleared_of_half (r j : Nat)
    (hhalf : blockNcut (r + 4) + 1 <= 2 * j) :
    physicalWeightDen (r + 4) <= j * (2 * j + 1) := by
  let N := blockNcut (r + 4)
  let D := physicalWeightDen (r + 4)
  have hcoord := physicalWeightDen_cutoff_square (r + 4)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have hsquare : (N + 1) * (N + 1) <= (2 * j) * (2 * j) :=
    Nat.mul_le_mul hhalf hhalf
  have hscaledSquare :
      12 * ((N + 1) * (N + 1)) <= 12 * ((2 * j) * (2 * j)) :=
    Nat.mul_le_mul_left 12 hsquare
  have hpoly :
      12 * ((2 * j) * (2 * j)) <= 25 * (j * (2 * j + 1)) := by
    have hfour : (2 * j) * (2 * j) = 4 * (j * j) := by
      calc
        (2 * j) * (2 * j) = (2 * 2) * (j * j) := by ac_rfl
        _ = 4 * (j * j) := by rfl
    have h48le50 : 48 * (j * j) <= 50 * (j * j) :=
      Nat.mul_le_mul_right (j * j) (by decide : 48 <= 50)
    have htwice : j * (2 * j) = 2 * (j * j) := by ac_rfl
    have hinner : j * (2 * j) <= j * (2 * j + 1) :=
      Nat.mul_le_mul_left j (Nat.le_succ (2 * j))
    have h25inner : 25 * (j * (2 * j)) <=
        25 * (j * (2 * j + 1)) := Nat.mul_le_mul_left 25 hinner
    calc
      12 * ((2 * j) * (2 * j)) = 12 * (4 * (j * j)) := by rw [hfour]
      _ = 48 * (j * j) := by
        rw [← Nat.mul_assoc]
      _ <= 50 * (j * j) := h48le50
      _ = (25 * 2) * (j * j) := by rfl
      _ = 25 * (2 * (j * j)) := Nat.mul_assoc 25 2 (j * j)
      _ = 25 * (j * (2 * j)) := by rw [htwice]
      _ <= 25 * (j * (2 * j + 1)) := h25inner
  have hscaled : 25 * D <= 25 * (j * (2 * j + 1)) := by
    calc
      25 * D = 12 * ((N + 1) * (N + 1)) := by
        simpa only [Nat.mul_assoc] using hcoord
      _ <= 12 * ((2 * j) * (2 * j)) := hscaledSquare
      _ <= 25 * (j * (2 * j + 1)) := hpoly
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

/-- Physical heat coefficients descend at every index `j` in the upper half
of the cutoff.  This single theorem subsumes the separate endpoint descent
lemmas wherever `N+1 <= 2*j`. -/
theorem physical_coeff_descending_of_half (r j : Nat) (hj : 0 < j)
    (hhalf : blockNcut (r + 4) + 1 <= 2 * j) :
    coeffW (blockWeight (r + 4)) j <=
      coeffW (blockWeight (r + 4)) (j - 1) := by
  have hp0 : Q'.ofNat (j + 1) *
      qpow (blockWeight (r + 4)) (2 * j + 1) <= Q'.ofNat j :=
    physical_power_upper_step r j (2 * j + 1)
      (physical_margin_cleared_of_half r j hhalf)
  have hp : Q'.ofNat (j + 1) *
      qpow (blockWeight (r + 4)) (2 * j + 1) <=
        (1 : Q') * Q'.ofNat j :=
    Q'.le_trans' _ _ _ hp0 (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have hs := coeffW_succ_le_of_cross
    (w := blockWeight (r + 4)) (R := (1 : Q')) (j - 1)
    (blockWeight_nonneg (r + 4)) (by
      simpa only [show j - 1 + 1 = j by omega,
        show j - 1 + 2 = j + 1 by omega,
        show 2 * (j - 1) + 3 = 2 * j + 1 by omega] using hp)
  have hs' : coeffW (blockWeight (r + 4)) j <=
      (1 : Q') * coeffW (blockWeight (r + 4)) (j - 1) := by
    simpa only [show j - 1 + 1 = j by omega] using hs
  exact Q'.le_trans' _ _ _ hs' (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-! ## 2. The whole upper-half endpoint increment environment -/

private theorem physical_endpointCoefficient_mono_of_double_depth
    (r m n : Nat)
    (hdepth : 2 * m <= blockNcut (r + 4)) (hn : n < m) :
    endpointCoefficient (blockWeight (r + 4)) (blockNcut (r + 4)) n <=
      endpointCoefficient (blockWeight (r + 4))
        (blockNcut (r + 4)) (n + 1) := by
  let N := blockNcut (r + 4)
  have hj : 0 < N - n := by
    dsimp only [N]
    omega
  have hhalf : N + 1 <= 2 * (N - n) := by
    dsimp only [N]
    omega
  have hdesc := physical_coeff_descending_of_half r (N - n) hj (by
    simpa only [N] using hhalf)
  unfold endpointCoefficient
  simpa only [N, show N - (n + 1) = N - n - 1 by omega] using hdesc

/-- Every increment used by the semantic endpoint compiler is nonnegative
through depth `m <= N/2`.  The bound grows linearly with the physical cutoff;
there is no fixed shell table. -/
theorem physical_endpointIncrements_nonneg_of_double_depth
    (r m i : Nat) (hdepth : 2 * m <= blockNcut (r + 4)) (hi : i <= m) :
    (0 : Q') <= endpointIncrementEnvironment
      (blockWeight (r + 4)) (blockNcut (r + 4)) i := by
  cases i with
  | zero =>
      exact coeffW_nonneg (blockWeight_nonneg (r + 4))
        (blockNcut (r + 4))
  | succ n =>
      exact Q'.sub_nonneg_of_le
        (physical_endpointCoefficient_mono_of_double_depth r m n hdepth
          (by omega))

/-! ## 3. All-depth endpoint ratio on the macroscopic physical region -/

/-- The semantic endpoint compiler now applies at every physical depth in
the upper half of the cutoff.  `R` remains free so later heat-floor payment
can choose the sharpest convenient rational factor. -/
theorem physical_endpointRatio_of_double_depth
    (r R m : Nat) (hm : 0 < m) (hmR : m <= 2 * R)
    (hdepth : 2 * m <= blockNcut (r + 4)) :
    Q'.ofNat (R + 1) * endpointBoxExpr
        (blockWeight (r + 4)) (blockNcut (r + 4)) (m - 1) <=
      Q'.ofNat R * endpointBoxExpr
        (blockWeight (r + 4)) (blockNcut (r + 4)) m := by
  exact endpointRatio_allDepth_prefix R m hm hmR
    (endpointIncrementEnvironment
      (blockWeight (r + 4)) (blockNcut (r + 4)))
    (fun i hi =>
      physical_endpointIncrements_nonneg_of_double_depth r m i hdepth hi)

/-! ## 4. A variable-depth physical Bernoulli floor -/

private theorem bernoulli_lower_cover_of_cleared
    (A B n D : Nat) (hD : 0 < D) (hnD : n <= D)
    (hcleared : A * D <= B * (D - n)) :
    Q'.ofNat A <=
      Q'.ofNat B *
        ((1 : Q') - Q'.ofNat n * Q'.mkPos 1 D hD) := by
  show (Q'.ofNat A).num *
      ((Q'.ofNat B *
        ((1 : Q') +
          (-(Q'.ofNat n * Q'.mkPos 1 D hD)))).den : Int) <=
    (Q'.ofNat B *
      ((1 : Q') +
        (-(Q'.ofNat n * Q'.mkPos 1 D hD)))).num *
      (Q'.ofNat A).den
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.add_num_cast, Q'.add_den_cast, Q'.mkPos_num,
    Q'.mkPos_den, Q'.neg_den, neg_num_cast, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.one_mul, Int.mul_one]
  push_cast
  have hcasted : (A : Int) * (D : Int) <=
      (B : Int) * ((D - n : Nat) : Int) := by
    exact_mod_cast hcleared
  have hsub : ((D - n : Nat) : Int) = (D : Int) - (n : Int) := by
    omega
  rw [hsub] at hcasted
  exact hcasted

/-- Lower Bernoulli in the cross-multiplied form needed by the arbitrary-depth
endpoint ratio.  The only arithmetic premise is `(R+1)*n <= D_k`. -/
theorem physical_heat_cross_of_cover (r R n : Nat)
    (hcover : (R + 1) * n <= physicalWeightDen (r + 4)) :
    Q'.ofNat R <= qpow (blockWeight (r + 4)) n * Q'.ofNat (R + 1) := by
  let k := r + 4
  let D := physicalWeightDen k
  have hnScaled : n <= (R + 1) * n := by
    have h := Nat.mul_le_mul_right n (by omega : 1 <= R + 1)
    simpa only [Nat.one_mul] using h
  have hnD : n <= D := Nat.le_trans hnScaled (by
    simpa only [k, D] using hcover)
  have hsum : R * D + (R + 1) * n <= (R + 1) * D := by
    have hadd := Nat.add_le_add_left (by
      simpa only [k, D] using hcover) (R * D)
    calc
      R * D + (R + 1) * n <= R * D + D := hadd
      _ = (R + 1) * D := by rw [Nat.add_mul, Nat.one_mul]
  have hcleared : R * D <= (R + 1) * (D - n) := by
    have hsub := Nat.le_sub_of_add_le hsum
    rw [Nat.mul_sub_left_distrib]
    exact hsub
  have hcoverClosed : Q'.ofNat R <=
      Q'.ofNat (R + 1) *
        ((1 : Q') - Q'.ofNat n *
          Q'.mkPos 1 D (physicalWeightDen_pos k)) :=
    bernoulli_lower_cover_of_cleared R (R + 1) n D
      (physicalWeightDen_pos k) hnD hcleared
  have hmargin :
      ((1 : Q') - blockWeight k) ≈
        Q'.mkPos 1 D (physicalWeightDen_pos k) :=
    Q'.eqv_trans _ _ _ (one_sub_blockWeight_eqv_margin k)
      (blockMargin_eqv_closed k)
  have hcoverRat : Q'.ofNat R <=
      Q'.ofNat (R + 1) *
        ((1 : Q') - Q'.ofNat n * ((1 : Q') - blockWeight k)) := by
    have hinside :
        ((1 : Q') - Q'.ofNat n *
            Q'.mkPos 1 D (physicalWeightDen_pos k)) ≈
          ((1 : Q') - Q'.ofNat n * ((1 : Q') - blockWeight k)) := by
      exact Q'.add_eqv_congr_left 1 _ _
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _
            (Q'.eqv_symm hmargin)))
    exact Q'.le_trans' _ _ _ hcoverClosed
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat (R + 1)) _ _ hinside))
  have hbern := MovingCutoff.qpow_ge_bernoulli
    (blockWeight_nonneg k) (blockWeight_le_one k) n
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (R + 1)) hbern
    (HeatKernelRGStep.zero_le_ofNat (R + 1))
  have hordered : Q'.ofNat R <=
      Q'.ofNat (R + 1) * qpow (blockWeight k) n :=
    Q'.le_trans' _ _ _ hcoverRat hscaled
  exact Q'.le_trans' _ _ _ (by simpa only [k] using hordered)
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

/-- The schedule identity pays every endpoint depth in the explicit growing
region `5*(m+1) <= N_k+1`. -/
theorem physical_fifth_depth_cover (r m : Nat)
    (hfifth : 5 * (m + 1) <= blockNcut (r + 4) + 1) :
    (m + 1) * (2 * blockNcut (r + 4) - m + 2) <=
      physicalWeightDen (r + 4) := by
  let N := blockNcut (r + 4)
  let D := physicalWeightDen (r + 4)
  let M := m + 1
  let n := 2 * N - m + 2
  have hcoord := physicalWeightDen_cutoff_square (r + 4)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have hn : n <= 2 * (N + 1) := by
    dsimp only [n]
    omega
  have hupper0 := Nat.mul_le_mul_left (25 * M) hn
  have hupper : 25 * (M * n) <= 50 * (M * (N + 1)) := by
    calc
      25 * (M * n) = (25 * M) * n := by rw [Nat.mul_assoc]
      _ <= (25 * M) * (2 * (N + 1)) := hupper0
      _ = (25 * 2) * (M * (N + 1)) := by ac_rfl
      _ = 50 * (M * (N + 1)) := by rfl
  have hfifth' : 5 * M <= N + 1 := by
    simpa only [M, N] using hfifth
  have hmiddle0 := Nat.mul_le_mul_right (10 * (N + 1)) hfifth'
  have hmiddle : 50 * (M * (N + 1)) <=
      10 * ((N + 1) * (N + 1)) := by
    calc
      50 * (M * (N + 1)) = (5 * 10) * (M * (N + 1)) := by rfl
      _ = (5 * M) * (10 * (N + 1)) := by ac_rfl
      _ <= (N + 1) * (10 * (N + 1)) := hmiddle0
      _ = 10 * ((N + 1) * (N + 1)) := by ac_rfl
  have htenTwelve : 10 * ((N + 1) * (N + 1)) <=
      12 * ((N + 1) * (N + 1)) :=
    Nat.mul_le_mul_right ((N + 1) * (N + 1)) (by decide : 10 <= 12)
  have hscaled : 25 * (M * n) <= 25 * D := by
    calc
      25 * (M * n) <= 50 * (M * (N + 1)) := hupper
      _ <= 10 * ((N + 1) * (N + 1)) := hmiddle
      _ <= 12 * ((N + 1) * (N + 1)) := htenTwelve
      _ = 25 * D := by
        simpa only [Nat.mul_assoc] using hcoord.symm
  have hout := Nat.le_of_mul_le_mul_left hscaled (by decide)
  simpa only [M, n, N, D] using hout

theorem physical_heat_cross_fifth_depth (r m : Nat)
    (hfifth : 5 * (m + 1) <= blockNcut (r + 4) + 1) :
    Q'.ofNat m <=
      qpow (blockWeight (r + 4))
          (2 * blockNcut (r + 4) - m + 2) *
        Q'.ofNat (m + 1) :=
  physical_heat_cross_of_cover r m
    (2 * blockNcut (r + 4) - m + 2)
    (physical_fifth_depth_cover r m hfifth)

/-! ## 5. Complete half-time cells on the macroscopic endpoint band -/

theorem physical_endpointBox_le_heat_of_cover
    (r m : Nat) (hm : 0 < m)
    (hdepth : 2 * m <= blockNcut (r + 4))
    (hcover : (m + 1) * (2 * blockNcut (r + 4) - m + 2) <=
      physicalWeightDen (r + 4)) :
    endpointBoxExpr (blockWeight (r + 4)) (blockNcut (r + 4)) (m - 1) <=
      qpow (blockWeight (r + 4))
          (2 * blockNcut (r + 4) - m + 2) *
        endpointBoxExpr (blockWeight (r + 4)) (blockNcut (r + 4)) m := by
  let N := blockNcut (r + 4)
  let w := blockWeight (r + 4)
  let exponent := 2 * N - m + 2
  have hratio := physical_endpointRatio_of_double_depth r m m hm
    (by omega) (by simpa only [N] using hdepth)
  have hheat : Q'.ofNat m <= qpow w exponent * Q'.ofNat (m + 1) := by
    exact physical_heat_cross_of_cover r m exponent (by
      simpa only [N, exponent] using hcover)
  have hmN : m <= N := by omega
  have hsupport := boxSum_top_endpoint w N m hmN
  have hbox0 : (0 : Q') <= boxSum w N (2 * N - m) :=
    boxSum_nonneg (by simpa only [w] using blockWeight_nonneg (r + 4))
      N (2 * N - m)
  have hendpoint0 : (0 : Q') <= endpointBoxExpr w N m :=
    Q'.le_trans' _ _ _ hbox0 (Q'.le_of_eqv hsupport)
  have hheatScaled := Q'.mul_le_mul_of_nonneg_right _ _
    (endpointBoxExpr w N m) hheat hendpoint0
  have hreorder :
      (qpow w exponent * Q'.ofNat (m + 1)) * endpointBoxExpr w N m ≈
        Q'.ofNat (m + 1) *
          (qpow w exponent * endpointBoxExpr w N m) := by
    refine Q'.eqv_trans _
      ((Q'.ofNat (m + 1) * qpow w exponent) * endpointBoxExpr w N m) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hcancel : Q'.ofNat (m + 1) * endpointBoxExpr w N (m - 1) <=
      Q'.ofNat (m + 1) *
        (qpow w exponent * endpointBoxExpr w N m) :=
    Q'.le_trans' _ _ _ (by simpa only [N, w] using hratio)
      (Q'.le_trans' _ _ _ hheatScaled (Q'.le_of_eqv hreorder))
  exact Q'.le_of_mul_le_mul_left hcancel (Q'.ofNat_succ_pos m)

theorem physical_halfTime_box_of_cover
    (r m : Nat) (hm : 0 < m)
    (hdepth : 2 * m <= blockNcut (r + 4))
    (hcover : (m + 1) * (2 * blockNcut (r + 4) - m + 2) <=
      physicalWeightDen (r + 4)) :
    let N := blockNcut (r + 4)
    dimQ (2 * N - m) *
        boxSum (blockWeight (r + 4)) N (2 * N - m + 1) <=
      qpow (blockWeight (r + 4)) (2 * N - m + 2) *
        (dimQ (2 * N - m + 1) *
          boxSum (blockWeight (r + 4)) N (2 * N - m)) := by
  let N := blockNcut (r + 4)
  let w := blockWeight (r + 4)
  let exponent := 2 * N - m + 2
  have hmN : m <= N := by omega
  have hpredN : m - 1 <= N := by omega
  have hendpoint := physical_endpointBox_le_heat_of_cover r m hm hdepth hcover
  have ePrev0 := boxSum_top_endpoint w N (m - 1) hpredN
  have ePrev : boxSum w N (2 * N - m + 1) ≈ endpointBoxExpr w N (m - 1) := by
    simpa only [show 2 * N - (m - 1) = 2 * N - m + 1 by omega] using ePrev0
  have eNow := boxSum_top_endpoint w N m hmN
  have hbox : boxSum w N (2 * N - m + 1) <=
      qpow w exponent * boxSum w N (2 * N - m) := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv ePrev)
      (Q'.le_trans' _ _ _ (by simpa only [N, w, exponent] using hendpoint)
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm eNow))))
  let low := dimQ (2 * N - m)
  let high := dimQ (2 * N - m + 1)
  have hboxLeft0 : (0 : Q') <= boxSum w N (2 * N - m + 1) :=
    boxSum_nonneg (by simpa only [w] using blockWeight_nonneg (r + 4))
      N (2 * N - m + 1)
  have hdim : low <= high := by
    have hnat : 2 * N - m + 1 <= 2 * N - m + 1 + 1 := Nat.le_succ _
    simpa only [low, high, dimQ, Nat.add_assoc] using ofNat_le_ofNat hnat
  have hdimScaled : low * boxSum w N (2 * N - m + 1) <=
      high * boxSum w N (2 * N - m + 1) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdim hboxLeft0
  have hhigh0 : (0 : Q') <= high := by
    unfold high dimQ
    exact HeatKernelRGStep.zero_le_ofNat _
  have hratioScaled : high * boxSum w N (2 * N - m + 1) <=
      high * (qpow w exponent * boxSum w N (2 * N - m)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ high hbox hhigh0
  have hreorder :
      high * (qpow w exponent * boxSum w N (2 * N - m)) ≈
        qpow w exponent * (high * boxSum w N (2 * N - m)) := by
    refine Q'.eqv_trans _
      ((high * qpow w exponent) * boxSum w N (2 * N - m)) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _
      ((qpow w exponent * high) * boxSum w N (2 * N - m)) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  change low * boxSum w N (2 * N - m + 1) <=
    qpow w exponent * (high * boxSum w N (2 * N - m))
  exact Q'.le_trans' _ _ _ hdimScaled
    (Q'.le_trans' _ _ _ hratioScaled (Q'.le_of_eqv hreorder))

theorem physical_halfTime_lineSum_of_cover
    (r m : Nat) (hm : 0 < m)
    (hdepth : 2 * m <= blockNcut (r + 4))
    (hcover : (m + 1) * (2 * blockNcut (r + 4) - m + 2) <=
      physicalWeightDen (r + 4)) :
    let N := blockNcut (r + 4)
    dimQ (2 * N - m) *
        lineSum (lagCorr (blockWeight (r + 4)) N) (2 * N - m + 1) <=
      qpow (blockWeight (r + 4)) (2 * N - m + 2) *
        (dimQ (2 * N - m + 1) *
          lineSum (lagCorr (blockWeight (r + 4)) N) (2 * N - m)) := by
  let N := blockNcut (r + 4)
  let w := blockWeight (r + 4)
  have hbox := physical_halfTime_box_of_cover r m hm hdepth hcover
  have eleft :
      dimQ (2 * N - m) * lineSum (lagCorr w N) (2 * N - m + 1) ≈
        dimQ (2 * N - m) * boxSum w N (2 * N - m + 1) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (2 * N - m + 1)))
  have eright :
      qpow w (2 * N - m + 2) *
          (dimQ (2 * N - m + 1) * boxSum w N (2 * N - m)) ≈
        qpow w (2 * N - m + 2) *
          (dimQ (2 * N - m + 1) * lineSum (lagCorr w N) (2 * N - m)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N (2 * N - m)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ (by simpa only [N, w] using hbox)
      (Q'.le_of_eqv eright))

theorem physical_halfTime_lineSum_of_cover_from_four
    (k m : Nat) (hk : 4 <= k) (hm : 0 < m)
    (hdepth : 2 * m <= blockNcut k)
    (hcover : (m + 1) * (2 * blockNcut k - m + 2) <=
      physicalWeightDen k) :
    let N := blockNcut k
    dimQ (2 * N - m) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - m + 1) <=
      qpow (blockWeight k) (2 * N - m + 2) *
        (dimQ (2 * N - m + 1) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - m)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using
    physical_halfTime_lineSum_of_cover r m hm (by
      simpa only [Nat.add_comm] using hdepth) (by
      simpa only [Nat.add_comm] using hcover)

/-! ## 6. Simple one-fifth corollaries -/

theorem physical_endpointBox_le_heat_fifth_depth
    (r m : Nat) (hm : 0 < m)
    (hfifth : 5 * (m + 1) <= blockNcut (r + 4) + 1) :
    endpointBoxExpr (blockWeight (r + 4)) (blockNcut (r + 4)) (m - 1) <=
      qpow (blockWeight (r + 4))
          (2 * blockNcut (r + 4) - m + 2) *
        endpointBoxExpr (blockWeight (r + 4)) (blockNcut (r + 4)) m := by
  apply physical_endpointBox_le_heat_of_cover r m hm
  · omega
  · exact physical_fifth_depth_cover r m hfifth

theorem physical_halfTime_box_fifth_depth
    (r m : Nat) (hm : 0 < m)
    (hfifth : 5 * (m + 1) <= blockNcut (r + 4) + 1) :
    let N := blockNcut (r + 4)
    dimQ (2 * N - m) *
        boxSum (blockWeight (r + 4)) N (2 * N - m + 1) <=
      qpow (blockWeight (r + 4)) (2 * N - m + 2) *
        (dimQ (2 * N - m + 1) *
          boxSum (blockWeight (r + 4)) N (2 * N - m)) := by
  apply physical_halfTime_box_of_cover r m hm
  · omega
  · exact physical_fifth_depth_cover r m hfifth

theorem physical_halfTime_lineSum_fifth_depth
    (r m : Nat) (hm : 0 < m)
    (hfifth : 5 * (m + 1) <= blockNcut (r + 4) + 1) :
    let N := blockNcut (r + 4)
    dimQ (2 * N - m) *
        lineSum (lagCorr (blockWeight (r + 4)) N) (2 * N - m + 1) <=
      qpow (blockWeight (r + 4)) (2 * N - m + 2) *
        (dimQ (2 * N - m + 1) *
          lineSum (lagCorr (blockWeight (r + 4)) N) (2 * N - m)) := by
  apply physical_halfTime_lineSum_of_cover r m hm
  · omega
  · exact physical_fifth_depth_cover r m hfifth

theorem physical_halfTime_lineSum_fifth_depth_from_four
    (k m : Nat) (hk : 4 <= k) (hm : 0 < m)
    (hfifth : 5 * (m + 1) <= blockNcut k + 1) :
    let N := blockNcut k
    dimQ (2 * N - m) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - m + 1) <=
      qpow (blockWeight k) (2 * N - m + 2) *
        (dimQ (2 * N - m + 1) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - m)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using
    physical_halfTime_lineSum_fifth_depth r m hm (by
      simpa only [Nat.add_comm] using hfifth)

end YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_coeff_descending_of_half
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_endpointIncrements_nonneg_of_double_depth
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_endpointRatio_of_double_depth
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_heat_cross_of_cover
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_fifth_depth_cover
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_endpointBox_le_heat_of_cover
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_halfTime_box_of_cover
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_halfTime_lineSum_of_cover
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_halfTime_lineSum_of_cover_from_four
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_endpointBox_le_heat_fifth_depth
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_halfTime_box_fifth_depth
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_halfTime_lineSum_fifth_depth
#print axioms YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent.physical_halfTime_lineSum_fifth_depth_from_four
