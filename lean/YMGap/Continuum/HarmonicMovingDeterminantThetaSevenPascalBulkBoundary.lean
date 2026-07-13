/-
The exact sign certificate for the seven-coordinate boundary payment in the
bulk Pascal step.

After the first seven coordinates are separated from the old row, the
remaining signed convolution has seven fixed polynomial weights.  Clearing
the adjacent-binomial denominators turns it into a two-variable polynomial.
On the physical cone `m >= 3`, `k >= 1`, that polynomial has a manifestly
nonnegative expansion in `u = m - 3` and `v = k - 1`.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCoreBoundaryBridge
import YMGap.Continuum.RingNormaliserStream

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBulkBoundary

open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence

/-- The seven signed weights left after expanding the appended cell into the
old Pascal row. -/
def sevenBulkBoundaryWeight : Nat → Int → Int
  | 0, m => -22680 * m * (m + 1)
  | 1, m => 11340 * m * (m + 1) * (2 * m - 5)
  | 2, m => 945 * m * (m + 1) * (50 * m - 47)
  | 3, m => -1890 * m * (m + 1) *
      (4 * m * m * m - 4 * m * m - 15 * m + 6)
  | 4, m => -4347 * m * (m - 1) * (m + 1) *
      (2 * m - 1) * (2 * m + 1)
  | 5, m => 18 * m * (m - 1) * (m + 1) *
      (2 * m - 1) * (2 * m + 1) * (52 * m * m - 285)
  | 6, m => m * (m - 1) * (m + 1) *
      (2 * m - 1) * (2 * m + 1) *
      (80 * m * m * m * m + 2218 * m * m - 5679)
  | _, _ => 0

/-- Difference between the exact boundary formula and the signed bulk
weight.  Only the first four coordinates are changed by the appended-cell
payment. -/
def sevenBulkBoundaryAdjustment : Nat → Int → Int
  | 0, m => 5670 * 8 * m * m
  | 1, m => 5670 * 12 * m * m
  | 2, m => -(5670 * m * m)
  | 3, m => -(5670 * 6 * m * m)
  | _, _ => 0

/-- Falling product `x (x-1) ... (x-s+1)`. -/
def bulkFalling (x : Int) : Nat → Int
  | 0 => 1
  | s + 1 => bulkFalling x s * (x - s)

/-- The tail of `(k+1)...(k+6)` remaining after its first `s` factors. -/
def bulkRisingTailSix (k : Int) : Nat → Int
  | 0 => (k + 1) * (k + 2) * (k + 3) * (k + 4) * (k + 5) * (k + 6)
  | 1 => (k + 2) * (k + 3) * (k + 4) * (k + 5) * (k + 6)
  | 2 => (k + 3) * (k + 4) * (k + 5) * (k + 6)
  | 3 => (k + 4) * (k + 5) * (k + 6)
  | 4 => (k + 5) * (k + 6)
  | 5 => k + 6
  | 6 => 1
  | _ => 0

def bulkBoundaryTerm (j : Nat) (m k : Int) : Int :=
  sevenBulkBoundaryWeight j m *
    bulkFalling (4 * m + 2 - k) (6 - j) *
    bulkRisingTailSix k (6 - j)

/-- Cleared polynomial associated to the seven signed binomial weights. -/
def sevenBulkBoundaryCleared (m k : Int) : Int :=
  bulkBoundaryTerm 0 m k + (bulkBoundaryTerm 1 m k +
  (bulkBoundaryTerm 2 m k + (bulkBoundaryTerm 3 m k +
  (bulkBoundaryTerm 4 m k + (bulkBoundaryTerm 5 m k +
  bulkBoundaryTerm 6 m k)))))

private def boundaryBasePositive (v : Int) : Int :=
  56700 *
    (intPolyEval v [1381030, 9580, 0, 836571, 102017, 7413, 221] +
      83162 * ((v - 1) * (v - 1)))

private def boundaryPositiveCoeffs (v : Int) : List Int :=
  [boundaryBasePositive v,
   intPolyEval v
    [193972605120, 86271769656, 97258993398, 127018308465,
      16788445875, 1206381519, 35957727],
   intPolyEval v
    [221248434960, 222452073900, 198492645996, 149901743259,
      20856279717, 1493932761, 44492607],
   intPolyEval v
    [157978558080, 224884547676, 181317688330, 101707376076,
      14632371028, 1051366608, 31361962],
   intPolyEval v
    [75041724240, 124597468296, 93940077420, 43561729890,
      6417829530, 465664374, 13990410],
   intPolyEval v
    [23866284960, 41915780424, 30009687792, 12198625110,
      1834500570, 135595026, 4141158],
   intPolyEval v
    [4993047360, 8811119520, 6047115984, 2236534776,
      344250648, 26233704, 825048],
   intPolyEval v
    [657417600, 1134190944, 751910880, 260109144,
      41331432, 3297672, 108408],
   intPolyEval v
    [49351680, 82059264, 52986240, 17570880, 2923200, 248256, 8640],
   intPolyEval v
    [1612800, 2568960, 1633280, 532800, 94400, 8640, 320]]

/-- Manifestly nonnegative expansion in `u=m-3` and `v=k-1`. -/
def sevenBulkBoundaryPositive (u v : Int) : Int :=
  intPolyEval u (boundaryPositiveCoeffs v)

private abbrev PE := IntRingNormaliser.PolyExpr
private def pc (z : Int) : PE := .const z
private def vx : PE := .var 0
private def vy : PE := .var 1
private def pa (x y : PE) : PE := .add x y
private def pm (x y : PE) : PE := .mul x y
private def pn (x : PE) : PE := .neg x
private def ps (x y : PE) : PE := pa x (pn y)

private def pWeight : Nat → PE → PE
  | 0, m => pm (pm (pc (-22680)) m) (pa m (pc 1))
  | 1, m => pm (pm (pm (pc 11340) m) (pa m (pc 1)))
      (ps (pm (pc 2) m) (pc 5))
  | 2, m => pm (pm (pm (pc 945) m) (pa m (pc 1)))
      (ps (pm (pc 50) m) (pc 47))
  | 3, m => pm (pm (pm (pc (-1890)) m) (pa m (pc 1)))
      (pa (ps (ps (pm (pc 4) (pm m (pm m m)))
        (pm (pc 4) (pm m m))) (pm (pc 15) m)) (pc 6))
  | 4, m => pm (pm (pm (pm (pm (pc (-4347)) m) (ps m (pc 1)))
      (pa m (pc 1))) (ps (pm (pc 2) m) (pc 1)))
      (pa (pm (pc 2) m) (pc 1))
  | 5, m => pm (pm (pm (pm (pm (pm (pc 18) m) (ps m (pc 1)))
      (pa m (pc 1))) (ps (pm (pc 2) m) (pc 1)))
      (pa (pm (pc 2) m) (pc 1)))
      (ps (pm (pc 52) (pm m m)) (pc 285))
  | 6, m =>
      let front := pm (pm (pm (pm m (ps m (pc 1))) (pa m (pc 1)))
        (ps (pm (pc 2) m) (pc 1))) (pa (pm (pc 2) m) (pc 1))
      let back := ps
        (pa (pm (pc 80) (pm m (pm m (pm m m))))
          (pm (pc 2218) (pm m m)))
        (pc 5679)
      pm front back
  | _, _ => pc 0

private def pAdjustment : Nat → PE → PE
  | 0, m => pm (pm (pc 45360) m) m
  | 1, m => pm (pm (pc 68040) m) m
  | 2, m => pm (pm (pc (-5670)) m) m
  | 3, m => pm (pm (pc (-34020)) m) m
  | _, _ => pc 0

private theorem bulk_cases_le_six {j : Nat} (hj : j ≤ 6) :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by
  omega

set_option maxRecDepth 100000 in
private theorem formula_weight_adjustment_normal (j : Nat) (hj : j ≤ 6) :
    RingNormaliser.normalize (pFormula j vx) =
      RingNormaliser.normalize (pa (pWeight j vx) (pAdjustment j vx)) := by
  rcases bulk_cases_le_six hj with h | h | h | h | h | h | h <;>
    subst j <;> decide

/-- Exact coordinatewise relation used to cancel the nonpositive part of
the appended cell. -/
theorem sevenBoundaryScaledFormula_eq_weight_adjustment
    (j : Nat) (m : Int) (hj : j ≤ 6) :
    sevenBoundaryScaledFormula j m =
      sevenBulkBoundaryWeight j m + sevenBulkBoundaryAdjustment j m := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq _ _
    (formula_weight_adjustment_normal j hj) (fun _ => m)
  rcases bulk_cases_le_six hj with h0 | h1 | h2 | h3 | h4 | h5 | h6 <;>
    subst j <;>
    simpa [sevenBoundaryScaledFormula, sevenBulkBoundaryWeight,
      sevenBulkBoundaryAdjustment, intPolyEval, pFormula, pWeight,
      pAdjustment,
      HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula.pIntPoly,
      HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula.pc,
      HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula.pa,
      HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula.pm,
      pc, vx, pa, pm, pn, ps, IntRingNormaliser.eval,
      Int.sub_eq_add_neg, Int.neg_mul, Int.mul_assoc] using h

private def pFalling (x : PE) : Nat → PE
  | 0 => pc 1
  | s + 1 => pm (pFalling x s) (ps x (pc s))

private def pRisingTailSix (k : PE) : Nat → PE
  | 0 => pm (pm (pm (pm (pm (pa k (pc 1)) (pa k (pc 2)))
      (pa k (pc 3))) (pa k (pc 4))) (pa k (pc 5))) (pa k (pc 6))
  | 1 => pm (pm (pm (pm (pa k (pc 2)) (pa k (pc 3)))
      (pa k (pc 4))) (pa k (pc 5))) (pa k (pc 6))
  | 2 => pm (pm (pm (pa k (pc 3)) (pa k (pc 4)))
      (pa k (pc 5))) (pa k (pc 6))
  | 3 => pm (pm (pa k (pc 4)) (pa k (pc 5))) (pa k (pc 6))
  | 4 => pm (pa k (pc 5)) (pa k (pc 6))
  | 5 => pa k (pc 6)
  | 6 => pc 1
  | _ => pc 0

private def pBoundaryTerm (j : Nat) (m k : PE) : PE :=
  let q := ps (pa (pm (pc 4) m) (pc 2)) k
  pm (pm (pWeight j m) (pFalling q (6 - j)))
    (pRisingTailSix k (6 - j))

private def pCleared (m k : PE) : PE :=
  pa (pBoundaryTerm 0 m k) <| pa (pBoundaryTerm 1 m k) <|
  pa (pBoundaryTerm 2 m k) <| pa (pBoundaryTerm 3 m k) <|
  pa (pBoundaryTerm 4 m k) (pa (pBoundaryTerm 5 m k)
    (pBoundaryTerm 6 m k))

private def pIntPoly (x : PE) : List Int → PE
  | [] => pc 0
  | a :: as => pa (pc a) (pm x (pIntPoly x as))

private def pBasePositive (v : PE) : PE :=
  pm (pc 56700)
    (pa (pIntPoly v [1381030, 9580, 0, 836571, 102017, 7413, 221])
      (pm (pc 83162) (pm (ps v (pc 1)) (ps v (pc 1)))))

private def pPositiveCoeffs (v : PE) : List PE :=
  [pBasePositive v,
   pIntPoly v [193972605120, 86271769656, 97258993398, 127018308465,
      16788445875, 1206381519, 35957727],
   pIntPoly v [221248434960, 222452073900, 198492645996, 149901743259,
      20856279717, 1493932761, 44492607],
   pIntPoly v [157978558080, 224884547676, 181317688330, 101707376076,
      14632371028, 1051366608, 31361962],
   pIntPoly v [75041724240, 124597468296, 93940077420, 43561729890,
      6417829530, 465664374, 13990410],
   pIntPoly v [23866284960, 41915780424, 30009687792, 12198625110,
      1834500570, 135595026, 4141158],
   pIntPoly v [4993047360, 8811119520, 6047115984, 2236534776,
      344250648, 26233704, 825048],
   pIntPoly v [657417600, 1134190944, 751910880, 260109144,
      41331432, 3297672, 108408],
   pIntPoly v [49351680, 82059264, 52986240, 17570880, 2923200, 248256, 8640],
   pIntPoly v [1612800, 2568960, 1633280, 532800, 94400, 8640, 320]]

private def pPolyEvalExpr (x : PE) : List PE → PE
  | [] => pc 0
  | a :: as => pa a (pm x (pPolyEvalExpr x as))

private def pPositive (u v : PE) : PE :=
  pPolyEvalExpr u (pPositiveCoeffs v)

private def groupRows01 : List (List Int) :=
  [[-189145756800, 150486245280, -45244830960, 6842102400, -559288800, 23677920, -408240],
   [-333988492320, 316899361800, -95730749100, 13565815200, -993043800, 36129240, -510300],
   [-170642687040, 294751525320, -91110697020, 11723745600, -724059000, 20434680, -192780],
   [44391201120, 164496089520, -51095068920, 5613753600, -267397200, 5034960, -22680],
   [88763351040, 63455374080, -18217936800, 1552672800, -49442400, 453600],
   [43352910720, 17905224960, -4080585600, 232243200, -3628800],
   [10620771840, 3548966400, -522547200, 14515200],
   [1341204480, 429649920, -29030400],
   [69672960, 23224320]]

private def groupRows23 : List (List Int) :=
  [[572107536000, -104735877120, -26913380760, 4511902500, 192156300, -52016580, 1916460],
   [1089943918560, -261037773360, -62449551990, 9540203085, 528881535, -104892165, 3249855],
   [765046976400, -314715236220, -66011587740, 8746943625, 635084415, -88736445, 2129085],
   [175177054080, -238500457020, -42787700550, 4464461610, 425856690, -40421430, 691740],
   [-64551498480, -120640416120, -19075868280, 1314139680, 172927440, -10531080, 113400],
   [-53128716480, -40309723440, -5996372760, 186701760, 42804720, -1496880, 7560],
   [-14670694080, -8471826720, -1264999680, -4233600, 5987520, -90720],
   [-1930521600, -1009048320, -158094720, -5080320, 362880],
   [-101606400, -51770880, -8709120, -483840]]

private def groupRows45 : List (List Int) :=
  [[-387844329600, -194653458720, -12144958560, 7040439000, 1006425000, -22249080, -6418440],
   [-810405116640, -365291046648, 3862430136, 21844210410, 2712017430, -55689282, -16071966],
   [-673521473520, -236023737084, 51435145044, 30203126289, 3364330167, -46867005, -17040051],
   [-266258618640, -27119438388, 67932565848, 24015320721, 2494282203, -9687573, -9916011],
   [-36351594720, 42914888856, 42945349860, 11893897260, 1191461040, 8698284, -3420900],
   [9281744640, 25517727648, 15416962344, 3732065820, 369471060, 6590052, -699804],
   [4488462720, 6479301024, 3222320976, 721639296, 71679888, 1925280, -78624],
   [681488640, 813233088, 366612192, 78456384, 7883712, 269568, -3744],
   [37739520, 41243904, 17596800, 3669120, 374400, 14976]]

private def groupRows6 : List (List Int) :=
  [[87902236800, 140015705760, 89018455680, 29039131800, 5145071400, 470904840, 17440920],
   [248422295520, 395701227864, 251576864352, 82068079770, 14540590710, 1330833726, 49290138],
   [300365619120, 478439521884, 304179785712, 99227927745, 17580924135, 1609101531, 59596353],
   [204668921520, 326008353564, 207267891952, 67613840145, 11979629335, 1096440651, 40608913],
   [87181466400, 138867621480, 88288532640, 28801020150, 5102883450, 467043570, 17297910],
   [24360346080, 38802551256, 24669683808, 8047614330, 1425853590, 130501854, 4833402],
   [4554506880, 7254678816, 4612341888, 1504613880, 266583240, 24399144, 903672],
   [565246080, 900356256, 572423808, 186733080, 33084840, 3028104, 112152],
   [43545600, 69361920, 44098560, 14385600, 2548800, 233280, 8640],
   [1612800, 2568960, 1633280, 532800, 94400, 8640, 320]]

private def biPolyEval (u v : Int) (rows : List (List Int)) : Int :=
  intPolyEval u (rows.map (intPolyEval v))

private def pBiPoly (u v : PE) (rows : List (List Int)) : PE :=
  pPolyEvalExpr u (rows.map (pIntPoly v))

private def pShiftedDifference : PE :=
  ps (pCleared (pa vx (pc 3)) (pa vy (pc 1))) (pPositive vx vy)

private theorem pShiftedDifference_degree :
    RingNormaliserStream.degBound pShiftedDifference ≤ 17 := by decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem pShiftedDifference_grid :
    RingNormaliserStream.gridCheck2B pShiftedDifference 17 = true := by decide

private theorem pShiftedDifference_zero (u v : Int) :
    IntRingNormaliser.eval
      (fun i => if i = 0 then u else if i = 1 then v else 0)
      pShiftedDifference = 0 := by
  have hq := RingNormaliserStream.poly_identity_of_grid2
    pShiftedDifference 17 pShiftedDifference_degree
    (RingNormaliserStream.grid_of_check pShiftedDifference 17
      pShiftedDifference_grid)
    (YMGap.Constructive.Q'.ofInt u) (YMGap.Constructive.Q'.ofInt v)
  let rho : Nat → Int :=
    fun i => if i = 0 then u else if i = 1 then v else 0
  have henv :
      (fun i => YMGap.Constructive.Q'.ofInt (rho i)) =
        RingNormaliserStream.env2
          (YMGap.Constructive.Q'.ofInt u)
          (YMGap.Constructive.Q'.ofInt v) := by
    funext i
    by_cases h0 : i = 0
    · subst i
      rfl
    · by_cases h1 : i = 1
      · subst i
        rfl
      · simpa [rho, RingNormaliserStream.env2, h0, h1] using
          RingNormaliser.ofInt_zero
  have hr := IntRingNormaliser.ring_eval_ofInt rho pShiftedDifference
  rw [henv] at hr
  have hzq :
      (YMGap.Constructive.Q'.ofInt
        (IntRingNormaliser.eval rho pShiftedDifference)).eqv 0 :=
    YMGap.Constructive.Q'.eqv_trans _ _ _
      (YMGap.Constructive.Q'.eqv_symm hr) hq
  have hz : IntRingNormaliser.eval rho pShiftedDifference = 0 := by
    have hz' := hzq
    change IntRingNormaliser.eval rho pShiftedDifference * (1 : Int) =
      (0 : Int) * (1 : Int) at hz'
    omega
  exact hz

set_option maxHeartbeats 2000000 in
/- Exact identity behind the positive bulk-boundary certificate. -/
theorem sevenBulkBoundaryCleared_shift (u v : Int) :
    sevenBulkBoundaryCleared (u + 3) (v + 1) =
      sevenBulkBoundaryPositive u v := by
  have h := pShiftedDifference_zero u v
  change IntRingNormaliser.eval
      (fun i => if i = 0 then u else if i = 1 then v else 0)
      (pCleared (pa vx (pc 3)) (pa vy (pc 1))) +
    -IntRingNormaliser.eval
      (fun i => if i = 0 then u else if i = 1 then v else 0)
      (pPositive vx vy) = 0 at h
  have hL : IntRingNormaliser.eval
      (fun i => if i = 0 then u else if i = 1 then v else 0)
      (pCleared (pa vx (pc 3)) (pa vy (pc 1))) =
        sevenBulkBoundaryCleared (u + 3) (v + 1) := by
    simp [pCleared, pBoundaryTerm, pWeight, pFalling, pRisingTailSix,
      pc, vx, vy, pa, pm, pn, ps, IntRingNormaliser.eval,
      sevenBulkBoundaryCleared, bulkBoundaryTerm, sevenBulkBoundaryWeight,
      bulkFalling, bulkRisingTailSix, Int.sub_eq_add_neg, Int.mul_assoc]
  have hR : IntRingNormaliser.eval
      (fun i => if i = 0 then u else if i = 1 then v else 0)
      (pPositive vx vy) = sevenBulkBoundaryPositive u v := by
    simp [pPositive, pPositiveCoeffs, pBasePositive, pPolyEvalExpr,
      pIntPoly, pc, vx, vy, pa, pm, pn, ps, IntRingNormaliser.eval,
      sevenBulkBoundaryPositive, boundaryPositiveCoeffs,
      boundaryBasePositive, intPolyEval, Int.sub_eq_add_neg, Int.mul_assoc]
  rw [hL, hR] at h
  omega

private theorem intPolyEval_nat_nonnegative {x : Int} (hx : 0 ≤ x) :
    ∀ cs : List Nat, 0 ≤ intPolyEval x (cs.map Int.ofNat)
  | [] => by simp [intPolyEval]
  | a :: as => by
      simp only [List.map, intPolyEval]
      exact Int.add_nonneg (Int.natCast_nonneg a)
        (Int.mul_nonneg hx (intPolyEval_nat_nonnegative hx as))

private theorem boundaryBasePositive_nonnegative {v : Int} (hv : 0 ≤ v) :
    0 ≤ boundaryBasePositive v := by
  have hp : 0 ≤ intPolyEval v
      [1381030, 9580, 0, 836571, 102017, 7413, 221] := by
    simpa using intPolyEval_nat_nonnegative hv
      [1381030, 9580, 0, 836571, 102017, 7413, 221]
  have hs : 0 ≤ (v - 1) * (v - 1) := by
    by_cases h : 0 ≤ v - 1
    · exact Int.mul_nonneg h h
    · have h' : v - 1 ≤ 0 := by omega
      exact Int.mul_nonneg_of_nonpos_of_nonpos h' h'
  exact Int.mul_nonneg (by decide)
    (Int.add_nonneg hp (Int.mul_nonneg (by decide) hs))

private theorem boundaryPositiveCoeffs_nonnegative {v : Int} (hv : 0 ≤ v) :
    ∀ z ∈ boundaryPositiveCoeffs v, 0 ≤ z := by
  intro z hz
  simp [boundaryPositiveCoeffs] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h <;> subst z
  · exact boundaryBasePositive_nonnegative hv
  all_goals
    first
    | simpa using intPolyEval_nat_nonnegative hv
        [193972605120, 86271769656, 97258993398, 127018308465,
          16788445875, 1206381519, 35957727]
    | simpa using intPolyEval_nat_nonnegative hv
        [221248434960, 222452073900, 198492645996, 149901743259,
          20856279717, 1493932761, 44492607]
    | simpa using intPolyEval_nat_nonnegative hv
        [157978558080, 224884547676, 181317688330, 101707376076,
          14632371028, 1051366608, 31361962]
    | simpa using intPolyEval_nat_nonnegative hv
        [75041724240, 124597468296, 93940077420, 43561729890,
          6417829530, 465664374, 13990410]
    | simpa using intPolyEval_nat_nonnegative hv
        [23866284960, 41915780424, 30009687792, 12198625110,
          1834500570, 135595026, 4141158]
    | simpa using intPolyEval_nat_nonnegative hv
        [4993047360, 8811119520, 6047115984, 2236534776,
          344250648, 26233704, 825048]
    | simpa using intPolyEval_nat_nonnegative hv
        [657417600, 1134190944, 751910880, 260109144,
          41331432, 3297672, 108408]
    | simpa using intPolyEval_nat_nonnegative hv
        [49351680, 82059264, 52986240, 17570880, 2923200, 248256, 8640]
    | simpa using intPolyEval_nat_nonnegative hv
        [1612800, 2568960, 1633280, 532800, 94400, 8640, 320]

private theorem intPolyEval_nonnegative_of_mem {x : Int} (hx : 0 ≤ x) :
    ∀ cs : List Int, (∀ z ∈ cs, 0 ≤ z) → 0 ≤ intPolyEval x cs
  | [], _ => by simp [intPolyEval]
  | a :: as, h => by
      simp only [intPolyEval]
      exact Int.add_nonneg (h a (by simp))
        (Int.mul_nonneg hx (intPolyEval_nonnegative_of_mem hx as
          (fun z hz => h z (by simp [hz]))))

/-- The cleared boundary polynomial is nonnegative throughout the physical
bulk cone. -/
theorem sevenBulkBoundaryCleared_nonnegative (m k : Nat)
    (hm : 3 ≤ m) (hk : 1 ≤ k) :
    0 ≤ sevenBulkBoundaryCleared (m : Int) (k : Int) := by
  let u := m - 3
  let v := k - 1
  have hm' : (m : Int) = (u : Int) + 3 := by
    dsimp only [u]
    omega
  have hk' : (k : Int) = (v : Int) + 1 := by
    dsimp only [v]
    omega
  rw [hm', hk', sevenBulkBoundaryCleared_shift]
  apply intPolyEval_nonnegative_of_mem (Int.natCast_nonneg u)
  exact boundaryPositiveCoeffs_nonnegative (Int.natCast_nonneg v)

private def pWeightSixBack (m : PE) : PE :=
  ps (pa (pm (pc 80) (pm m (pm m (pm m m))))
      (pm (pc 2218) (pm m m)))
    (pc 5679)

set_option maxRecDepth 100000 in
private theorem formulaSix_weight_normal :
    RingNormaliser.normalize (pFormula 6 vx) =
      RingNormaliser.normalize (pWeight 6 vx) := by decide

set_option maxRecDepth 100000 in
private theorem weightSixBack_shift_normal :
    RingNormaliser.normalize (pWeightSixBack (pa vx (pc 3))) =
      RingNormaliser.normalize
        (pIntPoly vx [20763, 21948, 6538, 960, 80]) := by decide

private theorem formulaSix_eq_weight (m : Int) :
    sevenBoundaryScaledFormula 6 m = sevenBulkBoundaryWeight 6 m := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq _ _
    formulaSix_weight_normal (fun _ => m)
  simpa [sevenBoundaryScaledFormula, sevenBulkBoundaryWeight, intPolyEval,
    pFormula, pWeight,
    HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula.pIntPoly,
    HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula.pc,
    HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula.pa,
    HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula.pm,
    pIntPoly, pc, vx, pa, pm, pn, ps,
    IntRingNormaliser.eval, Int.sub_eq_add_neg, Int.mul_assoc] using h

private theorem weightSixBack_shift (u : Int) :
    80 * (u + 3) * (u + 3) * (u + 3) * (u + 3) +
        2218 * (u + 3) * (u + 3) - 5679 =
      intPolyEval u [20763, 21948, 6538, 960, 80] := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq _ _
    weightSixBack_shift_normal (fun _ => u)
  simpa [pWeightSixBack, pIntPoly, pc, vx, pa, pm, pn, ps,
    IntRingNormaliser.eval, intPolyEval, Int.sub_eq_add_neg,
    Int.mul_assoc] using h

/-- The sixth boundary coordinate, which starts the induction bulk, is
nonnegative from scale three onward. -/
theorem sevenBoundaryScaledFormula_six_nonnegative (m : Nat) (hm : 3 ≤ m) :
    0 ≤ sevenBoundaryScaledFormula 6 (m : Int) := by
  let u := m - 3
  have hm' : (m : Int) = (u : Int) + 3 := by
    dsimp only [u]
    omega
  rw [formulaSix_eq_weight, hm']
  simp only [sevenBulkBoundaryWeight]
  rw [weightSixBack_shift]
  have hu : (0 : Int) ≤ (u : Int) := Int.natCast_nonneg u
  have hp : 0 ≤ intPolyEval (u : Int) [20763, 21948, 6538, 960, 80] := by
    simpa using intPolyEval_nat_nonnegative hu [20763, 21948, 6538, 960, 80]
  exact Int.mul_nonneg
    (Int.mul_nonneg
      (Int.mul_nonneg
        (Int.mul_nonneg
          (Int.mul_nonneg (by omega) (by omega)) (by omega))
        (by omega))
      (by omega))
    hp

/-- Actual sixth gap deficit is nonnegative; the common scale `5670` is
strictly positive, so no sign is lost when it is removed. -/
theorem sevenGapDeficit_six_nonnegative (m : Nat) (hm : 3 ≤ m) :
    0 ≤ sevenGapDeficit m 6 := by
  have hs := sevenGapDeficit_boundary_scaled m 6 (by omega) (by omega)
  have hf := sevenBoundaryScaledFormula_six_nonnegative m hm
  have hscaled : (0 : Int) ≤ 5670 * sevenGapDeficit m 6 := by
    rw [hs]
    exact hf
  have hzero : (5670 : Int) * 0 ≤ 5670 * sevenGapDeficit m 6 := by
    simpa using hscaled
  exact Int.le_of_mul_le_mul_left hzero (by decide)

#print axioms sevenBulkBoundaryWeight
#print axioms sevenBulkBoundaryAdjustment
#print axioms sevenBoundaryScaledFormula_eq_weight_adjustment
#print axioms bulkFalling
#print axioms bulkRisingTailSix
#print axioms sevenBulkBoundaryCleared
#print axioms sevenBulkBoundaryPositive
#print axioms sevenBulkBoundaryCleared_shift
#print axioms sevenBulkBoundaryCleared_nonnegative
#print axioms sevenBoundaryScaledFormula_six_nonnegative
#print axioms sevenGapDeficit_six_nonnegative

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBulkBoundary
