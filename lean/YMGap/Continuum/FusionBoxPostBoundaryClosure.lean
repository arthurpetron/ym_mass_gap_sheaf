/-
`FusionBoxPostBoundaryClosure` -- scale the selected endpoint shells back to
the canonical cleared integer ledger, then close every post-boundary prefix.

The endpoint estimates are analytic inequalities between the actual finite
fusion boxes.  The boundary-shell classification supplies the corresponding
positive integer cells.  This file identifies their common `4^D` scale and
uses the generic total-negative domination compiler.
-/

import YMGap.Continuum.FusionBoxEndpointShellPayment
import YMGap.Continuum.FusionBoxBoundaryShellClassification
import YMGap.Continuum.FusionBoxPhysicalIntervalConsumer

namespace YMGap.Continuum.FusionBoxPostBoundaryClosure

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionBoxBernsteinReconstruction
open YMGap.Continuum.FusionBoxPrefixReserve
open YMGap.Continuum.FusionBoxFirstShellReserve
open YMGap.Continuum.FusionBoxEndpointShellPayment
open YMGap.Continuum.FusionBoxBoundaryShellClassification
open YMGap.Continuum.FusionBoxPhysicalIntervalConsumer

private abbrev halfW : Q' := wH

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl
private theorem ofInt_num_cast_local (z : Int) : (Q'.ofInt z).num = z := rfl
private theorem ofInt_den_cast_local (z : Int) :
    ((Q'.ofInt z).den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, Q'.mkPos_num, Q'.mkPos_den, neg_num_cast_local,
               ofInt_num_cast_local, ofInt_den_cast_local,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

private theorem fusionOK_at_exact_sum_local
    (a b t : Nat) (h : a + b = t) : fusionOK a b t = true := by
  apply (fusionOK_strand a b t).mpr
  exact ⟨b, a, 0, by omega, by omega, by omega⟩

private theorem boxKer_at_exact_sum
    (w : Q') (a b t : Nat) (h : a + b = t) :
    (boxKer w t a b).eqv (coeffW w a * coeffW w b) := by
  unfold boxKer fusionInd
  rw [fusionOK_at_exact_sum_local a b t h]
  exact Q'.one_mul_eqv _

private theorem half_double_sum_local (x : Nat) : (x + x) / 2 = x := by
  rw [← Nat.mul_two x, Nat.mul_div_left x (by decide)]

private theorem evenShellHalfExponent (m : Nat) :
    boxQuadHalfExponent m m (m + 1) (m + 1) =
      c4 m + c4 (m + 1) := by
  unfold boxQuadHalfExponent boxQuadExponent
  exact half_double_sum_local (c4 m + c4 (m + 1))

private theorem oddCentralHalfExponent (m : Nat) :
    boxQuadHalfExponent (m + 1) (m + 1) (m + 1) (m + 1) =
      2 * c4 (m + 1) := by
  unfold boxQuadHalfExponent boxQuadExponent
  rw [half_double_sum_local]
  omega

private theorem oddDisplacedCasimir (m : Nat) :
    c4 m + c4 (m + 2) = 2 * c4 (m + 1) + 2 := by
  unfold c4
  simp only [Nat.add_mul, Nat.mul_add]
  omega

private theorem oddDisplacedHalfExponent (m : Nat) :
    boxQuadHalfExponent m m (m + 2) (m + 2) =
      2 * c4 (m + 1) + 2 := by
  unfold boxQuadHalfExponent boxQuadExponent
  rw [half_double_sum_local, oddDisplacedCasimir]

private theorem pow_four_eq_square_square_local (x : Nat) :
    x ^ 4 = (x * x) * (x * x) := by
  simp [Nat.pow_succ, Nat.mul_assoc]

private theorem evenSelectedClearedCell_eq_weight (N m : Nat) :
    Int.ofNat (boxCellClearedMultiplicity N
      (boxProductMultiplicity (2 * m + 1) (2 * m + 1)
        m m (m + 1) (m + 1)) m m (m + 1) (m + 1)) =
      evenFirstShellCellWeight N m := by
  have hfusion : fusionOK m (m + 1) (2 * m + 1) = true :=
    fusionOK_at_exact_sum_local m (m + 1) (2 * m + 1) (by omega)
  unfold boxCellClearedMultiplicity boxProductMultiplicity
    boxQuadDimension evenFirstShellCellWeight
  simp only [hfusion, Bool.true_and, if_true, evenShellHalfExponent]
  rw [Nat.pow_two]

private theorem oddCentralClearedCell_eq_weight (N m : Nat) :
    Int.ofNat (boxCellClearedMultiplicity N
      (boxProductMultiplicity (2 * m + 2) (2 * m + 2)
        (m + 1) (m + 1) (m + 1) (m + 1))
      (m + 1) (m + 1) (m + 1) (m + 1)) =
      oddFirstShellCellWeight N m := by
  have hfusion : fusionOK (m + 1) (m + 1) (2 * m + 2) = true :=
    fusionOK_at_exact_sum_local (m + 1) (m + 1) (2 * m + 2) (by omega)
  unfold boxCellClearedMultiplicity boxProductMultiplicity
    boxQuadDimension oddFirstShellCellWeight
  simp only [hfusion, Bool.true_and, if_true, oddCentralHalfExponent]
  rw [pow_four_eq_square_square_local]

private theorem oddDisplacedClearedCell_eq_weight (N m : Nat) :
    Int.ofNat (boxCellClearedMultiplicity N
      (boxProductMultiplicity (2 * m + 2) (2 * m + 2)
        m m (m + 2) (m + 2)) m m (m + 2) (m + 2)) =
      oddSecondShellCellWeight N m := by
  have hfusion : fusionOK m (m + 2) (2 * m + 2) = true :=
    fusionOK_at_exact_sum_local m (m + 2) (2 * m + 2) (by omega)
  unfold boxCellClearedMultiplicity boxProductMultiplicity
    boxQuadDimension oddSecondShellCellWeight
  simp only [hfusion, Bool.true_and, if_true, oddDisplacedHalfExponent]
  rw [Nat.pow_two]

private theorem evenSelectedCell_endpoint
    (N m : Nat) (hguard : 2 * m + 2 <= 2 * N) :
    (Q'.ofInt (evenFirstShellCellWeight N m)).eqv
      (Q'.ofNat (4 ^ boxBernsteinDegree N) *
        ((coeffW halfW m * coeffW halfW (m + 1)) *
          (coeffW halfW m * coeffW halfW (m + 1)))) := by
  have hbound : m + 1 <= N := by omega
  have hcell := boxProductClearedCell_endpoint N
    (2 * m + 1) (2 * m + 1) m m (m + 1) (m + 1)
    rfl (by omega) (by omega) (by omega) (by omega)
  rw [evenSelectedClearedCell_eq_weight] at hcell
  refine Q'.eqv_trans _ _ _ hcell ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat (4 ^ boxBernsteinDegree N)) _ _
    (Q'.eqv_trans _
      ((coeffW halfW m * coeffW halfW (m + 1)) *
        boxKer halfW (2 * m + 1) m (m + 1)) _
      (Q'.mul_eqv_congr_right _ _ _
        (boxKer_at_exact_sum halfW m (m + 1) (2 * m + 1) (by omega)))
      (Q'.mul_eqv_congr_left _ _ _
        (boxKer_at_exact_sum halfW m (m + 1) (2 * m + 1) (by omega))))

private theorem oddCentralCell_endpoint
    (N m : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N) :
    (Q'.ofInt (oddFirstShellCellWeight N m)).eqv
      (Q'.ofNat (4 ^ boxBernsteinDegree N) *
        ((coeffW halfW (m + 1) * coeffW halfW (m + 1)) *
          (coeffW halfW (m + 1) * coeffW halfW (m + 1)))) := by
  have hbound : m + 2 <= N := by omega
  have hcell := boxProductClearedCell_endpoint N
    (2 * m + 2) (2 * m + 2)
    (m + 1) (m + 1) (m + 1) (m + 1)
    rfl (by omega) (by omega) (by omega) (by omega)
  rw [oddCentralClearedCell_eq_weight] at hcell
  refine Q'.eqv_trans _ _ _ hcell ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat (4 ^ boxBernsteinDegree N)) _ _
    (Q'.eqv_trans _
      ((coeffW halfW (m + 1) * coeffW halfW (m + 1)) *
        boxKer halfW (2 * m + 2) (m + 1) (m + 1)) _
      (Q'.mul_eqv_congr_right _ _ _
        (boxKer_at_exact_sum halfW (m + 1) (m + 1)
          (2 * m + 2) (by omega)))
      (Q'.mul_eqv_congr_left _ _ _
        (boxKer_at_exact_sum halfW (m + 1) (m + 1)
          (2 * m + 2) (by omega))))

private theorem oddDisplacedCell_endpoint
    (N m : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N) :
    (Q'.ofInt (oddSecondShellCellWeight N m)).eqv
      (Q'.ofNat (4 ^ boxBernsteinDegree N) *
        ((coeffW halfW m * coeffW halfW (m + 2)) *
          (coeffW halfW m * coeffW halfW (m + 2)))) := by
  have hbound : m + 2 <= N := by omega
  have hcell := boxProductClearedCell_endpoint N
    (2 * m + 2) (2 * m + 2) m m (m + 2) (m + 2)
    rfl (by omega) (by omega) (by omega) (by omega)
  rw [oddDisplacedClearedCell_eq_weight] at hcell
  refine Q'.eqv_trans _ _ _ hcell ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat (4 ^ boxBernsteinDegree N)) _ _
    (Q'.eqv_trans _
      ((coeffW halfW m * coeffW halfW (m + 2)) *
        boxKer halfW (2 * m + 2) m (m + 2)) _
      (Q'.mul_eqv_congr_right _ _ _
        (boxKer_at_exact_sum halfW m (m + 2) (2 * m + 2) (by omega)))
      (Q'.mul_eqv_congr_left _ _ _
        (boxKer_at_exact_sum halfW m (m + 2) (2 * m + 2) (by omega))))

private theorem ofNat_four_eqv_ofInt_four :
    (Q'.ofNat 4).eqv (Q'.ofInt 4) := Q'.eqv_refl _

/-- The four selected even cells are exactly the cleared endpoint reserve. -/
theorem evenFirstShellPositiveReserve_endpoint
    (N m : Nat) (hguard : 2 * m + 2 <= 2 * N) :
    (Q'.ofNat (4 ^ boxBernsteinDegree N) *
      (Q'.ofNat 4 *
        ((coeffW halfW m * coeffW halfW m) *
          (coeffW halfW (m + 1) * coeffW halfW (m + 1))))).eqv
      (Q'.ofInt (evenFirstShellPositiveReserve N m)) := by
  have hcell := evenSelectedCell_endpoint N m hguard
  refine Q'.eqv_trans _
    (Q'.ofNat 4 *
      (Q'.ofNat (4 ^ boxBernsteinDegree N) *
        ((coeffW halfW m * coeffW halfW (m + 1)) *
          (coeffW halfW m * coeffW halfW (m + 1))))) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * Q'.ofInt (evenFirstShellCellWeight N m)) _
    (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ (Q'.eqv_symm hcell)) ?_
  refine Q'.eqv_trans _
    (Q'.ofInt 4 * Q'.ofInt (evenFirstShellCellWeight N m)) _
    (Q'.mul_eqv_congr_right _ _ _ ofNat_four_eqv_ofInt_four) ?_
  simpa only [evenFirstShellPositiveReserve] using
    Q'.eqv_symm
      (RingNormaliser.ofInt_mul 4 (evenFirstShellCellWeight N m))

/-- The odd central cell and four displaced cells are exactly the cleared
two-shell endpoint reserve. -/
theorem oddSecondShellPositiveReserve_endpoint
    (N m : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N) :
    (Q'.ofNat (4 ^ boxBernsteinDegree N) *
      (((coeffW halfW (m + 1) * coeffW halfW (m + 1)) *
          (coeffW halfW (m + 1) * coeffW halfW (m + 1))) +
        Q'.ofNat 4 *
          ((coeffW halfW m * coeffW halfW (m + 2)) *
            (coeffW halfW m * coeffW halfW (m + 2))))).eqv
      (Q'.ofInt (oddSecondShellPositiveReserve N m)) := by
  have hcentral := oddCentralCell_endpoint N m hguard
  have hdisplaced := oddDisplacedCell_endpoint N m hguard
  refine Q'.eqv_trans _
    ((Q'.ofNat (4 ^ boxBernsteinDegree N) *
        ((coeffW halfW (m + 1) * coeffW halfW (m + 1)) *
          (coeffW halfW (m + 1) * coeffW halfW (m + 1)))) +
      Q'.ofNat 4 *
        (Q'.ofNat (4 ^ boxBernsteinDegree N) *
          ((coeffW halfW m * coeffW halfW (m + 2)) *
            (coeffW halfW m * coeffW halfW (m + 2))))) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    (Q'.ofInt (oddFirstShellCellWeight N m) +
      Q'.ofNat 4 * Q'.ofInt (oddSecondShellCellWeight N m)) _
    (Q'.add_eqv_congr'
      (Q'.eqv_symm hcentral)
      (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _
        (Q'.eqv_symm hdisplaced))) ?_
  refine Q'.eqv_trans _
    (Q'.ofInt (oddFirstShellCellWeight N m) +
      Q'.ofInt 4 * Q'.ofInt (oddSecondShellCellWeight N m)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ ofNat_four_eqv_ofInt_four)) ?_
  refine Q'.eqv_trans _
    (Q'.ofInt (oddFirstShellCellWeight N m) +
      Q'.ofInt (4 * oddSecondShellCellWeight N m)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (RingNormaliser.ofInt_mul 4 (oddSecondShellCellWeight N m)))) ?_
  simpa only [oddSecondShellPositiveReserve] using
    Q'.eqv_symm (RingNormaliser.ofInt_add
      (oddFirstShellCellWeight N m)
      (4 * oddSecondShellCellWeight N m))

/-! ## 2. Endpoint payment transported to the integer ledger -/

/-- The full negative outer-product ledger in an even row is paid by the
four selected first-shell cells. -/
theorem evenNegativeClearedTotal_le_firstShellReserve
    (N m : Nat) (hguard : 2 * m + 2 <= 2 * N) :
    boxNegativeClearedTotal N (2 * m) <=
      evenFirstShellPositiveReserve N m := by
  rw [boxNegativeClearedTotal_eq_product]
  exact boxProductClearedTotal_le_reserve_of_endpoint
    N (2 * m) (2 * m + 2) (by omega)
    (Q'.ofNat 4 *
      ((coeffW halfW m * coeffW halfW m) *
        (coeffW halfW (m + 1) * coeffW halfW (m + 1))))
    (evenFirstShellPositiveReserve N m)
    (evenOuterProduct_le_fourCentral N m)
    (evenFirstShellPositiveReserve_endpoint N m hguard)

/-- The full negative outer-product ledger in an odd row is paid by the
central cell together with the four first displaced cells. -/
theorem oddNegativeClearedTotal_le_secondShellReserve
    (N m : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N) :
    boxNegativeClearedTotal N (2 * m + 1) <=
      oddSecondShellPositiveReserve N m := by
  rw [boxNegativeClearedTotal_eq_product]
  exact boxProductClearedTotal_le_reserve_of_endpoint
    N (2 * m + 1) (2 * m + 1 + 2) (by omega)
    (((coeffW halfW (m + 1) * coeffW halfW (m + 1)) *
        (coeffW halfW (m + 1) * coeffW halfW (m + 1))) +
      Q'.ofNat 4 *
        ((coeffW halfW m * coeffW halfW (m + 2)) *
          (coeffW halfW m * coeffW halfW (m + 2))))
    (oddSecondShellPositiveReserve N m)
    (oddOuterProduct_le_central_add_fourDisplaced N m)
    (oddSecondShellPositiveReserve_endpoint N m hguard)

/-- Every even prefix strictly past its first shell is nonnegative. -/
theorem evenPostBoundaryPrefix_nonnegative
    (N m K : Nat) (hguard : 2 * m + 2 <= 2 * N)
    (hK : c4 m + c4 (m + 1) < K) :
    0 <= boxClearedPowerPrefix N (2 * m) K := by
  exact boxClearedPowerPrefix_nonnegative_of_total_domination
    N (2 * m) K (evenFirstShellPositiveReserve N m)
    (evenNegativeClearedTotal_le_firstShellReserve N m hguard)
    (evenPositiveClearedPrefix_ge_firstShellReserve N m K hguard hK)

/-- Every odd prefix beyond the second selected shell is nonnegative.  The
two intervening cutoffs are supplied separately by the boundary classifier. -/
theorem oddPostSecondShellPrefix_nonnegative
    (N m K : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N)
    (hK : 2 * c4 (m + 1) + 2 < K) :
    0 <= boxClearedPowerPrefix N (2 * m + 1) K := by
  exact boxClearedPowerPrefix_nonnegative_of_total_domination
    N (2 * m + 1) K (oddSecondShellPositiveReserve N m)
    (oddNegativeClearedTotal_le_secondShellReserve N m hguard)
    (oddPositiveClearedPrefix_ge_secondReserve N m K hguard hK)

/-! ## 3. The concrete post-boundary and all-cutoff families -/

/-- Every odd prefix strictly beyond its first shell is nonnegative.  The two
boundary cutoffs are exact finite shell classifications; all later cutoffs
are paid at once by total-negative domination. -/
theorem oddPostBoundaryPrefix_nonnegative
    (N m K : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N)
    (hK : 2 * c4 (m + 1) < K) :
    0 <= boxClearedPowerPrefix N (2 * m + 1) K := by
  by_cases hfirst : K = 2 * c4 (m + 1) + 1
  · rw [hfirst]
    exact odd_boxClearedPowerPrefix_nonnegative_firstBoundary N m
  · by_cases hsecond : K = 2 * c4 (m + 1) + 2
    · rw [hsecond]
      exact odd_boxClearedPowerPrefix_nonnegative_secondBoundary N m hguard
    · exact oddPostSecondShellPrefix_nonnegative N m K hguard (by omega)

/-- The formerly open producer: all even and odd prefixes beyond their
balanced support boundary are constructively nonnegative for every cutoff. -/
def postBoundaryEvenOddPrefixReserve : PostBoundaryEvenOddPrefixReserve :=
  ⟨fun N m K hguard hK =>
      evenPostBoundaryPrefix_nonnegative N m K hguard hK,
    fun N m K hguard hK =>
      oddPostBoundaryPrefix_nonnegative N m K hguard hK⟩

/-- The resulting term-filtered prefix reserve at every `N`, channel, and
cutoff. -/
def allCutoffPhysicalPrefixReserve : AllCutoffPhysicalPrefixReserve :=
  allCutoffPhysicalPrefixReserve_of_postBoundary
    postBoundaryEvenOddPrefixReserve

/-- Uniform fusion-box log-concavity on the full physical coupling interval,
simultaneously for every cutoff. -/
def uniformBoxLogConcave_physical_allN :
    forall w, (0 : Q') <= w -> w <= wH -> UniformBoxLogConcave w :=
  uniformBoxLogConcave_physical_interval postBoundaryEvenOddPrefixReserve

#print axioms YMGap.Continuum.FusionBoxPostBoundaryClosure.evenFirstShellPositiveReserve_endpoint
#print axioms YMGap.Continuum.FusionBoxPostBoundaryClosure.oddSecondShellPositiveReserve_endpoint
#print axioms YMGap.Continuum.FusionBoxPostBoundaryClosure.evenNegativeClearedTotal_le_firstShellReserve
#print axioms YMGap.Continuum.FusionBoxPostBoundaryClosure.oddNegativeClearedTotal_le_secondShellReserve
#print axioms YMGap.Continuum.FusionBoxPostBoundaryClosure.evenPostBoundaryPrefix_nonnegative
#print axioms YMGap.Continuum.FusionBoxPostBoundaryClosure.oddPostSecondShellPrefix_nonnegative
#print axioms YMGap.Continuum.FusionBoxPostBoundaryClosure.oddPostBoundaryPrefix_nonnegative
#print axioms YMGap.Continuum.FusionBoxPostBoundaryClosure.postBoundaryEvenOddPrefixReserve
#print axioms YMGap.Continuum.FusionBoxPostBoundaryClosure.allCutoffPhysicalPrefixReserve
#print axioms YMGap.Continuum.FusionBoxPostBoundaryClosure.uniformBoxLogConcave_physical_allN

end YMGap.Continuum.FusionBoxPostBoundaryClosure
