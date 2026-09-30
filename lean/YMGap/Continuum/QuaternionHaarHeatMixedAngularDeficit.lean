/-
# Mixed-angular Jacobi deficit of the original SU(2) heat polynomial

An explicit generic polynomial heat-tail modulus pays the degree-six and
degree-four mixed derivative terms. The resulting cutoff depends on the nome,
derivative caps and tolerance, not on the Haar carrier or a heat minimum.
-/

import YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative
import YMGap.Continuum.QuaternionHaarHeatAngularDeficit
import YMGap.Continuum.SU2HeatPolynomialPrefixBound
import YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval

namespace YMGap.Continuum.QuaternionHaarHeatMixedAngularDeficit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval
  (deficit deficit_bounds deficit_abs_small)
open YMGap.Continuum.FiniteJacobiWeightConvergence (centeredCutoff)
open YMGap.Continuum.PolynomialWeightedSumBounds (sum_range_add)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
  (heatTerm deficitPolynomial)
open YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative (angularDerivative_finitePolySum)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.SU2HeatPolynomialPrefixBound
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

/-- Generic-m analogue of the quartic finite-tail modulus. -/
def tailScale (w : Q') (m : Nat) : Q' :=
  tailTerm w m (SU2HeatPolynomialPrefixBound.labelCutoff w m) *
    HKConv.divPos 1 (1 + (-HalfPow.half))

def tailRescale (w : Q') (m : Nat) (epsilon : Q') : Q' :=
  HKConv.divPos epsilon (tailScale w m + 1)

def tailCutoff (w : Q') (m : Nat) (epsilon : Q') : Nat :=
  SU2HeatPolynomialPrefixBound.labelCutoff w m +
    powBaseCutoff HalfPow.half (tailRescale w m epsilon)

private theorem tailScale_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (m : Nat) :
    (0 : Q') ≤ tailScale w m :=
  Q'.mul_nonneg _ _
    (tailTerm_nonneg (Q'.le_of_lt hw0) m (SU2HeatPolynomialPrefixBound.labelCutoff w m))
    (HKConv.divPos_nonneg Q'.zero_le_one)

private theorem tailRescale_positive (w : Q') (m : Nat) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < tailRescale w m epsilon :=
  HKConv.divPos_pos (CReal.num_pos_of_pos hepsilon)

private theorem tailRescale_budget {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hepsilon : (0 : Q') < epsilon) (m : Nat) :
    tailScale w m * tailRescale w m epsilon ≤ epsilon := by
  have hs0 : (0 : Q') ≤ tailScale w m := tailScale_nonnegative hw0 m
  have hd0 : (0 : Q') ≤ tailRescale w m epsilon :=
    Q'.le_of_lt (tailRescale_positive w m hepsilon)
  have hden : (0 : Q') < tailScale w m + 1 :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ hs0)
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  have hle : tailScale w m * tailRescale w m epsilon ≤
      (tailScale w m + 1) * tailRescale w m epsilon :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.add_le_self_of_nonneg (tailScale w m) 1 Q'.zero_le_one) hd0
  have heq : (tailScale w m + 1) * tailRescale w m epsilon ≈ epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (tailScale w m + 1) (tailRescale w m epsilon))
      (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hden))
  exact Q'.le_trans' _ _ _ hle (Q'.le_of_eqv heq)

private theorem closedTail_small {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hepsilon : (0 : Q') < epsilon)
    (m M : Nat)
    (hM : powBaseCutoff HalfPow.half (tailRescale w m epsilon) ≤ M) :
    geoTailBase (tailTerm w m (SU2HeatPolynomialPrefixBound.labelCutoff w m))
      HalfPow.half M ≤ epsilon := by
  have hp : HalfPow.half ^ M ≤ tailRescale w m epsilon :=
    Q'.le_trans' _ _ _
      (pow_base_antitone HalfPow.half_nonneg
        (Q'.le_of_lt (by decide : HalfPow.half < (1 : Q'))) hM)
      (pow_base_le_cutoff (by decide : (0 : Q') < HalfPow.half)
        (by decide : HalfPow.half < (1 : Q'))
        (tailRescale_positive w m hepsilon))
  have hs0 : (0 : Q') ≤ tailScale w m := tailScale_nonnegative hw0 m
  have heq : geoTailBase
      (tailTerm w m (SU2HeatPolynomialPrefixBound.labelCutoff w m))
      HalfPow.half M ≈ tailScale w m * HalfPow.half ^ M := by
    unfold geoTailBase tailScale
    exact Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv _ (HalfPow.half ^ M)
        (HKConv.divPos 1 (1 + (-HalfPow.half))))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_comm_eqv (HalfPow.half ^ M)
            (HKConv.divPos 1 (1 + (-HalfPow.half)))))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _
          (HKConv.divPos 1 (1 + (-HalfPow.half))) (HalfPow.half ^ M))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hp hs0)
      (tailRescale_budget hw0 hepsilon m))

/-- Every finite degree-`m` heat tail beginning after this explicit cutoff
has scalar mass at most the requested positive tolerance. -/
theorem finite_shifted_tail_le {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hepsilon : (0 : Q') < epsilon) (m N L : Nat)
    (hN : tailCutoff w m epsilon ≤ N) :
    finSum (fun k => tailTerm w m (N+k)) L ≤ epsilon := by
  have hlabel : SU2HeatPolynomialPrefixBound.labelCutoff w m ≤ N := by
    unfold tailCutoff at hN
    omega
  let M := N - SU2HeatPolynomialPrefixBound.labelCutoff w m
  have hM : powBaseCutoff HalfPow.half (tailRescale w m epsilon) ≤ M := by
    unfold tailCutoff at hN
    dsimp [M]
    omega
  have hrewrite : SU2HeatPolynomialPrefixBound.labelCutoff w m + M = N := by
    dsimp [M]
    exact Nat.add_sub_of_le hlabel
  have hterm : ∀ k : Nat,
      tailTerm w m (N+k) ≤
        geoIncrBase
          (tailTerm w m (SU2HeatPolynomialPrefixBound.labelCutoff w m))
          HalfPow.half (M+k) := by
    intro k
    rw [← hrewrite, Nat.add_assoc]
    exact SU2HeatPolynomialPrefixBound.shifted_geometric hw0 hw1 m (M+k)
  exact Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise _ _ hterm L)
    (Q'.le_trans' _ _ _
      (geoTailBase_series_le
        (tailTerm_nonneg (Q'.le_of_lt hw0) m _)
        (by decide : (0 : Q') < HalfPow.half)
        (by decide : HalfPow.half < (1 : Q')) M L)
      (closedTail_small hw0 hepsilon m M hM))

/-- One tolerance pays both polynomial majorant tails. -/
def tailTolerance (d e m epsilon : Q') : Q' :=
  HKConv.divPos (HalfPow.half * epsilon) ((4*d*e + 2*m) + 1)

def headTolerance (w d e m epsilon : Q') : Q' :=
  HKConv.divPos (HalfPow.half * epsilon)
    (heatSecondDerivativeCap w d e m + 1)

def bandSize (w d e m epsilon : Q') : Nat :=
  max (tailCutoff w 6 (tailTolerance d e m epsilon))
    (tailCutoff w 4 (tailTolerance d e m epsilon)) + 1

/-- Computed Jacobi cutoff for the mixed differentiated deficit. -/
def deficitCutoff (w d e m epsilon : Q') : Nat :=
  centeredCutoff (w*w) (bandSize w d e m epsilon)
    (headTolerance w d e m epsilon)

private theorem tailTolerance_positive (d e m : Q') {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < tailTolerance d e m epsilon :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (ExpNeg.half_mul_pos _ hepsilon))

private theorem headTolerance_positive (w d e m : Q') {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < headTolerance w d e m epsilon :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (ExpNeg.half_mul_pos _ hepsilon))

private theorem scaledTolerance_budget (a epsilon : Q')
    (ha : (0 : Q') ≤ a) (hepsilon : (0 : Q') < epsilon) :
    a * HKConv.divPos (HalfPow.half * epsilon) (a + 1) ≤
      HalfPow.half * epsilon := by
  have hd : (0 : Q') < HKConv.divPos (HalfPow.half * epsilon) (a + 1) :=
    HKConv.divPos_pos (CReal.num_pos_of_pos (ExpNeg.half_mul_pos _ hepsilon))
  have hp : (0 : Q') < a + 1 := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ ha)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  have hle : a * HKConv.divPos (HalfPow.half * epsilon) (a + 1) ≤
      (a + 1) * HKConv.divPos (HalfPow.half * epsilon) (a + 1) :=
    Q'.mul_le_mul_of_nonneg_right a (a+1)
      (HKConv.divPos (HalfPow.half * epsilon) (a+1))
      (Q'.add_le_self_of_nonneg a 1 Q'.zero_le_one) (Q'.le_of_lt hd)
  have heq : (a+1) * HKConv.divPos (HalfPow.half * epsilon) (a+1) ≈
      HalfPow.half * epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (a+1) (HKConv.divPos (HalfPow.half * epsilon) (a+1)))
      (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp))
  exact Q'.le_trans' _ _ _ hle (Q'.le_of_eqv heq)

private theorem bandSize_le_deficitCutoff (w d e m epsilon : Q') :
    bandSize w d e m epsilon ≤ deficitCutoff w d e m epsilon :=
  Nat.le_add_right _ _

private def weightedRangeInterval {blocks : Nat} (f : Nat → RatPoly)
    (c a : Nat → Q')
    (hI : ∀ r, Interval blocks (f r) (c r))
    (ha : ∀ r, (0 : Q') ≤ a r)
    (N : Nat) (A : Q') (hA : ∀ r, r < N → a r ≤ A) :
    Interval blocks
      (finitePolySum (fun r => polySmul (a r) (f r)) (List.range N))
      (A * finSum c N) :=
  (Interval.finiteRange _ _ (fun r => (hI r).smul (a r) (ha r)) N).weaken
    (Q'.le_trans' _ _ _ (finSum_le_lt _ _ N (fun r hr =>
      Q'.mul_le_mul_of_nonneg_right _ _ _ (hA r hr) (hI r).nonnegative))
      (Q'.ge_of_eqv (const_mul_finSum c A N)))

private theorem finitePolySum_coeff_congr {T : Type} (f g : T → RatPoly)
    (h : ∀ a, RatPolyCoeffEqv (f a) (g a)) : ∀ xs : List T,
    RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => (h a).add (finitePolySum_coeff_congr f g h xs)

private theorem finitePolySum_supported {T : Type} {blocks : Nat}
    (f : T → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) : ∀ xs : List T,
    SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a :: xs => polyAdd_supported (h a) (finitePolySum_supported f h xs)

private theorem derivative_prefix_bound {w d e m : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hd : (0 : Q') ≤ d) (he : (0 : Q') ≤ e)
    (hm : (0 : Q') ≤ m) (J : Nat) :
    finSum (fun r =>
      (4*d*e)*tailTerm w 6 r + (2*m)*tailTerm w 4 r) J ≤
      heatSecondDerivativeCap w d e m := by
  have hsum : finSum (fun r =>
      (4*d*e)*tailTerm w 6 r + (2*m)*tailTerm w 4 r) J ≈
      (4*d*e)*finSum (tailTerm w 6) J +
        (2*m)*finSum (tailTerm w 4) J :=
    Q'.eqv_trans _ _ _ (finSum_add _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_symm (const_mul_finSum _ _ _))
        (Q'.eqv_symm (const_mul_finSum _ _ _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
    (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (SU2HeatPolynomialPrefixBound.prefix_bound hw0 hw1 6 J)
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (by decide) hd) he))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (SU2HeatPolynomialPrefixBound.prefix_bound hw0 hw1 4 J)
        (Q'.mul_nonneg _ _ (by decide) hm)))

private theorem derivative_tail_bound {w d e m epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hd : (0 : Q') ≤ d) (he : (0 : Q') ≤ e)
    (hm : (0 : Q') ≤ m)
    (hepsilon : (0 : Q') < epsilon) (J L : Nat)
    (hJ6 : tailCutoff w 6 (tailTolerance d e m epsilon) ≤ J)
    (hJ4 : tailCutoff w 4 (tailTolerance d e m epsilon) ≤ J) :
    finSum (fun r =>
      (4*d*e)*tailTerm w 6 (J+r) +
        (2*m)*tailTerm w 4 (J+r)) L ≤
      HalfPow.half * epsilon := by
  let tau := tailTolerance d e m epsilon
  have h6 := finite_shifted_tail_le hw0 hw1
    (tailTolerance_positive d e m hepsilon) 6 J L hJ6
  have h4 := finite_shifted_tail_le hw0 hw1
    (tailTolerance_positive d e m hepsilon) 4 J L hJ4
  have hsum : finSum (fun r =>
      (4*d*e)*tailTerm w 6 (J+r) +
        (2*m)*tailTerm w 4 (J+r)) L ≈
      (4*d*e)*finSum (fun r => tailTerm w 6 (J+r)) L +
        (2*m)*finSum (fun r => tailTerm w 4 (J+r)) L :=
    Q'.eqv_trans _ _ _ (finSum_add _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_symm (const_mul_finSum _ _ _))
        (Q'.eqv_symm (const_mul_finSum _ _ _)))
  have hbound :
      (4*d*e)*finSum (fun r => tailTerm w 6 (J+r)) L +
        (2*m)*finSum (fun r => tailTerm w 4 (J+r)) L ≤
      (4*d*e)*tau + (2*m)*tau :=
    Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ h6
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hd) he))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ h4
        (Q'.mul_nonneg _ _ (by decide) hm))
  have hfactor : (4*d*e)*tau + (2*m)*tau ≈
      ((4*d*e)+(2*m))*tau :=
    Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
    (Q'.le_trans' _ _ _ hbound
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
        (scaledTolerance_budget ((4*d*e)+(2*m)) epsilon
          (Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hd) he)
            (Q'.mul_nonneg _ _ (by decide) hm)) hepsilon)))

/-- The mixed derivative of the literal Jacobi deficit has a computed
two-sided original-Haar interval, with no local heat floor in the cap. -/
def mixedAngularDeficitInterval {blocks i j k l : Nat} {x : RatPoly}
    {w d e m epsilon : Q'}
    (hoi : i < 4*blocks) (hoj : j < 4*blocks)
    (hii : k < 4*blocks) (hij : l < 4*blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (X : SquareBound blocks x 1)
    (DX : Interval blocks (angularDerivative i j x) d)
    (DY : Interval blocks (angularDerivative k l x) e)
    (DXY : Interval blocks
      (angularDerivative i j (angularDerivative k l x)) m)
    (hepsilon : (0 : Q') < epsilon) (N : Nat)
    (hN : deficitCutoff w d e m epsilon ≤ N) :
    Interval blocks
      (angularDerivative i j
        (angularDerivative k l (deficitPolynomial w N x))) epsilon := by
  let J := bandSize w d e m epsilon
  let delta := headTolerance w d e m epsilon
  have hdelta : (0 : Q') < delta :=
    headTolerance_positive w d e m hepsilon
  have hJN : J ≤ N :=
    Nat.le_trans (bandSize_le_deficitCutoff w d e m epsilon) hN
  let derivativeTerm := fun r =>
    angularDerivative i j (angularDerivative k l (heatTerm w x r))
  let derivativeCap := fun r =>
    (4*d*e)*tailTerm w 6 r + (2*m)*tailTerm w 4 r
  have hterm : ∀ r, Interval blocks (derivativeTerm r) (derivativeCap r) :=
    fun r => heatSecondTermInterval hoi hoj hii hij (Q'.le_of_lt hw0)
      X DX DY DXY r
  let head := weightedRangeInterval derivativeTerm derivativeCap (deficit w N)
    hterm (fun r => (deficit_bounds hw0 hw1 N r).1) J delta
    (fun r hr => Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (deficit_abs_small hw0 hw1 J hdelta N r hN hr))
  have hhead : delta * finSum derivativeCap J ≤
      HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (derivative_prefix_bound hw0 hw1 DX.nonnegative DY.nonnegative
          DXY.nonnegative J) (Q'.le_of_lt hdelta))
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_comm_eqv delta
          (heatSecondDerivativeCap w d e m)))
        (scaledTolerance_budget (heatSecondDerivativeCap w d e m) epsilon
          (Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _
              (Q'.mul_nonneg _ _
                (Q'.mul_nonneg _ _ (by decide) DX.nonnegative)
                DY.nonnegative)
              (SU2HeatPolynomialPrefixBound.prefixBudget_nonnegative hw0 6))
            (Q'.mul_nonneg _ _
              (Q'.mul_nonneg _ _ (by decide) DXY.nonnegative)
              (SU2HeatPolynomialPrefixBound.prefixBudget_nonnegative hw0 4)))
          hepsilon))
  let tail := weightedRangeInterval
    (fun r => derivativeTerm (J+r))
    (fun r => derivativeCap (J+r))
    (fun r => deficit w N (J+r))
    (fun r => hterm (J+r))
    (fun r => (deficit_bounds hw0 hw1 N (J+r)).1)
    (N-J) 1 (fun r _ => (deficit_bounds hw0 hw1 N (J+r)).2)
  have htail : (1 : Q') *
      finSum (fun r => derivativeCap (J+r)) (N-J) ≤
      HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (derivative_tail_bound hw0 hw1 DX.nonnegative DY.nonnegative
        DXY.nonnegative hepsilon J (N-J)
        (by unfold J bandSize; omega)
        (by unfold J bandSize; omega))
  have hsplit := sum_range_add
    (fun r => polySmul (deficit w N r) (derivativeTerm r)) J (N-J)
  rw [Nat.add_sub_of_le hJN] at hsplit
  have hp : SupportedQuaternionBlocks blocks (deficitPolynomial w N x) := by
    unfold deficitPolynomial
    exact finitePolySum_supported _
      (fun r => polySmul_supported
        (QuaternionHaarAllNomeHeatCertificate.termInterval
          (Q'.le_of_lt hw0) X r).support _)
      (List.range N)
  have hdiff :=
    (angularDerivative_congr i j
      (angularDerivative_finitePolySum k l
        (fun r => polySmul (deficit w N r) (heatTerm w x r))
        (List.range N))).trans
      (angularDerivative_finitePolySum i j _ (List.range N))
  have hsmul := finitePolySum_coeff_congr
    (fun r => angularDerivative i j
      (angularDerivative k l
        (polySmul (deficit w N r) (heatTerm w x r))))
    (fun r => polySmul (deficit w N r) (derivativeTerm r))
    (fun r =>
      (angularDerivative_congr i j
        (angularDerivative_smul k l (deficit w N r) (heatTerm w x r))).trans
      (angularDerivative_smul i j (deficit w N r)
        (angularDerivative k l (heatTerm w x r))))
    (List.range N)
  have total : Interval blocks
      (finitePolySum
        (fun r => polySmul (deficit w N r) (derivativeTerm r))
        (List.range N)) epsilon := by
    rw [hsplit]
    exact ((head.weaken hhead).add (tail.weaken htail)).changeCap
      (ExpNeg.two_halves epsilon)
  exact Interval.ofCoeff
    (angularDerivative_supported_at hoi hoj
      (angularDerivative_supported_at hii hij hp))
    (hdiff.trans hsmul) total

end YMGap.Continuum.QuaternionHaarHeatMixedAngularDeficit

#print axioms YMGap.Continuum.QuaternionHaarHeatMixedAngularDeficit.tailCutoff
#print axioms YMGap.Continuum.QuaternionHaarHeatMixedAngularDeficit.finite_shifted_tail_le
#print axioms YMGap.Continuum.QuaternionHaarHeatMixedAngularDeficit.deficitCutoff
#print axioms YMGap.Continuum.QuaternionHaarHeatMixedAngularDeficit.mixedAngularDeficitInterval
