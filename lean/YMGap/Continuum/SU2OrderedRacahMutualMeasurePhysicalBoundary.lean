/-
# Physical-coordinate repair of the mutual-measure boundary

The unguarded coordinate family used by the first mutual-measure shell
quantifies outside the finite monomial boxes.  The smallest reduced endpoint
already refutes that statement.  This file banks the exact counterexample,
introduces the degree-guarded family, and integrates the measure-six
order-zero correction fence into a complete physical Jacobi block.
-/

import YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge
import YMGap.Continuum.SU2OrderedRacahRightJacobiEndpointLift

namespace YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahHeightOneCoordinateFamily
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge
open YMGap.Continuum.SU2OrderedRacahRightJacobiEndpointLift
open YMGap.Continuum.SU2OrderedRacahRightJacobiInduction
open YMGap.Continuum.SU2OrderedRacahRightJacobiLift
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients

local infix:50 " ≈ " => Q'.eqv

/-- The order-zero channel obtained by peeling the middle correction-fence
channel. -/
def correctionFenceReducedEndpointZero : FixedRightCGChannel 2 1 1 2 :=
  reducePositiveInnerRightChannel correctionFenceMiddle (by decide)

/-- Its order-one adjacent channel, obtained by peeling the upper
correction-fence channel. -/
def correctionFenceReducedEndpointOne : FixedRightCGChannel 2 1 1 2 :=
  reducePositiveInnerRightChannel correctionFenceUpper (by decide)

/-- The endpoint equation itself fails immediately outside the third
monomial degree.  Here `l = 2` while the reduced third degree is one. -/
theorem correctionFence_reduced_endpoint_unphysical_counterexample :
    ¬ RightEndpointTransposeJacobiAt correctionFenceReducedEndpointZero
      correctionFenceReducedEndpointOne 0 1 2 2 := by
  unfold RightEndpointTransposeJacobiAt correctionFenceReducedEndpointZero
    correctionFenceReducedEndpointOne
  decide

/-- Even inside the physical box, the generic three-carrier formula aliases
the missing lower neighbour at order zero.  The on-shell coordinate below is
an exact counterexample. -/
theorem correctionFence_reduced_raw_row_endpoint_alias_counterexample :
    ¬ RightTransposeJacobiAt correctionFenceReducedEndpointZero
      correctionFenceReducedEndpointZero correctionFenceReducedEndpointOne
      1 0 0 0 := by
  unfold RightTransposeJacobiAt correctionFenceReducedEndpointZero
    correctionFenceReducedEndpointOne
  decide

/-- Consequently the unguarded full-coordinate family is not merely
unproved: it is refuted by a closed exact-rational computation. -/
theorem correctionFence_reduced_fullCoordinateFamily_is_false :
    ¬ RightTransposeJacobiFullCoordinateFamily
      correctionFenceReducedEndpointZero correctionFenceReducedEndpointZero
      correctionFenceReducedEndpointOne := by
  intro hfull
  exact correctionFence_reduced_raw_row_endpoint_alias_counterexample
    (hfull 1 0 0 0)

/-- The first raw mutual-measure shell carrying this reduced endpoint is
therefore false as currently stated. -/
theorem fullJacobiAtMeasure_four_is_false :
    ¬ FullJacobiAtMeasure 4 := by
  intro hshell
  exact correctionFence_reduced_fullCoordinateFamily_is_false
    (hshell 2 1 1 2 correctionFenceReducedEndpointZero
      correctionFenceReducedEndpointZero correctionFenceReducedEndpointOne
      rfl)

/-- In particular, no unconditional theorem with the old unguarded
all-measure conclusion can be constructed. -/
theorem rawFullCoordinateFamily_all_measures_is_false :
    ¬ (∀ a b c d (qm q qp : FixedRightCGChannel a b c d),
      RightTransposeJacobiFullCoordinateFamily qm q qp) := by
  intro hall
  exact correctionFence_reduced_fullCoordinateFamily_is_false
    (hall 2 1 1 2 correctionFenceReducedEndpointZero
      correctionFenceReducedEndpointZero correctionFenceReducedEndpointOne)

/-- The correct finite-dimensional invariant: every coordinate lies in the
four monomial degree boxes. -/
def RightTransposeJacobiPhysicalCoordinateFamily {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) : Prop :=
  ∀ i j l s, i < a + 1 → j < b + 1 → l < c + 1 → s < d + 1 →
    RightTransposeJacobiAt qm q qp i j l s

/-- Physical endpoint analogue of the preceding invariant. -/
def RightEndpointTransposeJacobiPhysicalCoordinateFamily {a b c d : Nat}
    (q qp : FixedRightCGChannel a b c d) : Prop :=
  ∀ i j l s, i < a + 1 → j < b + 1 → l < c + 1 → s < d + 1 →
    RightEndpointTransposeJacobiAt q qp i j l s

/-- Endpoint-aware finite-dimensional Jacobi invariant.  Natural
subtraction must not be used to manufacture a lower neighbour at `p=0`, and
rows are asserted only for genuinely adjacent channels. -/
def RightJacobiPhysicalCoordinateFamily {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) : Prop :=
  (q.p = 0 → qp.p = q.p + 1 →
      RightEndpointTransposeJacobiPhysicalCoordinateFamily q qp) ∧
    (0 < q.p → q.p = qm.p + 1 → qp.p = q.p + 1 →
      RightTransposeJacobiPhysicalCoordinateFamily qm q qp)

theorem rightJacobiPhysical_of_endpoint {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp0 : q.p = 0)
    (_hnext : qp.p = q.p + 1)
    (hendpoint : RightEndpointTransposeJacobiPhysicalCoordinateFamily q qp) :
    RightJacobiPhysicalCoordinateFamily qm q qp := by
  constructor
  · intro _ _
    exact hendpoint
  · intro hp
    have : False := by omega
    exact False.elim this

theorem rightJacobiPhysical_of_positive {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (hnext : qp.p = q.p + 1)
    (hfull : RightTransposeJacobiPhysicalCoordinateFamily qm q qp) :
    RightJacobiPhysicalCoordinateFamily qm q qp := by
  constructor
  · intro hp0
    have : False := by omega
    exact False.elim this
  · intro _ _ _
    exact hfull

theorem endpointPhysical_of_rightJacobiPhysical {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp0 : q.p = 0)
    (hnext : qp.p = q.p + 1)
    (hfamily : RightJacobiPhysicalCoordinateFamily qm q qp) :
    RightEndpointTransposeJacobiPhysicalCoordinateFamily q qp :=
  hfamily.1 hp0 hnext

theorem transposePhysical_of_rightJacobiPhysical {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (hnext : qp.p = q.p + 1)
    (hfamily : RightJacobiPhysicalCoordinateFamily qm q qp) :
    RightTransposeJacobiPhysicalCoordinateFamily qm q qp :=
  hfamily.2 hp hprev hnext

/-- Physical Jacobi information strictly below one label measure. -/
def PhysicalJacobiBelow (N : Nat) : Prop :=
  ∀ a b c d (qm q qp : FixedRightCGChannel a b c d),
    rightLabelMeasure a b c < N →
    RightJacobiPhysicalCoordinateFamily qm q qp

/-- Physical Jacobi information on one label-measure shell. -/
def PhysicalJacobiAtMeasure (N : Nat) : Prop :=
  ∀ a b c d (qm q qp : FixedRightCGChannel a b c d),
    rightLabelMeasure a b c = N →
    RightJacobiPhysicalCoordinateFamily qm q qp

/-- Physical Jacobi information through a closed measure interval. -/
def PhysicalJacobiThrough (N : Nat) : Prop :=
  ∀ a b c d (qm q qp : FixedRightCGChannel a b c d),
    rightLabelMeasure a b c ≤ N →
    RightJacobiPhysicalCoordinateFamily qm q qp

/-- Construct the closed physical-measure interval from a sound shell step. -/
theorem physicalJacobiThrough_of_measure_step
    (hstep : ∀ N, PhysicalJacobiBelow N → PhysicalJacobiAtMeasure N) :
    ∀ N, PhysicalJacobiThrough N
  | 0 => by
      intro a b c d qm q qp hmeasure
      apply hstep 0 (by
        intro a' b' c' d' qm' q' qp' hlt
        have hfalse : False := by
          unfold rightLabelMeasure at hlt
          omega
        exact False.elim hfalse) a b c d qm q qp
      omega
  | N + 1 => by
      have hN := physicalJacobiThrough_of_measure_step hstep N
      intro a b c d qm q qp hmeasure
      by_cases hsmall : rightLabelMeasure a b c ≤ N
      · exact hN a b c d qm q qp hsmall
      · apply hstep (N + 1) (by
          intro a' b' c' d' qm' q' qp' hlt
          exact hN a' b' c' d' qm' q' qp' (by omega))
            a b c d qm q qp
        omega

/-- Constructive all-measure induction for the corrected physical family. -/
theorem physicalJacobi_all_of_measure_step
    (hstep : ∀ N, PhysicalJacobiBelow N → PhysicalJacobiAtMeasure N) :
    ∀ a b c d (qm q qp : FixedRightCGChannel a b c d),
      RightJacobiPhysicalCoordinateFamily qm q qp := by
  intro a b c d qm q qp
  exact physicalJacobiThrough_of_measure_step hstep
    (rightLabelMeasure a b c) a b c d qm q qp (by omega)

private theorem same_product_of_left_zero (A X Y : Q') (hA : A ≈ 0) :
    A * X ≈ A * Y := by
  exact Q'.eqv_trans _ 0 _
    (Q'.eqv_trans _ (0 * X) _
      (Q'.mul_eqv_congr_right _ _ X hA) (Q'.zero_mul_eqv X))
    (Q'.eqv_symm
      (Q'.eqv_trans _ (0 * Y) _
        (Q'.mul_eqv_congr_right _ _ Y hA) (Q'.zero_mul_eqv Y)))

/-- Split Omega congruence needs a reduced row only at the two coordinates
that have nonzero lift weights.  The apparent missing boundary rows are
annihilated by `c-l` and `b-j`, respectively. -/
theorem omegaLiftSplit_congr_physical (b c : Nat)
    (x y : Nat → Nat → Nat → Q') (i j l : Nat)
    (hj : j < b + 1) (hl : l < c + 1)
    (hfirst : l < c → x i (j - 1) l ≈ y i (j - 1) l)
    (hsecond : j < b → x i j (l - 1) ≈ y i j (l - 1)) :
    omegaLiftSplit b c x i j l ≈ omegaLiftSplit b c y i j l := by
  unfold omegaLiftSplit
  apply Q'.add_eqv_congr'
  · by_cases hcl : l < c
    · exact Q'.mul_eqv_congr_left _ _ _ (hfirst hcl)
    · have hzero : c - l = 0 := by omega
      apply same_product_of_left_zero
      simpa only [hzero] using
        Q'.mul_zero_eqv (Q'.ofNat j)
  · apply Q'.neg_eqv_congr
    by_cases hjb : j < b
    · exact Q'.mul_eqv_congr_left _ _ _ (hsecond hjb)
    · have hzero : b - j = 0 := by omega
      apply same_product_of_left_zero
      have hcoeff : Q'.ofNat (b - j) * Q'.ofNat l ≈ 0 := by
        simpa only [hzero] using Q'.zero_mul_eqv (Q'.ofNat l)
      exact hcoeff

private theorem insert_zero_lower (X Y Z : Q') :
    Y + Z ≈ (0 : Q') * X + Y + Z := by
  have hzero : (0 : Q') * X + Y ≈ Y :=
    Q'.eqv_trans _ (0 + Y) _
      (Q'.add_eqv_congr' (Q'.zero_mul_eqv X) (Q'.eqv_refl Y))
      (Q'.eqv_of_eq (Q'.zero_add' Y))
  exact Q'.eqv_symm
    (Q'.add_eqv_congr' hzero (Q'.eqv_refl Z))

private theorem zero_carrier_change (X Y : Q') :
    (0 : Q') * X ≈ 0 * Y :=
  Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv X)
    (Q'.eqv_symm (Q'.zero_mul_eqv Y))

/-- A physical reduced endpoint family suffices to lift every physical row
at original inner order one.  Unlike the older endpoint lift, this theorem
does not demand false rows outside the finite degree boxes. -/
theorem liftedReducedRightTransposeJacobiAt_of_endpoint_physicalFamily
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hpp : 0 < qp.p) (hp1 : q.p = 1)
    (i j l s : Nat)
    (hi : i < a + 1) (hj : j < b + 1)
    (hl : l < c + 1) (hs : s < d + 1)
    (hendpoint : RightEndpointTransposeJacobiPhysicalCoordinateFamily
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel qp hpp)) :
    LiftedReducedRightTransposeJacobiAt qm q qp i j l s := by
  have hb : 0 < b := by
    have hq := Nat.le_min.mp q.p_le
    omega
  have hc : 0 < c := by
    have hq := Nat.le_min.mp q.p_le
    omega
  let rowRhs : Nat → Nat → Nat → Q' := fun u v w =>
    jacobiDiagonal a (b - 1) (c - 1) d 0 *
        peeledRightCoefficient q s u v w +
      jacobiBackward a (b - 1) (c - 1) d 1 *
        peeledRightCoefficient qp s u v w
  have hrow (u v w : Nat)
      (hendpointAt : RightEndpointTransposeJacobiAt
        (reducePositiveInnerRightChannel q hp)
        (reducePositiveInnerRightChannel qp hpp) u v w s) :
      firstPairExchange3 a (b - 1) (peeledRightCoefficient q s) u v w ≈
        rowRhs u v w := by
    unfold RightEndpointTransposeJacobiAt at hendpointAt
    simpa only [rowRhs, peeledRightCoefficient, reduced_intermediate_eq,
      reduced_inner_order_eq, hp1, Nat.reduceSubDiff, Nat.zero_add] using
        hendpointAt
  have hlift := omegaLiftSplit_congr_physical b c
    (firstPairExchange3 a (b - 1) (peeledRightCoefficient q s)) rowRhs
    i j l hj hl
    (fun hcl => hrow i (j - 1) l
      (hendpoint i (j - 1) l s hi (by omega) (by omega) hs))
    (fun hjb => hrow i j (l - 1)
      (hendpoint i j (l - 1) s hi (by omega) (by omega) hs))
  let threeRhs : Nat → Nat → Nat → Q' := fun u v w =>
    (0 : Q') * peeledRightCoefficient qm s u v w +
      jacobiDiagonal a (b - 1) (c - 1) d 0 *
        peeledRightCoefficient q s u v w +
      jacobiBackward a (b - 1) (c - 1) d 1 *
        peeledRightCoefficient qp s u v w
  have htwoThree : omegaLiftSplit b c rowRhs i j l ≈
      omegaLiftSplit b c threeRhs i j l := by
    apply omegaLiftSplit_congr_physical b c rowRhs threeRhs i j l hj hl
    · intro _
      exact insert_zero_lower
        (peeledRightCoefficient qm s i (j - 1) l)
        (jacobiDiagonal a (b - 1) (c - 1) d 0 *
          peeledRightCoefficient q s i (j - 1) l)
        (jacobiBackward a (b - 1) (c - 1) d 1 *
          peeledRightCoefficient qp s i (j - 1) l)
    · intro _
      exact insert_zero_lower
        (peeledRightCoefficient qm s i j (l - 1))
        (jacobiDiagonal a (b - 1) (c - 1) d 0 *
          peeledRightCoefficient q s i j (l - 1))
        (jacobiBackward a (b - 1) (c - 1) d 1 *
          peeledRightCoefficient qp s i j (l - 1))
  have hlinear := omegaLiftSplit_three_term b c
    (0 : Q') (jacobiDiagonal a (b - 1) (c - 1) d 0)
    (jacobiBackward a (b - 1) (c - 1) d 1)
    (peeledRightCoefficient qm s) (peeledRightCoefficient q s)
    (peeledRightCoefficient qp s) i j l
  have hcarriers :
      (0 : Q') * omegaLiftSplit b c (peeledRightCoefficient qm s) i j l +
          jacobiDiagonal a (b - 1) (c - 1) d 0 *
            omegaLiftSplit b c (peeledRightCoefficient q s) i j l +
          jacobiBackward a (b - 1) (c - 1) d 1 *
            omegaLiftSplit b c (peeledRightCoefficient qp s) i j l ≈
        (0 : Q') *
            triRight a b c d qm.intermediate
              (mono i) (mono j) (mono l) s +
          jacobiDiagonal a (b - 1) (c - 1) d 0 *
            triRight a b c d q.intermediate
              (mono i) (mono j) (mono l) s +
          jacobiBackward a (b - 1) (c - 1) d 1 *
            triRight a b c d qp.intermediate
              (mono i) (mono j) (mono l) s := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (zero_carrier_change _ _)
        (Q'.mul_eqv_congr_left _ _ _
          (peeled_omegaLiftSplit_eq_triRight q hp i j l s)))
      (Q'.mul_eqv_congr_left _ _ _
        (peeled_omegaLiftSplit_eq_triRight qp hpp i j l s))
  unfold LiftedReducedRightTransposeJacobiAt
  simp only [hp1, reducedLowerCoefficient, Nat.reduceLT, if_false,
    Nat.reduceSubDiff]
  exact Q'.eqv_trans _ _ _ hlift
    (Q'.eqv_trans _ _ _ htwoThree
      (Q'.eqv_trans _ _ _ hlinear hcarriers))

/-- The same local-weight argument repairs the ordinary three-carrier lift
at inner order at least two. -/
theorem liftedReducedRightTransposeJacobiAt_of_reduced_physicalFamily
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hm : 0 < qm.p) (hp : 0 < q.p) (hpp : 0 < qp.p)
    (hp2 : 1 < q.p) (i j l s : Nat)
    (hi : i < a + 1) (hj : j < b + 1)
    (hl : l < c + 1) (hs : s < d + 1)
    (hreduced : RightTransposeJacobiPhysicalCoordinateFamily
      (reducePositiveInnerRightChannel qm hm)
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel qp hpp)) :
    LiftedReducedRightTransposeJacobiAt qm q qp i j l s := by
  have hb : 0 < b := by
    have hq := Nat.le_min.mp q.p_le
    omega
  have hc : 0 < c := by
    have hq := Nat.le_min.mp q.p_le
    omega
  let rowRhs : Nat → Nat → Nat → Q' := fun u v w =>
    reducedLowerCoefficient a b c d q.p *
        peeledRightCoefficient qm s u v w +
      jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1) *
        peeledRightCoefficient q s u v w +
      jacobiBackward a (b - 1) (c - 1) d q.p *
        peeledRightCoefficient qp s u v w
  have hrow (u v w : Nat)
      (hreducedAt : RightTransposeJacobiAt
        (reducePositiveInnerRightChannel qm hm)
        (reducePositiveInnerRightChannel q hp)
        (reducePositiveInnerRightChannel qp hpp) u v w s) :
      firstPairExchange3 a (b - 1) (peeledRightCoefficient q s) u v w ≈
        rowRhs u v w := by
    unfold RightTransposeJacobiAt at hreducedAt
    have hsub : (q.p - 1) - 1 = q.p - 2 := by omega
    have hsucc : q.p - 1 + 1 = q.p := by omega
    simpa only [rowRhs, peeledRightCoefficient, reduced_intermediate_eq,
      reduced_inner_order_eq, hsub, hsucc, reducedLowerCoefficient,
      if_pos hp2] using hreducedAt
  have hlift := omegaLiftSplit_congr_physical b c
    (firstPairExchange3 a (b - 1) (peeledRightCoefficient q s)) rowRhs
    i j l hj hl
    (fun hcl => hrow i (j - 1) l
      (hreduced i (j - 1) l s hi (by omega) (by omega) hs))
    (fun hjb => hrow i j (l - 1)
      (hreduced i j (l - 1) s hi (by omega) (by omega) hs))
  have hlinear := omegaLiftSplit_three_term b c
    (reducedLowerCoefficient a b c d q.p)
    (jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1))
    (jacobiBackward a (b - 1) (c - 1) d q.p)
    (peeledRightCoefficient qm s) (peeledRightCoefficient q s)
    (peeledRightCoefficient qp s) i j l
  have hcarriers :
      reducedLowerCoefficient a b c d q.p *
            omegaLiftSplit b c (peeledRightCoefficient qm s) i j l +
          jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1) *
            omegaLiftSplit b c (peeledRightCoefficient q s) i j l +
          jacobiBackward a (b - 1) (c - 1) d q.p *
            omegaLiftSplit b c (peeledRightCoefficient qp s) i j l ≈
        reducedLowerCoefficient a b c d q.p *
            triRight a b c d qm.intermediate
              (mono i) (mono j) (mono l) s +
          jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1) *
            triRight a b c d q.intermediate
              (mono i) (mono j) (mono l) s +
          jacobiBackward a (b - 1) (c - 1) d q.p *
            triRight a b c d qp.intermediate
              (mono i) (mono j) (mono l) s := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _
          (peeled_omegaLiftSplit_eq_triRight qm hm i j l s))
        (Q'.mul_eqv_congr_left _ _ _
          (peeled_omegaLiftSplit_eq_triRight q hp i j l s)))
      (Q'.mul_eqv_congr_left _ _ _
        (peeled_omegaLiftSplit_eq_triRight qp hpp i j l s))
  unfold LiftedReducedRightTransposeJacobiAt
  exact Q'.eqv_trans _ _ _ hlift
    (Q'.eqv_trans _ _ _ hlinear hcarriers)

/-- Specialize a lower-measure physical hypothesis to the common positive
inner peel. -/
theorem reducedRightJacobiPhysical_of_physicalJacobiBelow
    (N : Nat) {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = N)
    (hm : 0 < qm.p) (hp : 0 < q.p) (hpp : 0 < qp.p)
    (hbelow : PhysicalJacobiBelow N) :
    RightJacobiPhysicalCoordinateFamily
      (reducePositiveInnerRightChannel qm hm)
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel qp hpp) := by
  have hq := Nat.le_min.mp q.p_le
  apply hbelow a (b - 1) (c - 1) d
    (reducePositiveInnerRightChannel qm hm)
    (reducePositiveInnerRightChannel q hp)
    (reducePositiveInnerRightChannel qp hpp)
  rw [← hmeasure]
  exact innerPeel_measure_lt a b c (by omega) (by omega)

/-- At original inner order one, the lower-measure endpoint-aware invariant
supplies precisely the two-carrier reduced family. -/
theorem reducedEndpointPhysical_of_physicalJacobiBelow
    (N : Nat) {a b c d : Nat}
    (q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = N)
    (hp : 0 < q.p) (hpp : 0 < qp.p) (hp1 : q.p = 1)
    (hnext : qp.p = q.p + 1)
    (hbelow : PhysicalJacobiBelow N) :
    RightEndpointTransposeJacobiPhysicalCoordinateFamily
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel qp hpp) := by
  have hq := Nat.le_min.mp q.p_le
  have hreduced : RightJacobiPhysicalCoordinateFamily
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel qp hpp) := by
    apply hbelow a (b - 1) (c - 1) d
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel qp hpp)
    rw [← hmeasure]
    exact innerPeel_measure_lt a b c (by omega) (by omega)
  apply endpointPhysical_of_rightJacobiPhysical
    (reducePositiveInnerRightChannel q hp)
    (reducePositiveInnerRightChannel q hp)
    (reducePositiveInnerRightChannel qp hpp) (by
      rw [reduced_inner_order_eq]
      omega) (by
      rw [reduced_inner_order_eq, reduced_inner_order_eq]
      omega) hreduced

/-- The corrected lower-measure invariant constructs every physical lifted
row, using the endpoint branch at `p=1` and the ordinary three-carrier branch
above it. -/
theorem liftedPhysicalFamily_of_physicalJacobiBelow
    (N : Nat) {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = N)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (hbelow : PhysicalJacobiBelow N) :
    ∀ i j l s, i < a + 1 → j < b + 1 → l < c + 1 → s < d + 1 →
      LiftedReducedRightTransposeJacobiAt qm q qp i j l s := by
  have hpp : 0 < qp.p := by omega
  intro i j l s hi hj hl hs
  by_cases hp1 : q.p = 1
  · apply liftedReducedRightTransposeJacobiAt_of_endpoint_physicalFamily
      qm q qp hp hpp hp1 i j l s hi hj hl hs
    exact reducedEndpointPhysical_of_physicalJacobiBelow
      N q qp hmeasure hp hpp hp1 hnext hbelow
  · have hp2 : 1 < q.p := by omega
    have hm : 0 < qm.p := by omega
    have hreduced := reducedRightJacobiPhysical_of_physicalJacobiBelow
      N qm q qp hmeasure hm hp hpp hbelow
    have hpositive :
        0 < (reducePositiveInnerRightChannel q hp).p := by
      rw [reduced_inner_order_eq]
      omega
    have hprevReduced :
        (reducePositiveInnerRightChannel q hp).p =
          (reducePositiveInnerRightChannel qm hm).p + 1 := by
      rw [reduced_inner_order_eq, reduced_inner_order_eq]
      omega
    have hnextReduced :
        (reducePositiveInnerRightChannel qp hpp).p =
          (reducePositiveInnerRightChannel q hp).p + 1 := by
      rw [reduced_inner_order_eq, reduced_inner_order_eq]
      omega
    apply liftedReducedRightTransposeJacobiAt_of_reduced_physicalFamily
      qm q qp hm hp hpp hp2 i j l s hi hj hl hs
    exact transposePhysical_of_rightJacobiPhysical
      (reducePositiveInnerRightChannel qm hm)
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel qp hpp) hpositive hprevReduced
        hnextReduced hreduced

/-- Full physical Omega-correction data on one adjacent positive-order
block. -/
def OmegaCorrectionPhysicalCoordinateFamily {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) : Prop :=
  ∀ i j l s, i < a + 1 → j < b + 1 → l < c + 1 → s < d + 1 →
    OmegaCorrectionThreeCarrierAt qm q qp i j l s

/-- Lower-measure lifting plus a physical correction family closes a whole
positive-order block. -/
theorem rightJacobiPhysical_of_below_and_correction
    (N : Nat) {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = N)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (hbelow : PhysicalJacobiBelow N)
    (hcorrection : OmegaCorrectionPhysicalCoordinateFamily qm q qp) :
    RightJacobiPhysicalCoordinateFamily qm q qp := by
  apply rightJacobiPhysical_of_positive qm q qp hp hprev hnext
  intro i j l s hi hj hl hs
  apply rightTransposeJacobiAt_of_lifted_reduced_and_correction
    qm q qp hp i j l s (by omega)
  · exact liftedPhysicalFamily_of_physicalJacobiBelow
      N qm q qp hmeasure hp hprev hnext hbelow i j l s hi hj hl hs
  · exact hcorrection i j l s hi hj hl hs

/-- Sound shell step.  Its only inputs beyond lower measure are the exact
order-zero endpoint rows and the exact positive-order Omega corrections. -/
theorem physicalJacobiAtMeasure_of_endpoint_and_correction
    (N : Nat) (hbelow : PhysicalJacobiBelow N)
    (hendpoint : ∀ a b c d
      (q qp : FixedRightCGChannel a b c d),
      rightLabelMeasure a b c = N → q.p = 0 → qp.p = q.p + 1 →
      RightEndpointTransposeJacobiPhysicalCoordinateFamily q qp)
    (hcorrection : ∀ a b c d
      (qm q qp : FixedRightCGChannel a b c d),
      rightLabelMeasure a b c = N → 0 < q.p →
      q.p = qm.p + 1 → qp.p = q.p + 1 →
      OmegaCorrectionPhysicalCoordinateFamily qm q qp) :
    PhysicalJacobiAtMeasure N := by
  intro a b c d qm q qp hmeasure
  constructor
  · intro hp0 hnext
    exact hendpoint a b c d q qp hmeasure hp0 hnext
  · intro hp hprev hnext
    have hblock := rightJacobiPhysical_of_below_and_correction
      N qm q qp hmeasure hp hprev hnext hbelow
        (hcorrection a b c d qm q qp hmeasure hp hprev hnext)
    exact transposePhysical_of_rightJacobiPhysical
      qm q qp hp hprev hnext hblock

/-- All-measure closure in its strongest sound form: endpoint bases and
positive-order correction families at each shell imply every adjacent
physical Jacobi family. -/
theorem physicalJacobi_all_of_endpoint_and_correction_steps
    (hendpoint : ∀ N, PhysicalJacobiBelow N → ∀ a b c d
      (q qp : FixedRightCGChannel a b c d),
      rightLabelMeasure a b c = N → q.p = 0 → qp.p = q.p + 1 →
      RightEndpointTransposeJacobiPhysicalCoordinateFamily q qp)
    (hcorrection : ∀ N, PhysicalJacobiBelow N → ∀ a b c d
      (qm q qp : FixedRightCGChannel a b c d),
      rightLabelMeasure a b c = N → 0 < q.p →
      q.p = qm.p + 1 → qp.p = q.p + 1 →
      OmegaCorrectionPhysicalCoordinateFamily qm q qp) :
    ∀ a b c d (qm q qp : FixedRightCGChannel a b c d),
      RightJacobiPhysicalCoordinateFamily qm q qp := by
  apply physicalJacobi_all_of_measure_step
  intro N hbelow
  exact physicalJacobiAtMeasure_of_endpoint_and_correction N hbelow
    (hendpoint N hbelow) (hcorrection N hbelow)

/-- The reduced correction-fence endpoint is exact on its complete physical
coordinate box. -/
theorem correctionFence_reduced_endpoint_physicalCoordinateFamily :
    RightEndpointTransposeJacobiPhysicalCoordinateFamily
      correctionFenceReducedEndpointZero correctionFenceReducedEndpointOne := by
  intro i j l s hi hj hl hs
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj' : j = 0 ∨ j = 1 := by omega
  have hl' : l = 0 ∨ l = 1 := by omega
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases hi' with rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl <;>
    rcases hl' with rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl <;>
    unfold RightEndpointTransposeJacobiAt correctionFenceReducedEndpointZero
      correctionFenceReducedEndpointOne <;> decide

/-- Endpoint-aware package on the reduced measure-four block. -/
theorem correctionFence_reduced_rightJacobiPhysicalCoordinateFamily :
    RightJacobiPhysicalCoordinateFamily correctionFenceReducedEndpointZero
      correctionFenceReducedEndpointZero correctionFenceReducedEndpointOne :=
  rightJacobiPhysical_of_endpoint correctionFenceReducedEndpointZero
    correctionFenceReducedEndpointZero correctionFenceReducedEndpointOne
    rfl rfl correctionFence_reduced_endpoint_physicalCoordinateFamily

/-- At the original measure-six block the lifted peeled row is exact on the
whole physical box.  This is the guarded endpoint replacement for the false
global congruence premise. -/
theorem correctionFence_liftedReduced_physicalCoordinateFamily :
    ∀ i j l s, i < 3 → j < 3 → l < 3 → s < 3 →
      LiftedReducedRightTransposeJacobiAt correctionFenceLower
        correctionFenceMiddle correctionFenceUpper i j l s := by
  intro i j l s hi hj hl hs
  apply liftedReducedRightTransposeJacobiAt_of_endpoint_physicalFamily
    correctionFenceLower correctionFenceMiddle correctionFenceUpper
      (by decide) (by decide) (by decide) i j l s hi hj hl hs
  simpa only [correctionFenceReducedEndpointZero,
    correctionFenceReducedEndpointOne] using
      correctionFence_reduced_endpoint_physicalCoordinateFamily

/-- The measure-six order-zero correction base now feeds the Jacobi
induction step at every physical coordinate. -/
theorem correctionFence_rightTransposeJacobi_physicalCoordinateFamily :
    RightTransposeJacobiPhysicalCoordinateFamily correctionFenceLower
      correctionFenceMiddle correctionFenceUpper := by
  intro i j l s hi hj hl hs
  apply rightTransposeJacobiAt_of_lifted_reduced_and_correction
    correctionFenceLower correctionFenceMiddle correctionFenceUpper
      (by decide) i j l s (by omega)
  · exact correctionFence_liftedReduced_physicalCoordinateFamily
      i j l s hi hj hl hs
  · exact correctionFence_mutualMeasureBase.2.2.2 i j l s hi hj hl hs

/-- Endpoint-aware package on the original positive-order block. -/
theorem correctionFence_rightJacobiPhysicalCoordinateFamily :
    RightJacobiPhysicalCoordinateFamily correctionFenceLower
      correctionFenceMiddle correctionFenceUpper :=
  rightJacobiPhysical_of_positive correctionFenceLower correctionFenceMiddle
    correctionFenceUpper (by decide) (by decide) (by decide)
      correctionFence_rightTransposeJacobi_physicalCoordinateFamily

/-- Integrated boundary package: measure, upper-order-zero fence, all
previous correction bases, and the complete physical Jacobi family. -/
theorem correctionFence_mutualMeasurePhysicalBase :
    rightLabelMeasure 2 2 2 = 6 ∧ correctionFenceUpper.r = 0 ∧
    PositiveCorrectionBaseRegimes correctionFenceLower
      correctionFenceMiddle correctionFenceUpper ∧
    RightJacobiPhysicalCoordinateFamily correctionFenceLower
      correctionFenceMiddle correctionFenceUpper := by
  exact ⟨correctionFence_mutualMeasureBase.1,
    correctionFence_mutualMeasureBase.2.1,
    correctionFence_mutualMeasureBase.2.2.1,
    correctionFence_rightJacobiPhysicalCoordinateFamily⟩

end YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary

#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.correctionFence_reduced_endpoint_unphysical_counterexample
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.correctionFence_reduced_raw_row_endpoint_alias_counterexample
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.correctionFence_reduced_fullCoordinateFamily_is_false
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.fullJacobiAtMeasure_four_is_false
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.rawFullCoordinateFamily_all_measures_is_false
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.physicalJacobiThrough_of_measure_step
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.physicalJacobi_all_of_measure_step
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.omegaLiftSplit_congr_physical
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.liftedReducedRightTransposeJacobiAt_of_endpoint_physicalFamily
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.liftedReducedRightTransposeJacobiAt_of_reduced_physicalFamily
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.reducedRightJacobiPhysical_of_physicalJacobiBelow
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.reducedEndpointPhysical_of_physicalJacobiBelow
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.liftedPhysicalFamily_of_physicalJacobiBelow
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.rightJacobiPhysical_of_below_and_correction
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.physicalJacobiAtMeasure_of_endpoint_and_correction
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.physicalJacobi_all_of_endpoint_and_correction_steps
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.correctionFence_reduced_endpoint_physicalCoordinateFamily
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.correctionFence_reduced_rightJacobiPhysicalCoordinateFamily
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.correctionFence_liftedReduced_physicalCoordinateFamily
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.correctionFence_rightTransposeJacobi_physicalCoordinateFamily
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.correctionFence_rightJacobiPhysicalCoordinateFamily
#print axioms YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary.correctionFence_mutualMeasurePhysicalBase
