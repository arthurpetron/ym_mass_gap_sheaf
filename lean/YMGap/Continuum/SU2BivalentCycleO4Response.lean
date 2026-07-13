/-
# Same-state O(4) response on globally projected bivalent cycles

The one-link packet response is not by itself the state of a closed shared-link
cycle: gauge gluing keeps a common irrep label and the unique global vacuum
must be removed.  This module first constructs a normalized positive packet
functional from any explicit finite nonnegative spectral weight with positive
partition.  It then repeats the directional response construction for that
same state and instantiates it with the globally projected bivalent-cycle
weights.

For the checked two-link bigon the positivity witness is derived from the exact
projected norm `1`.  Thus the quarter-turn response here uses the corrected
gauge-compatible state in which the screened vacuum has already been removed.

Honest scope: this closes finite bivalent cycles.  Simultaneous gluing of
trivalent and higher-valence cells still needs the label-dependent
intertwiner/F-move calculus, and the lattice quarter-turn is not a continuum
family of physical O(4) rotations.
-/

import YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization
import YMGap.Continuum.SU2FiniteCharacterPacketO4Response

namespace YMGap.Continuum.SU2BivalentCycleO4Response

set_option maxHeartbeats 900000
set_option maxRecDepth 14000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RegularFunctional
open YMGap.Continuum.RegularLinearScalingLimit
open YMGap.Continuum.O4RestorationAF
open YMGap.Continuum.O4ObservableSymmetryBridge
open YMGap.Continuum.O4FiniteLatticeResponse
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketO4Response
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum
open YMGap.Continuum.SU2GlobalVacuumCycleQuotient
open YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, zero_num_cast, zero_den_cast, one_num_cast,
               one_den_cast, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## 1. A normalized positive functional from exact finite weights -/

/-- Content-bearing finite spectral weights, including their positive
normalizing partition as data. -/
structure PositivePacketWeight (N : Nat) : Type where
  weight : Nat -> Q'
  weight_nonneg : forall s, (0 : Q') <= weight s
  partition_pos : (0 : Q') < fsum weight (N + 1)

def weightedMoment {N : Nat} (W : PositivePacketWeight N)
    (P : CharacterPacket N) : Q' :=
  fsum (fun s => W.weight s * coeffAt P s) (N + 1)

def weightedExpectation {N : Nat} (W : PositivePacketWeight N)
    (P : CharacterPacket N) : Q' :=
  Q'.divPos (weightedMoment W P) (fsum W.weight (N + 1)) W.partition_pos

theorem weightedMoment_zero {N : Nat} (W : PositivePacketWeight N) :
    weightedMoment W (spectralZero N) ≈ 0 := by
  apply FusionQuotientCollapse.fsum_zero_below
  intro s hs
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (W.weight s) _ _ (coeffAt_spectralZero s))
    (Q'.mul_zero_eqv (W.weight s))

theorem weightedMoment_one {N : Nat} (W : PositivePacketWeight N) :
    weightedMoment W (spectralOne N) ≈ fsum W.weight (N + 1) := by
  unfold weightedMoment
  exact CubeRatioBounds.fsum_eqv_congr_lt _ _ (N + 1) (fun s hs =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (W.weight s) _ _
        (coeffAt_spectralOne_of_lt hs))
      (Q'.mul_one_eqv (W.weight s)))

theorem weightedMoment_add {N : Nat} (W : PositivePacketWeight N)
    (P Q : CharacterPacket N) :
    weightedMoment W (spectralAdd P Q) ≈
      weightedMoment W P + weightedMoment W Q := by
  unfold weightedMoment
  refine Q'.eqv_trans _
    (fsum (fun s => W.weight s * coeffAt P s +
      W.weight s * coeffAt Q s) (N + 1)) _ ?_ ?_
  · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (W.weight s) _ _
          (coeffAt_spectralAdd P Q s))
        (Q'.mul_add_eqv (W.weight s) (coeffAt P s) (coeffAt Q s))) (N + 1)
  · exact CubeRatioBounds.fsum_add _ _ (N + 1)

theorem weightedMoment_scale {N : Nat} (W : PositivePacketWeight N)
    (q : Q') (P : CharacterPacket N) :
    weightedMoment W (spectralScale q P) ≈ q * weightedMoment W P := by
  unfold weightedMoment
  refine Q'.eqv_trans _
    (fsum (fun s => q * (W.weight s * coeffAt P s)) (N + 1)) _ ?_ ?_
  · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (W.weight s) _ _
          (coeffAt_spectralScale q P s))
        (by ring_qeqv)) (N + 1)
  · exact Q'.eqv_symm (CubeRatioBounds.fsum_const_mul q _ (N + 1))

theorem weightedExpectation_zero {N : Nat} (W : PositivePacketWeight N) :
    weightedExpectation W (spectralZero N) ≈ 0 := by
  unfold weightedExpectation Q'.divPos
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (weightedMoment_zero W))
    (Q'.zero_mul_eqv _)

theorem weightedExpectation_one {N : Nat} (W : PositivePacketWeight N) :
    weightedExpectation W (spectralOne N) ≈ 1 := by
  unfold weightedExpectation Q'.divPos
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (weightedMoment_one W))
    (Q'.mul_recipPos_eqv _ W.partition_pos)

theorem weightedExpectation_add {N : Nat} (W : PositivePacketWeight N)
    (P Q : CharacterPacket N) :
    weightedExpectation W (spectralAdd P Q) ≈
      weightedExpectation W P + weightedExpectation W Q := by
  unfold weightedExpectation Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (weightedMoment_add W P Q)) ?_
  exact Q'.add_mul_eqv (weightedMoment W P) (weightedMoment W Q)
    (Q'.recipPos (fsum W.weight (N + 1)) W.partition_pos)

theorem weightedExpectation_scale {N : Nat} (W : PositivePacketWeight N)
    (q : Q') (P : CharacterPacket N) :
    weightedExpectation W (spectralScale q P) ≈
      q * weightedExpectation W P := by
  unfold weightedExpectation Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (weightedMoment_scale W q P)) ?_
  exact Q'.mul_assoc_eqv q (weightedMoment W P)
    (Q'.recipPos (fsum W.weight (N + 1)) W.partition_pos)

theorem weightedMoment_square_nonneg {N : Nat} (W : PositivePacketWeight N)
    (P : CharacterPacket N) :
    (0 : Q') <= weightedMoment W (spectralMul P P) := by
  let sqSum := fsum (fun s => W.weight s *
    (coeffAt P s * coeffAt P s)) (N + 1)
  have hs : (0 : Q') <= sqSum :=
    fsum_nonneg (fun s => Q'.mul_nonneg _ _ (W.weight_nonneg s)
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg (coeffAt P s))) (N + 1)
  have heq : weightedMoment W (spectralMul P P) ≈ sqSum := by
    unfold weightedMoment sqSum
    exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.mul_eqv_congr_left (W.weight s) _ _
        (coeffAt_spectralMul P P s)) (N + 1)
  exact Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv heq)

theorem weightedExpectation_square_nonneg {N : Nat}
    (W : PositivePacketWeight N) (P : CharacterPacket N) :
    (0 : Q') <= weightedExpectation W (spectralMul P P) := by
  unfold weightedExpectation Q'.divPos
  exact Q'.mul_nonneg _ _ (weightedMoment_square_nonneg W P)
    (Q'.le_of_lt (Q'.recipPos_pos _ W.partition_pos))

def weightedPacketFunctional {N : Nat} (W : PositivePacketWeight N) :
    QLinearFunctional (packetSpectralAlg N) where
  E := weightedExpectation W
  normalized := weightedExpectation_one W
  positive := weightedExpectation_square_nonneg W
  additive := weightedExpectation_add W
  homogeneous := weightedExpectation_scale W

/-! ## 2. Directional response for the same weighted state -/

def weightedDir4Eval {N : Nat} (W : PositivePacketWeight N)
    (o : PacketDir4 N) : Dir4Observable :=
  ⟨weightedExpectation W o.east, weightedExpectation W o.north,
    weightedExpectation W o.west, weightedExpectation W o.south⟩

theorem weightedDir4Eval_zero {N : Nat} (W : PositivePacketWeight N) :
    DirectionalEqv (weightedDir4Eval W (packetDir4Alg N).zero) dir4Alg.zero :=
  ⟨weightedExpectation_zero W, weightedExpectation_zero W,
    weightedExpectation_zero W, weightedExpectation_zero W⟩

theorem weightedDir4Eval_one {N : Nat} (W : PositivePacketWeight N) :
    DirectionalEqv (weightedDir4Eval W (packetDir4Alg N).one) dir4Alg.one :=
  ⟨weightedExpectation_one W, weightedExpectation_one W,
    weightedExpectation_one W, weightedExpectation_one W⟩

theorem weightedDir4Eval_add {N : Nat} (W : PositivePacketWeight N)
    (a b : PacketDir4 N) :
    DirectionalEqv
      (weightedDir4Eval W ((packetDir4Alg N).add a b))
      (dir4Alg.add (weightedDir4Eval W a) (weightedDir4Eval W b)) :=
  ⟨weightedExpectation_add W a.east b.east,
    weightedExpectation_add W a.north b.north,
    weightedExpectation_add W a.west b.west,
    weightedExpectation_add W a.south b.south⟩

theorem weightedDir4Eval_smul {N : Nat} (W : PositivePacketWeight N)
    (q : Q') (a : PacketDir4 N) :
    DirectionalEqv
      (weightedDir4Eval W ((packetDir4Alg N).smul q a))
      (dir4Alg.smul q (weightedDir4Eval W a)) :=
  ⟨weightedExpectation_scale W q a.east,
    weightedExpectation_scale W q a.north,
    weightedExpectation_scale W q a.west,
    weightedExpectation_scale W q a.south⟩

theorem weightedDir4Eval_quarterTurn {N : Nat} (W : PositivePacketWeight N)
    (o : PacketDir4 N) :
    weightedDir4Eval W ((packetQuarterTurnHom N).map o) =
      quarterTurnHom.map (weightedDir4Eval W o) := rfl

def weightedDir4Functional {N : Nat} (W : PositivePacketWeight N) (j : Nat) :
    QLinearFunctional (packetDir4Alg N) where
  E := fun o => (dir4Functional j).E (weightedDir4Eval W o)
  normalized := Q'.eqv_trans _ _ _
    (dir4Functional_congr j (weightedDir4Eval_one W))
    (dir4Functional j).normalized
  positive := by
    intro o
    let delta := half ^ j * O4FiniteLatticeResponse.eighth
    let a := weightedExpectation W (spectralMul o.east o.east)
    let b := weightedExpectation W (spectralMul o.north o.north)
    let c := weightedExpectation W (spectralMul o.west o.west)
    let d := weightedExpectation W (spectralMul o.south o.south)
    have ha : (0 : Q') <= a := weightedExpectation_square_nonneg W o.east
    have hb : (0 : Q') <= b := weightedExpectation_square_nonneg W o.north
    have hc : (0 : Q') <= c := weightedExpectation_square_nonneg W o.west
    have hd : (0 : Q') <= d := weightedExpectation_square_nonneg W o.south
    have hdelta0 : (0 : Q') <= delta :=
      Q'.mul_nonneg _ _ (Q'.pow_nonneg half half_nonneg j)
        O4FiniteLatticeResponse.eighth_nonneg
    have hp1 : half ^ j <= (1 : Q') := by
      simpa using (half_pow_antitone 0 j (Nat.zero_le j))
    have hdelta8 : delta <= O4FiniteLatticeResponse.eighth :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ O4FiniteLatticeResponse.eighth
          hp1 O4FiniteLatticeResponse.eighth_nonneg)
        (Q'.le_of_eqv (Q'.one_mul_eqv O4FiniteLatticeResponse.eighth))
    have hdelta4 : delta <= quarter :=
      Q'.le_trans' _ _ _ hdelta8 eighth_le_quarter
    have hwest : (0 : Q') <= quarter + (-delta) :=
      Q'.sub_nonneg_of_le hdelta4
    have heast : (0 : Q') <= quarter + delta :=
      Q'.zero_le_add _ _ quarter_nonneg hdelta0
    let weighted :=
      (((quarter + delta) * a + quarter * b) +
        (quarter + (-delta)) * c) + quarter * d
    have hw : (0 : Q') <= weighted :=
      Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ heast ha)
            (Q'.mul_nonneg _ _ quarter_nonneg hb))
          (Q'.mul_nonneg _ _ hwest hc))
        (Q'.mul_nonneg _ _ quarter_nonneg hd)
    have heq :
        (dir4Functional j).E
          (weightedDir4Eval W
            ((packetDir4Alg N).mul ((packetDir4Alg N).star o) o)) ≈
          weighted := by
      dsimp [packetDir4Alg, weightedDir4Eval, dir4Functional,
        isotropicPart, directionalHarmonic, delta, a, b, c, d, weighted]
      ring_qeqv
    exact Q'.le_trans' _ _ _ hw (Q'.ge_of_eqv heq)
  additive := by
    intro a b
    exact Q'.eqv_trans _ _ _
      (dir4Functional_congr j (weightedDir4Eval_add W a b))
      ((dir4Functional j).additive (weightedDir4Eval W a)
        (weightedDir4Eval W b))
  homogeneous := by
    intro q a
    exact Q'.eqv_trans _ _ _
      (dir4Functional_congr j (weightedDir4Eval_smul W q a))
      ((dir4Functional j).homogeneous q (weightedDir4Eval W a))

def weightedDir4Scaling {N : Nat} (W : PositivePacketWeight N) :
    LinearScalingLimitModulus (packetDir4Alg N) where
  atSpacing := weightedDir4Functional W
  modOf := fun o => by
    change RegularCReal.ModCauchy
      (fun j => RegularCReal.ofQ'
        ((dir4Functional j).E (weightedDir4Eval W o)))
    exact dir4Scaling.modOf (weightedDir4Eval W o)

def weightedDir4Response {N : Nat} (W : PositivePacketWeight N)
    (o : PacketDir4 N) : Q' :=
  dir4Response (weightedDir4Eval W o)

theorem weightedDir4Response_nonneg {N : Nat} (W : PositivePacketWeight N)
    (o : PacketDir4 N) : (0 : Q') <= weightedDir4Response W o :=
  dir4Response_nonneg (weightedDir4Eval W o)

def weightedQuarterTurnResponse {N : Nat} (W : PositivePacketWeight N) :
    ActionDecayControlledResponse (packetDir4Alg N) (weightedDir4Scaling W)
      halfScalingDecay where
  action := packetQuarterTurnAction N
  response := weightedDir4Response W
  response_nonneg := weightedDir4Response_nonneg W
  stage_upper := by
    intro o j
    change
      (dir4Functional j).E
          (weightedDir4Eval W ((packetQuarterTurnHom N).map o)) <=
        (dir4Functional j).E (weightedDir4Eval W o) +
          dir4Response (weightedDir4Eval W o) * breakCoeff halfScalingDecay j
    rw [weightedDir4Eval_quarterTurn]
    exact finiteQuarterTurnResponse.stage_upper (weightedDir4Eval W o) j
  stage_lower := by
    intro o j
    change
      (dir4Functional j).E (weightedDir4Eval W o) <=
        (dir4Functional j).E
            (weightedDir4Eval W ((packetQuarterTurnHom N).map o)) +
          dir4Response (weightedDir4Eval W o) * breakCoeff halfScalingDecay j
    rw [weightedDir4Eval_quarterTurn]
    exact finiteQuarterTurnResponse.stage_lower (weightedDir4Eval W o) j

theorem weightedQuarterTurn_same_state_response {N : Nat}
    (W : PositivePacketWeight N) (o : PacketDir4 N) (j : Nat) :
    ((weightedDir4Scaling W).atSpacing j).E
        ((packetQuarterTurnHom N).map o) <=
      ((weightedDir4Scaling W).atSpacing j).E o +
        weightedDir4Response W o * breakCoeff halfScalingDecay j
    /\
    ((weightedDir4Scaling W).atSpacing j).E o <=
      ((weightedDir4Scaling W).atSpacing j).E
          ((packetQuarterTurnHom N).map o) +
        weightedDir4Response W o * breakCoeff halfScalingDecay j :=
  (weightedQuarterTurnResponse W).same_state_bound o j

theorem weightedDir4_limit_quarterTurn_invariant {N : Nat}
    (W : PositivePacketWeight N) (o : PacketDir4 N) :
    RegularCReal.Equiv
      (limitE (weightedDir4Scaling W) ((packetQuarterTurnHom N).map o))
      (limitE (weightedDir4Scaling W) o) :=
  limitE_invariant_of_decay_response
    (weightedQuarterTurnResponse W).toDecayControlled o

/-! ## 3. Globally projected bivalent-cycle state -/

def projectedCycleWeightData (f : Nat -> Q') (N : Nat)
    (hpos : (0 : Q') < modeNorm (globalVacuumProject f) (N + 1)) :
    PositivePacketWeight N where
  weight := projectedCycleWeight f
  weight_nonneg := projectedCycleWeight_nonneg f
  partition_pos := by
    simpa [modeNorm, projectedCycleWeight] using hpos

theorem bigon_projected_norm_pos :
    (0 : Q') < modeNorm (globalVacuumProject bigonGaugePacket) 3 := by
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv bigon_projected_norm_exact)

def bigonProjectedWeightData : PositivePacketWeight 2 :=
  projectedCycleWeightData bigonGaugePacket 2 bigon_projected_norm_pos

/-- The same-state quarter-turn response for the corrected globally projected
two-link bigon state. -/
theorem bigonQuarterTurn_same_state_response (o : PacketDir4 2) (j : Nat) :
    ((weightedDir4Scaling bigonProjectedWeightData).atSpacing j).E
        ((packetQuarterTurnHom 2).map o) <=
      ((weightedDir4Scaling bigonProjectedWeightData).atSpacing j).E o +
        weightedDir4Response bigonProjectedWeightData o *
          breakCoeff halfScalingDecay j
    /\
    ((weightedDir4Scaling bigonProjectedWeightData).atSpacing j).E o <=
      ((weightedDir4Scaling bigonProjectedWeightData).atSpacing j).E
          ((packetQuarterTurnHom 2).map o) +
        weightedDir4Response bigonProjectedWeightData o *
          breakCoeff halfScalingDecay j :=
  weightedQuarterTurn_same_state_response bigonProjectedWeightData o j

theorem bigon_limit_quarterTurn_invariant (o : PacketDir4 2) :
    RegularCReal.Equiv
      (limitE (weightedDir4Scaling bigonProjectedWeightData)
        ((packetQuarterTurnHom 2).map o))
      (limitE (weightedDir4Scaling bigonProjectedWeightData) o) :=
  weightedDir4_limit_quarterTurn_invariant bigonProjectedWeightData o

end YMGap.Continuum.SU2BivalentCycleO4Response

#print axioms YMGap.Continuum.SU2BivalentCycleO4Response.weightedPacketFunctional
#print axioms YMGap.Continuum.SU2BivalentCycleO4Response.weightedDir4Functional
#print axioms YMGap.Continuum.SU2BivalentCycleO4Response.weightedQuarterTurnResponse
#print axioms YMGap.Continuum.SU2BivalentCycleO4Response.weightedQuarterTurn_same_state_response
#print axioms YMGap.Continuum.SU2BivalentCycleO4Response.weightedDir4_limit_quarterTurn_invariant
#print axioms YMGap.Continuum.SU2BivalentCycleO4Response.projectedCycleWeightData
#print axioms YMGap.Continuum.SU2BivalentCycleO4Response.bigonProjectedWeightData
#print axioms YMGap.Continuum.SU2BivalentCycleO4Response.bigonQuarterTurn_same_state_response
#print axioms YMGap.Continuum.SU2BivalentCycleO4Response.bigon_limit_quarterTurn_invariant
