/-
# Directional O(4) lift of an arbitrary finite positive functional

The packet and cycle response modules specialize to diagonal spectral
weights.  Four-valent recoupling mixes multiplicity coordinates, so its
observable algebra must retain off-diagonal operators.  This file removes the
diagonal restriction: any normalized positive rational linear functional on
any explicit finite `LinearObsAlg` lifts to four directional copies, with the
same exact order-four lattice action and decaying same-state response.

No algebra laws are assumed beyond the operations and functional laws already
carried by `QLinearFunctional`.  Nontriviality of the order-four action is
witnessed by `A.one != A.zero`.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketO4Response

namespace YMGap.Continuum.O4FiniteFunctionalLift

set_option maxHeartbeats 900000
set_option maxRecDepth 14000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.RegularFunctional
open YMGap.Continuum.RegularLinearScalingLimit
open YMGap.Continuum.O4RestorationAF
open YMGap.Continuum.O4ObservableSymmetryBridge
open YMGap.Continuum.O4FiniteLatticeResponse
open YMGap.Continuum.SU2FiniteCharacterPacketO4Response

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Four directional copies of an arbitrary finite algebra -/

structure FunctionalDir4 (A : LinearObsAlg) where
  east : A.carrier
  north : A.carrier
  west : A.carrier
  south : A.carrier

def functionalDir4Alg (A : LinearObsAlg) : LinearObsAlg where
  carrier := FunctionalDir4 A
  zero := ⟨A.zero, A.zero, A.zero, A.zero⟩
  add := fun a b =>
    ⟨A.add a.east b.east, A.add a.north b.north,
      A.add a.west b.west, A.add a.south b.south⟩
  one := ⟨A.one, A.one, A.one, A.one⟩
  mul := fun a b =>
    ⟨A.mul a.east b.east, A.mul a.north b.north,
      A.mul a.west b.west, A.mul a.south b.south⟩
  star := fun a =>
    ⟨A.star a.east, A.star a.north, A.star a.west, A.star a.south⟩
  smul := fun q a =>
    ⟨A.smul q a.east, A.smul q a.north,
      A.smul q a.west, A.smul q a.south⟩

def functionalQuarterTurnHom (A : LinearObsAlg) :
    LinearObservableHom (functionalDir4Alg A) (functionalDir4Alg A) where
  map := fun o => ⟨o.south, o.east, o.north, o.west⟩
  map_zero := rfl
  map_add := fun _ _ => rfl
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl
  map_smul := fun _ _ => rfl

def functionalQuarterTurnInvHom (A : LinearObsAlg) :
    LinearObservableHom (functionalDir4Alg A) (functionalDir4Alg A) where
  map := fun o => ⟨o.north, o.west, o.south, o.east⟩
  map_zero := rfl
  map_add := fun _ _ => rfl
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl
  map_smul := fun _ _ => rfl

def functionalEastIndicator (A : LinearObsAlg) : FunctionalDir4 A :=
  ⟨A.one, A.zero, A.zero, A.zero⟩

theorem functionalQuarterTurn_moves_east (A : LinearObsAlg)
    (hne : A.one ≠ A.zero) :
    (functionalQuarterTurnHom A).map (functionalEastIndicator A) ≠
      functionalEastIndicator A := by
  intro h
  have he := congrArg (fun o : FunctionalDir4 A => o.east) h
  exact hne he.symm

def functionalQuarterTurnAction (A : LinearObsAlg)
    (hne : A.one ≠ A.zero) :
    OrderFourObservableAction (functionalDir4Alg A) where
  act := functionalQuarterTurnHom A
  inv := functionalQuarterTurnInvHom A
  leftInv := fun _ => rfl
  rightInv := fun _ => rfl
  orderFour := fun _ => rfl
  moved := functionalEastIndicator A
  moved_ne := functionalQuarterTurn_moves_east A hne

/-! ## Evaluate each copy in the same finite state -/

def functionalDir4Eval {A : LinearObsAlg} (F : QLinearFunctional A)
    (o : FunctionalDir4 A) : Dir4Observable :=
  ⟨F.E o.east, F.E o.north, F.E o.west, F.E o.south⟩

theorem functionalDir4Eval_one {A : LinearObsAlg}
    (F : QLinearFunctional A) :
    DirectionalEqv (functionalDir4Eval F (functionalDir4Alg A).one)
      dir4Alg.one :=
  ⟨F.normalized, F.normalized, F.normalized, F.normalized⟩

theorem functionalDir4Eval_add {A : LinearObsAlg}
    (F : QLinearFunctional A) (a b : FunctionalDir4 A) :
    DirectionalEqv
      (functionalDir4Eval F ((functionalDir4Alg A).add a b))
      (dir4Alg.add (functionalDir4Eval F a) (functionalDir4Eval F b)) :=
  ⟨F.additive a.east b.east, F.additive a.north b.north,
    F.additive a.west b.west, F.additive a.south b.south⟩

theorem functionalDir4Eval_smul {A : LinearObsAlg}
    (F : QLinearFunctional A) (q : Q') (a : FunctionalDir4 A) :
    DirectionalEqv
      (functionalDir4Eval F ((functionalDir4Alg A).smul q a))
      (dir4Alg.smul q (functionalDir4Eval F a)) :=
  ⟨F.homogeneous q a.east, F.homogeneous q a.north,
    F.homogeneous q a.west, F.homogeneous q a.south⟩

theorem functionalDir4Eval_quarterTurn {A : LinearObsAlg}
    (F : QLinearFunctional A) (o : FunctionalDir4 A) :
    functionalDir4Eval F ((functionalQuarterTurnHom A).map o) =
      quarterTurnHom.map (functionalDir4Eval F o) := rfl

def functionalDir4Functional {A : LinearObsAlg}
    (F : QLinearFunctional A) (j : Nat) :
    QLinearFunctional (functionalDir4Alg A) where
  E := fun o => (dir4Functional j).E (functionalDir4Eval F o)
  normalized := Q'.eqv_trans _ _ _
    (dir4Functional_congr j (functionalDir4Eval_one F))
    (dir4Functional j).normalized
  positive := by
    intro o
    let delta := half ^ j * O4FiniteLatticeResponse.eighth
    let a := F.E (A.mul (A.star o.east) o.east)
    let b := F.E (A.mul (A.star o.north) o.north)
    let c := F.E (A.mul (A.star o.west) o.west)
    let d := F.E (A.mul (A.star o.south) o.south)
    have ha : (0 : Q') ≤ a := F.positive o.east
    have hb : (0 : Q') ≤ b := F.positive o.north
    have hc : (0 : Q') ≤ c := F.positive o.west
    have hd : (0 : Q') ≤ d := F.positive o.south
    have hdelta0 : (0 : Q') ≤ delta :=
      Q'.mul_nonneg _ _ (Q'.pow_nonneg half half_nonneg j)
        O4FiniteLatticeResponse.eighth_nonneg
    have hp1 : half ^ j ≤ (1 : Q') := by
      simpa using (half_pow_antitone 0 j (Nat.zero_le j))
    have hdelta8 : delta ≤ O4FiniteLatticeResponse.eighth :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ O4FiniteLatticeResponse.eighth
          hp1 O4FiniteLatticeResponse.eighth_nonneg)
        (Q'.le_of_eqv (Q'.one_mul_eqv O4FiniteLatticeResponse.eighth))
    have hdelta4 : delta ≤ quarter :=
      Q'.le_trans' _ _ _ hdelta8 eighth_le_quarter
    have hwest : (0 : Q') ≤ quarter + (-delta) :=
      Q'.sub_nonneg_of_le hdelta4
    have heast : (0 : Q') ≤ quarter + delta :=
      Q'.zero_le_add _ _ quarter_nonneg hdelta0
    let weighted :=
      (((quarter + delta) * a + quarter * b) +
        (quarter + (-delta)) * c) + quarter * d
    have hw : (0 : Q') ≤ weighted :=
      Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ heast ha)
            (Q'.mul_nonneg _ _ quarter_nonneg hb))
          (Q'.mul_nonneg _ _ hwest hc))
        (Q'.mul_nonneg _ _ quarter_nonneg hd)
    have heq :
        (dir4Functional j).E
          (functionalDir4Eval F
            ((functionalDir4Alg A).mul
              ((functionalDir4Alg A).star o) o)) ≈ weighted := by
      dsimp [functionalDir4Alg, functionalDir4Eval, dir4Functional,
        isotropicPart, directionalHarmonic, delta, a, b, c, d, weighted]
      ring_qeqv
    exact Q'.le_trans' _ _ _ hw (Q'.ge_of_eqv heq)
  additive := by
    intro a b
    exact Q'.eqv_trans _ _ _
      (dir4Functional_congr j (functionalDir4Eval_add F a b))
      ((dir4Functional j).additive (functionalDir4Eval F a)
        (functionalDir4Eval F b))
  homogeneous := by
    intro q a
    exact Q'.eqv_trans _ _ _
      (dir4Functional_congr j (functionalDir4Eval_smul F q a))
      ((dir4Functional j).homogeneous q (functionalDir4Eval F a))

def functionalDir4Scaling {A : LinearObsAlg} (F : QLinearFunctional A) :
    LinearScalingLimitModulus (functionalDir4Alg A) where
  atSpacing := functionalDir4Functional F
  modOf := fun o => by
    change RegularCReal.ModCauchy
      (fun j => RegularCReal.ofQ'
        ((dir4Functional j).E (functionalDir4Eval F o)))
    exact dir4Scaling.modOf (functionalDir4Eval F o)

def functionalDir4Response {A : LinearObsAlg} (F : QLinearFunctional A)
    (o : FunctionalDir4 A) : Q' :=
  dir4Response (functionalDir4Eval F o)

theorem functionalDir4Response_nonneg {A : LinearObsAlg}
    (F : QLinearFunctional A) (o : FunctionalDir4 A) :
    (0 : Q') ≤ functionalDir4Response F o :=
  dir4Response_nonneg (functionalDir4Eval F o)

def functionalQuarterTurnResponse {A : LinearObsAlg}
    (F : QLinearFunctional A) (hne : A.one ≠ A.zero) :
    ActionDecayControlledResponse (functionalDir4Alg A)
      (functionalDir4Scaling F) halfScalingDecay where
  action := functionalQuarterTurnAction A hne
  response := functionalDir4Response F
  response_nonneg := functionalDir4Response_nonneg F
  stage_upper := by
    intro o j
    change
      (dir4Functional j).E
          (functionalDir4Eval F ((functionalQuarterTurnHom A).map o)) ≤
        (dir4Functional j).E (functionalDir4Eval F o) +
          dir4Response (functionalDir4Eval F o) * breakCoeff halfScalingDecay j
    rw [functionalDir4Eval_quarterTurn]
    exact finiteQuarterTurnResponse.stage_upper (functionalDir4Eval F o) j
  stage_lower := by
    intro o j
    change
      (dir4Functional j).E (functionalDir4Eval F o) ≤
        (dir4Functional j).E
            (functionalDir4Eval F ((functionalQuarterTurnHom A).map o)) +
          dir4Response (functionalDir4Eval F o) * breakCoeff halfScalingDecay j
    rw [functionalDir4Eval_quarterTurn]
    exact finiteQuarterTurnResponse.stage_lower (functionalDir4Eval F o) j

theorem functionalQuarterTurn_same_state_response {A : LinearObsAlg}
    (F : QLinearFunctional A) (hne : A.one ≠ A.zero)
    (o : FunctionalDir4 A) (j : Nat) :
    ((functionalDir4Scaling F).atSpacing j).E
        ((functionalQuarterTurnHom A).map o) ≤
      ((functionalDir4Scaling F).atSpacing j).E o +
        functionalDir4Response F o * breakCoeff halfScalingDecay j
    /\
    ((functionalDir4Scaling F).atSpacing j).E o ≤
      ((functionalDir4Scaling F).atSpacing j).E
          ((functionalQuarterTurnHom A).map o) +
        functionalDir4Response F o * breakCoeff halfScalingDecay j :=
  (functionalQuarterTurnResponse F hne).same_state_bound o j

theorem functionalDir4_limit_quarterTurn_invariant {A : LinearObsAlg}
    (F : QLinearFunctional A) (hne : A.one ≠ A.zero)
    (o : FunctionalDir4 A) :
    RegularCReal.Equiv
      (limitE (functionalDir4Scaling F) ((functionalQuarterTurnHom A).map o))
      (limitE (functionalDir4Scaling F) o) :=
  limitE_invariant_of_decay_response
    (functionalQuarterTurnResponse F hne).toDecayControlled o

end YMGap.Continuum.O4FiniteFunctionalLift

#print axioms YMGap.Continuum.O4FiniteFunctionalLift.functionalQuarterTurnAction
#print axioms YMGap.Continuum.O4FiniteFunctionalLift.functionalDir4Functional
#print axioms YMGap.Continuum.O4FiniteFunctionalLift.functionalQuarterTurnResponse
#print axioms YMGap.Continuum.O4FiniteFunctionalLift.functionalQuarterTurn_same_state_response
#print axioms YMGap.Continuum.O4FiniteFunctionalLift.functionalDir4_limit_quarterTurn_invariant
