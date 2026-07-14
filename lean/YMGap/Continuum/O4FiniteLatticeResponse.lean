/-
A finite-lattice, same-state validation of the observable O(4) response bridge.

The existing `DecayControlledSymmetryResponse` deliberately asks only for a
carrier map and two expectation inequalities.  That is the correct minimal
consumer interface, but by itself it cannot certify that the map is an
observable-algebra action.  Here we add an action-bearing producer interface
and inhabit it on a concrete four-direction lattice algebra.

The carrier is the exact rational function algebra on the four oriented lattice
directions.  The quarter-turn cyclically permutes the directions and is a
nonidentity order-four linear `*`-automorphism.  At spacing `j` the state is

  E_j(o) = (1/4) sum_dir o_dir + (1/2)^j (1/8) (o_e - o_w).

It is normalized and positive because its four coordinate weights are
`1/4` plus or minus `(1/8)(1/2)^j`, and two copies of `1/4`; all are
nonnegative.  The SAME `E_j` occurs on
both sides of the response estimate.  Exact Q' arithmetic gives

  |E_j(rot o) - E_j(o)| <= (1/8) sum_dir |o_dir| (1/2)^j.

Thus this module validates the full coefficient-response-to-limit pipeline on
a nonconstant finite lattice state and a nontrivial finite action.  It does not
identify this four-point directional algebra with the interacting Wilson
observable algebra, and an H4 quarter-turn is not the missing continuum family
of physical O(4) rotations.
-/

import YMGap.Continuum.O4ObservableSymmetryBridge

namespace YMGap.Continuum.O4FiniteLatticeResponse

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.RegularFunctional
open YMGap.Continuum.RegularLinearScalingLimit
open YMGap.Continuum.RegularLinearGeometricSymmetry
open YMGap.Continuum.O4RestorationAF
open YMGap.Continuum.O4ObservableSymmetryBridge

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add]; ac_rfl))

/-! ## 1. An action-bearing correction to the minimal response interface -/

/-- A linear observable homomorphism.  The laws use structural equality because
the concrete lattice action is a literal coordinate permutation. -/
structure LinearObservableHom (A B : LinearObsAlg) where
  map : A.carrier -> B.carrier
  map_zero : map A.zero = B.zero
  map_add : forall a b, map (A.add a b) = B.add (map a) (map b)
  map_one : map A.one = B.one
  map_mul : forall a b, map (A.mul a b) = B.mul (map a) (map b)
  map_star : forall a, map (A.star a) = B.star (map a)
  map_smul : forall q a, map (A.smul q a) = B.smul q (map a)

/-- A genuine nonidentity order-four observable action, with inverse and an
explicit moved observable carried as data. -/
structure OrderFourObservableAction (A : LinearObsAlg) : Type where
  act : LinearObservableHom A A
  inv : LinearObservableHom A A
  leftInv : forall o, inv.map (act.map o) = o
  rightInv : forall o, act.map (inv.map o) = o
  orderFour : forall o, act.map (act.map (act.map (act.map o))) = o
  moved : A.carrier
  moved_ne : act.map moved ≠ moved

/-- Strengthening of `DecayControlledSymmetryResponse` which requires the map
to be a genuine order-four observable-algebra action.  Both inequalities use
one and the same finite-spacing state `(L.atSpacing j)`. -/
structure ActionDecayControlledResponse (A : LinearObsAlg)
    (L : LinearScalingLimitModulus A) (D : ScalingDimensionDecay) where
  action : OrderFourObservableAction A
  response : A.carrier -> Q'
  response_nonneg : forall o, (0 : Q') <= response o
  stage_upper : forall o j,
    (L.atSpacing j).E (action.act.map o) <=
      (L.atSpacing j).E o + response o * breakCoeff D j
  stage_lower : forall o j,
    (L.atSpacing j).E o <=
      (L.atSpacing j).E (action.act.map o) + response o * breakCoeff D j

/-- Forget only the proved action laws; the response data then plug directly
into the existing continuum bridge. -/
def ActionDecayControlledResponse.toDecayControlled
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    {D : ScalingDimensionDecay}
    (R : ActionDecayControlledResponse A L D) :
    DecayControlledSymmetryResponse A L D where
  map := R.action.act.map
  response := R.response
  response_nonneg := R.response_nonneg
  stage_upper := R.stage_upper
  stage_lower := R.stage_lower

/-- The same-state response theorem exposed without either side being hidden
inside a structure projection. -/
theorem ActionDecayControlledResponse.same_state_bound
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    {D : ScalingDimensionDecay}
    (R : ActionDecayControlledResponse A L D) (o : A.carrier) (j : Nat) :
    (L.atSpacing j).E (R.action.act.map o) <=
        (L.atSpacing j).E o + R.response o * breakCoeff D j
    /\
    (L.atSpacing j).E o <=
        (L.atSpacing j).E (R.action.act.map o) +
          R.response o * breakCoeff D j :=
  ⟨R.stage_upper o j, R.stage_lower o j⟩

/-! ## 2. The four-direction finite lattice observable algebra -/

/-- Exact rational observables on the four oriented directions at a lattice
site. -/
structure Dir4Observable where
  east : Q'
  north : Q'
  west : Q'
  south : Q'
deriving DecidableEq, Repr

/-- The finite commutative function algebra `Q'^{4}` with coordinatewise
product and the identity involution. -/
def dir4Alg : LinearObsAlg where
  carrier := Dir4Observable
  zero := ⟨0, 0, 0, 0⟩
  add := fun a b =>
    ⟨a.east + b.east, a.north + b.north,
      a.west + b.west, a.south + b.south⟩
  one := ⟨1, 1, 1, 1⟩
  mul := fun a b =>
    ⟨a.east * b.east, a.north * b.north,
      a.west * b.west, a.south * b.south⟩
  star := id
  smul := fun q a =>
    ⟨q * a.east, q * a.north, q * a.west, q * a.south⟩

/-- Counterclockwise lattice quarter-turn on directional observables. -/
def quarterTurnHom : LinearObservableHom dir4Alg dir4Alg where
  map := fun o => ⟨o.south, o.east, o.north, o.west⟩
  map_zero := rfl
  map_add := fun _ _ => rfl
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl
  map_smul := fun _ _ => rfl

/-- The inverse clockwise quarter-turn. -/
def quarterTurnInvHom : LinearObservableHom dir4Alg dir4Alg where
  map := fun o => ⟨o.north, o.west, o.south, o.east⟩
  map_zero := rfl
  map_add := fun _ _ => rfl
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl
  map_smul := fun _ _ => rfl

def eastIndicator : Dir4Observable := ⟨1, 0, 0, 0⟩

theorem quarterTurn_moves_east : quarterTurnHom.map eastIndicator ≠ eastIndicator := by
  intro h
  have he := congrArg Dir4Observable.east h
  change (0 : Q') = (1 : Q') at he
  exact (by decide : (0 : Q') ≠ (1 : Q')) he

/-- The concrete quarter-turn, including inverse, order-four law, and moved
directional indicator. -/
def quarterTurnAction : OrderFourObservableAction dir4Alg where
  act := quarterTurnHom
  inv := quarterTurnInvHom
  leftInv := fun _ => rfl
  rightInv := fun _ => rfl
  orderFour := fun _ => rfl
  moved := eastIndicator
  moved_ne := quarterTurn_moves_east

/-! ## 3. Exact anisotropic finite-spacing states -/

def quarter : Q' := Q'.mkPos 1 4 (by decide)
def eighth : Q' := Q'.mkPos 1 8 (by decide)

theorem quarter_nonneg : (0 : Q') <= quarter := by decide
theorem eighth_nonneg : (0 : Q') <= eighth := by decide
theorem eighth_pos : (0 : Q') < eighth := by decide
theorem eighth_le_quarter : eighth <= quarter := by decide

/-- H4-invariant average of the four directional values. -/
def isotropicPart (o : Dir4Observable) : Q' :=
  quarter * (((o.east + o.north) + o.west) + o.south)

/-- The selected first anisotropic directional harmonic. -/
def directionalHarmonic (o : Dir4Observable) : Q' :=
  eighth * (o.east + (-o.west))

/-- The exact finite-spacing state: isotropic average plus a geometric
east-west anisotropy. -/
def dir4Functional (j : Nat) : QLinearFunctional dir4Alg where
  E := fun o => isotropicPart o + half ^ j * directionalHarmonic o
  normalized := by
    have hIso : (isotropicPart dir4Alg.one).eqv (1 : Q') := by decide
    have hHar : (directionalHarmonic dir4Alg.one).eqv (0 : Q') := by
      unfold directionalHarmonic dir4Alg
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left eighth _ _ (Q'.add_neg_self_eqv (1 : Q'))) ?_
      exact Q'.mul_zero_eqv eighth
    have hTail : (half ^ j * directionalHarmonic dir4Alg.one).eqv (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (half ^ j) _ _ hHar)
        (Q'.mul_zero_eqv (half ^ j))
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hIso hTail)
      (QPoly.q_add_zero_eqv 1)
  positive := by
    intro o
    let delta := half ^ j * eighth
    have hdelta0 : (0 : Q') <= delta :=
      Q'.mul_nonneg _ _ (Q'.pow_nonneg half half_nonneg j) eighth_nonneg
    have hp1 : half ^ j <= (1 : Q') := by
      simpa using (half_pow_antitone 0 j (Nat.zero_le j))
    have hdelta8 : delta <= eighth := by
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ eighth hp1 eighth_nonneg)
        (Q'.le_of_eqv (Q'.one_mul_eqv eighth))
    have hdelta4 : delta <= quarter :=
      Q'.le_trans' _ _ _ hdelta8 eighth_le_quarter
    have hwest : (0 : Q') <= quarter + (-delta) :=
      Q'.sub_nonneg_of_le hdelta4
    have heast : (0 : Q') <= quarter + delta :=
      Q'.zero_le_add _ _ quarter_nonneg hdelta0
    have hsE : (0 : Q') <= o.east * o.east :=
      SumOfSquares.q_mul_self_nonneg o.east
    have hsN : (0 : Q') <= o.north * o.north :=
      SumOfSquares.q_mul_self_nonneg o.north
    have hsW : (0 : Q') <= o.west * o.west :=
      SumOfSquares.q_mul_self_nonneg o.west
    have hsS : (0 : Q') <= o.south * o.south :=
      SumOfSquares.q_mul_self_nonneg o.south
    let weighted :=
      (((quarter + delta) * (o.east * o.east)
        + quarter * (o.north * o.north))
        + (quarter + (-delta)) * (o.west * o.west))
        + quarter * (o.south * o.south)
    have hw : (0 : Q') <= weighted :=
      Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ heast hsE)
            (Q'.mul_nonneg _ _ quarter_nonneg hsN))
          (Q'.mul_nonneg _ _ hwest hsW))
        (Q'.mul_nonneg _ _ quarter_nonneg hsS)
    have heq :
        (isotropicPart (dir4Alg.mul (dir4Alg.star o) o) +
          half ^ j * directionalHarmonic
            (dir4Alg.mul (dir4Alg.star o) o)).eqv weighted := by
      dsimp [dir4Alg, isotropicPart, directionalHarmonic, delta, weighted]
      ring_qeqv
    exact Q'.le_trans' _ _ _ hw (Q'.ge_of_eqv heq)
  additive := by
    intro a b
    dsimp [dir4Alg, isotropicPart, directionalHarmonic]
    ring_qeqv
  homogeneous := by
    intro q a
    dsimp [dir4Alg, isotropicPart, directionalHarmonic]
    ring_qeqv

/-- The spacing family reuses the already constructed geometric modulus on the
pair `(isotropicPart o, directionalHarmonic o)`; no limit datum is posited. -/
def dir4Scaling : LinearScalingLimitModulus dir4Alg where
  atSpacing := dir4Functional
  modOf := fun o => by
    change RegularCReal.ModCauchy
      (fun j => RegularCReal.ofQ'
        (isotropicPart o + half ^ j * directionalHarmonic o))
    exact tailPlaneScaling.modOf (isotropicPart o, directionalHarmonic o)

/-! ## 4. The exact same-state response estimate -/

/-- The isotropic average is exactly invariant under the cyclic action. -/
theorem isotropicPart_quarterTurn (o : Dir4Observable) :
    (isotropicPart (quarterTurnHom.map o)).eqv (isotropicPart o) := by
  dsimp [quarterTurnHom, isotropicPart]
  ring_qeqv

private theorem add_increment_sub_base (X Y : Q') :
    ((X + Y) + (-X)).eqv Y := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (X + Y) (Y + X) (-X)
      (Q'.add_comm_eqv X Y)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv Y X (-X)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left Y (X + (-X)) 0 (Q'.add_neg_self_eqv X)) ?_
  exact QPoly.q_add_zero_eqv Y

private theorem same_base_sub (B X Y : Q') :
    ((B + X) + (-(B + Y))).eqv (X + (-Y)) := by
  have hneg : (-(B + Y)).eqv ((-B) + (-Y)) := Q'.neg_add_eqv B Y
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (B + X) _ _ hneg) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (B + X) (-B) (-Y))) ?_
  exact Q'.add_eqv_congr_right _ _ (-Y) (add_increment_sub_base B X)

private theorem scaled_le_abs_scaled (delta : Q')
    (hdelta : (0 : Q') <= delta) (x : Q') :
    delta * x <= delta * Q'.abs x :=
  Q'.mul_le_mul_of_nonneg_left x (Q'.abs x) delta (Q'.le_abs_self x) hdelta

private theorem neg_scaled_le_abs_scaled (delta : Q')
    (hdelta : (0 : Q') <= delta) (x : Q') :
    (-(delta * x)) <= delta * Q'.abs x := by
  refine Q'.le_trans' _ (delta * (-x)) _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_neg_eqv delta x))) ?_
  exact Q'.mul_le_mul_of_nonneg_left (-x) (Q'.abs x) delta
    (Q'.neg_le_abs x) hdelta

/-- Exact signed defect for the forward quarter-turn. -/
theorem quarterTurn_difference_forward (j : Nat) (o : Dir4Observable) :
    ((dir4Functional j).E (quarterTurnHom.map o) +
      (-((dir4Functional j).E o))).eqv
      ((((half ^ j * eighth) * o.south +
        (-((half ^ j * eighth) * o.north))) +
        (-((half ^ j * eighth) * o.east))) +
        (half ^ j * eighth) * o.west) := by
  let B := isotropicPart o
  let X := half ^ j * directionalHarmonic (quarterTurnHom.map o)
  let Y := half ^ j * directionalHarmonic o
  have hrot :
      ((dir4Functional j).E (quarterTurnHom.map o)).eqv (B + X) := by
    change (isotropicPart (quarterTurnHom.map o) + X).eqv (B + X)
    exact Q'.add_eqv_congr_right _ _ X (isotropicPart_quarterTurn o)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      hrot (Q'.neg_eqv_congr _ _ (Q'.eqv_refl ((dir4Functional j).E o)))) ?_
  refine Q'.eqv_trans _ _ _ (same_base_sub B X Y) ?_
  dsimp [B, X, Y, directionalHarmonic, quarterTurnHom, dir4Functional]
  ring_qeqv

/-- Exact signed defect in the reverse direction. -/
theorem quarterTurn_difference_backward (j : Nat) (o : Dir4Observable) :
    ((dir4Functional j).E o +
      (-((dir4Functional j).E (quarterTurnHom.map o)))).eqv
      ((((half ^ j * eighth) * o.east +
        (-((half ^ j * eighth) * o.west))) +
        (-((half ^ j * eighth) * o.south))) +
        (half ^ j * eighth) * o.north) := by
  let B := isotropicPart o
  let X := half ^ j * directionalHarmonic o
  let Y := half ^ j * directionalHarmonic (quarterTurnHom.map o)
  have hrot :
      ((dir4Functional j).E (quarterTurnHom.map o)).eqv (B + Y) := by
    change (isotropicPart (quarterTurnHom.map o) + Y).eqv (B + Y)
    exact Q'.add_eqv_congr_right _ _ Y (isotropicPart_quarterTurn o)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((dir4Functional j).E o) _ _
      (Q'.neg_eqv_congr _ _ hrot)) ?_
  refine Q'.eqv_trans _ _ _ (same_base_sub B X Y) ?_
  dsimp [B, X, Y, directionalHarmonic, quarterTurnHom, dir4Functional]
  ring_qeqv

/-- Derived response coefficient: one eighth times the exact L1 size of the
four directional observable. -/
def dir4Response (o : Dir4Observable) : Q' :=
  eighth * (((Q'.abs o.east + Q'.abs o.north) + Q'.abs o.west) +
    Q'.abs o.south)

theorem dir4Response_nonneg (o : Dir4Observable) :
    (0 : Q') <= dir4Response o := by
  apply Q'.mul_nonneg _ _ eighth_nonneg
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _ (Q'.abs_nonneg o.east) (Q'.abs_nonneg o.north))
      (Q'.abs_nonneg o.west))
    (Q'.abs_nonneg o.south)

theorem quarterTurn_forward_bound (j : Nat) (o : Dir4Observable) :
    ((dir4Functional j).E (quarterTurnHom.map o) +
      (-((dir4Functional j).E o))) <= dir4Response o * half ^ j := by
  let delta := half ^ j * eighth
  have hd : (0 : Q') <= delta :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg half half_nonneg j) eighth_nonneg
  have hsum :
      (((delta * o.south + (-(delta * o.north))) + (-(delta * o.east))) +
          delta * o.west) <=
        (((delta * Q'.abs o.south + delta * Q'.abs o.north) +
          delta * Q'.abs o.east) + delta * Q'.abs o.west) :=
    Q'.add_le_add
      (Q'.add_le_add
        (Q'.add_le_add (scaled_le_abs_scaled delta hd o.south)
          (neg_scaled_le_abs_scaled delta hd o.north))
        (neg_scaled_le_abs_scaled delta hd o.east))
      (scaled_le_abs_scaled delta hd o.west)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (quarterTurn_difference_forward j o)) ?_
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (by
    dsimp [delta, dir4Response]
    ring_qeqv))

theorem quarterTurn_backward_bound (j : Nat) (o : Dir4Observable) :
    ((dir4Functional j).E o +
      (-((dir4Functional j).E (quarterTurnHom.map o)))) <=
        dir4Response o * half ^ j := by
  let delta := half ^ j * eighth
  have hd : (0 : Q') <= delta :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg half half_nonneg j) eighth_nonneg
  have hsum :
      (((delta * o.east + (-(delta * o.west))) + (-(delta * o.south))) +
          delta * o.north) <=
        (((delta * Q'.abs o.east + delta * Q'.abs o.west) +
          delta * Q'.abs o.south) + delta * Q'.abs o.north) :=
    Q'.add_le_add
      (Q'.add_le_add
        (Q'.add_le_add (scaled_le_abs_scaled delta hd o.east)
          (neg_scaled_le_abs_scaled delta hd o.west))
        (neg_scaled_le_abs_scaled delta hd o.south))
      (scaled_le_abs_scaled delta hd o.north)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (quarterTurn_difference_backward j o)) ?_
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (by
    dsimp [delta, dir4Response]
    ring_qeqv))

/-- The concrete action-bearing, same-state response certificate. -/
def finiteQuarterTurnResponse :
    ActionDecayControlledResponse dir4Alg dir4Scaling halfScalingDecay where
  action := quarterTurnAction
  response := dir4Response
  response_nonneg := dir4Response_nonneg
  stage_upper := by
    intro o j
    apply Q'.le_add_of_sub_le
    exact quarterTurn_forward_bound j o
  stage_lower := by
    intro o j
    apply Q'.le_add_of_sub_le
    exact quarterTurn_backward_bound j o

/-- Direct packaging into the pre-existing response interface. -/
def finiteQuarterTurnDecayResponse :
    DecayControlledSymmetryResponse dir4Alg dir4Scaling halfScalingDecay :=
  finiteQuarterTurnResponse.toDecayControlled

/-- Concrete same-state theorem, with the single finite-spacing state visible
on both sides. -/
theorem finiteQuarterTurn_same_state_response (o : Dir4Observable) (j : Nat) :
    (dir4Scaling.atSpacing j).E (quarterTurnHom.map o) <=
        (dir4Scaling.atSpacing j).E o +
          dir4Response o * breakCoeff halfScalingDecay j
    /\
    (dir4Scaling.atSpacing j).E o <=
        (dir4Scaling.atSpacing j).E (quarterTurnHom.map o) +
          dir4Response o * breakCoeff halfScalingDecay j :=
  finiteQuarterTurnResponse.same_state_bound o j

/-- The existing O(4) observable bridge now gives exact selected quarter-turn
symmetry of the constructive continuum functional. -/
theorem dir4_limit_quarterTurn_invariant (o : Dir4Observable) :
    RegularCReal.Equiv
      (limitE dir4Scaling (quarterTurnHom.map o))
      (limitE dir4Scaling o) :=
  limitE_invariant_of_decay_response finiteQuarterTurnDecayResponse o

/-! ## 5. Kernel-checked non-vacuity and sharpness -/

private theorem isotropicPart_east :
    (isotropicPart eastIndicator).eqv quarter := by decide

private theorem isotropicPart_turned_east :
    (isotropicPart (quarterTurnHom.map eastIndicator)).eqv quarter := by decide

private theorem directionalHarmonic_east :
    (directionalHarmonic eastIndicator).eqv eighth := by decide

private theorem directionalHarmonic_turned_east :
    (directionalHarmonic (quarterTurnHom.map eastIndicator)).eqv (0 : Q') := by decide

private theorem dir4Response_east :
    (dir4Response eastIndicator).eqv eighth := by decide

private theorem lt_imp_not_eqv {a b : Q'} (h : a < b) : ¬ a.eqv b := by
  intro he
  have he' : a.num * (b.den : Int) = b.num * (a.den : Int) := he
  have h' : a.num * (b.den : Int) < b.num * (a.den : Int) := h
  rw [he'] at h'
  exact Int.lt_irrefl _ h'

private theorem lt_add_of_pos_right (a b : Q') (hb : (0 : Q') < b) :
    a < a + b := by
  show a.num * ((a + b).den : Int) < (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int)
      < (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) =
      (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
  have key : (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  calc
    a.num * ((a.den : Int) * (b.den : Int))
        = (a.num * (b.den : Int)) * (a.den : Int) := by ac_rfl
    _ < (a.num * (b.den : Int)) * (a.den : Int) +
          b.num * (a.den : Int) * (a.den : Int) := by omega
    _ = (a.num * (b.den : Int) + b.num * (a.den : Int)) *
          (a.den : Int) := by rw [Int.add_mul]

/-- The quarter-turn is not an exact symmetry at any finite spacing on the
east indicator: its strictly positive defect is `(1/8)(1/2)^j`. -/
theorem quarterTurn_not_exact_at_any_stage (j : Nat) :
    ¬ ((dir4Functional j).E (quarterTurnHom.map eastIndicator)).eqv
      ((dir4Functional j).E eastIndicator) := by
  let delta := half ^ j * eighth
  have hdelta : (0 : Q') < delta :=
    Q'.mul_pos (half_pow_pos_local j) eighth_pos
  have hrot :
      ((dir4Functional j).E (quarterTurnHom.map eastIndicator)).eqv quarter := by
    have htail :
        (half ^ j * directionalHarmonic (quarterTurnHom.map eastIndicator)).eqv
          (0 : Q') :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (half ^ j) _ _ directionalHarmonic_turned_east)
        (Q'.mul_zero_eqv (half ^ j))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' isotropicPart_turned_east htail)
      (QPoly.q_add_zero_eqv quarter)
  have heast :
      ((dir4Functional j).E eastIndicator).eqv (quarter + delta) := by
    exact Q'.add_eqv_congr' isotropicPart_east
      (Q'.mul_eqv_congr_left (half ^ j) _ _ directionalHarmonic_east)
  intro h
  have hcanon : quarter.eqv (quarter + delta) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hrot) (Q'.eqv_trans _ _ _ h heast)
  exact (lt_imp_not_eqv (lt_add_of_pos_right quarter delta hdelta)) hcanon

/-- On the east indicator the response bound is exact, not merely loose. -/
theorem east_indicator_response_exact (j : Nat) :
    (((dir4Functional j).E eastIndicator +
      (-((dir4Functional j).E (quarterTurnHom.map eastIndicator)))).eqv
        (dir4Response eastIndicator * breakCoeff halfScalingDecay j)) := by
  let delta := half ^ j * eighth
  have heast : ((dir4Functional j).E eastIndicator).eqv (quarter + delta) := by
    exact Q'.add_eqv_congr' isotropicPart_east
      (Q'.mul_eqv_congr_left (half ^ j) _ _ directionalHarmonic_east)
  have hrot :
      ((dir4Functional j).E (quarterTurnHom.map eastIndicator)).eqv quarter := by
    have htail :
        (half ^ j * directionalHarmonic (quarterTurnHom.map eastIndicator)).eqv
          (0 : Q') :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (half ^ j) _ _ directionalHarmonic_turned_east)
        (Q'.mul_zero_eqv (half ^ j))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' isotropicPart_turned_east htail)
      (QPoly.q_add_zero_eqv quarter)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' heast (Q'.neg_eqv_congr _ _ hrot)) ?_
  refine Q'.eqv_trans _ _ _ (add_increment_sub_base quarter delta) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (half ^ j) eighth) ?_
  exact Q'.eqv_symm
    (Q'.mul_eqv_congr_right (dir4Response eastIndicator) eighth (half ^ j)
      dir4Response_east)

#print axioms LinearObservableHom
#print axioms OrderFourObservableAction
#print axioms ActionDecayControlledResponse
#print axioms ActionDecayControlledResponse.toDecayControlled
#print axioms ActionDecayControlledResponse.same_state_bound
#print axioms quarterTurnAction
#print axioms dir4Functional
#print axioms dir4Scaling
#print axioms quarterTurn_difference_forward
#print axioms quarterTurn_forward_bound
#print axioms finiteQuarterTurnResponse
#print axioms finiteQuarterTurn_same_state_response
#print axioms dir4_limit_quarterTurn_invariant
#print axioms quarterTurn_not_exact_at_any_stage
#print axioms east_indicator_response_exact

end YMGap.Continuum.O4FiniteLatticeResponse
