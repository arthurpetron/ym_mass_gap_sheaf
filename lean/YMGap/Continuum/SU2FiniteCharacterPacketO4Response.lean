/-
# A same-state four-direction action on finite SU(2) Wilson packets

The one-link packet transfer already supplies the exact positive diagonal
Wilson Gram

    B(P,P) = sum_s lambda_s c_s^2,

at every finite character cutoff.  This module uses that same Gram, rather
than an unrelated four-point functional, to construct a finite directional
observable algebra and an action-bearing anisotropy response.

At cutoff `N`, packet coefficients form the finite spectral function algebra:
addition, scalar multiplication, involution, and multiplication are all
coefficientwise.  Its normalized state is the Wilson eigenweight average

    phi_N(P) = (sum_s lambda_s c_s) / (sum_s lambda_s).

The square expectation is exactly the existing packet Wilson Gram divided by
the positive partition sum.  Thus positivity is inherited from the already
proved interacting packet state.  Four copies carry the literal lattice
quarter-turn.  The finite-spacing state is the isotropic directional average
of `phi_N` plus an east-west bias `(1/8)(1/2)^j`; hence its response is bounded
by the same exact geometric coefficient and the constructive continuum limit
is quarter-turn invariant.

Honest scope: coefficientwise multiplication is the finite spectral/idempotent
algebra dual to the character basis.  It is not the shared-link plaquette
fusion algebra, and the cyclic H4 quarter-turn proved here is not a continuum
family of physical O(4) rotations.  The construction nevertheless closes the
previous same-state mismatch: the positivity and anisotropy both use the same
finite Wilson-packet state.

The module is MLTT/HoTT-clean under the repository axiom gate.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
import YMGap.Continuum.O4FiniteLatticeResponse
import YMGap.Constructive.RegularCRealArith
import YMGap.Continuum.BondMovingMoment

namespace YMGap.Continuum.SU2FiniteCharacterPacketO4Response

open YMGap.Constructive
open YMGap.Constructive.QPoly
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

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## 1. The finite packet spectral algebra -/

def spectralZero (N : Nat) : CharacterPacket N where
  coeff _ := 0

def spectralOne (N : Nat) : CharacterPacket N where
  coeff _ := 1

def spectralAdd {N : Nat} (P Q : CharacterPacket N) : CharacterPacket N where
  coeff i := P.coeff i + Q.coeff i

def spectralMul {N : Nat} (P Q : CharacterPacket N) : CharacterPacket N where
  coeff i := P.coeff i * Q.coeff i

def spectralScale {N : Nat} (q : Q') (P : CharacterPacket N) : CharacterPacket N where
  coeff i := q * P.coeff i

/-- The finite spectral/idempotent algebra on the packet coefficient table. -/
def packetSpectralAlg (N : Nat) : LinearObsAlg where
  carrier := CharacterPacket N
  zero := spectralZero N
  add := spectralAdd
  one := spectralOne N
  mul := spectralMul
  star := id
  smul := spectralScale

theorem coeffAt_spectralZero {N : Nat} (s : Nat) :
    coeffAt (spectralZero N) s ≈ 0 := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt (spectralZero N) hs]
    exact Q'.eqv_refl 0
  · unfold coeffAt
    rw [dif_neg hs]
    exact Q'.eqv_refl 0

theorem coeffAt_spectralOne_of_lt {N : Nat} {s : Nat} (hs : s < N + 1) :
    coeffAt (spectralOne N) s ≈ 1 := by
  rw [coeffAt_of_lt (spectralOne N) hs]
  exact Q'.eqv_refl 1

theorem coeffAt_spectralAdd {N : Nat} (P Q : CharacterPacket N) (s : Nat) :
    coeffAt (spectralAdd P Q) s ≈ coeffAt P s + coeffAt Q s := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt (spectralAdd P Q) hs,
      coeffAt_of_lt P hs, coeffAt_of_lt Q hs]
    exact Q'.eqv_refl _
  · unfold coeffAt
    rw [dif_neg hs, dif_neg hs, dif_neg hs]
    exact Q'.eqv_symm (QPoly.q_zero_add_eqv 0)

theorem coeffAt_spectralMul {N : Nat} (P Q : CharacterPacket N) (s : Nat) :
    coeffAt (spectralMul P Q) s ≈ coeffAt P s * coeffAt Q s := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt (spectralMul P Q) hs,
      coeffAt_of_lt P hs, coeffAt_of_lt Q hs]
    exact Q'.eqv_refl _
  · unfold coeffAt
    rw [dif_neg hs, dif_neg hs, dif_neg hs]
    exact Q'.eqv_symm (Q'.zero_mul_eqv 0)

theorem coeffAt_spectralScale {N : Nat} (q : Q')
    (P : CharacterPacket N) (s : Nat) :
    coeffAt (spectralScale q P) s ≈ q * coeffAt P s := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt (spectralScale q P) hs, coeffAt_of_lt P hs]
    exact Q'.eqv_refl _
  · unfold coeffAt
    rw [dif_neg hs, dif_neg hs]
    exact Q'.eqv_symm (Q'.mul_zero_eqv q)

/-! The following setoid laws certify that the carrier really is a commutative
unital algebra.  Structural equality of unreduced `Q'` fractions is not used. -/

theorem spectralMul_assoc {N : Nat} (P Q R : CharacterPacket N) :
    PacketEqv (spectralMul (spectralMul P Q) R)
      (spectralMul P (spectralMul Q R)) := by
  intro i
  exact Q'.mul_assoc_eqv (P.coeff i) (Q.coeff i) (R.coeff i)

theorem spectralMul_comm {N : Nat} (P Q : CharacterPacket N) :
    PacketEqv (spectralMul P Q) (spectralMul Q P) := by
  intro i
  exact Q'.mul_comm_eqv (P.coeff i) (Q.coeff i)

theorem spectralOne_mul {N : Nat} (P : CharacterPacket N) :
    PacketEqv (spectralMul (spectralOne N) P) P := by
  intro i
  exact Q'.one_mul_eqv (P.coeff i)

theorem spectralMul_one {N : Nat} (P : CharacterPacket N) :
    PacketEqv (spectralMul P (spectralOne N)) P := by
  intro i
  exact Q'.mul_one_eqv (P.coeff i)

theorem spectralMul_add {N : Nat} (P Q R : CharacterPacket N) :
    PacketEqv (spectralMul P (spectralAdd Q R))
      (spectralAdd (spectralMul P Q) (spectralMul P R)) := by
  intro i
  exact Q'.mul_add_eqv (P.coeff i) (Q.coeff i) (R.coeff i)

/-! ## 2. The normalized state derived from the Wilson packet Gram -/

def packetPartition (N : Nat) : Q' :=
  fsum packetEigen (N + 1)

theorem packetPartition_pos (N : Nat) : (0 : Q') < packetPartition N := by
  have hterm : packetEigen 0 ≤ packetPartition N :=
    BondMovingMoment.fsum_term_le_of_nonneg packetEigen_nonneg 0 (N + 1)
      (Nat.succ_pos N)
  rw [packetEigen_zero] at hterm
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) hterm

def packetMoment {N : Nat} (P : CharacterPacket N) : Q' :=
  fsum (fun s => packetEigen s * coeffAt P s) (N + 1)

def packetExpectation {N : Nat} (P : CharacterPacket N) : Q' :=
  Q'.divPos (packetMoment P) (packetPartition N) (packetPartition_pos N)

theorem packetMoment_zero (N : Nat) : packetMoment (spectralZero N) ≈ 0 := by
  apply FusionQuotientCollapse.fsum_zero_below
  intro s hs
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (packetEigen s) _ _ (coeffAt_spectralZero s))
    (Q'.mul_zero_eqv (packetEigen s))

theorem packetMoment_one (N : Nat) :
    packetMoment (spectralOne N) ≈ packetPartition N := by
  unfold packetMoment packetPartition
  exact CubeRatioBounds.fsum_eqv_congr_lt _ _ (N + 1) (fun s hs =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (packetEigen s) _ _
        (coeffAt_spectralOne_of_lt hs))
      (Q'.mul_one_eqv (packetEigen s)))

theorem packetMoment_add {N : Nat} (P Q : CharacterPacket N) :
    packetMoment (spectralAdd P Q) ≈ packetMoment P + packetMoment Q := by
  unfold packetMoment
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s * coeffAt P s +
      packetEigen s * coeffAt Q s) (N + 1)) _ ?_ ?_
  · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (packetEigen s) _ _
          (coeffAt_spectralAdd P Q s))
        (Q'.mul_add_eqv (packetEigen s) (coeffAt P s) (coeffAt Q s))) (N + 1)
  · exact CubeRatioBounds.fsum_add _ _ (N + 1)

theorem packetMoment_scale {N : Nat} (q : Q') (P : CharacterPacket N) :
    packetMoment (spectralScale q P) ≈ q * packetMoment P := by
  unfold packetMoment
  refine Q'.eqv_trans _
    (fsum (fun s => q * (packetEigen s * coeffAt P s)) (N + 1)) _ ?_ ?_
  · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (packetEigen s) _ _
          (coeffAt_spectralScale q P s))
        (by ring_qeqv)) (N + 1)
  · exact Q'.eqv_symm (CubeRatioBounds.fsum_const_mul q _ (N + 1))

theorem packetExpectation_zero (N : Nat) :
    packetExpectation (spectralZero N) ≈ 0 := by
  unfold packetExpectation Q'.divPos
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (packetMoment_zero N))
    (Q'.zero_mul_eqv _)

theorem packetExpectation_one (N : Nat) :
    packetExpectation (spectralOne N) ≈ 1 := by
  unfold packetExpectation Q'.divPos
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (packetMoment_one N))
    (Q'.mul_recipPos_eqv (packetPartition N) (packetPartition_pos N))

theorem packetExpectation_add {N : Nat} (P Q : CharacterPacket N) :
    packetExpectation (spectralAdd P Q) ≈
      packetExpectation P + packetExpectation Q := by
  unfold packetExpectation Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (packetMoment_add P Q)) ?_
  exact Q'.add_mul_eqv (packetMoment P) (packetMoment Q)
    (Q'.recipPos (packetPartition N) (packetPartition_pos N))

theorem packetExpectation_scale {N : Nat} (q : Q') (P : CharacterPacket N) :
    packetExpectation (spectralScale q P) ≈ q * packetExpectation P := by
  unfold packetExpectation Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (packetMoment_scale q P)) ?_
  exact Q'.mul_assoc_eqv q (packetMoment P)
    (Q'.recipPos (packetPartition N) (packetPartition_pos N))

theorem packetMoment_square_eq_gram {N : Nat} (P : CharacterPacket N) :
    packetMoment (spectralMul P P) ≈ packetWilsonGram P P := by
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s * (coeffAt P s * coeffAt P s)) (N + 1)) _ ?_ ?_
  · unfold packetMoment
    exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.mul_eqv_congr_left (packetEigen s) _ _
        (coeffAt_spectralMul P P s)) (N + 1)
  · exact Q'.eqv_symm (packetWilsonGram_diagonal P P)

/-- The square state is literally the existing interacting Wilson packet Gram,
normalized by the positive finite packet partition sum. -/
theorem packetExpectation_square_eq_normalized_gram {N : Nat}
    (P : CharacterPacket N) :
    packetExpectation (spectralMul P P) ≈
      packetWilsonGram P P *
        Q'.recipPos (packetPartition N) (packetPartition_pos N) := by
  unfold packetExpectation Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ (packetMoment_square_eq_gram P)

theorem packetExpectation_square_nonneg {N : Nat} (P : CharacterPacket N) :
    (0 : Q') ≤ packetExpectation (spectralMul P P) := by
  have hprod : (0 : Q') ≤
      packetWilsonGram P P *
        Q'.recipPos (packetPartition N) (packetPartition_pos N) :=
    Q'.mul_nonneg _ _ (packetWilsonGram_nonneg P)
      (Q'.le_of_lt (Q'.recipPos_pos _ _))
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_of_eqv (Q'.eqv_symm
      (packetExpectation_square_eq_normalized_gram P)))

def packetSpectralFunctional (N : Nat) : QLinearFunctional (packetSpectralAlg N) where
  E := packetExpectation
  normalized := packetExpectation_one N
  positive := packetExpectation_square_nonneg
  additive := packetExpectation_add
  homogeneous := packetExpectation_scale

/-! ## 3. Four directional copies and the literal quarter-turn action -/

structure PacketDir4 (N : Nat) where
  east : CharacterPacket N
  north : CharacterPacket N
  west : CharacterPacket N
  south : CharacterPacket N

def packetDir4Alg (N : Nat) : LinearObsAlg where
  carrier := PacketDir4 N
  zero := ⟨spectralZero N, spectralZero N, spectralZero N, spectralZero N⟩
  add := fun a b =>
    ⟨spectralAdd a.east b.east, spectralAdd a.north b.north,
      spectralAdd a.west b.west, spectralAdd a.south b.south⟩
  one := ⟨spectralOne N, spectralOne N, spectralOne N, spectralOne N⟩
  mul := fun a b =>
    ⟨spectralMul a.east b.east, spectralMul a.north b.north,
      spectralMul a.west b.west, spectralMul a.south b.south⟩
  star := id
  smul := fun q a =>
    ⟨spectralScale q a.east, spectralScale q a.north,
      spectralScale q a.west, spectralScale q a.south⟩

def packetQuarterTurnHom (N : Nat) :
    LinearObservableHom (packetDir4Alg N) (packetDir4Alg N) where
  map := fun o => ⟨o.south, o.east, o.north, o.west⟩
  map_zero := rfl
  map_add := fun _ _ => rfl
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl
  map_smul := fun _ _ => rfl

def packetQuarterTurnInvHom (N : Nat) :
    LinearObservableHom (packetDir4Alg N) (packetDir4Alg N) where
  map := fun o => ⟨o.north, o.west, o.south, o.east⟩
  map_zero := rfl
  map_add := fun _ _ => rfl
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl
  map_smul := fun _ _ => rfl

def packetEastIndicator (N : Nat) : PacketDir4 N :=
  ⟨spectralOne N, spectralZero N, spectralZero N, spectralZero N⟩

theorem packetQuarterTurn_moves_east (N : Nat) :
    (packetQuarterTurnHom N).map (packetEastIndicator N) ≠
      packetEastIndicator N := by
  intro h
  have he := congrArg
    (fun o => o.east.coeff (⟨0, Nat.succ_pos N⟩ : Fin (N + 1))) h
  change (0 : Q') = (1 : Q') at he
  exact (by decide : (0 : Q') ≠ (1 : Q')) he

def packetQuarterTurnAction (N : Nat) :
    OrderFourObservableAction (packetDir4Alg N) where
  act := packetQuarterTurnHom N
  inv := packetQuarterTurnInvHom N
  leftInv := fun _ => rfl
  rightInv := fun _ => rfl
  orderFour := fun _ => rfl
  moved := packetEastIndicator N
  moved_ne := packetQuarterTurn_moves_east N

/-! ## 4. Evaluation through the normalized Wilson packet state -/

def packetDir4Eval {N : Nat} (o : PacketDir4 N) : Dir4Observable :=
  ⟨packetExpectation o.east, packetExpectation o.north,
    packetExpectation o.west, packetExpectation o.south⟩

def DirectionalEqv (a b : Dir4Observable) : Prop :=
  a.east ≈ b.east /\ a.north ≈ b.north /\
    a.west ≈ b.west /\ a.south ≈ b.south

theorem isotropicPart_congr {a b : Dir4Observable} (h : DirectionalEqv a b) :
    isotropicPart a ≈ isotropicPart b := by
  exact Q'.mul_eqv_congr_left quarter _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' h.1 h.2.1) h.2.2.1)
      h.2.2.2)

theorem directionalHarmonic_congr {a b : Dir4Observable}
    (h : DirectionalEqv a b) :
    directionalHarmonic a ≈ directionalHarmonic b := by
  exact Q'.mul_eqv_congr_left eighth _ _
    (Q'.add_eqv_congr' h.1 (Q'.neg_eqv_congr _ _ h.2.2.1))

theorem dir4Functional_congr (j : Nat) {a b : Dir4Observable}
    (h : DirectionalEqv a b) :
    (dir4Functional j).E a ≈ (dir4Functional j).E b := by
  exact Q'.add_eqv_congr'
    (isotropicPart_congr h)
    (Q'.mul_eqv_congr_left (half ^ j) _ _
      (directionalHarmonic_congr h))

theorem packetDir4Eval_zero (N : Nat) :
    DirectionalEqv (packetDir4Eval (packetDir4Alg N).zero) dir4Alg.zero :=
  ⟨packetExpectation_zero N, packetExpectation_zero N,
    packetExpectation_zero N, packetExpectation_zero N⟩

theorem packetDir4Eval_one (N : Nat) :
    DirectionalEqv (packetDir4Eval (packetDir4Alg N).one) dir4Alg.one :=
  ⟨packetExpectation_one N, packetExpectation_one N,
    packetExpectation_one N, packetExpectation_one N⟩

theorem packetDir4Eval_add {N : Nat} (a b : PacketDir4 N) :
    DirectionalEqv
      (packetDir4Eval ((packetDir4Alg N).add a b))
      (dir4Alg.add (packetDir4Eval a) (packetDir4Eval b)) :=
  ⟨packetExpectation_add a.east b.east,
    packetExpectation_add a.north b.north,
    packetExpectation_add a.west b.west,
    packetExpectation_add a.south b.south⟩

theorem packetDir4Eval_smul {N : Nat} (q : Q') (a : PacketDir4 N) :
    DirectionalEqv
      (packetDir4Eval ((packetDir4Alg N).smul q a))
      (dir4Alg.smul q (packetDir4Eval a)) :=
  ⟨packetExpectation_scale q a.east,
    packetExpectation_scale q a.north,
    packetExpectation_scale q a.west,
    packetExpectation_scale q a.south⟩

theorem packetDir4Eval_quarterTurn {N : Nat} (o : PacketDir4 N) :
    packetDir4Eval ((packetQuarterTurnHom N).map o) =
      quarterTurnHom.map (packetDir4Eval o) := rfl

/-! ## 5. The decaying same-state finite-spacing functional -/

def packetDir4Functional (N j : Nat) : QLinearFunctional (packetDir4Alg N) where
  E := fun o => (dir4Functional j).E (packetDir4Eval o)
  normalized := Q'.eqv_trans _ _ _
    (dir4Functional_congr j (packetDir4Eval_one N))
    (dir4Functional j).normalized
  positive := by
    intro o
    let delta := half ^ j * eighth
    let a := packetExpectation (spectralMul o.east o.east)
    let b := packetExpectation (spectralMul o.north o.north)
    let c := packetExpectation (spectralMul o.west o.west)
    let d := packetExpectation (spectralMul o.south o.south)
    have ha : (0 : Q') ≤ a := packetExpectation_square_nonneg o.east
    have hb : (0 : Q') ≤ b := packetExpectation_square_nonneg o.north
    have hc : (0 : Q') ≤ c := packetExpectation_square_nonneg o.west
    have hd : (0 : Q') ≤ d := packetExpectation_square_nonneg o.south
    have hdelta0 : (0 : Q') ≤ delta :=
      Q'.mul_nonneg _ _ (Q'.pow_nonneg half half_nonneg j) eighth_nonneg
    have hp1 : half ^ j ≤ (1 : Q') := by
      simpa using (half_pow_antitone 0 j (Nat.zero_le j))
    have hdelta8 : delta ≤ eighth :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ eighth hp1 eighth_nonneg)
        (Q'.le_of_eqv (Q'.one_mul_eqv eighth))
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
          (packetDir4Eval
            ((packetDir4Alg N).mul ((packetDir4Alg N).star o) o)) ≈
          weighted := by
      dsimp [packetDir4Alg, packetDir4Eval, dir4Functional,
        isotropicPart, directionalHarmonic, delta, a, b, c, d, weighted]
      ring_qeqv
    exact Q'.le_trans' _ _ _ hw (Q'.ge_of_eqv heq)
  additive := by
    intro a b
    exact Q'.eqv_trans _ _ _
      (dir4Functional_congr j (packetDir4Eval_add a b))
      ((dir4Functional j).additive (packetDir4Eval a) (packetDir4Eval b))
  homogeneous := by
    intro q a
    exact Q'.eqv_trans _ _ _
      (dir4Functional_congr j (packetDir4Eval_smul q a))
      ((dir4Functional j).homogeneous q (packetDir4Eval a))

def packetDir4Scaling (N : Nat) : LinearScalingLimitModulus (packetDir4Alg N) where
  atSpacing := packetDir4Functional N
  modOf := fun o => by
    change RegularCReal.ModCauchy
      (fun j => RegularCReal.ofQ'
        ((dir4Functional j).E (packetDir4Eval o)))
    exact dir4Scaling.modOf (packetDir4Eval o)

/-! ## 6. Exact decaying response for the packet quarter-turn -/

def packetDir4Response {N : Nat} (o : PacketDir4 N) : Q' :=
  dir4Response (packetDir4Eval o)

theorem packetDir4Response_nonneg {N : Nat} (o : PacketDir4 N) :
    (0 : Q') ≤ packetDir4Response o :=
  dir4Response_nonneg (packetDir4Eval o)

/-- The quarter-turn response on four packet copies.  Both sides use the same
normalized Wilson-packet functional at the same spacing. -/
def packetQuarterTurnResponse (N : Nat) :
    ActionDecayControlledResponse (packetDir4Alg N) (packetDir4Scaling N)
      halfScalingDecay where
  action := packetQuarterTurnAction N
  response := packetDir4Response
  response_nonneg := packetDir4Response_nonneg
  stage_upper := by
    intro o j
    change
      (dir4Functional j).E
          (packetDir4Eval ((packetQuarterTurnHom N).map o)) ≤
        (dir4Functional j).E (packetDir4Eval o) +
          dir4Response (packetDir4Eval o) * breakCoeff halfScalingDecay j
    rw [packetDir4Eval_quarterTurn]
    exact finiteQuarterTurnResponse.stage_upper (packetDir4Eval o) j
  stage_lower := by
    intro o j
    change
      (dir4Functional j).E (packetDir4Eval o) ≤
        (dir4Functional j).E
            (packetDir4Eval ((packetQuarterTurnHom N).map o)) +
          dir4Response (packetDir4Eval o) * breakCoeff halfScalingDecay j
    rw [packetDir4Eval_quarterTurn]
    exact finiteQuarterTurnResponse.stage_lower (packetDir4Eval o) j

def packetQuarterTurnDecayResponse (N : Nat) :
    DecayControlledSymmetryResponse (packetDir4Alg N) (packetDir4Scaling N)
      halfScalingDecay :=
  (packetQuarterTurnResponse N).toDecayControlled

/-- Visible same-state estimate at arbitrary packet cutoff. -/
theorem packetQuarterTurn_same_state_response (N : Nat)
    (o : PacketDir4 N) (j : Nat) :
    ((packetDir4Scaling N).atSpacing j).E
        ((packetQuarterTurnHom N).map o) ≤
      ((packetDir4Scaling N).atSpacing j).E o +
        packetDir4Response o * breakCoeff halfScalingDecay j
    /\
    ((packetDir4Scaling N).atSpacing j).E o ≤
      ((packetDir4Scaling N).atSpacing j).E
          ((packetQuarterTurnHom N).map o) +
        packetDir4Response o * breakCoeff halfScalingDecay j :=
  (packetQuarterTurnResponse N).same_state_bound o j

/-- Exact selected quarter-turn invariance in the constructive spacing limit,
uniformly in the finite packet cutoff. -/
theorem packetDir4_limit_quarterTurn_invariant (N : Nat) (o : PacketDir4 N) :
    RegularCReal.Equiv
      (limitE (packetDir4Scaling N) ((packetQuarterTurnHom N).map o))
      (limitE (packetDir4Scaling N) o) :=
  limitE_invariant_of_decay_response (packetQuarterTurnDecayResponse N) o

/-! ## 7. Kernel-checked non-vacuity and exact sharpness -/

theorem packetEastIndicator_eval (N : Nat) :
    DirectionalEqv (packetDir4Eval (packetEastIndicator N)) eastIndicator :=
  ⟨packetExpectation_one N, packetExpectation_zero N,
    packetExpectation_zero N, packetExpectation_zero N⟩

theorem packetTurnedEastIndicator_eval (N : Nat) :
    DirectionalEqv
      (packetDir4Eval ((packetQuarterTurnHom N).map (packetEastIndicator N)))
      (quarterTurnHom.map eastIndicator) :=
  ⟨packetExpectation_zero N, packetExpectation_one N,
    packetExpectation_zero N, packetExpectation_zero N⟩

/-- The action is genuinely broken at every finite spacing, even though the
defect decays geometrically to zero. -/
theorem packetQuarterTurn_not_exact_at_any_stage (N j : Nat) :
    ¬ ((packetDir4Functional N j).E
          ((packetQuarterTurnHom N).map (packetEastIndicator N))) ≈
        ((packetDir4Functional N j).E (packetEastIndicator N)) := by
  intro h
  have hturned := dir4Functional_congr j (packetTurnedEastIndicator_eval N)
  have heast := dir4Functional_congr j (packetEastIndicator_eval N)
  have hc :
      (dir4Functional j).E (quarterTurnHom.map eastIndicator) ≈
        (dir4Functional j).E eastIndicator :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hturned)
      (Q'.eqv_trans _ _ _ h heast)
  exact quarterTurn_not_exact_at_any_stage j hc

theorem dir4Response_congr {a b : Dir4Observable} (h : DirectionalEqv a b) :
    dir4Response a ≈ dir4Response b := by
  exact Q'.mul_eqv_congr_left eighth _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.abs_eqv_congr h.1)
          (Q'.abs_eqv_congr h.2.1))
        (Q'.abs_eqv_congr h.2.2.1))
      (Q'.abs_eqv_congr h.2.2.2))

/-- On the packet east indicator the bound is exact.  Its nonzero finite-stage
defect is precisely `(1/8)(1/2)^j`, now evaluated through the normalized
Wilson-packet state rather than through an independent toy expectation. -/
theorem packetEastIndicator_response_exact (N j : Nat) :
    (((packetDir4Functional N j).E (packetEastIndicator N) +
      (-((packetDir4Functional N j).E
        ((packetQuarterTurnHom N).map (packetEastIndicator N))))) ≈
      (packetDir4Response (packetEastIndicator N) *
        breakCoeff halfScalingDecay j)) := by
  have heast := dir4Functional_congr j (packetEastIndicator_eval N)
  have hturned := dir4Functional_congr j (packetTurnedEastIndicator_eval N)
  refine Q'.eqv_trans _
    ((dir4Functional j).E eastIndicator +
      (-((dir4Functional j).E (quarterTurnHom.map eastIndicator))) ) _ ?_ ?_
  · exact Q'.add_eqv_congr' heast
      (Q'.neg_eqv_congr _ _ hturned)
  · refine Q'.eqv_trans _
      (dir4Response eastIndicator * breakCoeff halfScalingDecay j) _
      (east_indicator_response_exact j) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (dir4Response_congr (packetEastIndicator_eval N)))

end YMGap.Continuum.SU2FiniteCharacterPacketO4Response

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.spectralMul_assoc
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.spectralMul_add
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetPartition_pos
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetExpectation_square_eq_normalized_gram
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetExpectation_square_nonneg
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetSpectralFunctional
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetQuarterTurnAction
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetDir4Functional
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetDir4Scaling
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetQuarterTurnResponse
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetQuarterTurn_same_state_response
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetDir4_limit_quarterTurn_invariant
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetQuarterTurn_not_exact_at_any_stage
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketO4Response.packetEastIndicator_response_exact
