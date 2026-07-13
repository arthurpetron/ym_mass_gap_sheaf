/-
An exact strictly-positive compressed-transfer model.

This file inhabits `PositiveTimeTransfer` with a rational signed-coordinate
involution on a four-coordinate ambient GNS space.  The positive-time plane is
spanned by the fixed vacuum vector `Omega=e₃` and the excitation
`v=(2,1,0,1)`.  For `U(x₁,x₂,x₃,x₄)=(x₂,x₁,x₃,-x₄)`, orthogonal compression
fixes Omega and sends v to (1/2)v.  Thus the non-vacuum transfer
eigenvalue is strictly between zero and one, avoiding the infinite-energy
zero-eigenvalue artifact while retaining a genuinely nonidentity transfer.

Every identity is exact over `Q'`.  Positivity, self-adjointness, and
contractivity are inherited from the derived (not assumed) compression
theorems.  No classical choice or numerical input is used.
-/

import YMGap.Continuum.PositiveTimeCompressedTransfer
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.PositiveTimeCompressedTransferHalf

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveTimeCompressedTransfer

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

private theorem int_mul_two (a : Int) : a * 2 = a + a := by omega

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero,
               Int.two_mul, int_mul_two];
             ac_rfl))

set_option maxHeartbeats 1000000

/-! ## Weighted rational lines and the two-dimensional positive carrier -/

/-- A one-dimensional rational GNS datum with Gram weight `w`. -/
abbrev weightedLine (w : Q') (hw : (0 : Q') ≤ w) : GNSData where
  V := Q'
  veq := Q'.eqv
  veq_refl := Q'.eqv_refl
  veq_symm := fun h => Q'.eqv_symm h
  veq_trans := fun h₁ h₂ => Q'.eqv_trans _ _ _ h₁ h₂
  zero := 0
  add := fun a b => a + b
  neg := fun a => -a
  smul := fun s a => s * a
  add_congr := fun ha hb => Q'.add_eqv_congr' ha hb
  neg_congr := fun h => Q'.neg_eqv_congr _ _ h
  smul_congr := fun s {a a'} h => Q'.mul_eqv_congr_left s _ _ h
  add_assoc := Q'.add_assoc_eqv
  add_comm := Q'.add_comm_eqv
  zero_add := QPoly.q_zero_add_eqv
  neg_add := Q'.neg_add_self_eqv
  B := fun a b => w * (a * b)
  B_congr_left := fun b h => Q'.mul_eqv_congr_left w _ _
    (Q'.mul_eqv_congr_right _ _ b h)
  B_add_left := fun a b c => by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left w _ _ (QPoly.q_add_mul a b c)) ?_
    exact Q'.mul_add_eqv w (a * c) (b * c)
  B_smul_left := fun s a b => by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left w _ _ (Q'.mul_assoc_eqv s a b)) ?_
    ring_qeqv
  B_symm := fun a b => Q'.mul_eqv_congr_left w _ _ (Q'.mul_comm_eqv a b)
  self_nonneg := fun a => Q'.mul_nonneg _ _ hw
    (SumOfSquares.q_mul_self_nonneg a)

abbrev sextupleLine : GNSData := weightedLine 6 (by decide)

/-- Coefficients `(a,b)` of `a Omega + b v`, with `Omega=e₃` of squared norm
one and `v=(2,1,0,1)` of squared norm six. -/
abbrev halfPositivePlane : GNSData := gnsProduct unitQGNS sextupleLine

/-- Four orthogonal exact rational coordinates. -/
abbrev ambientFour : GNSData :=
  gnsProduct unitQGNS (gnsProduct unitQGNS (gnsProduct unitQGNS unitQGNS))

def halfMode : Q' := Q'.mkPos 1 2 (by decide)

/-- The signed swap is an exact orthogonal involution. -/
def signedSwap4 (x : Q' × (Q' × (Q' × Q'))) :
    Q' × (Q' × (Q' × Q')) :=
  (x.2.1, (x.1, (x.2.2.1, -x.2.2.2)))

def identityReflection4 (x : Q' × (Q' × (Q' × Q'))) :
    Q' × (Q' × (Q' × Q')) := x

/-! ## Ambient isometric time automorphism -/

def ambientHalf : AmbientTimeReflection where
  space := ambientFour
  tau := signedSwap4
  tauInv := signedSwap4
  theta := identityReflection4
  tau_map_veq := by
    intro a b h
    exact ⟨h.2.1, ⟨h.1, ⟨h.2.2.1, Q'.neg_eqv_congr _ _ h.2.2.2⟩⟩⟩
  tau_map_add := by
    intro a b
    unfold signedSwap4 ambientFour gnsProduct unitQGNS
    exact ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _,
      Q'.neg_add_eqv _ _⟩⟩⟩
  tau_map_neg := by
    intro a
    unfold signedSwap4 ambientFour gnsProduct unitQGNS
    exact ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _,
      Q'.eqv_refl _⟩⟩⟩
  tau_map_smul := by
    intro r a
    unfold signedSwap4 ambientFour gnsProduct unitQGNS
    exact ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _,
      Q'.eqv_symm (Q'.mul_neg_eqv r a.2.2.2)⟩⟩⟩
  tau_left_inv := by
    intro a
    unfold signedSwap4 ambientFour gnsProduct unitQGNS
    exact ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _,
      Q'.neg_neg_eqv _⟩⟩⟩
  tau_right_inv := by
    intro a
    unfold signedSwap4 ambientFour gnsProduct unitQGNS
    exact ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _,
      Q'.neg_neg_eqv _⟩⟩⟩
  tau_isometry := by
    intro a b
    have hneg : ((-a.2.2.2) * (-b.2.2.2)) ≈ (a.2.2.2 * b.2.2.2) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a.2.2.2 (-b.2.2.2)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a.2.2.2 b.2.2.2)) ?_
      exact Q'.neg_neg_eqv _
    unfold signedSwap4 ambientFour gnsProduct unitQGNS
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.mul_eqv_congr_left 1 _ _ hneg)))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)) ?_
    exact Q'.add_assoc_eqv _ _ _
  theta_involutive := fun _ =>
    ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩⟩⟩
  theta_time_inverse := fun _ =>
    ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩⟩⟩

/-! ## Exact positive-time compression -/

/-- The closed scalar identity `2·(1/2)=1`, propagated to every rational. -/
theorem two_halfMode : ((2 : Q') * halfMode) ≈ 1 := by decide

theorem two_halfMode_mul (x : Q') : (2 : Q') * (halfMode * x) ≈ x := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (2 : Q') halfMode x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right ((2 : Q') * halfMode) 1 x two_halfMode) ?_
  exact Q'.one_mul_eqv x

theorem halfMode_two_mul (x : Q') : halfMode * ((2 : Q') * x) ≈ x := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv halfMode (2 : Q') x)) ?_
  have hh : (halfMode * (2 : Q')) ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv halfMode 2) two_halfMode
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (halfMode * (2 : Q')) 1 x hh) ?_
  exact Q'.one_mul_eqv x

theorem two_halfMode_add (x : Q') : halfMode * x + halfMode * x ≈ x :=
  Q'.eqv_trans _ _ _ (q_two_mul (halfMode * x)) (two_halfMode_mul x)

theorem halfMode_middle_sum (x : Q') :
    halfMode * x + (x + halfMode * x) ≈ (2 : Q') * x := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (halfMode * x) x)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv x (halfMode * x) (halfMode * x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left x _ _ (two_halfMode_add x)) ?_
  exact q_two_mul x

theorem cancel_shift (p x : Q') : p + -(x + p) ≈ -x := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left p _ _ (Q'.neg_add_eqv x p)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left p _ _ (Q'.add_comm_eqv (-x) (-p))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv p (-p) (-x))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-x) (Q'.add_neg_self_eqv p)) ?_
  exact QPoly.q_zero_add_eqv (-x)

/-- `(a,b)` embeds as `a·e₃+b·(2,1,0,1)`. -/
def embedHalfPlane (x : Q' × Q') : Q' × (Q' × (Q' × Q')) :=
  ((2 : Q') * x.2, (x.2, (x.1, x.2)))

/-- A left inverse to `embedHalfPlane` whose restriction to
`signedSwap4 (embedHalfPlane x)` gives the required compressed coefficients.
The interface does not assert that this formula is the full ambient orthogonal
projector; orthogonality on the required time-translated subspace is certified
separately by `compressed_decomposition` and `compressed_orthogonal`. -/
def projectHalfPlane (x : Q' × (Q' × (Q' × Q'))) : Q' × Q' :=
  (x.2.2.1, halfMode * x.1)

def compressedHalf (x : Q' × Q') : Q' × Q' :=
  (x.1, halfMode * x.2)

def residualHalf (x : Q' × Q') : Q' × (Q' × (Q' × Q')) :=
  (0, (x.2 + halfMode * x.2, (0, -(x.2 + halfMode * x.2))))

def halfCoordinate (x : Q' × Q') : Nat → Q'
  | 0 => x.1
  | _ + 1 => x.2

def halfModeWeight : Nat → Q'
  | 0 => 1
  | _ + 1 => 3

private def embedGramL : RingNormaliser.PolyExpr :=
  .add (.mul (.const 1) (.mul (.mul (.const 2) (.var 1))
      (.mul (.const 2) (.var 3))))
    (.add (.mul (.const 1) (.mul (.var 1) (.var 3)))
      (.add (.mul (.const 1) (.mul (.var 0) (.var 2)))
        (.mul (.const 1) (.mul (.var 1) (.var 3)))))

private def embedGramR : RingNormaliser.PolyExpr :=
  .add (.mul (.const 1) (.mul (.var 0) (.var 2)))
    (.mul (.const 6) (.mul (.var 1) (.var 3)))

private theorem embedGram_normal :
    RingNormaliser.normalize embedGramL = RingNormaliser.normalize embedGramR := by
  decide

private theorem embedGram_exact (a b c d : Q') :
    (1 * (((2 : Q') * b) * ((2 : Q') * d)) +
      (1 * (b * d) + (1 * (a * c) + 1 * (b * d)))) ≈
      (1 * (a * c) + 6 * (b * d)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    embedGramL embedGramR embedGram_normal
    (fun | 0 => a | 1 => b | 2 => c | _ => d)
  simpa [RingNormaliser.eval, embedGramL, embedGramR] using h

private def orthoGramL : RingNormaliser.PolyExpr :=
  .add (.mul (.const 1) (.mul (.mul (.const 2) (.var 0)) (.const 0)))
    (.add (.mul (.const 1) (.mul (.var 0) (.var 2)))
      (.add (.mul (.const 1) (.mul (.var 1) (.const 0)))
        (.mul (.const 1) (.mul (.var 0) (.neg (.var 2))))))

private theorem orthoGram_normal :
    RingNormaliser.normalize orthoGramL =
      RingNormaliser.normalize (.const 0) := by
  decide

private theorem orthoGram_exact (p a r : Q') :
    (1 * (((2 : Q') * p) * 0) +
      (1 * (p * r) + (1 * (a * 0) + 1 * (p * (-r))))) ≈ 0 := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    orthoGramL (.const 0) orthoGram_normal
    (fun | 0 => p | 1 => a | _ => r)
  simpa [RingNormaliser.eval, orthoGramL] using h

def rationalHalfCompression : PositiveTimeTransfer ambientHalf where
  positive := halfPositivePlane
  embed := embedHalfPlane
  project := projectHalfPlane
  transfer := compressedHalf
  residual := residualHalf
  embed_form := by
    intro a b
    change
      (1 * (((2 : Q') * a.2) * ((2 : Q') * b.2)) +
        (1 * (a.2 * b.2) + (1 * (a.1 * b.1) + 1 * (a.2 * b.2)))) ≈
      (1 * (a.1 * b.1) + 6 * (a.2 * b.2))
    exact embedGram_exact a.1 a.2 b.1 b.2
  reflected_form := by
    intro a b
    change
      (1 * (((2 : Q') * a.2) * ((2 : Q') * b.2)) +
        (1 * (a.2 * b.2) + (1 * (a.1 * b.1) + 1 * (a.2 * b.2)))) ≈
      (1 * (a.1 * b.1) + 6 * (a.2 * b.2))
    exact embedGram_exact a.1 a.2 b.1 b.2
  project_embed := by
    intro a
    exact ⟨Q'.eqv_refl a.1, halfMode_two_mul a.2⟩
  transfer_projected_time := by
    intro a
    exact ⟨Q'.eqv_refl a.1, Q'.eqv_refl (halfMode * a.2)⟩
  transfer_map_veq := by
    intro a b h
    exact ⟨h.1, Q'.mul_eqv_congr_left halfMode _ _ h.2⟩
  transfer_map_zero := by
    unfold compressedHalf halfPositivePlane sextupleLine weightedLine gnsProduct unitQGNS
    exact ⟨Q'.eqv_refl _, by ring_qeqv⟩
  transfer_map_add := by
    intro a b
    unfold compressedHalf halfPositivePlane sextupleLine weightedLine gnsProduct unitQGNS
    exact ⟨Q'.eqv_refl _, by ring_qeqv⟩
  transfer_map_neg := by
    intro a
    unfold compressedHalf halfPositivePlane sextupleLine weightedLine gnsProduct unitQGNS
    exact ⟨Q'.eqv_refl _, Q'.mul_neg_eqv _ _⟩
  transfer_map_smul := by
    intro r a
    unfold compressedHalf halfPositivePlane sextupleLine weightedLine gnsProduct unitQGNS
    exact ⟨Q'.eqv_refl _, by ring_qeqv⟩
  compressed_decomposition := by
    intro a
    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
    · exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (two_halfMode_mul a.2))
        (Q'.eqv_symm (QPoly.q_add_zero_eqv _))
    · exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm (halfMode_middle_sum a.2))
        (Q'.eqv_refl _)
    · exact Q'.eqv_symm (QPoly.q_add_zero_eqv a.1)
    · exact Q'.eqv_symm (cancel_shift (halfMode * a.2) a.2)
  compressed_orthogonal := by
    intro a
    change
      (1 * (((2 : Q') * (halfMode * a.2)) * 0) +
        (1 * ((halfMode * a.2) * (a.2 + halfMode * a.2)) +
          (1 * (a.1 * 0) +
            1 * ((halfMode * a.2) * (-(a.2 + halfMode * a.2)))))) ≈ 0
    exact orthoGram_exact (halfMode * a.2) a.1 (a.2 + halfMode * a.2)
  modeCount := 2
  coordinate := halfCoordinate
  modeWeight := halfModeWeight
  modeWeight_nonneg := by
    intro i
    cases i with
    | zero => decide
    | succ _ =>
        change (0 : Q') ≤ (3 : Q')
        decide
  transfer_weightedGram := by
    intro a b
    change
      (1 * (a.1 * b.1) + 6 * ((halfMode * a.2) * b.2)) ≈
        ((0 + 1 * (a.1 * b.1)) + 3 * (a.2 * b.2))
    have hsix : (6 * ((halfMode * a.2) * b.2)) ≈
        (3 * (a.2 * b.2)) := by
      have h6 : (6 * halfMode) ≈ (3 : Q') := by decide
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv 6 (halfMode * a.2) b.2)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ b.2
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 6 halfMode a.2))
            (Q'.mul_eqv_congr_right _ _ a.2 h6))) ?_
      exact Q'.mul_assoc_eqv 3 a.2 b.2
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (QPoly.q_zero_add_eqv (1 * (a.1 * b.1)))) hsix

/-! ## Strictly positive spectrum and non-vacuity -/

def halfVacuumMode : halfPositivePlane.V := (1, 0)

def halfExcitedMode : halfPositivePlane.V := (0, 1)

theorem halfMode_pos : (0 : Q') < halfMode := by decide

theorem halfMode_lt_one : halfMode < (1 : Q') := by decide

theorem compressedHalf_vacuum_eigen :
    halfPositivePlane.veq (compressedHalf halfVacuumMode) halfVacuumMode := by
  exact ⟨by decide, by decide⟩

theorem compressedHalf_excited_eigen :
    halfPositivePlane.veq (compressedHalf halfExcitedMode)
      (halfPositivePlane.smul halfMode halfExcitedMode) := by
  exact ⟨by decide, by decide⟩

theorem halfExcited_qmk_ne_zero_qmk :
    halfPositivePlane.qmk halfExcitedMode ≠
      halfPositivePlane.qmk halfPositivePlane.zero := by
  intro h
  have hr : halfPositivePlane.rad halfExcitedMode halfPositivePlane.zero := Quotient.exact h
  have hnot : ¬ halfPositivePlane.rad halfExcitedMode halfPositivePlane.zero := by
    unfold GNSData.rad GNSData.sub halfPositivePlane sextupleLine weightedLine
      gnsProduct unitQGNS halfExcitedMode
    decide
  exact hnot hr

theorem halfExcited_qmk_ne_vacuum_qmk :
    halfPositivePlane.qmk halfExcitedMode ≠
      halfPositivePlane.qmk halfVacuumMode := by
  intro h
  have hr : halfPositivePlane.rad halfExcitedMode halfVacuumMode := Quotient.exact h
  have hnot : ¬ halfPositivePlane.rad halfExcitedMode halfVacuumMode := by
    unfold GNSData.rad GNSData.sub halfPositivePlane sextupleLine weightedLine
      gnsProduct unitQGNS halfExcitedMode halfVacuumMode
    decide
  exact hnot hr

/-! ## Existing completion and transfer-operator bridge -/

def rationalHalfTransferOperator : TransferOperator halfPositivePlane.gnsComplete where
  T := PositiveTimeCompression.completedTransfer rationalHalfCompression
  vacuum := embedV halfPositivePlane halfVacuumMode
  selfAdjoint := PositiveTimeCompression.completedTransfer_selfAdjoint rationalHalfCompression
  positive := PositiveTimeCompression.completedTransfer_positive rationalHalfCompression
  contraction := PositiveTimeCompression.completedTransfer_contraction rationalHalfCompression

theorem rationalHalf_completed_vacuum_eigen :
    rationalHalfTransferOperator.T (embedV halfPositivePlane halfVacuumMode) =
      embedV halfPositivePlane halfVacuumMode := by
  refine Eq.trans
    (PositiveTimeCompression.completedTransfer_embed rationalHalfCompression halfVacuumMode) ?_
  apply Quotient.sound
  apply embed_null_of_rad halfPositivePlane
  have hsub : halfPositivePlane.veq
      (halfPositivePlane.sub (compressedHalf halfVacuumMode) halfVacuumMode)
      (halfPositivePlane.sub halfVacuumMode halfVacuumMode) :=
    halfPositivePlane.add_congr compressedHalf_vacuum_eigen
      (halfPositivePlane.veq_refl _)
  exact Q'.eqv_trans _ _ _ (halfPositivePlane.B_diag_congr hsub)
    (halfPositivePlane.rad_refl halfVacuumMode)

theorem rationalHalf_completed_excited_eigen :
    rationalHalfTransferOperator.T (embedV halfPositivePlane halfExcitedMode) =
      embedV halfPositivePlane
        (halfPositivePlane.smul halfMode halfExcitedMode) := by
  refine Eq.trans
    (PositiveTimeCompression.completedTransfer_embed rationalHalfCompression halfExcitedMode) ?_
  apply Quotient.sound
  apply embed_null_of_rad halfPositivePlane
  have hsub : halfPositivePlane.veq
      (halfPositivePlane.sub (compressedHalf halfExcitedMode)
        (halfPositivePlane.smul halfMode halfExcitedMode))
      (halfPositivePlane.sub (halfPositivePlane.smul halfMode halfExcitedMode)
        (halfPositivePlane.smul halfMode halfExcitedMode)) :=
    halfPositivePlane.add_congr compressedHalf_excited_eigen
      (halfPositivePlane.veq_refl _)
  exact Q'.eqv_trans _ _ _ (halfPositivePlane.B_diag_congr hsub)
    (halfPositivePlane.rad_refl
      (halfPositivePlane.smul halfMode halfExcitedMode))

theorem rationalHalf_vacuum_fixed :
    rationalHalfTransferOperator.T rationalHalfTransferOperator.vacuum =
      rationalHalfTransferOperator.vacuum :=
  rationalHalf_completed_vacuum_eigen

theorem half_completed_excited_ne_zero :
    embedV halfPositivePlane halfExcitedMode ≠
      embedV halfPositivePlane halfPositivePlane.zero := by
  intro h
  apply halfExcited_qmk_ne_zero_qmk
  apply embedQuot_injective halfPositivePlane
  exact h

/-- The completed transfer is genuinely nonidentity.  Unlike the zero-mode
model, its nonzero excited vector is scaled by the strictly positive `1/2`. -/
theorem rationalHalf_completed_nonidentity :
    rationalHalfTransferOperator.T (embedV halfPositivePlane halfExcitedMode) ≠
      embedV halfPositivePlane halfExcitedMode := by
  intro hid
  have hq : halfPositivePlane.qmk
      (halfPositivePlane.smul halfMode halfExcitedMode) =
      halfPositivePlane.qmk halfExcitedMode := by
    apply embedQuot_injective halfPositivePlane
    exact Eq.trans (Eq.symm rationalHalf_completed_excited_eigen) hid
  have hr : halfPositivePlane.rad
      (halfPositivePlane.smul halfMode halfExcitedMode) halfExcitedMode :=
    Quotient.exact hq
  have hnot : ¬ halfPositivePlane.rad
      (halfPositivePlane.smul halfMode halfExcitedMode) halfExcitedMode := by
    unfold GNSData.rad GNSData.sub halfPositivePlane sextupleLine weightedLine gnsProduct
      unitQGNS halfMode halfExcitedMode
    decide
  exact hnot hr

end YMGap.Continuum.PositiveTimeCompressedTransferHalf

#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.weightedLine
#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.ambientHalf
#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.rationalHalfCompression
#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.halfMode_pos
#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.halfMode_lt_one
#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.halfExcited_qmk_ne_zero_qmk
#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.halfExcited_qmk_ne_vacuum_qmk
#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.rationalHalfTransferOperator
#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.rationalHalf_completed_vacuum_eigen
#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.rationalHalf_completed_excited_eigen
#print axioms YMGap.Continuum.PositiveTimeCompressedTransferHalf.rationalHalf_completed_nonidentity
