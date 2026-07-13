/-
`FusedSchurAllK` generalizes the endpoint Schur construction from the first
quadratic-cutoff step to every consecutive pair `Ncut(k), Ncut(k+1)`.

At `w=1`, the exact fused operator masses are the derived tails `tailCut(k)`.
Rotating the consecutive mass eigenvalues by the same rational 3-4-5 coupling
gives an all-scale head mass, a strictly positive shell mass, an exact Schur
erosion, and a contracting reciprocal-cutoff spacing.  The coupling-size
condition is discharged identically at every scale.

The only remaining all-scale analytic statement is the Schur-level spacing
cross inequality.  It is isolated as a one-field Type carrier; from that field
the full operator mass cross law and physical additive-margin step are theorems.
-/

import YMGap.Continuum.FusedSchurSpacingBridge

namespace YMGap.Continuum.FusedSchurAllK

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.EndpointCutoffTailClose
open YMGap.Continuum.FusedOffDiagonalCompression
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.SpectralMarginBridge
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Every endpoint fused mass is the exact moving-cutoff tail -/

/-- The actual fused operator mass at `w=1,Ncut(k)` is exactly `tailCut(k)`. -/
theorem fused_endpoint_mass_eq_tailCut (k : Nat) :
    ((1 : Q') - lamPW (1 : Q') (Ncut k) 1) ≈ tailCut k := by
  have hlam := lamPW_eq_vacNorm_p2
    (by decide : (0 : Q') <= (1 : Q'))
    (by decide : (1 : Q') <= (1 : Q')) (Ncut k) 0
  have hv := vacNorm_endpoint_formula (Ncut k)
  have hrate : lamPW (1 : Q') (Ncut k) 1 ≈ endpointRate (Ncut k) :=
    Q'.eqv_trans _ _ _ hlam hv
  have hsub :
      ((1 : Q') - lamPW (1 : Q') (Ncut k) 1) ≈
        (1 : Q') - endpointRate (Ncut k) :=
    Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr _ _ hrate)
  exact Q'.eqv_trans _ _ _ hsub
    (Q'.eqv_trans _ _ _ (one_sub_endpointRate (Ncut k))
      (CutoffTailRefinedCarrier.endpointTail_Ncut k))

/-! ## 2. All-k rotated mass blocks and exact coupling erosion -/

/-- The rotated mass operator for the consecutive actual fused endpoint masses. -/
def endpointMassOp (k : Nat) : CompactTransferGNS.FiniteOp :=
  rotatedFusedOp (tailCut k) (tailCut (k + 1))

def headMass (k : Nat) : Q' := rot00 (tailCut k) (tailCut (k + 1))
def shellMass (k : Nat) : Q' := rot11 (tailCut k) (tailCut (k + 1))
def coupling (k : Nat) : Q' := rot01 (tailCut k) (tailCut (k + 1))

/-- The shell mass is strictly positive at every cutoff pair. -/
theorem shellMass_pos (k : Nat) : (0 : Q') < shellMass k := by
  unfold shellMass rot11
  exact Q'.add_pos
    (Q'.mul_pos (Q'.mul_pos (by decide) (by decide)) (tailCut_pos k))
    (Q'.mul_pos (Q'.mul_pos (by decide) (by decide)) (tailCut_pos (k + 1)))

def erosion (k : Nat) : Q' := shellLoss (coupling k) (shellMass k) (shellMass_pos k)
def schur (k : Nat) : Q' := schurMass (headMass k) (shellMass k) (coupling k) (shellMass_pos k)

/-- The Schur erosion is nonnegative at every scale. -/
theorem erosion_nonneg (k : Nat) : (0 : Q') <= erosion k := by
  unfold erosion shellLoss Q'.divPos
  exact Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg (coupling k))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- The coupling-size condition is exact (`g² = erosion*shellMass`) for every
scale; no new analytic estimate is needed. -/
theorem coupling_size (k : Nat) :
    coupling k * coupling k <= erosion k * shellMass k := by
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.divPos_mul_eqv (coupling k * coupling k) (shellMass k) (shellMass_pos k)))

/-! ## 3. Reciprocal-cutoff spacing contracts at every step -/

def spacing (k : Nat) : Q' := unit (Ncut k) (Ncut_pos k)

theorem spacing_pos (k : Nat) : (0 : Q') < spacing k :=
  unit_pos (Ncut k) (Ncut_pos k)

theorem Ncut_mono_step (k : Nat) : Ncut k <= Ncut (k + 1) := by
  unfold Ncut
  exact Nat.mul_le_mul (by omega) (by omega)

theorem spacing_contracts (k : Nat) : spacing (k + 1) <= spacing k :=
  unit_antitone (Ncut_pos k) (Ncut_pos (k + 1)) (Ncut_mono_step k)

/-! ## 4. Exact tail/spacing cross arithmetic -/

private theorem ofNat_mul_unit_le_of_cross
    {p p' d d' : Nat} (hd : 0 < d) (hd' : 0 < d')
    (hcross : p * d' <= p' * d) :
    Q'.ofNat p * unit d hd <= Q'.ofNat p' * unit d' hd' := by
  show (Q'.ofNat p * unit d hd).num *
      ((Q'.ofNat p' * unit d' hd').den : Int) <=
    (Q'.ofNat p' * unit d' hd').num *
      ((Q'.ofNat p * unit d hd).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_num_cast, Q'.mul_den_cast, Q'.mul_den_cast]
  rw [unit_num, unit_num, unit_den, unit_den]
  rw [show ((Q'.ofNat p).den : Int) = 1 from rfl,
    show ((Q'.ofNat p').den : Int) = 1 from rfl]
  rw [show (Q'.ofNat p).num = (p : Int) from rfl,
    show (Q'.ofNat p').num = (p' : Int) from rfl]
  rw [Int.mul_one, Int.mul_one]
  rw [Int.one_mul, Int.one_mul]
  change (p : Int) * (d' : Int) <= (p' : Int) * (d : Int)
  exact_mod_cast hcross

private theorem unit_mul_unit_eqv
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    unit a ha * unit b hb ≈ unit (a * b) (Nat.mul_pos ha hb) := by
  show (unit a ha * unit b hb).num *
      ((unit (a * b) (Nat.mul_pos ha hb)).den : Int) =
    (unit (a * b) (Nat.mul_pos ha hb)).num *
      ((unit a ha * unit b hb).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast]
  rw [unit_num, unit_num, unit_num, unit_den, unit_den, unit_den]
  rfl

private theorem tailDen_mono_step (k : Nat) :
    2 * Ncut k + 3 <= 2 * Ncut (k + 1) + 3 :=
  Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Ncut_mono_step k)) 3

/-- The exact cutoff tail decreases with the cutoff. -/
theorem tailCut_antitone_step (k : Nat) : tailCut (k + 1) <= tailCut k := by
  unfold tailCut
  have hu := unit_antitone (tailDenom_pos k) (tailDenom_pos (k + 1))
    (tailDen_mono_step k)
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hu (by decide)

private theorem nat_tail_cross (k : Nat) :
    (3 * Ncut k) * (2 * Ncut (k + 1) + 3) <=
      (3 * Ncut (k + 1)) * (2 * Ncut k + 3) := by
  have h9' : 3 * (3 * Ncut k) <= 3 * (3 * Ncut (k + 1)) := by
    exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left 3 (Ncut_mono_step k))
  have hcommon :
      6 * (Ncut k * Ncut (k + 1)) + (3 * (3 * Ncut k)) <=
        6 * (Ncut k * Ncut (k + 1)) + (3 * (3 * Ncut (k + 1))) :=
    Nat.add_le_add_left h9' _
  simpa [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcommon

/-- The endpoint mass divided by reciprocal-cutoff spacing is monotone:
equivalently `tailCut(k)*spacing(k+1) <= tailCut(k+1)*spacing(k)`. -/
theorem tailCut_spacing_cross (k : Nat) :
    tailCut k * spacing (k + 1) <= tailCut (k + 1) * spacing k := by
  have hleft : tailCut k * spacing (k + 1) ≈
      Q'.ofNat 3 * unit ((2 * Ncut k + 3) * Ncut (k + 1))
        (Nat.mul_pos (tailDenom_pos k) (Ncut_pos (k + 1))) := by
    unfold tailCut spacing
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (unit_mul_unit_eqv _ _ _ _)
  have hright : tailCut (k + 1) * spacing k ≈
      Q'.ofNat 3 * unit ((2 * Ncut (k + 1) + 3) * Ncut k)
        (Nat.mul_pos (tailDenom_pos (k + 1)) (Ncut_pos k)) := by
    unfold tailCut spacing
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (unit_mul_unit_eqv _ _ _ _)
  have hdenCross :
      3 * ((2 * Ncut (k + 1) + 3) * Ncut k) <=
        3 * ((2 * Ncut k + 3) * Ncut (k + 1)) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using nat_tail_cross k
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _
      (ofNat_mul_unit_le_of_cross
        (Nat.mul_pos (tailDenom_pos k) (Ncut_pos (k + 1)))
        (Nat.mul_pos (tailDenom_pos (k + 1)) (Ncut_pos k))
        hdenCross)
      (Q'.ge_of_eqv hright))

/-! ## 5. The all-k Schur cross law -/

/-- The sole remaining all-scale operator estimate after shell positivity,
coupling size, and spacing contraction have all been derived. -/
structure SchurCrossAllK : Type where
  cross : forall k,
    schur k * spacing (k + 1) <= tailCut (k + 1) * spacing k

/-- Eliminating a nonnegative shell loss cannot increase the head mass. -/
theorem schur_le_headMass (k : Nat) : schur k <= headMass k := by
  have hneg : -(erosion k) <= (0 : Q') := by
    have h := Q'.neg_le_neg (erosion_nonneg k)
    exact Q'.le_trans' _ _ _ h (by decide)
  have hadd : headMass k + -(erosion k) <= headMass k + (0 : Q') :=
    Q'.add_le_add_left _ _ _ hneg
  have hadd' : schur k <= headMass k + (0 : Q') := by
    simpa [schur, schurMass, erosion] using hadd
  exact Q'.le_trans' _ _ _ hadd' (Q'.le_of_eqv (QPoly.q_add_zero_eqv _))

/-- The Schur mass is bounded by the old endpoint mass. -/
theorem schur_le_tailCut (k : Nat) : schur k <= tailCut k :=
  Q'.le_trans' _ _ _ (schur_le_headMass k)
    (rot00_le_left (tailCut_antitone_step k))

/-- **The all-k Schur cross law is unconditional.**  The Schur complement is
at most the old tail, and the old tail already obeys the exact reciprocal-cutoff
spacing cross inequality. -/
def schurCrossAllK : SchurCrossAllK where
  cross := fun k => by
    have hscale : schur k * spacing (k + 1) <=
        tailCut k * spacing (k + 1) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (schur_le_tailCut k)
        (Q'.le_of_lt (spacing_pos (k + 1)))
    exact Q'.le_trans' _ _ _ hscale (tailCut_spacing_cross k)

/-- Any proof of the isolated Schur cross law gives the full cross-multiplied
operator mass inequality at every scale. -/
theorem operator_mass_spacing_cross (H : SchurCrossAllK) (k : Nat) :
    headMass k * spacing (k + 1) <=
      (erosion k + tailCut (k + 1)) * spacing k := by
  exact spacing_cross_of_schur (shellMass_pos k) (erosion_nonneg k)
    (Q'.le_of_lt (spacing_pos (k + 1))) (spacing_contracts k)
    (coupling_size k) (H.cross k)

/-- The corresponding physical additive-margin step, with the actual two
positive reciprocal-cutoff spacings. -/
theorem operator_physical_margin_step (H : SchurCrossAllK) (k : Nat) :
    Q'.divPos (headMass k) (spacing k) (spacing_pos k) -
        Q'.divPos (erosion k) (spacing (k + 1)) (spacing_pos (k + 1)) <=
      Q'.divPos (tailCut (k + 1)) (spacing (k + 1)) (spacing_pos (k + 1)) := by
  exact hadd_of_hlat_varying
    (headMass k) (tailCut (k + 1)) (erosion k)
    (spacing k) (spacing (k + 1))
    (spacing_pos k) (spacing_pos (k + 1))
    (operator_mass_spacing_cross H k)

/-- Unconditional all-scale operator mass cross law. -/
theorem operator_mass_spacing_cross_unconditional (k : Nat) :
    headMass k * spacing (k + 1) <=
      (erosion k + tailCut (k + 1)) * spacing k :=
  operator_mass_spacing_cross schurCrossAllK k

/-- Unconditional all-scale physical additive-margin step. -/
theorem operator_physical_margin_step_unconditional (k : Nat) :
    Q'.divPos (headMass k) (spacing k) (spacing_pos k) -
        Q'.divPos (erosion k) (spacing (k + 1)) (spacing_pos (k + 1)) <=
      Q'.divPos (tailCut (k + 1)) (spacing (k + 1)) (spacing_pos (k + 1)) :=
  operator_physical_margin_step schurCrossAllK k

end YMGap.Continuum.FusedSchurAllK

#print axioms YMGap.Continuum.FusedSchurAllK.fused_endpoint_mass_eq_tailCut
#print axioms YMGap.Continuum.FusedSchurAllK.shellMass_pos
#print axioms YMGap.Continuum.FusedSchurAllK.erosion_nonneg
#print axioms YMGap.Continuum.FusedSchurAllK.coupling_size
#print axioms YMGap.Continuum.FusedSchurAllK.Ncut_mono_step
#print axioms YMGap.Continuum.FusedSchurAllK.spacing_contracts
#print axioms YMGap.Continuum.FusedSchurAllK.tailCut_antitone_step
#print axioms YMGap.Continuum.FusedSchurAllK.tailCut_spacing_cross
#print axioms YMGap.Continuum.FusedSchurAllK.schur_le_headMass
#print axioms YMGap.Continuum.FusedSchurAllK.schur_le_tailCut
#print axioms YMGap.Continuum.FusedSchurAllK.schurCrossAllK
#print axioms YMGap.Continuum.FusedSchurAllK.operator_mass_spacing_cross
#print axioms YMGap.Continuum.FusedSchurAllK.operator_physical_margin_step
#print axioms YMGap.Continuum.FusedSchurAllK.operator_mass_spacing_cross_unconditional
#print axioms YMGap.Continuum.FusedSchurAllK.operator_physical_margin_step_unconditional
