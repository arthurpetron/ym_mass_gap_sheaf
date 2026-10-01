/-
# Whole signed-family kinetic upper on the SAME completed Wilson carrier

The exact original finite bound passes through the already constructed energy
limit. For the actual centered family v it gives

    B(v,v)-B(v,T(1)v) <= 192*(1-w)*|qs|*sum(c_p^2).

The coefficient-L1 refinement gives the same actual loss a second ceiling

    B(v,v)-B(v,T(1)v) <= 192*(1-w)*(sum |c_p|)^2.

The positive-transfer telescope propagates this ceiling to every integer lag
n with the explicit factor n, on the same literal-width carrier.

Strict spatial padding, original transfer/action/partition, coefficient signs
and list multiplicities are retained. The explicit late-cutoff onset does not
depend on width, depth or coefficients. This is absolute temporal time loss,
NOT the norm of v-Tv, a SAME-variance estimate or a scaling-survival theorem.
The existing conservative coefficient-variance floor does not supply useful
scaling smallness; its previously checked calibration obstruction is unchanged.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper
import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyKineticUpper

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
open YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor (finite_family_energy_pin)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime completedTime_zero)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
  (mixedMoment mixedMoment_split)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail (mixedMoment_time_decreasing)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)

local infix:50 " ≈ " => Q'.eqv

/-- Explicit family coefficient cost. It is not an OS norm. -/
def coefficientBudget (qs : List Z4Plaq) (c : Z4Plaq → Q') : Q' :=
  Q'.ofNat qs.length*listQSum (fun p => c p*c p) qs

def energyCeiling (w : Q') (qs : List Z4Plaq) (c : Z4Plaq → Q') : Q' :=
  192*(1-w)*coefficientBudget qs c

def coefficientL1Budget (qs : List Z4Plaq) (c : Z4Plaq → Q') : Q' :=
  listQSum (fun p => Q'.abs (c p)) qs * listQSum (fun p => Q'.abs (c p)) qs

def energyL1Ceiling (w : Q') (qs : List Z4Plaq) (c : Z4Plaq → Q') : Q' :=
  192*(1-w)*coefficientL1Budget qs c

/-- A common stage onset for ALL widths, terminal depths and coefficients.
The parameter w remains fixed in each limit and explicit in this function. -/
def cutoffOnset (w : Q') : Nat := max 1 (sufficientCutoff w)

private theorem halve_bound {a b : Q'} (h : (2 : Q')*a ≤ (2 : Q')*b) : a ≤ b := by
  have h' := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half h HalfPow.half_nonneg
  have cancel : ∀ x : Q', HalfPow.half*((2 : Q')*x) ≈ x := fun x =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ x (by decide : HalfPow.half*2 ≈ 1))
        (Q'.one_mul_eqv x))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (cancel a))
    (Q'.le_trans' _ _ _ h' (Q'.le_of_eqv (cancel b)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {base width : Nat} (hwidth : base < width) (qs : List Z4Plaq)
  (c : Z4Plaq → Q') (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)

local notation "wideFaces" =>
  (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
local notation "e" => familyExpression width qs c wideFaces
local notation "he" => family_within width qs c wideFaces
local notation "x" => familyState width qs c wideFaces
local notation "v" => centeredVector hw0 hw1 x
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

attribute [local irreducible] familyExpression energyLimit energyCauchy finiteEnergy
  normalizedEnergy coefficientBudget energyCeiling coefficientL1Budget energyL1Ceiling

/-- Independent late cutoff and arbitrary terminal depth, in the ACTUAL
original finite energy sequence already supplied to the completed consumer. -/
theorem finite_family_energy_nome_bound (k t : Nat) (hk : cutoffOnset w ≤ k) :
    finiteEnergy hw0 hw1 e k t ≤ energyCeiling w qs c := by
  have hk1 : 1 ≤ headCutoff w+k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hk) (Nat.le_add_left _ _)
  have heq : headCutoff w+k-1+1 = headCutoff w+k := Nat.sub_add_cancel hk1
  have hS : sufficientCutoff w ≤ headCutoff w+k-1+1 := by
    rw [heq]
    exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hk) (Nat.le_add_left _ _)
  have hH : headCutoff w ≤ headCutoff w+k-1+1 := by rw [heq]; exact Nat.le_add_right _ _
  have h := family_energy_nome_normalized hw0 hw1 (headCutoff w+k-1) hS hH hwidth t c qs hqs
  simp only [heq] at h
  have hdouble : 384*(1-w)*(Q'.ofNat qs.length*listQSum (fun p => c p*c p) qs) ≈
      (2 : Q')*energyCeiling w qs c := by
    unfold energyCeiling coefficientBudget
    exact poly_identity_of_normal_eq
      (.mul (.mul (.const 384) (.var 0)) (.var 1))
      (.mul (.const 2) (.mul (.mul (.const 192) (.var 0)) (.var 1))) (by decide)
      (fun | 0 => (1 : Q')-w | _ => Q'.ofNat qs.length*listQSum (fun p => c p*c p) qs)
  have hn := halve_bound (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hdouble))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (finite_family_energy_pin hw0 hw1 hwidth qs c hqs k t)) hn

private theorem energyLimit_le_ceiling (ceiling : Q')
    (hbound : ∀ k t : Nat, cutoffOnset w ≤ k → finiteEnergy hw0 hw1 e k t ≤ ceiling) :
    leEv (energyLimit hw0 hw1 e he) (ofQ' ceiling) := by
  apply leEv_of_ofQ'_limit_le
    (by unfold energyLimit; exact convergesTo_ofQ'CauchySeq _ (energyCauchy hw0 hw1 e he))
    (convergesTo_const _)
  intro epsilon hp
  exact ⟨cutoffOnset w, fun s hs => Q'.le_trans' _ _ _
    (hbound s s hs)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hp))⟩

/-- Pass the new bound through the EXISTING constructed energy CReal and
its explicit modulus. No new limit or convergence premise is assumed. -/
theorem family_energyLimit_nome_bound :
    leEv (energyLimit hw0 hw1 e he) (ofQ' (energyCeiling w qs c)) :=
  energyLimit_le_ceiling hw0 hw1 hwidth qs c hqs (energyCeiling w qs c)
    (finite_family_energy_nome_bound hw0 hw1 hwidth qs c hqs)

/-- Width and all regulator coefficients are absent from the bound. Each
literal width still has its OWN original carrier; no spatial map is inferred. -/
theorem completed_family_energy_nome_bound :
    RCle (RCsub (B v v) (B v (T 1 v)))
      (Quotient.mk crealSetoid (ofQ' (energyCeiling w qs c))) := by
  have h : RCle (Quotient.mk crealSetoid (energyLimit hw0 hw1 e he))
      (Quotient.mk crealSetoid (ofQ' (energyCeiling w qs c))) :=
    family_energyLimit_nome_bound hw0 hw1 hwidth qs c hqs
  rw [energyLimit_completed_pin] at h
  exact h

/-- Actual finite energy, now with a coefficient-L1 cost and no separate
list-length factor. Repeated and zero-coefficient entries remain allowed. -/
theorem finite_family_energy_l1_bound (k t : Nat) (hk : cutoffOnset w ≤ k) :
    finiteEnergy hw0 hw1 e k t ≤ energyL1Ceiling w qs c := by
  have hk1 : 1 ≤ headCutoff w+k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hk) (Nat.le_add_left _ _)
  have heq : headCutoff w+k-1+1 = headCutoff w+k := Nat.sub_add_cancel hk1
  have hS : sufficientCutoff w ≤ headCutoff w+k-1+1 := by
    rw [heq]
    exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hk) (Nat.le_add_left _ _)
  have hH : headCutoff w ≤ headCutoff w+k-1+1 := by rw [heq]; exact Nat.le_add_right _ _
  have h := family_energy_l1_normalized hw0 hw1 (headCutoff w+k-1) hS hH hwidth t c qs hqs
  simp only [heq] at h
  have hdouble : 384*(1-w)*(listQSum (fun p => Q'.abs (c p)) qs *
      listQSum (fun p => Q'.abs (c p)) qs) ≈ (2 : Q')*energyL1Ceiling w qs c := by
    unfold energyL1Ceiling coefficientL1Budget
    exact poly_identity_of_normal_eq
      (.mul (.mul (.const 384) (.var 0)) (.var 1))
      (.mul (.const 2) (.mul (.mul (.const 192) (.var 0)) (.var 1))) (by decide)
      (fun | 0 => (1 : Q')-w | _ => listQSum (fun p => Q'.abs (c p)) qs *
        listQSum (fun p => Q'.abs (c p)) qs)
  have hn := halve_bound (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hdouble))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (finite_family_energy_pin hw0 hw1 hwidth qs c hqs k t)) hn

theorem family_energyLimit_l1_bound :
    leEv (energyLimit hw0 hw1 e he) (ofQ' (energyL1Ceiling w qs c)) :=
  energyLimit_le_ceiling hw0 hw1 hwidth qs c hqs (energyL1Ceiling w qs c)
    (finite_family_energy_l1_bound hw0 hw1 hwidth qs c hqs)

/-- The coefficient-L1 bound acts on the SAME original completed time loss,
not a new Haar completion or a variance-relative proxy. -/
theorem completed_family_energy_l1_bound :
    RCle (RCsub (B v v) (B v (T 1 v)))
      (Quotient.mk crealSetoid (ofQ' (energyL1Ceiling w qs c))) := by
  have h : RCle (Quotient.mk crealSetoid (energyLimit hw0 hw1 e he))
      (Quotient.mk crealSetoid (ofQ' (energyL1Ceiling w qs c))) :=
    family_energyLimit_l1_bound hw0 hw1 hwidth qs c hqs
  rw [energyLimit_completed_pin] at h
  exact h

private theorem sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem zero_scale (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem sub_add_cancel (a b : RC) : RCsub (RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

private theorem loss_telescope (a b c : RC) :
    RCsub a c = RCadd (RCsub a b) (RCsub b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B' C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
      (by decide) (fun | 0 => A.approx n | 1 => B'.approx n | _ => C.approx n)))

private theorem scale_nat_succ (n : Nat) (a : RC) :
    RCadd (RCscale (Q'.ofNat n) a) a = RCscale (Q'.ofNat (n+1)) a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv (A.approx k)))))))

private theorem moment_increment_pin (u : Completion hw0 hw1 width) (k : Nat) :
    mixedMoment hw0 hw1 u k 1 = RCsub (B u (T k u)) (B u (T (k+1) u)) := by
  have h := mixedMoment_split hw0 hw1 u k 0
  change B u (T k u) = RCadd (B u (T (k+1) u)) (mixedMoment hw0 hw1 u k 1) at h
  rw [h, sub_add_cancel]

/-- An actual positive-transfer telescope on EVERY state of this SAME
completed carrier. Each time increment is bounded by the first increment. -/
theorem time_loss_linear_bound (u : Completion hw0 hw1 width) (n : Nat) :
    RCle (RCsub (B u u) (B u (T n u)))
      (RCscale (Q'.ofNat n) (RCsub (B u u) (B u (T 1 u)))) := by
  have hm : ∀ k : Nat, RCle (mixedMoment hw0 hw1 u k 1) (mixedMoment hw0 hw1 u 0 1) := by
    intro k
    induction k with
    | zero => exact RCle_refl _
    | succ k ih => exact RCle_trans (mixedMoment_time_decreasing hw0 hw1 u k 1) ih
  induction n with
  | zero =>
      simp only [completedTime_zero, sub_self, show Q'.ofNat 0 = (0 : Q') from rfl,
        zero_scale]
      exact RCle_refl _
  | succ n ih =>
      have h := RCadd_le_add ih (hm n)
      rw [moment_increment_pin hw0 hw1 u n, ← loss_telescope,
        moment_increment_pin hw0 hw1 u 0, completedTime_zero, scale_nat_succ] at h
      exact h

private theorem rational_scale (a b : Q') :
    RCscale a (Quotient.mk crealSetoid (ofQ' b)) =
      Quotient.mk crealSetoid (ofQ' (a*b)) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

/-- The WHOLE family's actual time loss, at EVERY integer lag, with the
explicit coefficient-L1 ceiling and no spatial-width or regulator factor. -/
theorem completed_family_time_l1_bound (n : Nat) :
    RCle (RCsub (B v v) (B v (T n v)))
      (Quotient.mk crealSetoid (ofQ' (Q'.ofNat n*energyL1Ceiling w qs c))) := by
  have h := RCle_trans (time_loss_linear_bound hw0 hw1 v n)
    (RCscale_mono (Q'.ofNat_nonneg n) (completed_family_energy_l1_bound hw0 hw1 hwidth qs c hqs))
  rwa [rational_scale] at h

#print axioms coefficientBudget
#print axioms energyCeiling
#print axioms coefficientL1Budget
#print axioms energyL1Ceiling
#print axioms cutoffOnset
#print axioms finite_family_energy_nome_bound
#print axioms family_energyLimit_nome_bound
#print axioms completed_family_energy_nome_bound
#print axioms finite_family_energy_l1_bound
#print axioms family_energyLimit_l1_bound
#print axioms completed_family_energy_l1_bound
#print axioms time_loss_linear_bound
#print axioms completed_family_time_l1_bound

end YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyKineticUpper
