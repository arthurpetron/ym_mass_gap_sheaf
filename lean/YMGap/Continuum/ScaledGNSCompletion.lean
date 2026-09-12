/-
# Completion under a controlled positive constructive-real normalization

For c <= lambda <= 1 with explicit c>0 and a regularity modulus for lambda,
the rational GNS form and lambda times that form have canonically equivalent
Cauchy completions. Representatives are unchanged. Forward Cauchy moduli are
unchanged; inverse moduli evaluate the supplied rate at c*epsilon. Null
modulus recovery avoids choosing any witness from a propositional limit.
-/

import YMGap.Continuum.GNSNullModulusRecovery
import YMGap.Continuum.CRealSeminormCompletion
import YMGap.Continuum.RCDistBridge
import YMGap.Continuum.RCCauchySchwarz
import YMGap.Continuum.FCLimitContinuity
import YMGap.Constructive.TrigAddCReal
import YMGap.Constructive.CRealInnerRegularity

namespace YMGap.Continuum.ScaledGNSCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSNullModulusRecovery
open YMGap.Continuum.CRealSeminormCompletion

local infix:50 " ≈ " => Q'.eqv

structure Normalization where
  value : CReal
  regularity : CReal.InnerRegularity value
  floor : Q'
  floor_pos : (0 : Q') < floor
  lower : ∀ K, floor ≤ value.approx K
  upper : ∀ K, value.approx K ≤ (1 : Q')

variable (D : GNSData) (N : Normalization)

def scaledDist (x y : D.V) : CReal := CReal.mul (CReal.ofQ' (D.distSqQ x y)) N.value

def scaledDistRegularity (x y : D.V) : CReal.InnerRegularity (scaledDist D N x y) :=
  N.regularity.scaleLeftSigned (D.distSqQ x y)

private theorem pointwise_le {a b : CReal} (h : ∀ K, a.approx K ≤ b.approx K) : CReal.leEv a b := by
  apply CReal.leEv_of_le
  intro K
  exact Q'.le_trans' _ _ _ (h K)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos K)))

theorem scaledDist_lower (x y : D.V) :
    CReal.leEv (CReal.ofQ' (N.floor * D.distSqQ x y)) (scaledDist D N x y) := by
  apply pointwise_le
  intro K
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (N.lower K) (D.self_nonneg (D.sub x y)))
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

theorem scaledDist_upper (x y : D.V) :
    CReal.leEv (scaledDist D N x y) (CReal.ofQ' (D.distSqQ x y)) := by
  apply pointwise_le
  intro K
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (N.upper K) (D.self_nonneg (D.sub x y)))
    (Q'.le_of_eqv (Q'.mul_one_eqv _))

theorem rawDist_le_of_scaledDist_le (x y : D.V) (epsilon : Q')
    (h : CReal.leEv (scaledDist D N x y) (CReal.ofQ' (N.floor * epsilon))) :
    D.distSqQ x y ≤ epsilon :=
  Q'.le_of_mul_le_mul_left
    (GNSData.RCofQ'_le_reflect (CReal.leEv_trans (scaledDist_lower D N x y) h)) N.floor_pos

theorem scaledDist_null_iff (x y : D.V) :
    CReal.Equiv (scaledDist D N x y) CReal.czero ↔ D.rad x y := by
  constructor
  · intro h
    have hb : CReal.leEv (scaledDist D N x y) (CReal.ofQ' (N.floor * 0)) :=
      CReal.leEv_trans (CReal.leEv_of_equiv h)
        (CReal.leEv_of_equiv (CReal.ofQ'_equiv_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv _))))
    exact Q'.eqv_of_le_le (rawDist_le_of_scaledDist_le D N x y 0 hb) (D.self_nonneg (D.sub x y))
  · intro h
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.zero_mul_eqv _))

/-- The positive scaled form supplies every squared-seminorm law. -/
def scaledSeminorm : SquaredSeminorm where
  Carrier := D.V
  distSq := scaledDist D N
  distSq_refl := fun x => (scaledDist_null_iff D N x x).2 (D.rad_refl x)
  distSq_symm := fun x y => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.mul_eqv_congr_right _ _ _ (D.distSqQ_comm x y))
  distSq_nonneg := fun x y => pointwise_le (fun K =>
    Q'.mul_nonneg _ _ (D.self_nonneg (D.sub x y))
      (Q'.le_trans' _ _ _ (Q'.le_of_lt N.floor_pos) (N.lower K)))
  distSq_triangle := by
    intro x y z
    apply pointwise_le
    intro K
    have h := Q'.mul_le_mul_of_nonneg_right _ _ (N.value.approx K)
      (D.distSqQ_triangle x y z) (Q'.le_trans' _ _ _ (Q'.le_of_lt N.floor_pos) (N.lower K))
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr' (Q'.add_mul_eqv _ _ _) (Q'.add_mul_eqv _ _ _))))
  null_congr := by
    intro x x' y y' hx hy
    have hsub := D.rad_add ((scaledDist_null_iff D N x x').1 hx)
      (D.rad_neg ((scaledDist_null_iff D N y y').1 hy))
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.mul_eqv_congr_right _ _ _ (D.B_welldef hsub hsub))

local notation "S" => scaledSeminorm D N

/-- Forward rate: unchanged. -/
def toScaledCauchy (X : CauchyGNS D) : (S).Cauchy where
  seq := X.seq
  modulus := X.modulus
  isCauchy := fun e he m n hm hn => CReal.leEv_trans (scaledDist_upper D N _ _)
    (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (X.isCauchy e he m n hm hn)))

/-- Inverse rate: epsilon is replaced by floor*epsilon, explicitly. -/
def toRawCauchy (X : (S).Cauchy) : CauchyGNS D where
  seq := X.seq
  modulus := fun e => X.modulus (N.floor * e)
  isCauchy := fun e he m n hm hn => rawDist_le_of_scaledDist_le D N _ _ e
    (X.isCauchy _ (Q'.mul_pos N.floor_pos he) m n hm hn)

def toScaledClose {X Y : CauchyGNS D} (h : GNSModulusCompletion.CauchyNullModulus D X Y) :
    (S).Close (toScaledCauchy D N X) (toScaledCauchy D N Y) where
  modulus := h.modulus
  close := fun e he n hn => CReal.leEv_trans (scaledDist_upper D N _ _)
    (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (h.close e he n hn)))

def toRawClose {X Y : (S).Cauchy} (h : (S).Close X Y) :
    GNSModulusCompletion.CauchyNullModulus D (toRawCauchy D N X) (toRawCauchy D N Y) where
  modulus := fun e => h.modulus (N.floor * e)
  close := fun e he n hn => rawDist_le_of_scaledDist_le D N _ _ e
    (h.close _ (Q'.mul_pos N.floor_pos he) n hn)

/-- Canonical completion map; null moduli are recovered, never selected. -/
def toScaledCompletion : GNSCompletionSpace D → (S).Completion :=
  Quotient.lift (fun X => Quotient.mk (S).completionSetoid (toScaledCauchy D N X))
    (fun _ _ h => Quotient.sound ⟨toScaledClose D N (recoverNullModulus h)⟩)

def toRawCompletion : (S).Completion → GNSCompletionSpace D :=
  Quotient.lift (fun X => Quotient.mk (cauchySetoid D) (toRawCauchy D N X))
    (fun _ _ h => by
      rcases h with ⟨hdata⟩
      exact Quotient.sound (toRawClose D N hdata).toCauchyNull)

theorem raw_scaled_inverse (x : GNSCompletionSpace D) :
    toRawCompletion D N (toScaledCompletion D N x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (cauchyNull_refl D X)

theorem scaled_raw_inverse (x : (S).Completion) :
    toScaledCompletion D N (toRawCompletion D N x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  refine ⟨{ modulus := fun _ => 0, close := ?_ }⟩
  intro e he n _
  exact CReal.leEv_trans (CReal.leEv_of_equiv ((S).distSq_refl (X.seq n)))
    (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (Q'.le_of_lt he)))

theorem toScaledCompletion_embed (x : D.V) :
    toScaledCompletion D N (embedV D x) = (S).embedRep x := rfl

theorem toRawCompletion_embed (x : D.V) :
    toRawCompletion D N ((S).embedRep x) = embedV D x := rfl

/-- Transported full form, normalized by the SAME constructive scalar. -/
def scaledCompletedInner (x y : (S).Completion) : CReal.RC :=
  CReal.RCmul (D.cinnerCompl (toRawCompletion D N x) (toRawCompletion D N y))
    (Quotient.mk CReal.crealSetoid N.value)

theorem scaledCompletedInner_embed (x y : D.V) :
    scaledCompletedInner D N ((S).embedRep x) ((S).embedRep y) =
      Quotient.mk CReal.crealSetoid (CReal.mul (CReal.ofQ' (D.B x y)) N.value) := by
  unfold scaledCompletedInner
  rw [toRawCompletion_embed, toRawCompletion_embed]
  exact congrArg (fun r => CReal.RCmul r (Quotient.mk CReal.crealSetoid N.value))
    (D.cinnerCompl_embed x y)

theorem scaledCompletedInner_comparison (x y : GNSCompletionSpace D) :
    scaledCompletedInner D N (toScaledCompletion D N x) (toScaledCompletion D N y) =
      CReal.RCmul (D.cinnerCompl x y) (Quotient.mk CReal.crealSetoid N.value) := by
  unfold scaledCompletedInner
  rw [raw_scaled_inverse, raw_scaled_inverse]

/-- The full completed form is represented by this explicit CReal product. -/
def scaledPairingRep (X Y : (S).Cauchy) : CReal :=
  CReal.mul (D.cinnerRep (toRawCauchy D N X) (toRawCauchy D N Y)) N.value

theorem scaledCompletedInner_mk (X Y : (S).Cauchy) :
    scaledCompletedInner D N (Quotient.mk (S).completionSetoid X)
      (Quotient.mk (S).completionSetoid Y) =
      Quotient.mk CReal.crealSetoid (scaledPairingRep D N X Y) := rfl

/-- The transported inner form is the limit of the SAME scaled dense forms. -/
theorem scaledPairingRep_converges (X Y : (S).Cauchy) :
    CReal.ConvergesTo (fun n => CReal.mul (CReal.ofQ' (D.B (X.seq n) (Y.seq n))) N.value)
      (scaledPairingRep D N X Y) := by
  have h := CReal.convergesTo_const_mul N.value
    (CReal.convergesTo_ofQ'CauchySeq _ (D.cInnerQCauchy (toRawCauchy D N X) (toRawCauchy D N Y)))
  apply CReal.convergesTo_limit_congr
    (TrigAddCReal.convergesTo_congr_seq (fun n => CRealAlg.cmul_comm _ _) h)
  exact CRealAlg.cmul_comm _ _

end YMGap.Continuum.ScaledGNSCompletion

#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledDistRegularity
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledDist_lower
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledDist_upper
#print axioms YMGap.Continuum.ScaledGNSCompletion.rawDist_le_of_scaledDist_le
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledDist_null_iff
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledSeminorm
#print axioms YMGap.Continuum.ScaledGNSCompletion.toScaledCauchy
#print axioms YMGap.Continuum.ScaledGNSCompletion.toRawCauchy
#print axioms YMGap.Continuum.ScaledGNSCompletion.toScaledClose
#print axioms YMGap.Continuum.ScaledGNSCompletion.toRawClose
#print axioms YMGap.Continuum.ScaledGNSCompletion.toScaledCompletion
#print axioms YMGap.Continuum.ScaledGNSCompletion.toRawCompletion
#print axioms YMGap.Continuum.ScaledGNSCompletion.raw_scaled_inverse
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaled_raw_inverse
#print axioms YMGap.Continuum.ScaledGNSCompletion.toScaledCompletion_embed
#print axioms YMGap.Continuum.ScaledGNSCompletion.toRawCompletion_embed
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledCompletedInner
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledCompletedInner_embed
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledCompletedInner_comparison
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledPairingRep
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledCompletedInner_mk
#print axioms YMGap.Continuum.ScaledGNSCompletion.scaledPairingRep_converges
