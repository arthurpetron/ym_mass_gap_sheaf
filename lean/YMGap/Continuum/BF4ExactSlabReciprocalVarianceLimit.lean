/-
# The reciprocal two-head replica integral converges to the actual energy

An explicit max modulus combines the original pairing-loss modulus with
the geometric normalization-defect cutoff. The resulting variance limit
is the squared residual of the EXISTING conditional projection. Exact
two-head Fubini then identifies the actual replica-integral limit with
twice that energy. Cross-exterior path transport and coercivity remain open.
-/

import YMGap.Continuum.BF4ExactSlabReciprocalEnergyError
import YMGap.Continuum.BF4ExactSlabReciprocalEnergyLimit
import YMGap.Constructive.CRealLimitClose

namespace YMGap.Continuum.BF4ExactSlabReciprocalVarianceLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing
open YMGap.Continuum.BF4ExactSlabReciprocalEnergyError
open YMGap.Continuum.BF4ExactSlabReciprocalEnergyLimit
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "V" => varianceEnergy hw0 hw1 K extent hK link hl
local notation "L" => finiteLoss hw0 hw1 K extent hK link
local notation "R" => replicaIntegral hw0 hw1 K extent hK link hl

private theorem two_step {a b c epsilon : Q'}
    (hab : a ≤ b + HalfPow.half * epsilon)
    (hbc : b ≤ c + HalfPow.half * epsilon) : a ≤ c + epsilon :=
  Q'.le_trans' _ _ _ hab
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hbc)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (ExpNeg.two_halves epsilon)))))

/-- The loss modulus and the original-norm geometric cutoff suffice; no
modulus is extracted from a proposition or quotient representative. -/
def varianceCauchy (p : (F).V) : QCauchy (V p) where
  M epsilon := max
    ((finiteLossCauchy hw0 hw1 K extent hK link hl p).M (HalfPow.half * epsilon))
    (errorCutoff hw0 hw1 K extent hK link p (HalfPow.half * epsilon))
  bound := by
    intro epsilon he i j hi hj
    have hs := ExpNeg.half_mul_pos epsilon he
    have hc := (finiteLossCauchy hw0 hw1 K extent hK link hl p).bound
      _ hs i j (Nat.le_trans (Nat.le_max_left _ _) hi)
        (Nat.le_trans (Nat.le_max_left _ _) hj)
    have hb (k : Nat)
        (hk : errorCutoff hw0 hw1 K extent hK link p (HalfPow.half * epsilon) ≤ k) :
        L p k ≤ V p k + HalfPow.half * epsilon :=
      finiteLoss_le_varianceEnergy_add hw0 hw1 K extent hK link hl p _ hs k hk
    exact ⟨Q'.le_trans' _ _ _
      (varianceEnergy_le_finiteLoss hw0 hw1 K extent hK link hl p i)
      (two_step hc.1 (hb j (Nat.le_trans (Nat.le_max_right _ _) hj))),
      Q'.le_trans' _ _ _
      (varianceEnergy_le_finiteLoss hw0 hw1 K extent hK link hl p j)
      (two_step hc.2 (hb i (Nat.le_trans (Nat.le_max_right _ _) hi)))⟩

def varianceReal (p : (F).V) : CReal :=
  ofQ'CauchySeq (V p) (varianceCauchy hw0 hw1 K extent hK link hl p)

theorem varianceReal_converges (p : (F).V) :
    ConvergesTo (fun k => ofQ' (V p k))
      (varianceReal hw0 hw1 K extent hK link hl p) :=
  convergesTo_ofQ'CauchySeq _ _

private theorem limits_equiv_of_sandwich (a b : Nat → Q')
    {A B : CReal}
    (hA : ConvergesTo (fun k => ofQ' (a k)) A)
    (hB : ConvergesTo (fun k => ofQ' (b k)) B)
    (cut : Q' → Nat) (hlo : ∀ k, a k ≤ b k)
    (hhi : ∀ epsilon, (0 : Q') < epsilon → ∀ k, cut epsilon ≤ k →
      b k ≤ a k + epsilon) : Equiv A B := by
  refine Equiv_of_limit_of_close
    (aSeq := fun k => ofQ' (a k)) (bSeq := fun k => ofQ' (b k)) hA hB ?_
  intro epsilon he
  refine ⟨cut epsilon, fun k hk => ⟨0, fun _ _ => ?_⟩⟩
  exact ⟨Q'.le_trans' _ _ _ (hlo k)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)), hhi epsilon he k hk⟩

theorem varianceReal_equiv_finiteLossReal (p : (F).V) :
    Equiv (varianceReal hw0 hw1 K extent hK link hl p)
      (finiteLossReal hw0 hw1 K extent hK link hl p) :=
  limits_equiv_of_sandwich (V p) (L p)
    (varianceReal_converges hw0 hw1 K extent hK link hl p)
    (finiteLossReal_converges hw0 hw1 K extent hK link hl p)
    (errorCutoff hw0 hw1 K extent hK link p)
    (varianceEnergy_le_finiteLoss hw0 hw1 K extent hK link hl p)
    (finiteLoss_le_varianceEnergy_add hw0 hw1 K extent hK link hl p)

/-- The normalized-variance limit is the SAME original completed residual
energy, not the unnormalized determinant or an independently supplied law. -/
theorem variance_limit_eq_residual_norm (p : (F).V) :
    Quotient.mk crealSetoid (varianceReal hw0 hw1 K extent hK link hl p) =
      normSq ((projections hw0 hw1 K extent hK).residual ⟨link,hl⟩ (embedV F p)) :=
  (Quotient.sound (varianceReal_equiv_finiteLossReal hw0 hw1 K extent hK link hl p)).trans
    (finiteLoss_limit_eq_residual_norm hw0 hw1 K extent hK link hl p)

private theorem double_budget {a b epsilon : Q'}
    (h : a ≤ b + HalfPow.half * epsilon) : a+a ≤ (b+b)+epsilon :=
  Q'.le_trans' _ _ _ (Q'.add_le_add h h)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.regroup b b (HalfPow.half * epsilon))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (ExpNeg.two_halves epsilon))))

/-- Explicit Cauchy data for the literal two-head replica integrals. -/
def replicaCauchy (p : (F).V) : QCauchy (R p) where
  M epsilon := (varianceCauchy hw0 hw1 K extent hK link hl p).M (HalfPow.half * epsilon)
  bound := by
    intro epsilon he i j hi hj
    have hc := (varianceCauchy hw0 hw1 K extent hK link hl p).bound
      _ (ExpNeg.half_mul_pos epsilon he) i j hi hj
    have step (a b : Nat) (h : V p a ≤ V p b + HalfPow.half * epsilon) :
        R p a ≤ R p b + epsilon :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (replicaIntegral_pin hw0 hw1 K extent hK link hl p a))
        (Q'.le_trans' _ _ _ (double_budget h)
          (Q'.add_le_add_right _ _ epsilon
            (Q'.ge_of_eqv (replicaIntegral_pin hw0 hw1 K extent hK link hl p b))))
    exact ⟨step i j hc.1, step j i hc.2⟩

def replicaReal (p : (F).V) : CReal :=
  ofQ'CauchySeq (R p) (replicaCauchy hw0 hw1 K extent hK link hl p)

theorem replicaReal_converges (p : (F).V) :
    ConvergesTo (fun k => ofQ' (R p k))
      (replicaReal hw0 hw1 K extent hK link hl p) :=
  convergesTo_ofQ'CauchySeq _ _

private theorem limit_equiv_double (r v : Nat → Q') {A B : CReal}
    (hr : ∀ k, (r k).eqv (v k + v k))
    (hA : ConvergesTo (fun k => ofQ' (r k)) A)
    (hB : ConvergesTo (fun k => ofQ' (v k)) B) : Equiv A (add B B) := by
  refine Equiv_of_limit_of_equal
    (aSeq := fun k => ofQ' (r k))
    (bSeq := fun k => add (ofQ' (v k)) (ofQ' (v k))) ?_
    hA (convergesTo_add hB hB)
  intro k
  change Equiv (ofQ' (r k)) (ofQ' (v k + v k))
  exact ofQ'_equiv_of_eqv (hr k)

/-- The reciprocal two-HEAD-copy limit is twice the actual conditional
residual energy. Cross-EXTERIOR path transport is a separate open identity. -/
theorem replica_limit_eq_twice_residual_norm (p : (F).V) :
    Quotient.mk crealSetoid (replicaReal hw0 hw1 K extent hK link hl p) =
      RCadd
        (normSq ((projections hw0 hw1 K extent hK).residual ⟨link,hl⟩ (embedV F p)))
        (normSq ((projections hw0 hw1 K extent hK).residual ⟨link,hl⟩ (embedV F p))) := by
  have he : Equiv (replicaReal hw0 hw1 K extent hK link hl p)
      (add (varianceReal hw0 hw1 K extent hK link hl p)
        (varianceReal hw0 hw1 K extent hK link hl p)) :=
    limit_equiv_double (R p) (V p)
      (replicaIntegral_pin hw0 hw1 K extent hK link hl p)
      (replicaReal_converges hw0 hw1 K extent hK link hl p)
      (varianceReal_converges hw0 hw1 K extent hK link hl p)
  exact (Quotient.sound he).trans (congrArg (fun x => RCadd x x)
    (variance_limit_eq_residual_norm hw0 hw1 K extent hK link hl p))

#print axioms varianceCauchy
#print axioms varianceReal
#print axioms varianceReal_converges
#print axioms varianceReal_equiv_finiteLossReal
#print axioms variance_limit_eq_residual_norm
#print axioms replicaCauchy
#print axioms replicaReal
#print axioms replicaReal_converges
#print axioms replica_limit_eq_twice_residual_norm

end YMGap.Continuum.BF4ExactSlabReciprocalVarianceLimit
