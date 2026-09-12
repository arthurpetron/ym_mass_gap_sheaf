/-
# A null modulus is computable from the two Cauchy moduli

No witness is selected from the legacy propositional null relation. The
output rate is max(X.modulus(epsilon/10),Y.modulus(epsilon/10)). Two quadratic
triangle inequalities compare any term beyond that rate to a later pair
whose null bound is used ONLY inside a proof. The budget is 2+4+4=10.

Consequently the legacy and Type-modulated GNS completions are canonically
inverse, with unchanged representatives and inner products. This repairs an
overly strong historical claim that their comparison required choice.
-/

import YMGap.Continuum.GNSModulusCompletion

namespace YMGap.Continuum.GNSNullModulusRecovery

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion

local infix:50 " ≈ " => Q'.eqv

def nullTolerance (epsilon : Q') : Q' := Q'.mkPos 1 10 (by decide) * epsilon

theorem nullTolerance_pos {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < nullTolerance epsilon := Q'.mul_pos (by decide) he

private theorem ten_budget (epsilon : Q') :
    (nullTolerance epsilon + nullTolerance epsilon) +
      (((nullTolerance epsilon + nullTolerance epsilon) +
        (nullTolerance epsilon + nullTolerance epsilon)) +
       ((nullTolerance epsilon + nullTolerance epsilon) +
        (nullTolerance epsilon + nullTolerance epsilon))) ≈ epsilon := by
  let c : Q' := Q'.mkPos 1 10 (by decide)
  have htwo : nullTolerance epsilon + nullTolerance epsilon ≈ (c + c) * epsilon :=
    Q'.eqv_symm (Q'.add_mul_eqv c c epsilon)
  have hfour : (nullTolerance epsilon + nullTolerance epsilon) +
      (nullTolerance epsilon + nullTolerance epsilon) ≈ ((c + c) + (c + c)) * epsilon :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' htwo htwo) (Q'.eqv_symm (Q'.add_mul_eqv _ _ epsilon))
  have height := Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hfour hfour)
    (Q'.eqv_symm (Q'.add_mul_eqv _ _ epsilon))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' htwo height)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ epsilon))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ epsilon
        (by decide : (c + c) + (((c + c) + (c + c)) + ((c + c) + (c + c))) ≈ 1))
        (Q'.one_mul_eqv epsilon)))

/-- The rate does not inspect or extract the propositional null witness. -/
def nullRate {D : GNSData} (X Y : CauchyGNS D) (epsilon : Q') : Nat :=
  max (X.modulus (nullTolerance epsilon)) (Y.modulus (nullTolerance epsilon))

theorem nullRate_close {D : GNSData} {X Y : CauchyGNS D} (h : CauchyNull D X Y)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat) (hn : nullRate X Y epsilon ≤ n) :
    D.distSqQ (X.seq n) (Y.seq n) ≤ epsilon := by
  have hd := nullTolerance_pos he
  obtain ⟨N, hN⟩ := h (nullTolerance epsilon) hd
  let m := max N n
  have hnX := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnY := Nat.le_trans (Nat.le_max_right _ _) hn
  have hX := X.isCauchy _ hd n m hnX (Nat.le_trans hnX (Nat.le_max_right _ _))
  have hY := Y.isCauchy _ hd m n (Nat.le_trans hnY (Nat.le_max_right _ _)) hnY
  have hmiddle := hN m (Nat.le_max_left _ _)
  have hright := Q'.le_trans' _ _ _ (D.distSqQ_triangle (X.seq m) (Y.seq m) (Y.seq n))
    (Q'.add_le_add (Q'.add_le_add hmiddle hmiddle) (Q'.add_le_add hY hY))
  exact Q'.le_trans' _ _ _ (D.distSqQ_triangle (X.seq n) (X.seq m) (Y.seq n))
    (Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.add_le_add hX hX) (Q'.add_le_add hright hright))
      (Q'.le_of_eqv (ten_budget epsilon)))

/-- Recover Type-level closeness data using the already supplied Cauchy rates. -/
def recoverNullModulus {D : GNSData} {X Y : CauchyGNS D} (h : CauchyNull D X Y) :
    CauchyNullModulus D X Y where
  modulus := nullRate X Y
  close := nullRate_close h

/-- Canonical inverse to forgetting null moduli. -/
def fromLegacyCompletion (D : GNSData) : GNSCompletionSpace D → ModulatedGNSCompletionSpace D :=
  Quotient.lift (fun X => Quotient.mk (modulatedCauchySetoid D) X)
    (fun _ _ h => Quotient.sound ⟨recoverNullModulus h⟩)

theorem to_from_legacy (D : GNSData) (x : GNSCompletionSpace D) :
    toLegacyCompletion D (fromLegacyCompletion D x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  rfl

theorem from_to_legacy (D : GNSData) (x : ModulatedGNSCompletionSpace D) :
    fromLegacyCompletion D (toLegacyCompletion D x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  rfl

theorem fromLegacyCompletion_inner (D : GNSData) (x y : GNSCompletionSpace D) :
    modulatedCinnerCompl D (fromLegacyCompletion D x) (fromLegacyCompletion D y) =
      D.cinnerCompl x y := by
  rw [← toLegacyCompletion_inner, to_from_legacy, to_from_legacy]

end YMGap.Continuum.GNSNullModulusRecovery

#print axioms YMGap.Continuum.GNSNullModulusRecovery.nullRate
#print axioms YMGap.Continuum.GNSNullModulusRecovery.nullRate_close
#print axioms YMGap.Continuum.GNSNullModulusRecovery.recoverNullModulus
#print axioms YMGap.Continuum.GNSNullModulusRecovery.fromLegacyCompletion
#print axioms YMGap.Continuum.GNSNullModulusRecovery.to_from_legacy
#print axioms YMGap.Continuum.GNSNullModulusRecovery.from_to_legacy
#print axioms YMGap.Continuum.GNSNullModulusRecovery.fromLegacyCompletion_inner
