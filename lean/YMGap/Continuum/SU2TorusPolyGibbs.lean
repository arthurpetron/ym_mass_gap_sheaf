/-
# SU(2) Gibbs layer on the polynomial domain (replaces the vacuous `LinkHaar` route)

ADDITIVE.  `SU2TorusWilsonGibbs.LinkHaar SU2` / `ConfigHaar SU2 N` ask for an
invariant mean on ALL functions of the rational unit quaternions; that group is
non-amenable (free rank-2 subgroup), so they are empty and every theorem assuming
them is vacuous.  This file re-points the Schur and Gibbs statements to
YM Group Realizer's `SU2PolyLinkHaar.PolyLinkHaar` (functional on `RatPoly`).

* `PolySchurUpTo H J`, `PolyHaarAgreesUpTo H J`, `polySchurUpTo_of_agrees` (REDUCTION).
* `polyHaarAgreesUpTo2` and `polySchurUpTo2_constructed` (**DISCHARGED**) for the
  constructed `quaternionPolyLinkHaar2`.
* `PolyCharMeanUpTo H J`: `H(χ_s) ≈ δ_{s0}` for `s ≤ J`; `polyCharMeanUpTo2_constructed`
  (**DISCHARGED**, exact).
* Truncated character-sum Boltzmann weight `boltzmannPoly c J = Σ_{s≤J} c_s χ_s`
  (one relative plaquette `g₀g₁⁻¹`), `partitionPoly H c J := H(boltzmannPoly c J)`;
  `partitionPoly_eqv_c0` (from `PolyCharMeanUpTo`; so `Z > 0` iff `c₀ > 0`) and the
  discharged instance `partition_constructed`.

Still OPEN: polynomial invariance as a field, positivity on squares, Schur for
general `s`, the full torus (multi-plaquette) polynomial Gibbs measure, and the
identification of `c_s` with the Wilson character coefficients (Bessel ratios).
U(1) rule: the character-mean / Schur data are SU(2)-specific (dimensions `s+1`);
the truncated-sum algebra itself is group-blind.  Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.SU2PolyLinkHaar

namespace YMGap.Continuum.SU2TorusPolyGibbs

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2PolyLinkHaar
open YMGap.Continuum.SU2TorusSchurSmall (pairing polySchurUpTo2)

/-- Schur up to spin `J` on a polynomial link Haar. -/
def PolySchurUpTo (H : PolyLinkHaar) (J : Nat) : Prop :=
  ∀ s t, s ≤ J → t ≤ J →
    (H.h (polyMul (relativeCharacter s) (relativeCharacter t))).eqv (if s = t then 1 else 0)

/-- Agreement with the exact `quaternionHaar 2` pairing up to spin `J`. -/
def PolyHaarAgreesUpTo (H : PolyLinkHaar) (J : Nat) : Prop :=
  ∀ s t, s ≤ J → t ≤ J →
    (H.h (polyMul (relativeCharacter s) (relativeCharacter t))).eqv (pairing s t)

theorem polySchurUpTo_of_agrees {H : PolyLinkHaar} (hA : PolyHaarAgreesUpTo H 2) :
    PolySchurUpTo H 2 := fun s t hs ht =>
  Q'.eqv_trans _ _ _ (hA s t hs ht) (polySchurUpTo2 s t hs ht)

/-- **DISCHARGED**: agreement for the constructed functional. -/
theorem polyHaarAgreesUpTo2 : PolyHaarAgreesUpTo quaternionPolyLinkHaar2 2 :=
  fun s t _ _ => by rw [polyHaarAgrees]; exact Q'.eqv_refl _

/-- **DISCHARGED**: Schur `s, t ≤ 2` for the constructed functional. -/
theorem polySchurUpTo2_constructed : PolySchurUpTo quaternionPolyLinkHaar2 2 :=
  polySchurUpTo_of_agrees polyHaarAgreesUpTo2

/-- Character means `H(χ_s) ≈ δ_{s0}` up to spin `J`. -/
def PolyCharMeanUpTo (H : PolyLinkHaar) (J : Nat) : Prop :=
  ∀ s, s ≤ J → (H.h (relativeCharacter s)).eqv (if s = 0 then 1 else 0)

set_option maxRecDepth 100000 in
theorem charMean0 : (quaternionHaar 2 (relativeCharacter 0)).eqv 1 := by decide
set_option maxRecDepth 100000 in
theorem charMean1 : (quaternionHaar 2 (relativeCharacter 1)).eqv 0 := by decide
set_option maxRecDepth 100000 in
theorem charMean2 : (quaternionHaar 2 (relativeCharacter 2)).eqv 0 := by decide

/-- **DISCHARGED** (exact). -/
theorem polyCharMeanUpTo2_constructed : PolyCharMeanUpTo quaternionPolyLinkHaar2 2
  | 0, _ => charMean0
  | 1, _ => charMean1
  | 2, _ => charMean2
  | s + 3, h => absurd h (by omega)

/-- Truncated character-sum Boltzmann weight `Σ_{s≤J} c_s χ_s` of one relative plaquette. -/
def boltzmannPoly (c : Nat → Q') : Nat → RatPoly
  | 0 => polySmul (c 0) (relativeCharacter 0)
  | J + 1 => polyAdd (boltzmannPoly c J) (polySmul (c (J + 1)) (relativeCharacter (J + 1)))

def partitionPoly (H : PolyLinkHaar) (c : Nat → Q') (J : Nat) : Q' := H.h (boltzmannPoly c J)

/-- **PROVED (REDUCTION)**: character means up to `J` ⇒ `Z ≈ c₀`. -/
theorem partitionPoly_eqv_c0 (H : PolyLinkHaar) (c : Nat → Q') :
    ∀ J, PolyCharMeanUpTo H J → (partitionPoly H c J).eqv (c 0)
  | 0, hm => by
      show (H.h (polySmul (c 0) (relativeCharacter 0))).eqv (c 0)
      refine Q'.eqv_trans _ _ _ (H.smul _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (hm 0 (Nat.le_refl 0))) ?_
      exact Q'.mul_one_eqv _
  | J + 1, hm => by
      show (H.h (polyAdd (boltzmannPoly c J)
        (polySmul (c (J + 1)) (relativeCharacter (J + 1))))).eqv (c 0)
      have ih := partitionPoly_eqv_c0 H c J (fun s hs => hm s (Nat.le_succ_of_le hs))
      have h1 : (H.h (polySmul (c (J + 1)) (relativeCharacter (J + 1)))).eqv 0 := by
        refine Q'.eqv_trans _ _ _ (H.smul _ _) ?_
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (hm (J + 1) (Nat.le_refl _))) ?_
        show (c (J + 1) * 0).eqv 0
        exact Q'.mul_zero_eqv _
      refine Q'.eqv_trans _ _ _ (H.add _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ih h1) ?_
      exact YMGap.Constructive.QPoly.q_add_zero_eqv _

/-- **DISCHARGED**: on the constructed functional, `Z_J ≈ c₀` for `J ≤ 2`. -/
theorem partition_constructed (c : Nat → Q') (J : Nat) (hJ : J ≤ 2) :
    (partitionPoly quaternionPolyLinkHaar2 c J).eqv (c 0) :=
  partitionPoly_eqv_c0 _ c J fun s hs => polyCharMeanUpTo2_constructed s (Nat.le_trans hs hJ)

end YMGap.Continuum.SU2TorusPolyGibbs

#print axioms YMGap.Continuum.SU2TorusPolyGibbs.polySchurUpTo2_constructed
#print axioms YMGap.Continuum.SU2TorusPolyGibbs.polyCharMeanUpTo2_constructed
#print axioms YMGap.Continuum.SU2TorusPolyGibbs.partition_constructed
