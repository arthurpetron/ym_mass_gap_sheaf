/-
# Torus RP (d5b): the conjugation twist on split crossing plaquettes

`Ctw a T` conjugates exactly the second-half blocks selected by `T` (fresh split partners). On the split crossing
plaquette words (direct orientation; left split at `t = 0`, right split at `t = M`), `Ctw` produces exactly the
words of `rpk_cross0_cv` / `rpk_crossM_cv`, so `Ctw (T_K[split])` is an RPK (`rpk_C_cross0`, `rpk_C_crossM`).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPCrossCoord
import YMGap.Continuum.SU2TorusRPThetaConj

namespace YMGap.Continuum.SU2TorusRPCrossC

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub qpe_trans qpe_mul qpe_conj qmul_sub qconj_sub TK_word_sub)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl)
open YMGap.Continuum.SU2TorusRPCore (RPK rpk_congr)
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly)
open YMGap.Continuum.SU2WilsonActivity (wilsonA)
open PolyQuaternion (mul conj)

local notation "cv" => PolyQuaternion.coordinateVariable

theorem qpe_refl (n : Nat) (q : PolyQuaternion) : QPE n q q :=
  ⟨pe_refl n _, pe_refl n _, pe_refl n _, pe_refl n _⟩

/-- Second-half selector. -/
def secT (a : Nat) (T : Nat → Bool) (b : Nat) : Bool := decide (a ≤ b) && T b

/-- The conjugation twist. -/
def Ctw (a : Nat) (T : Nat → Bool) : RatPoly → RatPoly :=
  signSelectedPolynomial (4 * (a + a)) (conjSel (secT a T))

theorem Ctw_ringSub (a : Nat) (T : Nat → Bool) : RingSub (a + a) (Ctw a T) :=
  YMGap.Continuum.SU2TorusRPConj.conj_ringSub _ _ _

theorem C_fix {a : Nat} (T : Nat → Bool) {b : Nat} (hb : b < a) : QPE (a + a) (qsub (Ctw a T) (cv b)) (cv b) := by
  have h := YMGap.Continuum.SU2TorusRPThetaConj.conj_coord (a + a) (secT a T) b (by omega)
  have hs : secT a T b = false := by
    unfold secT; rw [decide_eq_false (by omega)]; rfl
  unfold Ctw; rw [h, hs, if_neg (by decide)]; exact qpe_refl _ _

theorem C_fixT {a : Nat} (T : Nat → Bool) {b : Nat} (hb : b < a + a) (hT : T b = false) :
    QPE (a + a) (qsub (Ctw a T) (cv b)) (cv b) := by
  have h := YMGap.Continuum.SU2TorusRPThetaConj.conj_coord (a + a) (secT a T) b hb
  have hs : secT a T b = false := by unfold secT; rw [hT, Bool.and_false]
  unfold Ctw; rw [h, hs, if_neg (by decide)]; exact qpe_refl _ _

theorem C_conj {a : Nat} (T : Nat → Bool) {b : Nat} (hab : a ≤ b) (hb : b < a + a) (hT : T b = true) :
    QPE (a + a) (qsub (Ctw a T) (cv b)) (conj (cv b)) := by
  have h := YMGap.Continuum.SU2TorusRPThetaConj.conj_coord (a + a) (secT a T) b hb
  have hs : secT a T b = true := by unfold secT; rw [hT, decide_eq_true hab]; rfl
  unfold Ctw; rw [h, hs, if_pos rfl]; exact qpe_refl _ _

variable {a : Nat} {β : Q'} (K : Nat) (T : Nat → Bool)

theorem rpk_C_cross0 (hβ : (0 : Q') ≤ β) (s1 p s2 : Nat) (h1 : s1 < a) (hp : p < a) (h2 : s2 < a)
    (hT1 : T (s1 + a) = true) (hT2 : T (s2 + a) = true) (hTp : T (p + a) = false) :
    RPK a (Ctw a T (wilsonPoly
      (mul (mul (mul (cv (s1 + a)) (cv s1)) (cv p))
        (mul (conj (mul (cv (s2 + a)) (cv s2))) (conj (cv (p + a))))).scalar (wilsonA β) K)) := by
  have hS := Ctw_ringSub a T
  refine rpk_congr (pe_trans _ (TK_word_sub hS _ _ _ _ _ K)
    (YMGap.Continuum.SU2TorusRPSubst.wilsonPoly_pe _ ?_ _ K)) (YMGap.Continuum.SU2TorusRPCrossCoord.rpk_cross0_cv hβ K s1 p s2 h1 hp h2)
  exact (qpe_mul (qpe_mul (qpe_trans (qmul_sub hS _ _) (qpe_mul (C_conj T (by omega) (by omega) hT1) (C_fix T h1)))
      (C_fix T hp))
    (qpe_mul (qpe_conj (qpe_trans (qmul_sub hS _ _) (qpe_mul (C_conj T (by omega) (by omega) hT2) (C_fix T h2))))
      (qpe_conj (C_fixT T (by omega) hTp)))).s

theorem rpk_C_crossM (hβ : (0 : Q') ≤ β) (s1 p s2 : Nat) (h1 : s1 < a) (hp : p < a) (h2 : s2 < a)
    (hT1 : T (s1 + a) = true) (hT2 : T (s2 + a) = true) (hTp : T (p + a) = false) :
    RPK a (Ctw a T (wilsonPoly
      (mul (mul (mul (cv s1) (cv (s1 + a))) (cv (p + a)))
        (mul (conj (mul (cv s2) (cv (s2 + a)))) (conj (cv p)))).scalar (wilsonA β) K)) := by
  have hS := Ctw_ringSub a T
  refine rpk_congr (pe_trans _ (TK_word_sub hS _ _ _ _ _ K)
    (YMGap.Continuum.SU2TorusRPSubst.wilsonPoly_pe _ ?_ _ K)) (YMGap.Continuum.SU2TorusRPCrossCoord.rpk_crossM_cv hβ K s1 p s2 h1 hp h2)
  exact (qpe_mul (qpe_mul (qpe_trans (qmul_sub hS _ _) (qpe_mul (C_fix T h1) (C_conj T (by omega) (by omega) hT1)))
      (C_fixT T (by omega) hTp))
    (qpe_mul (qpe_conj (qpe_trans (qmul_sub hS _ _) (qpe_mul (C_fix T h2) (C_conj T (by omega) (by omega) hT2))))
      (qpe_conj (C_fix T hp)))).s

end YMGap.Continuum.SU2TorusRPCrossC

#print axioms YMGap.Continuum.SU2TorusRPCrossC.rpk_C_cross0
#print axioms YMGap.Continuum.SU2TorusRPCrossC.rpk_C_crossM
