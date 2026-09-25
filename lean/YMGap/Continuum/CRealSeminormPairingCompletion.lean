/-
# Choice-free mixed-pairing completion on the same squared-seminorm quotient

Computed closeness rates prove that the representative scalar limit is
independent of both supplied representatives. Quotient.lift₂ constructs
the completed pairing on D.Completion itself. Dense symmetry and diagonal
positivity, when supplied, pass through these same scalar limits.

No stream uniform bound, completed pairing, selected representative,
metric completeness or positive-definiteness assumption is introduced.
-/

import YMGap.Continuum.CRealSeminormPairingCompletionLimit
import YMGap.Constructive.CRealLimitClose
import YMGap.Continuum.RCCauchySchwarz

namespace YMGap.Continuum.CRealSeminormPairingCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance_pos)

variable {D : SquaredSeminorm} (P : PairingData D)

/-- The changed first and original second representatives supply the two
computed ceilings; both given closeness moduli remain explicit. -/
def closeRate {X X' Y Y' : D.Cauchy} (hX : D.Close X X') (hY : D.Close Y Y')
    (epsilon : Q') : Nat :=
  max (max (normBase P X') (normBase P Y))
    (max (hX.modulus (pairDelta P X' Y epsilon))
      (hY.modulus (pairDelta P X' Y epsilon)))

theorem pairSequence_close {X X' Y Y' : D.Cauchy}
    (hX : D.Close X X') (hY : D.Close Y Y')
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : closeRate P hX hY epsilon ≤ n) :
    leRat (sub (pairSequence P X Y n)
      (pairSequence P X' Y' n)) epsilon ∧
    leRat (sub (pairSequence P X' Y' n)
      (pairSequence P X Y n)) epsilon := by
  let B := pairCeiling P X' Y
  let hB := pairCeiling_nonnegative P X' Y
  let delta := pairDelta P X' Y epsilon
  have hdeltaPos : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hnX' : normBase P X' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnY : normBase P Y ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnX : hX.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnY' : hY.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact P.pairing_close (X.seq n) (X'.seq n) (Y.seq n) (Y'.seq n)
    B hB epsilon he (hX.close delta hdeltaPos n hnX) (hY.close delta hdeltaPos n hnY')
    (leRat_mono (diagonal_le_normCeiling P Y n hnY) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling P X' n hnX') (Q'.le_max'_left _ _))

theorem representativeInner_welldef {X X' Y Y' : D.Cauchy}
    (hX : D.Close X X') (hY : D.Close Y Y') :
    Equiv (representativeInner P X Y)
      (representativeInner P X' Y') := by
  apply Equiv_of_limit_of_close (pairSequence_converges P X Y)
    (pairSequence_converges P X' Y')
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  refine ⟨closeRate P hX hY (HalfPow.half*epsilon), fun n hn => ?_⟩
  have h := pairSequence_close P hX hY (HalfPow.half*epsilon) hh n hn
  obtain ⟨K, hK⟩ := evTwoSided_of_leRat h.1 h.2 hh
  refine ⟨K, fun k hk => ?_⟩
  exact ⟨Q'.le_trans' _ _ _ (hK k hk).1
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    Q'.le_trans' _ _ _ (hK k hk).2
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

/-! A Cauchy stream is a genuine dense approximation in the second pairing
argument.  The proof keeps the stream's supplied modulus and uses the same
finite `pairing_close` estimate as the mixed-limit construction; no quotient
representative is selected and no completed continuity axiom is added. -/

theorem representativeInner_right_stage_converges
    (X Y : D.Cauchy) :
    ConvergesTo
      (fun n => representativeInner P X (D.constant (Y.seq n)))
      (representativeInner P X Y) := by
  intro epsilon hepsilon
  let q : Q' := HalfPow.half * (HalfPow.half * epsilon)
  have hqpos : (0 : Q') < q :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)
  let B : Q' := pairCeiling P X Y
  have hB : (0 : Q') ≤ B := pairCeiling_nonnegative P X Y
  let delta : Q' := pairDelta P X Y q
  have hdelta : (0 : Q') < delta := pairingTolerance_pos B hB hqpos
  let Nstage : Nat := max (normBase P Y) (Y.modulus delta)
  refine ⟨Nstage, fun N hN => ?_⟩
  have hNbase : normBase P Y ≤ N :=
    Nat.le_trans (Nat.le_max_left _ _) hN
  have hNmod : Y.modulus delta ≤ N :=
    Nat.le_trans (Nat.le_max_right _ _) hN
  obtain ⟨NstA, hstA⟩ :=
    (pairSequence_converges P X (D.constant (Y.seq N))) q hqpos
  obtain ⟨NstB, hstB⟩ :=
    (pairSequence_converges P X Y) q hqpos
  let m : Nat := max (max NstA NstB)
    (max (max (normBase P X) (normBase P Y)) (Y.modulus delta))
  have hmA : NstA ≤ m :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hmB : NstB ≤ m :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hmX : normBase P X ≤ m :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      (Nat.le_max_right _ _)
  have hmY : normBase P Y ≤ m := by
    exact Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      (Nat.le_max_right _ _)
  have hmDelta : Y.modulus delta ≤ m := by
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  obtain ⟨NapxA, hclA⟩ := hstA m hmA
  obtain ⟨NapxB, hclB⟩ := hstB m hmB
  have hdistX :
      leEv (D.distSq (X.seq m) (X.seq m)) (ofQ' delta) := by
    exact leEv_trans (leEv_of_equiv (D.distSq_refl (X.seq m)))
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt hdelta))
  have hdistY :
      leEv (D.distSq (Y.seq m) (Y.seq N)) (ofQ' delta) :=
    Y.isCauchy delta hdelta m N hmDelta hNmod
  have hnormX :
      leEv (P.pairing (X.seq m) (X.seq m)) (ofQ' B) := by
    exact leEv_trans (diagonal_le_normCeiling P X m hmX)
      (leEv_of_le (ofQ'_le_ofQ'
        (Q'.le_max'_left (normCeiling P X) (normCeiling P Y))))
  have hnormY :
      leEv (P.pairing (Y.seq m) (Y.seq m)) (ofQ' B) := by
    exact leEv_trans (diagonal_le_normCeiling P Y m hmY)
      (leEv_of_le (ofQ'_le_ofQ'
        (Q'.le_max'_right (normCeiling P X) (normCeiling P Y))))
  have hpair := P.pairing_close
    (X.seq m) (X.seq m) (Y.seq m) (Y.seq N) B hB q hqpos
    hdistX hdistY hnormY hnormX
  obtain ⟨K, hK⟩ := evTwoSided_of_leRat hpair.1 hpair.2 hqpos
  refine ⟨max (max NapxA NapxB) K, fun k hk => ?_⟩
  have hkA : NapxA ≤ k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
  have hkB : NapxB ≤ k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
  obtain ⟨hA1, hA2⟩ := hclA k hkA
  obtain ⟨hB1, hB2⟩ := hclB k hkB
  have hkK : K ≤ k := by
    exact Nat.le_trans (Nat.le_max_right _ _) hk
  obtain ⟨hK1, hK2⟩ := hK k hkK
  have hK1' :
      (pairSequence P X (D.constant (Y.seq N)) m).approx k ≤
        (pairSequence P X Y m).approx k + (q + q) := by
    simpa [pairSequence] using hK2
  have hK2' :
      (pairSequence P X Y m).approx k ≤
        (pairSequence P X (D.constant (Y.seq N)) m).approx k + (q + q) := by
    simpa [pairSequence] using hK1
  have hfour : ∀ u v w z : Q',
      u ≤ v + q → v ≤ w + (q + q) →
      w ≤ z + q → u ≤ z + epsilon := by
    intro u v w z huv hvw hwz
    have h1 : u ≤ (w + (q + q)) + q :=
      Q'.le_trans' _ _ _ huv (Q'.add_le_add_right _ _ q hvw)
    have hw : w + (q + q) ≤ (z + q) + (q + q) :=
      Q'.add_le_add_right _ _ (q + q) hwz
    have h2 : u ≤ ((z + q) + (q + q)) + q :=
      Q'.le_trans' _ _ _ h1 (Q'.add_le_add_right _ _ q hw)
    refine Q'.le_trans' _ _ _ h2 ?_
    have hqq : (q + q).eqv (HalfPow.half * epsilon) :=
      ExpNeg.two_halves (HalfPow.half * epsilon)
    have htail : (q + ((q + q) + q)).eqv ((q + q) + (q + q)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left q _ _ (Q'.add_assoc_eqv q q q)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv q q (q + q))
    have hsum : (((z + q) + (q + q)) + q).eqv
        (z + epsilon) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (z + q) (q + q) q) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z q ((q + q) + q)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left z _ _ htail) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left z _ _ (Q'.add_eqv_congr' hqq hqq)) ?_
      exact Q'.add_eqv_congr_left z _ _ (ExpNeg.two_halves epsilon)
    exact Q'.le_of_eqv hsum
  exact ⟨hfour _ _ _ _ hA2 hK1' hB1,
    hfour _ _ _ _ hB2 hK2' hA1⟩

theorem representativeInner_eq_of_right_stage_pairings
    (X X' Y : D.Cauchy)
    (h : ∀ z : D.Carrier,
      Equiv (representativeInner P X (D.constant z))
        (representativeInner P X' (D.constant z))) :
    Equiv (representativeInner P X Y) (representativeInner P X' Y) := by
  apply Equiv_of_limit_of_equal (fun n => h (Y.seq n))
  · exact representativeInner_right_stage_converges P X Y
  · exact representativeInner_right_stage_converges P X' Y

/-- Quotient descent on the SAME supplied squared-seminorm completion. -/
def completedInner : D.Completion → D.Completion → RC :=
  Quotient.lift₂ (fun X Y => Quotient.mk crealSetoid (representativeInner P X Y))
    (fun _ _ _ _ hX hY => by
      rcases hX with ⟨hX⟩
      rcases hY with ⟨hY⟩
      exact Quotient.sound (representativeInner_welldef P hX hY))

theorem completedInner_mk (X Y : D.Cauchy) :
    completedInner P
      (Quotient.mk D.completionSetoid X) (Quotient.mk D.completionSetoid Y) =
      Quotient.mk crealSetoid (representativeInner P X Y) := rfl

/-! A completed diagonal inherits the explicit stream ceiling.  The generic
ceiling theorem only bounds stages at or beyond `normBase`; the proof therefore
uses the same representative stream with the index map `n ↦ max n normBase`.
This is a per-representative certificate, not a uniform bound over carriers,
widths, volumes, or couplings. -/

theorem completedInner_diagonal_le_normCeiling (X : D.Cauchy) :
    RCle
      (completedInner P
        (Quotient.mk D.completionSetoid X)
        (Quotient.mk D.completionSetoid X))
      (Quotient.mk crealSetoid (ofQ' (normCeiling P X))) := by
  let base := normBase P X
  have hshift :
      ConvergesTo
        (fun n => pairSequence P X X (max n base))
        (representativeInner P X X) := by
    intro epsilon hepsilon
    obtain ⟨Nstage, hstage⟩ := pairSequence_converges P X X epsilon hepsilon
    refine ⟨max Nstage base, fun n hn => ?_⟩
    have hN : Nstage ≤ n :=
      Nat.le_trans (Nat.le_max_left _ _) hn
    have hterm : Nstage ≤ max n base :=
      Nat.le_trans hN (Nat.le_max_left _ _)
    exact hstage (max n base) hterm
  have hbound :
      leEv (representativeInner P X X)
        (ofQ' (normCeiling P X)) := by
    apply CReal.leEv_of_convergesTo_le hshift (convergesTo_const _)
    intro n
    exact diagonal_le_normCeiling P X (max n base) (Nat.le_max_right _ _)
  rw [completedInner_mk]
  exact hbound

theorem representativeInner_constant (x y : D.Carrier) :
    Equiv (representativeInner P (D.constant x) (D.constant y))
      (P.pairing x y) :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl (P.pairing x y))
    (pairSequence_converges P (D.constant x) (D.constant y))
    (convergesTo_const (P.pairing x y))

/-- Dense constants retain the supplied actual pairing. -/
theorem completedInner_embedRep (x y : D.Carrier) :
    completedInner P
      (D.embedRep x) (D.embedRep y) =
      Quotient.mk crealSetoid (P.pairing x y) :=
  Quotient.sound (representativeInner_constant P x y)

theorem representativeInner_symm
    (hsymm : ∀ x y, Equiv (P.pairing x y) (P.pairing y x)) (X Y : D.Cauchy) :
    Equiv (representativeInner P X Y)
      (representativeInner P Y X) :=
  Equiv_of_limit_of_equal
    (fun n => hsymm (X.seq n) (Y.seq n))
    (pairSequence_converges P X Y)
    (pairSequence_converges P Y X)

theorem completedInner_symm
    (hsymm : ∀ x y, Equiv (P.pairing x y) (P.pairing y x)) (x y : D.Completion) :
    completedInner P x y = completedInner P y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_symm P hsymm X Y)

theorem representativeInner_nonnegative
    (hpos : ∀ x, leEv czero (P.pairing x x)) (X : D.Cauchy) :
    leEv czero (representativeInner P X X) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (pairSequence_converges P X X)
    (fun n => hpos (X.seq n))

theorem completedInner_nonnegative
    (hpos : ∀ x, leEv czero (P.pairing x x)) (x : D.Completion) :
    RCnonneg (completedInner P x x) := by
  refine Quotient.inductionOn x ?_
  exact representativeInner_nonnegative P hpos

/-- Uniqueness uses the actual dense scalar sequence, regardless of which
explicit inner or outer moduli another construction used. -/
theorem representativeInner_unique (X Y : D.Cauchy) (L : CReal)
    (hL : ConvergesTo (pairSequence P X Y) L) :
    Equiv (representativeInner P X Y) L :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl _)
    (pairSequence_converges P X Y) hL

theorem completedInner_unit_norm_one (u : D.Carrier)
    (hu : Equiv (P.pairing u u) cone) :
    completedInner P (D.embedRep u) (D.embedRep u) = Quotient.mk crealSetoid cone := by
  rw [completedInner_embedRep]
  exact Quotient.sound hu

end YMGap.Continuum.CRealSeminormPairingCompletion

#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.closeRate
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairSequence_close
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_welldef
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_right_stage_converges
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_eq_of_right_stage_pairings
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_mk
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_constant
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_embedRep
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_symm
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_symm
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_nonnegative
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_nonnegative
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_unique
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_unit_norm_one
