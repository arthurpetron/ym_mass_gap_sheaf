/-
# Haar positivity on ordinary bare class polynomials

This successor identifies the canonical extractor's vacuum coefficient with
the packet vacuum after character synthesis.  Combined with exact fusion
synthesis, this descends packet square positivity all the way to ordinary
`QPoly.pmul`.

# Axiom gate

All declarations are MLTT/HoTT-clean up to `propext` / `Quot.sound`.  There is
no classical choice, trusted native computation, proof hole, or custom axiom.
-/

import YMGap.Continuum.SU2CharacterFusionSynthesis

namespace YMGap.Continuum.SU2ClassPolynomialHaarDescent

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebExtraction
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialPacketDescent
open YMGap.Continuum.SU2CharacterFusionSynthesis

private theorem coeffEqv_cons {a b : Q'} {as bs : List Q'}
    (hab : a.eqv b) (ht : CoeffEqv as bs) : CoeffEqv (a :: as) (b :: bs) := by
  apply (coeffEqv_iff_polyEqv _ _).2
  intro x
  exact q_add_congr hab
    (Q'.mul_eqv_congr_left x _ _ ((coeffEqv_iff_polyEqv _ _).1 ht x))

private theorem coeffEqv_padd_assoc (a b c : List Q') :
    CoeffEqv (padd (padd a b) c) (padd a (padd b c)) :=
  (coeffEqv_iff_polyEqv _ _).2 (padd_assoc a b c)

private theorem coeffEqv_padd_comm (a b : List Q') :
    CoeffEqv (padd a b) (padd b a) :=
  (coeffEqv_iff_polyEqv _ _).2 (padd_comm a b)

private theorem coeffEqv_interchange (a b c d : List Q') :
    CoeffEqv (padd (padd a b) (padd c d))
      (padd (padd a c) (padd b d)) := by
  apply (coeffEqv_iff_polyEqv _ _).2
  intro x
  refine Q'.eqv_trans _
    (eval (padd a b) x + eval (padd c d) x) _
    (eval_padd (padd a b) (padd c d) x) ?_
  refine Q'.eqv_trans _
    ((eval a x + eval b x) + (eval c x + eval d x)) _ ?_ ?_
  · exact q_add_congr (eval_padd a b x) (eval_padd c d x)
  · refine Q'.eqv_trans _
      ((eval a x + eval c x) + (eval b x + eval d x)) _
      (q_interchange _ _ _ _) ?_
    refine Q'.eqv_trans _
      (eval (padd a c) x + eval (padd b d) x) _ ?_ ?_
    · exact Q'.eqv_symm
        (q_add_congr (eval_padd a c x) (eval_padd b d x))
    · exact Q'.eqv_symm (eval_padd (padd a c) (padd b d) x)

private theorem coeffEqv_scale_padd (c : Q') (a b : List Q') :
    CoeffEqv (pscale c (padd a b)) (padd (pscale c a) (pscale c b)) := by
  apply (coeffEqv_iff_polyEqv _ _).2
  intro x
  refine Q'.eqv_trans _ (c * eval (padd a b) x) _
    (eval_pscale c (padd a b) x) ?_
  refine Q'.eqv_trans _ (c * (eval a x + eval b x)) _
    (Q'.mul_eqv_congr_left c _ _ (eval_padd a b x)) ?_
  refine Q'.eqv_trans _ (c * eval a x + c * eval b x) _
    (Q'.mul_add_eqv c (eval a x) (eval b x)) ?_
  refine Q'.eqv_trans _
    (eval (pscale c a) x + eval (pscale c b) x) _ ?_ ?_
  · exact q_add_congr (Q'.eqv_symm (eval_pscale c a x))
      (Q'.eqv_symm (eval_pscale c b x))
  · exact Q'.eqv_symm (eval_padd (pscale c a) (pscale c b) x)

private theorem coeffEqv_scale_swap (c d : Q') (a : List Q') :
    CoeffEqv (pscale c (pscale d a)) (pscale d (pscale c a)) := by
  apply (coeffEqv_iff_polyEqv _ _).2
  intro x
  refine Q'.eqv_trans _ (c * (d * eval a x)) _
    (Q'.eqv_trans _ _ _ (eval_pscale c (pscale d a) x)
      (Q'.mul_eqv_congr_left c _ _ (eval_pscale d a x))) ?_
  refine Q'.eqv_trans _ (d * (c * eval a x)) _ ?_ ?_
  · refine Q'.eqv_trans _ ((c * d) * eval a x) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c d (eval a x))) ?_
    refine Q'.eqv_trans _ ((d * c) * eval a x) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv c d)) ?_
    exact Q'.mul_assoc_eqv d c (eval a x)
  · exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _ (eval_pscale d (pscale c a) x)
        (Q'.mul_eqv_congr_left d _ _ (eval_pscale c a x)))

private theorem tail_padd (a b : List Q') :
    (padd a b).tail = padd a.tail b.tail := by
  cases a with
  | nil => cases b <;> rfl
  | cons c cs =>
      cases b with
      | nil => cases cs <;> rfl
      | cons d ds => rfl

private theorem tail_pscale (c : Q') (a : List Q') :
    (pscale c a).tail = pscale c a.tail := by
  cases a <;> rfl

private theorem zeroCons_padd (a b : List Q') :
    CoeffEqv (0 :: padd a b) (padd (0 :: a) (0 :: b)) := by
  exact coeffEqv_cons (Q'.eqv_symm (q_zero_add_eqv 0)) (coeffEqv_refl _)

private theorem xLift_padd (a b : List Q') :
    CoeffEqv (xLift (padd a b)) (padd (xLift a) (xLift b)) := by
  unfold xLift
  rw [tail_padd]
  refine coeffEqv_trans
    (coeffEqv_padd
      (coeffEqv_zeroCons (coeffEqv_scale_padd HalfPow.half a b))
      (coeffEqv_scale_padd HalfPow.half a.tail b.tail)) ?_
  refine coeffEqv_trans
    (coeffEqv_padd (zeroCons_padd (pscale HalfPow.half a)
      (pscale HalfPow.half b)) (coeffEqv_refl _)) ?_
  exact coeffEqv_interchange
    (0 :: pscale HalfPow.half a) (0 :: pscale HalfPow.half b)
    (pscale HalfPow.half a.tail) (pscale HalfPow.half b.tail)

private theorem xLift_pscale (c : Q') (a : List Q') :
    CoeffEqv (xLift (pscale c a)) (pscale c (xLift a)) := by
  unfold xLift
  rw [tail_pscale]
  refine coeffEqv_trans
    (coeffEqv_padd
      (coeffEqv_zeroCons (coeffEqv_scale_swap HalfPow.half c a))
      (coeffEqv_scale_swap HalfPow.half c a.tail)) ?_
  refine coeffEqv_trans
    (coeffEqv_padd
      (coeffEqv_cons (Q'.eqv_symm (q_mul_zero c)) (coeffEqv_refl _))
      (coeffEqv_refl _)) ?_
  exact coeffEqv_symm
    (coeffEqv_scale_padd c (0 :: pscale HalfPow.half a)
      (pscale HalfPow.half a.tail))

private theorem chebStep_padd (c d : Q') (a b : List Q') :
    CoeffEqv (chebStep (c + d) (padd a b))
      (padd (chebStep c a) (chebStep d b)) := by
  unfold chebStep
  refine coeffEqv_trans
    (coeffEqv_padd (coeffEqv_refl [c + d]) (xLift_padd a b)) ?_
  refine coeffEqv_trans
    (coeffEqv_padd (coeffEqv_symm (coeffEqv_refl (padd [c] [d])))
      (coeffEqv_refl _)) ?_
  exact coeffEqv_interchange [c] [d] (xLift a) (xLift b)

private theorem chebStep_pscale (c d : Q') (a : List Q') :
    CoeffEqv (chebStep (c * d) (pscale c a))
      (pscale c (chebStep d a)) := by
  unfold chebStep
  refine coeffEqv_trans
    (coeffEqv_padd (coeffEqv_refl [c * d]) (xLift_pscale c a)) ?_
  exact coeffEqv_symm (coeffEqv_scale_padd c [d] (xLift a))

private theorem chebExtract_padd : forall p q : Poly,
    CoeffEqv (chebExtract (padd p q))
      (padd (chebExtract p) (chebExtract q))
  | [], q => coeffEqv_refl _
  | c :: cs, [] => by
      exact coeffEqv_symm (coeffEqv_padd_comm (chebExtract (c :: cs)) [])
  | c :: cs, d :: ds => by
      exact coeffEqv_trans
        (coeffEqv_chebStep (coeffEqv_refl [c + d])
          (chebExtract_padd cs ds))
        (chebStep_padd c d (chebExtract cs) (chebExtract ds))

private theorem chebExtract_pscale (c : Q') : forall p : Poly,
    CoeffEqv (chebExtract (pscale c p)) (pscale c (chebExtract p))
  | [] => coeffEqv_refl []
  | d :: ds => by
      exact coeffEqv_trans
        (coeffEqv_chebStep (coeffEqv_refl [c * d])
          (chebExtract_pscale c ds))
        (chebStep_pscale c d (chebExtract ds))

private theorem chebExtract_psub (p q : Poly) :
    CoeffEqv (chebExtract (psub p q))
      (psub (chebExtract p) (chebExtract q)) := by
  unfold psub pneg
  exact coeffEqv_trans (chebExtract_padd p (pscale (-1) q))
    (coeffEqv_padd (coeffEqv_refl _)
      (chebExtract_pscale (-1) q))

/-! ## The extractor on individual character modes -/

def basisCoeffs : Nat -> List Q'
  | 0 => [1]
  | n + 1 => 0 :: basisCoeffs n

private theorem two_half : ((2 : Q') * HalfPow.half).eqv 1 := by decide

private theorem scale_two_half (a : List Q') :
    CoeffEqv (pscale 2 (pscale HalfPow.half a)) a := by
  apply (coeffEqv_iff_polyEqv _ _).2
  intro x
  refine Q'.eqv_trans _ ((2 : Q') * (HalfPow.half * eval a x)) _
    (Q'.eqv_trans _ _ _ (eval_pscale 2 (pscale HalfPow.half a) x)
      (Q'.mul_eqv_congr_left 2 _ _ (eval_pscale HalfPow.half a x))) ?_
  refine Q'.eqv_trans _ (((2 : Q') * HalfPow.half) * eval a x) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv 2 HalfPow.half (eval a x))) ?_
  exact Q'.eqv_trans _ (1 * eval a x) _
    (Q'.mul_eqv_congr_right _ _ _ two_half) (Q'.one_mul_eqv _)

private theorem scale_zeroCons (c : Q') (a : List Q') :
    CoeffEqv (pscale c (0 :: a)) (0 :: pscale c a) :=
  coeffEqv_cons (q_mul_zero c) (coeffEqv_refl _)

private theorem xLift_basis_succ (n : Nat) :
    CoeffEqv (pscale 2 (xLift (basisCoeffs (n + 1))))
      (padd (basisCoeffs n) (basisCoeffs (n + 2))) := by
  unfold xLift
  refine coeffEqv_trans
    (coeffEqv_scale_padd 2
      (0 :: pscale HalfPow.half (0 :: basisCoeffs n))
      (pscale HalfPow.half (basisCoeffs n))) ?_
  refine coeffEqv_trans
    (coeffEqv_padd
      (coeffEqv_trans (scale_zeroCons 2 _)
        (coeffEqv_zeroCons
          (coeffEqv_trans (scale_zeroCons HalfPow.half _ |> coeffEqv_pscale 2)
            (coeffEqv_zeroCons (scale_two_half (basisCoeffs n))))))
      (scale_two_half (basisCoeffs n))) ?_
  exact coeffEqv_padd_comm (basisCoeffs (n + 2)) (basisCoeffs n)

private theorem psub_padd_left (a b : List Q') :
    CoeffEqv (psub (padd a b) a) b := by
  apply (coeffEqv_iff_polyEqv _ _).2
  intro x
  refine Q'.eqv_trans _ ((eval a x + eval b x) + -(eval a x)) _
    (Q'.eqv_trans _ _ _ (eval_psub (padd a b) a x)
      (q_add_congr (eval_padd a b x) (Q'.eqv_refl _))) ?_
  refine Q'.eqv_trans _ (eval a x + (eval b x + -(eval a x))) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (eval a x + (-(eval a x) + eval b x)) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _ ((eval a x + -(eval a x)) + eval b x) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  have hcancel : (eval a x + -(eval a x)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
      (Q'.neg_add_self_eqv _)
  exact Q'.eqv_trans _ (0 + eval b x) _
    (q_add_congr hcancel (Q'.eqv_refl _)) (q_zero_add_eqv _)

private theorem pmul_chi1_eq_doubleX (p : Poly) :
    PolyEqv (pmul chi1 p) (0 :: pscale 2 p) := by
  intro x
  refine Q'.eqv_trans _ (eval chi1 x * eval p x) _
    (eval_pmul chi1 p x) ?_
  refine Q'.eqv_trans _ (((2 : Q') * x) * eval p x) _
    (Q'.mul_eqv_congr_right _ _ _ (eval_chi1 x)) ?_
  refine Q'.eqv_trans _ (x * ((2 : Q') * eval p x)) _ ?_ ?_
  · refine Q'.eqv_trans _ (((2 : Q') * x) * eval p x) _
      (Q'.eqv_refl _) ?_
    refine Q'.eqv_trans _ ((x * (2 : Q')) * eval p x) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv 2 x)) ?_
    exact Q'.mul_assoc_eqv x 2 (eval p x)
  · exact Q'.eqv_symm
      (Q'.eqv_trans _ (x * eval (pscale 2 p) x) _
        (q_zero_add_eqv _)
        (Q'.mul_eqv_congr_left x _ _ (eval_pscale 2 p x)))

private theorem chebStep_zero (a : List Q') :
    CoeffEqv (chebStep 0 a) (xLift a) := by
  apply (coeffEqv_iff_polyEqv _ _).2
  intro x
  refine Q'.eqv_trans _ (eval [0] x + eval (xLift a) x) _
    (eval_padd [0] (xLift a) x) ?_
  refine Q'.eqv_trans _ (0 + eval (xLift a) x) _
    (q_add_congr (Q'.eqv_trans _ _ _
      (q_add_congr (Q'.eqv_refl 0) (q_mul_zero x))
      (q_add_zero_eqv 0)) (Q'.eqv_refl _)) ?_
  exact q_zero_add_eqv _

private theorem chebExtract_pmul_chi1 (p : Poly) :
    CoeffEqv (chebExtract (pmul chi1 p))
      (pscale 2 (xLift (chebExtract p))) := by
  refine coeffEqv_trans
    (chebExtract_unique (pmul_chi1_eq_doubleX p)) ?_
  show CoeffEqv (chebExtract (0 :: pscale 2 p)) _
  refine coeffEqv_trans
    (coeffEqv_chebStep (coeffEqv_refl [0])
      (chebExtract_pscale 2 p)) ?_
  refine coeffEqv_trans (chebStep_zero (pscale 2 (chebExtract p))) ?_
  exact xLift_pscale 2 (chebExtract p)

theorem chebExtract_chebPoly : forall n : Nat,
    CoeffEqv (chebExtract (chebPoly n)) (basisCoeffs n)
  | 0 => by unfold chebPoly chi0 basisCoeffs CoeffEqv; decide
  | 1 => by unfold chebPoly chi1 basisCoeffs CoeffEqv; decide
  | n + 2 => by
      rw [chebPoly]
      refine coeffEqv_trans (chebExtract_psub _ _) ?_
      refine coeffEqv_trans
        (coeffEqv_padd
          (chebExtract_pmul_chi1 (chebPoly (n + 1)))
          (coeffEqv_pscale (-1) (chebExtract_chebPoly n))) ?_
      refine coeffEqv_trans
        (coeffEqv_padd
          (coeffEqv_pscale 2 (coeffEqv_xLift (chebExtract_chebPoly (n + 1))))
          (coeffEqv_refl _)) ?_
      refine coeffEqv_trans
        (coeffEqv_padd (xLift_basis_succ n) (coeffEqv_refl _)) ?_
      exact psub_padd_left (basisCoeffs n) (basisCoeffs (n + 2))

/-! ## The extracted vacuum on character synthesis -/

private theorem headCoeff_padd (a b : List Q') :
    (headCoeff (padd a b)).eqv (headCoeff a + headCoeff b) := by
  cases a with
  | nil => exact Q'.eqv_symm (q_zero_add_eqv _)
  | cons c cs =>
      cases b with
      | nil => exact Q'.eqv_symm (q_add_zero_eqv _)
      | cons d ds => exact Q'.eqv_refl _

private theorem headCoeff_pscale (c : Q') (a : List Q') :
    (headCoeff (pscale c a)).eqv (c * headCoeff a) := by
  cases a with
  | nil => exact Q'.eqv_symm (q_mul_zero c)
  | cons d ds => exact Q'.eqv_refl _

theorem bareVacuumHaar_padd (p q : Poly) :
    (bareVacuumHaar (padd p q)).eqv
      (bareVacuumHaar p + bareVacuumHaar q) := by
  exact Q'.eqv_trans _ _ _
    (headCoeff_congr (chebExtract_padd p q))
    (headCoeff_padd (chebExtract p) (chebExtract q))

theorem bareVacuumHaar_pscale (c : Q') (p : Poly) :
    (bareVacuumHaar (pscale c p)).eqv (c * bareVacuumHaar p) := by
  exact Q'.eqv_trans _ _ _
    (headCoeff_congr (chebExtract_pscale c p))
    (headCoeff_pscale c (chebExtract p))

private theorem headCoeff_basis_zero : (headCoeff (basisCoeffs 0)).eqv 1 :=
  Q'.eqv_refl 1

private theorem headCoeff_basis_succ (n : Nat) :
    (headCoeff (basisCoeffs (n + 1))).eqv 0 :=
  Q'.eqv_refl 0

theorem bareVacuumHaar_chebPoly_zero :
    (bareVacuumHaar (chebPoly 0)).eqv 1 :=
  Q'.eqv_trans _ _ _ (headCoeff_congr (chebExtract_chebPoly 0))
    headCoeff_basis_zero

theorem bareVacuumHaar_chebPoly_succ (n : Nat) :
    (bareVacuumHaar (chebPoly (n + 1))).eqv 0 :=
  Q'.eqv_trans _ _ _ (headCoeff_congr (chebExtract_chebPoly (n + 1)))
    (headCoeff_basis_succ n)

private theorem bareVacuumHaar_chebSynthesisFrom_pos : forall
    (k : Nat) (a : List Q'), 0 < k ->
    (bareVacuumHaar (chebSynthesisFrom k a)).eqv 0
  | _, [], _ => Q'.eqv_refl 0
  | k, c :: cs, hk => by
      refine Q'.eqv_trans _
        (bareVacuumHaar (pscale c (chebPoly k)) +
          bareVacuumHaar (chebSynthesisFrom (k + 1) cs)) _
        (bareVacuumHaar_padd _ _) ?_
      refine Q'.eqv_trans _
        (c * bareVacuumHaar (chebPoly k) +
          bareVacuumHaar (chebSynthesisFrom (k + 1) cs)) _
        (q_add_congr (bareVacuumHaar_pscale c (chebPoly k))
          (Q'.eqv_refl _)) ?_
      have hkform : k = (k - 1) + 1 := by omega
      have hmode : (bareVacuumHaar (chebPoly k)).eqv 0 := by
        rw [hkform]
        exact bareVacuumHaar_chebPoly_succ (k - 1)
      exact Q'.eqv_trans _ (c * 0 + 0) _
        (q_add_congr (Q'.mul_eqv_congr_left c _ _ hmode)
          (bareVacuumHaar_chebSynthesisFrom_pos (k + 1) cs (by omega)))
        (Q'.eqv_trans _ _ _ (q_add_congr (q_mul_zero c) (Q'.eqv_refl 0))
          (q_add_zero_eqv 0))

theorem bareVacuumHaar_chebSynthesis (a : List Q') :
    (bareVacuumHaar (chebSynthesis a)).eqv (headCoeff a) := by
  cases a with
  | nil => exact Q'.eqv_refl 0
  | cons c cs =>
      refine Q'.eqv_trans _
        (bareVacuumHaar (pscale c (chebPoly 0)) +
          bareVacuumHaar (chebSynthesisFrom 1 cs)) _
        (bareVacuumHaar_padd _ _) ?_
      refine Q'.eqv_trans _
        (c * bareVacuumHaar (chebPoly 0) +
          bareVacuumHaar (chebSynthesisFrom 1 cs)) _
        (q_add_congr (bareVacuumHaar_pscale c (chebPoly 0))
          (Q'.eqv_refl _)) ?_
      refine Q'.eqv_trans _ (c * 1 + 0) _
        (q_add_congr (Q'.mul_eqv_congr_left c _ _
          bareVacuumHaar_chebPoly_zero)
          (bareVacuumHaar_chebSynthesisFrom_pos 1 cs (by omega))) ?_
      exact Q'.eqv_trans _ (c + 0) _
        (q_add_congr (Q'.mul_one_eqv c) (Q'.eqv_refl 0))
        (q_add_zero_eqv c)

/-! ## Packet coefficient lists and final descent -/

def coeffListOfFn : (n : Nat) -> (Fin n -> Q') -> List Q'
  | 0, _ => []
  | n + 1, f => f ⟨0, Nat.succ_pos n⟩ ::
      coeffListOfFn n (fun i => f i.succ)

theorem coeffListOfFn_length : forall (n : Nat) (f : Fin n -> Q'),
    (coeffListOfFn n f).length = n
  | 0, _ => rfl
  | n + 1, f => by
      simp only [coeffListOfFn, List.length]
      rw [coeffListOfFn_length n (fun i => f i.succ)]

theorem listCoeff_coeffListOfFn : forall (n : Nat) (f : Fin n -> Q')
    (s : Nat) (hs : s < n),
    listCoeff (coeffListOfFn n f) s = f ⟨s, hs⟩
  | 0, _, s, hs => by omega
  | n + 1, f, 0, hs => rfl
  | n + 1, f, s + 1, hs => by
      have hrec := listCoeff_coeffListOfFn n (fun i => f i.succ) s (by omega)
      exact hrec

def packetCoeffList {N : Nat} (P : CharacterPacket N) : List Q' :=
  coeffListOfFn (N + 1) P.coeff

theorem packetCoeffList_length {N : Nat} (P : CharacterPacket N) :
    (packetCoeffList P).length = N + 1 :=
  coeffListOfFn_length (N + 1) P.coeff

theorem coeffAt_listPacket_packetCoeffList {N : Nat} (P : CharacterPacket N)
    (s : Nat) :
    coeffAt (listPacketAt N (packetCoeffList P)) s = coeffAt P s := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt _ hs, coeffAt_of_lt _ hs]
    exact listCoeff_coeffListOfFn (N + 1) P.coeff s hs
  · rw [coeffAt, dif_neg hs, coeffAt, dif_neg hs]

theorem synthesis_eq_chebSynthesis_packetCoeffList {N : Nat}
    (P : CharacterPacket N) :
    PolyEqv (synthesis P) (chebSynthesis (packetCoeffList P)) := by
  refine peqv_trans ?_ (synthesis_listPacketAt (N := N) (packetCoeffList P) (by
    rw [packetCoeffList_length]
    exact Nat.le_refl _))
  intro x
  refine Q'.eqv_trans _
    (finSum (fun s => coeffAt P s * Cheb.U s x) (N + 1)) _
    (eval_synthesis P x) ?_
  refine Q'.eqv_trans _
    (finSum (fun s => coeffAt (listPacketAt N (packetCoeffList P)) s *
      Cheb.U s x) (N + 1)) _ ?_ ?_
  · exact finSum_congr_eqv (fun s =>
      Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_of_eq (Eq.symm (coeffAt_listPacket_packetCoeffList P s))))
      (N + 1)
  · exact Q'.eqv_symm
      (eval_synthesis (listPacketAt N (packetCoeffList P)) x)

theorem bareVacuumHaar_synthesis_packet {N : Nat} (P : CharacterPacket N) :
    (bareVacuumHaar (synthesis P)).eqv (vacuumHaar P) := by
  refine Q'.eqv_trans _
    (bareVacuumHaar (chebSynthesis (packetCoeffList P))) _
    (bareVacuumHaar_congr (synthesis_eq_chebSynthesis_packetCoeffList P)) ?_
  refine Q'.eqv_trans _ (headCoeff (packetCoeffList P)) _
    (bareVacuumHaar_chebSynthesis (packetCoeffList P)) ?_
  exact Q'.eqv_of_eq
    (listCoeff_coeffListOfFn (N + 1) P.coeff 0 (Nat.succ_pos N))

/-- The packet functional and the extractor functional agree on the exact
fusion product of arbitrary bare polynomials. -/
theorem bareVacuumHaar_polynomialFusionProduct (p q : Poly) :
    (bareVacuumHaar (polynomialFusionProduct p q)).eqv
      (bareFusionHaar p q) :=
  bareVacuumHaar_synthesis_packet (polynomialFusionPacket p q)

/-- **Exact Haar square positivity on every ordinary bare rational class
polynomial.** -/
theorem bareVacuumHaar_pmul_self_nonneg (p : Poly) :
    (0 : Q') <= bareVacuumHaar (pmul p p) := by
  have heq : (bareVacuumHaar (pmul p p)).eqv (bareFusionHaar p p) :=
    Q'.eqv_trans _ _ _
      (bareVacuumHaar_congr
        (peqv_symm (polynomialFusionProduct_eq_pmul p p)))
      (bareVacuumHaar_polynomialFusionProduct p p)
  exact Q'.le_trans' _ _ _ (bareFusionHaar_square_nonneg p)
    (Q'.le_of_eqv (Q'.eqv_symm heq))

end YMGap.Continuum.SU2ClassPolynomialHaarDescent

#print axioms YMGap.Continuum.SU2ClassPolynomialHaarDescent.chebExtract_chebPoly
#print axioms YMGap.Continuum.SU2ClassPolynomialHaarDescent.bareVacuumHaar_chebSynthesis
#print axioms YMGap.Continuum.SU2ClassPolynomialHaarDescent.bareVacuumHaar_synthesis_packet
#print axioms YMGap.Continuum.SU2ClassPolynomialHaarDescent.bareVacuumHaar_pmul_self_nonneg
