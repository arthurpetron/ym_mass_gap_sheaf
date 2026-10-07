/-
# Torus RP assembly (b4): the conj flip is a `RingSub` (support-free), and `RingSub` composes

* `parity_monoMul`: `selectedExponentParity N S (a·b) = parity a xor parity b`. This holds with no support
  hypothesis, since exponents add and parities xor.
* `conj_ringSub N S : RingSub n (signSelectedPolynomial N S)` for every `N`, `S`, `n`. The monomials are unchanged and
  the coefficients match up to sign bookkeeping.
* `ringSub_comp`: `RingSub n S → RingSub n R → RingSub n (S ∘ R)`, provided `S` respects `PE n` (`PECongr`).
  Unsupported `PECongr` holds for the conj flip (`conj_peCongr`), but it is FALSE for reindex (Prover's
  `SU2ReindexPECongr.pecongr_fails`: n=1, σ=id, x₄). Use only supported forms: `reindex_peCongrOn` /
  Prover's `pe_reindex`, together with `SU2TorusRPCompOn.ringSubOn_comp` and `haar_step`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (geometry (c) and assembly (d) remain).
-/

import YMGap.Continuum.SU2TorusRPHeadSub

namespace YMGap.Continuum.SU2TorusRPConj

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul varMono)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (selectedExponentParity signSelectedTerm signSelectedPolynomial signSelectedPolynomial_add
   signSelectedPolynomial_neg)
open YMGap.Continuum.SU2HaarAlgebra (PE phi sm sm_congr sm_flatMap sm_map pe_refl pe_trans)
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)

/-! ## Parity is additive -/

def step (S : Nat → Bool) (m : List Nat) (p : Bool) (c : Nat) : Bool :=
  if S c then xor p (decide (exponentAt m c % 2 = 1)) else p

theorem foldl_xor (S : Nat → Bool) (m : List Nat) : ∀ (l : List Nat) (p : Bool),
    l.foldl (step S m) p = xor p (l.foldl (step S m) false)
  | [], p => by simp
  | c :: l, p => by
    simp only [List.foldl_cons]
    rw [foldl_xor S m l (step S m p c), foldl_xor S m l (step S m false c)]
    unfold step; split <;> simp

theorem foldl_add (S : Nat → Bool) (a b : List Nat) : ∀ l : List Nat,
    l.foldl (step S (monoMul a b)) false = xor (l.foldl (step S a) false) (l.foldl (step S b) false)
  | [] => rfl
  | c :: l => by
    simp only [List.foldl_cons]
    rw [foldl_xor S _ l, foldl_xor S a l, foldl_xor S b l, foldl_add S a b l]
    unfold step
    rw [YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul]
    split
    · have h : ∀ x y : Nat, decide ((x + y) % 2 = 1) = xor (decide (x % 2 = 1)) (decide (y % 2 = 1)) := by
        intro x y
        rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
          rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp [Nat.add_mod, hx, hy]
      rw [h]
      cases decide (exponentAt a c % 2 = 1) <;> cases decide (exponentAt b c % 2 = 1) <;>
        simp [Bool.xor_comm]
    · simp [Bool.xor_comm]

theorem parity_eq (N : Nat) (S : Nat → Bool) (m : List Nat) :
    selectedExponentParity N S m = (List.range N).foldl (step S m) false := rfl

theorem parity_monoMul (N : Nat) (S : Nat → Bool) (a b : List Nat) :
    selectedExponentParity N S (monoMul a b) =
      xor (selectedExponentParity N S a) (selectedExponentParity N S b) := by
  rw [parity_eq, parity_eq, parity_eq]; exact foldl_add S a b _

theorem parity_nil (N : Nat) (S : Nat → Bool) : selectedExponentParity N S [] = false := by
  rw [parity_eq]
  suffices h : ∀ (l : List Nat), l.foldl (step S []) false = false from h _
  intro l; induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.foldl_cons]
    have : step S [] false c = false := by unfold step; split <;> simp [exponentAt]
    rw [this, ih]

/-! ## Coefficient bookkeeping -/

def sg (b : Bool) (x : Q') : Q' := if b then -x else x

theorem neg_mul_neg' (a b : Q') : ((-a) * (-b)).eqv (a * b) :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv _ _) (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv _ _))
    (Q'.neg_neg_eqv _))

theorem sg_mul (p q : Bool) (a b : Q') : (sg (xor p q) (a * b)).eqv (sg p a * sg q b) := by
  cases p <;> cases q <;> simp only [sg, Bool.xor] <;> simp
  · exact Q'.eqv_refl _
  · exact Q'.eqv_symm (Q'.mul_neg_eqv _ _)
  · exact Q'.eqv_symm (Q'.neg_mul_eqv _ _)
  · exact Q'.eqv_symm (neg_mul_neg' _ _)

theorem sg_smul (p : Bool) (c a : Q') : (sg p (c * a)).eqv (c * sg p a) := by
  cases p
  · exact Q'.eqv_refl _
  · exact Q'.eqv_symm (Q'.mul_neg_eqv _ _)

/-- Two polynomials with the same monomial list and pointwise-equivalent coefficients are `PE`. -/
theorem pe_coeffwise (n : Nat) {β : Type} (l : List β) (e : β → List Nat) (f g : β → Q')
    (h : ∀ x ∈ l, (f x).eqv (g x)) : PE n (l.map fun x => (e x, f x)) (l.map fun x => (e x, g x)) := fun m => by
  unfold phi; rw [sm_map, sm_map]
  exact sm_congr l fun x hx => Q'.mul_eqv_congr_right _ _ _ (h x hx)

/-! ## The instance -/

theorem conj_ringSub (n N : Nat) (S : Nat → Bool) : RingSub n (signSelectedPolynomial N S) where
  mul p q := by
    have e1 : signSelectedPolynomial N S (polyMul p q) =
        (p.flatMap fun s => q.map fun t => (s, t)).map fun x =>
          (monoMul x.1.1 x.2.1, sg (selectedExponentParity N S (monoMul x.1.1 x.2.1)) (x.1.2 * x.2.2)) := by
      simp [signSelectedPolynomial, signSelectedTerm, polyMul, List.map_flatMap, List.flatMap_map, sg, Function.comp_def]
    have e2 : polyMul (signSelectedPolynomial N S p) (signSelectedPolynomial N S q) =
        (p.flatMap fun s => q.map fun t => (s, t)).map fun x =>
          (monoMul x.1.1 x.2.1, sg (selectedExponentParity N S x.1.1) x.1.2 *
            sg (selectedExponentParity N S x.2.1) x.2.2) := by
      simp [signSelectedPolynomial, signSelectedTerm, polyMul, List.map_flatMap, List.flatMap_map, sg, Function.comp_def]
    rw [e1, e2]
    exact pe_coeffwise n _ _ _ _ fun x _ => by rw [parity_monoMul]; exact sg_mul _ _ _ _
  add p q := by rw [signSelectedPolynomial_add]; exact pe_refl n _
  smul c p := by
    have e1 : signSelectedPolynomial N S (polySmul c p) =
        p.map fun t => (t.1, sg (selectedExponentParity N S t.1) (c * t.2)) := by
      simp [signSelectedPolynomial, signSelectedTerm, polySmul, sg, Function.comp_def]
    have e2 : polySmul c (signSelectedPolynomial N S p) =
        p.map fun t => (t.1, c * sg (selectedExponentParity N S t.1) t.2) := by
      simp [signSelectedPolynomial, signSelectedTerm, polySmul, sg, Function.comp_def]
    rw [e1, e2]; exact pe_coeffwise n _ _ _ _ fun t _ => sg_smul _ _ _
  neg p := by rw [signSelectedPolynomial_neg]; exact pe_refl n _
  one := by
    show PE n [signSelectedTerm N S ([], 1)] polyOne
    simp only [signSelectedTerm, parity_nil]; exact pe_refl n _

/-! ## Composition -/

/-- `S` respects `PE n`. -/
def PECongr (n : Nat) (S : RatPoly → RatPoly) : Prop := ∀ {X Y}, PE n X Y → PE n (S X) (S Y)

theorem ringSub_comp {n : Nat} {S R : RatPoly → RatPoly} (hS : RingSub n S) (hSc : PECongr n S)
    (hR : RingSub n R) : RingSub n (fun p => S (R p)) where
  mul p q := pe_trans n (hSc (hR.mul p q)) (hS.mul _ _)
  add p q := pe_trans n (hSc (hR.add p q)) (hS.add _ _)
  smul c p := pe_trans n (hSc (hR.smul c p)) (hS.smul _ _)
  neg p := pe_trans n (hSc (hR.neg p)) (hS.neg _)
  one := pe_trans n (hSc hR.one) hS.one

end YMGap.Continuum.SU2TorusRPConj

#print axioms YMGap.Continuum.SU2TorusRPConj.parity_monoMul
#print axioms YMGap.Continuum.SU2TorusRPConj.conj_ringSub
#print axioms YMGap.Continuum.SU2TorusRPConj.ringSub_comp
