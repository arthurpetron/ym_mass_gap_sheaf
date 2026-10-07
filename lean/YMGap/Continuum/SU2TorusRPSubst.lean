/-
# Torus RP assembly (b1): transporting a ring substitution through the Wilson integrand

`RingSub n S` says the polynomial map `S` is a ring homomorphism up to Haar-context equivalence `PE n` (`mul`, `add`,
`smul`, `neg`, `one`). `PE` is used, not `≅`, because block substitutions pad monomials with zeros.
For such an `S`:
* `chiPow_sub`, `wilsonPoly_sub`: `S (T_K(x)) ≡ T_K(S x)`;
* `qmul_sub`, `qconj_sub`: `S` acts componentwise on Hamilton products and conjugates;
* `word_sub`: `S (Re((l₁ l₂)(l₃* l₄*))) ≡ Re((Sl₁ Sl₂)(Sl₃* Sl₄*))`, the shape of `plaqWord`;
* `prodPoly_sub`: products over plaquettes.
Also included: `PE` congruences for `polySmul`, `polyNeg` and `wilsonPoly`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (instances (b2), geometry (c) and assembly (d) remain).
-/

import YMGap.Continuum.SU2TorusRPPad

namespace YMGap.Continuum.SU2TorusRPSubst

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarAlgebra (PE phi sm pe_refl pe_symm pe_trans pe_append pe_mulL pe_mulR)
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly chiPow)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open PolyQuaternion (mul conj)

section
variable (n : Nat)

theorem phi_neg (m : List Nat) : ∀ X : RatPoly, (phi n (polyNeg X) m).eqv (-(phi n X m))
  | [] => by show (0 : Q').eqv (-0); decide
  | t :: X => by
    show ((-t.2) * quaternionHaarMono n (monoMul m t.1) + phi n (polyNeg X) m).eqv
      (-(t.2 * quaternionHaarMono n (monoMul m t.1) + phi n X m))
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.neg_mul_eqv _ _) (phi_neg m X))
      (Q'.eqv_symm (Q'.neg_add_eqv _ _))

theorem pe_neg {X Y : RatPoly} (h : PE n X Y) : PE n (polyNeg X) (polyNeg Y) := fun m =>
  Q'.eqv_trans _ _ _ (phi_neg n m X) (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (h m)) (Q'.eqv_symm (phi_neg n m Y)))

theorem pe_mul2 {X X' Y Y' : RatPoly} (h : PE n X X') (h' : PE n Y Y') : PE n (polyMul X Y) (polyMul X' Y') :=
  pe_trans n (pe_mulR n Y h) (pe_mulL n X' h')

theorem pe_smul (c : Q') {X Y : RatPoly} (h : PE n X Y) : PE n (polySmul c X) (polySmul c Y) := by
  rw [YMGap.Continuum.SU2TorusRPWilson.smul_eq, YMGap.Continuum.SU2TorusRPWilson.smul_eq]; exact pe_mulL n _ h

theorem chiPow_pe {x y : RatPoly} (h : PE n x y) : ∀ k, PE n (chiPow x k) (chiPow y k)
  | 0 => pe_refl n _
  | k + 1 => pe_mul2 n (pe_smul n 2 h) (chiPow_pe h k)

theorem wilsonPoly_pe {x y : RatPoly} (h : PE n x y) (c : Nat → Q') : ∀ K, PE n (wilsonPoly x c K) (wilsonPoly y c K)
  | 0 => pe_smul n _ (chiPow_pe n h 0)
  | K + 1 => pe_append n (wilsonPoly_pe h c K) (pe_smul n _ (chiPow_pe n h _))

end

/-- Ring homomorphism up to `PE n`. -/
structure RingSub (n : Nat) (S : RatPoly → RatPoly) : Prop where
  mul : ∀ p q, PE n (S (polyMul p q)) (polyMul (S p) (S q))
  add : ∀ p q, PE n (S (polyAdd p q)) (polyAdd (S p) (S q))
  smul : ∀ c p, PE n (S (polySmul c p)) (polySmul c (S p))
  neg : ∀ p, PE n (S (polyNeg p)) (polyNeg (S p))
  one : PE n (S polyOne) polyOne

variable {n : Nat} {S : RatPoly → RatPoly}

theorem chiPow_sub (hS : RingSub n S) (x : RatPoly) : ∀ k, PE n (S (chiPow x k)) (chiPow (S x) k)
  | 0 => hS.one
  | k + 1 => pe_trans n (hS.mul _ _) (pe_mul2 n (hS.smul 2 x) (chiPow_sub hS x k))

theorem wilsonPoly_sub (hS : RingSub n S) (x : RatPoly) (c : Nat → Q') :
    ∀ K, PE n (S (wilsonPoly x c K)) (wilsonPoly (S x) c K)
  | 0 => pe_trans n (hS.smul _ _) (pe_smul n _ (chiPow_sub hS x 0))
  | K + 1 => pe_trans n (hS.add _ _) (pe_append n (wilsonPoly_sub hS x c K)
      (pe_trans n (hS.smul _ _) (pe_smul n _ (chiPow_sub hS x _))))

/-- Componentwise `PE`. -/
structure QPE (n : Nat) (q r : PolyQuaternion) : Prop where
  s : PE n q.scalar r.scalar
  i : PE n q.iPart r.iPart
  j : PE n q.jPart r.jPart
  k : PE n q.kPart r.kPart

def qsub (S : RatPoly → RatPoly) (q : PolyQuaternion) : PolyQuaternion :=
  ⟨S q.scalar, S q.iPart, S q.jPart, S q.kPart⟩

theorem qpe_trans {q r t : PolyQuaternion} (h : QPE n q r) (h' : QPE n r t) : QPE n q t :=
  ⟨pe_trans n h.s h'.s, pe_trans n h.i h'.i, pe_trans n h.j h'.j, pe_trans n h.k h'.k⟩

theorem qpe_conj {q r : PolyQuaternion} (h : QPE n q r) : QPE n (conj q) (conj r) :=
  ⟨h.s, pe_neg n h.i, pe_neg n h.j, pe_neg n h.k⟩

theorem qpe_mul {q q' r r' : PolyQuaternion} (h : QPE n q q') (h' : QPE n r r') : QPE n (mul q r) (mul q' r') :=
  ⟨pe_append n (pe_mul2 n h.s h'.s) (pe_neg n (pe_append n (pe_mul2 n h.i h'.i)
      (pe_append n (pe_mul2 n h.j h'.j) (pe_mul2 n h.k h'.k)))),
   pe_append n (pe_mul2 n h.s h'.i) (pe_append n (pe_mul2 n h.i h'.s)
      (pe_append n (pe_mul2 n h.j h'.k) (pe_neg n (pe_mul2 n h.k h'.j)))),
   pe_append n (pe_mul2 n h.s h'.j) (pe_append n (pe_mul2 n h.j h'.s)
      (pe_append n (pe_mul2 n h.k h'.i) (pe_neg n (pe_mul2 n h.i h'.k)))),
   pe_append n (pe_mul2 n h.s h'.k) (pe_append n (pe_mul2 n h.k h'.s)
      (pe_append n (pe_mul2 n h.i h'.j) (pe_neg n (pe_mul2 n h.j h'.i))))⟩

theorem shape_s (hS : RingSub n S) (a b c d e f g h : RatPoly) :
    PE n (S (polyAdd (polyMul a b) (polyNeg (polyAdd (polyMul c d) (polyAdd (polyMul e f) (polyMul g h))))))
      (polyAdd (polyMul (S a) (S b)) (polyNeg (polyAdd (polyMul (S c) (S d))
        (polyAdd (polyMul (S e) (S f)) (polyMul (S g) (S h)))))) :=
  pe_trans n (hS.add _ _) (pe_append n (hS.mul _ _) (pe_trans n (hS.neg _) (pe_neg n
    (pe_trans n (hS.add _ _) (pe_append n (hS.mul _ _) (pe_trans n (hS.add _ _)
      (pe_append n (hS.mul _ _) (hS.mul _ _))))))))

theorem shape_v (hS : RingSub n S) (a b c d e f g h : RatPoly) :
    PE n (S (polyAdd (polyMul a b) (polyAdd (polyMul c d) (polyAdd (polyMul e f) (polyNeg (polyMul g h))))))
      (polyAdd (polyMul (S a) (S b)) (polyAdd (polyMul (S c) (S d))
        (polyAdd (polyMul (S e) (S f)) (polyNeg (polyMul (S g) (S h)))))) :=
  pe_trans n (hS.add _ _) (pe_append n (hS.mul _ _) (pe_trans n (hS.add _ _) (pe_append n (hS.mul _ _)
    (pe_trans n (hS.add _ _) (pe_append n (hS.mul _ _) (pe_trans n (hS.neg _) (pe_neg n (hS.mul _ _))))))))

theorem qmul_sub (hS : RingSub n S) (q r : PolyQuaternion) : QPE n (qsub S (mul q r)) (mul (qsub S q) (qsub S r)) :=
  ⟨shape_s hS _ _ _ _ _ _ _ _, shape_v hS _ _ _ _ _ _ _ _, shape_v hS _ _ _ _ _ _ _ _, shape_v hS _ _ _ _ _ _ _ _⟩

theorem qconj_sub (hS : RingSub n S) (q : PolyQuaternion) : QPE n (qsub S (conj q)) (conj (qsub S q)) :=
  ⟨pe_refl n _, hS.neg _, hS.neg _, hS.neg _⟩

/-- The `plaqWord` shape `(l₁ l₂)(l₃* l₄*)`. -/
theorem word_sub (hS : RingSub n S) (l1 l2 l3 l4 : PolyQuaternion) :
    QPE n (qsub S (mul (mul l1 l2) (mul (conj l3) (conj l4))))
      (mul (mul (qsub S l1) (qsub S l2)) (mul (conj (qsub S l3)) (conj (qsub S l4)))) :=
  qpe_trans (qmul_sub hS _ _) (qpe_mul (qmul_sub hS _ _)
    (qpe_trans (qmul_sub hS _ _) (qpe_mul (qconj_sub hS _) (qconj_sub hS _))))

theorem prodPoly_sub (hS : RingSub n S) (F : Z4Plaq → RatPoly) :
    ∀ ps : List Z4Plaq, PE n (S (prodPoly F ps)) (prodPoly (fun p => S (F p)) ps)
  | [] => hS.one
  | _ :: ps => pe_trans n (hS.mul _ _) (pe_mul2 n (pe_refl n _) (prodPoly_sub hS F ps))

/-- `T_K` of a substituted plaquette word. -/
theorem TK_word_sub (hS : RingSub n S) (l1 l2 l3 l4 : PolyQuaternion) (c : Nat → Q') (K : Nat) :
    PE n (S (wilsonPoly (mul (mul l1 l2) (mul (conj l3) (conj l4))).scalar c K))
      (wilsonPoly (mul (mul (qsub S l1) (qsub S l2)) (mul (conj (qsub S l3)) (conj (qsub S l4)))).scalar c K) :=
  pe_trans n (wilsonPoly_sub hS _ c K) (wilsonPoly_pe n (word_sub hS l1 l2 l3 l4).s c K)

end YMGap.Continuum.SU2TorusRPSubst

#print axioms YMGap.Continuum.SU2TorusRPSubst.TK_word_sub
#print axioms YMGap.Continuum.SU2TorusRPSubst.prodPoly_sub
