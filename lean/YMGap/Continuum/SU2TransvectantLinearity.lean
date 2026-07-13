/-
# Pointwise linearity of the arbitrary-label Cayley transvectants

The all-order coefficient proof needs to move an exact monomial expansion
through `OmegaK` and the diagonal finite sum.  This module supplies that
algebra over the project's rational setoid.  All equalities are pointwise
`Q'.eqv`; no quotient normalization, classical choice, or finite cutoff is
used.
-/

import YMGap.Continuum.SU2TransvectantGeneralCoefficient

namespace YMGap.Continuum.SU2TransvectantLinearity

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.TransvectantCG

/-- Unbounded pointwise setoid equality of two-factor binary forms. -/
def BForm2Eqv (c d : BForm2) : Prop :=
  ∀ a b, (c a b).eqv (d a b)

/-- Unbounded pointwise setoid equality of binary forms. -/
def BFormEqv (f g : YMGap.Continuum.BinaryForms.BForm) : Prop :=
  ∀ s, (f s).eqv (g s)

/-- Pointwise addition of two-factor forms. -/
def badd (c d : BForm2) : BForm2 := fun a b => c a b + d a b

/-- Pointwise rational scaling of a two-factor form. -/
def bscale (q : Q') (c : BForm2) : BForm2 := fun a b => q * c a b

theorem bform2Eqv_refl (c : BForm2) : BForm2Eqv c c :=
  fun _ _ => Q'.eqv_refl _

theorem bform2Eqv_trans {c d e : BForm2}
    (hcd : BForm2Eqv c d) (hde : BForm2Eqv d e) : BForm2Eqv c e :=
  fun a b => Q'.eqv_trans _ _ _ (hcd a b) (hde a b)

/-- Omega respects pointwise setoid equality. -/
theorem omega_congr (m n : Nat) {c d : BForm2} (h : BForm2Eqv c d) :
    BForm2Eqv (Omega m n c) (Omega m n d) := by
  intro a b
  unfold Omega
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _ (h (a + 1) b))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left _ _ _ (h a (b + 1))))

/-- Omega distributes over pointwise addition. -/
theorem omega_add (m n : Nat) (c d : BForm2) :
    BForm2Eqv (Omega m n (badd c d))
      (badd (Omega m n c) (Omega m n d)) := by
  intro a b
  unfold Omega badd
  let A := Q'.ofNat ((a + 1) * (n - b))
  let B := Q'.ofNat ((m - a) * (b + 1))
  let C := c (a + 1) b
  let D := d (a + 1) b
  let E := c a (b + 1)
  let F := d a (b + 1)
  have hmulA : (A * (C + D)).eqv (A * C + A * D) :=
    Q'.mul_add_eqv A C D
  have hmulB : (B * (E + F)).eqv (B * E + B * F) :=
    Q'.mul_add_eqv B E F
  have hneg : (-(B * (E + F))).eqv (-(B * E) + -(B * F)) :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hmulB)
      (Q'.neg_add_eqv (B * E) (B * F))
  have hsplit :
      (A * (C + D) + -(B * (E + F))).eqv
        ((A * C + A * D) + (-(B * E) + -(B * F))) :=
    Q'.add_eqv_congr' hmulA hneg
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_swap_inner (A * C) (A * D) (-(B * E)) (-(B * F)))

/-- Omega commutes with a rational scalar. -/
theorem omega_scale (m n : Nat) (q : Q') (c : BForm2) :
    BForm2Eqv (Omega m n (bscale q c))
      (bscale q (Omega m n c)) := by
  intro a b
  unfold Omega bscale
  let A := Q'.ofNat ((a + 1) * (n - b))
  let B := Q'.ofNat ((m - a) * (b + 1))
  let C := c (a + 1) b
  let D := c a (b + 1)
  have hA : (A * (q * C)).eqv (q * (A * C)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv A q C))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ C (Q'.mul_comm_eqv A q))
        (Q'.mul_assoc_eqv q A C))
  have hB0 : (B * (q * D)).eqv (q * (B * D)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv B q D))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B q))
        (Q'.mul_assoc_eqv q B D))
  have hB : (-(B * (q * D))).eqv (q * (-(B * D))) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hB0) ?_
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_neg_eqv q (B * D)))
      (Q'.eqv_refl _)
  have hsum := Q'.add_eqv_congr' hA hB
  exact Q'.eqv_trans _ _ _ hsum
    (Q'.eqv_symm (Q'.mul_add_eqv q (A * C) (-(B * D))))

/-- Every iterate of Omega respects pointwise setoid equality. -/
theorem omegaK_congr (m n k : Nat) {c d : BForm2}
    (h : BForm2Eqv c d) :
    BForm2Eqv (OmegaK m n k c) (OmegaK m n k d) := by
  induction k generalizing m n c d with
  | zero => exact h
  | succ k ih =>
      exact ih (m - 1) (n - 1) (omega_congr m n h)

/-- Every iterate of Omega distributes over pointwise addition. -/
theorem omegaK_add (m n k : Nat) (c d : BForm2) :
    BForm2Eqv (OmegaK m n k (badd c d))
      (badd (OmegaK m n k c) (OmegaK m n k d)) := by
  induction k generalizing m n c d with
  | zero => exact bform2Eqv_refl _
  | succ k ih =>
      exact bform2Eqv_trans
        (omegaK_congr (m - 1) (n - 1) k (omega_add m n c d))
        (ih (m - 1) (n - 1) (Omega m n c) (Omega m n d))

/-- Every iterate of Omega commutes with rational scaling. -/
theorem omegaK_scale (m n k : Nat) (q : Q') (c : BForm2) :
    BForm2Eqv (OmegaK m n k (bscale q c))
      (bscale q (OmegaK m n k c)) := by
  induction k generalizing m n c with
  | zero => exact bform2Eqv_refl _
  | succ k ih =>
      exact bform2Eqv_trans
        (omegaK_congr (m - 1) (n - 1) k (omega_scale m n q c))
        (ih (m - 1) (n - 1) (Omega m n c))

/-- Diagonal restriction respects pointwise setoid equality. -/
theorem diag_congr {c d : BForm2} (h : BForm2Eqv c d) :
    BFormEqv (diag c) (diag d) := by
  intro s
  unfold diag
  exact finSum_eqv_congr _ _ (fun a => h a (s - a)) (s + 1)

/-- The arbitrary-order transvectant respects pointwise setoid equality. -/
theorem transvect_congr (m n k : Nat) {c d : BForm2}
    (h : BForm2Eqv c d) :
    BFormEqv (transvect m n k c) (transvect m n k d) :=
  diag_congr (omegaK_congr m n k h)

/-- The arbitrary-order transvectant distributes over pointwise addition. -/
theorem transvect_add (m n k : Nat) (c d : BForm2) :
    BFormEqv (transvect m n k (badd c d))
      (fun s => transvect m n k c s + transvect m n k d s) :=
  fun s => Q'.eqv_trans _ _ _
    (diag_congr (omegaK_add m n k c d) s)
    (finSum_add
      (fun a => OmegaK m n k c a (s - a))
      (fun a => OmegaK m n k d a (s - a)) (s + 1))

/-- The arbitrary-order transvectant commutes with rational scaling. -/
theorem transvect_scale (m n k : Nat) (q : Q') (c : BForm2) :
    BFormEqv (transvect m n k (bscale q c))
      (fun s => q * transvect m n k c s) :=
  fun s => Q'.eqv_trans _ _ _
    (diag_congr (omegaK_scale m n k q c) s)
    (Q'.eqv_symm
      (const_mul_finSum
        (fun a => OmegaK m n k c a (s - a)) q (s + 1)))

end YMGap.Continuum.SU2TransvectantLinearity

#print axioms YMGap.Continuum.SU2TransvectantLinearity.omega_congr
#print axioms YMGap.Continuum.SU2TransvectantLinearity.omega_add
#print axioms YMGap.Continuum.SU2TransvectantLinearity.omega_scale
#print axioms YMGap.Continuum.SU2TransvectantLinearity.omegaK_congr
#print axioms YMGap.Continuum.SU2TransvectantLinearity.omegaK_add
#print axioms YMGap.Continuum.SU2TransvectantLinearity.omegaK_scale
#print axioms YMGap.Continuum.SU2TransvectantLinearity.diag_congr
#print axioms YMGap.Continuum.SU2TransvectantLinearity.transvect_congr
#print axioms YMGap.Continuum.SU2TransvectantLinearity.transvect_add
#print axioms YMGap.Continuum.SU2TransvectantLinearity.transvect_scale
