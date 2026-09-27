/-
An eventual order with a geometric real error closes to an exact eventual order.
The representative bound below is eliminated only into this proposition proof: this
file does not assign a Type-valued convergence modulus to an arbitrary RC class.
-/

import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Constructive.CRealMul
import YMGap.Constructive.CRealLog

open YMGap.Constructive

namespace YMGap.Continuum.RCGeometricErrorClosure

set_option autoImplicit false

/-- Any geometric upper error disappears from the order on constructive real
classes. The class `c` may have either sign. -/
theorem le_of_geometric_error (q : Q') (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (a b c : CReal.RC)
    (h : ∀ n : Nat, CReal.RCle a
      (CReal.RCadd b (CReal.RCscale (q ^ n) c))) : CReal.RCle a b := by
  revert h
  refine Quotient.inductionOn a (fun A => ?_)
  refine Quotient.inductionOn b (fun B => ?_)
  refine Quotient.inductionOn c (fun C => ?_)
  intro h ε hε
  obtain ⟨Nc, M, hM0, hC⟩ := CReal.localBound C
  let p : Q' := HalfPow.half * ε
  have hp : (0 : Q') < p := ExpNeg.half_mul_pos ε hε
  let D : Q' := 1 + M
  have hD : (0 : Q') < D := Q'.pos_add_nonneg (by decide) hM0
  have hDnum : 0 < D.num := CReal.num_pos_of_pos hD
  let δ : Q' := HKConv.divPos p D
  have hδ : (0 : Q') < δ := HKConv.divPos_pos (CReal.num_pos_of_pos hp)
  let n : Nat := HKConvGen.powBaseCutoff q δ
  have hqn : q ^ n ≤ δ := HKConvGen.pow_base_le_cutoff hq0 hq1 hδ
  have hqnn : (0 : Q') ≤ q ^ n := Q'.pow_nonneg q (Q'.le_of_lt hq0) n
  have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδ
  have hMle : M ≤ D := by
    apply Q'.le_trans' M (M + 1) D
    · exact Q'.add_le_self_of_nonneg M 1 (by decide)
    · exact Q'.le_of_eqv (Q'.add_comm_eqv M 1)
  have hδD : (δ * D).eqv p := HKConv.divPos_mul_eqv hDnum
  have hqM : q ^ n * M ≤ p := by
    have h1 : q ^ n * M ≤ δ * M :=
      Q'.mul_le_mul_of_nonneg_right (q ^ n) δ M hqn hM0
    have h2 : δ * M ≤ δ * D :=
      Q'.mul_le_mul_of_nonneg_left M D δ hMle hδnn
    exact Q'.le_trans' _ _ _ h1
      (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hδD))
  obtain ⟨Nh, hNh⟩ := h n p hp
  refine ⟨max Nh Nc, fun k hk => ?_⟩
  have hkN : Nh ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hkC : Nc ≤ k := Nat.le_trans (Nat.le_max_right _ _) hk
  have hAk : A.approx k ≤ (B.approx k + q ^ n * C.approx k) + p := hNh k hkN
  have hCk : C.approx k ≤ M := (hC k hkC).2
  have hterm : q ^ n * C.approx k ≤ p :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hCk hqnn) hqM
  have hsum : (B.approx k + q ^ n * C.approx k) + p
      ≤ (B.approx k + p) + p :=
    Q'.add_le_add_right _ _ p
      (Q'.add_le_add_left _ _ _ hterm)
  have hreassoc : ((B.approx k + p) + p).eqv
      (B.approx k + (p + p)) := Q'.add_assoc_eqv _ _ _
  have htwo : (p + p).eqv ε := ExpNeg.two_halves ε
  exact Q'.le_trans' _ _ _ hAk
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc)
        (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv htwo))))

end YMGap.Continuum.RCGeometricErrorClosure

#print axioms YMGap.Continuum.RCGeometricErrorClosure.le_of_geometric_error
