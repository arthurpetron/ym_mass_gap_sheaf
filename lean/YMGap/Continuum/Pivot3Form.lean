/-
Assembly of the scaled SU(2) heat-kernel 3×3 energy identity

    P · form3 ≃ P·M₀² + M₁² + big·M₂²      (`pform3_eq_sos`)

with `P = 3a⁴+2a²+1`.  Both sides are reduced to the symmetric quadratic form
`qform` with explicit base-polynomial (`evalC`) matrix entries; the six entries
match by `QPoly` `decide`.  This is the (degree-32) polynomial core of 3×3
positive-semidefiniteness.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.Pivot3Identity

namespace YMGap.Continuum.Pivot3

open YMGap.Constructive

/-! ## Gram entries as `evalC` base-polynomials -/

/-- `G₁₁ = 1 + m₂ ≃ evalC [1,0,…,0,3]` (the `1` and the `3a⁸`). -/
theorem G11_evalC (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (G11 t ht)
      (evalC t ht [Q'.ofNat 1,0,0,0,0,0,0,0,Q'.ofNat 3]) := by
  -- G11 = C 1 + m2
  refine equiv_trans (add_congr (C_evalC t ht 1) (m2_evalC t ht)) ?_
  refine equiv_trans (evalC_add t ht [Q'.ofNat 1] [0,0,0,0,0,0,0,0,Q'.ofNat 3]) ?_
  exact evalC_eqv t ht _ _ (by decide)

/-- `G₁₂ = m₁ + m₃ ≃ evalC` (the `2a³` and `4a¹⁵`). -/
theorem G12_evalC (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (G12 t ht)
      (evalC t ht [0,0,0,Q'.ofNat 2,0,0,0,0,0,0,0,0,0,0,0,Q'.ofNat 4]) := by
  refine equiv_trans (add_congr (m1_evalC t ht) (m3_evalC t ht)) ?_
  refine equiv_trans
    (evalC_add t ht [0,0,0,Q'.ofNat 2]
      [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,Q'.ofNat 4]) ?_
  exact evalC_eqv t ht _ _ (by decide)

/-- `G₂₂ = (1 + m₂) + m₄ ≃ evalC` (the `1`, `3a⁸`, `5a²⁴`). -/
theorem G22_evalC (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (G22 t ht)
      (evalC t ht [Q'.ofNat 1,0,0,0,0,0,0,0,Q'.ofNat 3,
        0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,Q'.ofNat 5]) := by
  -- G22 = (C 1 + m2) + m4
  refine equiv_trans
    (add_congr (add_congr (C_evalC t ht 1) (m2_evalC t ht)) (m4_evalC t ht)) ?_
  refine equiv_trans
    (add_congr (evalC_add t ht [Q'.ofNat 1] [0,0,0,0,0,0,0,0,Q'.ofNat 3])
      (equiv_refl _)) ?_
  refine equiv_trans
    (evalC_add t ht (QPoly.padd [Q'.ofNat 1] [0,0,0,0,0,0,0,0,Q'.ofNat 3])
      [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,Q'.ofNat 5]) ?_
  exact evalC_eqv t ht _ _ (by decide)

/-! ## `form3` as `qform` of the `evalC` Gram entries -/

/-- The six Gram-entry coefficient lists `[G00,G11,G22,G01,G02,G12]`. -/
def lG00 : QPoly.Poly := [Q'.ofNat 1]
def lG11 : QPoly.Poly := [Q'.ofNat 1,0,0,0,0,0,0,0,Q'.ofNat 3]
def lG22 : QPoly.Poly :=
  [Q'.ofNat 1,0,0,0,0,0,0,0,Q'.ofNat 3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,Q'.ofNat 5]
def lG01 : QPoly.Poly := [0,0,0,Q'.ofNat 2]
def lG02 : QPoly.Poly := [0,0,0,0,0,0,0,0,Q'.ofNat 3]
def lG12 : QPoly.Poly := [0,0,0,Q'.ofNat 2,0,0,0,0,0,0,0,0,0,0,0,Q'.ofNat 4]

/-- **`form3 ≃ qform` of the `evalC` Gram entries.** -/
theorem form3_qform_evalC (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') :
    CReal.Equiv (form3 t ht c0 c1 c2)
      (qform (evalC t ht lG00) (evalC t ht lG11) (evalC t ht lG22)
             (evalC t ht lG01) (evalC t ht lG02) (evalC t ht lG12) c0 c1 c2) := by
  rw [form3_eq_qform]
  exact qform_congr (C_evalC t ht 1) (G11_evalC t ht) (G22_evalC t ht)
    (m1_evalC t ht) (m2_evalC t ht) (G12_evalC t ht) c0 c1 c2

/-! ## The scaled left-hand side `P · form3` -/

/-- The scale polynomial `P = 3a⁴+2a²+1`. -/
def lP : QPoly.Poly := [Q'.ofNat 1,0,Q'.ofNat 2,0,Q'.ofNat 3]

/-- `Pp = evalC lP` (the `CReal` value of `P`). -/
def Pp (t : Q') (ht : (0 : Q') ≤ t) : CReal := evalC t ht lP

/-- **`P·form3 ≃ qform` of the `evalC` of `pmul lP G_i`.** -/
theorem Pform3_qform (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') :
    CReal.Equiv (CReal.mul (Pp t ht) (form3 t ht c0 c1 c2))
      (qform (evalC t ht (QPoly.pmul lP lG00)) (evalC t ht (QPoly.pmul lP lG11))
             (evalC t ht (QPoly.pmul lP lG22)) (evalC t ht (QPoly.pmul lP lG01))
             (evalC t ht (QPoly.pmul lP lG02)) (evalC t ht (QPoly.pmul lP lG12))
             c0 c1 c2) := by
  refine equiv_trans (mul_congr_right (A := Pp t ht) (form3_qform_evalC t ht c0 c1 c2)) ?_
  refine equiv_trans (qform_scale (Pp t ht) _ _ _ _ _ _ c0 c1 c2) ?_
  exact qform_congr
    (evalC_mul t ht lP lG00) (evalC_mul t ht lP lG11) (evalC_mul t ht lP lG22)
    (evalC_mul t ht lP lG01) (evalC_mul t ht lP lG02) (evalC_mul t ht lP lG12) c0 c1 c2

/-! ## The sum-of-squares right-hand side `P·M₀² + M₁² + big·M₂²`

`M₀ = c₀ + m₁c₁ + m₂c₂`, `M₁ = α·c₁ + β·c₂`, `M₂ = γ·c₂`, with
`α = (1−a²)P`, `β = (1−a²)S₁₂'`, `γ = (1−a²)²(a²+1)`, and weights `P`, `1`,
`big`. -/

/-- `α = (1−a²)·P`. -/
def lAlpha : QPoly.Poly := [Q'.ofNat 1,0,Q'.ofNat 1,0,Q'.ofNat 1,0,-(Q'.ofNat 3)]
/-- `β = (1−a²)·S₁₂'`. -/
def lBeta : QPoly.Poly :=
  [0,0,0,Q'.ofNat 2,0,Q'.ofNat 2,0,Q'.ofNat 2,0,Q'.ofNat 2,0,-(Q'.ofNat 4),0,-(Q'.ofNat 4)]
/-- `γ = (1−a²)²(a²+1)`. -/
def lGamma : QPoly.Poly := [Q'.ofNat 1,0,-(Q'.ofNat 1),0,-(Q'.ofNat 1),0,Q'.ofNat 1]
/-- `big = 15a¹⁶+24a¹⁴+36a¹²+36a¹⁰+32a⁸+20a⁶+12a⁴+4a²+1`. -/
def lbig : QPoly.Poly :=
  [Q'.ofNat 1,0,Q'.ofNat 4,0,Q'.ofNat 12,0,Q'.ofNat 20,0,Q'.ofNat 32,0,Q'.ofNat 36,
   0,Q'.ofNat 36,0,Q'.ofNat 24,0,Q'.ofNat 15]

/-- `big` as a `CReal`. -/
def bigp (t : Q') (ht : (0 : Q') ≤ t) : CReal := evalC t ht lbig

/-- The three SOS linear forms. -/
def M0 (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') : CReal :=
  lin3 (evalC t ht lG01) (evalC t ht lG02) c0 c1 c2
def M1 (t : Q') (ht : (0 : Q') ≤ t) (c1 c2 : Q') : CReal :=
  lin2 (evalC t ht lAlpha) (evalC t ht lBeta) c1 c2
def M2 (t : Q') (ht : (0 : Q') ≤ t) (c2 : Q') : CReal :=
  CReal.mul (CReal.ofQ' c2) (evalC t ht lGamma)

/-- The sum-of-squares value `P·M₀² + (M₁² + big·M₂²)`. -/
def sos3 (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') : CReal :=
  CReal.add (CReal.mul (Pp t ht) (CReal.mul (M0 t ht c0 c1 c2) (M0 t ht c0 c1 c2)))
    (CReal.add (CReal.mul (M1 t ht c1 c2) (M1 t ht c1 c2))
      (CReal.mul (bigp t ht) (CReal.mul (M2 t ht c2) (M2 t ht c2))))

/-! ### Each square reduced to a `qform` of `evalC` entries -/

/-- `P·M₀² ≃ qform` with `evalC` entries
`pmul lP [1], pmul lP (G01²), pmul lP (G02²), pmul lP G01, pmul lP G02,
pmul lP (G01·G02)`. -/
theorem PM0_qform (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') :
    CReal.Equiv (CReal.mul (Pp t ht) (CReal.mul (M0 t ht c0 c1 c2) (M0 t ht c0 c1 c2)))
      (qform (evalC t ht (QPoly.pmul lP [Q'.ofNat 1]))
             (evalC t ht (QPoly.pmul lP (QPoly.pmul lG01 lG01)))
             (evalC t ht (QPoly.pmul lP (QPoly.pmul lG02 lG02)))
             (evalC t ht (QPoly.pmul lP lG01))
             (evalC t ht (QPoly.pmul lP lG02))
             (evalC t ht (QPoly.pmul lP (QPoly.pmul lG01 lG02))) c0 c1 c2) := by
  -- M0² ≃ qform(C1, U², V², U, V, UV) with U=evalC lG01, V=evalC lG02.
  refine equiv_trans (mul_congr_right (A := Pp t ht)
    (lin3_sq (evalC t ht lG01) (evalC t ht lG02) c0 c1 c2)) ?_
  -- scale by P
  refine equiv_trans (qform_scale (Pp t ht) _ _ _ _ _ _ c0 c1 c2) ?_
  -- normalise each entry: P·C1, P·(U·U)→evalC pmul lP (pmul lG01 lG01), etc.
  refine qform_congr ?_ ?_ ?_ ?_ ?_ ?_ c0 c1 c2
  · -- P·(C 1) ≃ evalC (pmul lP [1])
    exact equiv_trans (mul_congr_right (A := Pp t ht) (C_evalC t ht 1))
      (evalC_mul t ht lP [Q'.ofNat 1])
  · -- P·(U·U) ≃ evalC (pmul lP (pmul lG01 lG01))
    exact equiv_trans (mul_congr_right (A := Pp t ht) (evalC_mul t ht lG01 lG01))
      (evalC_mul t ht lP (QPoly.pmul lG01 lG01))
  · exact equiv_trans (mul_congr_right (A := Pp t ht) (evalC_mul t ht lG02 lG02))
      (evalC_mul t ht lP (QPoly.pmul lG02 lG02))
  · exact evalC_mul t ht lP lG01
  · exact evalC_mul t ht lP lG02
  · exact equiv_trans (mul_congr_right (A := Pp t ht) (evalC_mul t ht lG01 lG02))
      (evalC_mul t ht lP (QPoly.pmul lG01 lG02))

/-- `M₁² ≃ qform 0 α² β² 0 0 (αβ)` with `evalC` entries. -/
theorem M1_qform (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') :
    CReal.Equiv (CReal.mul (M1 t ht c1 c2) (M1 t ht c1 c2))
      (qform (C 0) (evalC t ht (QPoly.pmul lAlpha lAlpha))
             (evalC t ht (QPoly.pmul lBeta lBeta)) (C 0) (C 0)
             (evalC t ht (QPoly.pmul lAlpha lBeta)) c0 c1 c2) := by
  refine equiv_trans (lin2_sq (evalC t ht lAlpha) (evalC t ht lBeta) c0 c1 c2) ?_
  exact qform_congr (equiv_refl (C 0)) (evalC_mul t ht lAlpha lAlpha)
    (evalC_mul t ht lBeta lBeta) (equiv_refl (C 0)) (equiv_refl (C 0))
    (evalC_mul t ht lAlpha lBeta) c0 c1 c2

/-- `big·M₂² ≃ qform 0 0 (big·γ²) 0 0 0` with `evalC` entries. -/
theorem bigM2_qform (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') :
    CReal.Equiv (CReal.mul (bigp t ht) (CReal.mul (M2 t ht c2) (M2 t ht c2)))
      (qform (C 0) (C 0) (evalC t ht (QPoly.pmul lbig (QPoly.pmul lGamma lGamma)))
             (C 0) (C 0) (C 0) c0 c1 c2) := by
  -- M2² ≃ qform 0 0 γ² 0 0 0
  refine equiv_trans (mul_congr_right (A := bigp t ht) (lin1_sq (evalC t ht lGamma) c0 c1 c2)) ?_
  refine equiv_trans (qform_scale (bigp t ht) _ _ _ _ _ _ c0 c1 c2) ?_
  refine qform_congr ?_ ?_ ?_ ?_ ?_ ?_ c0 c1 c2
  · exact mul_C0_eqv (bigp t ht)
  · exact mul_C0_eqv (bigp t ht)
  · exact equiv_trans (mul_congr_right (A := bigp t ht) (evalC_mul t ht lGamma lGamma))
      (evalC_mul t ht lbig (QPoly.pmul lGamma lGamma))
  · exact mul_C0_eqv (bigp t ht)
  · exact mul_C0_eqv (bigp t ht)
  · exact mul_C0_eqv (bigp t ht)

/-! ### Combine the three squares and match to the scaled left-hand side -/

-- Entry-sum abbreviations (RHS qform entries after `qform_add`).
private def rA : QPoly.Poly :=
  QPoly.padd (QPoly.pmul lP [Q'.ofNat 1]) (QPoly.padd [] [])
private def rB : QPoly.Poly :=
  QPoly.padd (QPoly.pmul lP (QPoly.pmul lG01 lG01))
    (QPoly.padd (QPoly.pmul lAlpha lAlpha) [])
private def rC : QPoly.Poly :=
  QPoly.padd (QPoly.pmul lP (QPoly.pmul lG02 lG02))
    (QPoly.padd (QPoly.pmul lBeta lBeta) (QPoly.pmul lbig (QPoly.pmul lGamma lGamma)))
private def rD : QPoly.Poly := QPoly.padd (QPoly.pmul lP lG01) (QPoly.padd [] [])
private def rE : QPoly.Poly := QPoly.padd (QPoly.pmul lP lG02) (QPoly.padd [] [])
private def rF : QPoly.Poly :=
  QPoly.padd (QPoly.pmul lP (QPoly.pmul lG01 lG02))
    (QPoly.padd (QPoly.pmul lAlpha lBeta) [])

/-- **The scaled SU(2) heat-kernel 3×3 energy identity:**
`P·form3 ≃ P·M₀² + M₁² + big·M₂²`.  Both sides reduce to `qform` with `evalC`
matrix entries that match by `QPoly` `decide`. -/
theorem pform3_eq_sos (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') :
    CReal.Equiv (CReal.mul (Pp t ht) (form3 t ht c0 c1 c2)) (sos3 t ht c0 c1 c2) := by
  -- RHS sos3 ≃ qform(evalC rA, …, evalC rF).
  have hsos : CReal.Equiv (sos3 t ht c0 c1 c2)
      (qform (evalC t ht rA) (evalC t ht rB) (evalC t ht rC)
             (evalC t ht rD) (evalC t ht rE) (evalC t ht rF) c0 c1 c2) := by
    unfold sos3
    -- qform(PM0) + (qform(M1) + qform(bigM2))
    refine equiv_trans
      (add_congr (PM0_qform t ht c0 c1 c2)
        (add_congr (M1_qform t ht c0 c1 c2) (bigM2_qform t ht c0 c1 c2))) ?_
    -- fold the inner add: qform(M1)+qform(bigM2) ≃ qform(M1+bigM2)
    refine equiv_trans (add_congr (equiv_refl _)
      (qform_add _ _ _ _ _ _ _ _ _ _ _ _ c0 c1 c2)) ?_
    -- fold outer add
    refine equiv_trans (qform_add _ _ _ _ _ _ _ _ _ _ _ _ c0 c1 c2) ?_
    -- entrywise: each sum of CReals ≃ evalC of padd
    refine qform_congr ?_ ?_ ?_ ?_ ?_ ?_ c0 c1 c2
    · exact equiv_trans (add_congr (equiv_refl _)
        (evalC_add t ht [] [])) (evalC_add t ht (QPoly.pmul lP [Q'.ofNat 1]) (QPoly.padd [] []))
    · exact equiv_trans (add_congr (equiv_refl _)
        (evalC_add t ht (QPoly.pmul lAlpha lAlpha) []))
        (evalC_add t ht (QPoly.pmul lP (QPoly.pmul lG01 lG01))
          (QPoly.padd (QPoly.pmul lAlpha lAlpha) []))
    · exact equiv_trans (add_congr (equiv_refl _)
        (evalC_add t ht (QPoly.pmul lBeta lBeta) (QPoly.pmul lbig (QPoly.pmul lGamma lGamma))))
        (evalC_add t ht (QPoly.pmul lP (QPoly.pmul lG02 lG02))
          (QPoly.padd (QPoly.pmul lBeta lBeta) (QPoly.pmul lbig (QPoly.pmul lGamma lGamma))))
    · exact equiv_trans (add_congr (equiv_refl _)
        (evalC_add t ht [] [])) (evalC_add t ht (QPoly.pmul lP lG01) (QPoly.padd [] []))
    · exact equiv_trans (add_congr (equiv_refl _)
        (evalC_add t ht [] [])) (evalC_add t ht (QPoly.pmul lP lG02) (QPoly.padd [] []))
    · exact equiv_trans (add_congr (equiv_refl _)
        (evalC_add t ht (QPoly.pmul lAlpha lBeta) []))
        (evalC_add t ht (QPoly.pmul lP (QPoly.pmul lG01 lG02))
          (QPoly.padd (QPoly.pmul lAlpha lBeta) []))
  -- LHS ≃ qform(evalC (pmul lP lG_i)); match entries to RHS by decide.
  refine equiv_trans (Pform3_qform t ht c0 c1 c2) (equiv_trans ?_ hsos.symm)
  exact qform_congr
    (evalC_eqv t ht (QPoly.pmul lP lG00) rA (by decide))
    (evalC_eqv t ht (QPoly.pmul lP lG11) rB (by decide))
    (evalC_eqv t ht (QPoly.pmul lP lG22) rC (by decide))
    (evalC_eqv t ht (QPoly.pmul lP lG01) rD (by decide))
    (evalC_eqv t ht (QPoly.pmul lP lG02) rE (by decide))
    (evalC_eqv t ht (QPoly.pmul lP lG12) rF (by decide)) c0 c1 c2

end YMGap.Continuum.Pivot3

/-! ## Axiom-dependency gate (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Pivot3.pform3_eq_sos
