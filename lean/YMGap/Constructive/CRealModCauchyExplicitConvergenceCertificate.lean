/-
# Explicit convergence certificates from eventual CReal Cauchy data

`CReal.ModCauchyEv` already carries a Type-level outer modulus, indexed inner
regularity, and the eventual approximation threshold needed by the diagonal
completion.  This module exposes those same data through
`CReal.ExplicitConvergenceCertificate`, without extracting witnesses from the
legacy propositional `ConvergesTo` interface.

The result is a generic witness-preserving compiler.  It constructs no new
limit and asserts no parameter uniformity beyond the supplied `ModCauchyEv`.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Constructive.CRealConvergenceCertificate
import YMGap.Constructive.CRealCompleteCauchy

namespace YMGap.Constructive

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open HalfPow

namespace CReal

/-! ## The witness-bearing upgrade -/

/-- Compile an eventual-outer CReal Cauchy witness into an explicit
convergence certificate for the same sequence and the same diagonal limit.

For tolerance `ε`, the term stage is the stored outer modulus at
`q = ε/4`.  At a term `N` beyond that stage, the approximation stage only
needs the term's inner regularity threshold and `q.den`; the auxiliary bridge
index used by the eventual outer bound is constructed internally from the
same Cauchy witness. -/
def ModCauchyEv.toExplicitConvergenceCertificate
    {s : Nat → CReal}
    (c : ModCauchyEv s) :
    ExplicitConvergenceCertificate
      s (completeLimitCauchy s c) where
  modulus := fun ε => c.M (HalfPow.half * (HalfPow.half * ε))
  approximationModulus := fun ε N =>
    max (c.reg N (HalfPow.half * (HalfPow.half * ε)))
      (HalfPow.half * (HalfPow.half * ε)).den
  bound := by
    intro ε hε N hN n hn
    let q : Q' := HalfPow.half * (HalfPow.half * ε)
    have hqpos : (0 : Q') < q :=
      ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
    have hregNn : c.reg N q ≤ n :=
      Nat.le_trans (Nat.le_max_left _ _) hn
    have hqdenn : q.den ≤ n :=
      Nat.le_trans (Nat.le_max_right _ _) hn
    have hinvn : Q'.invSucc n ≤ q :=
      Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hqdenn)
        (HalfPow.invSucc_den_le q hqpos)
    have hinvnpos : (0 : Q') < Q'.invSucc n := Q'.invSucc_pos n
    let Kpair : Nat := c.boundK q N (MhatE s c n)
    let J : Nat := max (RhatE s c n) Kpair
    have hRnJ : RhatE s c n ≤ J := Nat.le_max_left _ _
    have hKJ : Kpair ≤ J := Nat.le_max_right _ _
    have hnR : n ≤ RhatE s c n := k_le_RhatE s c n
    have hregNR : c.reg N q ≤ RhatE s c n :=
      Nat.le_trans hregNn hnR
    have hregNJ : c.reg N q ≤ J := Nat.le_trans hregNR hRnJ
    have hregMnR : c.reg (MhatE s c n) (Q'.invSucc n) ≤ RhatE s c n :=
      reg_le_RhatE s c n
    have hregMnJ : c.reg (MhatE s c n) (Q'.invSucc n) ≤ J :=
      Nat.le_trans hregMnR hRnJ
    have hMqn : c.M q ≤ MhatE s c n :=
      Nat.le_trans (c.Mmono q (Q'.invSucc n) hinvnpos hinvn)
        (M_le_MhatE s c n)
    obtain ⟨hI1, hI2⟩ :=
      c.regular N q hqpos n J hregNn hregNJ
    obtain ⟨hO1, hO2⟩ :=
      c.bound q hqpos N (MhatE s c n) hN hMqn J hKJ
    obtain ⟨hII1, hII2⟩ :=
      c.regular (MhatE s c n) (Q'.invSucc n) hinvnpos J
        (RhatE s c n) hregMnJ hregMnR
    have hII1' :
        (s (MhatE s c n)).approx J ≤
          (s (MhatE s c n)).approx (RhatE s c n) + q :=
      Q'.le_trans' _ _ _ hII1 (Q'.add_le_add_left _ _ q hinvn)
    have hII2' :
        (s (MhatE s c n)).approx (RhatE s c n) ≤
          (s (MhatE s c n)).approx J + q :=
      Q'.le_trans' _ _ _ hII2 (Q'.add_le_add_left _ _ q hinvn)
    have h3q : ∀ w : Q', ((w + q) + q) + q ≤ w + ε := by
      intro w
      have hreassoc : (((w + q) + q) + q).eqv
          (w + ((q + q) + q)) := by
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (w + q) q q) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv w q (q + q)) ?_
        exact Q'.add_eqv_congr_left w (q + (q + q)) ((q + q) + q)
          (Q'.eqv_symm (Q'.add_assoc_eqv q q q))
      have hqq_half : q + q ≤ HalfPow.half * ε := by
        refine Q'.le_trans' _ _ _
          (Q'.le_of_eqv (ExpNeg.two_halves (HalfPow.half * ε))) ?_
        exact Q'.le_refl' _
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) ?_
      refine Q'.add_le_add_left w ((q + q) + q) ε ?_
      have hstep1 : (q + q) + q ≤ (HalfPow.half * ε) + q :=
        Q'.add_le_add_right (q + q) (HalfPow.half * ε) q hqq_half
      have hqle : q ≤ HalfPow.half * ε := by
        refine Q'.le_trans' _ _ _ ?_ hqq_half
        exact Q'.add_le_self_of_nonneg q q (Q'.le_of_lt hqpos)
      have hstep2 : (HalfPow.half * ε) + q ≤
          (HalfPow.half * ε) + (HalfPow.half * ε) :=
        Q'.add_le_add_left (HalfPow.half * ε) q
          (HalfPow.half * ε) hqle
      refine Q'.le_trans' _ _ _ hstep1 ?_
      refine Q'.le_trans' _ _ _ hstep2 ?_
      exact Q'.le_of_eqv (ExpNeg.two_halves ε)
    refine ⟨?_, ?_⟩
    · show (s N).approx n ≤
        (completeLimitCauchy s c).approx n + ε
      have hchain : (s N).approx n ≤
          (((s (MhatE s c n)).approx (RhatE s c n) + q) + q) + q := by
        refine Q'.le_trans' _ _ _ hI1 ?_
        refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO1) ?_
        exact Q'.add_le_add_right _ _ q
          (Q'.add_le_add_right _ _ q hII1')
      exact Q'.le_trans' _ _ _ hchain
        (h3q ((s (MhatE s c n)).approx (RhatE s c n)))
    · show (completeLimitCauchy s c).approx n ≤
        (s N).approx n + ε
      have hchain :
          (s (MhatE s c n)).approx (RhatE s c n) ≤
            (((s N).approx n + q) + q) + q := by
        refine Q'.le_trans' _ _ _ hII2' ?_
        refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO2) ?_
        exact Q'.add_le_add_right _ _ q
          (Q'.add_le_add_right _ _ q hI2)
      exact Q'.le_trans' _ _ _ hchain
        (h3q ((s N).approx n))

end CReal

end YMGap.Constructive

/-! ## Dependency gate -/

#print axioms
  YMGap.Constructive.CReal.ModCauchyEv.toExplicitConvergenceCertificate
