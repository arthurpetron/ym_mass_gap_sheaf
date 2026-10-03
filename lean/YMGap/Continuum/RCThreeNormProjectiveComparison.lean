/-
# Three diagonal costs control a cleared projective comparison

The common scale is an arbitrary nonnegative quotient real. No norm floor,
inverse, choice of representatives, carrier map, or comparison producer is
constructed. The two polarization diagonals and the norm diagonal are the
only relative comparison inputs. Zero norms and a zero common scale remain
valid. This is homogeneous order algebra, not a continuum or Wilson estimate.
-/

import YMGap.Continuum.RCSignedPairBudget
import YMGap.Continuum.ScaledGNSCompletionEstimates
import YMGap.Continuum.ReconstructionCapstone
import YMGap.Continuum.RCBilinearDifference

namespace YMGap.Continuum.RCThreeNormProjectiveComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ScaledGNSCompletionEstimates (mul_mono_left mul_mono_right)
open YMGap.Continuum.RCSignedPairBudget (neg_mono scale_congr)

local infixl:65 " +ᵣ " => RCadd
local infixl:65 " -ᵣ " => RCsub
local infixl:70 " *ᵣ " => RCmul
local prefix:75 "-ᵣ" => RCneg

/-- Both signed differences are bounded by the same budget. -/
def twoSided (budget a b : RC) : Prop :=
  RCle (a -ᵣ b) budget ∧ RCle (b -ᵣ a) budget

/- A small private reflection adapter. It merely transports the existing
   rational ring normalizer through five quotient inductions. -/
private inductive E where
  | c : Int → E
  | v : Nat → E
  | a : E → E → E
  | m : E → E → E
  | n : E → E

private def toPoly : E → PolyExpr
  | .c z => .const z
  | .v i => .var i
  | .a p q => .add (toPoly p) (toPoly q)
  | .m p q => .mul (toPoly p) (toPoly q)
  | .n p => .neg (toPoly p)

private def evalR (env : Nat → RC) : E → RC
  | .c z => Quotient.mk crealSetoid (ofQ' (Q'.ofInt z))
  | .v i => env i
  | .a p q => evalR env p +ᵣ evalR env q
  | .m p q => evalR env p *ᵣ evalR env q
  | .n p => -ᵣ(evalR env p)

private def evalC (env : Nat → CReal) : E → CReal
  | .c z => ofQ' (Q'.ofInt z)
  | .v i => env i
  | .a p q => add (evalC env p) (evalC env q)
  | .m p q => mul (evalC env p) (evalC env q)
  | .n p => neg (evalC env p)

private theorem evalR_mk (p : E) (env : Nat → CReal) :
    evalR (fun i => Quotient.mk crealSetoid (env i)) p =
      Quotient.mk crealSetoid (evalC env p) := by
  induction p with
  | c z => rfl
  | v i => rfl
  | a p q hp hq => simp only [evalR, evalC, hp, hq]; rfl
  | m p q hp hq => simp only [evalR, evalC, hp, hq]; rfl
  | n p hp => simp only [evalR, evalC, hp]; rfl

private theorem evalC_approx (p : E) (env : Nat → CReal) (k : Nat) :
    (evalC env p).approx k = eval (fun i => (env i).approx k) (toPoly p) := by
  induction p with
  | c z => rfl
  | v i => rfl
  | a p q hp hq =>
      change (evalC env p).approx k + (evalC env q).approx k =
        eval (fun i => (env i).approx k) (toPoly p) +
          eval (fun i => (env i).approx k) (toPoly q)
      rw [hp, hq]
  | m p q hp hq =>
      change (evalC env p).approx k * (evalC env q).approx k =
        eval (fun i => (env i).approx k) (toPoly p) *
          eval (fun i => (env i).approx k) (toPoly q)
      rw [hp, hq]
  | n p hp =>
      change -(evalC env p).approx k = -eval (fun i => (env i).approx k) (toPoly p)
      rw [hp]

private theorem reflect (p q : E) (h : normalize (toPoly p) = normalize (toPoly q))
    (a b c d e : RC) :
    evalR (fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => e) p =
      evalR (fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => e) q := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  refine Quotient.inductionOn₂ d e ?_
  intro D E'
  let env : Nat → CReal := fun | 0 => A | 1 => B | 2 => C | 3 => D | _ => E'
  have he : (fun
      | 0 => Quotient.mk crealSetoid A | 1 => Quotient.mk crealSetoid B
      | 2 => Quotient.mk crealSetoid C | 3 => Quotient.mk crealSetoid D
      | _ => Quotient.mk crealSetoid E') =
      (fun i => Quotient.mk crealSetoid (env i)) := by
    funext i
    cases i with
    | zero => rfl
    | succ i => cases i with
      | zero => rfl
      | succ i => cases i with
        | zero => rfl
        | succ i => cases i <;> rfl
  refine (congrArg (fun f : Nat → RC => evalR f p) he).trans ?_
  refine (evalR_mk p env).trans ?_
  refine Eq.trans ?_ ((evalR_mk q env).symm.trans
    (congrArg (fun f : Nat → RC => evalR f q) he).symm)
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  rw [evalC_approx, evalC_approx]
  exact poly_identity_of_normal_eq _ _ h _

private theorem zero_add (a : RC) : RCzero +ᵣ a = a :=
  reflect (.a (.c 0) (.v 0)) (.v 0) (by decide) a a a a a

private theorem sub_self (a : RC) : a -ᵣ a = RCzero :=
  reflect (.a (.v 0) (.n (.v 0))) (.c 0) (by decide) a a a a a

private theorem add_sub_cancel (a b : RC) : (a -ᵣ b) +ᵣ b = a :=
  reflect (.a (.a (.v 0) (.n (.v 1))) (.v 1)) (.v 0) (by decide) a b a a a

private theorem neg_sub (a b : RC) : -ᵣ(a -ᵣ b) = b -ᵣ a :=
  reflect (.n (.a (.v 0) (.n (.v 1)))) (.a (.v 1) (.n (.v 0)))
    (by decide) a b a a a

private theorem scale_mul (s : Q') (a b : RC) :
    (RCscale s a) *ᵣ b = RCscale s (a *ᵣ b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (CRealAlg.cmul_assoc (ofQ' s) A B)

/-- A nonnegative factor preserves both signed cleared comparisons. -/
theorem twoSided_mul_right (budget a b F : RC) (hF : RCnonneg F)
    (h : twoSided budget a b) :
    twoSided (budget *ᵣ F) (a *ᵣ F) (b *ᵣ F) := by
  have hf := mul_mono_right hF h.1
  have hr := mul_mono_right hF h.2
  rw [RCBilinearDifference.mul_sub] at hf hr
  exact ⟨hf, hr⟩

private theorem scale_add_same (a : RC) : a +ᵣ a = RCscale 2 a :=
  reflect (.a (.v 0) (.v 0)) (.m (.c 2) (.v 0)) (by decide) a a a a a

private theorem mul_nonneg (a b : RC) (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (a *ᵣ b) := by
  refine Quotient.inductionOn₂ a b ?_ ha hb
  intro A B hA hB
  exact CReal.mul_nonneg hA hB

private theorem add_nonneg {a b : RC} (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (a +ᵣ b) := by
  simpa only [zero_add] using RCadd_le_add ha hb

private theorem sub_nonneg {a b : RC} (h : RCle b a) : RCnonneg (a -ᵣ b) := by
  have hh := RCadd_le_add h (RCle_refl (-ᵣb))
  change RCle (b -ᵣ b) (a -ᵣ b) at hh
  simpa only [sub_self] using hh

private theorem le_of_sub_nonneg {a b : RC} (h : RCnonneg (b -ᵣ a)) : RCle a b := by
  have hh := RCadd_le_add h (RCle_refl a)
  simpa only [zero_add, add_sub_cancel] using hh

private theorem signed_product_upper (x y A B : RC)
    (hx : RCle x A) (hnx : RCle (-ᵣx) A)
    (hy : RCle y B) (hny : RCle (-ᵣy) B) : RCle (x *ᵣ y) (A *ᵣ B) := by
  have h1 := mul_nonneg (A -ᵣ x) (B +ᵣ y) (sub_nonneg hx) (by
    have h := sub_nonneg hny
    have hn : B -ᵣ (-ᵣy) = B +ᵣ y :=
      reflect (.a (.v 0) (.n (.n (.v 1)))) (.a (.v 0) (.v 1))
        (by decide) B y B B B
    simpa only [hn] using h)
  have h2 := mul_nonneg (A +ᵣ x) (B -ᵣ y) (by
    have h := sub_nonneg hnx
    have hn : A -ᵣ (-ᵣx) = A +ᵣ x :=
      reflect (.a (.v 0) (.n (.n (.v 1)))) (.a (.v 0) (.v 1))
        (by decide) A x A A A
    simpa only [hn] using h) (sub_nonneg hy)
  have hh := RCscale_mono HalfPow.half_nonneg (add_nonneg h1 h2)
  rw [RCscale_RCzero] at hh
  have hr : (A -ᵣ x) *ᵣ (B +ᵣ y) +ᵣ (A +ᵣ x) *ᵣ (B -ᵣ y) =
      RCscale 2 ((A *ᵣ B) -ᵣ (x *ᵣ y)) :=
    reflect (.a (.m (.a (.v 0) (.n (.v 1))) (.a (.v 2) (.v 3)))
      (.m (.a (.v 0) (.v 1)) (.a (.v 2) (.n (.v 3)))))
      (.m (.c 2) (.a (.m (.v 0) (.v 2)) (.n (.m (.v 1) (.v 3)))))
      (by decide) A x B y A
  rw [hr, RCscale_RCscale,
    scale_congr (by decide : Q'.eqv (HalfPow.half * 2) 1), RCscale_one] at hh
  exact le_of_sub_nonneg hh

private theorem norm_scale_bound (delta : Q') (P Nk : RC)
    (hdelta : delta ≤ HalfPow.half) (hP : RCnonneg P)
    (hN : RCle (P -ᵣ Nk) (RCscale delta P)) : RCle P (RCscale 2 Nk) := by
  have hh := RCle_trans hN (RCscale_mono_scalar hdelta hP)
  have h := RCadd_le_add hh (RCle_refl Nk)
  rw [add_sub_cancel] at h
  have h2 := RCscale_mono (by decide : (0 : Q') ≤ 2) h
  have hs := RCadd_le_add h2 (RCle_refl (-ᵣP))
  have hl : RCscale 2 P -ᵣ P = P :=
    reflect (.a (.m (.c 2) (.v 0)) (.n (.v 0))) (.v 0) (by decide) P P P P P
  have hr : RCscale 2 (RCscale HalfPow.half P +ᵣ Nk) -ᵣ P = RCscale 2 Nk := by
    rw [RCscale_RCadd, RCscale_RCscale,
      scale_congr (by decide : Q'.eqv (2 * HalfPow.half) 1), RCscale_one]
    exact reflect (.a (.a (.v 0) (.m (.c 2) (.v 1))) (.n (.v 0)))
      (.m (.c 2) (.v 1)) (by decide) P Nk P P P
  change RCle (RCscale 2 P -ᵣ P)
    (RCscale 2 (RCscale HalfPow.half P +ᵣ Nk) -ᵣ P) at hs
  simpa only [hl, hr] using hs

private theorem polarization_error (delta : Q') (lambda Nl Ck Cl Qkp Qkm Qlp Qlm : RC)
    (hd0 : (0 : Q') ≤ delta)
    (hp : twoSided (RCscale delta (lambda *ᵣ Qlp)) Qkp (lambda *ᵣ Qlp))
    (hm : twoSided (RCscale delta (lambda *ᵣ Qlm)) Qkm (lambda *ᵣ Qlm))
    (hk : RCscale 4 Ck = Qkp -ᵣ Qkm)
    (hl : RCscale 4 Cl = Qlp -ᵣ Qlm)
    (hs : RCle (Qlp +ᵣ Qlm) (RCscale 4 Nl)) (hlambda : RCnonneg lambda) :
    twoSided (RCscale delta (lambda *ᵣ Nl)) Ck (lambda *ᵣ Cl) := by
  have hbudget := RCscale_mono hd0 (mul_mono_left hlambda hs)
  have hbs : RCscale delta (lambda *ᵣ (Qlp +ᵣ Qlm)) =
      RCscale delta (lambda *ᵣ Qlp) +ᵣ RCscale delta (lambda *ᵣ Qlm) := by
    have hdist : lambda *ᵣ (Qlp +ᵣ Qlm) = lambda *ᵣ Qlp +ᵣ lambda *ᵣ Qlm :=
      reflect (.m (.v 0) (.a (.v 1) (.v 2)))
        (.a (.m (.v 0) (.v 1)) (.m (.v 0) (.v 2))) (by decide)
        lambda Qlp Qlm lambda lambda
    rw [hdist, RCscale_RCadd]
  have hbr : RCscale delta (lambda *ᵣ RCscale 4 Nl) =
      RCscale 4 (RCscale delta (lambda *ᵣ Nl)) := by
    rw [RCmul_comm lambda (RCscale 4 Nl), scale_mul,
      RCmul_comm Nl lambda, RCscale_RCscale, RCscale_RCscale]
    exact scale_congr (Q'.mul_comm_eqv delta 4) _
  rw [hbs, hbr] at hbudget
  have hforward := RCle_trans (RCadd_le_add hp.1 hm.2) hbudget
  have hreverse := RCle_trans (RCadd_le_add hp.2 hm.1) hbudget
  have hf : (Qkp -ᵣ lambda *ᵣ Qlp) +ᵣ (lambda *ᵣ Qlm -ᵣ Qkm) =
      (Qkp -ᵣ Qkm) -ᵣ lambda *ᵣ (Qlp -ᵣ Qlm) :=
    reflect (.a (.a (.v 0) (.n (.m (.v 1) (.v 2))))
        (.a (.m (.v 1) (.v 3)) (.n (.v 4))))
      (.a (.a (.v 0) (.n (.v 4))) (.n (.m (.v 1) (.a (.v 2) (.n (.v 3))))))
      (by decide) Qkp lambda Qlp Qlm Qkm
  have hr : (lambda *ᵣ Qlp -ᵣ Qkp) +ᵣ (Qkm -ᵣ lambda *ᵣ Qlm) =
      lambda *ᵣ (Qlp -ᵣ Qlm) -ᵣ (Qkp -ᵣ Qkm) :=
    reflect (.a (.a (.m (.v 1) (.v 2)) (.n (.v 0)))
        (.a (.v 4) (.n (.m (.v 1) (.v 3)))))
      (.a (.m (.v 1) (.a (.v 2) (.n (.v 3)))) (.n (.a (.v 0) (.n (.v 4)))))
      (by decide) Qkp lambda Qlp Qlm Qkm
  rw [hf, ← hk, ← hl] at hforward
  rw [hr, ← hk, ← hl] at hreverse
  have hcomm : lambda *ᵣ RCscale 4 Cl = RCscale 4 (lambda *ᵣ Cl) := by
    rw [RCmul_comm lambda (RCscale 4 Cl), scale_mul, RCmul_comm Cl lambda]
  rw [hcomm] at hforward hreverse
  have hsub (a b : RC) : RCscale 4 a -ᵣ RCscale 4 b = RCscale 4 (a -ᵣ b) :=
    reflect (.a (.m (.c 4) (.v 0)) (.n (.m (.c 4) (.v 1))))
      (.m (.c 4) (.a (.v 0) (.n (.v 1)))) (by decide) a b a a a
  rw [hsub] at hforward hreverse
  let quarter : Q' := Q'.mkPos 1 4 (by decide)
  have hquarter : (0 : Q') ≤ quarter := by decide
  have hq4 : Q'.eqv (quarter * 4) 1 := by decide
  have cancel (a b : RC) (h : RCle (RCscale 4 a) (RCscale 4 b)) : RCle a b := by
    have hh := RCscale_mono hquarter h
    simpa only [RCscale_RCscale, scale_congr hq4, RCscale_one] using hh
  exact ⟨cancel _ _ hforward, cancel _ _ hreverse⟩

/-- Relative errors on the three actual diagonals imply a two-sided cleared
projective error. No division or positive lower norm is used. -/
theorem three_norm_projective_compare (delta : Q')
    (lambda Nk Nl Ck Cl Qkp Qkm Qlp Qlm : RC)
    (hd0 : (0 : Q') ≤ delta) (hdhalf : delta ≤ HalfPow.half)
    (hlambda : RCnonneg lambda) (hNl : RCnonneg Nl)
    (hN : twoSided (RCscale delta (lambda *ᵣ Nl)) Nk (lambda *ᵣ Nl))
    (hQplus : twoSided (RCscale delta (lambda *ᵣ Qlp)) Qkp (lambda *ᵣ Qlp))
    (hQminus : twoSided (RCscale delta (lambda *ᵣ Qlm)) Qkm (lambda *ᵣ Qlm))
    (hpolk : RCscale 4 Ck = Qkp -ᵣ Qkm)
    (hpoll : RCscale 4 Cl = Qlp -ᵣ Qlm)
    (hsum : RCle (Qlp +ᵣ Qlm) (RCscale 4 Nl))
    (hCl : RCle Cl Nl) (hnegCl : RCle (-ᵣCl) Nl) :
    twoSided (RCscale (4 * delta) (Nk *ᵣ Nl)) (Ck *ᵣ Nl) (Cl *ᵣ Nk) := by
  let P := lambda *ᵣ Nl
  let D := RCscale delta P
  have hP : RCnonneg P := mul_nonneg lambda Nl hlambda hNl
  have hscale : RCle P (RCscale 2 Nk) := norm_scale_bound delta P Nk hdhalf hP hN.2
  have hcross : twoSided D Ck (lambda *ᵣ Cl) :=
    polarization_error delta lambda Nl Ck Cl Qkp Qkm Qlp Qlm
      hd0 hQplus hQminus hpolk hpoll hsum hlambda
  have hnormNeg : RCle (-ᵣ(Nk -ᵣ P)) D := by
    simpa only [neg_sub] using hN.2
  have hnormNeg' : RCle (-ᵣ(P -ᵣ Nk)) D := by
    simpa only [neg_sub] using hN.1
  have hprod := signed_product_upper Cl (P -ᵣ Nk) Nl D hCl hnegCl hN.2 hnormNeg'
  have hprod' := signed_product_upper Cl (Nk -ᵣ P) Nl D hCl hnegCl hN.1 hnormNeg
  have he := RCadd_le_add (mul_mono_right hNl hcross.1) hprod
  have he' := RCadd_le_add (mul_mono_right hNl hcross.2) hprod'
  have hclear : (Ck -ᵣ lambda *ᵣ Cl) *ᵣ Nl +ᵣ Cl *ᵣ (P -ᵣ Nk) =
      Ck *ᵣ Nl -ᵣ Cl *ᵣ Nk :=
    reflect (.a (.m (.a (.v 0) (.n (.m (.v 1) (.v 2)))) (.v 3))
        (.m (.v 2) (.a (.m (.v 1) (.v 3)) (.n (.v 4)))))
      (.a (.m (.v 0) (.v 3)) (.n (.m (.v 2) (.v 4))))
      (by decide) Ck lambda Cl Nl Nk
  have hclear' : (lambda *ᵣ Cl -ᵣ Ck) *ᵣ Nl +ᵣ Cl *ᵣ (Nk -ᵣ P) =
      Cl *ᵣ Nk -ᵣ Ck *ᵣ Nl :=
    reflect (.a (.m (.a (.m (.v 1) (.v 2)) (.n (.v 0))) (.v 3))
        (.m (.v 2) (.a (.v 4) (.n (.m (.v 1) (.v 3))))))
      (.a (.m (.v 2) (.v 4)) (.n (.m (.v 0) (.v 3))))
      (by decide) Ck lambda Cl Nl Nk
  have hbound : D *ᵣ Nl +ᵣ Nl *ᵣ D = RCscale 2 (RCscale delta (P *ᵣ Nl)) := by
    rw [RCmul_comm Nl D, scale_add_same, scale_mul]
  rw [hclear, hbound] at he
  rw [hclear', hbound] at he'
  have hpay := RCscale_mono (by decide : (0 : Q') ≤ 2)
    (RCscale_mono hd0 (mul_mono_right hNl hscale))
  have hpaid : RCscale 2 (RCscale delta ((RCscale 2 Nk) *ᵣ Nl)) =
      RCscale (4 * delta) (Nk *ᵣ Nl) := by
    rw [scale_mul, RCscale_RCscale, RCscale_RCscale]
    exact scale_congr (poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.const 2))
      (.mul (.const 4) (.var 0)) (by decide) (fun _ => delta)) _
  rw [hpaid] at hpay
  exact ⟨RCle_trans he hpay, RCle_trans he' hpay⟩

#print axioms twoSided
#print axioms twoSided_mul_right
#print axioms three_norm_projective_compare

end YMGap.Continuum.RCThreeNormProjectiveComparison
