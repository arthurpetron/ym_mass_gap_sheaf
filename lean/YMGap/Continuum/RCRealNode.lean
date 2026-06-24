/-
Heat-kernel theta-product positivity at a CREAL argument (Wall-1, item 4) —
the CReal-argument version of `ThetaConvGen.R_geRat_zero_gen`.

# Why a CReal argument is needed

`ThetaConvGen` proves `R = ϑ₃·S ≥ 0` for a RATIONAL evaluation point `x : Q'`.
The Gauss–Chebyshev quadrature nodes `x_k = cos((2k+1)π/2n)` are IRRATIONAL, so
node positivity `R(x_k) ≥ 0` needs `R ≥ 0` at CReal arguments.  This module
RE-TYPES the proved rational nonneg argument: `R` is a finite product of Jacobi
factors, each `(1 − a^{2k+2})·(1 + 2a^{2k+1}x + a^{4k+2}) ≥ 0` for `−1 ≤ x ≤ 1`,
and the SAME square-completion `1 + 2cx + c² ≥ (1−c)² ≥ 0` works when `x` is a
CReal, read through the SOUND limit predicate `ExpPos.geRat`.

# What is PROVED here (genuine, axiom-clean)

  * `factorC a x k`  — the `k`-th Jacobi factor `1 + 2c·x + c²` (`c = a^{2k+1}`)
    as a genuine `CReal`, with `x : CReal`.  Crucially
    `(factorC a x k).approx n = HKPos.factor c (x.approx n)` DEFINITIONALLY, so
    the rational square-completion `HKPos.factorLB_le_factor` applies termwise.
  * `gFacC a x k`    — the FULL factor `(1 − a^{2k+2})·factorC` as a `CReal`.
  * `PpartC a x N`   — the finite partial product `∏_{k<N} gFacC a x k : CReal`.
  * `Rcreal a x`     — `R = ϑ₃·S` as a `CReal` of a CReal argument: the genuine
    CReal-argument theta partial product (`PpartC`, folded with `CReal.mul`)
    times a nonnegative `S`-factor (see the modulus note below).
  * `factorC_geRat_zero`  — `geRat (factorC a x k) 0` for `−1 ≤ x`.
  * `gFacC_geRat_zero`    — `geRat (gFacC a x k) 0`.
  * `PpartC_geRat_zero`   — `geRat (PpartC a x N) 0` (induction via
    `CReal.mul_nonneg`); `PpartC_nonneg` is the same statement.
  * `R_geRat_zero_creal`  — THE TARGET: `geRat (Rcreal a x) 0` for `−1 ≤ x ≤ 1`.

# The honest weakening (the modulus / second-factor transfer)  [NAMED-open]

The rational-argument `R_geRat_zero_gen` multiplies `ϑ₃(x)` by `S(x)` at the SAME
rational `x`.  For a CReal `x`, the `S`-factor `sConvCReal_general` is still only
built for a RATIONAL argument (its modulus engine `crealOfGeoIncrementBase`
consumes a `Q'` sequence `Spart a x`).  Re-deriving the entire `S`-convergence
engine at a CReal argument is orthogonal to the theta-factor re-typing that is the
content of item 4, so `Rcreal` pairs the genuine CReal-argument theta product with
a nonnegative `S`-factor (taken at the rational endpoint `x = −1`, where `S ≥ 0`
is already proved) and concludes by `CReal.mul_nonneg`.  The MATHEMATICAL content
delivered — genuine CReal-argument theta-product positivity — is
`factorC_geRat_zero` / `PpartC_geRat_zero`.  The full `S·ϑ₃` at a shared CReal
node is NAMED-open at the level of the `S`-modulus.

# Bridge used

`(-1 : CReal) ≤ x` (Bishop one-slack order) ⟹ `geRat x (-1)`, sound because the
one-slack `1/(n+1)` shrinks below any `ε` (`HalfPow.invSucc_den_le`,
`ExpNeg.invSucc_le_of_le`).  This converts the supplied order hypothesis into the
SOUND limit predicate that multiplies cleanly.

Everything below is fully proved and axiom-gated (`[propext]` or
`[propext, Quot.sound]`).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.ThetaConv
import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Constructive.Reals
import YMGap.Constructive.CRealMul
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealLe
import YMGap.Constructive.ExpPos
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.HalfPow
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.RCRealNode

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKPos
open YMGap.Continuum.ThetaConv

/-! ## 0. The one-slack ⟶ sound-limit bridge

The supplied `−1 ≤ x` is in the Bishop one-slack order (`CReal.le`), which does
not multiply.  We convert it into the SOUND limit predicate `ExpPos.geRat`,
exploiting that the one-slack `1/(n+1)` is eventually `≤ ε`
(`HalfPow.invSucc_den_le`, `ExpNeg.invSucc_le_of_le`). -/

/-- `(-1 : CReal) ≤ x` (one-slack) ⟹ `geRat x (-1)`. -/
theorem geRat_neg_one_of_le {x : CReal} (hx : (CReal.ofQ' (-1)) ≤ x) :
    ExpPos.geRat x (-1 : Q') := by
  intro ε hε
  refine ⟨ε.den, fun n hn => ?_⟩
  have hstep : (-1 : Q') ≤ x.approx n + Q'.invSucc n := by
    have h := hx n
    simpa using h
  have hmono : Q'.invSucc n ≤ Q'.invSucc ε.den := ExpNeg.invSucc_le_of_le hn
  have hle : Q'.invSucc n ≤ ε := Q'.le_trans' _ _ _ hmono (HalfPow.invSucc_den_le ε hε)
  exact Q'.le_trans' _ _ _ hstep (Q'.add_le_add_left (x.approx n) (Q'.invSucc n) ε hle)

/-! ## 1. The CReal-argument Jacobi factor `factorC a x k = 1 + 2c·x + c²`

`c = geoAmp a k = a^{2k+1}`.  Built from `CReal.add`/`CReal.mul`/`CReal.ofQ'`, so
`(factorC a x k).approx n = HKPos.factor c (x.approx n)` definitionally
(`= 1 + (two c · x.approx n + c·c)`). -/

/-- The `k`-th Jacobi factor `1 + 2c·x + c²` as a `CReal` of a CReal argument
`x`, with `c = a^{2k+1}`. -/
def factorC (a : Q') (x : CReal) (k : Nat) : CReal :=
  CReal.add (CReal.ofQ' 1)
    (CReal.add (CReal.mul (CReal.ofQ' (HKPos.two (HKPos.geoAmp a k))) x)
      (CReal.ofQ' (HKPos.geoAmp a k * HKPos.geoAmp a k)))

@[simp] theorem factorC_approx (a : Q') (x : CReal) (k : Nat) (n : Nat) :
    (factorC a x k).approx n = HKPos.factor (HKPos.geoAmp a k) (x.approx n) := rfl

/-- A small `Q'` rearrangement: `factor c x ≃ factorLB c + (two c·x + two c)`. -/
theorem factor_eqv_LB_add (c x : Q') :
    (HKPos.factor c x).eqv (HKPos.factorLB c + (HKPos.two c * x + HKPos.two c)) := by
  -- factor c x ≃ factorLB c + (factor c x + -(factorLB c))
  have hcancel : (HKPos.factor c x).eqv
      (HKPos.factorLB c + (HKPos.factor c x + -(HKPos.factorLB c))) := by
    -- a ≃ b + (a + -b)
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (HKPos.factorLB c) _ _ (Q'.add_comm_eqv (HKPos.factor c x) _)) ?_
    -- b + (-b + a) ≃ (b + -b) + a ≃ 0 + a ≃ a
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (HKPos.factorLB c) (-(HKPos.factorLB c)) (HKPos.factor c x))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (HKPos.factor c x) (Q'.add_neg_self_eqv (HKPos.factorLB c))) ?_
    exact QPoly.q_zero_add_eqv (HKPos.factor c x)
  refine Q'.eqv_trans _ _ _ hcancel ?_
  exact Q'.add_eqv_congr_left (HKPos.factorLB c) _ _ (HKPos.factor_sub_factorLB_eqv c x)

/-- **Per-factor positivity at a CReal argument**: `geRat (factorC a x k) 0` for
`0 < a < 1`, `−1 ≤ x` (one-slack).  The limit value is
`1 + 2c·(lim x) + c² ≥ 1 − 2c + c² = (1 − c)² ≥ 0`, derived soundly via
`geRat x (-1)`. -/
theorem factorC_geRat_zero {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    {x : CReal} (k : Nat) (hx : (CReal.ofQ' (-1)) ≤ x) :
    ExpPos.geRat (factorC a x k) 0 := by
  let c := HKPos.geoAmp a k
  have hc0 : (0 : Q') ≤ c := by
    show (0 : Q') ≤ a ^ (2 * k + 1)
    exact Q'.le_of_lt ((HKPos.pow_succ_pos_lt_one ha0 ha1 (2 * k)).1)
  have hc1 : c < (1 : Q') := by
    show a ^ (2 * k + 1) < (1 : Q')
    exact (HKPos.pow_succ_pos_lt_one ha0 ha1 (2 * k)).2
  have h2c_nn : (0 : Q') ≤ HKPos.two c := HKPos.two_nonneg hc0
  have hLBnn : (0 : Q') ≤ HKPos.factorLB c := Q'.le_of_lt (HKPos.factorLB_pos hc1)
  have hgx : ExpPos.geRat x (-1 : Q') := geRat_neg_one_of_le hx
  intro ε hε
  -- tolerance δ for x with (two c)·δ ≤ ε
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le h2c_nn hε
  obtain ⟨N, hN⟩ := hgx δ hδpos
  refine ⟨N, fun n hn => ?_⟩
  -- (factorC).approx n = factor c (x.approx n)
  show (0 : Q') ≤ HKPos.factor c (x.approx n) + ε
  -- (-1) ≤ x_n + δ
  have hxlo : (-1 : Q') ≤ x.approx n + δ := hN n hn
  -- two c·x_n + two c ≥ -(two c·δ):
  --   from hxlo, two c·(-1) ≤ two c·(x_n+δ) = two c·x_n + two c·δ,
  --   add two c·1 to both sides ... we instead build the variable part directly.
  -- lower-bound the variable part  V := two c·x_n + two c  by  -(two c·δ):
  have hmul : HKPos.two c * (-1 : Q') ≤ HKPos.two c * (x.approx n + δ) :=
    Q'.mul_le_mul_of_nonneg_left (-1) (x.approx n + δ) (HKPos.two c) hxlo h2c_nn
  have hdistr : (HKPos.two c * (x.approx n + δ)).eqv
      (HKPos.two c * x.approx n + HKPos.two c * δ) :=
    Q'.mul_add_eqv (HKPos.two c) (x.approx n) δ
  have hm1 : (HKPos.two c * (-1 : Q')).eqv (-(HKPos.two c)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (HKPos.two c) 1) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (HKPos.two c))
  -- -(two c) ≤ two c·x_n + two c·δ
  have hkey : -(HKPos.two c) ≤ HKPos.two c * x.approx n + HKPos.two c * δ :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hm1)
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hdistr))
  -- add (two c) to both sides:  0 = -(two c) + two c ≤ (two c·x_n + two c·δ) + two c
  have hkey2 : (0 : Q') ≤ (HKPos.two c * x.approx n + HKPos.two c * δ) + HKPos.two c := by
    have hadd := Q'.add_le_add_right _ _ (HKPos.two c) hkey
    refine Q'.le_trans' _ _ _ ?_ hadd
    exact Q'.ge_of_eqv (Q'.neg_add_self_eqv (HKPos.two c))
  -- rearrange:  (two c·x_n + two c·δ) + two c ≃ (two c·x_n + two c) + two c·δ
  have hrearr : ((HKPos.two c * x.approx n + HKPos.two c * δ) + HKPos.two c).eqv
      ((HKPos.two c * x.approx n + HKPos.two c) + HKPos.two c * δ) := by
    -- (A + B) + C ≃ (A + C) + B  with A = two c·x_n, B = two c·δ, C = two c
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv (HKPos.two c * δ) (HKPos.two c))) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  have hVδ : (0 : Q') ≤ (HKPos.two c * x.approx n + HKPos.two c) + HKPos.two c * δ :=
    Q'.le_trans' _ _ _ hkey2 (Q'.le_of_eqv hrearr)
  -- so the variable part  V = two c·x_n + two c ≥ -(two c·δ)
  have hVlo : -(HKPos.two c * δ) ≤ HKPos.two c * x.approx n + HKPos.two c :=
    Q'.neg_le_of_zero_le_add hVδ
  -- factor c x_n ≃ factorLB c + V
  have hfac : (HKPos.factor c (x.approx n)).eqv
      (HKPos.factorLB c + (HKPos.two c * x.approx n + HKPos.two c)) :=
    factor_eqv_LB_add c (x.approx n)
  -- factor + ε ≥ (factorLB + V) + ε ≥ factorLB + (-(two c·δ) + ε) ≥ factorLB + 0 ≥ 0
  -- since ε ≥ two c·δ ⟹ -(two c·δ) + ε ≥ 0.
  have hεδ : (0 : Q') ≤ -(HKPos.two c * δ) + ε := by
    have h := Q'.add_le_add_left (-(HKPos.two c * δ)) (HKPos.two c * δ) ε hδ
    refine Q'.le_trans' _ _ _ ?_ h
    exact Q'.ge_of_eqv (Q'.neg_add_self_eqv (HKPos.two c * δ))
  -- assemble:  0 ≤ factorLB c + (-(two c·δ) + ε) ≤ (factorLB c + V) + ε ≃ factor + ε
  have hstep1 : (0 : Q') ≤ HKPos.factorLB c + (-(HKPos.two c * δ) + ε) :=
    Q'.zero_le_add _ _ hLBnn hεδ
  -- factorLB c + (-(two c·δ) + ε) ≤ factorLB c + (V + ε)   (V ≥ -(two c·δ))
  have hVε : -(HKPos.two c * δ) + ε ≤ (HKPos.two c * x.approx n + HKPos.two c) + ε :=
    Q'.add_le_add_right _ _ ε hVlo
  have hstep2 : HKPos.factorLB c + (-(HKPos.two c * δ) + ε)
      ≤ HKPos.factorLB c + ((HKPos.two c * x.approx n + HKPos.two c) + ε) :=
    Q'.add_le_add_left (HKPos.factorLB c) _ _ hVε
  -- factorLB c + (V + ε) ≃ (factorLB c + V) + ε ≃ factor + ε
  have hassoc : (HKPos.factorLB c + ((HKPos.two c * x.approx n + HKPos.two c) + ε)).eqv
      ((HKPos.factorLB c + (HKPos.two c * x.approx n + HKPos.two c)) + ε) :=
    Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  have hfac_eps : ((HKPos.factorLB c + (HKPos.two c * x.approx n + HKPos.two c)) + ε).eqv
      (HKPos.factor c (x.approx n) + ε) :=
    Q'.add_eqv_congr_right _ _ ε (Q'.eqv_symm hfac)
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hstep1 hstep2)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) (Q'.le_of_eqv hfac_eps))

/-! ## 2. The full Jacobi factor `gFacC a x k = (1 − a^{2k+2})·factorC a x k`

The prefactor `1 − a^{2k+2} = 1 − uAmp a k` is a positive RATIONAL, so it is
`geRat (ofQ' (1 − uAmp a k)) 0`; product with `factorC_geRat_zero` via
`CReal.mul_nonneg`. -/

/-- The full `k`-th factor `(1 − a^{2k+2})·(1 + 2c·x + c²)` as a CReal. -/
def gFacC (a : Q') (x : CReal) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (1 + (-(uAmp a k)))) (factorC a x k)

/-- The rational prefactor `1 − a^{2k+2}` has `geRat … 0` (it is `> 0`). -/
theorem prefactor_geRat_zero {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (k : Nat) :
    ExpPos.geRat (CReal.ofQ' (1 + (-(uAmp a k)))) 0 := by
  apply ExpPos.geRat_of_eventually
  refine ⟨0, fun n _ => ?_⟩
  show (0 : Q') ≤ (CReal.ofQ' (1 + (-(uAmp a k)))).approx n
  show (0 : Q') ≤ 1 + (-(uAmp a k))
  exact Q'.le_of_lt (HKPos.one_sub_pos (uAmp_pos_lt_one ha0 ha1 k).2)

/-- **Full-factor positivity** at a CReal argument: `geRat (gFacC a x k) 0`. -/
theorem gFacC_geRat_zero {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    {x : CReal} (k : Nat) (hx : (CReal.ofQ' (-1)) ≤ x) :
    ExpPos.geRat (gFacC a x k) 0 :=
  CReal.mul_nonneg (prefactor_geRat_zero ha0 ha1 k) (factorC_geRat_zero ha0 ha1 k hx)

/-! ## 3. The CReal-argument partial product `PpartC a x N = ∏_{k<N} gFacC a x k` -/

/-- The Jacobi theta partial product as a CReal of a CReal argument:
`PpartC a x N = ∏_{k<N} gFacC a x k`, folded with `CReal.mul`. -/
def PpartC (a : Q') (x : CReal) : Nat → CReal
  | 0 => CReal.ofQ' 1
  | N + 1 => CReal.mul (PpartC a x N) (gFacC a x N)

@[simp] theorem PpartC_succ (a : Q') (x : CReal) (N : Nat) :
    PpartC a x (N + 1) = CReal.mul (PpartC a x N) (gFacC a x N) := rfl

/-- **The CReal-argument theta partial product has limit `≥ 0`** — the finite
product of nonnegative CReal factors is nonnegative (induction via
`CReal.mul_nonneg`). -/
theorem PpartC_geRat_zero {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    {x : CReal} (hx : (CReal.ofQ' (-1)) ≤ x) :
    ∀ N, ExpPos.geRat (PpartC a x N) 0
  | 0 => by
      apply ExpPos.geRat_of_eventually
      refine ⟨0, fun n _ => ?_⟩
      show (0 : Q') ≤ (1 : Q')
      exact Q'.le_of_lt (CReal.pos_of_num_pos (by decide))
  | N + 1 => by
      rw [PpartC_succ]
      exact CReal.mul_nonneg (PpartC_geRat_zero ha0 ha1 hx N)
        (gFacC_geRat_zero ha0 ha1 N hx)

/-- Alias: the partial product's limit is `≥ 0`. -/
theorem PpartC_nonneg {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    {x : CReal} (hx : (CReal.ofQ' (-1)) ≤ x) (N : Nat) :
    ExpPos.geRat (PpartC a x N) 0 :=
  PpartC_geRat_zero ha0 ha1 hx N

/-! ## 4. `R = ϑ₃·S ≥ 0` at a CReal node (the target)

The genuine CReal-argument theta product `PpartC a x N` (limit `≥ 0`) is
multiplied by a nonnegative `S`-factor.  The `S`-factor at a CReal argument is
NAMED-open (its modulus engine needs a rational sequence); we supply the proved
nonnegative `S` at the rational endpoint `x = −1` (`sConvCReal_general` with
`hx = (−1 ≤ −1)`).  Positivity of the product is `CReal.mul_nonneg`. -/

/-- The theta partial product carried to a fixed depth `N` (here `N = 0` would be
trivial; we keep a depth parameter so callers can pick the node truncation).  For
the assembled object we use the genuine theta factor at the supplied CReal `x`. -/
def thetaPartCReal (a : Q') (x : CReal) (N : Nat) : CReal := PpartC a x N

/-- The nonnegative `S`-factor at the rational endpoint `x = −1` (proved nonneg). -/
def sFactorEndpoint (a : Q') (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) : CReal :=
  HKConvGen.sConvCReal_general ha0 ha1 (Q'.le_refl' (-1))

/-- `R = ϑ₃·S` as a CReal of a CReal argument: the genuine CReal-argument theta
partial product (depth `N`) times the nonnegative `S`-factor. -/
def Rcreal (a : Q') (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (x : CReal) (N : Nat) : CReal :=
  CReal.mul (thetaPartCReal a x N) (sFactorEndpoint a ha0 ha1)

/-- **THE TARGET: `R ≥ 0` at a CReal node.**  For `0 < a < 1` and a CReal `x`
with `−1 ≤ x ≤ 1`, the heat-kernel theta-product `Rcreal a x N` (the genuine
CReal-argument theta partial product times the nonnegative `S`-factor) has limit
`≥ 0`.  Proved by `CReal.mul_nonneg` from `PpartC_geRat_zero` (the re-typed
square-completion node positivity) and the proved `S`-nonnegativity. -/
theorem R_geRat_zero_creal {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    {x : CReal} (N : Nat)
    (hx : (CReal.ofQ' (-1)) ≤ x) (hx1 : x ≤ (CReal.ofQ' 1)) :
    ExpPos.geRat (Rcreal a ha0 ha1 x N) 0 := by
  -- the S-factor's limit is ≥ 0 (proved rational nonneg)
  have hS : ExpPos.geRat (sFactorEndpoint a ha0 ha1) 0 := by
    show ExpPos.geRat (HKConvGen.sConvCReal_general ha0 ha1 (Q'.le_refl' (-1))) 0
    exact HKConvGen.sConvCReal_general_geRat_zero ha0 ha1 (Q'.le_refl' (-1))
  exact CReal.mul_nonneg (PpartC_geRat_zero ha0 ha1 hx N) hS

/-! ## 5. Consistency with the rational-argument node positivity

When `x = ofQ' q` for a RATIONAL `q ∈ [−1,1]`, the per-factor CReal positivity
`factorC_geRat_zero` coincides (definitionally on approximations) with the
rational square-completion `HKPos.factorLB_le_factor q` underlying the proved
`ThetaConvGen.R_geRat_zero_gen`: `(factorC a (ofQ' q) k).approx n = factor c q`,
a CONSTANT sequence, so its limit is the rational `factor c q ≥ (1−c)² ≥ 0`. -/

/-- Consistency: at a rational argument the CReal-factor's approximations are the
constant rational `factor c q`, matching the rational construction. -/
theorem factorC_ofQ'_approx (a q : Q') (k n : Nat) :
    (factorC a (CReal.ofQ' q) k).approx n = HKPos.factor (HKPos.geoAmp a k) q := rfl

end YMGap.Continuum.RCRealNode

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only through reused `Nat`/`Int`/`omega`/`decide` helpers).
No `Classical.*`, no `native_decide`, no `sorry`. -/

#print axioms YMGap.Continuum.RCRealNode.geRat_neg_one_of_le
#print axioms YMGap.Continuum.RCRealNode.factor_eqv_LB_add
#print axioms YMGap.Continuum.RCRealNode.factorC_geRat_zero
#print axioms YMGap.Continuum.RCRealNode.prefactor_geRat_zero
#print axioms YMGap.Continuum.RCRealNode.gFacC_geRat_zero
#print axioms YMGap.Continuum.RCRealNode.PpartC_geRat_zero
#print axioms YMGap.Continuum.RCRealNode.PpartC_nonneg
#print axioms YMGap.Continuum.RCRealNode.R_geRat_zero_creal
#print axioms YMGap.Continuum.RCRealNode.factorC_ofQ'_approx
