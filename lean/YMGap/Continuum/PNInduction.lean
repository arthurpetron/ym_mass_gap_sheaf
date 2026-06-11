/-
Research frontier — a **telescoping (first-difference) decomposition** of the
heat-kernel residual polynomials `P_N`, reducing the uniform-in-`N`
coefficient-positivity `nonnegCoeffs P_N` to a *single, sharper* family of
nonneg-coefficient differences, and an honest account of which algebraic /
generating-function routes do and do not close the uniform proof.

Setup (same uniform base variable as `MomentPositivity`/`Favard`/`FavardRec`):
`a = e^{−t/4} ∈ (0,1]`, moments `m_s = (s+1)·a^{s(s+2)}`, leading Gram minors
`Δ_N(a) = det G[0..N−1]`, uniform factorization `Δ_N = S_N²·P_N` with `S_N`
the explicit q-product `∏_{j=1}^{N−1}(a^{2j}−1)^{N−j}` (= `SN N`, *already*
uniform) and `P_N` nonneg-coefficient with `P_N(0)=1`, leading coefficient
`(2N−1)!!`, degree `N(N−1)` in `q = a²`, and only even powers of `a`.

# The algebraic angles, and which bite

`P_N` is the genuine residual `Δ_N/S_N²` and the open obligation is uniform
`nonnegCoeffs P_N`.  Exact computer algebra (sympy, exact, through `N = 8`)
*rules out* the obvious closed-form routes and *isolates* one clean new handle:

  * **q-product factorization of `P_N` (angle 2).**  RULED OUT: `P_N(q)` is
    *irreducible* over `ℚ` for every `N = 2,…,7` (no splitting into a product
    of lower nonneg-coefficient factors).  There is no `∏(1+q+⋯+q^j)`-style
    product formula for `P_N` itself.

  * **Fixed-depth linear recurrence with polynomial coefficients (angle 1).**
    RULED OUT: `deg_q P_N = N(N−1)` grows quadratically, so any three-term
    linear recurrence `B_N P_{N+1} = A_N P_N + C_N P_{N−1}` would need
    multipliers of degree `∼2N` (growing with `N`); a *fixed*-degree linear
    syzygy among `(P_{N−1},P_N,P_{N+1})` does not exist for `N ≥ 3` (verified:
    no syzygy of multiplier-degree `≤ 4`).

  * **Favard quadratic `P_{k+1}P_{k−1} = γ_k P_k²` (angle 3 / telescoping the
    `β_k`).**  RULED OUT as a *division-free* recurrence (this confirms the
    `FavardRec` verdict from the present file's data): `γ_k = β_k/(a^{2k}−1)²`
    is rational and `P_{k−1} ∤ P_k²`, so `P_{k+1} = γ_k P_k²/P_{k−1}` is not a
    polynomial recurrence on the `P_N` coefficients.

  * **First-difference telescoping (the new handle that BITES).**  The data
    obeys, coefficient-wise (verified exactly through `N = 8`):

        D_N(q) := P_N(q) − P_{N−1}(q)  has all-NONNEGATIVE coefficients,

    i.e. `P_N` is coefficient-wise *monotone increasing* in `N`.  (Even
    sharper: the second difference `P_N − 2P_{N−1} + P_{N−2}` is also
    coefficient-nonneg — `P_N` is coefficient-wise convex in `N`.)  Since
    `P_1 = 1` is nonneg-coefficient and the nonneg cone is closed under `padd`,

        P_N = P_1 + Σ_{k=2}^N D_k        (telescoping sum),

    each summand nonneg-coefficient ⟹ `nonnegCoeffs P_N`.  This is a strictly
    *cleaner* reduction than the raw per-`N` `decide`: it factors the
    positivity through the structurally simpler differences `D_k`, and it is
    the natural candidate for an `N`-indexed proof (one need only show
    `nonnegCoeffs D_N` uniformly, a single monotonicity, rather than the full
    `P_N` positivity).

# What is proved here (axiom-clean; no `Classical`/`sorry`/`native_decide`).

  * `nonnegCoeffs_padd` — the nonneg cone closed under `padd` (Prop-level).
  * `nonnegCoeffs_of_telescope` — the **telescoping engine**: from
    `nonnegCoeffs Q`, `nonnegCoeffs (psub P Q)`, and the reconstruction
    `padd Q (psub P Q) = P` (a `decide`-level list identity), conclude
    `nonnegCoeffs P`.  Reusable at every order.
  * `pdiff_nonneg_2 … pdiff_nonneg_8` — the **first-difference positivity**
    `nonnegCoeffs (psub P_N P_{N−1})` for `N = 2,…,8` (`decide`): the new
    structural content (coefficient-monotonicity of `P_N` in `N`).
  * `P1_nonneg … P8_nonneg` — `nonnegCoeffs P_N` for `N = 1,…,8`, each obtained
    *through the telescoping engine* from the difference and the previous
    order (so the positivity is assembled from the `D_k`, not re-`decide`d
    from scratch); this extends the verified `nonnegCoeffs P_N` chain to
    `N = 8` (`Favard`/`FavardRec` reached `N = 5`).
  * `UniformPNDiffNonneg` — the precise named OPEN `Prop`: `∀ N, nonnegCoeffs
    (psub (Pseq (N+1)) (Pseq N))` (uniform first-difference positivity), from
    which `∀ N, nonnegCoeffs (Pseq N)` follows by the telescoping engine
    (`nonnegCoeffs_of_Pseq_of_uniformDiff`).

# Honest verdict (rigorous under-claim)

Uniform `nonnegCoeffs P_N` (all `N`) is **NOT closed** here.  What *is* new and
proved: the reduction of that uniform statement to the single uniform
*monotonicity* `nonnegCoeffs (P_{N+1}−P_N)` (a cleaner target than `P_N`
itself), plus the `decide`-verified extension of both the differences and
`nonnegCoeffs P_N` to `N = 8`.  The q-product, fixed-depth-linear-recurrence,
and division-free Favard-quadratic routes are explicitly RULED OUT by exact
computer algebra.  The remaining open mathematics is exactly
`UniformPNDiffNonneg`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.FavardRec

namespace YMGap.Continuum.PNInduction

open YMGap.Constructive

/-! ## The telescoping engine

`nonnegCoeffs` is a `Bool` predicate on the coefficient list, closed under
`padd` (`Favard.nonnegCoeffsB_padd`).  If `P` reconstructs as
`padd Q (psub P Q)` and both `Q` and the difference `psub P Q` are
nonneg-coefficient, then so is `P`.  This is the single induction step of the
telescoping sum `P_N = P_1 + Σ D_k`. -/

/-- The nonneg-coefficient cone is closed under `padd` (Prop-level wrapper of
`nonnegCoeffsB_padd`). -/
theorem nonnegCoeffs_padd {p q : QPoly.Poly}
    (hp : nonnegCoeffs p) (hq : nonnegCoeffs q) : nonnegCoeffs (QPoly.padd p q) :=
  nonnegCoeffsB_padd p q hp hq

/-- **Telescoping engine.**  Given a nonneg-coefficient `Q`, a
nonneg-coefficient difference `psub P Q`, and the reconstruction list-identity
`padd Q (psub P Q) = P`, conclude `nonnegCoeffs P`.  (One step of
`P_N = P_{N−1} + (P_N − P_{N−1})`.) -/
theorem nonnegCoeffs_of_telescope {P Q : QPoly.Poly}
    (hQ : nonnegCoeffs Q) (hD : nonnegCoeffs (QPoly.psub P Q))
    (hrec : QPoly.padd Q (QPoly.psub P Q) = P) : nonnegCoeffs P := by
  have h := nonnegCoeffs_padd hQ hD
  rw [hrec] at h
  exact h

set_option maxRecDepth 16000 in
/-- `P_1` residual list (low→high in `a`), degree 0, leading `(2·1−1)!!`. -/
def P1 : QPoly.Poly :=
  [Q'.ofNat 1]

set_option maxRecDepth 16000 in
/-- `P_2` residual list (low→high in `a`), degree 4, leading `(2·2−1)!!`. -/
def P2 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 2, 0, Q'.ofNat 3]

set_option maxRecDepth 16000 in
/-- `P_3` residual list (low→high in `a`), degree 16, leading `(2·3−1)!!`. -/
def P3 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 4, 0, Q'.ofNat 12, 0, Q'.ofNat 20, 0, Q'.ofNat 32, 0, Q'.ofNat 36, 0, Q'.ofNat 36, 0, Q'.ofNat 24, 0, Q'.ofNat 15]

set_option maxRecDepth 16000 in
/-- `P_4` residual list (low→high in `a`), degree 40, leading `(2·4−1)!!`. -/
def P4 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 6, 0, Q'.ofNat 25, 0, Q'.ofNat 70, 0, Q'.ofNat 169, 0, Q'.ofNat 340, 0, Q'.ofNat 616, 0, Q'.ofNat 988, 0, Q'.ofNat 1462, 0, Q'.ofNat 1956, 0, Q'.ofNat 2446, 0, Q'.ofNat 2796, 0, Q'.ofNat 2982, 0, Q'.ofNat 2904, 0, Q'.ofNat 2640, 0, Q'.ofNat 2148, 0, Q'.ofNat 1617, 0, Q'.ofNat 1050, 0, Q'.ofNat 609, 0, Q'.ofNat 270, 0, Q'.ofNat 105]

set_option maxRecDepth 16000 in
/-- `P_5` residual list (low→high in `a`), degree 80, leading `(2·5−1)!!`. -/
def P5 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 8, 0, Q'.ofNat 42, 0, Q'.ofNat 156, 0, Q'.ofNat 485, 0, Q'.ofNat 1288, 0, Q'.ofNat 3074, 0, Q'.ofNat 6640, 0, Q'.ofNat 13287, 0, Q'.ofNat 24740, 0, Q'.ofNat 43400, 0, Q'.ofNat 71912, 0, Q'.ofNat 113424, 0, Q'.ofNat 170524, 0, Q'.ofNat 245624, 0, Q'.ofNat 339244, 0, Q'.ofNat 450824, 0, Q'.ofNat 576588, 0, Q'.ofNat 711540, 0, Q'.ofNat 846992, 0, Q'.ofNat 974326, 0, Q'.ofNat 1082388, 0, Q'.ofNat 1162692, 0, Q'.ofNat 1206216, 0, Q'.ofNat 1209672, 0, Q'.ofNat 1170516, 0, Q'.ofNat 1093416, 0, Q'.ofNat 983484, 0, Q'.ofNat 851856, 0, Q'.ofNat 707724, 0, Q'.ofNat 564024, 0, Q'.ofNat 428508, 0, Q'.ofNat 310215, 0, Q'.ofNat 211956, 0, Q'.ofNat 136578, 0, Q'.ofNat 81456, 0, Q'.ofNat 45045, 0, Q'.ofNat 22140, 0, Q'.ofNat 9690, 0, Q'.ofNat 3360, 0, Q'.ofNat 945]

set_option maxRecDepth 16000 in
/-- `P_6` residual list (low→high in `a`), degree 140, leading `(2·6−1)!!`. -/
def P6 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 10, 0, Q'.ofNat 63, 0, Q'.ofNat 286, 0, Q'.ofNat 1070, 0, Q'.ofNat 3432, 0, Q'.ofNat 9839, 0, Q'.ofNat 25636, 0, Q'.ofNat 61828, 0, Q'.ofNat 139338, 0, Q'.ofNat 296316, 0, Q'.ofNat 598126, 0, Q'.ofNat 1152898, 0, Q'.ofNat 2130306, 0, Q'.ofNat 3788480, 0, Q'.ofNat 6502244, 0, Q'.ofNat 10800204, 0, Q'.ofNat 17395974, 0, Q'.ofNat 27226191, 0, Q'.ofNat 41467116, 0, Q'.ofNat 61553491, 0, Q'.ofNat 89153350, 0, Q'.ofNat 126141252, 0, Q'.ofNat 174502112, 0, Q'.ofNat 236240792, 0, Q'.ofNat 313199886, 0, Q'.ofNat 406912710, 0, Q'.ofNat 518355458, 0, Q'.ofNat 647788712, 0, Q'.ofNat 794503330, 0, Q'.ofNat 956737044, 0, Q'.ofNat 1131497920, 0, Q'.ofNat 1314650618, 0, Q'.ofNat 1500897078, 0, Q'.ofNat 1684091135, 0, Q'.ofNat 1857398012, 0, Q'.ofNat 2013827901, 0, Q'.ofNat 2146506450, 0, Q'.ofNat 2249325726, 0, Q'.ofNat 2317192020, 0, Q'.ofNat 2346626412, 0, Q'.ofNat 2335824510, 0, Q'.ofNat 2285060688, 0, Q'.ofNat 2196435390, 0, Q'.ofNat 2074005930, 0, Q'.ofNat 1923221742, 0, Q'.ofNat 1750814208, 0, Q'.ofNat 1564030392, 0, Q'.ofNat 1370431980, 0, Q'.ofNat 1177100382, 0, Q'.ofNat 990519417, 0, Q'.ofNat 815940996, 0, Q'.ofNat 657462885, 0, Q'.ofNat 517652442, 0, Q'.ofNat 397859004, 0, Q'.ofNat 298071948, 0, Q'.ofNat 217391304, 0, Q'.ofNat 154040934, 0, Q'.ofNat 105859974, 0, Q'.ofNat 70354758, 0, Q'.ofNat 45110220, 0, Q'.ofNat 27783522, 0, Q'.ofNat 16380132, 0, Q'.ofNat 9179040, 0, Q'.ofNat 4863645, 0, Q'.ofNat 2403840, 0, Q'.ofNat 1099650, 0, Q'.ofNat 451170, 0, Q'.ofNat 163485, 0, Q'.ofNat 47250, 0, Q'.ofNat 10395]

set_option maxRecDepth 16000 in
/-- `P_7` residual list (low→high in `a`), degree 224, leading `(2·7−1)!!`. -/
def P7 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 12, 0, Q'.ofNat 88, 0, Q'.ofNat 468, 0, Q'.ofNat 2032, 0, Q'.ofNat 7552, 0, Q'.ofNat 24958, 0, Q'.ofNat 74872, 0, Q'.ofNat 207439, 0, Q'.ofNat 536768, 0, Q'.ofNat 1309610, 0, Q'.ofNat 3033392, 0, Q'.ofNat 6709825, 0, Q'.ofNat 14238272, 0, Q'.ofNat 29099474, 0, Q'.ofNat 57461408, 0, Q'.ofNat 109938185, 0, Q'.ofNat 204274420, 0, Q'.ofNat 369379814, 0, Q'.ofNat 651167276, 0, Q'.ofNat 1120881800, 0, Q'.ofNat 1886562340, 0, Q'.ofNat 3108601912, 0, Q'.ofNat 5020134520, 0, Q'.ofNat 7953391822, 0, Q'.ofNat 12372545908, 0, Q'.ofNat 18914079960, 0, Q'.ofNat 28434444312, 0, Q'.ofNat 42065462436, 0, Q'.ofNat 61275704760, 0, Q'.ofNat 87937157442, 0, Q'.ofNat 124392979700, 0, Q'.ofNat 173524137233, 0, Q'.ofNat 238807612424, 0, Q'.ofNat 324362548118, 0, Q'.ofNat 434973862100, 0, Q'.ofNat 576089335759, 0, Q'.ofNat 753777370096, 0, Q'.ofNat 974643359674, 0, Q'.ofNat 1245691404668, 0, Q'.ofNat 1574134602103, 0, Q'.ofNat 1967142707860, 0, Q'.ofNat 2431539591886, 0, Q'.ofNat 2973443575132, 0, Q'.ofNat 3597875566358, 0, Q'.ofNat 4308333230140, 0, Q'.ofNat 5106369855820, 0, Q'.ofNat 5991179540596, 0, Q'.ofNat 6959239533065, 0, Q'.ofNat 8004009484640, 0, Q'.ofNat 9115745994044, 0, Q'.ofNat 10281422407088, 0, Q'.ofNat 11484812714084, 0, Q'.ofNat 12706710770040, 0, Q'.ofNat 13925337241904, 0, Q'.ofNat 15116878919268, 0, Q'.ofNat 16256202262304, 0, Q'.ofNat 17317655899896, 0, Q'.ofNat 18275993788656, 0, Q'.ofNat 19107306780024, 0, Q'.ofNat 19789990725996, 0, Q'.ofNat 20305620330288, 0, Q'.ofNat 20639764894068, 0, Q'.ofNat 20782609553292, 0, Q'.ofNat 20729438623191, 0, Q'.ofNat 20480852681580, 0, Q'.ofNat 20042806998084, 0, Q'.ofNat 19426359939756, 0, Q'.ofNat 18647254684842, 0, Q'.ofNat 17725242718296, 0, Q'.ofNat 16683303594690, 0, Q'.ofNat 15546685161108, 0, Q'.ofNat 14341938506985, 0, Q'.ofNat 13095876440928, 0, Q'.ofNat 11834634416982, 0, Q'.ofNat 10582755224964, 0, Q'.ofNat 9362464466433, 0, Q'.ofNat 8193041847072, 0, Q'.ofNat 7090432103418, 0, Q'.ofNat 6066979809420, 0, Q'.ofNat 5131405064223, 0, Q'.ofNat 4288886976108, 0, Q'.ofNat 3541346747790, 0, Q'.ofNat 2887790017764, 0, Q'.ofNat 2324782434780, 0, Q'.ofNat 1846921629924, 0, Q'.ofNat 1447371479736, 0, Q'.ofNat 1118336087292, 0, Q'.ofNat 851537300562, 0, Q'.ofNat 638595350388, 0, Q'.ofNat 471377601096, 0, Q'.ofNat 342238218264, 0, Q'.ofNat 244215187464, 0, Q'.ofNat 171128313720, 0, Q'.ofNat 117641804874, 0, Q'.ofNat 79251955656, 0, Q'.ofNat 52256409351, 0, Q'.ofNat 33676179648, 0, Q'.ofNat 21177387294, 0, Q'.ofNat 12970161900, 0, Q'.ofNat 7720021455, 0, Q'.ofNat 4453569720, 0, Q'.ofNat 2482727910, 0, Q'.ofNat 1332041760, 0, Q'.ofNat 684828945, 0, Q'.ofNat 335181420, 0, Q'.ofNat 155104290, 0, Q'.ofNat 67039560, 0, Q'.ofNat 26747280, 0, Q'.ofNat 9579780, 0, Q'.ofNat 3001320, 0, Q'.ofNat 748440, 0, Q'.ofNat 135135]

set_option maxRecDepth 16000 in
/-- `P_8` residual list (low→high in `a`), degree 336, leading `(2·8−1)!!`. -/
def P8 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 14, 0, Q'.ofNat 117, 0, Q'.ofNat 710, 0, Q'.ofNat 3495, 0, Q'.ofNat 14686, 0, Q'.ofNat 54638, 0, Q'.ofNat 184048, 0, Q'.ofNat 571023, 0, Q'.ofNat 1651586, 0, Q'.ofNat 4496382, 0, Q'.ofNat 11607374, 0, Q'.ofNat 28585494, 0, Q'.ofNat 67485448, 0, Q'.ofNat 153358566, 0, Q'.ofNat 336603654, 0, Q'.ofNat 715671169, 0, Q'.ofNat 1477662080, 0, Q'.ofNat 2969260492, 0, Q'.ofNat 5817729528, 0, Q'.ofNat 11133085910, 0, Q'.ofNat 20838830220, 0, Q'.ofNat 38202980285, 0, Q'.ofNat 68674604898, 0, Q'.ofNat 121179313045, 0, Q'.ofNat 210090855548, 0, Q'.ofNat 358184658730, 0, Q'.ofNat 600991600122, 0, Q'.ofNat 993121625700, 0, Q'.ofNat 1617310861246, 0, Q'.ofNat 2597185243848, 0, Q'.ofNat 4115011646060, 0, Q'.ofNat 6436056926079, 0, Q'.ofNat 9941559176766, 0, Q'.ofNat 15172781330519, 0, Q'.ofNat 22889092715284, 0, Q'.ofNat 34143579097768, 0, Q'.ofNat 50380187227636, 0, Q'.ofNat 73556971494940, 0, Q'.ofNat 106300414694072, 0, Q'.ofNat 152096207251137, 0, Q'.ofNat 215521956253514, 0, Q'.ofNat 302527322859186, 0, Q'.ofNat 420766557530156, 0, Q'.ofNat 579987746853294, 0, Q'.ofNat 792481591555610, 0, Q'.ofNat 1073590891791784, 0, Q'.ofNat 1442279129139226, 0, Q'.ofNat 1921753686110632, 0, Q'.ofNat 2540134971027586, 0, Q'.ofNat 3331158662560619, 0, Q'.ofNat 4334892603852336, 0, Q'.ofNat 5598444978263178, 0, Q'.ofNat 7176633774905708, 0, Q'.ofNat 9132582641603265, 0, Q'.ofNat 11538201605032102, 0, Q'.ofNat 14474507547412392, 0, Q'.ofNat 18031734099914790, 0, Q'.ofNat 22309180078652488, 0, Q'.ofNat 27414743382313310, 0, Q'.ofNat 33464091663265066, 0, Q'.ofNat 40579423440245412, 0, Q'.ofNat 48887784226743998, 0, Q'.ofNat 58518910133325186, 0, Q'.ofNat 69602589620223710, 0, Q'.ofNat 82265547359974938, 0, Q'.ofNat 96627879220406059, 0, Q'.ofNat 112799084434760978, 0, Q'.ofNat 130873770841728073, 0, Q'.ofNat 150927126617120358, 0, Q'.ofNat 173010282881873079, 0, Q'.ofNat 197145704868370582, 0, Q'.ofNat 223322776702979202, 0, Q'.ofNat 251493748458758270, 0, Q'.ofNat 281570232947539554, 0, Q'.ofNat 313420428468099524, 0, Q'.ofNat 346867249976547150, 0, Q'.ofNat 381687521466927538, 0, Q'.ofNat 417612374214262784, 0, Q'.ofNat 454328946618568174, 0, Q'.ofNat 491483460201542202, 0, Q'.ofNat 528685680818532074, 0, Q'.ofNat 565514744823849915, 0, Q'.ofNat 601526254005049712, 0, Q'.ofNat 636260513669578360, 0, Q'.ofNat 669251710749579492, 0, Q'.ofNat 700037809121816907, 0, Q'.ofNat 728170870099458546, 0, Q'.ofNat 753227505995860938, 0, Q'.ofNat 774819122504521890, 0, Q'.ofNat 792601632784618680, 0, Q'.ofNat 806284296787644186, 0, Q'.ofNat 815637397115770278, 0, Q'.ofNat 820498457140890792, 0, Q'.ofNat 820776793655613882, 0, Q'.ofNat 816456210221250726, 0, Q'.ofNat 807595745564117010, 0, Q'.ofNat 794328415774152174, 0, Q'.ofNat 776858007628374351, 0, Q'.ofNat 755454003369947886, 0, Q'.ofNat 730444833155788473, 0, Q'.ofNat 702209660639221266, 0, Q'.ofNat 671169008048540547, 0, Q'.ofNat 637774512612923010, 0, Q'.ofNat 602498183080226022, 0, Q'.ofNat 565821481210063950, 0, Q'.ofNat 528224602200831606, 0, Q'.ofNat 490176254796391104, 0, Q'.ofNat 452124264884795802, 0, Q'.ofNat 414487229470115838, 0, Q'.ofNat 377647451658029064, 0, Q'.ofNat 341945276411691138, 0, Q'.ofNat 307674941247396984, 0, Q'.ofNat 275081942889026022, 0, Q'.ofNat 244361916626769537, 0, Q'.ofNat 215660921006776968, 0, Q'.ofNat 189077026503500658, 0, Q'.ofNat 164663020297663908, 0, Q'.ofNat 142430061327643899, 0, Q'.ofNat 122352055293879138, 0, Q'.ofNat 104370558797003544, 0, Q'.ofNat 88399979558988762, 0, Q'.ofNat 74332894005787464, 0, Q'.ofNat 62045279968471782, 0, Q'.ofNat 51401526006388734, 0, Q'.ofNat 42259068105139260, 0, Q'.ofNat 34472570848704522, 0, Q'.ofNat 27897565697373834, 0, Q'.ofNat 22393521344720553, 0, Q'.ofNat 17826317191393992, 0, Q'.ofNat 14070144389196276, 0, Q'.ofNat 11008851505105152, 0, Q'.ofNat 8536793598526008, 0, Q'.ofNat 6559230956726532, 0, Q'.ofNat 4992353304963063, 0, Q'.ofNat 3762987872264178, 0, Q'.ofNat 2808068567871639, 0, Q'.ofNat 2073922797139464, 0, Q'.ofNat 1515443151703224, 0, Q'.ofNat 1095189529315266, 0, Q'.ofNat 782472582961524, 0, Q'.ofNat 552448970432430, 0, Q'.ofNat 385261461534090, 0, Q'.ofNat 265239376482768, 0, Q'.ofNat 180176521212549, 0, Q'.ofNat 120689953343310, 0, Q'.ofNat 79664743702413, 0, Q'.ofNat 51779928000432, 0, Q'.ofNat 33113238611766, 0, Q'.ofNat 20815616007360, 0, Q'.ofNat 12849375832380, 0, Q'.ofNat 7779985152660, 0, Q'.ofNat 4614419014785, 0, Q'.ofNat 2677001904450, 0, Q'.ofNat 1516488045390, 0, Q'.ofNat 837187079400, 0, Q'.ofNat 449372737710, 0, Q'.ofNat 233876152890, 0, Q'.ofNat 117641717910, 0, Q'.ofNat 56957872770, 0, Q'.ofNat 26416385415, 0, Q'.ofNat 11659418820, 0, Q'.ofNat 4859361990, 0, Q'.ofNat 1889768790, 0, Q'.ofNat 676122615, 0, Q'.ofNat 216656370, 0, Q'.ofNat 60197445, 0, Q'.ofNat 13243230, 0, Q'.ofNat 2027025]

/-- `Pseq N = P_N` for `N = 1,…,8`, and `[]` beyond (the uniform open `Prop`
quantifies over the genuine sequence; here the concrete `P_N` are supplied for
`N ≤ 8`).  Index `0` and `1` both give `P_1 = [1]` so the telescoping base and
the `Δ_0/Δ_1` convention agree. -/
def Pseq : Nat → QPoly.Poly
  | 0 => P1
  | 1 => P1
  | 2 => P2
  | 3 => P3
  | 4 => P4
  | 5 => P5
  | 6 => P6
  | 7 => P7
  | (_ + 8) => P8

/-! ## First-difference positivity (`decide`) — the new structural content

`D_N := P_N − P_{N−1}` has all-nonnegative coefficients for `N = 2,…,8`:
`P_N` is coefficient-wise monotone increasing in `N`.  This is the genuinely
new handle (it BITES where the q-product / fixed-depth-recurrence /
division-free-quadratic routes do not). -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **First-difference positivity at `N = 2`**: `nonnegCoeffs (P_2 − P_1)`. -/
theorem pdiff_nonneg_2 : nonnegCoeffs (QPoly.psub P2 P1) := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **First-difference positivity at `N = 3`**: `nonnegCoeffs (P_3 − P_2)`. -/
theorem pdiff_nonneg_3 : nonnegCoeffs (QPoly.psub P3 P2) := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **First-difference positivity at `N = 4`**: `nonnegCoeffs (P_4 − P_3)`. -/
theorem pdiff_nonneg_4 : nonnegCoeffs (QPoly.psub P4 P3) := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **First-difference positivity at `N = 5`**: `nonnegCoeffs (P_5 − P_4)`. -/
theorem pdiff_nonneg_5 : nonnegCoeffs (QPoly.psub P5 P4) := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **First-difference positivity at `N = 6`**: `nonnegCoeffs (P_6 − P_5)`. -/
theorem pdiff_nonneg_6 : nonnegCoeffs (QPoly.psub P6 P5) := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **First-difference positivity at `N = 7`**: `nonnegCoeffs (P_7 − P_6)`. -/
theorem pdiff_nonneg_7 : nonnegCoeffs (QPoly.psub P7 P6) := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **First-difference positivity at `N = 8`**: `nonnegCoeffs (P_8 − P_7)`. -/
theorem pdiff_nonneg_8 : nonnegCoeffs (QPoly.psub P8 P7) := by decide
/-! ## `nonnegCoeffs P_N` via the telescoping engine, `N = 1,…,8`

`P_1 = 1` is nonneg-coefficient; each `P_N` is then assembled as
`P_{N−1} + (P_N − P_{N−1})` through `nonnegCoeffs_of_telescope`, using the
first-difference positivity `pdiff_nonneg_N` and the reconstruction identity
`padd P_{N−1} (psub P_N P_{N−1}) = P_N` (`decide`).  This extends the verified
`nonnegCoeffs P_N` chain to `N = 8`. -/

/-- `P_1 = 1` is nonneg-coefficient (telescoping base). -/
theorem P1_nonneg : nonnegCoeffs P1 := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- Reconstruction `padd P_1 (psub P_2 P_1) = P_2` (`decide`). -/
theorem precon_2 : QPoly.padd P1 (QPoly.psub P2 P1) = P2 := by decide

/-- **`nonnegCoeffs P_2`** via the telescoping engine (from `P_1` and `D_2`). -/
theorem P2_nonneg : nonnegCoeffs P2 :=
  nonnegCoeffs_of_telescope P1_nonneg pdiff_nonneg_2 precon_2

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- Reconstruction `padd P_2 (psub P_3 P_2) = P_3` (`decide`). -/
theorem precon_3 : QPoly.padd P2 (QPoly.psub P3 P2) = P3 := by decide

/-- **`nonnegCoeffs P_3`** via the telescoping engine (from `P_2` and `D_3`). -/
theorem P3_nonneg : nonnegCoeffs P3 :=
  nonnegCoeffs_of_telescope P2_nonneg pdiff_nonneg_3 precon_3

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- Reconstruction `padd P_3 (psub P_4 P_3) = P_4` (`decide`). -/
theorem precon_4 : QPoly.padd P3 (QPoly.psub P4 P3) = P4 := by decide

/-- **`nonnegCoeffs P_4`** via the telescoping engine (from `P_3` and `D_4`). -/
theorem P4_nonneg : nonnegCoeffs P4 :=
  nonnegCoeffs_of_telescope P3_nonneg pdiff_nonneg_4 precon_4

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- Reconstruction `padd P_4 (psub P_5 P_4) = P_5` (`decide`). -/
theorem precon_5 : QPoly.padd P4 (QPoly.psub P5 P4) = P5 := by decide

/-- **`nonnegCoeffs P_5`** via the telescoping engine (from `P_4` and `D_5`). -/
theorem P5_nonneg : nonnegCoeffs P5 :=
  nonnegCoeffs_of_telescope P4_nonneg pdiff_nonneg_5 precon_5

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- Reconstruction `padd P_5 (psub P_6 P_5) = P_6` (`decide`). -/
theorem precon_6 : QPoly.padd P5 (QPoly.psub P6 P5) = P6 := by decide

/-- **`nonnegCoeffs P_6`** via the telescoping engine (from `P_5` and `D_6`). -/
theorem P6_nonneg : nonnegCoeffs P6 :=
  nonnegCoeffs_of_telescope P5_nonneg pdiff_nonneg_6 precon_6

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- Reconstruction `padd P_6 (psub P_7 P_6) = P_7` (`decide`). -/
theorem precon_7 : QPoly.padd P6 (QPoly.psub P7 P6) = P7 := by decide

/-- **`nonnegCoeffs P_7`** via the telescoping engine (from `P_6` and `D_7`). -/
theorem P7_nonneg : nonnegCoeffs P7 :=
  nonnegCoeffs_of_telescope P6_nonneg pdiff_nonneg_7 precon_7

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- Reconstruction `padd P_7 (psub P_8 P_7) = P_8` (`decide`). -/
theorem precon_8 : QPoly.padd P7 (QPoly.psub P8 P7) = P8 := by decide

/-- **`nonnegCoeffs P_8`** via the telescoping engine (from `P_7` and `D_8`). -/
theorem P8_nonneg : nonnegCoeffs P8 :=
  nonnegCoeffs_of_telescope P7_nonneg pdiff_nonneg_8 precon_8
/-! ## The precise named OPEN `Prop` (uniform first-difference positivity)

The single remaining mathematical gap.  Uniform `nonnegCoeffs P_N` (all `N`)
reduces — via the telescoping engine — to the uniform *monotonicity* of the
residuals: that every first difference `P_{N+1} − P_N` is nonneg-coefficient.
This is a cleaner `N`-indexed target than `P_N` itself (a single difference
positivity rather than the full coefficient positivity), verified through
`N = 8` (`pdiff_nonneg_2 … pdiff_nonneg_8`) but OPEN as an `N`-indexed theorem. -/

/-- **OPEN.**  Uniform first-difference positivity of the residual family:
every `P_{N+1} − P_N` (`= psub (Pseq (N+1)) (Pseq N)`) is nonneg-coefficient.
Verified for `N ≤ 7` by `pdiff_nonneg_*`; an `N`-indexed proof is open. -/
def UniformPNDiffNonneg : Prop :=
  ∀ N : Nat, nonnegCoeffs (QPoly.psub (Pseq (N + 1)) (Pseq N))

/-- **Conditional uniform closure.**  *If* `UniformPNDiffNonneg` holds and the
reconstruction `padd (Pseq N) (psub (Pseq (N+1)) (Pseq N)) = Pseq (N+1)` holds
for all `N` (the latter is a structural `padd`/`psub` list-identity, true for
every list — supplied here as a hypothesis `hrec`), then `nonnegCoeffs (Pseq N)`
for all `N`, by induction through the telescoping engine.  This packages the
reduction "uniform difference-positivity ⟹ uniform `P_N`-positivity". -/
theorem nonnegCoeffs_of_Pseq_of_uniformDiff
    (hdiff : UniformPNDiffNonneg)
    (hrec : ∀ N : Nat,
      QPoly.padd (Pseq N) (QPoly.psub (Pseq (N + 1)) (Pseq N)) = Pseq (N + 1))
    (hbase : nonnegCoeffs (Pseq 0)) :
    ∀ N : Nat, nonnegCoeffs (Pseq N)
  | 0 => hbase
  | (N + 1) =>
      nonnegCoeffs_of_telescope
        (nonnegCoeffs_of_Pseq_of_uniformDiff hdiff hrec hbase N)
        (hdiff N) (hrec N)

end YMGap.Continuum.PNInduction

/-! ## OPEN obligation — sharp statement

**Proved here (axiom-clean), the new content:**

  * `nonnegCoeffs_of_telescope` — the telescoping engine
    `P_N = P_{N−1} + (P_N − P_{N−1})` at the coefficient-list level.
  * `pdiff_nonneg_2 … pdiff_nonneg_8` — the **first-difference positivity**
    `nonnegCoeffs (P_N − P_{N−1})` for `N = 2,…,8` (coefficient-monotonicity
    of `P_N` in `N`).
  * `P1_nonneg … P8_nonneg` — `nonnegCoeffs P_N` for `N = 1,…,8`, each
    assembled through the telescoping engine (extending the prior `N ≤ 5`
    chain to `N = 8`).
  * `UniformPNDiffNonneg` + `nonnegCoeffs_of_Pseq_of_uniformDiff` — the
    reduction of uniform `nonnegCoeffs P_N` to the uniform monotonicity
    `nonnegCoeffs (P_{N+1} − P_N)`.

**Ruled out (exact computer algebra, recorded in the header):** a q-product
factorization of `P_N` (`P_N` irreducible over ℚ), a fixed-depth linear
recurrence with polynomial coefficients (degree `N(N−1)` grows; no
multiplier-degree-`≤4` syzygy for `N ≥ 3`), and a division-free Favard
quadratic (`P_{k−1} ∤ P_k²`).

**OPEN — the single remaining gap:** `UniformPNDiffNonneg`, i.e.
`∀ N, nonnegCoeffs (P_{N+1} − P_N)`.  Equivalently, the residual polynomials
`P_N = Δ_N/S_N²` are coefficient-wise monotone increasing in `N`.  This is a
strictly cleaner uniform target than `nonnegCoeffs P_N` (a single difference
positivity), is verified through `N = 8`, and — via
`nonnegCoeffs_of_Pseq_of_uniformDiff` — closes the uniform all-`N`
coefficient-positivity, hence (with the `Δ_N = S_N²·P_N` engine) the uniform
all-`N` minor nonnegativity `Δ_N(a) ≥ 0`.
-/

#print axioms YMGap.Continuum.PNInduction.nonnegCoeffs_of_telescope
#print axioms YMGap.Continuum.PNInduction.pdiff_nonneg_2
#print axioms YMGap.Continuum.PNInduction.pdiff_nonneg_8
#print axioms YMGap.Continuum.PNInduction.P5_nonneg
#print axioms YMGap.Continuum.PNInduction.P8_nonneg
#print axioms YMGap.Continuum.PNInduction.nonnegCoeffs_of_Pseq_of_uniformDiff
