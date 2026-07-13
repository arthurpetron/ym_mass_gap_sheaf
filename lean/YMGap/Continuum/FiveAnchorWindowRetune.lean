/-
Exact five-anchor correlation window through `w = 10/11`.

The strengthened head uses the first five adjacent edges and only the first
five diagonal coordinates.  The unused `c_5^2` pays the first symbolic tail
edge; PF2 then propagates the exact ratio `c_5/c_4 = (6/5)w^11`.
-/

import YMGap.Continuum.HarmonicSchurRotationIdentity

namespace YMGap.Continuum.FiveAnchorWindowRetune

set_option maxHeartbeats 3200000
set_option maxRecDepth 70000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ThreeAnchorWindowRetune

local infix:50 " ≈ " => Q'.eqv

def fiveAnchorCap : Q' := Q'.mkPos 10 11 (by decide)
private def capInv : Q' := Q'.mkPos 11 10 (by decide)
private def sixFifths : Q' := Q'.mkPos 6 5 (by decide)

def tailRatio5 (w : Q') : Q' := sixFifths * qpow w 11

private def headSlack5P : Poly :=
  psub (pmul retuneP (prefixDP 4)) (prefixAP 5)

private def oneSlack5P : Poly :=
  psub (pmul retuneP (prefixDP 1)) (prefixAP 1)

private def twoSlack5P : Poly :=
  psub (pmul retuneP (prefixDP 2)) (prefixAP 2)

private def threeSlack5P : Poly :=
  psub (pmul retuneP (prefixDP 3)) (prefixAP 3)

private def ratio5P : Poly := monoP sixFifths 11
private def ratioSlack5P : Poly := psub retuneP ratio5P

private theorem scaled_bernstein_nonneg
    (p : Poly) (D : Nat) (terms : List (Nat × Q'))
    (hrep : allZero
      (psub (scaleVar fiveAnchorCap p) (bernTermsP D terms)))
    (hnn : ∀ t ∈ terms, (0 : Q') ≤ t.2)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fiveAnchorCap) :
    (0 : Q') ≤ eval p w := by
  let x := capInv * w
  have hx0 : (0 : Q') ≤ x := Q'.mul_nonneg _ _ (by decide) hw0
  have hx1 : x ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ capInv hwc (by decide)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hb : (0 : Q') ≤ eval (bernTermsP D terms) x :=
    eval_bernTermsP_nonneg hx0 hx1 D terms hnn
  have hs : (0 : Q') ≤ eval (scaleVar fiveAnchorCap p) x :=
    Q'.le_trans' _ _ _ hb
      (Q'.ge_of_eqv (poly_eqv _ _ x hrep))
  refine Q'.le_trans' _ _ _ hs (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (eval_scaleVar fiveAnchorCap x p) ?_
  apply eval_eqv_arg
  unfold x
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ w)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ w (by decide : fiveAnchorCap * capInv ≈ 1)) ?_
  exact Q'.one_mul_eqv w

private def head5Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 679 88 (by decide)),
   (2, Q'.mkPos 226471 968 (by decide)),
   (3, Q'.mkPos 49442969 10648 (by decide)),
   (4, Q'.mkPos 361103393 5324 (by decide)),
   (5, Q'.mkPos 376229903 484 (by decide)),
   (6, Q'.mkPos 51571135618697 7086244 (by decide)),
   (7, Q'.mkPos 4460407951372103 77948684 (by decide)),
   (8, Q'.mkPos 661172323376067559 1714871048 (by decide)),
   (9, Q'.mkPos 42638658361781124881 18863581528 (by decide)),
   (10, Q'.mkPos 220125705892746707755 18863581528 (by decide)),
   (11, Q'.mkPos 122251605372659102409095 2282493364888 (by decide)),
   (12, Q'.mkPos 125695596554910080516745 570623341222 (by decide)),
   (13, Q'.mkPos 466214270439100884997005 570623341222 (by decide)),
   (14, Q'.mkPos 1568008525802098194482595 570623341222 (by decide)),
   (15, Q'.mkPos 4803990556908734200237735 570623341222 (by decide)),
   (16, Q'.mkPos 8670969634205739639673584476785 367597838908577288 (by decide)),
   (17, Q'.mkPos 245213000528785630746274737428215 4043576227994350168 (by decide)),
   (18, Q'.mkPos 6381274368988070870180309928644135 44479338507937851848 (by decide)),
   (19, Q'.mkPos 153190376640693482596642519050581465 489272723587316370328 (by decide)),
   (20, Q'.mkPos 154530479980839065168304432168269015 244636361793658185164 (by decide)),
   (21, Q'.mkPos 288733788170921168196107382952094835 244636361793658185164 (by decide)),
   (22, Q'.mkPos 500409146889991293570210784246281765 244636361793658185164 (by decide)),
   (23, Q'.mkPos 11793363020990052784902307231446768026385 3581720973020949488986124 (by decide)),
   (24, Q'.mkPos 35302065505559666602125249936101468283005 7163441946041898977972248 (by decide)),
   (25, Q'.mkPos 49171719931645764976233899344295511297697 7163441946041898977972248 (by decide)),
   (26, Q'.mkPos 63786386062311380834931037600749105972683 7163441946041898977972248 (by decide)),
   (27, Q'.mkPos 7009515984252580399489826707154747210877 651221995094718088906568 (by decide)),
   (28, Q'.mkPos 987340481604030749880674767822511643381 81402749386839761113321 (by decide)),
   (29, Q'.mkPos 1037445934298291203918156410406414560489 81402749386839761113321 (by decide)),
   (30, Q'.mkPos 217916132048332855642275176902126706664574796439 17449402268886407318558803753801 (by decide)),
   (31, Q'.mkPos 2190515247008692063230014060291932292694540733881 191943424957750480504146841291811 (by decide)),
   (32, Q'.mkPos 164255007002584418614545508874836383220300608930027 16891021396282042284364922033679368 (by decide)),
   (33, Q'.mkPos 1435216120618593803017320481327942432099405212635853 185801235359102465128014142370473048 (by decide)),
   (34, Q'.mkPos 1062376163077282220802501444822186530625603010392807 185801235359102465128014142370473048 (by decide)),
   (35, Q'.mkPos 732453773461782970014097045215192925126529715917355 185801235359102465128014142370473048 (by decide)),
   (36, Q'.mkPos 235030343443259091367382321906420802734711796239735 92900617679551232564007071185236524 (by decide)),
   (37, Q'.mkPos 140294648264363638459955313265376342698668813276115 92900617679551232564007071185236524 (by decide)),
   (38, Q'.mkPos 7074801375828831729829609779854952441123880413535 8445510698141021142182461016839684 (by decide)),
   (39, Q'.mkPos 70991342854709679758540689429460536161418636004013465465 164579111157003461112324931035988801693964 (by decide)),
   (40, Q'.mkPos 67778075246598927968921261982635768404935808657259253015 329158222314006922224649862071977603387928 (by decide)),
   (41, Q'.mkPos 29948554735581891983935312604432688158626392958787552835 329158222314006922224649862071977603387928 (by decide)),
   (42, Q'.mkPos 12225773123099183498248329740689080577092609763253453265 329158222314006922224649862071977603387928 (by decide)),
   (43, Q'.mkPos 4600439361410028064274594994287425050733566390446137485 329158222314006922224649862071977603387928 (by decide)),
   (44, Q'.mkPos 397817991841833301424636027308119784232228657384256585 82289555578501730556162465517994400846982 (by decide)),
   (45, Q'.mkPos 126067205239891828442686448741254740893651845127760845 82289555578501730556162465517994400846982 (by decide)),
   (46, Q'.mkPos 36454524802608315226222286825631152010058650387573955 82289555578501730556162465517994400846982 (by decide)),
   (47, Q'.mkPos 9573138314983881696029280058020018861867037273329095 82289555578501730556162465517994400846982 (by decide)),
   (48, Q'.mkPos 21410934966510069810943260324239072423753981339681902533493795 776137870278977299217629725556088065712278604874248 (by decide)),
   (49, Q'.mkPos 50091388706144051131627429539726265706805832016707780596880405 8537516573068750291393926981116968722835064653616728 (by decide)),
   (50, Q'.mkPos 104258949486241189425875450745478762273032052241221754901400261 93912682303756253205333196792286655951185711189784008 (by decide)),
   (51, Q'.mkPos 191151095433239614221728027566619416534995898016396064427084219 1033039505341318785258665164715153215463042823087624088 (by decide)),
   (52, Q'.mkPos 13859097359126635571460535324197041649560014755161755933773673 516519752670659392629332582357576607731521411543812044 (by decide)),
   (53, Q'.mkPos 1720834582888282072000100391300274313197681351714818075187277 516519752670659392629332582357576607731521411543812044 (by decide)),
   (54, Q'.mkPos 179212505245574780572208106250583280075722674209263955792763 516519752670659392629332582357576607731521411543812044 (by decide)),
   (55, Q'.mkPos 15219248674014903744059516269354111392700606229881195767743 516519752670659392629332582357576607731521411543812044 (by decide)),
   (56, Q'.mkPos 2018981772631866575723695484083653669489093783719772998279 1033039505341318785258665164715153215463042823087624088 (by decide)),
   (57, Q'.mkPos 97420169929287317034353395773728571581244669957941292211 1033039505341318785258665164715153215463042823087624088 (by decide)),
   (58, Q'.mkPos 3349669568575934232699881094833171726561625506010965489 1033039505341318785258665164715153215463042823087624088 (by decide)),
   (59, Q'.mkPos 4090151036996585386079665188199560223060670120294616817833421 221441192393758617872326760262020927010209756412144064452325528 (by decide))]

private theorem head5_bernstein_identity :
    allZero (psub (scaleVar fiveAnchorCap headSlack5P)
      (bernTermsP 59 head5Bern)) := by decide

private def one5Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 129 88 (by decide)),
   (2, Q'.mkPos 912 121 (by decide)),
   (3, Q'.mkPos 27693 1331 (by decide)),
   (4, Q'.mkPos 175143 5324 (by decide)),
   (5, Q'.mkPos 156153 5324 (by decide)),
   (6, Q'.mkPos 22225913 1771561 (by decide)),
   (7, Q'.mkPos 20255712 19487171 (by decide)),
   (8, Q'.mkPos 1123839069 1714871048 (by decide)),
   (9, Q'.mkPos 25105450421 18863581528 (by decide))]

private theorem one5_bernstein_identity :
    allZero (psub (scaleVar fiveAnchorCap oneSlack5P)
      (bernTermsP 9 one5Bern)) := by decide

private def two5Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 125 44 (by decide)),
   (2, Q'.mkPos 3695 121 (by decide)),
   (3, Q'.mkPos 1091235 5324 (by decide)),
   (4, Q'.mkPos 10216065 10648 (by decide)),
   (5, Q'.mkPos 4419813 1331 (by decide)),
   (6, Q'.mkPos 15589371650 1771561 (by decide)),
   (7, Q'.mkPos 355580384735 19487171 (by decide)),
   (8, Q'.mkPos 25720101555605 857435524 (by decide)),
   (9, Q'.mkPos 185624828355955 4715895382 (by decide)),
   (10, Q'.mkPos 8853632756072 214358881 (by decide)),
   (11, Q'.mkPos 19737131940458725 570623341222 (by decide)),
   (12, Q'.mkPos 26281757573417265 1141246682444 (by decide)),
   (13, Q'.mkPos 3472764988476945 285311670611 (by decide)),
   (14, Q'.mkPos 1469330778123690 285311670611 (by decide)),
   (15, Q'.mkPos 508775449686523 285311670611 (by decide)),
   (16, Q'.mkPos 186410338243941556325 367597838908577288 (by decide)),
   (17, Q'.mkPos 211519085173533392005 2021788113997175084 (by decide)),
   (18, Q'.mkPos 54598552319942397065 5559917313492231481 (by decide)),
   (19, Q'.mkPos 183239372065722089195 244636361793658185164 (by decide)),
   (20, Q'.mkPos 455738098568831207021 489272723587316370328 (by decide))]

private theorem two5_bernstein_identity :
    allZero (psub (scaleVar fiveAnchorCap twoSlack5P)
      (bernTermsP 20 two5Bern)) := by decide

private def three5Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 393 88 (by decide)),
   (2, Q'.mkPos 18687 242 (by decide)),
   (3, Q'.mkPos 2287429 2662 (by decide)),
   (4, Q'.mkPos 18388455 2662 (by decide)),
   (5, Q'.mkPos 113684379 2662 (by decide)),
   (6, Q'.mkPos 748057069607 3543122 (by decide)),
   (7, Q'.mkPos 33400855482717 38974342 (by decide)),
   (8, Q'.mkPos 623897111886627 214358881 (by decide)),
   (9, Q'.mkPos 19774353055913450 2357947691 (by decide)),
   (10, Q'.mkPos 97696284460858785 4715895382 (by decide)),
   (11, Q'.mkPos 25235081126319748905 570623341222 (by decide)),
   (12, Q'.mkPos 4257472708007904805 51874849202 (by decide)),
   (13, Q'.mkPos 6899561567749735785 51874849202 (by decide)),
   (14, Q'.mkPos 9794904228737778675 51874849202 (by decide)),
   (15, Q'.mkPos 12206848356012853955 51874849202 (by decide)),
   (16, Q'.mkPos 47373898756540415198374905 183798919454288644 (by decide)),
   (17, Q'.mkPos 501898189153400488814785005 2021788113997175084 (by decide)),
   (18, Q'.mkPos 2337283570234058417017751005 11119834626984462962 (by decide)),
   (19, Q'.mkPos 19124598179839238873131448175 122318180896829092582 (by decide)),
   (20, Q'.mkPos 12485342633013742560691929885 122318180896829092582 (by decide)),
   (21, Q'.mkPos 7145113914550024409696749705 122318180896829092582 (by decide)),
   (22, Q'.mkPos 3579454399889810018415852855 122318180896829092582 (by decide)),
   (23, Q'.mkPos 22938630081775753275859369635735 1790860486510474744493062 (by decide)),
   (24, Q'.mkPos 4371391368387227851256765708950 895430243255237372246531 (by decide)),
   (25, Q'.mkPos 1441158321715788431072851876167 895430243255237372246531 (by decide)),
   (26, Q'.mkPos 811991561696405637248587724067 1790860486510474744493062 (by decide)),
   (27, Q'.mkPos 191818205375570201451231904467 1790860486510474744493062 (by decide)),
   (28, Q'.mkPos 37144383935033411407549912149 1790860486510474744493062 (by decide)),
   (29, Q'.mkPos 5787901400618157314164725705 1790860486510474744493062 (by decide)),
   (30, Q'.mkPos 13833887690469274291708169621961889 34898804537772814637117607507602 (by decide)),
   (31, Q'.mkPos 12499941682662046224400587416601147 383886849915500961008293682583622 (by decide)),
   (32, Q'.mkPos 11989959323403948258431956046465253 16891021396282042284364922033679368 (by decide)),
   (33, Q'.mkPos 72243190919456334218796859507135061 185801235359102465128014142370473048 (by decide))]

private theorem three5_bernstein_identity :
    allZero (psub (scaleVar fiveAnchorCap threeSlack5P)
      (bernTermsP 33 three5Bern)) := by decide

private def ratio5Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 151 88 (by decide)),
   (2, Q'.mkPos 10255 968 (by decide)),
   (3, Q'.mkPos 413665 10648 (by decide)),
   (4, Q'.mkPos 500815 5324 (by decide)),
   (5, Q'.mkPos 841211 5324 (by decide)),
   (6, Q'.mkPos 1000741 5324 (by decide)),
   (7, Q'.mkPos 843665 5324 (by decide)),
   (8, Q'.mkPos 988415 10648 (by decide)),
   (9, Q'.mkPos 383355 10648 (by decide)),
   (10, Q'.mkPos 88641 10648 (by decide)),
   (11, Q'.mkPos 1025177596941 2282493364888 (by decide))]

private theorem ratio5_bernstein_identity :
    allZero (psub (scaleVar fiveAnchorCap ratioSlack5P)
      (bernTermsP 11 ratio5Bern)) := by decide

/-! ## Certified head and PF2 tail -/

theorem strengthened_five_anchor_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fiveAnchorCap) :
    adjCorr w 5 ≤ retuneCube w * coordNormSq w 4 := by
  apply slack_nonneg_to_bound w (adjCorr w 5) (coordNormSq w 4)
    (prefixAP 5) (prefixDP 4) headSlack5P
    (prefixA_eval w 5) (prefixD_eval w 4) rfl
  exact scaled_bernstein_nonneg headSlack5P 59 head5Bern
    head5_bernstein_identity (by decide) hw0 hwc

theorem one_edge_head5 {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fiveAnchorCap) :
    adjCorr w 1 ≤ retuneCube w * coordNormSq w 1 := by
  apply slack_nonneg_to_bound w (adjCorr w 1) (coordNormSq w 1)
    (prefixAP 1) (prefixDP 1) oneSlack5P
    (prefixA_eval w 1) (prefixD_eval w 1) rfl
  exact scaled_bernstein_nonneg oneSlack5P 9 one5Bern
    one5_bernstein_identity (by decide) hw0 hwc

theorem two_edge_head5 {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fiveAnchorCap) :
    adjCorr w 2 ≤ retuneCube w * coordNormSq w 2 := by
  apply slack_nonneg_to_bound w (adjCorr w 2) (coordNormSq w 2)
    (prefixAP 2) (prefixDP 2) twoSlack5P
    (prefixA_eval w 2) (prefixD_eval w 2) rfl
  exact scaled_bernstein_nonneg twoSlack5P 20 two5Bern
    two5_bernstein_identity (by decide) hw0 hwc

theorem three_edge_head5 {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fiveAnchorCap) :
    adjCorr w 3 ≤ retuneCube w * coordNormSq w 3 := by
  apply slack_nonneg_to_bound w (adjCorr w 3) (coordNormSq w 3)
    (prefixAP 3) (prefixDP 3) threeSlack5P
    (prefixA_eval w 3) (prefixD_eval w 3) rfl
  exact scaled_bernstein_nonneg threeSlack5P 33 three5Bern
    three5_bernstein_identity (by decide) hw0 hwc

theorem tailRatio5_le_retune {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fiveAnchorCap) :
    tailRatio5 w ≤ retuneCube w := by
  have hs := scaled_bernstein_nonneg ratioSlack5P 11 ratio5Bern
    ratio5_bernstein_identity (by decide) hw0 hwc
  have hq : tailRatio5 w ≈ eval ratio5P w := by
    unfold tailRatio5 ratio5P
    exact Q'.eqv_symm (eval_monoP sixFifths w 11)
  have he : eval ratioSlack5P w ≈ retuneCube w + -(tailRatio5 w) := by
    refine Q'.eqv_trans _ _ _ (eval_psub _ _ w) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (retune_eval w))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hq))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv he))

theorem coeffW_five_eq_tailRatio5_mul_four (w : Q') :
    coeffW w 5 ≈ tailRatio5 w * coeffW w 4 := by
  have hc5 := hcoeff w 5
  have hq : tailRatio5 w ≈ eval ratio5P w := by
    unfold tailRatio5 ratio5P
    exact Q'.eqv_symm (eval_monoP sixFifths w 11)
  have hc4 := hcoeff w 4
  refine Q'.eqv_trans _ _ _ hc5 ?_
  refine Q'.eqv_trans _ _ _
    (poly_eqv (coeffPoly 5) (pmul ratio5P (coeffPoly 4)) w (by decide)) ?_
  exact Q'.eqv_symm (hEvalMul hq hc4)

theorem adjacent_tail5_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    {a : Nat} (ha : 4 ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      tailRatio5 w * (coeffW w a * coeffW w a) := by
  by_cases h4 : a = 4
  · subst a
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 4) _ _
        (coeffW_five_eq_tailRatio5_mul_four w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · have ha5 : 4 < a := by omega
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := 4) (N := a) ha5
    have hr : coeffW w (a + 1) * coeffW w 4 ≤ coeffW w a * coeffW w 5 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hc4p := FusionResidualBound.coeffW_pos hwp 4
    have hR : coeffW w 5 * (coeffW w a * coeffW w a) ≈
        coeffW w 4 * (tailRatio5 w * (coeffW w a * coeffW w a)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (coeffW_five_eq_tailRatio5_mul_four w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    have hcancel : coeffW w 4 * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w 4 * (tailRatio5 w * (coeffW w a * coeffW w a)) :=
      Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hR)
    exact Q'.le_of_mul_le_mul_left hcancel hc4p

private def edgeTail (w : Q') (j : Nat) : Q' :=
  coeffW w (5 + j) * coeffW w (5 + j + 1)

private def squareTail (w : Q') (j : Nat) : Q' :=
  coeffW w (5 + j) * coeffW w (5 + j)

private theorem tail_sum_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hwc : w ≤ fiveAnchorCap) (M : Nat) :
    fsum (edgeTail w) M ≤ retuneCube w * fsum (squareTail w) M := by
  have hterm : ∀ j, edgeTail w j ≤ retuneCube w * squareTail w j := by
    intro j
    have ht := adjacent_tail5_le hw0 hw1 hwp (a := 5 + j) (by omega)
    exact Q'.le_trans' _ _ _ ht
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (tailRatio5_le_retune hw0 hwc)
        (Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (5 + j)) (coeffW_nonneg hw0 (5 + j))))
  have hsum : fsum (edgeTail w) M ≤
      fsum (fun j => retuneCube w * squareTail w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact CharacterTail.finSum_le_termwise _ _ hterm M
  have hfactor : retuneCube w * fsum (squareTail w) M ≈
      fsum (fun j => retuneCube w * squareTail w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact const_mul_finSum (squareTail w) (retuneCube w) M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hfactor)

/-! ## Uniform all-cutoff quotient window -/

theorem five_anchor_retune_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fiveAnchorCap) (N : Nat) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hwc (by decide)
  by_cases hwz : w.eqv 0
  · have hA0 : adjCorr w N ≈ (0 : Q') := by
      unfold adjCorr
      refine Q'.eqv_trans _ _ _
        (fsum_eqv_congr _ (fun _ => (0 : Q')) (fun a => ?_) N) ?_
      · refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (coeffW w a) _ _
            (coeffW_excited_zero hwz a)) ?_
        exact Q'.mul_zero_eqv _
      · rw [fsum_zero_seq]
        exact Q'.eqv_refl 0
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA0)
      (Q'.mul_nonneg _ _
        (qpow_nonneg _
          (Q'.mul_nonneg _ _ (by decide)
            (Q'.zero_le_add _ _ (by decide) hw0)) 3)
        (coordNormSq_nonneg hw0 N))
  · have hwp : (0 : Q') < w := pos_of_nonneg_not_eqv_zero hw0 hwz
    rcases Nat.le_total N 5 with hsmall | hlarge
    · have cases : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Q'.mul_nonneg _ _
          (qpow_nonneg _
            (Q'.mul_nonneg _ _ (by decide)
              (Q'.zero_le_add _ _ (by decide) hw0)) 3)
          (coordNormSq_nonneg hw0 0)
      · exact one_edge_head5 hw0 hwc
      · exact two_edge_head5 hw0 hwc
      · exact three_edge_head5 hw0 hwc
      · have hA45 : adjCorr w 4 ≤ adjCorr w 5 := by
          unfold adjCorr
          exact AFRateCalibration.fsum_le_of_le
            (fun i => Q'.mul_nonneg _ _
              (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 (i + 1))) (by omega)
        exact Q'.le_trans' _ _ _ hA45 (strengthened_five_anchor_head hw0 hwc)
      · have hD45 : coordNormSq w 4 ≤ coordNormSq w 5 := by
          unfold coordNormSq
          exact AFRateCalibration.fsum_le_of_le
            (fun i => Q'.mul_nonneg _ _
              (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 i)) (by omega)
        have hr0 : (0 : Q') ≤ retuneCube w := qpow_nonneg _
          (Q'.mul_nonneg _ _ (by decide)
            (Q'.zero_le_add _ _ (by decide) hw0)) 3
        exact Q'.le_trans' _ _ _ (strengthened_five_anchor_head hw0 hwc)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hD45 hr0)
    · obtain ⟨M, rfl⟩ := Nat.le.dest hlarge
      have hA : adjCorr w (5 + M) ≈
          adjCorr w 5 + fsum (edgeTail w) M := by
        unfold adjCorr edgeTail
        exact FusionCoreStepRoundH.fsum_split_at
          (fun a => coeffW w a * coeffW w (a + 1)) 5 M
      have hD : coordNormSq w (5 + M) ≈
          coordNormSq w 4 + fsum (squareTail w) (M + 1) := by
        unfold coordNormSq squareTail
        rw [show 5 + M + 1 = 5 + (M + 1) by omega]
        exact FusionCoreStepRoundH.fsum_split_at
          (fun a => coeffW w a * coeffW w a) 5 (M + 1)
      have hsquare0 : ∀ j, (0 : Q') ≤ squareTail w j := by
        intro j
        unfold squareTail
        exact Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (5 + j)) (coeffW_nonneg hw0 (5 + j))
      have htailPrefix : fsum (squareTail w) M ≤
          fsum (squareTail w) (M + 1) :=
        AFRateCalibration.fsum_le_of_le hsquare0 (by omega)
      have hprefix : coordNormSq w 4 + fsum (squareTail w) M ≤
          coordNormSq w (5 + M) :=
        Q'.le_trans' _ _ _
          (Q'.add_le_add_left (coordNormSq w 4) _ _ htailPrefix)
          (Q'.ge_of_eqv hD)
      have hr0 : (0 : Q') ≤ retuneCube w := qpow_nonneg _
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.zero_le_add _ _ (by decide) hw0)) 3
      have hpaid : adjCorr w 5 + fsum (edgeTail w) M ≤
          retuneCube w * coordNormSq w 4 +
            retuneCube w * fsum (squareTail w) M :=
        AFRateCalibration.q_add_le_add
          (strengthened_five_anchor_head hw0 hwc)
          (tail_sum_le hw0 hw1 hwp hwc M)
      have hcollect : retuneCube w * coordNormSq w 4 +
          retuneCube w * fsum (squareTail w) M ≈
          retuneCube w * (coordNormSq w 4 + fsum (squareTail w) M) :=
        Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
        (Q'.le_trans' _ _ _ hpaid
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
            (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hr0)))

theorem five_anchor_ratio_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fiveAnchorCap) (N : Nat) :
    Q'.divPos (adjCorr w N) (coordNormSq w N) (coordNormSq_pos hw0 N) ≤
      retuneCube w :=
  Q'.divPos_le_of_le_mul _ _ _ (five_anchor_retune_all_cutoffs hw0 hwc N)

theorem five_anchor_lamPW_le_retune {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fiveAnchorCap) (N : Nat) :
    lamPW w N 1 ≤ retuneCube w := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hwc (by decide)
  have heq : lamPW w N 1 ≈
      Q'.divPos (adjCorr w N) (coordNormSq w N) (coordNormSq_pos hw0 N) :=
    Q'.eqv_trans _ _ _ (lamPW_eq_vacNorm_p2 hw0 hw1 N 0)
      (vacNorm_fundamental_eq_ratio hw0 hw1 N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (five_anchor_ratio_all_cutoffs hw0 hwc N)

/-! ## Harmonic scales `k=8,9` -/

theorem harmW_eight_mem_window : harmW 8 ≤ fiveAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit fiveAnchorCap
  decide

theorem harmW_nine_mem_window : harmW 9 ≤ fiveAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit fiveAnchorCap
  decide

theorem harmonicMass_k8_retune_floor :
    (1 : Q') - retuneCube (harmW 8) ≤ harmonicMass 8 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (five_anchor_lamPW_le_retune
      (harmW_nonneg 8) harmW_eight_mem_window (Ncut 8)))

theorem harmonicMass_k9_retune_floor :
    (1 : Q') - retuneCube (harmW 9) ≤ harmonicMass 9 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (five_anchor_lamPW_le_retune
      (harmW_nonneg 9) harmW_nine_mem_window (Ncut 9)))

theorem initial_ten_retune {k : Nat} (hk : k ≤ 9) :
    adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k) := by
  by_cases hk7 : k ≤ 7
  · exact FourAnchorWindowRetune.initial_eight_retune hk7
  · have cases : k = 8 ∨ k = 9 := by omega
    rcases cases with rfl | rfl
    · exact five_anchor_retune_all_cutoffs
        (harmW_nonneg 8) harmW_eight_mem_window (Ncut 8)
    · exact five_anchor_retune_all_cutoffs
        (harmW_nonneg 9) harmW_nine_mem_window (Ncut 9)

end YMGap.Continuum.FiveAnchorWindowRetune

#print axioms YMGap.Continuum.FiveAnchorWindowRetune.strengthened_five_anchor_head
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.one_edge_head5
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.two_edge_head5
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.three_edge_head5
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.tailRatio5_le_retune
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.coeffW_five_eq_tailRatio5_mul_four
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.adjacent_tail5_le
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.five_anchor_retune_all_cutoffs
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.five_anchor_ratio_all_cutoffs
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.five_anchor_lamPW_le_retune
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.harmW_eight_mem_window
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.harmW_nine_mem_window
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.harmonicMass_k8_retune_floor
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.harmonicMass_k9_retune_floor
#print axioms YMGap.Continuum.FiveAnchorWindowRetune.initial_ten_retune
