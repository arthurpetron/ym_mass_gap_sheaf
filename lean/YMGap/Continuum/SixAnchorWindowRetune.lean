/-
Exact six-anchor correlation window through `w = 13/14`.

The strengthened head uses the first six adjacent edges and only the first
six diagonal coordinates.  The unused `c_6^2` pays the first symbolic tail
edge; PF2 propagates the exact ratio `c_6/c_5 = (7/6)w^13`.
-/

import YMGap.Continuum.FiveAnchorWindowRetune

namespace YMGap.Continuum.SixAnchorWindowRetune

set_option maxHeartbeats 5200000
set_option maxRecDepth 100000

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
open YMGap.Continuum.FiveAnchorWindowRetune
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ThreeAnchorWindowRetune

local infix:50 " ≈ " => Q'.eqv

def sixAnchorCap : Q' := Q'.mkPos 13 14 (by decide)
private def capInv : Q' := Q'.mkPos 14 13 (by decide)
private def sevenSixths : Q' := Q'.mkPos 7 6 (by decide)

def tailRatio6 (w : Q') : Q' := sevenSixths * qpow w 13

private def headSlack6P : Poly :=
  psub (pmul retuneP (prefixDP 5)) (prefixAP 6)
private def short1SlackP : Poly :=
  psub (pmul retuneP (prefixDP 1)) (prefixAP 1)
private def short2SlackP : Poly :=
  psub (pmul retuneP (prefixDP 2)) (prefixAP 2)
private def short3SlackP : Poly :=
  psub (pmul retuneP (prefixDP 3)) (prefixAP 3)
private def short4SlackP : Poly :=
  psub (pmul retuneP (prefixDP 4)) (prefixAP 4)
private def ratio6P : Poly := monoP sevenSixths 13
private def ratioSlack6P : Poly := psub retuneP ratio6P

private theorem scaled_bernstein_nonneg
    (p : Poly) (degree : Nat) (terms : List (Nat × Q'))
    (hrep : allZero
      (psub (scaleVar sixAnchorCap p) (bernTermsP degree terms)))
    (hnn : ∀ t ∈ terms, (0 : Q') ≤ t.2)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ sixAnchorCap) :
    (0 : Q') ≤ eval p w := by
  let x := capInv * w
  have hx0 : (0 : Q') ≤ x := Q'.mul_nonneg _ _ (by decide) hw0
  have hx1 : x ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ capInv hwc (by decide)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hb : (0 : Q') ≤ eval (bernTermsP degree terms) x :=
    eval_bernTermsP_nonneg hx0 hx1 degree terms hnn
  have hs : (0 : Q') ≤ eval (scaleVar sixAnchorCap p) x :=
    Q'.le_trans' _ _ _ hb
      (Q'.ge_of_eqv (poly_eqv _ _ x hrep))
  refine Q'.le_trans' _ _ _ hs (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (eval_scaleVar sixAnchorCap x p) ?_
  apply eval_eqv_arg
  unfold x
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ w)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ w (by decide : sixAnchorCap * capInv ≈ 1)) ?_
  exact Q'.one_mul_eqv w

private def head6Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 1201 112 (by decide)),
   (2, Q'.mkPos 712267 1568 (by decide)),
   (3, Q'.mkPos 278049171 21952 (by decide)),
   (4, Q'.mkPos 89683485 343 (by decide)),
   (5, Q'.mkPos 11692707603 2744 (by decide)),
   (6, Q'.mkPos 859822613010985 15059072 (by decide)),
   (7, Q'.mkPos 136369532528861125 210827008 (by decide)),
   (8, Q'.mkPos 18663059359636652467 2951578112 (by decide)),
   (9, Q'.mkPos 2238450848897564665923 41322093568 (by decide)),
   (10, Q'.mkPos 132914460783381400149 322828856 (by decide)),
   (11, Q'.mkPos 709560935810242029549087 253097823104 (by decide)),
   (12, Q'.mkPos 8727619836624005093891049 506195646208 (by decide)),
   (13, Q'.mkPos 97612706647460215547205273 1012391292416 (by decide)),
   (14, Q'.mkPos 17828422222809548043461673 36156831872 (by decide)),
   (15, Q'.mkPos 20947096581789584796674303 9039207968 (by decide)),
   (16, Q'.mkPos 175122860114338500219446293950054985 17423626702474969088 (by decide)),
   (17, Q'.mkPos 9849596147745145486491081736786192537 243930773834649567232 (by decide)),
   (18, Q'.mkPos 514790763339124418393268247288946453667 3415030833685093941248 (by decide)),
   (19, Q'.mkPos 25073462963254062235008903438753825586875 47810431671591315177472 (by decide)),
   (20, Q'.mkPos 318342748775081609305911141511998921165 186759498717153574912 (by decide)),
   (21, Q'.mkPos 1107249863790926513864239383077499054153 213439427105318371328 (by decide)),
   (22, Q'.mkPos 3161629242391978567047403068364621372443 213439427105318371328 (by decide)),
   (23, Q'.mkPos 2281760903409022126545822706352096117607158457 57396423221745373870555136 (by decide)),
   (24, Q'.mkPos 1441251036492138572607837426295986687982459303 14349105805436343467638784 (by decide)),
   (25, Q'.mkPos 6866021305382922288996534850543092052890770197 28698211610872686935277568 (by decide)),
   (26, Q'.mkPos 7719313964004344500080098177121084911146284217 14349105805436343467638784 (by decide)),
   (27, Q'.mkPos 65616827654041592002103172716618198540415522903 57396423221745373870555136 (by decide)),
   (28, Q'.mkPos 2355754895181720555799601766188403841204848663 1024936128959738819117056 (by decide)),
   (29, Q'.mkPos 8970071253083944896338963173167755922430488495 2049872257919477638234112 (by decide)),
   (30, Q'.mkPos 95546011809737790490778056867368706058639259706094702617 12100716177742297710970518621913088 (by decide)),
   (31, Q'.mkPos 2289253783861963555329231417331867931924617335921971699269 169410026488392167953587260706783232 (by decide)),
   (32, Q'.mkPos 52057613290467310150662583678178624499392828711310917342707 2371740370837490351350221649894965248 (by decide)),
   (33, Q'.mkPos 1124184844237504110733043802996615451597853967479702170845219 33204365191724864918903103098529513472 (by decide)),
   (34, Q'.mkPos 51487174800503707731427015343461676859019434032040796582317 1037636412241402028715721971829047296 (by decide)),
   (35, Q'.mkPos 46842850672436919338773340109805728093842422326787921351299 677640105953568671814349042827132928 (by decide)),
   (36, Q'.mkPos 7756897410992038421525035419425806851958810816107598627041 84705013244196083976793630353391616 (by decide)),
   (37, Q'.mkPos 19549519072115184930955246027088525906127387561783128218797 169410026488392167953587260706783232 (by decide)),
   (38, Q'.mkPos 2929957485261713883234118398590102444201156731541485717599 21176253311049020994198407588347904 (by decide)),
   (39, Q'.mkPos 19735490479059613111205500713262045683102055939331998632978084924423 125006731534119636251008997646044759374954496 (by decide)),
   (40, Q'.mkPos 5358512574493779718474853829312586693146415200811884593812044022893 31251682883529909062752249411511189843738624 (by decide)),
   (41, Q'.mkPos 11079731619060577904539101435123108016138879835516988449585969947215 62503365767059818125504498823022379687477248 (by decide)),
   (42, Q'.mkPos 778893339212276381444931042149190409641396974395705200439280682479 4464526126218558437536035630215884263391232 (by decide)),
   (43, Q'.mkPos 2919030631963619160372239102318312537466724119346748882731219091719 17858104504874233750144142520863537053564928 (by decide)),
   (44, Q'.mkPos 325427806683689162875267777754948541592322266667553531987268450855 2232263063109279218768017815107942131695616 (by decide)),
   (45, Q'.mkPos 552531410471555552682128570813232179848525830505054742182652430715 4464526126218558437536035630215884263391232 (by decide)),
   (46, Q'.mkPos 1562443316940746807177324189043207759059136670065571289412095730529 15625841441764954531376124705755594921869312 (by decide)),
   (47, Q'.mkPos 9609494149618635721705377877565634807726018294074170127180612682277 125006731534119636251008997646044759374954496 (by decide)),
   (48, Q'.mkPos 4646599795809147968967431528781725366311835886843742732413999528239658974727897 82648637713323964698725096562236052672126638071268507648 (by decide)),
   (49, Q'.mkPos 45248012451416127012572477727527374418807081820305519502409367421394642231684713 1157080927986535505782151351871304737409772932997759107072 (by decide)),
   (50, Q'.mkPos 418911743040575549170586634147643930674878239480329042318685312196801343790359891 16199132991811497080950118926198266323736821061968627499008 (by decide)),
   (51, Q'.mkPos 3685831297427590045416695910889950517462142755609928984186427790283213680814382699 226787861885360959133301664966775728532315494867560784986112 (by decide)),
   (52, Q'.mkPos 17191176695154377551658921791857523900063307442985473033485722566374805488900301 1771780170979382493228919257552935379158714803652818632704 (by decide)),
   (53, Q'.mkPos 77955754760703916592593221108624535542471250045256224686913581527943321094561839 14174241367835059945831354060423483033269718429222549061632 (by decide)),
   (54, Q'.mkPos 41929472081776781127068904297009510450383957795993032352687959976457371678520605 14174241367835059945831354060423483033269718429222549061632 (by decide)),
   (55, Q'.mkPos 42771124741408034353843848434503347129893415687233681040997688283210357205226453 28348482735670119891662708120846966066539436858445098123264 (by decide)),
   (56, Q'.mkPos 738237931312457698741089122271004532834428429733942304715470217385531700177547 1012445811988218567559382432887391645233551316373039218688 (by decide)),
   (57, Q'.mkPos 337777465587274583445833735630529447838884180152839558507525740650550195658099 1012445811988218567559382432887391645233551316373039218688 (by decide)),
   (58, Q'.mkPos 4092905125043297546565339236256555203896727969413624727087289789598771608476759 28348482735670119891662708120846966066539436858445098123264 (by decide)),
   (59, Q'.mkPos 1234806398642747413021256158583908658980626386904832394391479842729080797093130440678117 20918190287753451881161865144034138985901134354048148493579575099392 (by decide)),
   (60, Q'.mkPos 59548221912950892765804570642150216007155353285131542290369048585311194395354391451631 2614773785969181485145233143004267373237641794256018561697446887424 (by decide)),
   (61, Q'.mkPos 43294275761807934321199768176797445254237082848521514814066158790308293786288649879609 5229547571938362970290466286008534746475283588512037123394893774848 (by decide)),
   (62, Q'.mkPos 7402996349741614413910397012995911883046728441322514327871294883015530064508954520817 2614773785969181485145233143004267373237641794256018561697446887424 (by decide)),
   (63, Q'.mkPos 1358515703643893836646087712475239306434490411065862384723833862370987703374982829939 1494156449125246562940133224573867070421509596717724892398541078528 (by decide)),
   (64, Q'.mkPos 102211353871120447964346199377537489238625806123623379390439431010891858434600264083 373539112281311640735033306143466767605377399179431223099635269632 (by decide)),
   (65, Q'.mkPos 57520167896408691667427096290741789697190336541456703519887529754345321192827766819 747078224562623281470066612286933535210754798358862446199270539264 (by decide)),
   (66, Q'.mkPos 52825586009579364306133647610724311001824954269270208628016603960384196050839449875 2614773785969181485145233143004267373237641794256018561697446887424 (by decide)),
   (67, Q'.mkPos 103104382291433319804759347402843044772955261744547533117290782074897774571255234347 20918190287753451881161865144034138985901134354048148493579575099392 (by decide)),
   (68, Q'.mkPos 1456925945763616552880600337280058036621301314702461913813591996968600243627991283 1307386892984590742572616571502133686618820897128009280848723443712 (by decide)),
   (69, Q'.mkPos 608183092116523424906271222593314352361517382322097190257487746983787023549524985 2614773785969181485145233143004267373237641794256018561697446887424 (by decide)),
   (70, Q'.mkPos 15120013883726231578297440848308300398954101081269152977175914853129071855444859251066052955521 338838299206760577394155633549789183359395536177524197998510552208217576572977152 (by decide)),
   (71, Q'.mkPos 37139946270759732012072986944808698931510545749520440931045450099454415011653293658759599876189 4743736188894648083518178869697048567031537506485338771979147730915046072021680128 (by decide)),
   (72, Q'.mkPos 82941612426833924495582097614095557480795462005925010727232007682100752858451298963863599680459 66412306644525073169254504175758679938441525090794742807708068232810645008303521792 (by decide)),
   (73, Q'.mkPos 167233432522618012844783550704914800904995652219767088711353206381854623371461928146691590107739 929772293023351024369563058460621519138181351271126399307912955259349030116249305088 (by decide)),
   (74, Q'.mkPos 336952796248049565156264472977439942463805244294467144935300530699449342612291221881477497359 14527692078489859755774422788447211236534083613611349989186139925927328595566395392 (by decide)),
   (75, Q'.mkPos 2464800096168215572591938169564032159226371019076386500300015469172168881100022768326248002303 929772293023351024369563058460621519138181351271126399307912955259349030116249305088 (by decide)),
   (76, Q'.mkPos 61645853985264162081275735633713357278339373937179584015494239541434811819623179878576860647 232443073255837756092390764615155379784545337817781599826978238814837257529062326272 (by decide)),
   (77, Q'.mkPos 1517836678297166042453044752985898726922729540271105605144065878356898241477744555747270589 66412306644525073169254504175758679938441525090794742807708068232810645008303521792 (by decide)),
   (78, Q'.mkPos 13469516808094190700527619366875037439491533524082500249581325149234265544049382370389 8106971025943002095856262716767416984673037730809905127894051297950518189490176 (by decide)),
   (79, Q'.mkPos 6576873516013014582012262817410055266956920558753897905493182812310120206946744655978995 66412306644525073169254504175758679938441525090794742807708068232810645008303521792 (by decide)),
   (80, Q'.mkPos 2156532829117405158694642979802777529465010749964334853158810190771619190805426256913197 464886146511675512184781529230310759569090675635563199653956477629674515058124652544 (by decide)),
   (81, Q'.mkPos 148175713759529975838227405012539319841298561426398154731926156951708816335954070358127 929772293023351024369563058460621519138181351271126399307912955259349030116249305088 (by decide)),
   (82, Q'.mkPos 448088622557244596526725526011184919215166814821505524440357948340309041601864432015 116221536627918878046195382307577689892272668908890799913489119407418628764531163136 (by decide)),
   (83, Q'.mkPos 148616847139725172586820559258816712059964849843617579252242062305201808715981705360996008065 9605034422311206159476933228246514114315558129644540202239127395006554582308425925515328618496 (by decide))]

private def short1Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 165 112 (by decide)),
   (2, Q'.mkPos 11931 1568 (by decide)),
   (3, Q'.mkPos 461259 21952 (by decide)),
   (4, Q'.mkPos 45321 1372 (by decide)),
   (5, Q'.mkPos 634929 21952 (by decide)),
   (6, Q'.mkPos 174879349 15059072 (by decide)),
   (7, Q'.mkPos 79312125 210827008 (by decide)),
   (8, Q'.mkPos 2193605907 2951578112 (by decide)),
   (9, Q'.mkPos 65887483451 41322093568 (by decide))]

private def short2Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 319 112 (by decide)),
   (2, Q'.mkPos 48121 1568 (by decide)),
   (3, Q'.mkPos 4530093 21952 (by decide)),
   (4, Q'.mkPos 21227475 21952 (by decide)),
   (5, Q'.mkPos 9185151 2744 (by decide)),
   (6, Q'.mkPos 133467740281 15059072 (by decide)),
   (7, Q'.mkPos 3866692937923 210827008 (by decide)),
   (8, Q'.mkPos 88684836097273 2951578112 (by decide)),
   (9, Q'.mkPos 1620696451885069 41322093568 (by decide)),
   (10, Q'.mkPos 1687944214841027 41322093568 (by decide)),
   (11, Q'.mkPos 8570472268443683 253097823104 (by decide)),
   (12, Q'.mkPos 11267620636416807 506195646208 (by decide)),
   (13, Q'.mkPos 11751765363710643 1012391292416 (by decide)),
   (14, Q'.mkPos 704682031458507 144627327488 (by decide)),
   (15, Q'.mkPos 61441582383277 36156831872 (by decide)),
   (16, Q'.mkPos 8571293455484666274377 17423626702474969088 (by decide)),
   (17, Q'.mkPos 24149397527838262716695 243930773834649567232 (by decide)),
   (18, Q'.mkPos 22128647287972332302593 3415030833685093941248 (by decide)),
   (19, Q'.mkPos 32760684197886668436901 47810431671591315177472 (by decide)),
   (20, Q'.mkPos 67156767824806710066875 47810431671591315177472 (by decide))]

private def short3Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 515 112 (by decide)),
   (2, Q'.mkPos 128481 1568 (by decide)),
   (3, Q'.mkPos 20650309 21952 (by decide)),
   (4, Q'.mkPos 171460411 21952 (by decide)),
   (5, Q'.mkPos 1096208949 21952 (by decide)),
   (6, Q'.mkPos 3849647706899 15059072 (by decide)),
   (7, Q'.mkPos 226851958912555 210827008 (by decide)),
   (8, Q'.mkPos 11201811662481177 2951578112 (by decide)),
   (9, Q'.mkPos 470057355158635621 41322093568 (by decide)),
   (10, Q'.mkPos 1210055224968143515 41322093568 (by decide)),
   (11, Q'.mkPos 132156057155497304709 2024782584832 (by decide)),
   (12, Q'.mkPos 256614598075692366887 2024782584832 (by decide)),
   (13, Q'.mkPos 436113012874750237967 2024782584832 (by decide)),
   (14, Q'.mkPos 92985627058254985407 289254654976 (by decide)),
   (15, Q'.mkPos 122165692595485369825 289254654976 (by decide)),
   (16, Q'.mkPos 8523124274191290340017326153 17423626702474969088 (by decide)),
   (17, Q'.mkPos 121925378854410018654903909627 243930773834649567232 (by decide)),
   (18, Q'.mkPos 1538939079773827399552120390825 3415030833685093941248 (by decide)),
   (19, Q'.mkPos 17133222177072335316219721083773 47810431671591315177472 (by decide)),
   (20, Q'.mkPos 12010185826179978394476860832195 47810431671591315177472 (by decide)),
   (21, Q'.mkPos 1059387356651417352601807879651 6830061667370187882496 (by decide)),
   (22, Q'.mkPos 575700150808605108181566124597 6830061667370187882496 (by decide)),
   (23, Q'.mkPos 4622924302013180195330325997971651 114792846443490747741110272 (by decide)),
   (24, Q'.mkPos 1938204204171414305235452970679013 114792846443490747741110272 (by decide)),
   (25, Q'.mkPos 710053257482935754577617241724079 114792846443490747741110272 (by decide)),
   (26, Q'.mkPos 225338623160095937961454105786389 114792846443490747741110272 (by decide)),
   (27, Q'.mkPos 61041521910406088699360069490699 114792846443490747741110272 (by decide)),
   (28, Q'.mkPos 1976620198052404265295581990067 16398978063355821105872896 (by decide)),
   (29, Q'.mkPos 368056597067356636919799794157 16398978063355821105872896 (by decide)),
   (30, Q'.mkPos 41180031504710764093474610003280762265 12100716177742297710970518621913088 (by decide)),
   (31, Q'.mkPos 68566729433975726366059823632219289159 169410026488392167953587260706783232 (by decide)),
   (32, Q'.mkPos 65300095292916136717536247562528343633 2371740370837490351350221649894965248 (by decide)),
   (33, Q'.mkPos 10390605386513740555673233006844881973 33204365191724864918903103098529513472 (by decide)),
   (34, Q'.mkPos 25744709131646963796568679548356808235 33204365191724864918903103098529513472 (by decide))]

private def short4Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 753 112 (by decide)),
   (2, Q'.mkPos 277707 1568 (by decide)),
   (3, Q'.mkPos 66822547 21952 (by decide)),
   (4, Q'.mkPos 13161147 343 (by decide)),
   (5, Q'.mkPos 1037479269 2744 (by decide)),
   (6, Q'.mkPos 45651703598537 15059072 (by decide)),
   (7, Q'.mkPos 4286057755138149 210827008 (by decide)),
   (8, Q'.mkPos 343350896374066227 2951578112 (by decide)),
   (9, Q'.mkPos 23826161275794862403 41322093568 (by decide)),
   (10, Q'.mkPos 115526060426372313 46118408 (by decide)),
   (11, Q'.mkPos 2436960801929767194777 253097823104 (by decide)),
   (12, Q'.mkPos 16701625608116496638005 506195646208 (by decide)),
   (13, Q'.mkPos 102685865829245862664677 1012391292416 (by decide)),
   (14, Q'.mkPos 71165150111947684681611 253097823104 (by decide)),
   (15, Q'.mkPos 44668336462611660791757 63274455776 (by decide)),
   (16, Q'.mkPos 28070741550460042023634421772873 17423626702474969088 (by decide)),
   (17, Q'.mkPos 817708735929548791665655223195865 243930773834649567232 (by decide)),
   (18, Q'.mkPos 21773148729930178350617117539051299 3415030833685093941248 (by decide)),
   (19, Q'.mkPos 531056495497648302891826311236994747 47810431671591315177472 (by decide)),
   (20, Q'.mkPos 6632476774556576410986856318913277 373518997434307149824 (by decide)),
   (21, Q'.mkPos 77943059556374854655683317593905215 2988151979474457198592 (by decide)),
   (22, Q'.mkPos 105327331609891388249616690143374413 2988151979474457198592 (by decide)),
   (23, Q'.mkPos 2517147133643606692551657116870017371045 57396423221745373870555136 (by decide)),
   (24, Q'.mkPos 103044041020387809326243198806890734077 2049872257919477638234112 (by decide)),
   (25, Q'.mkPos 217711749796106137773960042082237774563 4099744515838955276468224 (by decide)),
   (26, Q'.mkPos 53001705437239083660081455074801977123 1024936128959738819117056 (by decide)),
   (27, Q'.mkPos 380617416014659725043809124007068382707 8199489031677910552936448 (by decide)),
   (28, Q'.mkPos 39361881109864581379247983111903479171 1024936128959738819117056 (by decide)),
   (29, Q'.mkPos 60008002322784433758998152633928753193 2049872257919477638234112 (by decide)),
   (30, Q'.mkPos 248664435944702940889789132177238914984007247897 12100716177742297710970518621913088 (by decide)),
   (31, Q'.mkPos 2249063970374654434848626901002220075239805702789 169410026488392167953587260706783232 (by decide)),
   (32, Q'.mkPos 18705911014445210212876185179293903211935181764467 2371740370837490351350221649894965248 (by decide)),
   (33, Q'.mkPos 142924199796956581477078659490182866889172904945443 33204365191724864918903103098529513472 (by decide)),
   (34, Q'.mkPos 2236411673591347993697033972239121545859718167889 1037636412241402028715721971829047296 (by decide)),
   (35, Q'.mkPos 32823772793859394443659404357724241261020367739683 33204365191724864918903103098529513472 (by decide)),
   (36, Q'.mkPos 1720128038808885611831015219113729604436760977643 4150545648965608114862887887316189184 (by decide)),
   (37, Q'.mkPos 1314725138448068176357322301542579600049366893679 8301091297931216229725775774632378368 (by decide)),
   (38, Q'.mkPos 8149392761107555668834043538629513131774907863 148233773177343146959388853118435328 (by decide)),
   (39, Q'.mkPos 2157002902438783094695972842882291299015337071286582023 125006731534119636251008997646044759374954496 (by decide)),
   (40, Q'.mkPos 152173324945009816446139620498913453672630167301582197 31251682883529909062752249411511189843738624 (by decide)),
   (41, Q'.mkPos 76693548203466745283937314464921705059021636976507911 62503365767059818125504498823022379687477248 (by decide)),
   (42, Q'.mkPos 8559309177362202339308250147017378221150016448886657 31251682883529909062752249411511189843738624 (by decide)),
   (43, Q'.mkPos 6703635778251333123423070624819470042503438746640457 125006731534119636251008997646044759374954496 (by decide)),
   (44, Q'.mkPos 142179793372684441605039370947123519269472248824725 15625841441764954531376124705755594921869312 (by decide)),
   (45, Q'.mkPos 5876014154438153865509698073296782564818265561351 4464526126218558437536035630215884263391232 (by decide)),
   (46, Q'.mkPos 2480222430728257421147490157260299183710519042773 15625841441764954531376124705755594921869312 (by decide)),
   (47, Q'.mkPos 1942117357421526499403053015925196405758597304585 125006731534119636251008997646044759374954496 (by decide)),
   (48, Q'.mkPos 99028569323152031512290599280442338350819738964306179804889 82648637713323964698725096562236052672126638071268507648 (by decide)),
   (49, Q'.mkPos 75753222018057086359827016053303722637234954490704894554793 1157080927986535505782151351871304737409772932997759107072 (by decide)),
   (50, Q'.mkPos 18672547196160496252540699831333705495591416886528865114067 16199132991811497080950118926198266323736821061968627499008 (by decide)),
   (51, Q'.mkPos 68792278217874993520381493909951187196610809757842793911915 226787861885360959133301664966775728532315494867560784986112 (by decide))]

private def ratio6Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 221 112 (by decide)),
   (2, Q'.mkPos 22347 1568 (by decide)),
   (3, Q'.mkPos 1369563 21952 (by decide)),
   (4, Q'.mkPos 63375 343 (by decide)),
   (5, Q'.mkPos 8585343 21952 (by decide)),
   (6, Q'.mkPos 3342183 5488 (by decide)),
   (7, Q'.mkPos 1108029 1568 (by decide)),
   (8, Q'.mkPos 29952 49 (by decide)),
   (9, Q'.mkPos 610675 1568 (by decide)),
   (10, Q'.mkPos 1950637 10976 (by decide)),
   (11, Q'.mkPos 1207791 21952 (by decide)),
   (12, Q'.mkPos 28431 2744 (by decide)),
   (13, Q'.mkPos 307131969181955 680326948503552 (by decide))]

private theorem head6_bernstein_identity :
    allZero (psub (scaleVar sixAnchorCap headSlack6P)
      (bernTermsP 83 head6Bern)) := by decide
private theorem short1_bernstein_identity :
    allZero (psub (scaleVar sixAnchorCap short1SlackP)
      (bernTermsP 9 short1Bern)) := by decide
private theorem short2_bernstein_identity :
    allZero (psub (scaleVar sixAnchorCap short2SlackP)
      (bernTermsP 20 short2Bern)) := by decide
private theorem short3_bernstein_identity :
    allZero (psub (scaleVar sixAnchorCap short3SlackP)
      (bernTermsP 34 short3Bern)) := by decide
private theorem short4_bernstein_identity :
    allZero (psub (scaleVar sixAnchorCap short4SlackP)
      (bernTermsP 51 short4Bern)) := by decide
private theorem ratio6_bernstein_identity :
    allZero (psub (scaleVar sixAnchorCap ratioSlack6P)
      (bernTermsP 13 ratio6Bern)) := by decide

/-! ## Certified head and short windows -/

theorem strengthened_six_anchor_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ sixAnchorCap) :
    adjCorr w 6 ≤ retuneCube w * coordNormSq w 5 := by
  apply slack_nonneg_to_bound w (adjCorr w 6) (coordNormSq w 5)
    (prefixAP 6) (prefixDP 5) headSlack6P
    (prefixA_eval w 6) (prefixD_eval w 5) rfl
  exact scaled_bernstein_nonneg headSlack6P 83 head6Bern
    head6_bernstein_identity (by decide) hw0 hwc

theorem short_one_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ sixAnchorCap) :
    adjCorr w 1 ≤ retuneCube w * coordNormSq w 1 := by
  apply slack_nonneg_to_bound w (adjCorr w 1) (coordNormSq w 1)
    (prefixAP 1) (prefixDP 1) short1SlackP
    (prefixA_eval w 1) (prefixD_eval w 1) rfl
  exact scaled_bernstein_nonneg short1SlackP 9 short1Bern
    short1_bernstein_identity (by decide) hw0 hwc

theorem short_two_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ sixAnchorCap) :
    adjCorr w 2 ≤ retuneCube w * coordNormSq w 2 := by
  apply slack_nonneg_to_bound w (adjCorr w 2) (coordNormSq w 2)
    (prefixAP 2) (prefixDP 2) short2SlackP
    (prefixA_eval w 2) (prefixD_eval w 2) rfl
  exact scaled_bernstein_nonneg short2SlackP 20 short2Bern
    short2_bernstein_identity (by decide) hw0 hwc

theorem short_three_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ sixAnchorCap) :
    adjCorr w 3 ≤ retuneCube w * coordNormSq w 3 := by
  apply slack_nonneg_to_bound w (adjCorr w 3) (coordNormSq w 3)
    (prefixAP 3) (prefixDP 3) short3SlackP
    (prefixA_eval w 3) (prefixD_eval w 3) rfl
  exact scaled_bernstein_nonneg short3SlackP 34 short3Bern
    short3_bernstein_identity (by decide) hw0 hwc

theorem short_four_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ sixAnchorCap) :
    adjCorr w 4 ≤ retuneCube w * coordNormSq w 4 := by
  apply slack_nonneg_to_bound w (adjCorr w 4) (coordNormSq w 4)
    (prefixAP 4) (prefixDP 4) short4SlackP
    (prefixA_eval w 4) (prefixD_eval w 4) rfl
  exact scaled_bernstein_nonneg short4SlackP 51 short4Bern
    short4_bernstein_identity (by decide) hw0 hwc

/-! ## Exact anchor ratio and PF2 tail -/

theorem tailRatio6_le_retune {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ sixAnchorCap) :
    tailRatio6 w ≤ retuneCube w := by
  have hs := scaled_bernstein_nonneg ratioSlack6P 13 ratio6Bern
    ratio6_bernstein_identity (by decide) hw0 hwc
  have hq : tailRatio6 w ≈ eval ratio6P w := by
    unfold tailRatio6 ratio6P
    exact Q'.eqv_symm (eval_monoP sevenSixths w 13)
  have he : eval ratioSlack6P w ≈ retuneCube w + -(tailRatio6 w) := by
    refine Q'.eqv_trans _ _ _ (eval_psub _ _ w) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (retune_eval w))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hq))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv he))

theorem coeffW_six_eq_tailRatio6_mul_five (w : Q') :
    coeffW w 6 ≈ tailRatio6 w * coeffW w 5 := by
  have hc6 := hcoeff w 6
  have hq : tailRatio6 w ≈ eval ratio6P w := by
    unfold tailRatio6 ratio6P
    exact Q'.eqv_symm (eval_monoP sevenSixths w 13)
  have hc5 := hcoeff w 5
  refine Q'.eqv_trans _ _ _ hc6 ?_
  refine Q'.eqv_trans _ _ _
    (poly_eqv (coeffPoly 6) (pmul ratio6P (coeffPoly 5)) w (by decide)) ?_
  exact Q'.eqv_symm (hEvalMul hq hc5)

theorem adjacent_tail6_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    {a : Nat} (ha : 5 ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      tailRatio6 w * (coeffW w a * coeffW w a) := by
  by_cases h5 : a = 5
  · subst a
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 5) _ _
        (coeffW_six_eq_tailRatio6_mul_five w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · have ha6 : 5 < a := by omega
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := 5) (N := a) ha6
    have hr : coeffW w (a + 1) * coeffW w 5 ≤ coeffW w a * coeffW w 6 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hc5p := FusionResidualBound.coeffW_pos hwp 5
    have hR : coeffW w 6 * (coeffW w a * coeffW w a) ≈
        coeffW w 5 * (tailRatio6 w * (coeffW w a * coeffW w a)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (coeffW_six_eq_tailRatio6_mul_five w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    have hcancel : coeffW w 5 * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w 5 * (tailRatio6 w * (coeffW w a * coeffW w a)) :=
      Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hR)
    exact Q'.le_of_mul_le_mul_left hcancel hc5p

private def edgeTail (w : Q') (j : Nat) : Q' :=
  coeffW w (6 + j) * coeffW w (6 + j + 1)
private def squareTail (w : Q') (j : Nat) : Q' :=
  coeffW w (6 + j) * coeffW w (6 + j)

private theorem tail_sum_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hwc : w ≤ sixAnchorCap) (M : Nat) :
    fsum (edgeTail w) M ≤ retuneCube w * fsum (squareTail w) M := by
  have hterm : ∀ j, edgeTail w j ≤ retuneCube w * squareTail w j := by
    intro j
    have ht := adjacent_tail6_le hw0 hw1 hwp (a := 6 + j) (by omega)
    exact Q'.le_trans' _ _ _ ht
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (tailRatio6_le_retune hw0 hwc)
        (Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (6 + j)) (coeffW_nonneg hw0 (6 + j))))
  have hsum : fsum (edgeTail w) M ≤
      fsum (fun j => retuneCube w * squareTail w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact CharacterTail.finSum_le_termwise _ _ hterm M
  have hfactor : retuneCube w * fsum (squareTail w) M ≈
      fsum (fun j => retuneCube w * squareTail w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact const_mul_finSum (squareTail w) (retuneCube w) M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hfactor)

/-! ## Uniform all-cutoff theorem -/

theorem six_anchor_retune_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ sixAnchorCap) (N : Nat) :
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
    rcases Nat.le_total N 6 with hsmall | hlarge
    · have cases : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Q'.mul_nonneg _ _
          (qpow_nonneg _
            (Q'.mul_nonneg _ _ (by decide)
              (Q'.zero_le_add _ _ (by decide) hw0)) 3)
          (coordNormSq_nonneg hw0 0)
      · exact short_one_head hw0 hwc
      · exact short_two_head hw0 hwc
      · exact short_three_head hw0 hwc
      · exact short_four_head hw0 hwc
      · have hA56 : adjCorr w 5 ≤ adjCorr w 6 := by
          unfold adjCorr
          exact AFRateCalibration.fsum_le_of_le
            (fun i => Q'.mul_nonneg _ _
              (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 (i + 1))) (by omega)
        exact Q'.le_trans' _ _ _ hA56 (strengthened_six_anchor_head hw0 hwc)
      · have hD56 : coordNormSq w 5 ≤ coordNormSq w 6 := by
          unfold coordNormSq
          exact AFRateCalibration.fsum_le_of_le
            (fun i => Q'.mul_nonneg _ _
              (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 i)) (by omega)
        have hr0 : (0 : Q') ≤ retuneCube w := qpow_nonneg _
          (Q'.mul_nonneg _ _ (by decide)
            (Q'.zero_le_add _ _ (by decide) hw0)) 3
        exact Q'.le_trans' _ _ _ (strengthened_six_anchor_head hw0 hwc)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hD56 hr0)
    · obtain ⟨M, rfl⟩ := Nat.le.dest hlarge
      have hA : adjCorr w (6 + M) ≈
          adjCorr w 6 + fsum (edgeTail w) M := by
        unfold adjCorr edgeTail
        exact FusionCoreStepRoundH.fsum_split_at
          (fun a => coeffW w a * coeffW w (a + 1)) 6 M
      have hD : coordNormSq w (6 + M) ≈
          coordNormSq w 5 + fsum (squareTail w) (M + 1) := by
        unfold coordNormSq squareTail
        rw [show 6 + M + 1 = 6 + (M + 1) by omega]
        exact FusionCoreStepRoundH.fsum_split_at
          (fun a => coeffW w a * coeffW w a) 6 (M + 1)
      have hsquare0 : ∀ j, (0 : Q') ≤ squareTail w j := by
        intro j
        unfold squareTail
        exact Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (6 + j)) (coeffW_nonneg hw0 (6 + j))
      have htailPrefix : fsum (squareTail w) M ≤
          fsum (squareTail w) (M + 1) :=
        AFRateCalibration.fsum_le_of_le hsquare0 (by omega)
      have hprefix : coordNormSq w 5 + fsum (squareTail w) M ≤
          coordNormSq w (6 + M) :=
        Q'.le_trans' _ _ _
          (Q'.add_le_add_left (coordNormSq w 5) _ _ htailPrefix)
          (Q'.ge_of_eqv hD)
      have hr0 : (0 : Q') ≤ retuneCube w := qpow_nonneg _
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.zero_le_add _ _ (by decide) hw0)) 3
      have hpaid : adjCorr w 6 + fsum (edgeTail w) M ≤
          retuneCube w * coordNormSq w 5 +
            retuneCube w * fsum (squareTail w) M :=
        AFRateCalibration.q_add_le_add
          (strengthened_six_anchor_head hw0 hwc)
          (tail_sum_le hw0 hw1 hwp hwc M)
      have hcollect : retuneCube w * coordNormSq w 5 +
          retuneCube w * fsum (squareTail w) M ≈
          retuneCube w * (coordNormSq w 5 + fsum (squareTail w) M) :=
        Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
        (Q'.le_trans' _ _ _ hpaid
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
            (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hr0)))

theorem six_anchor_ratio_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ sixAnchorCap) (N : Nat) :
    Q'.divPos (adjCorr w N) (coordNormSq w N) (coordNormSq_pos hw0 N) ≤
      retuneCube w :=
  Q'.divPos_le_of_le_mul _ _ _ (six_anchor_retune_all_cutoffs hw0 hwc N)

theorem six_anchor_lamPW_le_retune {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ sixAnchorCap) (N : Nat) :
    lamPW w N 1 ≤ retuneCube w := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hwc (by decide)
  have heq : lamPW w N 1 ≈
      Q'.divPos (adjCorr w N) (coordNormSq w N) (coordNormSq_pos hw0 N) :=
    Q'.eqv_trans _ _ _ (lamPW_eq_vacNorm_p2 hw0 hw1 N 0)
      (vacNorm_fundamental_eq_ratio hw0 hw1 N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (six_anchor_ratio_all_cutoffs hw0 hwc N)

/-! ## Harmonic scales ten through twelve -/

theorem harmW_ten_mem_window : harmW 10 ≤ sixAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit sixAnchorCap
  decide

theorem harmW_eleven_mem_window : harmW 11 ≤ sixAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit sixAnchorCap
  decide

theorem harmW_twelve_mem_window : harmW 12 ≤ sixAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit sixAnchorCap
  decide

theorem harmonicMass_k10_retune_floor :
    (1 : Q') - retuneCube (harmW 10) ≤ harmonicMass 10 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (six_anchor_lamPW_le_retune
      (harmW_nonneg 10) harmW_ten_mem_window (Ncut 10)))

theorem harmonicMass_k11_retune_floor :
    (1 : Q') - retuneCube (harmW 11) ≤ harmonicMass 11 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (six_anchor_lamPW_le_retune
      (harmW_nonneg 11) harmW_eleven_mem_window (Ncut 11)))

theorem harmonicMass_k12_retune_floor :
    (1 : Q') - retuneCube (harmW 12) ≤ harmonicMass 12 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (six_anchor_lamPW_le_retune
      (harmW_nonneg 12) harmW_twelve_mem_window (Ncut 12)))

theorem initial_thirteen_retune {k : Nat} (hk : k ≤ 12) :
    adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k) := by
  by_cases hk9 : k ≤ 9
  · exact FiveAnchorWindowRetune.initial_ten_retune hk9
  · have cases : k = 10 ∨ k = 11 ∨ k = 12 := by omega
    rcases cases with rfl | rfl | rfl
    · exact six_anchor_retune_all_cutoffs
        (harmW_nonneg 10) harmW_ten_mem_window (Ncut 10)
    · exact six_anchor_retune_all_cutoffs
        (harmW_nonneg 11) harmW_eleven_mem_window (Ncut 11)
    · exact six_anchor_retune_all_cutoffs
        (harmW_nonneg 12) harmW_twelve_mem_window (Ncut 12)

end YMGap.Continuum.SixAnchorWindowRetune

#print axioms YMGap.Continuum.SixAnchorWindowRetune.strengthened_six_anchor_head
#print axioms YMGap.Continuum.SixAnchorWindowRetune.short_one_head
#print axioms YMGap.Continuum.SixAnchorWindowRetune.short_two_head
#print axioms YMGap.Continuum.SixAnchorWindowRetune.short_three_head
#print axioms YMGap.Continuum.SixAnchorWindowRetune.short_four_head
#print axioms YMGap.Continuum.SixAnchorWindowRetune.tailRatio6_le_retune
#print axioms YMGap.Continuum.SixAnchorWindowRetune.coeffW_six_eq_tailRatio6_mul_five
#print axioms YMGap.Continuum.SixAnchorWindowRetune.adjacent_tail6_le
#print axioms YMGap.Continuum.SixAnchorWindowRetune.six_anchor_retune_all_cutoffs
#print axioms YMGap.Continuum.SixAnchorWindowRetune.six_anchor_ratio_all_cutoffs
#print axioms YMGap.Continuum.SixAnchorWindowRetune.six_anchor_lamPW_le_retune
#print axioms YMGap.Continuum.SixAnchorWindowRetune.harmW_ten_mem_window
#print axioms YMGap.Continuum.SixAnchorWindowRetune.harmW_eleven_mem_window
#print axioms YMGap.Continuum.SixAnchorWindowRetune.harmW_twelve_mem_window
#print axioms YMGap.Continuum.SixAnchorWindowRetune.harmonicMass_k10_retune_floor
#print axioms YMGap.Continuum.SixAnchorWindowRetune.harmonicMass_k11_retune_floor
#print axioms YMGap.Continuum.SixAnchorWindowRetune.harmonicMass_k12_retune_floor
#print axioms YMGap.Continuum.SixAnchorWindowRetune.initial_thirteen_retune
