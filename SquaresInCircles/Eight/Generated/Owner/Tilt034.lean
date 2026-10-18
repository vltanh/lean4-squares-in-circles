module

public import SquaresInCircles.Eight.Candidate.Dual

/-! Generated F8 rational data and algebraic proof source. Uncompiled.
No replay status or external decision procedure is a theorem premise. -/

@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open scoped BigOperators
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

def tilt_034_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (5517979/100000000), (363539/100000000)]
    alternative := .zero
    polynomial := [(-44597946939038874892329668060094503678378169/3245132521928705890614473375856250000000000000), (4215104808669/6597757812500), (-12027386743083597940116422696173620300709628169/1622566260964352945307236687928125000000000000), (4215104808669/6597757812500), (-2182743230838923364121865065844286008885534379/295012047448064171874043034168750000000000000)]
    bernstein := [(2770065780624929744373507118340058765262922282391/34027680793139147079569620345618432000000000000000000000), (503516697168181143480983331878705177077678597186149/17013840396569573539784810172809216000000000000000000000), (400254122653788184394495000618583997278573820804111/8506920198284786769892405086404608000000000000000000000), (17159356534367386710782757569506984013622986128833/327189238395568721918938657169408000000000000000000000), (7488138826900006904635744910886858104285858868387/163594619197784360959469328584704000000000000000000000)]
    reserve := (40703/500000000000) }

theorem tilt_034_000_valid : tilt_034_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_000]
  · intro i; fin_cases i <;> norm_num [tilt_034_000]
  · norm_num [tilt_034_000]
  · norm_num [tilt_034_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_000]

def tilt_034_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1471/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (5517979/100000000), (367493/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1068670929740296456442897290730007958933819579/78730270097974362950412560807850000000000000000), (19609775686520444213073/31035261590900000000000), (-288792725628309055232419725745725183266619319579/39365135048987181475206280403925000000000000000), (19609775686520444213073/31035261590900000000000), (-576516780326877814008396554200720358574304819579/78730270097974362950412560807850000000000000000)]
    bernstein := [(8256600561973339415706950217728848253765307620279381/825546716982535656050918013616521216000000000000000000000), (5347798809615811866895083068036411144865944304683253/137591119497089276008486335602753536000000000000000000000), (34549175488480789121823986410238457727903714929835703/619160037736901742038188510212390912000000000000000000000), (160863490102305797462352916591154659578825964912401/2645983067251716846317044915437568000000000000000000000), (213722240826236253703776844434827749200980125765817/3968974600877575269475567373156352000000000000000000000)]
    reserve := (2500343/250000000000) }

theorem tilt_034_001_valid : tilt_034_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_001]
  · intro i; fin_cases i <;> norm_num [tilt_034_001]
  · norm_num [tilt_034_001]
  · norm_num [tilt_034_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_001]

def tilt_034_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4357/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (239/6250000), (844513/20000000), (2184013/50000000), (1/100000000), (5517979/100000000), (71917/20000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-8523430812337954814520440813195987736831205239/613720857938341374399354551158225000000000000000), (19618511981670777316527/30367420710500000000000), (-2298542376466933423943838061901876501557709455239/306860428969170687199677275579112500000000000000), (19618511981670777316527/30367420710500000000000), (-4588561322121528893073155682990557015378587705239/613720857938341374399354551158225000000000000000)]
    bernstein := [(114885453590384036664025702143545712311098732981952121/6435329623335542450021775978352869376000000000000000000000), (154544229521581926019776911193298459697028466011692619/3217664811667771225010887989176434688000000000000000000000), (106220944411230614465152699414446550619242460882285441/1608832405833885612505443994588217344000000000000000000000), (4444648817932483155907419190501324947117837661067823/61878169455149446634824769022623744000000000000000000000), (2024687675054459113745760151677850662727476069005997/30939084727574723317412384511311872000000000000000000000)]
    reserve := (8926151/500000000000) }

theorem tilt_034_002_valid : tilt_034_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_002]
  · intro i; fin_cases i <;> norm_num [tilt_034_002]
  · norm_num [tilt_034_002]
  · norm_num [tilt_034_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_002]

def tilt_034_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5470259/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (5517979/100000000), (367493/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-2766060539856952346048775496357667745320592171/204596670574455113051936401023370000000000000000), (19609775686520444213073/31035261590900000000000), (-750475722430425832468384567100325113123311692171/102298335287227556525968200511685000000000000000), (19609775686520444213073/31035261590900000000000), (-1498185384320994712590720358704292558501302792171/204596670574455113051936401023370000000000000000)]
    bernstein := [(138221507766229642410906553037915184491325941754928869/2145351584442798446235472636394812211200000000000000000000), (100081961950591216688086363322920175027950146743246991/1072675792221399223117736318197406105600000000000000000000), (59126450369046357287258938600668740655503839049686349/536337896110699611558868159098703052800000000000000000000), (2377288520293859540711159920975421879568002616032547/20628380619642292752264159965334732800000000000000000000), (1117066852106965212214902709301986719268815778679433/10314190309821146376132079982667366400000000000000000000)]
    reserve := (6442837/100000000000) }

theorem tilt_034_003_valid : tilt_034_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_003]
  · intro i; fin_cases i <;> norm_num [tilt_034_003]
  · norm_num [tilt_034_003]
  · norm_num [tilt_034_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_003]

def tilt_034_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1095143/20000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (5517979/100000000), (71917/20000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-554012717811691576450368358512749795476998387/40078734513049846903829337029050000000000000000), (19618511981670777316527/30367420710500000000000), (-150102557737224759832102311091851764610855498387/20039367256524923451914668514525000000000000000), (19618511981670777316527/30367420710500000000000), (-299651102756637828087754253825190779426233998387/40078734513049846903829337029050000000000000000)]
    bernstein := [(34915332814866655939250151191591564924372417218814493/420255991207557562670297509045731328000000000000000000000), (23800568813197947160967425226685788271966224551791927/210127995603778781335148754522865664000000000000000000000), (13791664234395944003856716267091490384729288851754053/105063997801889390667574377261432832000000000000000000000), (553942948801742308863292892524850532793975140991659/4040922992380361179522091433132032000000000000000000000), (264082899594405332236681806479725809948887880634401/2020461496190180589761045716566016000000000000000000000)]
    reserve := (41540553/500000000000) }

theorem tilt_034_004_valid : tilt_034_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_004]
  · intro i; fin_cases i <;> norm_num [tilt_034_004]
  · norm_num [tilt_034_004]
  · norm_num [tilt_034_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_004]

def tilt_034_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (545757/12500000), (1/100000000), (5517979/100000000), (367493/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-9261136112418417829482671019368476968573379163/682021273966388206430966608513200000000000000000), (19609775686520444213073/31035261590900000000000), (-2501744981170908785280482541529866261948369379163/341010636983194103215483304256600000000000000000), (19609775686520444213073/31035261590900000000000), (-4994228826229399152731482412040364046928165379163/682021273966388206430966608513200000000000000000)]
    bernstein := [(34719214451571587899277735957296123177932388460419957/7151511393705794799465572424883372032000000000000000000000), (40191622923716504862912355405079385027438350303435541/1191918565617632466577595404147228672000000000000000000000), (271679769267715808388412849699810520156151746557223191/5363633545279346099599179318662529024000000000000000000000), (1275508426244277195193476819733586035005628344222897/22921510877262162818799911618215936000000000000000000000), (1674380304326585441853953537073212920934381210524249/34382266315893244228199867427323904000000000000000000000)]
    reserve := (4854807/1000000000000) }

theorem tilt_034_005_valid : tilt_034_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_005]
  · intro i; fin_cases i <;> norm_num [tilt_034_005]
  · norm_num [tilt_034_005]
  · norm_num [tilt_034_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_005]

def tilt_034_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (1092499/25000000), (1/100000000), (5517979/100000000), (71917/20000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-73841037254984526503339073564946920091102199/5343577864850067370359459737512000000000000000), (19618511981670777316527/30367420710500000000000), (-20012701497683703496248944516662751733765742199/2671788932425033685179729868756000000000000000), (19618511981670777316527/30367420710500000000000), (-39951561958112422465994549959760556547440382199/5343577864850067370359459737512000000000000000)]
    bernstein := [(4905777017130604191929985809498058100224815103265561/56031475032130242429420408537213829120000000000000000000), (3298584607710534357191580186675709101372854604772779/28015737516065121214710204268606914560000000000000000000), (5704417403425223248189072489845304224619411131411043/42023606274097681822065306402910371840000000000000000000), (76266305641067929334559036050024055672379412022543/538764183001252331052119312857825280000000000000000000), (36414922174395121013673888304832828427673176176077/269382091500626165526059656428912640000000000000000000)]
    reserve := (1751079/20000000000) }

theorem tilt_034_006_valid : tilt_034_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_006]
  · intro i; fin_cases i <;> norm_num [tilt_034_006]
  · norm_num [tilt_034_006]
  · norm_num [tilt_034_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_006]

def tilt_034_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (4220523/100000000), (2184013/50000000), (1/100000000), (5517979/100000000), (367493/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-24735287995087669539418608295608872277111733/1821578628335442220472386607881250000000000000), (10891727126731178149187/17233473987100000000000), (-6682085890616204601384079508421864873781736733/910789314167721110236193303940625000000000000), (10891727126731178149187/17233473987100000000000), (-13339436493237321533228740408548120875286361733/1821578628335442220472386607881250000000000000)]
    bernstein := [(201649147323160687688468375326813344433389367254187/19100636317854646617740532597456896000000000000000000000), (377466172455861810201460720613576597841499693278593/9550318158927323308870266298728448000000000000000000000), (270068481197061334713012276844329712908543735060227/4775159079463661654435133149364224000000000000000000000), (11323005526389733745459173289651743939629638371181/183659964594756217478274351898624000000000000000000000), (5032661745845662315386565409002900284897176988359/91829982297378108739137175949312000000000000000000000)]
    reserve := (2111439/200000000000) }

theorem tilt_034_007_valid : tilt_034_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_007]
  · intro i; fin_cases i <;> norm_num [tilt_034_007]
  · norm_num [tilt_034_007]
  · norm_num [tilt_034_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_007]

def tilt_034_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (4224607/100000000), (2184013/50000000), (1/100000000), (5517979/100000000), (71917/20000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-44376800968639911655193894105670203221653609/3211389375686092773466691177056250000000000000), (98116433526521434915953/151910530809500000000000), (-12026740337120161650302102772858441526084278609/1605694687843046386733345588528125000000000000), (98116433526521434915953/151910530809500000000000), (-24009103873271683388949011651611212848946903609/3211389375686092773466691177056250000000000000)]
    bernstein := [(2756408216983871190683643704656995583772304710362551/33673858259994204160306091676729344000000000000000000000), (1884745177850478756531292298142345017619282219916389/16836929129997102080153045838364672000000000000000000000), (1093079129339606710077034094874317184924977224351471/8418464564998551040076522919182336000000000000000000000), (43891735751512361966579868970016896285075966310913/323787098653790424618327804583936000000000000000000000), (20897077717282053491017850701988121934429099533507/161893549326895212309163902291968000000000000000000000)]
    reserve := (3274241/40000000000) }

theorem tilt_034_008_valid : tilt_034_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_008]
  · intro i; fin_cases i <;> norm_num [tilt_034_008]
  · norm_num [tilt_034_008]
  · norm_num [tilt_034_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_008]

def tilt_034_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (4366057/100000000), (1/100000000), (5517979/100000000), (367493/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-4630594328434031502409004131606826091116424819/341010715088155877227109177924575000000000000000), (19609775686520444213073/31035261590900000000000), (-1250872802296510629494052966284342891271628674819/170505357544077938613554588962287500000000000000), (19609775686520444213073/31035261590900000000000), (-2497115010264587227485696928437078956452140924819/341010715088155877227109177924575000000000000000)]
    bernstein := [(17094374659136485796871117601973728463692298833431741/3575756515842781371192932333514391552000000000000000000000), (60154813113881240201218658231350810476788611221275799/1787878257921390685596466166757195776000000000000000000000), (45213645755086695092374264584937287905445293497055461/893939128960695342798233083378597888000000000000000000000), (1910711731532816265195791811715585678513063929407883/34382274190795974723008964745330688000000000000000000000), (835914496790740650625565895130255051934652353366337/17191137095397987361504482372665344000000000000000000000)]
    reserve := (4780631/1000000000000) }

theorem tilt_034_009_valid : tilt_034_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_009]
  · intro i; fin_cases i <;> norm_num [tilt_034_009]
  · norm_num [tilt_034_009]
  · norm_num [tilt_034_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_009]

def tilt_034_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (4369997/100000000), (1/100000000), (5517979/100000000), (71917/20000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-919400453581591916454789729451720868688393349/66794738595473542362134679226675000000000000000), (19618511981670777316527/30367420710500000000000), (-250155213242346503290605322560377303358763143349/33397369297736771181067339613337500000000000000), (19618511981670777316527/30367420710500000000000), (-499391026031111414664755855391302885848837893349/66794738595473542362134679226675000000000000000)]
    bernstein := [(99329520316750949511147755136426293569900946044910411/700393598174872651559177334047899648000000000000000000000), (60238372413951762931160062908630120411754544389516929/350196799087436325779588667023949824000000000000000000000), (99818022772648766333175436487682336678962843024151593/525295198631154488669383000535924736000000000000000000000), (1318926317271056382295278458312030278275747744498093/6734553828604544726530551288922112000000000000000000000), (638010218304838688443030914101467215155085950727527/3367276914302272363265275644461056000000000000000000000)]
    reserve := (141819571/1000000000000) }

theorem tilt_034_010_valid : tilt_034_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_010]
  · intro i; fin_cases i <;> norm_num [tilt_034_010]
  · norm_num [tilt_034_010]
  · norm_num [tilt_034_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_010]

def tilt_034_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3657/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (5517979/100000000), (367493/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-356246958938424625220590665222652238726849193/26243423365991454316804186935950000000000000000), (19609775686520444213073/31035261590900000000000), (-96264265191794677550546200150221044007955349193/13121711682995727158402093467975000000000000000), (19609775686520444213073/31035261590900000000000), (-192172283424650930475871809635219435777183849193/26243423365991454316804186935950000000000000000)]
    bernstein := [(2506909790366083061686899233195740895013679462757127/275182238994178552016972671205507072000000000000000000000), (5225138066599974550811676002522782540234146870179253/137591119497089276008486335602753536000000000000000000000), (3777458932775962197193124780489639676618915853747967/68795559748544638004243167801376768000000000000000000000), (158504008719331925974548978361685821655686065544401/2645983067251716846317044915437568000000000000000000000), (70060845244083063301218332605225162391034332169939/1322991533625858423158522457718784000000000000000000000)]
    reserve := (4554999/500000000000) }

theorem tilt_034_011_valid : tilt_034_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_011]
  · intro i; fin_cases i <;> norm_num [tilt_034_011]
  · norm_num [tilt_034_011]
  · norm_num [tilt_034_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_011]

def tilt_034_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4333/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (3803/100000000), (5517979/100000000), (71917/20000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-271237574768042404895433736605185502198704551489/19531216926690479053060630611336650000000000000000), (19618511981670777316527/30367420710500000000000), (-73149413728110524154676144305644951142874855051489/9765608463345239526530315305668325000000000000000), (19618511981670777316527/30367420710500000000000), (-146027589881453005904456854874684716783551005551489/19531216926690479053060630611336650000000000000000)]
    bernstein := [(3807321782713604144026818395910550833986957278635205871/204799653201213957635421038039129391104000000000000000000000), (4993854696540776646478192873317707182075586090236213869/102399826600606978817710519019564695552000000000000000000000), (10254622705365448099110218398014693696626517057936467573/153599739900910468226565778529347043328000000000000000000000), (142901879799482170324816814866910127728829232169804073/1969227434627057284955971519607013376000000000000000000000), (65161394786940988639590711222563920673470057747094747/984613717313528642477985759803506688000000000000000000000)]
    reserve := (18590469/1000000000000) }

theorem tilt_034_012_valid : tilt_034_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_012]
  · intro i; fin_cases i <;> norm_num [tilt_034_012]
  · norm_num [tilt_034_012]
  · norm_num [tilt_034_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_012]

def tilt_034_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (1103047/20000000), (367493/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-70918059534646422997994824142827983435719037/5246074588828042968229474593350000000000000000), (19609775686520444213073/31035261590900000000000), (-19242983010796220854600876525142237558186219037/2623037294414021484114737296675000000000000000), (19609775686520444213073/31035261590900000000000), (-38415047962057795286203758226141647132936719037/5246074588828042968229474593350000000000000000)]
    bernstein := [(3614130542948317506628856130058998825234033101049843/55009079080549539834541895511965696000000000000000000000), (2601204172065743979511221701524022678811552033635577/27504539540274769917270947755982848000000000000000000000), (1533565385754998992643998360029406960869269186211403/13752269770137384958635473877991424000000000000000000000), (61629383889790979118757692253683398573636681888709/528933452697591729178287456845824000000000000000000000), (28979417589243960392369570265391746198950237634351/264466726348795864589143728422912000000000000000000000)]
    reserve := (32850309/500000000000) }

theorem tilt_034_013_valid : tilt_034_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_013]
  · intro i; fin_cases i <;> norm_num [tilt_034_013]
  · norm_num [tilt_034_013]
  · norm_num [tilt_034_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_013]

def tilt_034_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (1380181/25000000), (71917/20000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-710379199514754508893007528516001690523897/51382942462480383033868990258000000000000000), (19618511981670777316527/30367420710500000000000), (-192439094625350581725022840242580800432783897/25691471231240191516934495129000000000000000), (19618511981670777316527/30367420710500000000000), (-384167810051186408941152672956645599175043897/51382942462480383033868990258000000000000000)]
    bernstein := [(43635600669222762722495012552632653469446284371383/538789202755378301201222103287726080000000000000000000), (29949647044797187050379848754331425521143588381637/269394601377689150600611051643863040000000000000000000), (17399630423804011731991769148295307461565094269743/134697300688844575300305525821931520000000000000000000), (699336008959632281351981624963481682579569933729/5180665411109406742319443300843520000000000000000000), (333143466717574182542099676707051898700202296131/2590332705554703371159721650421760000000000000000000)]
    reserve := (80988261/1000000000000) }

theorem tilt_034_014_valid : tilt_034_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_014]
  · intro i; fin_cases i <;> norm_num [tilt_034_014]
  · norm_num [tilt_034_014]
  · norm_num [tilt_034_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_014]

def tilt_034_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3657/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (5517979/100000000), (367493/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-356246958938424625220590665222652238726849193/26243423365991454316804186935950000000000000000), (19609775686520444213073/31035261590900000000000), (-96264265191794677550546200150221044007955349193/13121711682995727158402093467975000000000000000), (19609775686520444213073/31035261590900000000000), (-192172283424650930475871809635219435777183849193/26243423365991454316804186935950000000000000000)]
    bernstein := [(2506909790366083061686899233195740895013679462757127/275182238994178552016972671205507072000000000000000000000), (5225138066599974550811676002522782540234146870179253/137591119497089276008486335602753536000000000000000000000), (3777458932775962197193124780489639676618915853747967/68795559748544638004243167801376768000000000000000000000), (158504008719331925974548978361685821655686065544401/2645983067251716846317044915437568000000000000000000000), (70060845244083063301218332605225162391034332169939/1322991533625858423158522457718784000000000000000000000)]
    reserve := (4554999/500000000000) }

theorem tilt_034_015_valid : tilt_034_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_015]
  · intro i; fin_cases i <;> norm_num [tilt_034_015]
  · norm_num [tilt_034_015]
  · norm_num [tilt_034_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_015]

def tilt_034_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4333/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (3803/100000000), (5517979/100000000), (71917/20000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-271237574768042404895433736605185502198704551489/19531216926690479053060630611336650000000000000000), (19618511981670777316527/30367420710500000000000), (-73149413728110524154676144305644951142874855051489/9765608463345239526530315305668325000000000000000), (19618511981670777316527/30367420710500000000000), (-146027589881453005904456854874684716783551005551489/19531216926690479053060630611336650000000000000000)]
    bernstein := [(3807321782713604144026818395910550833986957278635205871/204799653201213957635421038039129391104000000000000000000000), (4993854696540776646478192873317707182075586090236213869/102399826600606978817710519019564695552000000000000000000000), (10254622705365448099110218398014693696626517057936467573/153599739900910468226565778529347043328000000000000000000000), (142901879799482170324816814866910127728829232169804073/1969227434627057284955971519607013376000000000000000000000), (65161394786940988639590711222563920673470057747094747/984613717313528642477985759803506688000000000000000000000)]
    reserve := (18590469/1000000000000) }

theorem tilt_034_016_valid : tilt_034_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_016]
  · intro i; fin_cases i <;> norm_num [tilt_034_016]
  · norm_num [tilt_034_016]
  · norm_num [tilt_034_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_016]

def tilt_034_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (1378809/25000000), (367493/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-70918188766087616049326080388263857717587821/5246075540024970901135863573960000000000000000), (19609775686520444213073/31035261590900000000000), (-19242986616228576652664402475336653122256387821/2623037770012485450567931786980000000000000000), (19609775686520444213073/31035261590900000000000), (-38415055043691065689279478870285042386795187821/5246075540024970901135863573960000000000000000)]
    bernstein := [(3612906909167697270217285019424452461800839009489219/55009089054572238876294392829286809600000000000000000000), (288954713508872970419984109178076057331326310362849/3056060503031791048683021823849267200000000000000000000), (4599778538883723551575226403570244555410241176406097/41256816790929179157220794621965107200000000000000000000), (6846402051393046568183879144340025750704079822733/58770394289072904782365804304793600000000000000000000), (28973533739239859844396701200794487251761605704383/264466774300828071520646119371571200000000000000000000)]
    reserve := (32839181/500000000000) }

theorem tilt_034_017_valid : tilt_034_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_017]
  · intro i; fin_cases i <;> norm_num [tilt_034_017]
  · norm_num [tilt_034_017]
  · norm_num [tilt_034_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_017]

def tilt_034_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (220829/4000000), (71917/20000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1419130348189243499120232976045125377114107/102765903539527428875146224025000000000000000), (19618511981670777316527/30367420710500000000000), (-384876630657676729998270841015988939281364107/51382951769763714437573112012500000000000000), (19618511981670777316527/30367420710500000000000), (-768334130967164216497421449055932753185614107/102765903539527428875146224025000000000000000)]
    bernstein := [(104401670242224046801479866426195176148750142971573/1077578600698635132601853270032384000000000000000000000), (68465617078046516584426588732475592108924422770047/538789300349317566300926635016192000000000000000000000), (117248939937836043238950516414997734080785009354199/808183950523976349451389952524288000000000000000000000), (1563452408048441227662417223559932807540637103699/10361332699025337813479358365696000000000000000000000), (748688366795578478392681633139955192694793335961/5180666349512668906739679182848000000000000000000000)]
    reserve := (96885433/1000000000000) }

theorem tilt_034_018_valid : tilt_034_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_018]
  · intro i; fin_cases i <;> norm_num [tilt_034_018]
  · norm_num [tilt_034_018]
  · norm_num [tilt_034_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_018]

def tilt_034_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (5517979/100000000), (363539/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-88164062831176431952261048587577182736015713/6490265043857411781228946751712500000000000000), (4215104808669/6597757812500), (-48109593002983359170295906159672684814465401051/6490265043857411781228946751712500000000000000), (4215104808669/6597757812500), (-2182792224552371942651983868685686710533153879/295012047448064171874043034168750000000000000)]
    bernstein := [(5412122738555273109724433695079337215831396925147891/34027680793139147079569620345618432000000000000000000000), (3208184782039980600576596896908696609257672362790649/17013840396569573539784810172809216000000000000000000000), (1752583918363379474127250519811418764844472659329611/8506920198284786769892405086404608000000000000000000000), (69171872929106289509366557772451786460513580955333/327189238395568721918938657169408000000000000000000000), (33494310600178897479035807049199869841261884451887/163594619197784360959469328584704000000000000000000000)]
    reserve := (15905059/100000000000) }

theorem tilt_034_019_valid : tilt_034_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_019]
  · intro i; fin_cases i <;> norm_num [tilt_034_019]
  · norm_num [tilt_034_019]
  · norm_num [tilt_034_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_019]

def tilt_034_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5472987/100000000), (1/100000000), (844513/20000000), (2184013/50000000), (1/100000000), (5517979/100000000), (363539/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-89175370283779705700063893401245350496140713/6490265043857411781228946751712500000000000000), (4215104808669/6597757812500), (-48107488275840923756369409073902624513080151051/6490265043857411781228946751712500000000000000), (4215104808669/6597757812500), (-2182650586616233820484970235477335416481091379/295012047448064171874043034168750000000000000)]
    bernstein := [(128215403000720842446381502304652539857158652835391/34027680793139147079569620345618432000000000000000000000), (566583052341207044814145024830365418282736923853149/17013840396569573539784810172809216000000000000000000000), (431963578464045334259632009295768452769962684517111/8506920198284786769892405086404608000000000000000000000), (18385901622378445823181046199923397222208812767833/327189238395568721918938657169408000000000000000000000), (8104972107427058546667790181420052565744793889387/163594619197784360959469328584704000000000000000000000)]
    reserve := (3767973/1000000000000) }

theorem tilt_034_020_valid : tilt_034_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_034_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_034_020]
  · intro i; fin_cases i <;> norm_num [tilt_034_020]
  · norm_num [tilt_034_020]
  · norm_num [tilt_034_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_034_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_034_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_034_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_034_020]

def tiltBundle034_row : Alternative → Row
  | .zero => tilt_034_000
  | (.spike 0 false false) => tilt_034_001
  | (.spike 0 false true) => tilt_034_002
  | (.spike 0 true false) => tilt_034_003
  | (.spike 0 true true) => tilt_034_004
  | (.spike 1 false false) => tilt_034_005
  | (.spike 1 false true) => tilt_034_006
  | (.spike 1 true false) => tilt_034_007
  | (.spike 1 true true) => tilt_034_008
  | (.spike 2 false false) => tilt_034_009
  | (.spike 2 false true) => tilt_034_010
  | (.spike 2 true false) => tilt_034_011
  | (.spike 2 true true) => tilt_034_012
  | (.spike 3 false false) => tilt_034_013
  | (.spike 3 false true) => tilt_034_014
  | (.spike 3 true false) => tilt_034_015
  | (.spike 3 true true) => tilt_034_016
  | (.spike 4 false false) => tilt_034_017
  | (.spike 4 false true) => tilt_034_018
  | (.spike 4 true false) => tilt_034_019
  | (.spike 4 true true) => tilt_034_020

def tiltBundle034 : TiltBundle where
  interval := ⟨(13/320), (7/160)⟩
  lambda := ![(7355001/50000000), (7355001/50000000), (9211713/100000000), (7313897/50000000), (7313897/50000000), (16214493/100000000), (15898203/100000000)]
  row := tiltBundle034_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_034_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_034_001_valid | exact tilt_034_002_valid | exact tilt_034_003_valid | exact tilt_034_004_valid | exact tilt_034_005_valid | exact tilt_034_006_valid | exact tilt_034_007_valid | exact tilt_034_008_valid | exact tilt_034_009_valid | exact tilt_034_010_valid | exact tilt_034_011_valid | exact tilt_034_012_valid | exact tilt_034_013_valid | exact tilt_034_014_valid | exact tilt_034_015_valid | exact tilt_034_016_valid | exact tilt_034_017_valid | exact tilt_034_018_valid | exact tilt_034_019_valid | exact tilt_034_020_valid
  same_interval := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_lambda := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_mode := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_owners := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_alternative := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_sign := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl

end SquaresInCircles.Eight.Generated.Owner
