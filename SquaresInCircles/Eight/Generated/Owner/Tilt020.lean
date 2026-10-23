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

def tilt_020_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5600969/100000000), (26979/100000000)]
    alternative := .zero
    polynomial := [(-364873913368271240900149994057104030119943/846108543650920211906097502770000000000000000), (53102323591057/84815400000000), (-44212543271335106248190115833434019278330119943/423054271825460105953048751385000000000000000), (53102323591057/84815400000000), (-88424721668756844225139331516873981452630119943/846108543650920211906097502770000000000000000)]
    bernstein := [(2437323066692224712439454953684462125741249466217321/8350203409574657055243746777078169600000000000000000000), (9673735107948311295148266488558197849446589861153619/23658909660461528323190615868388147200000000000000000000), (51460443259904599053450304923707168643894368301358571/106465093472076877454357771407746662400000000000000000000), (3047876231850390147550144218420298337650029166676819/5914727415115382080797653967097036800000000000000000000), (4477977138166915247028427622007541664898957293873657/8872091122673073121196480950645555200000000000000000000)]
    reserve := (291887867/1000000000000) }

theorem tilt_020_000_valid : tilt_020_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_000]
  · intro i; fin_cases i <;> norm_num [tilt_020_000]
  · norm_num [tilt_020_000]
  · norm_num [tilt_020_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_000]

def tilt_020_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14489/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (33/781250), 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5600969/100000000), (15673/50000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-2129021466330889925742284364770609508469171/7372989661203643100858593439850000000000000000), (89125730701258154153/166163970525000000000), (-331826777205269067245132270821702173625812469171/3686494830601821550429296719925000000000000000), (89125730701258154153/166163970525000000000), (-663651425389071803600338799359039576642116469171/7372989661203643100858593439850000000000000000)]
    bernstein := [(407670941483444949850049080363838662446765961939287629/1236982401117803402900144075965464576000000000000000000000), (12641165551441892820167300546061660498265694681199449/29451961931376271497622477999177728000000000000000000000), (456661613023831657382585428589184246598334481110637287/927736800838352552175108056974098432000000000000000000000), (26730437633012951634461042711484195956394734381426543/51540933379908475120839336498561024000000000000000000000), (39304582255372359544614405164045611328094547132350029/77311400069862712681259004747841536000000000000000000000)]
    reserve := (329568909/1000000000000) }

theorem tilt_020_001_valid : tilt_020_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_001]
  · intro i; fin_cases i <;> norm_num [tilt_020_001]
  · norm_num [tilt_020_001]
  · norm_num [tilt_020_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_001]

def tilt_020_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1073/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (3767/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5600969/100000000), (11417/50000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-12218105816453626860431236132348782016983267049/20232013800657872053543491892268550000000000000000), (90688260261121485313/121042177725000000000), (-1248581268105663993300904973996837451372297711267049/10116006900328936026771745946134275000000000000000), (90688260261121485313/121042177725000000000), (-2497150318105511532974949516757542553962578439267049/20232013800657872053543491892268550000000000000000)]
    bernstein := [(900995871753603046842278589582534421581810421920198352151/3394368656486180615426627288708381933568000000000000000000000), (230500479132332287822654189636876451193819745619315969117/565728109414363435904437881451396988928000000000000000000000), (1270904451675795748568974026281496246601086866828679690053/2545776492364635461569970466531286450176000000000000000000000), (76483540927874892987298808936910069962577180236826266717/141432027353590858976109470362849247232000000000000000000000), (112887340371354843351173902152773774570376492404426857751/212148041030386288464164205544273870848000000000000000000000)]
    reserve := (10617537/40000000000) }

theorem tilt_020_002_valid : tilt_020_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_002]
  · intro i; fin_cases i <;> norm_num [tilt_020_002]
  · norm_num [tilt_020_002]
  · norm_num [tilt_020_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_002]

def tilt_020_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (33/781250), 0, 0]] i.1) i.2
    mu := ![(2797447/50000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5600969/100000000), (15673/50000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-1686729792095196715273294210390098398125777/7369342459081637383875224229300000000000000000), (89125730701258154153/166163970525000000000), (-331662190975165356648383027368433474287550125777/3684671229540818691937612114650000000000000000), (89125730701258154153/166163970525000000000), (-663322695220538618100050781442656558476702125777/7369342459081637383875224229300000000000000000)]
    bernstein := [(481497177906326166457390826345898798610646866733035823/1236370502139837920229495539433996288000000000000000000000), (14397485671083256134584262587814034241809331442682163/29437392908091379053083227129380864000000000000000000000), (511956956651085021503339819832844052043539043473040269/927277876604878440172121654575497216000000000000000000000), (29801740794380111007058465915096820500483430729379941/51515437589159913342895647476416512000000000000000000000), (43911950910298508016565084846413741440928708823224623/77273156383739870014343471214624768000000000000000000000)]
    reserve := (97361021/250000000000) }

theorem tilt_020_003_valid : tilt_020_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_003]
  · intro i; fin_cases i <;> norm_num [tilt_020_003]
  · norm_num [tilt_020_003]
  · norm_num [tilt_020_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_003]

def tilt_020_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5600433/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5600969/100000000), (11417/50000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-195702319063543823803783862674082501042549/358234237676459586920120021610000000000000000), (90688260261121485313/121042177725000000000), (-22107742000976333163385680625756049129990642549/179117118838229793460060010805000000000000000), (90688260261121485313/121042177725000000000), (-44215288299633602782947557467649424177480242549/358234237676459586920120021610000000000000000)]
    bernstein := [(19415339308334563995696078338145691376426781419776651/60101731840933006050296283484756377600000000000000000000), (4658318582752267825360082759714182509824352055910617/10016955306822167675049380580792729600000000000000000000), (25099561236993235118622516078272132237701290923163553/45076298880699754537722212613567283200000000000000000000), (1498493687307153469401094887345318877806542481408217/2504238826705541918762345145198182400000000000000000000), (2215197909248276018304256594150673473609452579482251/3756358240058312878143517717797273600000000000000000000)]
    reserve := (161520631/500000000000) }

theorem tilt_020_004_valid : tilt_020_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_004]
  · intro i; fin_cases i <;> norm_num [tilt_020_004]
  · norm_num [tilt_020_004]
  · norm_num [tilt_020_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_004]

def tilt_020_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (33/781250), 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (4243931/100000000), (1/100000000), (5600969/100000000), (15673/50000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-6643290093377506088839393026633937511376103/22109305122204678899504057422425000000000000000), (89125730701258154153/166163970525000000000), (-995045661501091857436086251788746198315263376103/11054652561102339449752028711212500000000000000), (89125730701258154153/166163970525000000000), (-1990084679712090337366083664184465762693015376103/22109305122204678899504057422425000000000000000)]
    bernstein := [(1179022561439528406909831918091400088684800734028566297/3709325876451342941076218642524274688000000000000000000000), (36872260349994666837546658787663543674017215910509557/88317282772651022406576634345816064000000000000000000000), (43122392218860255865589728778612669951857270561490261/89741755075435716316360128448167936000000000000000000000), (78345595825198900484778809827605723488879219553074099/154555244852139289211509110105178112000000000000000000000), (38382064921180143782920466635554549394919392161816499/77277622426069644605754555052589056000000000000000000000)]
    reserve := (158926797/500000000000) }

theorem tilt_020_005_valid : tilt_020_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_005]
  · intro i; fin_cases i <;> norm_num [tilt_020_005]
  · norm_num [tilt_020_005]
  · norm_num [tilt_020_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_005]

def tilt_020_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (4247641/100000000), (1/100000000), (5600969/100000000), (11417/50000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-42019778690875439559281454330571715320543/78632229480109848908835777615000000000000000), (90688260261121485313/121042177725000000000), (-4852636972939427304235433425943241048421720543/39316114740054924454417888807500000000000000), (90688260261121485313/121042177725000000000), (-9705231926100163733031307570432151525128120543/78632229480109848908835777615000000000000000)]
    bernstein := [(4418823101481018623300446674981384587526424128173857/13192298985493706388709021495748198400000000000000000000), (1048692942769418140512992319128593679735902420273419/2198716497582284398118170249291366400000000000000000000), (5627215993104536356962653484559045661716012184636771/9894224239120279791531766121811148800000000000000000000), (335467242707501281209104570314665903963855355236619/549679124395571099529542562322841600000000000000000000), (165352607809102558108759308886101141266369280331019/274839562197785549764771281161420800000000000000000000)]
    reserve := (334954741/1000000000000) }

theorem tilt_020_006_valid : tilt_020_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_006]
  · intro i; fin_cases i <;> norm_num [tilt_020_006]
  · norm_num [tilt_020_006]
  · norm_num [tilt_020_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_006]

def tilt_020_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (33/781250), 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (4238913/100000000), (2122893/50000000), (1/100000000), (5600969/100000000), (15673/50000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-45191063110585671951043855064848965151577/150403287484140074040220761285000000000000000), (63648480195487290613/118636577587500000000), (-47383233094532744046997326095175593272939736039/526411506194490259140772664497500000000000000), (63648480195487290613/118636577587500000000), (-94766149851623713994290994883365732603123411039/1052823012388980518281545328995000000000000000)]
    bernstein := [(56180502653804013213751399845117966447535074735200161/176634390886206021750014347983401779200000000000000000000), (12298300971206963472243410463252450005450898467035787/29439065147701003625002391330566963200000000000000000000), (63697353168415162766975513294402352056487541174970083/132475793164654516312510760987551334400000000000000000000), (3733353893910618010323152680809541859249553838709387/7359766286925250906250597832641740800000000000000000000), (5487610897319455334474687999027697022100670279161761/11039649430387876359375896748962611200000000000000000000)]
    reserve := (39757619/125000000000) }

theorem tilt_020_007_valid : tilt_020_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_007]
  · intro i; fin_cases i <;> norm_num [tilt_020_007]
  · norm_num [tilt_020_007]
  · norm_num [tilt_020_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_007]

def tilt_020_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (1060657/25000000), (2122893/50000000), (1/100000000), (5600969/100000000), (11417/50000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-86142075499462073160326148119554224324126007/161196267682709290343083511539800000000000000000), (453562822177574113041/605476048450000000000), (-9947894530158260465856422131750120972903808376007/80598133841354645171541755769900000000000000000), (453562822177574113041/605476048450000000000), (-19895702918241021469639683937352122391583292626007/161196267682709290343083511539800000000000000000)]
    bernstein := [(9052994789252759319925106940255233076162799932677319593/27044246013066332292926261791417171968000000000000000000000), (2148666487351646289603851483327140615715010167282037731/4507374335511055382154376965236195328000000000000000000000), (11529601953115281038153835786222269726670796381417763579/20283184509799749219694696343562878976000000000000000000000), (687308552252150736169646753218926658773751799625794531/1126843583877763845538594241309048832000000000000000000000), (78172050013307960368275293457456758547061799093909261/130020413524357366792914720151044096000000000000000000000)]
    reserve := (167373769/500000000000) }

theorem tilt_020_008_valid : tilt_020_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_008]
  · intro i; fin_cases i <;> norm_num [tilt_020_008]
  · norm_num [tilt_020_008]
  · norm_num [tilt_020_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_008]

def tilt_020_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (33/781250), 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (1060983/25000000), (1/100000000), (5600969/100000000), (15673/50000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-3595822521664358770780579501983799720843/11963912517225903317634303637500000000000000), (89125730701258154153/166163970525000000000), (-538444749866156683203148565601635939227720843/5981956258612951658817151818750000000000000), (89125730701258154153/166163970525000000000), (-153840843415684528863932335803395699236531549/1709130359603700473947757662500000000000000)]
    bernstein := [(637837013285083266833081981615359918466701458813557/2007211445066027007550673211359232000000000000000000000), (139640625917257530118291641437900476708740577633319/334535240844337834591778868559872000000000000000000000), (723251863347137083037267880127184648004563058475871/1505408583799520255663004908519424000000000000000000000), (42388047917277565538695455700924437317134903316519/83633810211084458647944717139968000000000000000000000), (62298414070296448351927254477448106073851499952757/125450715316626687971917075709952000000000000000000000)]
    reserve := (158886353/500000000000) }

theorem tilt_020_009_valid : tilt_020_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_009]
  · intro i; fin_cases i <;> norm_num [tilt_020_009]
  · norm_num [tilt_020_009]
  · norm_num [tilt_020_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_009]

def tilt_020_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2123821/50000000), (1/100000000), (5600969/100000000), (11417/50000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-546645373423850281403929506805880284954813/1151400774169832747197782909225000000000000000), (90688260261121485313/121042177725000000000), (-71056418044965460351181713919775669374080954813/575700387084916373598891454612500000000000000), (90688260261121485313/121042177725000000000), (-142112289444557496852082023910044532867876954813/1151400774169832747197782909225000000000000000)]
    bernstein := [(76220884123601176600524941932823560353819651654155587/193172994908145046836105985891762176000000000000000000000), (17275314828328072400687046266709928057236622754299329/32195499151357507806017664315293696000000000000000000000), (91036093609201335631136925480402820043923437287509961/144879746181108785127079489418821632000000000000000000000), (5392066148508021390729008348721734362598502692910529/8048874787839376951504416078823424000000000000000000000), (2661169396398801769153264875421973779862399724820929/4024437393919688475752208039411712000000000000000000000)]
    reserve := (197286593/500000000000) }

theorem tilt_020_010_valid : tilt_020_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_010]
  · intro i; fin_cases i <;> norm_num [tilt_020_010]
  · norm_num [tilt_020_010]
  · norm_num [tilt_020_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_010]

def tilt_020_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2897/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (33/781250), 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5600969/100000000), (15673/50000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1064671311832840139318884876420979261537273/3686494830601821550429296719925000000000000000), (89125730701258154153/166163970525000000000), (-165913388763213201017742583153545122487413537273/1843247415300910775214648359962500000000000000), (89125730701258154153/166163970525000000000), (-331825712855114569195345847422213823995565537273/3686494830601821550429296719925000000000000000)]
    bernstein := [(203808529980297459690009680112072405357683268420741127/618491200558901701450072037982732288000000000000000000000), (6319941327454322648684923410133160116465857382575787/14725980965688135748811238999588864000000000000000000000), (228310600825743917174167452353236423066825353935810581/463868400419176276087554028487049216000000000000000000000), (13364096273818216319482866427133304945986442239745709/25770466689954237560419668249280512000000000000000000000), (19650607305432082465718988476459810142178274988472327/38655700034931356340629502373920768000000000000000000000)]
    reserve := (329525351/1000000000000) }

theorem tilt_020_011_valid : tilt_020_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_011]
  · intro i; fin_cases i <;> norm_num [tilt_020_011]
  · norm_num [tilt_020_011]
  · norm_num [tilt_020_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_011]

def tilt_020_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4291/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1883/50000000), (5600969/100000000), (11417/50000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-34897743191485393034636758132511959871367961/57790408413878073611926724916594000000000000000), (90688260261121485313/121042177725000000000), (-3566428042951144638271377955076472544843179207961/28895204206939036805963362458297000000000000000), (90688260261121485313/121042177725000000000), (-7132821188159097791149721273394812577726487047961/57790408413878073611926724916594000000000000000)]
    bernstein := [(2573903197101910284717753092761517529742359243590340839/9695621646878498386511948400982795223040000000000000000000), (658450079597951141518944597789584491189763612706011213/1615936941146416397751991400163799203840000000000000000000), (3630426128915343006092584237984800607367804067497652917/7271716235158873789883961300737096417280000000000000000000), (218479419787299005006018731791412576476276526921537613/403984235286604099437997850040949800960000000000000000000), (322469178042855586529765653285277459173718986209579239/605976352929906149156996775061424701440000000000000000000)]
    reserve := (16591917/62500000000) }

theorem tilt_020_012_valid : tilt_020_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_012]
  · intro i; fin_cases i <;> norm_num [tilt_020_012]
  · norm_num [tilt_020_012]
  · norm_num [tilt_020_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_012]

def tilt_020_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (33/781250), 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5598199/100000000), (15673/50000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-105382838882811237996375929520355069030691/460583955967714845453343396209375000000000000), (89125730701258154153/166163970525000000000), (-20728889250839182121734323360278051299318030691/230291977983857422726671698104687500000000000), (89125730701258154153/166163970525000000000), (-41457673118839481432230650344626582243567030691/460583955967714845453343396209375000000000000)]
    bernstein := [(30099916351492149748819720904187137338761361608342109/77273165154048409885773600803782656000000000000000000000), (899993893055428600668380236625011061516726479292329/1839837265572581187756514304851968000000000000000000000), (32002067936992776103460045547864972557293991701128727/57954873865536307414330200602836992000000000000000000000), (1862873151829718205841316438307716483171372678124703/3219715214752017078573900033490944000000000000000000000), (2744893456491092203567046269549086143472892927292509/4829572822128025617860850050236416000000000000000000000)]
    reserve := (389526121/1000000000000) }

theorem tilt_020_013_valid : tilt_020_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_013]
  · intro i; fin_cases i <;> norm_num [tilt_020_013]
  · norm_num [tilt_020_013]
  · norm_num [tilt_020_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_013]

def tilt_020_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (280187/5000000), (11417/50000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-146808384930291613976113845729369555965111/268675647765174772342199509950000000000000000), (90688260261121485313/121042177725000000000), (-16580804650628492560568783239616645392587965111/134337823882587386171099754975000000000000000), (90688260261121485313/121042177725000000000), (-33161462492872054829523590365387561415619965111/268675647765174772342199509950000000000000000)]
    bernstein := [(14556190751865092799860192533704485501014477291343689/45076293764962544333359070935252992000000000000000000000), (3492853192264172963428371863436575994718312073652163/7512715627493757388893178489208832000000000000000000000), (18820684711031988529611259864977053034197853992021467/33807220323721908250019303201439744000000000000000000000), (1123648799237156661325110734250047173731618419738563/1878178906873439347223294622302208000000000000000000000), (1661066233720231043792903389585692336832258325942089/2817268360310159020834941933453312000000000000000000000)]
    reserve := (64584683/200000000000) }

theorem tilt_020_014_valid : tilt_020_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_014]
  · intro i; fin_cases i <;> norm_num [tilt_020_014]
  · norm_num [tilt_020_014]
  · norm_num [tilt_020_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_014]

def tilt_020_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2897/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (33/781250), 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5600969/100000000), (15673/50000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1064671311832840139318884876420979261537273/3686494830601821550429296719925000000000000000), (89125730701258154153/166163970525000000000), (-165913388763213201017742583153545122487413537273/1843247415300910775214648359962500000000000000), (89125730701258154153/166163970525000000000), (-331825712855114569195345847422213823995565537273/3686494830601821550429296719925000000000000000)]
    bernstein := [(203808529980297459690009680112072405357683268420741127/618491200558901701450072037982732288000000000000000000000), (6319941327454322648684923410133160116465857382575787/14725980965688135748811238999588864000000000000000000000), (228310600825743917174167452353236423066825353935810581/463868400419176276087554028487049216000000000000000000000), (13364096273818216319482866427133304945986442239745709/25770466689954237560419668249280512000000000000000000000), (19650607305432082465718988476459810142178274988472327/38655700034931356340629502373920768000000000000000000000)]
    reserve := (329525351/1000000000000) }

theorem tilt_020_015_valid : tilt_020_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_015]
  · intro i; fin_cases i <;> norm_num [tilt_020_015]
  · norm_num [tilt_020_015]
  · norm_num [tilt_020_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_015]

def tilt_020_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4291/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1883/50000000), (5600969/100000000), (11417/50000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-34897743191485393034636758132511959871367961/57790408413878073611926724916594000000000000000), (90688260261121485313/121042177725000000000), (-3566428042951144638271377955076472544843179207961/28895204206939036805963362458297000000000000000), (90688260261121485313/121042177725000000000), (-7132821188159097791149721273394812577726487047961/57790408413878073611926724916594000000000000000)]
    bernstein := [(2573903197101910284717753092761517529742359243590340839/9695621646878498386511948400982795223040000000000000000000), (658450079597951141518944597789584491189763612706011213/1615936941146416397751991400163799203840000000000000000000), (3630426128915343006092584237984800607367804067497652917/7271716235158873789883961300737096417280000000000000000000), (218479419787299005006018731791412576476276526921537613/403984235286604099437997850040949800960000000000000000000), (322469178042855586529765653285277459173718986209579239/605976352929906149156996775061424701440000000000000000000)]
    reserve := (16591917/62500000000) }

theorem tilt_020_016_valid : tilt_020_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_016]
  · intro i; fin_cases i <;> norm_num [tilt_020_016]
  · norm_num [tilt_020_016]
  · norm_num [tilt_020_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_016]

def tilt_020_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (33/781250), 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (27991/500000), (15673/50000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-8431808190200904211964559780780779527001/36846723059304769234775784150000000000000000), (89125730701258154153/166163970525000000000), (-1658311437468964683555086472218832499835527001/18423361529652384617387892075000000000000000), (89125730701258154153/166163970525000000000), (-3316614443129739166205960979877884218891527001/36846723059304769234775784150000000000000000)]
    bernstein := [(2407795837675669564033997384108932016375629617093799/6181854316581369232819880422539264000000000000000000000), (71994812375530984080503308111032998129495931094219/147187007537651648400473343393792000000000000000000000), (2560017465997745411223170287467956442292640432567797/4636390737436026924614910316904448000000000000000000000), (149021632829351556823431074522915281773074134081933/257577263190890384700828350939136000000000000000000000), (219579146777179924813463314189990456460591332908199/386365894786335577051242526408704000000000000000000000)]
    reserve := (97373527/250000000000) }

theorem tilt_020_017_valid : tilt_020_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_017]
  · intro i; fin_cases i <;> norm_num [tilt_020_017]
  · norm_num [tilt_020_017]
  · norm_num [tilt_020_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_017]

def tilt_020_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5603741/100000000), (11417/50000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1406563882495299522333441243527087054924503/2686756957109480889441068686425000000000000000), (90688260261121485313/121042177725000000000), (-165808014574874764520783633640350978049842924503/1343378478554740444720534343212500000000000000), (90688260261121485313/121042177725000000000), (-331614622585867033742044933839458429012630924503/2686756957109480889441068686425000000000000000)]
    bernstein := [(1046197084294003077475256610267601529290951125770053/3025255154961644062417780444495872000000000000000000000), (245964973376234635939030551662642505157304065718551/504209192493607343736296740749312000000000000000000000), (195947998843072688734161101573026449709384652641472891/338072263566963723975186964672413696000000000000000000000), (897427220518057696949573820589862657169203164287023/1444753263106682581090542584070144000000000000000000000), (1327366481158367834744738419628558315345321810275469/2167129894660023871635813876105216000000000000000000000)]
    reserve := (172910553/500000000000) }

theorem tilt_020_018_valid : tilt_020_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_018]
  · intro i; fin_cases i <;> norm_num [tilt_020_018]
  · norm_num [tilt_020_018]
  · norm_num [tilt_020_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_018]

def tilt_020_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5600969/100000000), (26979/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-223084226972426717347642579533165146945143/846108543650920211906097502770000000000000000), (53102323591057/84815400000000), (-44212587360954197529928673789968053378773973943/423054271825460105953048751385000000000000000), (53102323591057/84815400000000), (-88424951637681422633139999937356573592401002743/846108543650920211906097502770000000000000000)]
    bernstein := [(3836636351039726020556890699098314885773491148588921/8350203409574657055243746777078169600000000000000000000), (13638453070376573549217914210619987194515617566326019/23658909660461528323190615868388147200000000000000000000), (69301656031378846020895994332986249605274980719910171/106465093472076877454357771407746662400000000000000000000), (4039053465011466006297939981394098007326525825449219/5914727415115382080797653967097036800000000000000000000), (5964740730405047099235903098759488382174907071790857/8872091122673073121196480950645555200000000000000000000)]
    reserve := (229733107/500000000000) }

theorem tilt_020_019_valid : tilt_020_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_019]
  · intro i; fin_cases i <;> norm_num [tilt_020_019]
  · norm_num [tilt_020_019]
  · norm_num [tilt_020_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_019]

def tilt_020_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1/10000000), 0, 0]] i.1) i.2
    mu := ![(5597663/100000000), (1/100000000), (424077/10000000), (2122893/50000000), (1/100000000), (5600969/100000000), (26979/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-364691003689041520857414975614337788945143/846108543650920211906097502770000000000000000), (11938731085796838613/19068622305000000000), (-44212471666086500596436409629422308881750373943/423054271825460105953048751385000000000000000), (11938731085796838613/19068622305000000000), (-88424578641169312151351961843869003425711802743/846108543650920211906097502770000000000000000)]
    bernstein := [(41465251722065301364837729718195785608813557815211657/141953457962769169939143695210328883200000000000000000000), (3226289056108244607596029141517078574137717460908673/7886303220153842774396871956129382400000000000000000000), (51483569444566632112529484162426474685583887187510171/106465093472076877454357771407746662400000000000000000000), (1016387733399039000206584338436692740183174987283073/1971575805038460693599217989032345600000000000000000000), (4479911472221240273251539580589233721761373280990857/8872091122673073121196480950645555200000000000000000000)]
    reserve := (58420911/200000000000) }

theorem tilt_020_020_valid : tilt_020_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_020_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_020_020]
  · intro i; fin_cases i <;> norm_num [tilt_020_020]
  · norm_num [tilt_020_020]
  · norm_num [tilt_020_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_020_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_020_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_020_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_020_020]

def tiltBundle020_row : Alternative → Row
  | .zero => tilt_020_000
  | (.spike 0 false false) => tilt_020_001
  | (.spike 0 false true) => tilt_020_002
  | (.spike 0 true false) => tilt_020_003
  | (.spike 0 true true) => tilt_020_004
  | (.spike 1 false false) => tilt_020_005
  | (.spike 1 false true) => tilt_020_006
  | (.spike 1 true false) => tilt_020_007
  | (.spike 1 true true) => tilt_020_008
  | (.spike 2 false false) => tilt_020_009
  | (.spike 2 false true) => tilt_020_010
  | (.spike 2 true false) => tilt_020_011
  | (.spike 2 true true) => tilt_020_012
  | (.spike 3 false false) => tilt_020_013
  | (.spike 3 false true) => tilt_020_014
  | (.spike 3 true false) => tilt_020_015
  | (.spike 3 true true) => tilt_020_016
  | (.spike 4 false false) => tilt_020_017
  | (.spike 4 false true) => tilt_020_018
  | (.spike 4 true false) => tilt_020_019
  | (.spike 4 true true) => tilt_020_020

def tiltBundle020 : TiltBundle where
  interval := ⟨(1/640), (1/320)⟩
  lambda := ![(2897783/20000000), (2897783/20000000), (1703083/20000000), (226333/1562500), (226333/1562500), (4194567/25000000), (2094733/12500000)]
  row := tiltBundle020_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_020_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_020_001_valid | exact tilt_020_002_valid | exact tilt_020_003_valid | exact tilt_020_004_valid | exact tilt_020_005_valid | exact tilt_020_006_valid | exact tilt_020_007_valid | exact tilt_020_008_valid | exact tilt_020_009_valid | exact tilt_020_010_valid | exact tilt_020_011_valid | exact tilt_020_012_valid | exact tilt_020_013_valid | exact tilt_020_014_valid | exact tilt_020_015_valid | exact tilt_020_016_valid | exact tilt_020_017_valid | exact tilt_020_018_valid | exact tilt_020_019_valid | exact tilt_020_020_valid
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
