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

def tilt_050_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-347551600787717939721794040274935971469/5913168812881519337941100000000000000000), (175028375726269/293109250000000), (-1666030187057928429070756174671935971469/2956584406440759668970550000000000000000), (175028375726269/293109250000000), (-2984508773328138918419718309068935971469/5913168812881519337941100000000000000000)]
    bernstein := [(18805620288491366107164610582410433756694211/946107010061043094070576000000000000000000000), (6152876232348504518797827385318094439485137/270316288588869455448736000000000000000000000), (41534993905735602869503560565859334882371959/1621897731533216732692416000000000000000000000), (12653057353267661292609803596475296040123247/445226828264020279562624000000000000000000000), (27776912249684588321170296629817332555619043/890453656528040559125248000000000000000000000)]
    reserve := (2484605347/125000000000) }

theorem tilt_050_000_valid : tilt_050_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_000]
  · intro i; fin_cases i <;> norm_num [tilt_050_000]
  · norm_num [tilt_050_000]
  · norm_num [tilt_050_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_000]

def tilt_050_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![(22297/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1038369814542146403917904617507337028657/17739506438644558013823300000000000000000), (175028375726269/293109250000000), (-4993805573352777871964791020698337028657/8869753219322279006911650000000000000000), (175028375726269/293109250000000), (-8949241332163409340011677423889337028657/17739506438644558013823300000000000000000)]
    bernstein := [(57133657913160039751507115979681148509228383/2838321030183129282211728000000000000000000000), (18664178950678121979041371207592887783470661/810948865766608366346208000000000000000000000), (125843051206165005824021244903601028684222627/4865693194599650198077248000000000000000000000), (38300415634904551405892776721119317048842491/1335680484792060838687872000000000000000000000), (84016133405987364054590658977591418255226879/2671360969584121677375744000000000000000000000)]
    reserve := (10064692701/500000000000) }

theorem tilt_050_001_valid : tilt_050_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_001]
  · intro i; fin_cases i <;> norm_num [tilt_050_001]
  · norm_num [tilt_050_001]
  · norm_num [tilt_050_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_001]

def tilt_050_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11148663/100000000), 0], ![0, 0, (1321/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (5797/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-10810672510739734767460292497570014739157/183308233199327099476174100000000000000000), (175028375726269/293109250000000), (-51683508685116259937278118663877014739157/91654116599663549738087050000000000000000), (175028375726269/293109250000000), (-92556344859492785107095944830184014739157/183308233199327099476174100000000000000000)]
    bernstein := [(576856279946656362599222033156892302419077883/29329317311892335916187856000000000000000000000), (188984767070708325692412979119111933821887161/8379804946254953118910816000000000000000000000), (1277017739112153201456054708431027264245138127/50278829677529718713464896000000000000000000000), (389332223003393542929028469408378268217753991/13802031676184628666441344000000000000000000000), (855234336854602718678626815507522578427620379/27604063352369257332882688000000000000000000000)]
    reserve := (9834123887/500000000000) }

theorem tilt_050_002_valid : tilt_050_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_002]
  · intro i; fin_cases i <;> norm_num [tilt_050_002]
  · norm_num [tilt_050_002]
  · norm_num [tilt_050_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_002]

def tilt_050_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2789953/25000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(248747/6250000), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-11051554245907896417443084353409093220343/189032177570446341724986400000000000000000), (175028375726269/293109250000000), (-53200677014010972591400742666937093220343/94516088785223170862493200000000000000000), (175028375726269/293109250000000), (-95349799782114048765358400980465093220343/189032177570446341724986400000000000000000)]
    bernstein := [(611043481683634145337825498005773429007802617/30245148411271414675997824000000000000000000000), (199524173724915173396617881752604180090606339/8641470974648975621713664000000000000000000000), (1344830463271181076863008237693378947530316373/51848825847893853730281984000000000000000000000), (409189534938332340356005449655456971211544509/14233011017068901023998976000000000000000000000), (897405568592360493263336001670759296126476121/28466022034137802047997952000000000000000000000)]
    reserve := (10101512371/500000000000) }

theorem tilt_050_003_valid : tilt_050_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_003]
  · intro i; fin_cases i <;> norm_num [tilt_050_003]
  · norm_num [tilt_050_003]
  · norm_num [tilt_050_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_003]

def tilt_050_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2227503/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(49849/1250000), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-2229926553603713439514477110984329673323/37882125290794179180648800000000000000000), (175028375726269/293109250000000), (-10676627904241792468389660768560329673323/18941062645397089590324400000000000000000), (175028375726269/293109250000000), (-19123329254879871497264844426136329673323/37882125290794179180648800000000000000000)]
    bernstein := [(119912265822175236942359640802367931916855237/6061140046527068668903808000000000000000000000), (39256035323440564358346508761661601617791879/1731754299007733905401088000000000000000000000), (265115527594921691881739865093128850874535153/10390525794046403432406528000000000000000000000), (80792016537270357532400754098646313805576249/2852301198365679373601792000000000000000000000), (177410661159987154373496268066504043762966181/5704602396731358747203584000000000000000000000)]
    reserve := (19783780757/1000000000000) }

theorem tilt_050_004_valid : tilt_050_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_004]
  · intro i; fin_cases i <;> norm_num [tilt_050_004]
  · norm_num [tilt_050_004]
  · norm_num [tilt_050_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_004]

def tilt_050_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (6392357/100000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-1383770309371000269132216111517502833141/23641169686537323186058100000000000000000), (175028375726269/293109250000000), (-6655119221003102196974409078504502833141/11820584843268661593029050000000000000000), (175028375726269/293109250000000), (-11926468132635204124816602045491502833141/23641169686537323186058100000000000000000)]
    bernstein := [(76149402573764005876885998240265666569340379/3782587149845971709769296000000000000000000000), (24875831859662436965141307581045471023202393/1080739185670277631362656000000000000000000000), (55907787097212571918325587440780485114626917/2161478371340555262725312000000000000000000000), (51046306408721973827892450924821838877150183/1780041011692221981067904000000000000000000000), (111974906362970912310119220319561055330597627/3560082023384443962135808000000000000000000000)]
    reserve := (5032891481/250000000000) }

theorem tilt_050_005_valid : tilt_050_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_005]
  · intro i; fin_cases i <;> norm_num [tilt_050_005]
  · norm_num [tilt_050_005]
  · norm_num [tilt_050_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_005]

def tilt_050_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (319929/5000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-13929349187524866865450406340131926469/236641845148642332385140000000000000000), (175028375726269/293109250000000), (-66694155219151283777791971547931926469/118320922574321166192570000000000000000), (175028375726269/293109250000000), (-119458961250777700690133536755731926469/236641845148642332385140000000000000000)]
    bernstein := [(749158152437316609829202591644956408339211/37862695223782773181622400000000000000000000), (245250442703395355547385314412458134700137/10817912921080792337606400000000000000000000), (1656279161867403483160098336324087668876959/64907477526484754025638400000000000000000000), (8580484467744099740765921932521971720400199/302901561790262185452979200000000000000000000), (18841691944980445976808247454561428213568731/605803123580524370905958400000000000000000000)]
    reserve := (9893090653/500000000000) }

theorem tilt_050_006_valid : tilt_050_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_006]
  · intro i; fin_cases i <;> norm_num [tilt_050_006]
  · norm_num [tilt_050_006]
  · norm_num [tilt_050_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_006]

def tilt_050_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (5858541/100000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-12106261697557297882964846704273384365427/206832259226989564714646100000000000000000), (13463721209713/22532850000000), (-19428706530696720890823504265155311121809/34472043204498260785774350000000000000000), (13463721209713/22532850000000), (-104465977486623027461976178886658482365427/206832259226989564714646100000000000000000)]
    bernstein := [(667662687170768216411775218046629364229006013/33093161476318330354343376000000000000000000000), (169601814979678386753103980631250451043959233/7354035883626295634298528000000000000000000000), (3430010476967890519213419740109189669876495893/132372645905273321417373504000000000000000000000), (149111232756231303942140165316292543821496667/5191084153147973388916608000000000000000000000), (981161574750035108620540861370704659802855069/31146504918887840333499648000000000000000000000)]
    reserve := (10087623203/500000000000) }

theorem tilt_050_007_valid : tilt_050_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_007]
  · intro i; fin_cases i <;> norm_num [tilt_050_007]
  · norm_num [tilt_050_007]
  · norm_num [tilt_050_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_007]

def tilt_050_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (586583/10000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-1218991755176994042334191774203927355227/20708959297911411704554300000000000000000), (175028375726269/293291500000000), (-5830356856808872751494497109620372455227/10354479648955705852277150000000000000000), (175028375726269/293291500000000), (-10441721958440751460654802445036817555227/20708959297911411704554300000000000000000)]
    bernstein := [(65415606725963519962691743274811451264072213/3313433487665825872728688000000000000000000000), (149938347268700098824434746529311884507880897/6626866975331651745457376000000000000000000000), (1012771086114897424156559909610160937869622279/39761201851989910472744256000000000000000000000), (44096313315319401715074073584775371194387401/1559262817725094528342912000000000000000000000), (96840993248546331895586945434512648628775669/3118525635450189056685824000000000000000000000)]
    reserve := (19742544091/1000000000000) }

theorem tilt_050_008_valid : tilt_050_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_008]
  · intro i; fin_cases i <;> norm_num [tilt_050_008]
  · norm_num [tilt_050_008]
  · norm_num [tilt_050_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_008]

def tilt_050_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (3196179/50000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-98840849366556356230202494311750777899/1688655241777623207650100000000000000000), (175028375726269/293109250000000), (-475365830528353615667834307138750777899/844327620888811603825050000000000000000), (175028375726269/293109250000000), (-851890811690150875105466119965750777899/1688655241777623207650100000000000000000)]
    bernstein := [(777032511220054187390758376145662303182483/38597834097774244746288000000000000000000000), (12437885129240181268108376203398494040072689/540369677368839426448032000000000000000000000), (83861496527251358633460532436781851431380823/3242218064213036558688192000000000000000000000), (61984678309674101128482075481930640107774729/2161478709475357705792128000000000000000000000), (135969285247609981401000339275507974986261301/4322957418950715411584256000000000000000000000)]
    reserve := (10065752773/500000000000) }

theorem tilt_050_009_valid : tilt_050_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_009]
  · intro i; fin_cases i <;> norm_num [tilt_050_009]
  · norm_num [tilt_050_009]
  · norm_num [tilt_050_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_009]

def tilt_050_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (6398581/100000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-198850517967024619822167086030243784947/3380598316173376422793900000000000000000), (175028375726269/293109250000000), (-952633579080696247753425505083243784947/1690299158086688211396950000000000000000), (175028375726269/293109250000000), (-1706416640194367875684683924136243784947/3380598316173376422793900000000000000000)]
    bernstein := [(10725716434228752919126114688575091410280893/540895730587740227647024000000000000000000000), (24572131030221407467091662424356933696431817/1081791461175480455294048000000000000000000000), (55303843924919286376642138441111026445879573/2163582922350960910588096000000000000000000000), (122768196927644020625583894964652162868987937/4327165844701921821176192000000000000000000000), (269548344825874089838299515008848947728332653/8654331689403843642352384000000000000000000000)]
    reserve := (19829545377/1000000000000) }

theorem tilt_050_010_valid : tilt_050_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_010]
  · intro i; fin_cases i <;> norm_num [tilt_050_010]
  · norm_num [tilt_050_010]
  · norm_num [tilt_050_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_010]

def tilt_050_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(19853/100000000), 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1038839493041638216199401418639298891407/17739506438644558013823300000000000000000), (175028375726269/293109250000000), (-4994275251852269684246287821830298891407/8869753219322279006911650000000000000000), (175028375726269/293109250000000), (-8949711010662901152293174225021298891407/17739506438644558013823300000000000000000)]
    bernstein := [(57055089624086549901246049589525436146545633/2838321030183129282211728000000000000000000000), (18641648540154428242728295585407124650476411/810948865766608366346208000000000000000000000), (125707346125046766016734137087055471179262877/4865693194599650198077248000000000000000000000), (38263011848240521951231215969373270185020741/1335680484792060838687872000000000000000000000), (83941006920958150204728401146130722422776129/2671360969584121677375744000000000000000000000)]
    reserve := (20101704147/1000000000000) }

theorem tilt_050_011_valid : tilt_050_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_011]
  · intro i; fin_cases i <;> norm_num [tilt_050_011]
  · norm_num [tilt_050_011]
  · norm_num [tilt_050_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_011]

def tilt_050_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11148663/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5881/100000000), 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (5161/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-138394998198392123112939626813371382218553/2347528018713963177162616700000000000000000), (175028375726269/293109250000000), (-661830996947665687384477594168980382218553/1173764009356981588581308350000000000000000), (175028375726269/293109250000000), (-1185266995696939251656015561524589382218553/2347528018713963177162616700000000000000000)]
    bernstein := [(7396072955459826733905463942188295017098235607/375604482994234108346018672000000000000000000000), (2422687825284098296640164722106624275459186669/107315566569781173813148192000000000000000000000), (16368904330854819378253627845071362987312218683/643893399418687042878889152000000000000000000000), (4990054129998710970373850225458140918261094739/176755050820816050986361728000000000000000000000), (10960731733014111797311664117624731201995791991/353510101641632101972723456000000000000000000000)]
    reserve := (9845560011/500000000000) }

theorem tilt_050_012_valid : tilt_050_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_012]
  · intro i; fin_cases i <;> norm_num [tilt_050_012]
  · norm_num [tilt_050_012]
  · norm_num [tilt_050_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_012]

def tilt_050_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9936389/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (88591/2500000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-3779596784801258491573415993892040703/64610612016541324817256250000000000000), (175028375726269/293109250000000), (-18186036222830771776209194484329540703/32305306008270662408628125000000000000), (175028375726269/293109250000000), (-32592475660860285060844972974767040703/64610612016541324817256250000000000000)]
    bernstein := [(208483106079292718204652740763014164161457/10337697922646611970761000000000000000000000), (476635173224187391433261245449781544380333/20675395845293223941522000000000000000000000), (1071047586289189624931213004615145428748777/41350791690586447883044000000000000000000000), (139683730552291752423270418210080304535189/4864799022421935045064000000000000000000000), (306376972800045853265912936648190538433041/9729598044843870090128000000000000000000000)]
    reserve := (20167266217/1000000000000) }

theorem tilt_050_013_valid : tilt_050_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_013]
  · intro i; fin_cases i <;> norm_num [tilt_050_013]
  · norm_num [tilt_050_013]
  · norm_num [tilt_050_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_013]

def tilt_050_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9916537/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (1775367/50000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-22168888066106377284850377327562942831/376668833543225662255740000000000000000), (175028375726269/293109250000000), (-106155969588325089545928301397362942831/188334416771612831127870000000000000000), (175028375726269/293109250000000), (-190143051110543801807006225467162942831/376668833543225662255740000000000000000)]
    bernstein := [(1192924233068004968569812515932816560287489/60267013366916105960918400000000000000000000), (2733543306347739476997700023017789389721341/120534026733832211921836800000000000000000000), (18460075920920793710394224037067492176617387/723204160402993271531020800000000000000000000), (803622366375323160062650388109254721767653/28360947466784049863961600000000000000000000), (1764614258274474900492603174219849005353057/56721894933568099727923200000000000000000000)]
    reserve := (19793982917/1000000000000) }

theorem tilt_050_014_valid : tilt_050_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_014]
  · intro i; fin_cases i <;> norm_num [tilt_050_014]
  · norm_num [tilt_050_014]
  · norm_num [tilt_050_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_014]

def tilt_050_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(19853/100000000), 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1038839493041638216199401418639298891407/17739506438644558013823300000000000000000), (175028375726269/293109250000000), (-4994275251852269684246287821830298891407/8869753219322279006911650000000000000000), (175028375726269/293109250000000), (-8949711010662901152293174225021298891407/17739506438644558013823300000000000000000)]
    bernstein := [(57055089624086549901246049589525436146545633/2838321030183129282211728000000000000000000000), (18641648540154428242728295585407124650476411/810948865766608366346208000000000000000000000), (125707346125046766016734137087055471179262877/4865693194599650198077248000000000000000000000), (38263011848240521951231215969373270185020741/1335680484792060838687872000000000000000000000), (83941006920958150204728401146130722422776129/2671360969584121677375744000000000000000000000)]
    reserve := (20101704147/1000000000000) }

theorem tilt_050_015_valid : tilt_050_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_015]
  · intro i; fin_cases i <;> norm_num [tilt_050_015]
  · norm_num [tilt_050_015]
  · norm_num [tilt_050_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_015]

def tilt_050_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11148663/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5881/100000000), 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (5161/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-138394998198392123112939626813371382218553/2347528018713963177162616700000000000000000), (175028375726269/293109250000000), (-661830996947665687384477594168980382218553/1173764009356981588581308350000000000000000), (175028375726269/293109250000000), (-1185266995696939251656015561524589382218553/2347528018713963177162616700000000000000000)]
    bernstein := [(7396072955459826733905463942188295017098235607/375604482994234108346018672000000000000000000000), (2422687825284098296640164722106624275459186669/107315566569781173813148192000000000000000000000), (16368904330854819378253627845071362987312218683/643893399418687042878889152000000000000000000000), (4990054129998710970373850225458140918261094739/176755050820816050986361728000000000000000000000), (10960731733014111797311664117624731201995791991/353510101641632101972723456000000000000000000000)]
    reserve := (9845560011/500000000000) }

theorem tilt_050_016_valid : tilt_050_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_016]
  · intro i; fin_cases i <;> norm_num [tilt_050_016]
  · norm_num [tilt_050_016]
  · norm_num [tilt_050_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_016]

def tilt_050_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-347551600787717939721794040274935971469/5913168812881519337941100000000000000000), (175028375726269/293109250000000), (-1666030187057928429070756174671935971469/2956584406440759668970550000000000000000), (175028375726269/293109250000000), (-2984508773328138918419718309068935971469/5913168812881519337941100000000000000000)]
    bernstein := [(18805620288491366107164610582410433756694211/946107010061043094070576000000000000000000000), (6152876232348504518797827385318094439485137/270316288588869455448736000000000000000000000), (41534993905735602869503560565859334882371959/1621897731533216732692416000000000000000000000), (12653057353267661292609803596475296040123247/445226828264020279562624000000000000000000000), (27776912249684588321170296629817332555619043/890453656528040559125248000000000000000000000)]
    reserve := (2484605347/125000000000) }

theorem tilt_050_017_valid : tilt_050_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_017]
  · intro i; fin_cases i <;> norm_num [tilt_050_017]
  · norm_num [tilt_050_017]
  · norm_num [tilt_050_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_017]

def tilt_050_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-347551600787717939721794040274935971469/5913168812881519337941100000000000000000), (175028375726269/293109250000000), (-1666030187057928429070756174671935971469/2956584406440759668970550000000000000000), (175028375726269/293109250000000), (-2984508773328138918419718309068935971469/5913168812881519337941100000000000000000)]
    bernstein := [(18805620288491366107164610582410433756694211/946107010061043094070576000000000000000000000), (6152876232348504518797827385318094439485137/270316288588869455448736000000000000000000000), (41534993905735602869503560565859334882371959/1621897731533216732692416000000000000000000000), (12653057353267661292609803596475296040123247/445226828264020279562624000000000000000000000), (27776912249684588321170296629817332555619043/890453656528040559125248000000000000000000000)]
    reserve := (2484605347/125000000000) }

theorem tilt_050_018_valid : tilt_050_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_018]
  · intro i; fin_cases i <;> norm_num [tilt_050_018]
  · norm_num [tilt_050_018]
  · norm_num [tilt_050_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_018]

def tilt_050_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-347551600787717939721794040274935971469/5913168812881519337941100000000000000000), (175028375726269/293109250000000), (-1666030187057928429070756174671935971469/2956584406440759668970550000000000000000), (175028375726269/293109250000000), (-2984508773328138918419718309068935971469/5913168812881519337941100000000000000000)]
    bernstein := [(18805620288491366107164610582410433756694211/946107010061043094070576000000000000000000000), (6152876232348504518797827385318094439485137/270316288588869455448736000000000000000000000), (41534993905735602869503560565859334882371959/1621897731533216732692416000000000000000000000), (12653057353267661292609803596475296040123247/445226828264020279562624000000000000000000000), (27776912249684588321170296629817332555619043/890453656528040559125248000000000000000000000)]
    reserve := (2484605347/125000000000) }

theorem tilt_050_019_valid : tilt_050_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_019]
  · intro i; fin_cases i <;> norm_num [tilt_050_019]
  · norm_num [tilt_050_019]
  · norm_num [tilt_050_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_019]

def tilt_050_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1393583/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9926463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(62249/1562500), (1/100000000), (1172437/20000000), (1598867/25000000), (1/100000000), (3547187/100000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-347551600787717939721794040274935971469/5913168812881519337941100000000000000000), (175028375726269/293109250000000), (-1666030187057928429070756174671935971469/2956584406440759668970550000000000000000), (175028375726269/293109250000000), (-2984508773328138918419718309068935971469/5913168812881519337941100000000000000000)]
    bernstein := [(18805620288491366107164610582410433756694211/946107010061043094070576000000000000000000000), (6152876232348504518797827385318094439485137/270316288588869455448736000000000000000000000), (41534993905735602869503560565859334882371959/1621897731533216732692416000000000000000000000), (12653057353267661292609803596475296040123247/445226828264020279562624000000000000000000000), (27776912249684588321170296629817332555619043/890453656528040559125248000000000000000000000)]
    reserve := (2484605347/125000000000) }

theorem tilt_050_020_valid : tilt_050_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_050_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_050_020]
  · intro i; fin_cases i <;> norm_num [tilt_050_020]
  · norm_num [tilt_050_020]
  · norm_num [tilt_050_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_050_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_050_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_050_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_050_020]

def tiltBundle050_row : Alternative → Row
  | .zero => tilt_050_000
  | (.spike 0 false false) => tilt_050_001
  | (.spike 0 false true) => tilt_050_002
  | (.spike 0 true false) => tilt_050_003
  | (.spike 0 true true) => tilt_050_004
  | (.spike 1 false false) => tilt_050_005
  | (.spike 1 false true) => tilt_050_006
  | (.spike 1 true false) => tilt_050_007
  | (.spike 1 true true) => tilt_050_008
  | (.spike 2 false false) => tilt_050_009
  | (.spike 2 false true) => tilt_050_010
  | (.spike 2 true false) => tilt_050_011
  | (.spike 2 true true) => tilt_050_012
  | (.spike 3 false false) => tilt_050_013
  | (.spike 3 false true) => tilt_050_014
  | (.spike 3 true false) => tilt_050_015
  | (.spike 3 true true) => tilt_050_016
  | (.spike 4 false false) => tilt_050_017
  | (.spike 4 false true) => tilt_050_018
  | (.spike 4 true false) => tilt_050_019
  | (.spike 4 true true) => tilt_050_020

def tiltBundle050 : TiltBundle where
  interval := ⟨(3/20), (7/40)⟩
  lambda := ![(22297327/100000000), (22297327/100000000), (7849747/50000000), (9926463/50000000), (9926463/50000000), 0, 0]
  row := tiltBundle050_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_050_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_050_001_valid | exact tilt_050_002_valid | exact tilt_050_003_valid | exact tilt_050_004_valid | exact tilt_050_005_valid | exact tilt_050_006_valid | exact tilt_050_007_valid | exact tilt_050_008_valid | exact tilt_050_009_valid | exact tilt_050_010_valid | exact tilt_050_011_valid | exact tilt_050_012_valid | exact tilt_050_013_valid | exact tilt_050_014_valid | exact tilt_050_015_valid | exact tilt_050_016_valid | exact tilt_050_017_valid | exact tilt_050_018_valid | exact tilt_050_019_valid | exact tilt_050_020_valid
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
