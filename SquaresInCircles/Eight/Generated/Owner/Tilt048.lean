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

def tilt_048_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-585040567818251781808515994100310791873/11067534731168667122211476000000000000000), (16702072116009/30223910000000), (-3048794324429619509997751434673950791873/5533767365584333561105738000000000000000), (16702072116009/30223910000000), (-5512548081040987238186986875247590791873/11067534731168667122211476000000000000000)]
    bernstein := [(1378998968056860123027936106645346308682514847/453326222588668605325782056960000000000000000000), (201194737244264690664677172897712751338335463/45332622258866860532578205696000000000000000000), (79204408251386254938501443618330674966221709/13599786677660058159773461708800000000000000000), (652734076762938538750584272899323176967499/90665244517733721065156411392000000000000000), (15530339576588664999533237426386468173463/1813304890354674421303128227840000000000000)]
    reserve := (1520978601/500000000000) }

theorem tilt_048_000_valid : tilt_048_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_000]
  · intro i; fin_cases i <;> norm_num [tilt_048_000]
  · norm_num [tilt_048_000]
  · norm_num [tilt_048_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_000]

def tilt_048_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![(22261/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1747114536416107179756205210178540636089/33202604193506001366634428000000000000000), (16702072116009/30223910000000), (-9138375806250210364323911531899460636089/16601302096753000683317214000000000000000), (16702072116009/30223910000000), (-16529637076084313548891617853620380636089/33202604193506001366634428000000000000000)]
    bernstein := [(4473324831882220223681019410133595344944104871/1359978667766005815977346170880000000000000000000), (637263709508577788339285337168406594682166959/135997866776600581597734617088000000000000000000), (247731617504386176382385703674578427215321637/40799360032980174479320385126400000000000000000), (2025758698593890190003997787094588637317107/271995733553201163195469234176000000000000000), (47944229959297534996718640767843608500959/5439914671064023263909384683520000000000000)]
    reserve := (822315257/250000000000) }

theorem tilt_048_001_valid : tilt_048_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_001]
  · intro i; fin_cases i <;> norm_num [tilt_048_001]
  · norm_num [tilt_048_001]
  · norm_num [tilt_048_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_001]

def tilt_048_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, (3297/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (5787/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-9439965404371848829761302956397191564948681/177910620803536323989549476700000000000000000), (16702072116009/30223910000000), (-49044807041899585060403262663618454564948681/88955310401768161994774738350000000000000000), (16702072116009/30223910000000), (-88649648679427321291045222370839717564948681/177910620803536323989549476700000000000000000)]
    bernstein := [(20678881682341099425438528560998227505419605483159/7287219028112847830611946565632000000000000000000000), (3085146020360136964323149019026244181217371386911/728721902811284783061194656563200000000000000000000), (1228428681846650350857582623184971533525995126773/218616570843385434918358396968960000000000000000000), (10193707543501587234848603927489493414127978403/1457443805622569566122389313126400000000000000000), (243661139932469496982486780270498921923672911/29148876112451391322447786262528000000000000000)]
    reserve := (14188459/5000000000) }

theorem tilt_048_002_valid : tilt_048_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_002]
  · intro i; fin_cases i <;> norm_num [tilt_048_002]
  · norm_num [tilt_048_002]
  · norm_num [tilt_048_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_002]

def tilt_048_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (445667/4000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(993371/25000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-7262646900405157907172365517036821227407/138205855989986451505851800000000000000000), (16702072116009/30223910000000), (-38028775505547872964831874923138821227407/69102927994993225752925900000000000000000), (16702072116009/30223910000000), (-68794904110690588022491384329240821227407/138205855989986451505851800000000000000000)]
    bernstein := [(19028413884607542254450656098810426048760685073/5660911861349845053679689728000000000000000000000), (2693486895038177738956356939807011858738726217/566091186134984505367968972800000000000000000000), (347821182534755086934433483180013016675426177/56609118613498450536796897280000000000000000000), (8514214024383284629812020999332389704367141/1132182372269969010735937945600000000000000000), (201210256355312388195183716322902812568217/22643647445399380214718758912000000000000000)]
    reserve := (1680684521/500000000000) }

theorem tilt_048_003_valid : tilt_048_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_003]
  · intro i; fin_cases i <;> norm_num [tilt_048_003]
  · norm_num [tilt_048_003]
  · norm_num [tilt_048_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_003]

def tilt_048_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5559707/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981439/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-14665255187408395056767904333096217940609/276965094142528656210523100000000000000000), (16702072116009/30223910000000), (-76320701293410486066296478989655217940609/138482547071264328105261550000000000000000), (16702072116009/30223910000000), (-137976147399412577075825053646214217940609/276965094142528656210523100000000000000000)]
    bernstein := [(33475625302384619774018079318274452507923613151/11344490256077973758383026176000000000000000000000), (448306596500350092752182118516074138087871189/103131729600708852348936601600000000000000000000), (1950987954343811157110625942289867753644446797/340334707682339212751490785280000000000000000000), (1466092057941035268357489065837159639552897/206263459201417704697873203200000000000000000), (384487204239550196963549532119784368037079/45377961024311895033532104704000000000000000)]
    reserve := (2950826749/1000000000000) }

theorem tilt_048_004_valid : tilt_048_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_004]
  · intro i; fin_cases i <;> norm_num [tilt_048_004]
  · norm_num [tilt_048_004]
  · norm_num [tilt_048_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_004]

def tilt_048_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (6362681/100000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-5821226327626347342964001443250020673829/110622406542234123953528060000000000000000), (16702072116009/30223910000000), (-30446978701934908264629201519823420673829/55311203271117061976764030000000000000000), (16702072116009/30223910000000), (-55072731076243469186294401596396820673829/110622406542234123953528060000000000000000)]
    bernstein := [(14891477718835168769347412677179985184897260731/4531093771969909717136509337600000000000000000000), (2121947286739857957673017358089696171181348899/453109377196990971713650933760000000000000000000), (275000607965196135446794500871370473054843019/45310937719699097171365093376000000000000000000), (518984130389293544753311675993253942684979/69709134953383226417484759040000000000000000), (944896279292939968328720250590059326171/107244823005204963719207321600000000000000)]
    reserve := (1643254197/500000000000) }

theorem tilt_048_005_valid : tilt_048_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_005]
  · intro i; fin_cases i <;> norm_num [tilt_048_005]
  · norm_num [tilt_048_005]
  · norm_num [tilt_048_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_005]

def tilt_048_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (6368773/100000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-29315018009356055819616463694757595755789/553641614267007923479019900000000000000000), (16702072116009/30223910000000), (-152561670502371387302332979961468595755789/276820807133503961739509950000000000000000), (16702072116009/30223910000000), (-275808322995386718785049496228179595755789/553641614267007923479019900000000000000000)]
    bernstein := [(66925294198341762923854758908175494635526793171/22677160520376644545700655104000000000000000000000), (9858500526348052058958161748508552919468737659/2267716052037664454570065510400000000000000000000), (1300070524440571680264830420035179251356460579/226771605203766445457006551040000000000000000000), (32239014487329307592169561536652821808408207/4535432104075328909140131020800000000000000000), (768609704518001870928983618778477117271659/90708642081506578182802620416000000000000000)]
    reserve := (2951220199/1000000000000) }

theorem tilt_048_006_valid : tilt_048_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_006]
  · intro i; fin_cases i <;> norm_num [tilt_048_006]
  · norm_num [tilt_048_006]
  · norm_num [tilt_048_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_006]

def tilt_048_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3020671/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-93877121728045221628131261682820812979/1784070379609729669416380000000000000000), (16702072116009/30206710000000), (-491523846109948406078171288542721812979/892035189804864834708190000000000000000), (16702072116009/30206710000000), (-889170570491851590528211315402622812979/1784070379609729669416380000000000000000)]
    bernstein := [(242479323778958842717369730772229556407577581/73075522748814527259294924800000000000000000000), (34458024893326818166798884018082998794932549/7307552274881452725929492480000000000000000000), (13377470766043811378972296092524491615266007/2192265682464435817778847744000000000000000000), (109299476044514949069918444271923634096177/14615104549762905451858984960000000000000000), (2585344601860320390827619074693397406549/292302090995258109037179699200000000000000)]
    reserve := (3318201699/1000000000000) }

theorem tilt_048_007_valid : tilt_048_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_007]
  · intro i; fin_cases i <;> norm_num [tilt_048_007]
  · norm_num [tilt_048_007]
  · norm_num [tilt_048_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_007]

def tilt_048_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3024111/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-2931925208259431628997370838500210978621/55369165543785051470206980000000000000000), (5567357372003/10080370000000), (-15242414318534110192938484411579679978621/27684582771892525735103490000000000000000), (5567357372003/10080370000000), (-27552903428808788756879597984659148978621/55369165543785051470206980000000000000000)]
    bernstein := [(6621325751945063220896006441490837277400854819/2267921020673435708219677900800000000000000000000), (978616464571795560223570660445831251102687051/226792102067343570821967790080000000000000000000), (387817904488675598489044290342276800688936793/68037630620203071246590337024000000000000000000), (3208997178385456562499200515023805424174623/453584204134687141643935580160000000000000000), (76558671791989367725732861315060705813051/9071684082693742832878711603200000000000000)]
    reserve := (2919557467/1000000000000) }

theorem tilt_048_008_valid : tilt_048_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_008]
  · intro i; fin_cases i <;> norm_num [tilt_048_008]
  · norm_num [tilt_048_008]
  · norm_num [tilt_048_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_008]

def tilt_048_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3181341/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-7276544068178603525884350472588949142437/138278029910456633820099150000000000000000), (16702072116009/30223910000000), (-38058739373991975086980722142332449142437/69139014955228316910049575000000000000000), (16702072116009/30223910000000), (-68840934679805346648077093812075949142437/138278029910456633820099150000000000000000)]
    bernstein := [(18613929409644501456126403655449486752578269243/5663868105132303721271261184000000000000000000000), (2652392400436841771467664966062138741504906147/566386810513230372127126118400000000000000000000), (1031239786298977269858118162652815739024063521/169916043153969111638137835520000000000000000000), (8433408947574384248498144273535662285259031/1132773621026460744254252236800000000000000000), (199607677834346882382291199400369394928147/22655472420529214885085044736000000000000000)]
    reserve := (3286434123/1000000000000) }

theorem tilt_048_009_valid : tilt_048_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_009]
  · intro i; fin_cases i <;> norm_num [tilt_048_009]
  · norm_num [tilt_048_009]
  · norm_num [tilt_048_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_009]

def tilt_048_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (6368773/100000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-29286099949983620490875695688203573996539/553641614267007923479019900000000000000000), (16702072116009/30223910000000), (-152532752442998951973592211954914573996539/276820807133503961739509950000000000000000), (16702072116009/30223910000000), (-275779404936014283456308728221625573996539/553641614267007923479019900000000000000000)]
    bernstein := [(68139949885581597486106912904714436591159632421/22677160520376644545700655104000000000000000000000), (9980134771220548993212389173867876068551550909/2267716052037664454570065510400000000000000000000), (1312251456884900758452783781547879589505183829/226771605203766445457006551040000000000000000000), (32482996154254544460755421207949103391200457/4535432104075328909140131020800000000000000000), (773496856551943441486173411886106794584909/90708642081506578182802620416000000000000000)]
    reserve := (187798947/62500000000) }

theorem tilt_048_010_valid : tilt_048_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_010]
  · intro i; fin_cases i <;> norm_num [tilt_048_010]
  · norm_num [tilt_048_010]
  · norm_num [tilt_048_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_010]

def tilt_048_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5059/25000000), 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1747842918734857061564169960732606875689/33202604193506001366634428000000000000000), (16702072116009/30223910000000), (-9139104188568960246131876282453526875689/16601302096753000683317214000000000000000), (16702072116009/30223910000000), (-16530365458403063430699582604174446875689/33202604193506001366634428000000000000000)]
    bernstein := [(4442730326401751869393743317336201065112809271/1359978667766005815977346170880000000000000000000), (634200010379303916724960050295160353730074559/135997866776600581597734617088000000000000000000), (246811184804798469487760311236173204418708437/40799360032980174479320385126400000000000000000), (2019613336970597437190199186669931773811907/271995733553201163195469234176000000000000000), (47821133347428804971172597924206414008559/5439914671064023263909384683520000000000000)]
    reserve := (816691179/250000000000) }

theorem tilt_048_011_valid : tilt_048_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_011]
  · intro i; fin_cases i <;> norm_num [tilt_048_011]
  · norm_num [tilt_048_011]
  · norm_num [tilt_048_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_011]

def tilt_048_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (695659/6250000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2997/50000000), 0, 0], ![0, 0, 0, (202361/2000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (5261/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-15442206845733802575232835332396799129150099/291131501103391788649772876180000000000000000), (16702072116009/30223910000000), (-80251249413395830665250673596686399329150099/145565750551695894324886438090000000000000000), (16702072116009/30223910000000), (-145060291981057858755268511860975999529150099/291131501103391788649772876180000000000000000)]
    bernstein := [(34060372891060876205079883004501033510878368517261/11924746285194927663094697008332800000000000000000000), (5070700587215171418696666838622503043038257239269/1192474628519492766309469700833280000000000000000000), (2016858120527696436929300351150626831546281846967/357742388555847829892840910249984000000000000000000), (16725415887098543332025500176895696100400614737/2384949257038985532618939401666560000000000000000), (399616796694742314958311874318703131733633269/47698985140779710652378788033331200000000000000)]
    reserve := (114251061/40000000000) }

theorem tilt_048_012_valid : tilt_048_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_012]
  · intro i; fin_cases i <;> norm_num [tilt_048_012]
  · norm_num [tilt_048_012]
  · norm_num [tilt_048_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_012]

def tilt_048_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10128169/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (1806017/50000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-181664030838339423643750700760005381883841/3455145664088933298655671050000000000000000), (16702072116009/30223910000000), (-950817082200817904408125436747739881883841/1727572832044466649327835525000000000000000), (16702072116009/30223910000000), (-1719970133563296385172500172735474381883841/3455145664088933298655671050000000000000000)]
    bernstein := [(471598243350616582636250533963320637481166410399/141522766401082707912936286208000000000000000000000), (66925386767608617041635608121346980916026384871/14152276640108270791293628620800000000000000000000), (25962873944193913455632724024391803735992295053/4245682992032481237388088586240000000000000000000), (212029348411306747925426133375757332446033483/28304553280216541582587257241600000000000000000), (5013710747083787212459065924108687061630871/566091065604330831651745144832000000000000000)]
    reserve := (3332313629/1000000000000) }

theorem tilt_048_013_valid : tilt_048_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_013]
  · intro i; fin_cases i <;> norm_num [tilt_048_013]
  · norm_num [tilt_048_013]
  · norm_num [tilt_048_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_013]

def tilt_048_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2526983/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (1809633/50000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-183287696128660110056512124165665666026841/3462063542891483652726501450000000000000000), (16702072116009/30223910000000), (-953980742648286459410409538536456166026841/1731031771445741826363250725000000000000000), (16702072116009/30223910000000), (-1724673789167912808764306952907246666026841/3462063542891483652726501450000000000000000)]
    bernstein := [(419620832388486981035110661500526864828161787399/141806122716835170415677499392000000000000000000000), (61759871107204527232876782878007462214548217871/14180612271683517041567749939200000000000000000000), (24422714259956830105159392999690310413859914053/4254183681505055112470324981760000000000000000000), (201823773321573699913602484678634366331542483/28361224543367034083135499878400000000000000000), (4810819606664051670429291931789775841463871/567224490867340681662709997568000000000000000)]
    reserve := (2959116463/1000000000000) }

theorem tilt_048_014_valid : tilt_048_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_014]
  · intro i; fin_cases i <;> norm_num [tilt_048_014]
  · norm_num [tilt_048_014]
  · norm_num [tilt_048_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_014]

def tilt_048_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5059/25000000), 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1747842918734857061564169960732606875689/33202604193506001366634428000000000000000), (16702072116009/30223910000000), (-9139104188568960246131876282453526875689/16601302096753000683317214000000000000000), (16702072116009/30223910000000), (-16530365458403063430699582604174446875689/33202604193506001366634428000000000000000)]
    bernstein := [(4442730326401751869393743317336201065112809271/1359978667766005815977346170880000000000000000000), (634200010379303916724960050295160353730074559/135997866776600581597734617088000000000000000000), (246811184804798469487760311236173204418708437/40799360032980174479320385126400000000000000000), (2019613336970597437190199186669931773811907/271995733553201163195469234176000000000000000), (47821133347428804971172597924206414008559/5439914671064023263909384683520000000000000)]
    reserve := (816691179/250000000000) }

theorem tilt_048_015_valid : tilt_048_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_015]
  · intro i; fin_cases i <;> norm_num [tilt_048_015]
  · norm_num [tilt_048_015]
  · norm_num [tilt_048_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_015]

def tilt_048_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (695659/6250000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2997/50000000), 0, 0], ![0, 0, 0, (202361/2000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (5261/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-15442206845733802575232835332396799129150099/291131501103391788649772876180000000000000000), (16702072116009/30223910000000), (-80251249413395830665250673596686399329150099/145565750551695894324886438090000000000000000), (16702072116009/30223910000000), (-145060291981057858755268511860975999529150099/291131501103391788649772876180000000000000000)]
    bernstein := [(34060372891060876205079883004501033510878368517261/11924746285194927663094697008332800000000000000000000), (5070700587215171418696666838622503043038257239269/1192474628519492766309469700833280000000000000000000), (2016858120527696436929300351150626831546281846967/357742388555847829892840910249984000000000000000000), (16725415887098543332025500176895696100400614737/2384949257038985532618939401666560000000000000000), (399616796694742314958311874318703131733633269/47698985140779710652378788033331200000000000000)]
    reserve := (114251061/40000000000) }

theorem tilt_048_016_valid : tilt_048_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_016]
  · intro i; fin_cases i <;> norm_num [tilt_048_016]
  · norm_num [tilt_048_016]
  · norm_num [tilt_048_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_016]

def tilt_048_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-585040567818251781808515994100310791873/11067534731168667122211476000000000000000), (16702072116009/30223910000000), (-3048794324429619509997751434673950791873/5533767365584333561105738000000000000000), (16702072116009/30223910000000), (-5512548081040987238186986875247590791873/11067534731168667122211476000000000000000)]
    bernstein := [(1378998968056860123027936106645346308682514847/453326222588668605325782056960000000000000000000), (201194737244264690664677172897712751338335463/45332622258866860532578205696000000000000000000), (79204408251386254938501443618330674966221709/13599786677660058159773461708800000000000000000), (652734076762938538750584272899323176967499/90665244517733721065156411392000000000000000), (15530339576588664999533237426386468173463/1813304890354674421303128227840000000000000)]
    reserve := (1520978601/500000000000) }

theorem tilt_048_017_valid : tilt_048_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_017]
  · intro i; fin_cases i <;> norm_num [tilt_048_017]
  · norm_num [tilt_048_017]
  · norm_num [tilt_048_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_017]

def tilt_048_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-585040567818251781808515994100310791873/11067534731168667122211476000000000000000), (16702072116009/30223910000000), (-3048794324429619509997751434673950791873/5533767365584333561105738000000000000000), (16702072116009/30223910000000), (-5512548081040987238186986875247590791873/11067534731168667122211476000000000000000)]
    bernstein := [(1378998968056860123027936106645346308682514847/453326222588668605325782056960000000000000000000), (201194737244264690664677172897712751338335463/45332622258866860532578205696000000000000000000), (79204408251386254938501443618330674966221709/13599786677660058159773461708800000000000000000), (652734076762938538750584272899323176967499/90665244517733721065156411392000000000000000), (15530339576588664999533237426386468173463/1813304890354674421303128227840000000000000)]
    reserve := (1520978601/500000000000) }

theorem tilt_048_018_valid : tilt_048_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_018]
  · intro i; fin_cases i <;> norm_num [tilt_048_018]
  · norm_num [tilt_048_018]
  · norm_num [tilt_048_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_018]

def tilt_048_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-585040567818251781808515994100310791873/11067534731168667122211476000000000000000), (16702072116009/30223910000000), (-3048794324429619509997751434673950791873/5533767365584333561105738000000000000000), (16702072116009/30223910000000), (-5512548081040987238186986875247590791873/11067534731168667122211476000000000000000)]
    bernstein := [(1378998968056860123027936106645346308682514847/453326222588668605325782056960000000000000000000), (201194737244264690664677172897712751338335463/45332622258866860532578205696000000000000000000), (79204408251386254938501443618330674966221709/13599786677660058159773461708800000000000000000), (652734076762938538750584272899323176967499/90665244517733721065156411392000000000000000), (15530339576588664999533237426386468173463/1813304890354674421303128227840000000000000)]
    reserve := (1520978601/500000000000) }

theorem tilt_048_019_valid : tilt_048_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_019]
  · intro i; fin_cases i <;> norm_num [tilt_048_019]
  · norm_num [tilt_048_019]
  · norm_num [tilt_048_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_019]

def tilt_048_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226109/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10118051/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3977461/100000000), (1/100000000), (3022391/50000000), (3182863/50000000), (1/100000000), (72313/2000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-585040567818251781808515994100310791873/11067534731168667122211476000000000000000), (16702072116009/30223910000000), (-3048794324429619509997751434673950791873/5533767365584333561105738000000000000000), (16702072116009/30223910000000), (-5512548081040987238186986875247590791873/11067534731168667122211476000000000000000)]
    bernstein := [(1378998968056860123027936106645346308682514847/453326222588668605325782056960000000000000000000), (201194737244264690664677172897712751338335463/45332622258866860532578205696000000000000000000), (79204408251386254938501443618330674966221709/13599786677660058159773461708800000000000000000), (652734076762938538750584272899323176967499/90665244517733721065156411392000000000000000), (15530339576588664999533237426386468173463/1813304890354674421303128227840000000000000)]
    reserve := (1520978601/500000000000) }

theorem tilt_048_020_valid : tilt_048_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_048_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_048_020]
  · intro i; fin_cases i <;> norm_num [tilt_048_020]
  · norm_num [tilt_048_020]
  · norm_num [tilt_048_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_048_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_048_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_048_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_048_020]

def tiltBundle048_row : Alternative → Row
  | .zero => tilt_048_000
  | (.spike 0 false false) => tilt_048_001
  | (.spike 0 false true) => tilt_048_002
  | (.spike 0 true false) => tilt_048_003
  | (.spike 0 true true) => tilt_048_004
  | (.spike 1 false false) => tilt_048_005
  | (.spike 1 false true) => tilt_048_006
  | (.spike 1 true false) => tilt_048_007
  | (.spike 1 true true) => tilt_048_008
  | (.spike 2 false false) => tilt_048_009
  | (.spike 2 false true) => tilt_048_010
  | (.spike 2 true false) => tilt_048_011
  | (.spike 2 true true) => tilt_048_012
  | (.spike 3 false false) => tilt_048_013
  | (.spike 3 false true) => tilt_048_014
  | (.spike 3 true false) => tilt_048_015
  | (.spike 3 true true) => tilt_048_016
  | (.spike 4 false false) => tilt_048_017
  | (.spike 4 false true) => tilt_048_018
  | (.spike 4 true false) => tilt_048_019
  | (.spike 4 true true) => tilt_048_020

def tiltBundle048 : TiltBundle where
  interval := ⟨(9/80), (1/8)⟩
  lambda := ![(22261089/100000000), (22261089/100000000), (750281/5000000), (20236101/100000000), (20236101/100000000), 0, 0]
  row := tiltBundle048_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_048_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_048_001_valid | exact tilt_048_002_valid | exact tilt_048_003_valid | exact tilt_048_004_valid | exact tilt_048_005_valid | exact tilt_048_006_valid | exact tilt_048_007_valid | exact tilt_048_008_valid | exact tilt_048_009_valid | exact tilt_048_010_valid | exact tilt_048_011_valid | exact tilt_048_012_valid | exact tilt_048_013_valid | exact tilt_048_014_valid | exact tilt_048_015_valid | exact tilt_048_016_valid | exact tilt_048_017_valid | exact tilt_048_018_valid | exact tilt_048_019_valid | exact tilt_048_020_valid
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
