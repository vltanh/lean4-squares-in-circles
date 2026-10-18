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

def quarter_002_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_002_000_valid : quarter_002_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_000]
  · intro i; fin_cases i <;> norm_num [quarter_002_000]
  · norm_num [quarter_002_000]
  · norm_num [quarter_002_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_000]

def quarter_002_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_002_001_valid : quarter_002_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_001]
  · intro i; fin_cases i <;> norm_num [quarter_002_001]
  · norm_num [quarter_002_001]
  · norm_num [quarter_002_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_001]

def quarter_002_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3267003/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (912737/12500000)]
    alternative := .zero
    polynomial := [(-2169191422463283237963/19147396786000000000000), (-1680685461741/903700000000), (-14934122485480637997963/9573698393000000000000), (-1680685461741/903700000000), (-27699053548497992757963/19147396786000000000000)]
    bernstein := [(18336304958251293684958548357/49017335772160000000000000000), (4489371739241140037519205867/12254333943040000000000000000), (1098455096793363008082180577/3063583485760000000000000000), (38369849824100541136894641/109413695920000000000000000), (9375388818738124642177371/27353423980000000000000000)]
    reserve := (8568752513/25000000000) }

theorem quarter_002_002_valid : quarter_002_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_002]
  · intro i; fin_cases i <;> norm_num [quarter_002_002]
  · norm_num [quarter_002_002]
  · norm_num [quarter_002_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_002]

def quarter_002_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (12539659/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (1879413/25000000)]
    alternative := .zero
    polynomial := [(-900823623365753756879/9856581478500000000000), (-222859008882521/125294200000000), (-7471877876655210566879/4928290739250000000000), (-222859008882521/125294200000000), (-14042932129944667376879/9856581478500000000000)]
    bernstein := [(33733764821576472263025601/98565814785000000000000000), (131989447673509091897660587/394263259140000000000000000), (1548188615022030467277299107/4731159109680000000000000000), (2016220219734266352555338603/6308212146240000000000000000), (7870928602205907369811025761/25232848584960000000000000000)]
    reserve := (311931828691/1000000000000) }

theorem quarter_002_003_valid : quarter_002_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_003]
  · intro i; fin_cases i <;> norm_num [quarter_002_003]
  · norm_num [quarter_002_003]
  · norm_num [quarter_002_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_003]

def quarter_002_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (23954683/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (3859927/50000000)]
    alternative := .zero
    polynomial := [(-2911757496123219851943/40486774303000000000000), (-1313146353535203/771985400000000), (-29902940094878057831943/20243387151500000000000), (-1313146353535203/771985400000000), (-56894122693632895811943/40486774303000000000000)]
    bernstein := [(32284069972296337902630332937/103646142215680000000000000000), (3153420973043746955499217587/10364614221568000000000000000), (307766680163278571481441041/1036461422156800000000000000), (1765375410924236418042747/6096831895040000000000000), (171989599413010471896969/609683189504000000000000)]
    reserve := (141048336557/500000000000) }

theorem quarter_002_004_valid : quarter_002_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_004]
  · intro i; fin_cases i <;> norm_num [quarter_002_004]
  · norm_num [quarter_002_004]
  · norm_num [quarter_002_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_004]

def quarter_002_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (355679/1562500), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (7907263/100000000)]
    alternative := .zero
    polynomial := [(-907114696706034174759/16587856321400000000000), (-642966360237003/395363150000000), (-11965685467053658698759/8293928160700000000000), (-642966360237003/395363150000000), (-23024256237401283222759/16587856321400000000000)]
    bernstein := [(70367095055716961453097/249793601075200000000000), (686137161622951353525729/2497936010752000000000000), (113629684704909812327936153/424649121827840000000000000), (157975382968151158449267207/606641602611200000000000000), (118134002360098990774428411/466647386624000000000000000)]
    reserve := (126577374851/500000000000) }

theorem quarter_002_005_valid : quarter_002_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_005]
  · intro i; fin_cases i <;> norm_num [quarter_002_005]
  · norm_num [quarter_002_005]
  · norm_num [quarter_002_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_005]

def quarter_002_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (860301/4000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (8078689/100000000)]
    alternative := .zero
    polynomial := [(-197092352289628577433/4984551113000000000000), (-1255496754111699/807868900000000), (-3520126394392621157433/2492275556500000000000), (-1255496754111699/807868900000000), (-6843160436495613737433/4984551113000000000000)]
    bernstein := [(3225949326069650397436388487/12760450849280000000000000000), (392357672769641300620139043/1595056356160000000000000000), (11916937875783963500254713/49845511130000000000000000), (2892146086420452069769539/12461377782500000000000000), (175250436533962308848823/778836111406250000000000)]
    reserve := (1406348797/6250000000) }

theorem quarter_002_006_valid : quarter_002_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_006]
  · intro i; fin_cases i <;> norm_num [quarter_002_006]
  · norm_num [quarter_002_006]
  · norm_num [quarter_002_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_006]

def quarter_002_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1261833/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (8233003/100000000)]
    alternative := .zero
    polynomial := [(-18207877560843676587/690847747736000000000), (-610922227224111/411650150000000), (-478773038112525358347/345423873868000000000), (-610922227224111/411650150000000), (-939338198664207040107/690847747736000000000)]
    bernstein := [(24256930460084798244717/107944960583750000000000), (376622922361305081633663/1727119369340000000000000), (1459948347390081789178733/6908477477360000000000000), (2659393558265338863882147/13004192898560000000000000), (20555908005932725264491429/104033543188480000000000000)]
    reserve := (19758923301/100000000000) }

theorem quarter_002_007_valid : quarter_002_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_007]
  · intro i; fin_cases i <;> norm_num [quarter_002_007]
  · norm_num [quarter_002_007]
  · norm_num [quarter_002_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_007]

def quarter_002_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(31327349/100000000), (31327349/100000000), (2195167/100000000), (2195167/100000000), (81381/10000000), (81381/10000000), (31327349/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8946151/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8120937/100000000), (1/100000000), (295783/50000000), (1/100000000), (4038997/50000000)]
    alternative := .zero
    polynomial := [(116601992067780741545977872403/9701812597816842987000000000000), (-47131536166427387369/38140046721150000000), (-5808942622036828316661796412597/4850906298908421493500000000000), (-47131536166427387369/38140046721150000000), (-11734487236141437374869570697597/9701812597816842987000000000000)]
    bernstein := [(989498532442168109666356684420849/5020545835943221760000000000000000), (46614572097433141388517307883989237/243496473043246255360000000000000000), (58631298768062615999890971788098691/315720003183192178560000000000000000), (558492367346087784487320939492900967/3104580031301389755840000000000000000), (270091698613958391137746975566076243/1552290015650694877920000000000000000)]
    reserve := (1359340957/7812500000) }

theorem quarter_002_008_valid : quarter_002_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_008]
  · intro i; fin_cases i <;> norm_num [quarter_002_008]
  · norm_num [quarter_002_008]
  · norm_num [quarter_002_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_008]

def quarter_002_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(14589197/50000000), (14589197/50000000), (4474679/100000000), (4474679/100000000), (175773/10000000), (175773/10000000), (14589197/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (244867/1562500), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (486249/6250000), (1/100000000), (75923/6250000), (1/100000000), (3943683/50000000)]
    alternative := .zero
    polynomial := [(2161291464230030952960186521/48530283142543947000000000000), (-509060018011502933717/511363177351200000000), (-24581577814415291890955723479/24265141571271973500000000000), (-509060018011502933717/511363177351200000000), (-51324447093060614734871633479/48530283142543947000000000000)]
    bernstein := [(1350231226752651010797799920924401/7764845302807031520000000000000000), (175213374496867078480828215126419/1035312707040937536000000000000000), (613150494025143022762414914986183/3727125745347375129600000000000000), (15873407233056227974304867656249/99390019875930003456000000000000), (1231078794640590320413399356049/7951201590074400276480000000000)]
    reserve := (77414638573/500000000000) }

theorem quarter_002_009_valid : quarter_002_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_009]
  · intro i; fin_cases i <;> norm_num [quarter_002_009]
  · norm_num [quarter_002_009]
  · norm_num [quarter_002_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_009]

def quarter_002_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(2731771/10000000), (2731771/10000000), (3195531/50000000), (3195531/50000000), (1316187/50000000), (1316187/50000000), (2731771/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6856469/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3733031/50000000), (1/100000000), (109157/6250000), (1/100000000), (7721619/100000000)]
    alternative := .zero
    polynomial := [(52898517228419236695850790941/786613807339964918250000000000), (-229922882587707512357/288250430971890000000), (-340243081787555685421681884059/393306903669982459125000000000), (-229922882587707512357/288250430971890000000), (-733384680803530607539214559059/786613807339964918250000000000)]
    bernstein := [(19946312985925503648291199239029/128878806194579852206080000000000), (40528679943981610793460734097791/268497512905374692096000000000000), (2220990040431759615541976464580467/15102985100927326430400000000000000), (300165885769358290546125171408607/2097636819573239782000000000000000), (364639965545064673219015601763047/2622046024466549727500000000000000)]
    reserve := (34766739613/250000000000) }

theorem quarter_002_010_valid : quarter_002_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_010]
  · intro i; fin_cases i <;> norm_num [quarter_002_010]
  · norm_num [quarter_002_010]
  · norm_num [quarter_002_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_010]

def quarter_002_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(25707813/100000000), (25707813/100000000), (400433/5000000), (400433/5000000), (171481/5000000), (171481/5000000), (25707813/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11972033/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (897019/12500000), (1/100000000), (2201377/100000000), (1/100000000), (7574211/100000000)]
    alternative := .zero
    polynomial := [(2470896546650614929130174776371/29913240436421082786000000000000), (-11479500552724027349/18117896472024000000), (-11168149482604845397840637783629/14956620218210541393000000000000), (-11479500552724027349/18117896472024000000), (-24807195511860305724811450343629/29913240436421082786000000000000)]
    bernstein := [(41593090054325695479754435304140571/299132404364210827860000000000000000), (162633576784281080516764736409643813/1196529617456843311440000000000000000), (1905830579150809340980158701299560317/14358355409482119737280000000000000000), (2478845819051686393948773391751303417/19144473879309492983040000000000000000), (9661294367674150100984208097993410851/76577895517237971932160000000000000000)]
    reserve := (25232593041/200000000000) }

theorem quarter_002_011_valid : quarter_002_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_011]
  · intro i; fin_cases i <;> norm_num [quarter_002_011]
  · norm_num [quarter_002_011]
  · norm_num [quarter_002_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_011]

def quarter_002_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(24314903/100000000), (24314903/100000000), (9380151/100000000), (9380151/100000000), (2073747/50000000), (2073747/50000000), (24314903/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (10411203/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6907193/100000000), (1/100000000), (323941/12500000), (1/100000000), (3720047/50000000)]
    alternative := .zero
    polynomial := [(15863906643207020515325110111/171622489729932326000000000000), (-2550713897024926711907/5139016519614200000000), (-5428565117603837916950141309233/8323690751901717811000000000000), (-2550713897024926711907/5139016519614200000000), (-12395929179598756823886818299233/16647381503803435622000000000000)]
    bernstein := [(5377361540935215167566818323074971727/42617296649736795192320000000000000000), (2634658727858292430374287215359234709/21308648324868397596160000000000000000), (3869071755669194356975198450693412309/31962972487302596394240000000000000000), (630706344521090649289245288449926301/5327162081217099399040000000000000000), (308120304082705662382807321114434367/2663581040608549699520000000000000000)]
    reserve := (57839483647/500000000000) }

theorem quarter_002_012_valid : quarter_002_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_012]
  · intro i; fin_cases i <;> norm_num [quarter_002_012]
  · norm_num [quarter_002_012]
  · norm_num [quarter_002_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_012]

def quarter_002_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(11554689/50000000), (11554689/50000000), (1318539/12500000), (1318539/12500000), (4787621/100000000), (4787621/100000000), (11554689/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4499623/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1664073/25000000), (1/100000000), (731759/25000000), (1/100000000), (457211/6250000)]
    alternative := .zero
    polynomial := [(24277199470082094222812531849/247442673345430612000000000000), (-12858330449716262023/33814776906800000000), (-71375908598484556930588720651/123721336672715306000000000000), (-12858330449716262023/33814776906800000000), (-167029016667051208083989973151/247442673345430612000000000000)]
    bernstein := [(4581701921648304937868864380746049/39590827735268897920000000000000000), (9002525875266859217757025831175649/79181655470537795840000000000000000), (7574808393234674651273708069153621/67869990403318110720000000000000000), (34670318944334663362797517607134449/316726621882151183360000000000000000), (67946711766685475342167401500183649/633453243764302366720000000000000000)]
    reserve := (53631986603/500000000000) }

theorem quarter_002_013_valid : quarter_002_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_013]
  · intro i; fin_cases i <;> norm_num [quarter_002_013]
  · norm_num [quarter_002_013]
  · norm_num [quarter_002_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_013]

def quarter_002_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(2758217/12500000), (2758217/12500000), (11547771/100000000), (11547771/100000000), (42829/800000), (42829/800000), (2758217/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1542089/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6420821/100000000), (1/100000000), (1608107/50000000), (1/100000000), (1439409/20000000)]
    alternative := .zero
    polynomial := [(93482752316724401863728091513/928901654375433401437500000000), (-737439843228497269/2625621458746875000), (-80073554333502003614762210329/154816942395905566906250000000), (-737439843228497269/2625621458746875000), (-573924078317736423552301353487/928901654375433401437500000000)]
    bernstein := [(255254222657828567444984675483168113/2377988235201109507680000000000000000), (26193439329996739315798274548573/247707107833448907050000000000000), (154710211717913996832493229410471/1486242647000693442300000000000000), (15852223384323257386357965523/154816942395905566906250000000), (93482752316724401863728091513/928901654375433401437500000000)]
    reserve := (50318971807/500000000000) }

theorem quarter_002_014_valid : quarter_002_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_014]
  · intro i; fin_cases i <;> norm_num [quarter_002_014]
  · norm_num [quarter_002_014]
  · norm_num [quarter_002_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_014]

def quarter_002_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(21551503/100000000), (21551503/100000000), (6064471/50000000), (6064471/50000000), (5543803/100000000), (5543803/100000000), (21551503/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6535599/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1249761/20000000), (1/100000000), (421213/12500000), (1/100000000), (1776243/25000000)]
    alternative := .zero
    polynomial := [(1796205360631303372929682489/17810323604402487600000000000), (137653840735965147407/211417069326000000000), (-10227201849639499630493808359/20778710871802902200000000000), (137653840735965147407/211417069326000000000), (-73936648622256121393470627577/124672265230817413200000000000)]
    bernstein := [(1796205360631303372929682489/17810323604402487600000000000), (7474729378614803929892453411/71241294417609950400000000000), (21730757279322664730954801416441/199475624369307861120000000000000), (90090209742249582967388173959077/797902497477231444480000000000000), (37288142171717459055306446188302023/319160998990892577792000000000000000)]
    reserve := (20170384329/200000000000) }

theorem quarter_002_015_valid : quarter_002_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_015]
  · intro i; fin_cases i <;> norm_num [quarter_002_015]
  · norm_num [quarter_002_015]
  · norm_num [quarter_002_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_015]

def quarter_002_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(4292787/20000000), (4292787/20000000), (12400691/100000000), (12400691/100000000), (5403407/100000000), (5403407/100000000), (4292787/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5393249/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3063263/50000000), (1/100000000), (3417949/100000000), (1/100000000), (175617/2500000)]
    alternative := .zero
    polynomial := [(366844732235047466220078484243/3677446922312612358000000000000), (100267180554359346557/143456282205600000000), (-908229276968976423059321887007/1838723461156306179000000000000), (100267180554359346557/143456282205600000000), (-2183303286173000312338722258257/3677446922312612358000000000000)]
    bernstein := [(1100816702529111341180033061019299343/9414264121120287636480000000000000000), (27156272258293935142896194227291783/224149145740959229440000000000000000), (884906250849751904395075537312623829/7060698090840215727360000000000000000), (50782288382833754256381991053260281/392261005046678651520000000000000000), (78580283219688047704892629565966143/588391507570017977280000000000000000)]
    reserve := (23386144437/200000000000) }

theorem quarter_002_016_valid : quarter_002_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_016]
  · intro i; fin_cases i <;> norm_num [quarter_002_016]
  · norm_num [quarter_002_016]
  · norm_num [quarter_002_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_016]

def quarter_002_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(21382473/100000000), (21382473/100000000), (12672867/100000000), (12672867/100000000), (5253423/100000000), (5253423/100000000), (21382473/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2125109/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1199899/20000000), (1/100000000), (216651/6250000), (1/100000000), (6929763/100000000)]
    alternative := .zero
    polynomial := [(116992734234338183902843121431/1200970976738096658000000000000), (1036842959159073317671/1385835948989500000000), (-299263402812010949437205988569/600485488369048329000000000000), (1036842959159073317671/1385835948989500000000), (-715519539858360082777255098569/1200970976738096658000000000000)]
    bernstein := [(25684939927052940683385770840686231/192155356278095465280000000000000000), (53060001468836084117288604988106293/384310712556190930560000000000000000), (328405842549326714434012404386837437/2305864275337145583360000000000000000), (225574964030782982015431873183210637/1537242850224763722240000000000000000), (464313264502017923110335999284308711/3074485700449527444480000000000000000)]
    reserve := (66833786017/500000000000) }

theorem quarter_002_017_valid : quarter_002_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_017]
  · intro i; fin_cases i <;> norm_num [quarter_002_017]
  · norm_num [quarter_002_017]
  · norm_num [quarter_002_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_017]

def quarter_002_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(21306833/100000000), (21306833/100000000), (12945443/100000000), (12945443/100000000), (5094307/100000000), (5094307/100000000), (21306833/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1554927/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (18337/312500), (1/100000000), (1757609/50000000), (1/100000000), (136413/2000000)]
    alternative := .zero
    polynomial := [(366380405549301018138225819/3907993118908648000000000000), (106600341107521824449/133408276320000000000), (-8892004558682427271122429229/17585969035088916000000000000), (106600341107521824449/133408276320000000000), (-21081432767308563705488890829/35171938070177832000000000000)]
    bernstein := [(1512219702252007812280724418227739/10004462384406138880000000000000000), (584332615614968789577388960456607/3751673394152302080000000000000000), (2706514190511493381970125153293167/16882530273685359360000000000000000), (57978413447087148915136416292397/351719380701778320000000000000000), (59560054573381322056229688784871/351719380701778320000000000000000)]
    reserve := (37788629817/250000000000) }

theorem quarter_002_018_valid : quarter_002_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_018]
  · intro i; fin_cases i <;> norm_num [quarter_002_018]
  · norm_num [quarter_002_018]
  · norm_num [quarter_002_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_018]

def quarter_002_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(1061839/5000000), (1061839/5000000), (13218337/100000000), (13218337/100000000), (4926493/100000000), (4926493/100000000), (1061839/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1975469/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2865861/50000000), (1/100000000), (3564443/100000000), (1/100000000), (6697853/100000000)]
    alternative := .zero
    polynomial := [(3033411907782516386440251779221/34209947889170365909500000000000), (6540592774843147577/7678046278573200000), (-8824913018272065755634515370779/17104973944585182954750000000000), (6540592774843147577/7678046278573200000), (-20683237944326647897709282520779/34209947889170365909500000000000)]
    bernstein := [(57981835528053468832368726823033421/342099478891703659095000000000000000), (5300627176860555105711199569736889/30408842568151436364000000000000000), (117641673363486018122914706195273827/656830999472071025462400000000000000), (715680405296701049032640288123857/3892331848723383854592000000000000), (117459571803934168068725960834261/622773095795741416734720000000000)]
    reserve := (5296507221/31250000000) }

theorem quarter_002_019_valid : quarter_002_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_019]
  · intro i; fin_cases i <;> norm_num [quarter_002_019]
  · norm_num [quarter_002_019]
  · norm_num [quarter_002_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_019]

def quarter_002_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(529303/2500000), (529303/2500000), (539657/4000000), (539657/4000000), (950079/20000000), (950079/20000000), (529303/2500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (85029/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1397833/25000000), (1/100000000), (1807081/50000000), (1/100000000), (3283317/50000000)]
    alternative := .zero
    polynomial := [(680591792528467525714557278053/8293650387511243941000000000000), (13874042427601576373/15298429506870000000), (-2196155055300235227222840621947/4146825193755621970500000000000), (13874042427601576373/15298429506870000000), (-5072901903128937980160238521947/8293650387511243941000000000000)]
    bernstein := [(256507204544664907148756320030957/1358831679489842207293440000000000), (3292564878489809930726674592814307/16985395993623027591168000000000000), (126688234965729620527210711309419319/636952349760863534668800000000000000), (108242003082311017001453979970459351/530793624800719612224000000000000000), (277247984285037247830410614796183893/1326984062001799030560000000000000000)]
    reserve := (188770403587/1000000000000) }

theorem quarter_002_020_valid : quarter_002_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_020]
  · intro i; fin_cases i <;> norm_num [quarter_002_020]
  · norm_num [quarter_002_020]
  · norm_num [quarter_002_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_020]

def quarter_002_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(2635569/12500000), (2635569/12500000), (1376639/10000000), (1376639/10000000), (2303391/50000000), (2303391/50000000), (2635569/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (5441423/100000000), (1/100000000), (917023/25000000), (1/100000000), (3224753/50000000)]
    alternative := .zero
    polynomial := [(931001636439722641330068351/12377867217880941490000000000), (16241190568821/17004446875000), (-3356557878678534941482498449/6188933608940470745000000000), (16241190568821/17004446875000), (-7644117393796792524295065249/12377867217880941490000000000)]
    bernstein := [(5385803498230856061670502352218403/25745963813192358299200000000000000), (11044688937713587283813445438698007/51491927626384716598400000000000000), (1741033850077561254731186547713591/7921835019443802553600000000000000), (46351271366833357844208593149870527/205967710505538866393600000000000000), (281497627216862694405157100532099/1222360299736135705600000000000000)]
    reserve := (4183804139/20000000000) }

theorem quarter_002_021_valid : quarter_002_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_021]
  · intro i; fin_cases i <;> norm_num [quarter_002_021]
  · norm_num [quarter_002_021]
  · norm_num [quarter_002_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_021]

def quarter_002_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(20895923/100000000), (20895923/100000000), (14047213/100000000), (14047213/100000000), (2304451/50000000), (2304451/50000000), (20895923/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1316907/25000000), (1/100000000), (3735617/100000000), (1/100000000), (1596901/25000000)]
    alternative := .zero
    polynomial := [(70475495878340354468246904601/981986359437882214875000000000), (513673379373887/526762800000000), (-531773294673893889785889383923/981986359437882214875000000000), (513673379373887/526762800000000), (-150562197638058561063534072131/245496589859470553718750000000)]
    bernstein := [(72427059258807375256563576635651647/314235635020122308760000000000000000), (197653661805360504905326514031627923/837961693386992823360000000000000000), (113712795428352239035939061421678463/471353452530183463140000000000000000), (403609117699308090638293428259819/1636643932396470358125000000000000), (17181853048566454109938969153989/68193497183186264921875000000000)]
    reserve := (57621615109/250000000000) }

theorem quarter_002_022_valid : quarter_002_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_022]
  · intro i; fin_cases i <;> norm_num [quarter_002_022]
  · norm_num [quarter_002_022]
  · norm_num [quarter_002_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_022]

def quarter_002_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(5172699/25000000), (5172699/25000000), (14324443/100000000), (14324443/100000000), (4639363/100000000), (4639363/100000000), (5172699/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (5087039/100000000), (1/100000000), (951151/25000000), (1/100000000), (6326337/100000000)]
    alternative := .zero
    polynomial := [(1033398719539223295701852786789/15305124373830980296500000000000), (126723475078179/127175975000000), (-4138950667360962723415645563211/7652562186915490148250000000000), (126723475078179/127175975000000), (-9311300054261148742533143913211/15305124373830980296500000000000)]
    bernstein := [(603050545146407226975634794867341/2391425683411090671328125000000000), (9859302875513208896869567196930713/38262810934577450741250000000000000), (120833307429624392196291631535590163/459153731214929408895000000000000000), (1315750802045448919000324030306217581/4897639799625913694880000000000000000), (10740687396609989977169257849954571429/39181118397007309559040000000000000000)]
    reserve := (126085989067/500000000000) }

theorem quarter_002_023_valid : quarter_002_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_023]
  · intro i; fin_cases i <;> norm_num [quarter_002_023]
  · norm_num [quarter_002_023]
  · norm_num [quarter_002_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_023]

def quarter_002_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(10236807/50000000), (10236807/50000000), (14594073/100000000), (14594073/100000000), (2347753/50000000), (2347753/50000000), (20473613/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4900947/100000000), (1/100000000), (1936899/50000000), (1/100000000), (6266033/100000000)]
    alternative := .zero
    polynomial := [(618327866253366613831308054257/9913531897091371441500000000000), (41622800142737/40841225000000), (-2680517600595078606541855955743/4956765948545685720750000000000), (41622800142737/40841225000000), (-5979363067443523826915019965743/9913531897091371441500000000000)]
    bernstein := [(6962979127472782343399922851326894577/25378641656553910890240000000000000000), (41801314990179890425908095415462169/149286127391493593472000000000000000), (217481178472005348992630200102630643/761359249696617326707200000000000000), (7392473547877331589237167123040361/25378641656553910890240000000000000), (44326868138792542712449315222369/149286127391493593472000000000000)]
    reserve := (137181871703/500000000000) }

theorem quarter_002_024_valid : quarter_002_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_024]
  · intro i; fin_cases i <;> norm_num [quarter_002_024]
  · norm_num [quarter_002_024]
  · norm_num [quarter_002_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_024]

def quarter_002_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(632759/3125000), (632759/3125000), (7426453/50000000), (7426453/50000000), (2387331/50000000), (2387331/50000000), (632759/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (588827/12500000), (1/100000000), (3942183/100000000), (1/100000000), (6206883/100000000)]
    alternative := .zero
    polynomial := [(45000542652213583236131249039/800434041809790783500000000000), (7679839643371/7360337500000), (-216809826831223092191162350961/400217020904895391750000000000), (7679839643371/7360337500000), (-478620196314659767618455950961/800434041809790783500000000000)]
    bernstein := [(60895829601712571408279972092271/204911114703306440576000000000000), (620879134494681104892089644516373/2049111147033064405760000000000000), (18984105450055115412806199491672821/61473334410991932172800000000000000), (64473500313447456757371242933776349/204911114703306440576000000000000000), (656676685868277578559401057703320799/2049111147033064405760000000000000000)]
    reserve := (297181681383/1000000000000) }

theorem quarter_002_025_valid : quarter_002_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_025]
  · intro i; fin_cases i <;> norm_num [quarter_002_025]
  · norm_num [quarter_002_025]
  · norm_num [quarter_002_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_025]

def quarter_002_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(20018249/100000000), (20018249/100000000), (603939/4000000), (603939/4000000), (4874151/100000000), (4874151/100000000), (20018249/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4517251/100000000), (1/100000000), (501119/12500000), (1/100000000), (6148963/100000000)]
    alternative := .zero
    polynomial := [(34067494101705102308097357273/695964321615961892350000000000), (483099942697273/451725100000000), (-189354311843994427286345912977/347982160807980946175000000000), (483099942697273/451725100000000), (-412776117789693956880789183227/695964321615961892350000000000)]
    bernstein := [(571467305020707248754361476268779093/1781668663336862444416000000000000000), (145548982750181748683665746711505939/445417165834215611104000000000000000), (111175756641163502755884368693703791/334062874375661708328000000000000000), (200696316745123916649868261467373/592310060949754802000000000000000), (2400272956117897724348627789465013/6959643216159618923500000000000000)]
    reserve := (320748361791/1000000000000) }

theorem quarter_002_026_valid : quarter_002_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_026]
  · intro i; fin_cases i <;> norm_num [quarter_002_026]
  · norm_num [quarter_002_026]
  · norm_num [quarter_002_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_026]

def quarter_002_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(27301419/100000000), (27301419/100000000), (6623203/100000000), (6623203/100000000), (2424669/100000000), (2424669/100000000), (27301419/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7391657/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1495141/25000000), (1/100000000), (1782171/100000000), (1/100000000), (1854421/25000000)]
    alternative := .zero
    polynomial := [(-227943986560995122811589422103/4941284505587791731000000000000), (182196811437651/119611280000000), (-2705540475189972696993877050853/2470642252793895865500000000000), (182196811437651/119611280000000), (-5183136963818950271176164679603/4941284505587791731000000000000)]
    bernstein := [(17043282537818018455148563886761757/49412845055877917310000000000000000), (69611271955807096844806580388785597/197651380223511669240000000000000000), (852521170910941851366019737506667911/2371816562682140030880000000000000000), (1159516979692953954628991763784332877/3162422083576186707840000000000000000), (4728994313805364279153417668689376317/12649688334304746831360000000000000000)]
    reserve := (344916033847/1000000000000) }

theorem quarter_002_027_valid : quarter_002_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_027]
  · intro i; fin_cases i <;> norm_num [quarter_002_027]
  · norm_num [quarter_002_027]
  · norm_num [quarter_002_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_027]

def quarter_002_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (27123987/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1414771/20000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-2045176436384187949203/14839533019000000000000), (1375723219576101/707385500000000), (-11938198350120634489203/7419766509500000000000), (1375723219576101/707385500000000), (-21831220263857081029203/14839533019000000000000)]
    bernstein := [(14232313946797236569150910717/37989204528640000000000000000), (7272057390209834234183394663/18994602264320000000000000000), (3713340669584878429664192757/9497301132160000000000000000), (1895007804238793106554407023/4748650566080000000000000000), (966512313079091909064725997/2374325283040000000000000000)]
    reserve := (187320504909/500000000000) }

theorem quarter_002_028_valid : quarter_002_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_028]
  · intro i; fin_cases i <;> norm_num [quarter_002_028]
  · norm_num [quarter_002_028]
  · norm_num [quarter_002_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_028]

def quarter_002_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (28042893/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1708703/25000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-2961433653682250127093/17922585767000000000000), (1390417219429161/683481200000000), (-14909824045531678347093/8961292883500000000000), (1390417219429161/683481200000000), (-26858214437381106567093/17922585767000000000000)]
    bernstein := [(1169108088585052769503834107/2867613722720000000000000000), (477394998356574226371066483/1147045489088000000000000000), (194828631953279649344286731/458818195635200000000000000), (79467631150836293708282691/183527278254080000000000000), (32396632704552157804661403/73410911301632000000000000)]
    reserve := (203846856939/500000000000) }

theorem quarter_002_029_valid : quarter_002_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_002_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_002_029]
  · intro i; fin_cases i <;> norm_num [quarter_002_029]
  · norm_num [quarter_002_029]
  · norm_num [quarter_002_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_002_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_002_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_002_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_002_029]

def quarterTable002 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 0, 0, 0, 2]
  rows := [quarter_002_000, quarter_002_001, quarter_002_002, quarter_002_003, quarter_002_004, quarter_002_005, quarter_002_006, quarter_002_007, quarter_002_008, quarter_002_009, quarter_002_010, quarter_002_011, quarter_002_012, quarter_002_013, quarter_002_014, quarter_002_015, quarter_002_016, quarter_002_017, quarter_002_018, quarter_002_019, quarter_002_020, quarter_002_021, quarter_002_022, quarter_002_023, quarter_002_024, quarter_002_025, quarter_002_026, quarter_002_027, quarter_002_028, quarter_002_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_002_000_valid
    · exact quarter_002_001_valid
    · exact quarter_002_002_valid
    · exact quarter_002_003_valid
    · exact quarter_002_004_valid
    · exact quarter_002_005_valid
    · exact quarter_002_006_valid
    · exact quarter_002_007_valid
    · exact quarter_002_008_valid
    · exact quarter_002_009_valid
    · exact quarter_002_010_valid
    · exact quarter_002_011_valid
    · exact quarter_002_012_valid
    · exact quarter_002_013_valid
    · exact quarter_002_014_valid
    · exact quarter_002_015_valid
    · exact quarter_002_016_valid
    · exact quarter_002_017_valid
    · exact quarter_002_018_valid
    · exact quarter_002_019_valid
    · exact quarter_002_020_valid
    · exact quarter_002_021_valid
    · exact quarter_002_022_valid
    · exact quarter_002_023_valid
    · exact quarter_002_024_valid
    · exact quarter_002_025_valid
    · exact quarter_002_026_valid
    · exact quarter_002_027_valid
    · exact quarter_002_028_valid
    · exact quarter_002_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
