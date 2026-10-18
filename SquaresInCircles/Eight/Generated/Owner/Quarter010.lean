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

def quarter_010_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_010_000_valid : quarter_010_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_000]
  · intro i; fin_cases i <;> norm_num [quarter_010_000]
  · norm_num [quarter_010_000]
  · norm_num [quarter_010_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_000]

def quarter_010_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_010_001_valid : quarter_010_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_001]
  · intro i; fin_cases i <;> norm_num [quarter_010_001]
  · norm_num [quarter_010_001]
  · norm_num [quarter_010_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_001]

def quarter_010_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3267003/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (912737/12500000)]
    alternative := .zero
    polynomial := [(-2169191422463283237963/19147396786000000000000), (-1680685461741/903700000000), (-14934122485480637997963/9573698393000000000000), (-1680685461741/903700000000), (-27699053548497992757963/19147396786000000000000)]
    bernstein := [(18336304958251293684958548357/49017335772160000000000000000), (4489371739241140037519205867/12254333943040000000000000000), (1098455096793363008082180577/3063583485760000000000000000), (38369849824100541136894641/109413695920000000000000000), (9375388818738124642177371/27353423980000000000000000)]
    reserve := (8568752513/25000000000) }

theorem quarter_010_002_valid : quarter_010_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_002]
  · intro i; fin_cases i <;> norm_num [quarter_010_002]
  · norm_num [quarter_010_002]
  · norm_num [quarter_010_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_002]

def quarter_010_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (12539659/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (1879413/25000000)]
    alternative := .zero
    polynomial := [(-900823623365753756879/9856581478500000000000), (-222859008882521/125294200000000), (-7471877876655210566879/4928290739250000000000), (-222859008882521/125294200000000), (-14042932129944667376879/9856581478500000000000)]
    bernstein := [(33733764821576472263025601/98565814785000000000000000), (131989447673509091897660587/394263259140000000000000000), (1548188615022030467277299107/4731159109680000000000000000), (2016220219734266352555338603/6308212146240000000000000000), (7870928602205907369811025761/25232848584960000000000000000)]
    reserve := (311931828691/1000000000000) }

theorem quarter_010_003_valid : quarter_010_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_003]
  · intro i; fin_cases i <;> norm_num [quarter_010_003]
  · norm_num [quarter_010_003]
  · norm_num [quarter_010_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_003]

def quarter_010_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (23954683/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (3859927/50000000)]
    alternative := .zero
    polynomial := [(-2911757496123219851943/40486774303000000000000), (-1313146353535203/771985400000000), (-29902940094878057831943/20243387151500000000000), (-1313146353535203/771985400000000), (-56894122693632895811943/40486774303000000000000)]
    bernstein := [(32284069972296337902630332937/103646142215680000000000000000), (3153420973043746955499217587/10364614221568000000000000000), (307766680163278571481441041/1036461422156800000000000000), (1765375410924236418042747/6096831895040000000000000), (171989599413010471896969/609683189504000000000000)]
    reserve := (141048336557/500000000000) }

theorem quarter_010_004_valid : quarter_010_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_004]
  · intro i; fin_cases i <;> norm_num [quarter_010_004]
  · norm_num [quarter_010_004]
  · norm_num [quarter_010_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_004]

def quarter_010_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (355679/1562500), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (7907263/100000000)]
    alternative := .zero
    polynomial := [(-907114696706034174759/16587856321400000000000), (-642966360237003/395363150000000), (-11965685467053658698759/8293928160700000000000), (-642966360237003/395363150000000), (-23024256237401283222759/16587856321400000000000)]
    bernstein := [(70367095055716961453097/249793601075200000000000), (686137161622951353525729/2497936010752000000000000), (113629684704909812327936153/424649121827840000000000000), (157975382968151158449267207/606641602611200000000000000), (118134002360098990774428411/466647386624000000000000000)]
    reserve := (126577374851/500000000000) }

theorem quarter_010_005_valid : quarter_010_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_005]
  · intro i; fin_cases i <;> norm_num [quarter_010_005]
  · norm_num [quarter_010_005]
  · norm_num [quarter_010_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_005]

def quarter_010_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (860301/4000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (8078689/100000000)]
    alternative := .zero
    polynomial := [(-197092352289628577433/4984551113000000000000), (-1255496754111699/807868900000000), (-3520126394392621157433/2492275556500000000000), (-1255496754111699/807868900000000), (-6843160436495613737433/4984551113000000000000)]
    bernstein := [(3225949326069650397436388487/12760450849280000000000000000), (392357672769641300620139043/1595056356160000000000000000), (11916937875783963500254713/49845511130000000000000000), (2892146086420452069769539/12461377782500000000000000), (175250436533962308848823/778836111406250000000000)]
    reserve := (1406348797/6250000000) }

theorem quarter_010_006_valid : quarter_010_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_006]
  · intro i; fin_cases i <;> norm_num [quarter_010_006]
  · norm_num [quarter_010_006]
  · norm_num [quarter_010_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_006]

def quarter_010_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1261833/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (8233003/100000000)]
    alternative := .zero
    polynomial := [(-18207877560843676587/690847747736000000000), (-610922227224111/411650150000000), (-478773038112525358347/345423873868000000000), (-610922227224111/411650150000000), (-939338198664207040107/690847747736000000000)]
    bernstein := [(24256930460084798244717/107944960583750000000000), (376622922361305081633663/1727119369340000000000000), (1459948347390081789178733/6908477477360000000000000), (2659393558265338863882147/13004192898560000000000000), (20555908005932725264491429/104033543188480000000000000)]
    reserve := (19758923301/100000000000) }

theorem quarter_010_007_valid : quarter_010_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_007]
  · intro i; fin_cases i <;> norm_num [quarter_010_007]
  · norm_num [quarter_010_007]
  · norm_num [quarter_010_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_007]

def quarter_010_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (18811861/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (8369161/100000000)]
    alternative := .zero
    polynomial := [(-1318866165176644236017/87784129729000000000000), (-1185006088149939/836916100000000), (-59841618732615779376017/43892064864500000000000), (-1185006088149939/836916100000000), (-118364371300054914516017/87784129729000000000000)]
    bernstein := [(2608586152372463088319132799/13219257182720000000000000000), (1261333853173377799977704171/6609628591360000000000000000), (31053317536256575038614649109/168545529079680000000000000000), (4987845913673359621442817587/28090921513280000000000000000), (2398740626523194738617560223/14045460756640000000000000000)]
    reserve := (5337001461/31250000000) }

theorem quarter_010_008_valid : quarter_010_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_008]
  · intro i; fin_cases i <;> norm_num [quarter_010_008]
  · norm_num [quarter_010_008]
  · norm_num [quarter_010_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_008]

def quarter_010_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(15625233/50000000), (15625233/50000000), (1288859/100000000), (6458/390625), (6458/390625), (6458/390625), (15625233/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8362249/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7997981/100000000), (66211/12500000), (1/100000000), (1/100000000), (4193803/50000000)]
    alternative := .zero
    polynomial := [(56920902497040318368508484071/4441692991682431546000000000000), (-1004388424888554805437/838548917793575000000), (-2582382102063921187743310795929/2220846495841215773000000000000), (-1004388424888554805437/838548917793575000000), (-5221685106624882693855130075929/4441692991682431546000000000000)]
    bernstein := [(120647103290010910772787025366920951/710670878669189047360000000000000000), (46635116762145364908789543129081357/284268351467675618944000000000000000), (17995288522083848758428012704024111/113707340587070247577600000000000000), (1386163461335139938602108752802449/9096587246965619806208000000000000), (106553856066775528071217713999999/727726979757249584496640000000000)]
    reserve := (146420098513/1000000000000) }

theorem quarter_010_009_valid : quarter_010_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_009]
  · intro i; fin_cases i <;> norm_num [quarter_010_009]
  · norm_num [quarter_010_009]
  · norm_num [quarter_010_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_009]

def quarter_010_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(13292231/50000000), (13292231/50000000), (774097/20000000), (545871/10000000), (545871/10000000), (545871/10000000), (13292231/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (564057/4000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7022369/100000000), (845423/50000000), (1/100000000), (1/100000000), (2067697/25000000)]
    alternative := .zero
    polynomial := [(161117258424794045464548948503/3068913244009747159750000000000), (-2434797759296796938659/2904026262838600000000), (-1201359544263608093370584097747/1534456622004873579875000000000), (-2434797759296796938659/2904026262838600000000), (-2563836346952010232205717143997/3068913244009747159750000000000)]
    bernstein := [(73663221977317877476635682138507/502810745898556974653440000000000), (3493189802726502593662827663053/24551305952077977278000000000000), (2710515284009198366985729262404937/19641044761662381822400000000000000), (1640829784914994408422930814856209/12275652976038988639000000000000000), (3967109796946461473057450491549103/30689132440097471597500000000000000)]
    reserve := (129267577201/1000000000000) }

theorem quarter_010_010_valid : quarter_010_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_010]
  · intro i; fin_cases i <;> norm_num [quarter_010_010]
  · norm_num [quarter_010_010]
  · norm_num [quarter_010_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_010]

def quarter_010_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(11485839/50000000), (11485839/50000000), (2789263/50000000), (4251073/50000000), (4251073/50000000), (4251073/50000000), (11485839/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2423573/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3119267/50000000), (2569477/100000000), (1/100000000), (1/100000000), (8187889/100000000)]
    alternative := .zero
    polynomial := [(2451874838550187796121805652763/32812493599784604575500000000000), (-379268746741977430143/638505298934075000000), (-8709846875390547271756001397237/16406246799892302287750000000000), (-379268746741977430143/638505298934075000000), (-19871568589331282339633808447237/32812493599784604575500000000000)]
    bernstein := [(42442258337595623238212435701935363/328124935997846045755000000000000000), (165641099650413348864816518919262389/1312499743991384183020000000000000000), (645839916236165036509862167455878167/5249998975965536732080000000000000000), (2515581890672770294338025042817703801/20999995903862146928320000000000000000), (9787561796605229633589938279146228203/83999983615448587713280000000000000000)]
    reserve := (14564826943/125000000000) }

theorem quarter_010_011_valid : quarter_010_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_011]
  · intro i; fin_cases i <;> norm_num [quarter_010_011]
  · norm_num [quarter_010_011]
  · norm_num [quarter_010_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_011]

def quarter_010_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(4035093/20000000), (4035093/20000000), (336139/5000000), (10916941/100000000), (10916941/100000000), (10916941/100000000), (4035093/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5295519/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2804373/50000000), (101237/3125000), (1/100000000), (1/100000000), (4062733/50000000)]
    alternative := .zero
    polynomial := [(31973297943928670466180363919/369099370275728938560000000000), (-6451042494326823917/15191224975212000000), (-66936448365744254190177392081/184549685137864469280000000000), (-6451042494326823917/15191224975212000000), (-165846194675417178846535148081/369099370275728938560000000000)]
    bernstein := [(110173838332579005491025890990512639/944894387905866082713600000000000000), (53974723995395390380142483121149813/472447193952933041356800000000000000), (79272952504832740432991907604683013/708670790929399562035200000000000000), (12927029314508506949807529687273757/118111798488233260339200000000000000), (6319069113124983816427551037427119/59055899244116630169600000000000000)]
    reserve := (53500744159/500000000000) }

theorem quarter_010_012_valid : quarter_010_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_012]
  · intro i; fin_cases i <;> norm_num [quarter_010_012]
  · norm_num [quarter_010_012]
  · norm_num [quarter_010_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_012]

def quarter_010_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(3599843/20000000), (3599843/20000000), (7504613/100000000), (12832581/100000000), (12832581/100000000), (12832581/100000000), (3599843/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1877341/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1274781/25000000), (3756311/100000000), (1/100000000), (1/100000000), (1009361/12500000)]
    alternative := .zero
    polynomial := [(68748811165972672809109345427/743584430308054254000000000000), (-2506022557440115649/8234971039622400000), (-92581410749344830212863598323/371792215154027127000000000000), (-2506022557440115649/8234971039622400000), (-253911632664662333234836542073/743584430308054254000000000000)]
    bernstein := [(12740285669209513920885674571869527/118973508849288680640000000000000000), (8353965415689240569426818135182609/79315672566192453760000000000000000), (147828321144787367614931554333309181/1427682106191464167680000000000000000), (32278431723929916581901037610618409/317262690264769815040000000000000000), (63397215834400421438214326993148109/634525380529539630080000000000000000)]
    reserve := (99912813229/1000000000000) }

theorem quarter_010_013_valid : quarter_010_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_013]
  · intro i; fin_cases i <;> norm_num [quarter_010_013]
  · norm_num [quarter_010_013]
  · norm_num [quarter_010_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_013]

def quarter_010_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(8146479/50000000), (8146479/50000000), (2013157/25000000), (7178083/50000000), (7178083/50000000), (7178083/50000000), (8146479/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8410087/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (936509/20000000), (4159211/100000000), (1/100000000), (1/100000000), (8030687/100000000)]
    alternative := .zero
    polynomial := [(15113267868222966245877621729/159595093833658684250000000000), (-58096710829275587073/268600380417250000000), (-1950023069081302891508724753/11399649559547048875000000000), (-58096710829275587073/268600380417250000000), (-42413590835361206726999768271/159595093833658684250000000000)]
    bernstein := [(40856871397859122027473346473164529/408563440214166231680000000000000000), (100813516333744376179490558393241/1021408600535415579200000000000000), (3552438353514307555421312426949/36478878590550556400000000000000), (61316058896980944068458627641/638380375334634737000000000000), (15113267868222966245877621729/159595093833658684250000000000)]
    reserve := (23674392967/250000000000) }

theorem quarter_010_014_valid : quarter_010_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_014]
  · intro i; fin_cases i <;> norm_num [quarter_010_014]
  · norm_num [quarter_010_014]
  · norm_num [quarter_010_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_014]

def quarter_010_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(635139/4000000), (635139/4000000), (336419/4000000), (7325683/50000000), (7325683/50000000), (7325683/50000000), (635139/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7574809/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2270123/50000000), (533589/12500000), (1/100000000), (1/100000000), (7993989/100000000)]
    alternative := .zero
    polynomial := [(612391674279252033858408567743/6455480060778694722000000000000), (7440378266380543279/16130967369464000000), (-498333863171652420467463932257/3227740030389347361000000000000), (7440378266380543279/16130967369464000000), (-1609059400622556874793336432257/6455480060778694722000000000000)]
    bernstein := [(612391674279252033858408567743/6455480060778694722000000000000), (1262003073547064014976488988611/12910960121557389444000000000000), (3117636382622325856946318556234143/30986304291737734665600000000000000), (2137348589637339510299657055766211/20657536194491823110400000000000000), (1756810503794725618175906093432425343/16526028955593458488320000000000000000)]
    reserve := (94863847229/1000000000000) }

theorem quarter_010_015_valid : quarter_010_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_015]
  · intro i; fin_cases i <;> norm_num [quarter_010_015]
  · norm_num [quarter_010_015]
  · norm_num [quarter_010_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_015]

def quarter_010_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(8206797/50000000), (8206797/50000000), (8701339/100000000), (14019293/100000000), (14019293/100000000), (14019293/100000000), (8206797/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1341271/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2298021/50000000), (16677/400000), (1/100000000), (1/100000000), (1590721/20000000)]
    alternative := .zero
    polynomial := [(86791905413346814906597313/923680979672764500000000000), (5545533147508637909/11077303827700000000), (-82810795778752250353933687/461840489836382250000000000), (5545533147508637909/11077303827700000000), (-252413496970851315614464687/923680979672764500000000000)]
    bernstein := [(251535041485759565830008357616913/2364623307962277120000000000000000), (14378599596196770331331063789057/131367961553459840000000000000000), (199544530568781470651384799243539/1773467480971707840000000000000000), (3795460517994137913473262710657/32841990388364960000000000000000), (17528766353685680065233367965713/147788956747642320000000000000000)]
    reserve := (106374254469/1000000000000) }

theorem quarter_010_016_valid : quarter_010_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_016]
  · intro i; fin_cases i <;> norm_num [quarter_010_016]
  · norm_num [quarter_010_016]
  · norm_num [quarter_010_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_016]

def quarter_010_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(16875949/100000000), (16875949/100000000), (4498451/50000000), (13458417/100000000), (13458417/100000000), (13458417/100000000), (16875949/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1446593/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2313959/50000000), (818111/20000000), (1/100000000), (1/100000000), (790087/10000000)]
    alternative := .zero
    polynomial := [(17205864528716604400486114873/186961774199600757875000000000), (495451092948890921809/914114462216500000000), (-38049315342980004136074190629/186961774199600757875000000000), (495451092948890921809/914114462216500000000), (-27627589935848304268280152751/93480887099800378937500000000)]
    bernstein := [(1775178995715065379091819077558949/14956941935968060630000000000000000), (12495270310997751767595995927741/102444807780603155000000000000000), (7492970469770123420702207950357391/59827767743872242520000000000000000), (105315433703824624717809896324713/819558462244825240000000000000000), (31530049518516210176192580526403369/239311070975488970080000000000000000)]
    reserve := (14835744861/125000000000) }

theorem quarter_010_017_valid : quarter_010_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_017]
  · intro i; fin_cases i <;> norm_num [quarter_010_017]
  · norm_num [quarter_010_017]
  · norm_num [quarter_010_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_017]

def quarter_010_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(4318993/25000000), (4318993/25000000), (2324763/25000000), (6478839/50000000), (6478839/50000000), (6478839/50000000), (4318993/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4826769/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (463863/10000000), (4030019/100000000), (1/100000000), (1/100000000), (7835241/100000000)]
    alternative := .zero
    polynomial := [(217211572716341405572015139887/2441169498483502279500000000000), (29551578488159602497/50478866610875000000), (-277533201227796911659118880113/1220584749241751139750000000000), (29551578488159602497/50478866610875000000), (-772277975171935228890252900113/2441169498483502279500000000000)]
    bernstein := [(823940812303687983638055405011836447/6249393916117765835520000000000000000), (211459900324363096084512296182577749/1562348479029441458880000000000000000), (162687969252473546916636264899172049/1171761359272081094160000000000000000), (13897523294183070912830825958470561/97646779939340091180000000000000000), (3559249093124449352075169579107287/24411694984835022795000000000000000)]
    reserve := (26368663053/200000000000) }

theorem quarter_010_018_valid : quarter_010_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_018]
  · intro i; fin_cases i <;> norm_num [quarter_010_018]
  · norm_num [quarter_010_018]
  · norm_num [quarter_010_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_018]

def quarter_010_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(17623061/100000000), (17623061/100000000), (4804459/50000000), (125073/1000000), (125073/1000000), (125073/1000000), (17623061/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1919003/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (463059/10000000), (996333/25000000), (1/100000000), (1/100000000), (7756507/100000000)]
    alternative := .zero
    polynomial := [(101060172201222437246311126061/1192849845432731343000000000000), (1133108323196620715453/1795860187456500000000), (-149886875978033509013858833939/596424922716365671500000000000), (1133108323196620715453/1795860187456500000000), (-400833924157289455274028793939/1192849845432731343000000000000)]
    bernstein := [(580128448103089748037761418896087/3976166151442437810000000000000000), (158665677576723779574396220562449/1060310973717983416000000000000000), (3512621343951849503628638410204907/22902717032308441785600000000000000), (1640074032410561184006496711949/10439984971992452096000000000000), (2417620181984678593473372760393/15033578359669131018240000000000)]
    reserve := (145901460353/1000000000000) }

theorem quarter_010_019_valid : quarter_010_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_019]
  · intro i; fin_cases i <;> norm_num [quarter_010_019]
  · norm_num [quarter_010_019]
  · norm_num [quarter_010_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_019]

def quarter_010_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(4481379/25000000), (4481379/25000000), (4963539/50000000), (12098791/100000000), (12098791/100000000), (12098791/100000000), (4481379/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1414603/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1151473/25000000), (988621/25000000), (1/100000000), (1/100000000), (191717/2500000)]
    alternative := .zero
    polynomial := [(6910225979741977667693065191/87297982326689824400000000000), (74916776161920280329/110378474570500000000), (-12042679781413878324253475409/43648991163344912200000000000), (74916776161920280329/110378474570500000000), (-30995585542569734316200016009/87297982326689824400000000000)]
    bernstein := [(2301703002100187631282034187919/14302901424404860829696000000000), (29485084093436278619320526337249/178786267805060760371200000000000), (377473283174398910675454223743231/2234828347563259504640000000000000), (965936663655166876515254240872797/5587070868908148761600000000000000), (2470448521497985789078417224606471/13967677172270371904000000000000000)]
    reserve := (160925600603/1000000000000) }

theorem quarter_010_020_valid : quarter_010_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_020]
  · intro i; fin_cases i <;> norm_num [quarter_010_020]
  · norm_num [quarter_010_020]
  · norm_num [quarter_010_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_020]

def quarter_010_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(6306253/25000000), (6306253/25000000), (2193/40000), (6280821/100000000), (6280821/100000000), (6280821/100000000), (6306253/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8753383/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3166683/50000000), (131663/6250000), (1/100000000), (1/100000000), (316191/4000000)]
    alternative := .zero
    polynomial := [(1602801200627251535255070863/58591595320833484000000000000), (33930939310319/31666830000000), (-22084976022805951044901239537/29295797660416742000000000000), (33930939310319/31666830000000), (-45772753246239153625057549937/58591595320833484000000000000)]
    bernstein := [(1634368785431036400706327799868703/9374655251333357440000000000000000), (10125110016314913056289324561334121/56247931508000144640000000000000000), (20883595054339373030365035305248949/112495863016000289280000000000000000), (43025630737322760379829143392383681/224991726032000578560000000000000000), (88552446097564862159766076209438989/449983452064001157120000000000000000)]
    reserve := (3486781629/20000000000) }

theorem quarter_010_021_valid : quarter_010_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_021]
  · intro i; fin_cases i <;> norm_num [quarter_010_021]
  · norm_num [quarter_010_021]
  · norm_num [quarter_010_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_021]

def quarter_010_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1261833/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8233003/100000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-18207877560843676587/690847747736000000000), (610922227224111/411650150000000), (-478773038112525358347/345423873868000000000), (610922227224111/411650150000000), (-939338198664207040107/690847747736000000000)]
    bernstein := [(20555908005932725264491429/104033543188480000000000000), (2659393558265338863882147/13004192898560000000000000), (1459948347390081789178733/6908477477360000000000000), (376622922361305081633663/1727119369340000000000000), (24256930460084798244717/107944960583750000000000)]
    reserve := (19758923301/100000000000) }

theorem quarter_010_022_valid : quarter_010_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_022]
  · intro i; fin_cases i <;> norm_num [quarter_010_022]
  · norm_num [quarter_010_022]
  · norm_num [quarter_010_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_022]

def quarter_010_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (860301/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8078689/100000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-197092352289628577433/4984551113000000000000), (1255496754111699/807868900000000), (-3520126394392621157433/2492275556500000000000), (1255496754111699/807868900000000), (-6843160436495613737433/4984551113000000000000)]
    bernstein := [(175250436533962308848823/778836111406250000000000), (2892146086420452069769539/12461377782500000000000000), (11916937875783963500254713/49845511130000000000000000), (392357672769641300620139043/1595056356160000000000000000), (3225949326069650397436388487/12760450849280000000000000000)]
    reserve := (1406348797/6250000000) }

theorem quarter_010_023_valid : quarter_010_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_023]
  · intro i; fin_cases i <;> norm_num [quarter_010_023]
  · norm_num [quarter_010_023]
  · norm_num [quarter_010_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_023]

def quarter_010_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (355679/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7907263/100000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-907114696706034174759/16587856321400000000000), (642966360237003/395363150000000), (-11965685467053658698759/8293928160700000000000), (642966360237003/395363150000000), (-23024256237401283222759/16587856321400000000000)]
    bernstein := [(118134002360098990774428411/466647386624000000000000000), (157975382968151158449267207/606641602611200000000000000), (113629684704909812327936153/424649121827840000000000000), (686137161622951353525729/2497936010752000000000000), (70367095055716961453097/249793601075200000000000)]
    reserve := (126577374851/500000000000) }

theorem quarter_010_024_valid : quarter_010_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_024]
  · intro i; fin_cases i <;> norm_num [quarter_010_024]
  · norm_num [quarter_010_024]
  · norm_num [quarter_010_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_024]

def quarter_010_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (23954683/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3859927/50000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-2911757496123219851943/40486774303000000000000), (1313146353535203/771985400000000), (-29902940094878057831943/20243387151500000000000), (1313146353535203/771985400000000), (-56894122693632895811943/40486774303000000000000)]
    bernstein := [(171989599413010471896969/609683189504000000000000), (1765375410924236418042747/6096831895040000000000000), (307766680163278571481441041/1036461422156800000000000000), (3153420973043746955499217587/10364614221568000000000000000), (32284069972296337902630332937/103646142215680000000000000000)]
    reserve := (141048336557/500000000000) }

theorem quarter_010_025_valid : quarter_010_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_025]
  · intro i; fin_cases i <;> norm_num [quarter_010_025]
  · norm_num [quarter_010_025]
  · norm_num [quarter_010_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_025]

def quarter_010_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (12539659/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1879413/25000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-900823623365753756879/9856581478500000000000), (222859008882521/125294200000000), (-7471877876655210566879/4928290739250000000000), (222859008882521/125294200000000), (-14042932129944667376879/9856581478500000000000)]
    bernstein := [(7870928602205907369811025761/25232848584960000000000000000), (2016220219734266352555338603/6308212146240000000000000000), (1548188615022030467277299107/4731159109680000000000000000), (131989447673509091897660587/394263259140000000000000000), (33733764821576472263025601/98565814785000000000000000)]
    reserve := (311931828691/1000000000000) }

theorem quarter_010_026_valid : quarter_010_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_026]
  · intro i; fin_cases i <;> norm_num [quarter_010_026]
  · norm_num [quarter_010_026]
  · norm_num [quarter_010_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_026]

def quarter_010_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3267003/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (912737/12500000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-2169191422463283237963/19147396786000000000000), (1680685461741/903700000000), (-14934122485480637997963/9573698393000000000000), (1680685461741/903700000000), (-27699053548497992757963/19147396786000000000000)]
    bernstein := [(9375388818738124642177371/27353423980000000000000000), (38369849824100541136894641/109413695920000000000000000), (1098455096793363008082180577/3063583485760000000000000000), (4489371739241140037519205867/12254333943040000000000000000), (18336304958251293684958548357/49017335772160000000000000000)]
    reserve := (8568752513/25000000000) }

theorem quarter_010_027_valid : quarter_010_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_027]
  · intro i; fin_cases i <;> norm_num [quarter_010_027]
  · norm_num [quarter_010_027]
  · norm_num [quarter_010_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_027]

def quarter_010_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (27123987/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1414771/20000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-2045176436384187949203/14839533019000000000000), (1375723219576101/707385500000000), (-11938198350120634489203/7419766509500000000000), (1375723219576101/707385500000000), (-21831220263857081029203/14839533019000000000000)]
    bernstein := [(14232313946797236569150910717/37989204528640000000000000000), (7272057390209834234183394663/18994602264320000000000000000), (3713340669584878429664192757/9497301132160000000000000000), (1895007804238793106554407023/4748650566080000000000000000), (966512313079091909064725997/2374325283040000000000000000)]
    reserve := (187320504909/500000000000) }

theorem quarter_010_028_valid : quarter_010_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_028]
  · intro i; fin_cases i <;> norm_num [quarter_010_028]
  · norm_num [quarter_010_028]
  · norm_num [quarter_010_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_028]

def quarter_010_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 0, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (28042893/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1708703/25000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-2961433653682250127093/17922585767000000000000), (1390417219429161/683481200000000), (-14909824045531678347093/8961292883500000000000), (1390417219429161/683481200000000), (-26858214437381106567093/17922585767000000000000)]
    bernstein := [(1169108088585052769503834107/2867613722720000000000000000), (477394998356574226371066483/1147045489088000000000000000), (194828631953279649344286731/458818195635200000000000000), (79467631150836293708282691/183527278254080000000000000), (32396632704552157804661403/73410911301632000000000000)]
    reserve := (203846856939/500000000000) }

theorem quarter_010_029_valid : quarter_010_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_010_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_010_029]
  · intro i; fin_cases i <;> norm_num [quarter_010_029]
  · norm_num [quarter_010_029]
  · norm_num [quarter_010_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_010_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_010_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_010_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_010_029]

def quarterTable010 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 2, 0, 0, 2]
  rows := [quarter_010_000, quarter_010_001, quarter_010_002, quarter_010_003, quarter_010_004, quarter_010_005, quarter_010_006, quarter_010_007, quarter_010_008, quarter_010_009, quarter_010_010, quarter_010_011, quarter_010_012, quarter_010_013, quarter_010_014, quarter_010_015, quarter_010_016, quarter_010_017, quarter_010_018, quarter_010_019, quarter_010_020, quarter_010_021, quarter_010_022, quarter_010_023, quarter_010_024, quarter_010_025, quarter_010_026, quarter_010_027, quarter_010_028, quarter_010_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_010_000_valid
    · exact quarter_010_001_valid
    · exact quarter_010_002_valid
    · exact quarter_010_003_valid
    · exact quarter_010_004_valid
    · exact quarter_010_005_valid
    · exact quarter_010_006_valid
    · exact quarter_010_007_valid
    · exact quarter_010_008_valid
    · exact quarter_010_009_valid
    · exact quarter_010_010_valid
    · exact quarter_010_011_valid
    · exact quarter_010_012_valid
    · exact quarter_010_013_valid
    · exact quarter_010_014_valid
    · exact quarter_010_015_valid
    · exact quarter_010_016_valid
    · exact quarter_010_017_valid
    · exact quarter_010_018_valid
    · exact quarter_010_019_valid
    · exact quarter_010_020_valid
    · exact quarter_010_021_valid
    · exact quarter_010_022_valid
    · exact quarter_010_023_valid
    · exact quarter_010_024_valid
    · exact quarter_010_025_valid
    · exact quarter_010_026_valid
    · exact quarter_010_027_valid
    · exact quarter_010_028_valid
    · exact quarter_010_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
