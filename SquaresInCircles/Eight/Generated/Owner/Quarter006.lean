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

def quarter_006_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_006_000_valid : quarter_006_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_000]
  · intro i; fin_cases i <;> norm_num [quarter_006_000]
  · norm_num [quarter_006_000]
  · norm_num [quarter_006_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_000]

def quarter_006_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, (100000001/100000000)]
    cone := fun i => (![![(1/2), 0, (100000001/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-13428912323878349907/21221563000000000000), (-203429902034299/53053907500000), (-34650475536093979907/10610781500000000000), (-203429902034299/53053907500000), (-55872038748309609907/21221563000000000000)]
    bernstein := [(1473968078880302685138893/3395450080000000000000000), (2841569285726815604215487/6790900160000000000000000), (16406229214018597040299999/40745400960000000000000000), (10505355874824997880394647/27163600640000000000000000), (20139685295585714783820573/54327201280000000000000000)]
    reserve := (74142178581/200000000000) }

theorem quarter_006_001_valid : quarter_006_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_001]
  · intro i; fin_cases i <;> norm_num [quarter_006_001]
  · norm_num [quarter_006_001]
  · norm_num [quarter_006_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_001]

def quarter_006_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3267003/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (912737/12500000)]
    alternative := .zero
    polynomial := [(-2169191422463283237963/19147396786000000000000), (-1680685461741/903700000000), (-14934122485480637997963/9573698393000000000000), (-1680685461741/903700000000), (-27699053548497992757963/19147396786000000000000)]
    bernstein := [(18336304958251293684958548357/49017335772160000000000000000), (4489371739241140037519205867/12254333943040000000000000000), (1098455096793363008082180577/3063583485760000000000000000), (38369849824100541136894641/109413695920000000000000000), (9375388818738124642177371/27353423980000000000000000)]
    reserve := (8568752513/25000000000) }

theorem quarter_006_002_valid : quarter_006_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_002]
  · intro i; fin_cases i <;> norm_num [quarter_006_002]
  · norm_num [quarter_006_002]
  · norm_num [quarter_006_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_002]

def quarter_006_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (12539659/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (1879413/25000000)]
    alternative := .zero
    polynomial := [(-900823623365753756879/9856581478500000000000), (-222859008882521/125294200000000), (-7471877876655210566879/4928290739250000000000), (-222859008882521/125294200000000), (-14042932129944667376879/9856581478500000000000)]
    bernstein := [(33733764821576472263025601/98565814785000000000000000), (131989447673509091897660587/394263259140000000000000000), (1548188615022030467277299107/4731159109680000000000000000), (2016220219734266352555338603/6308212146240000000000000000), (7870928602205907369811025761/25232848584960000000000000000)]
    reserve := (311931828691/1000000000000) }

theorem quarter_006_003_valid : quarter_006_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_003]
  · intro i; fin_cases i <;> norm_num [quarter_006_003]
  · norm_num [quarter_006_003]
  · norm_num [quarter_006_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_003]

def quarter_006_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (23954683/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (3859927/50000000)]
    alternative := .zero
    polynomial := [(-2911757496123219851943/40486774303000000000000), (-1313146353535203/771985400000000), (-29902940094878057831943/20243387151500000000000), (-1313146353535203/771985400000000), (-56894122693632895811943/40486774303000000000000)]
    bernstein := [(32284069972296337902630332937/103646142215680000000000000000), (3153420973043746955499217587/10364614221568000000000000000), (307766680163278571481441041/1036461422156800000000000000), (1765375410924236418042747/6096831895040000000000000), (171989599413010471896969/609683189504000000000000)]
    reserve := (141048336557/500000000000) }

theorem quarter_006_004_valid : quarter_006_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_004]
  · intro i; fin_cases i <;> norm_num [quarter_006_004]
  · norm_num [quarter_006_004]
  · norm_num [quarter_006_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_004]

def quarter_006_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (355679/1562500), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (7907263/100000000)]
    alternative := .zero
    polynomial := [(-907114696706034174759/16587856321400000000000), (-642966360237003/395363150000000), (-11965685467053658698759/8293928160700000000000), (-642966360237003/395363150000000), (-23024256237401283222759/16587856321400000000000)]
    bernstein := [(70367095055716961453097/249793601075200000000000), (686137161622951353525729/2497936010752000000000000), (113629684704909812327936153/424649121827840000000000000), (157975382968151158449267207/606641602611200000000000000), (118134002360098990774428411/466647386624000000000000000)]
    reserve := (126577374851/500000000000) }

theorem quarter_006_005_valid : quarter_006_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_005]
  · intro i; fin_cases i <;> norm_num [quarter_006_005]
  · norm_num [quarter_006_005]
  · norm_num [quarter_006_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_005]

def quarter_006_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (860301/4000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (8078689/100000000)]
    alternative := .zero
    polynomial := [(-197092352289628577433/4984551113000000000000), (-1255496754111699/807868900000000), (-3520126394392621157433/2492275556500000000000), (-1255496754111699/807868900000000), (-6843160436495613737433/4984551113000000000000)]
    bernstein := [(3225949326069650397436388487/12760450849280000000000000000), (392357672769641300620139043/1595056356160000000000000000), (11916937875783963500254713/49845511130000000000000000), (2892146086420452069769539/12461377782500000000000000), (175250436533962308848823/778836111406250000000000)]
    reserve := (1406348797/6250000000) }

theorem quarter_006_006_valid : quarter_006_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_006]
  · intro i; fin_cases i <;> norm_num [quarter_006_006]
  · norm_num [quarter_006_006]
  · norm_num [quarter_006_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_006]

def quarter_006_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1261833/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (8233003/100000000)]
    alternative := .zero
    polynomial := [(-18207877560843676587/690847747736000000000), (-610922227224111/411650150000000), (-478773038112525358347/345423873868000000000), (-610922227224111/411650150000000), (-939338198664207040107/690847747736000000000)]
    bernstein := [(24256930460084798244717/107944960583750000000000), (376622922361305081633663/1727119369340000000000000), (1459948347390081789178733/6908477477360000000000000), (2659393558265338863882147/13004192898560000000000000), (20555908005932725264491429/104033543188480000000000000)]
    reserve := (19758923301/100000000000) }

theorem quarter_006_007_valid : quarter_006_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_007]
  · intro i; fin_cases i <;> norm_num [quarter_006_007]
  · norm_num [quarter_006_007]
  · norm_num [quarter_006_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_007]

def quarter_006_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(32313339/100000000), (32313339/100000000), (191249/12500000), (191249/12500000), 0, 0, (32313339/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (113299/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9118111/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2076047/25000000), (1/100000000), (99429/25000000), (1/100000000), (4056533/50000000)]
    alternative := .zero
    polynomial := [(2401977950270687655989351/2800490333270421000000000000), (-221159714521358025603/168431063301020000000), (-1807461892153531161258390649/1400245166635210500000000000), (-221159714521358025603/168431063301020000000), (-3617325762257333010172770649/2800490333270421000000000000)]
    bernstein := [(18354611487691341002559018546091163/93200318291239610880000000000000000), (8899388719895131216025537693704727/46600159145619805440000000000000000), (994315380791201477283290368172573/5376941439879208320000000000000000), (2082816263673057253383559545808207/11650039786404951360000000000000000), (1005110755092979865695491120840203/5825019893202475680000000000000000)]
    reserve := (86275306653/500000000000) }

theorem quarter_006_008_valid : quarter_006_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_008]
  · intro i; fin_cases i <;> norm_num [quarter_006_008]
  · norm_num [quarter_006_008]
  · norm_num [quarter_006_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_008]

def quarter_006_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(15403743/50000000), (15403743/50000000), (947193/25000000), (947193/25000000), 0, 0, (15403743/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (224453/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (501931/3125000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8117081/100000000), (1/100000000), (246219/25000000), (1/100000000), (245099/3125000)]
    alternative := .zero
    polynomial := [(236405291009810927407912485901/7837597651650594576000000000000), (-109745002551254139603/99474421800950000000), (-4592728307527360458428006234099/3918798825825297288000000000000), (-109745002551254139603/99474421800950000000), (-9421861906064531844263924954099/7837597651650594576000000000000)]
    bernstein := [(216186934134237251827047723346965181/1254015624264095132160000000000000000), (11990816488031749089918518457320281/71658035672234007552000000000000000), (97623457893830725035856295275405423/601927499646765663436800000000000000), (2519216758864263639440245332088219/16051399990580417691648000000000000), (194694804105025924926342428165269/1284111999246433415331840000000000)]
    reserve := (151618242193/1000000000000) }

theorem quarter_006_009_valid : quarter_006_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_009]
  · intro i; fin_cases i <;> norm_num [quarter_006_009]
  · norm_num [quarter_006_009]
  · norm_num [quarter_006_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_009]

def quarter_006_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(7366441/25000000), (7366441/25000000), (2900677/50000000), (2900677/50000000), 0, 0, (7366441/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (214801/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2809941/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1586897/20000000), (1/100000000), (1508039/100000000), (1/100000000), (7587433/100000000)]
    alternative := .zero
    polynomial := [(9051872097073200233238090319/174591397826314025375000000000), (-106453308950782920921/115773794859625000000), (-93837506398532440998557139681/87295698913157012687500000000), (-106453308950782920921/115773794859625000000), (-196726884894138082230352369681/174591397826314025375000000000)]
    bernstein := [(333375772386636906991831352547/2200388816912560762880000000000), (2024716030966884634538349661739/13752430105703504768000000000000), (159626692446919979327209017421051/1117384946088409762400000000000000), (193307968625240773284486863420239/1396731182610512203000000000000000), (233695591798729398586050881074119/1745913978263140253750000000000000)]
    reserve := (33463216789/250000000000) }

theorem quarter_006_010_valid : quarter_006_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_010]
  · intro i; fin_cases i <;> norm_num [quarter_006_010]
  · norm_num [quarter_006_010]
  · norm_num [quarter_006_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_010]

def quarter_006_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(3533607/12500000), (3533607/12500000), (7596717/100000000), (7596717/100000000), 0, 0, (3533607/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2250209/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6089907/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3877399/50000000), (1/100000000), (123421/6250000), (1/100000000), (7344087/100000000)]
    alternative := .zero
    polynomial := [(202039168830725356220222847261/2999066380661732840960000000000), (-35940285947208048021/47459925982855000000), (-1493564344156628851611159987939/1499533190330866420480000000000), (-35940285947208048021/47459925982855000000), (-3189167857143983059442542823139/2999066380661732840960000000000)]
    bernstein := [(4012323324429929096371447710119061/29990663806617328409600000000000000), (15617024869548097598711938344653283/119962655226469313638400000000000000), (60697406731751856302745883112526849/479850620905877254553600000000000000), (235537891167965377379056309000927647/1919402483623509018214400000000000000), (912455618821661825617402325110202541/7677609934494036072857600000000000000)]
    reserve := (23769262221/200000000000) }

theorem quarter_006_011_valid : quarter_006_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_011]
  · intro i; fin_cases i <;> norm_num [quarter_006_011]
  · norm_num [quarter_006_011]
  · norm_num [quarter_006_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_011]

def quarter_006_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(27200281/100000000), (27200281/100000000), (4599789/50000000), (4599789/50000000), 0, 0, (27200281/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (272499/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (10435001/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1515353/20000000), (1/100000000), (2391393/100000000), (1/100000000), (355579/5000000)]
    alternative := .zero
    polynomial := [(597286909070981925419179551/7669933336173458875000000000), (-18870087124311341571/30790154536400000000), (-3575199930832728997419697949/3834966668086729437500000000), (-18870087124311341571/30790154536400000000), (-7747686770736439920258575449/7669933336173458875000000000)]
    bernstein := [(2333053703608744603989858035354931/19635029340604054720000000000000000), (324849290108369292402092988494697/2805004191514864960000000000000000), (829928209366935062343202000939151/7363136002726520520000000000000000), (537655130823274066790306583175681/4908757335151013680000000000000000), (130396838440015557373906168731601/1227189333787753420000000000000000)]
    reserve := (106256495921/1000000000000) }

theorem quarter_006_012_valid : quarter_006_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_012]
  · intro i; fin_cases i <;> norm_num [quarter_006_012]
  · norm_num [quarter_006_012]
  · norm_num [quarter_006_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_012]

def quarter_006_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(13122937/50000000), (13122937/50000000), (10631189/100000000), (10631189/100000000), 0, 0, (13122937/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (787261/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8800653/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (36997/500000), (1/100000000), (552707/20000000), (1/100000000), (6888549/100000000)]
    alternative := .zero
    polynomial := [(23738628588472138910402067029/281721000563069142000000000000), (-410434484101716911581/849518824510000000000), (-124141649090172696174000092971/140860500281534571000000000000), (-410434484101716911581/849518824510000000000), (-272021926768817531258402252971/281721000563069142000000000000)]
    bernstein := [(4790197492646644858418621526814229/45075360090091062720000000000000000), (11508071343000244483564106980033/110886494686570880000000000000000), (54743984685357550687247479727289887/540904321081092752640000000000000000), (11845465587155810218258871591614543/120200960240242833920000000000000000), (69089848764100313672407684741687829/721205761441457003520000000000000000)]
    reserve := (47898846943/500000000000) }

theorem quarter_006_013_valid : quarter_006_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_013]
  · intro i; fin_cases i <;> norm_num [quarter_006_013]
  · norm_num [quarter_006_013]
  · norm_num [quarter_006_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_013]

def quarter_006_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(3174171/12500000), (3174171/12500000), (2977487/25000000), (2977487/25000000), 0, 0, (3174171/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3527823/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1452851/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (361097/5000000), (1/100000000), (3095943/100000000), (1/100000000), (6673779/100000000)]
    alternative := .zero
    polynomial := [(867770509797962766804172429223/9947807992924321212000000000000), (-59578327356746653/163006058953125000), (-4184396473355410926926267890777/4973903996462160606000000000000), (-59578327356746653/163006058953125000), (-9236563456508784620656708210777/9947807992924321212000000000000)]
    bernstein := [(143584485183285774351171479411182519/1498022850699191900160000000000000000), (1493348149346888522544929833878823/15916492788678913939200000000000000), (4379268062091469840409570891259623/47749478366036741817600000000000000), (890494885999484013749638002023/9947807992924321212000000000000), (867770509797962766804172429223/9947807992924321212000000000000)]
    reserve := (87232334039/1000000000000) }

theorem quarter_006_014_valid : quarter_006_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_014]
  · intro i; fin_cases i <;> norm_num [quarter_006_014]
  · norm_num [quarter_006_014]
  · norm_num [quarter_006_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_014]

def quarter_006_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(24844893/100000000), (24844893/100000000), (12732661/100000000), (12732661/100000000), 0, 0, (24844893/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3771517/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2932651/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3527103/50000000), (1/100000000), (827451/25000000), (1/100000000), (6522051/100000000)]
    alternative := .zero
    polynomial := [(591813986600962708118620526759/6767871228655144214400000000000), (369039963120895851147/511198792183400000000), (-2771126743673349130008120657241/3383935614327572107200000000000), (369039963120895851147/511198792183400000000), (-6134067473947660968134861841241/6767871228655144214400000000000)]
    bernstein := [(591813986600962708118620526759/6767871228655144214400000000000), (622350235253397547411364156459/6767871228655144214400000000000), (164793894526543268792089960679261/1709777994607615380480000000000000), (1090735781598206647304246888346859/10828593965848230743040000000000000), (1819056684243544205235842754896107559/17325750345357169188864000000000000000)]
    reserve := (5465289293/62500000000) }

theorem quarter_006_015_valid : quarter_006_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_015]
  · intro i; fin_cases i <;> norm_num [quarter_006_015]
  · norm_num [quarter_006_015]
  · norm_num [quarter_006_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_015]

def quarter_006_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(24546209/100000000), (24546209/100000000), (6590343/50000000), (6590343/50000000), 0, 0, (24546209/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1952113/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (284623/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6891791/100000000), (1/100000000), (1713133/50000000), (1/100000000), (160501/2500000)]
    alternative := .zero
    polynomial := [(40707126936258326161064055833/473740954610668175750000000000), (217428299558719460293/276534836822750000000), (-191863762738401167271100579167/236870477305334087875000000000), (217428299558719460293/276534836822750000000), (-424434652413060660703265214167/473740954610668175750000000000)]
    bernstein := [(127449705912117710977090752948691433/1212776843803310529920000000000000000), (66556605743331968901936720049940033/606388421901655264960000000000000000), (34670353739583190708921893225753033/303194210950827632480000000000000000), (18019702091052856536165518671570433/151597105475413816240000000000000000), (9346543297723778707557091516112233/75798552737706908120000000000000000)]
    reserve := (52544582527/500000000000) }

theorem quarter_006_016_valid : quarter_006_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_016]
  · intro i; fin_cases i <;> norm_num [quarter_006_016]
  · norm_num [quarter_006_016]
  · norm_num [quarter_006_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_016]

def quarter_006_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(24266529/100000000), (24266529/100000000), (13600207/100000000), (13600207/100000000), 0, 0, (24266529/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4028491/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1633241/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1680831/25000000), (1/100000000), (3535319/100000000), (1/100000000), (3153901/50000000)]
    alternative := .zero
    polynomial := [(6208127305094677726973003058961/74965372743029868756000000000000), (200393790855646350151/235607758743600000000), (-30174860528196199433700355421039/37482686371514934378000000000000), (200393790855646350151/235607758743600000000), (-66557848361487076594373713901039/74965372743029868756000000000000)]
    bernstein := [(1480457446233233991988298782767227761/11994459638884779000960000000000000000), (3077256881707743611219638822350288883/23988919277769558001920000000000000000), (19151236439073746270330034816242914747/143933515666617348011520000000000000000), (13219302114861411951613735920132333947/95955677111078232007680000000000000000), (27329359923369015650408676248335052641/191911354222156464015360000000000000000)]
    reserve := (123428440363/1000000000000) }

theorem quarter_006_017_valid : quarter_006_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_017]
  · intro i; fin_cases i <;> norm_num [quarter_006_017]
  · norm_num [quarter_006_017]
  · norm_num [quarter_006_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_017]

def quarter_006_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(6001049/25000000), (6001049/25000000), (13993707/100000000), (13993707/100000000), 0, 0, (6001049/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4145049/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (80189/4000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6549321/100000000), (1/100000000), (3637607/100000000), (1/100000000), (386603/6250000)]
    alternative := .zero
    polynomial := [(287636586959854632503191899863/3684149667299037896400000000000), (308962301197541277641/337598286208400000000), (-1481064427183763293029073988137/1842074833649518948200000000000), (308962301197541277641/337598286208400000000), (-3249765441327381218561339876137/3684149667299037896400000000000)]
    bernstein := [(1344430013859038052158925372454847303/9431423148285537014784000000000000000), (348022477784765839295104314957901001/2357855787071384253696000000000000000), (269837429722426572480782570213399201/1768391840303538190272000000000000000), (23212236300113067604727642307928189/147365986691961515856000000000000000), (5982270010324488424245153474736463/36841496672990378964000000000000000)]
    reserve := (142547947719/1000000000000) }

theorem quarter_006_018_valid : quarter_006_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_018]
  · intro i; fin_cases i <;> norm_num [quarter_006_018]
  · norm_num [quarter_006_018]
  · norm_num [quarter_006_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_018]

def quarter_006_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(2969717/12500000), (2969717/12500000), (3590849/25000000), (3590849/25000000), 0, 0, (2969717/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2127277/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (77067/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6370303/100000000), (1/100000000), (3733707/100000000), (1/100000000), (3026991/50000000)]
    alternative := .zero
    polynomial := [(1719705942831181976868289275113/23998837152815279337000000000000), (78785472834014414003/80345207701137500000), (-9683454804840359288225731364887/11999418576407639668500000000000), (78785472834014414003/80345207701137500000), (-21086615552511900553319752004887/23998837152815279337000000000000)]
    bernstein := [(39007561062419728028127475702947713/239988371528152793370000000000000000), (10740036446991130337987355454393151/63996899074174078232000000000000000), (79734863153568832321665731055709631/460777673334053363270400000000000000), (1459830254547660375790088044516663/8191603081494282013696000000000000), (720819222491243713736980117510097/3931969479117255366574080000000000)]
    reserve := (162539379779/1000000000000) }

theorem quarter_006_019_valid : quarter_006_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_019]
  · intro i; fin_cases i <;> norm_num [quarter_006_019]
  · norm_num [quarter_006_019]
  · norm_num [quarter_006_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_019]

def quarter_006_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(11762437/50000000), (11762437/50000000), (1471269/10000000), (1471269/10000000), 0, 0, (23524873/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2179009/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6186731/100000000), (1/100000000), (478063/12500000), (1/100000000), (1188853/20000000)]
    alternative := .zero
    polynomial := [(1849325853339628079821754245497/28129661802602041672000000000000), (318599150285693/309336550000000), (-11385608856740271943688815594503/14064830901301020836000000000000), (318599150285693/309336550000000), (-24620543566820171967199385434503/28129661802602041672000000000000)]
    bernstein := [(846331189833573086666394406976993/4608763789738318507540480000000000), (10892034194326734452876465041152143/57609547371728981344256000000000000), (140023700024175278342440518696105777/720119342146612266803200000000000000), (359651830914134458311744164320068499/1800298355366530667008000000000000000), (922893402606054518091418779431703657/4500745888416326667520000000000000000)]
    reserve := (91817592357/500000000000) }

theorem quarter_006_020_valid : quarter_006_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_020]
  · intro i; fin_cases i <;> norm_num [quarter_006_020]
  · norm_num [quarter_006_020]
  · norm_num [quarter_006_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_020]

def quarter_006_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(2329467/10000000), (2329467/10000000), (3011599/20000000), (3011599/20000000), 0, 0, (2329467/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (44603/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2999221/50000000), (1/100000000), (782853/20000000), (1/100000000), (5886097/100000000)]
    alternative := .zero
    polynomial := [(61881136794370576645731328123/987161178013556911500000000000), (63023447819493/59984420000000), (-398030740778370698946502771877/493580589006778455750000000000), (63023447819493/59984420000000), (-857942618351111974538736871877/987161178013556911500000000000)]
    bernstein := [(32417925410171149460512841002043563/157945788482169105840000000000000000), (66549416688361840034916028418919047/315891576964338211680000000000000000), (409488864281533644040923440455964329/1895349461786029270080000000000000000), (16454749625171766292972490421206351/74327429873961932160000000000000000), (33695806134900776597294358133658219/148654859747923864320000000000000000)]
    reserve := (51311791409/250000000000) }

theorem quarter_006_021_valid : quarter_006_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_021]
  · intro i; fin_cases i <;> norm_num [quarter_006_021]
  · norm_num [quarter_006_021]
  · norm_num [quarter_006_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_021]

def quarter_006_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(23065809/100000000), (23065809/100000000), (7700643/50000000), (7700643/50000000), 0, 0, (23065809/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2280993/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (5805871/100000000), (1/100000000), (2001751/50000000), (1/100000000), (5828269/100000000)]
    alternative := .zero
    polynomial := [(7964351092695395724387952062027/135471213168437481098000000000000), (155769336089913/145146775000000), (-54530711466133879624563613577973/67735606584218740549000000000000), (155769336089913/145146775000000), (-117025774024963154973515179217973/135471213168437481098000000000000)]
    bernstein := [(78684815281162405171842269973807800427/346806305711199951610880000000000000000), (437901190779453150020866882675162707/1884816878865217128320000000000000000), (322063904727514372287729875263731287/1354712131684374810980000000000000000), (3579699026745225256453497931797159/14725131866134508815000000000000000), (5258573752251781824119801447362563/21167377057568356421562500000000000)]
    reserve := (56721009671/250000000000) }

theorem quarter_006_022_valid : quarter_006_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_022]
  · intro i; fin_cases i <;> norm_num [quarter_006_022]
  · norm_num [quarter_006_022]
  · norm_num [quarter_006_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_022]

def quarter_006_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(11419977/50000000), (11419977/50000000), (15740069/100000000), (15740069/100000000), 0, 0, (11419977/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (72849/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1402421/25000000), (1/100000000), (4091567/100000000), (1/100000000), (3607/62500)]
    alternative := .zero
    polynomial := [(893318912701229247982103029/16557859870184919200000000000), (307876150472949/280484200000000), (-6670296242768161272452232971/8278929935092459600000000000), (307876150472949/280484200000000), (-14233911398237551792886568971/16557859870184919200000000000)]
    bernstein := [(643327902457492604804358573901/2587165604716393625000000000000), (10520811397711130775115887655793/41394649675462298000000000000000), (128962229411425968939623564024743/496735796105547576000000000000000), (1404343793381612331931704393652541/5298515158459174144000000000000000), (11463284826811333104935547892978069/42388121267673393152000000000000000)]
    reserve := (248661276759/1000000000000) }

theorem quarter_006_023_valid : quarter_006_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_023]
  · intro i; fin_cases i <;> norm_num [quarter_006_023]
  · norm_num [quarter_006_023]
  · norm_num [quarter_006_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_023]

def quarter_006_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(5654641/25000000), (5654641/25000000), (8036077/50000000), (8036077/50000000), 0, 0, (5654641/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2380351/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1082111/20000000), (1/100000000), (4177891/100000000), (1/100000000), (5715259/100000000)]
    alternative := .zero
    polynomial := [(1241766369576687271322976260339/25838353356082461359000000000000), (9504484577389/8453992187500), (-10446762611206631559198393259661/12919176678041230679500000000000), (9504484577389/8453992187500), (-22135291591989950389719762779661/25838353356082461359000000000000)]
    bernstein := [(17905199399210715242550564825014032979/66146184591571101079040000000000000000), (25738032284562077088190613748441101/93163640269818452224000000000000000), (13005119095838174937262985288551627/46148500877840303078400000000000000), (19005294017823993767800959692241947/66146184591571101079040000000000000), (1936794200074166230870255378821971/6614618459157110107904000000000000)]
    reserve := (5413826817/20000000000) }

theorem quarter_006_024_valid : quarter_006_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_024]
  · intro i; fin_cases i <;> norm_num [quarter_006_024]
  · norm_num [quarter_006_024]
  · norm_num [quarter_006_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_024]

def quarter_006_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(22402903/100000000), (22402903/100000000), (8197823/50000000), (8197823/50000000), 0, 0, (22402903/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4856523/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2604577/50000000), (1/100000000), (2130991/50000000), (1/100000000), (2830383/50000000)]
    alternative := .zero
    polynomial := [(5151894430810137131229175939097/125676480712637232648000000000000), (300355205254231/260457700000000), (-51158465704921518812802366940903/62838240356318616324000000000000), (300355205254231/260457700000000), (-107468825840653174756833909820903/125676480712637232648000000000000)]
    bernstein := [(9429441835028303715919998950399033/32173179062435131557888000000000000), (10680227111386878195798285223608331/35747976736039035064320000000000000), (2938218715057722911575718864224911683/9651953718730539467366400000000000000), (1108339249325126422287560811077252803/3574797673603903506432000000000000000), (101552036936319666944741640854828437577/321731790624351315578880000000000000000)]
    reserve := (11723357293/40000000000) }

theorem quarter_006_025_valid : quarter_006_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_025]
  · intro i; fin_cases i <;> norm_num [quarter_006_025]
  · norm_num [quarter_006_025]
  · norm_num [quarter_006_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_025]

def quarter_006_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(22194049/100000000), (22194049/100000000), (16708927/100000000), (16708927/100000000), 0, 0, (22194049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4949319/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (5006137/100000000), (1/100000000), (2171709/50000000), (1/100000000), (700999/12500000)]
    alternative := .zero
    polynomial := [(1989061814211517344042915907109/60969375564787638936000000000000), (593051644332849/500613700000000), (-25074084361474473318754921372891/30484687782393819468000000000000), (593051644332849/500613700000000), (-52137230537160463981552758652891/60969375564787638936000000000000)]
    bernstein := [(49313391205555774453528658183751467669/156081601445856355676160000000000000000), (12555128764403044880759914541818797037/39020400361464088919040000000000000000), (9585721400867069556354626990720268803/29265300271098066689280000000000000000), (812867768911045395102848481730503473/2438775022591505557440000000000000000), (206717503520092975863856017783402029/609693755647876389360000000000000000)]
    reserve := (39493276873/125000000000) }

theorem quarter_006_026_valid : quarter_006_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_026]
  · intro i; fin_cases i <;> norm_num [quarter_006_026]
  · norm_num [quarter_006_026]
  · norm_num [quarter_006_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_026]

def quarter_006_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3267003/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (912737/12500000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-2169191422463283237963/19147396786000000000000), (1680685461741/903700000000), (-14934122485480637997963/9573698393000000000000), (1680685461741/903700000000), (-27699053548497992757963/19147396786000000000000)]
    bernstein := [(9375388818738124642177371/27353423980000000000000000), (38369849824100541136894641/109413695920000000000000000), (1098455096793363008082180577/3063583485760000000000000000), (4489371739241140037519205867/12254333943040000000000000000), (18336304958251293684958548357/49017335772160000000000000000)]
    reserve := (8568752513/25000000000) }

theorem quarter_006_027_valid : quarter_006_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_027]
  · intro i; fin_cases i <;> norm_num [quarter_006_027]
  · norm_num [quarter_006_027]
  · norm_num [quarter_006_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_027]

def quarter_006_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (27123987/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1414771/20000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-2045176436384187949203/14839533019000000000000), (1375723219576101/707385500000000), (-11938198350120634489203/7419766509500000000000), (1375723219576101/707385500000000), (-21831220263857081029203/14839533019000000000000)]
    bernstein := [(14232313946797236569150910717/37989204528640000000000000000), (7272057390209834234183394663/18994602264320000000000000000), (3713340669584878429664192757/9497301132160000000000000000), (1895007804238793106554407023/4748650566080000000000000000), (966512313079091909064725997/2374325283040000000000000000)]
    reserve := (187320504909/500000000000) }

theorem quarter_006_028_valid : quarter_006_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_028]
  · intro i; fin_cases i <;> norm_num [quarter_006_028]
  · norm_num [quarter_006_028]
  · norm_num [quarter_006_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_028]

def quarter_006_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (28042893/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1708703/25000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-2961433653682250127093/17922585767000000000000), (1390417219429161/683481200000000), (-14909824045531678347093/8961292883500000000000), (1390417219429161/683481200000000), (-26858214437381106567093/17922585767000000000000)]
    bernstein := [(1169108088585052769503834107/2867613722720000000000000000), (477394998356574226371066483/1147045489088000000000000000), (194828631953279649344286731/458818195635200000000000000), (79467631150836293708282691/183527278254080000000000000), (32396632704552157804661403/73410911301632000000000000)]
    reserve := (203846856939/500000000000) }

theorem quarter_006_029_valid : quarter_006_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_006_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_006_029]
  · intro i; fin_cases i <;> norm_num [quarter_006_029]
  · norm_num [quarter_006_029]
  · norm_num [quarter_006_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_006_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_006_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_006_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_006_029]

def quarterTable006 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 0, 0, 2, 2]
  rows := [quarter_006_000, quarter_006_001, quarter_006_002, quarter_006_003, quarter_006_004, quarter_006_005, quarter_006_006, quarter_006_007, quarter_006_008, quarter_006_009, quarter_006_010, quarter_006_011, quarter_006_012, quarter_006_013, quarter_006_014, quarter_006_015, quarter_006_016, quarter_006_017, quarter_006_018, quarter_006_019, quarter_006_020, quarter_006_021, quarter_006_022, quarter_006_023, quarter_006_024, quarter_006_025, quarter_006_026, quarter_006_027, quarter_006_028, quarter_006_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_006_000_valid
    · exact quarter_006_001_valid
    · exact quarter_006_002_valid
    · exact quarter_006_003_valid
    · exact quarter_006_004_valid
    · exact quarter_006_005_valid
    · exact quarter_006_006_valid
    · exact quarter_006_007_valid
    · exact quarter_006_008_valid
    · exact quarter_006_009_valid
    · exact quarter_006_010_valid
    · exact quarter_006_011_valid
    · exact quarter_006_012_valid
    · exact quarter_006_013_valid
    · exact quarter_006_014_valid
    · exact quarter_006_015_valid
    · exact quarter_006_016_valid
    · exact quarter_006_017_valid
    · exact quarter_006_018_valid
    · exact quarter_006_019_valid
    · exact quarter_006_020_valid
    · exact quarter_006_021_valid
    · exact quarter_006_022_valid
    · exact quarter_006_023_valid
    · exact quarter_006_024_valid
    · exact quarter_006_025_valid
    · exact quarter_006_026_valid
    · exact quarter_006_027_valid
    · exact quarter_006_028_valid
    · exact quarter_006_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
