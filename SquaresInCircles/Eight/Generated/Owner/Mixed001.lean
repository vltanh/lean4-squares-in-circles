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

def mixed_001_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-44023114674015643/64076356250000000), (-42064340/10252217), (-108099470924015643/32038178125000000), (-42064340/10252217), (-172175827174015643/64076356250000000)]
    bernstein := [(141809012789670638453/262456755200000000000), (343300361474731309041/656141888000000000000), (830020257690478769581/1640354720000000000000), (2004034820269922709033/4100886800000000000000), (4831435808391272355557/10252217000000000000000)]
    reserve := (235628830739/500000000000) }

theorem mixed_001_000_valid : mixed_001_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_000]
  · intro i; fin_cases i <;> norm_num [mixed_001_000]
  · norm_num [mixed_001_000]
  · norm_num [mixed_001_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_000]

def mixed_001_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3208677076379484783/5305390750000000000), (-81371960/21221563), (-8514067826379484783/2652695375000000000), (-81371960/21221563), (-13819458576379484783/5305390750000000000)]
    bernstein := [(398440040343319488262417/848862520000000000000000), (769821467242199697197803/1697725040000000000000000), (45932083125209102361323/105013920000000000000000), (2860481863390760054215843/6790900160000000000000000), (5499790888762519119986337/13581800320000000000000000)]
    reserve := (101234570513/250000000000) }

theorem mixed_001_001_valid : mixed_001_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_001]
  · intro i; fin_cases i <;> norm_num [mixed_001_001]
  · norm_num [mixed_001_001]
  · norm_num [mixed_001_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_001]

def mixed_001_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3267003/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (912737/12500000)]
    alternative := .zero
    polynomial := [(-92663288055956760816519/957369839300000000000000), (-1680685461741/903700000000), (-730909841206824498816519/478684919650000000000000), (-1680685461741/903700000000), (-1369156394357692236816519/957369839300000000000000)]
    bernstein := [(966247520088043904104141285641/2450866788608000000000000000000), (236735838225502664689345193271/612716697152000000000000000000), (57967556851432334861331424501/153179174288000000000000000000), (2026473625640590106724321333/5470684796000000000000000000), (495580246525690679573276823/1367671199000000000000000000)]
    reserve := (362353354291/1000000000000) }

theorem mixed_001_002_valid : mixed_001_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_002]
  · intro i; fin_cases i <;> norm_num [mixed_001_002]
  · norm_num [mixed_001_002]
  · norm_num [mixed_001_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_002]

def mixed_001_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (12539659/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (1879413/25000000)]
    alternative := .zero
    polynomial := [(-147638663224793269111981/1971316295700000000000000), (-222859008882521/125294200000000), (-1461849513882684631111981/985658147850000000000000), (-222859008882521/125294200000000), (-2776060364540575993111981/1971316295700000000000000)]
    bernstein := [(7133195100383229699381553739/19713162957000000000000000000), (27933022056879946469937582743/78852651828000000000000000000), (327935811815224217180169684773/946231821936000000000000000000), (427482237255739127791689792667/1261642429248000000000000000000), (1670522742807446047587957082979/5046569716992000000000000000000)]
    reserve := (5172209901/15625000000) }

theorem mixed_001_003_valid : mixed_001_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_003]
  · intro i; fin_cases i <;> norm_num [mixed_001_003]
  · norm_num [mixed_001_003]
  · norm_num [mixed_001_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_003]

def mixed_001_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (23954683/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (3859927/50000000)]
    alternative := .zero
    polynomial := [(-224373922239533698935699/4048677430300000000000000), (-1313146353535203/771985400000000), (-2923492182115017496935699/2024338715150000000000000), (-1313146353535203/771985400000000), (-5622610441990501294935699/4048677430300000000000000)]
    bernstein := [(3426263388417280420823494338141/10364614221568000000000000000000), (335001273883739933101251705591/1036461422156800000000000000000), (32730376526948214297491901813/103646142215680000000000000000), (187960653573170438754495471/609683189504000000000000000), (18334591006638448056093117/60968318950400000000000000)]
    reserve := (300723249751/1000000000000) }

theorem mixed_001_004_valid : mixed_001_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_004]
  · intro i; fin_cases i <;> norm_num [mixed_001_004]
  · norm_num [mixed_001_004]
  · norm_num [mixed_001_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_004]

def mixed_001_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (355679/1562500), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (7907263/100000000)]
    alternative := .zero
    polynomial := [(-316710299712657820801131/8293928160700000000000000), (-642966360237003/395363150000000), (-5845995684886470082801131/4146964080350000000000000), (-642966360237003/395363150000000), (-11375281070060282344801131/8293928160700000000000000)]
    bernstein := [(37509947354744588258380773/124896800537600000000000000), (366195732031696392814608861/1248968005376000000000000000), (60724060759598289092801291477/212324560913920000000000000000), (84541511655674296893631070763/303320801305600000000000000000), (63316419345027849689255508399/233323693312000000000000000000)]
    reserve := (135683647139/500000000000) }

theorem mixed_001_005_valid : mixed_001_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_005]
  · intro i; fin_cases i <;> norm_num [mixed_001_005]
  · norm_num [mixed_001_005]
  · norm_num [mixed_001_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_005]

def mixed_001_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (860301/4000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (8078689/100000000)]
    alternative := .zero
    polynomial := [(-11484892126460056257429/498455111300000000000000), (-1255496754111699/807868900000000), (-343788296336759314257429/249227555650000000000000), (-1255496754111699/807868900000000), (-676091700547058572257429/498455111300000000000000)]
    bernstein := [(345834960596636458573155171531/1276045084928000000000000000000), (42125217514823336805243476859/159505635616000000000000000000), (1281522804391632782121316319/4984551113000000000000000000), (311560148851545318614065407/1246137778250000000000000000), (18914957637719204335994499/77883611140625000000000000)]
    reserve := (30357730851/125000000000) }

theorem mixed_001_006_valid : mixed_001_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_006]
  · intro i; fin_cases i <;> norm_num [mixed_001_006]
  · norm_num [mixed_001_006]
  · norm_num [mixed_001_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_006]

def mixed_001_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1261833/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (8233003/100000000)]
    alternative := .zero
    polynomial := [(-85114001497122885053511/8635596846700000000000000), (-610922227224111/411650150000000), (-5842178508393143907053511/4317798423350000000000000), (-610922227224111/411650150000000), (-11599243015289164929053511/8635596846700000000000000)]
    bernstein := [(327291505845328477274956641/1349312007296875000000000000), (5091212232940435007937001899/21588992116750000000000000000), (19775980427494508302208915309/86355968467000000000000000000), (36103365111558257666917052631/162552411232000000000000000000), (279739668186310126487183755017/1300419289856000000000000000000)]
    reserve := (215114978967/1000000000000) }

theorem mixed_001_007_valid : mixed_001_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_007]
  · intro i; fin_cases i <;> norm_num [mixed_001_007]
  · norm_num [mixed_001_007]
  · norm_num [mixed_001_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_007]

def mixed_001_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (18811861/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (8369161/100000000)]
    alternative := .zero
    polynomial := [(12954269949119063913043/8778412972900000000000000), (-1185006088149939/836916100000000), (-5839320986794794450086957/4389206486450000000000000), (-1185006088149939/836916100000000), (-11691596243538707964086957/8778412972900000000000000)]
    bernstein := [(284026349550267728010358966979/1321925718272000000000000000000), (137668078992893016592982005391/660962859136000000000000000000), (3398275777845115843380245467489/16854552907968000000000000000000), (547420567793130722633369795927/2809092151328000000000000000000), (264103190981369482436709746083/1404546075664000000000000000000)]
    reserve := (94017275601/500000000000) }

theorem mixed_001_008_valid : mixed_001_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_008]
  · intro i; fin_cases i <;> norm_num [mixed_001_008]
  · norm_num [mixed_001_008]
  · norm_num [mixed_001_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_008]

def mixed_001_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17378669/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8422667/100000000), (1/100000000), (1/100000000), (1/100000000), (1697243/20000000)]
    alternative := .zero
    polynomial := [(19658612209052642773209/1780238182700000000000000), (-1145036621882967/848621500000000), (-1167166831056026139226791/890119091350000000000000), (-1145036621882967/848621500000000), (-2353992274321104921226791/1780238182700000000000000)]
    bernstein := [(53497602430599628898265174729/284838109232000000000000000000), (20666193878534772149594924403/113935243692800000000000000000), (7969148856337952664579780369/45574097477120000000000000000), (613402506993759415634069871/3645927798169600000000000000), (47113615926382120952352321/291674223853568000000000000)]
    reserve := (10095513263/62500000000) }

theorem mixed_001_009_valid : mixed_001_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_009]
  · intro i; fin_cases i <;> norm_num [mixed_001_009]
  · norm_num [mixed_001_009]
  · norm_num [mixed_001_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_009]

def mixed_001_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1081289/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7946909/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (169881/2000000), (1/100000000), (1/100000000), (1/100000000), (2145833/25000000)]
    alternative := .zero
    polynomial := [(873230409495893525520191/36453625587300000000000000), (-1473178829979322664/1186641457919921875), (-23429186405679935892479809/18226812793650000000000000), (-1473178829979322664/1186641457919921875), (-47731603220855765310479809/36453625587300000000000000)]
    bernstein := [(962529287830759371391376279/5972562016223232000000000000), (1929984155366600182107475041/12442837533798400000000000000), (104258092180091500046776960217/699909611276160000000000000000), (13872812079295047635611480857/97209668232800000000000000000), (49707349404136532471856268391/364536255873000000000000000000)]
    reserve := (681788829/5000000000) }

theorem mixed_001_010_valid : mixed_001_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_010]
  · intro i; fin_cases i <;> norm_num [mixed_001_010]
  · norm_num [mixed_001_010]
  · norm_num [mixed_001_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_010]

def mixed_001_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2783853/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3590469/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2147419/25000000), (1/100000000), (1/100000000), (1/100000000), (8659809/100000000)]
    alternative := .zero
    polynomial := [(7580361032004715603111073/206624870921900000000000000), (-918615299672613578079/826499483687600000000), (-130169551538429478250888927/103312435460950000000000000), (-918615299672613578079/826499483687600000000), (-267919464108863672104888927/206624870921900000000000000)]
    bernstein := [(281452143715587325173775555673/2066248709219000000000000000000), (1079957589563876613103460379319/8264994836876000000000000000000), (12398903345012449868218215121871/99179938042512000000000000000000), (15770280063683124335214203357171/132239917390016000000000000000000), (59976700196229542426771579779313/528959669560064000000000000000000)]
    reserve := (22677229909/200000000000) }

theorem mixed_001_011_valid : mixed_001_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_011]
  · intro i; fin_cases i <;> norm_num [mixed_001_011]
  · norm_num [mixed_001_011]
  · norm_num [mixed_001_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_011]

def mixed_001_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(15140809/50000000), (15140809/50000000), (44897/1000000), (933089/20000000), 0, 0, (15140809/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(29159/12500000), 0, (933089/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1452139/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (493801/6250000), (1636067/100000000), (1/100000000), (1/100000000), (7917203/100000000)]
    alternative := .zero
    polynomial := [(2090630699585854329237980444779/39160660231220414700000000000000), (-98060274840812962739/111700650245800000000), (-21626332375406311105701711555221/19580330115610207350000000000000), (-98060274840812962739/111700650245800000000), (-45343295450398476540641403555221/39160660231220414700000000000000)]
    bernstein := [(79543181379514046312820166760151316093/701759031343469831424000000000000000000), (38181512140063307911749197319456839231/350879515671734915712000000000000000000), (54835283423821483944571848546711927631/526319273507602373568000000000000000000), (8724223493241177902937135985879706359/87719878917933728928000000000000000000), (4150092670691880345578199405008355853/43859939458966864464000000000000000000)]
    reserve := (94621486529/1000000000000) }

theorem mixed_001_012_valid : mixed_001_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_012]
  · intro i; fin_cases i <;> norm_num [mixed_001_012]
  · norm_num [mixed_001_012]
  · norm_num [mixed_001_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_012]

def mixed_001_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(7242827/25000000), (7242827/25000000), (6336947/100000000), (6749129/100000000), 0, 0, (7242827/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(21091/6250000), 0, (6749129/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4857267/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1529597/20000000), (292409/12500000), (1/100000000), (1/100000000), (237621/3125000)]
    alternative := .zero
    polynomial := [(654988564129500743446893542861/10628025259801743300000000000000), (-171920418668441024507/242309579158000000000), (-5503167300540425738177834457139/5314012629900871650000000000000), (-171920418668441024507/242309579158000000000), (-11661323165210352219802562457139/10628025259801743300000000000000)]
    bernstein := [(160860081573134034365426934418591661/1700484041568278928000000000000000000), (102912886051364317510623564905248687/1133656027712185952000000000000000000), (1772532887931456107417302385229125783/20405808498819347136000000000000000000), (375685496204585818199713470419413087/4534624110848743808000000000000000000), (2142052899896075498275515685876858061/27207744665092462848000000000000000000)]
    reserve := (19682382041/250000000000) }

theorem mixed_001_013_valid : mixed_001_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_013]
  · intro i; fin_cases i <;> norm_num [mixed_001_013]
  · norm_num [mixed_001_013]
  · norm_num [mixed_001_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_013]

def mixed_001_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(11931407/50000000), (11931407/50000000), (6782237/100000000), (7358221/100000000), (356129/5000000), (178713/2500000), (11931407/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5891/50000000), 0, (235641/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6350301/100000000), (632149/25000000), (1/100000000), (2549847/100000000), (6294397/100000000)]
    alternative := .zero
    polynomial := [(8606378880754103198805979112966697401/126331555462596680545484100000000000000), (-39444178049076643319/79942631126994000000), (-51686149325938467698680133252181302599/63165777731298340272742050000000000000), (-39444178049076643319/79942631126994000000), (-111978677532631038596166245617329302599/126331555462596680545484100000000000000)]
    bernstein := [(2873179094418071699942067058285484649882289/35934309109360833577382144000000000000000000), (5196297420706630439660427161010262242167/67376829580051562957591520000000000000000), (44998897723346233624430422096208966222201/606391466220464066618323680000000000000000), (8995958593780402858999771038718884901/126331555462596680545484100000000000000), (8606378880754103198805979112966697401/126331555462596680545484100000000000000)]
    reserve := (13625065961/200000000000) }

theorem mixed_001_014_valid : mixed_001_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_014]
  · intro i; fin_cases i <;> norm_num [mixed_001_014]
  · norm_num [mixed_001_014]
  · norm_num [mixed_001_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_014]

def mixed_001_015 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(23860891/100000000), (23860891/100000000), (198843/2500000), (1077483/12500000), (2954027/50000000), (593569/10000000), (23860891/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(135591/100000000), 0, (271181/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (635531/10000000), (1481811/50000000), (1/100000000), (2116149/100000000), (1571307/25000000)]
    alternative := .zero
    polynomial := [(2370621576663241331021766775155557563/34793196767574557210780700000000000000), (109947333049858402871/199722861803400000000), (-14233311935589735548572279376918442437/17396598383787278605390350000000000000), (109947333049858402871/199722861803400000000), (-30837245447842712428166325528992442437/34793196767574557210780700000000000000)]
    bernstein := [(2370621576663241331021766775155557563/34793196767574557210780700000000000000), (96554428033050764600383793745689/1348991810157202125107812500000000), (12513968475233926953048695759448987859963/167007344484357874611747360000000000000000), (22674427242446566395428123187212093289/289943306396454643423172500000000000000), (2416604237809902989828877342787708057679721/29690194574996955486532864000000000000000000)]
    reserve := (34067314833/500000000000) }

theorem mixed_001_015_valid : mixed_001_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_015]
  · intro i; fin_cases i <;> norm_num [mixed_001_015]
  · norm_num [mixed_001_015]
  · norm_num [mixed_001_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_015]

def mixed_001_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(1664911/6250000), (1664911/6250000), (9743249/100000000), (5170511/50000000), 0, 0, (1664911/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(517051/100000000), 0, (5170511/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4942157/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7050661/100000000), (3590081/100000000), (1/100000000), (1/100000000), (6967297/100000000)]
    alternative := .zero
    polynomial := [(843313181170837768620074900919461/13226948684669694650775000000000000), (21858072822135893591/30702530770823125000), (-6203628374522636148409191027080539/6613474342334847325387500000000000), (21858072822135893591/30702530770823125000), (-13250569930216110065438456955080539/13226948684669694650775000000000000)]
    bernstein := [(2742060444101846138520076726071007354661/33860988632754418305984000000000000000000), (480511768659258434952394884904387235287/5643498105459069717664000000000000000000), (2265710445633168253751381991900481075583/25395741474565813729488000000000000000000), (131490471120844147833901258832591930887/1410874526364767429416000000000000000000), (205475650980382390391924999118894248261/2116311789547151144124000000000000000000)]
    reserve := (80979928667/1000000000000) }

theorem mixed_001_016_valid : mixed_001_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_016]
  · intro i; fin_cases i <;> norm_num [mixed_001_016]
  · norm_num [mixed_001_016]
  · norm_num [mixed_001_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_016]

def mixed_001_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(26278121/100000000), (26278121/100000000), (2078409/20000000), (10773593/100000000), 0, 0, (26278121/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13467/2500000), 0, (10773593/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3537259/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6892441/100000000), (945579/25000000), (1/100000000), (1/100000000), (1707673/25000000)]
    alternative := .zero
    polynomial := [(33450217746740213683819063984369/556474915165043257350000000000000), (67255168362775539383/85600257453040000000), (-259012085336694620053729723015631/278237457582521628675000000000000), (67255168362775539383/85600257453040000000), (-551474388420129453791278510015631/556474915165043257350000000000000)]
    bernstein := [(8650747136103659038513559507164019569/89035986426406921176000000000000000000), (1643484407718234998387250979459308737/16188361168437622032000000000000000000), (113038833412450017230745861015305469163/1068431837116883054112000000000000000000), (7122303336475606746368939040334654633/64753444673750488128000000000000000000), (162546032175025010521141348803548201089/1424575782822510738816000000000000000000)]
    reserve := (97160120119/1000000000000) }

theorem mixed_001_017_valid : mixed_001_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_017]
  · intro i; fin_cases i <;> norm_num [mixed_001_017]
  · norm_num [mixed_001_017]
  · norm_num [mixed_001_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_017]

def mixed_001_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3590469/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2783853/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8659809/100000000), (1/100000000), (1/100000000), (1/100000000), (2147419/25000000)]
    alternative := .zero
    polynomial := [(7580361032004715603111073/206624870921900000000000000), (918615299672613578079/826499483687600000000), (-130169551538429478250888927/103312435460950000000000000), (918615299672613578079/826499483687600000000), (-267919464108863672104888927/206624870921900000000000000)]
    bernstein := [(59976700196229542426771579779313/528959669560064000000000000000000), (15770280063683124335214203357171/132239917390016000000000000000000), (12398903345012449868218215121871/99179938042512000000000000000000), (1079957589563876613103460379319/8264994836876000000000000000000), (281452143715587325173775555673/2066248709219000000000000000000)]
    reserve := (22677229909/200000000000) }

theorem mixed_001_018_valid : mixed_001_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_018]
  · intro i; fin_cases i <;> norm_num [mixed_001_018]
  · norm_num [mixed_001_018]
  · norm_num [mixed_001_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_018]

def mixed_001_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7946909/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1081289/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2145833/25000000), (1/100000000), (1/100000000), (1/100000000), (169881/2000000)]
    alternative := .zero
    polynomial := [(873230409495893525520191/36453625587300000000000000), (1473178829979322664/1186641457919921875), (-23429186405679935892479809/18226812793650000000000000), (1473178829979322664/1186641457919921875), (-47731603220855765310479809/36453625587300000000000000)]
    bernstein := [(49707349404136532471856268391/364536255873000000000000000000), (13872812079295047635611480857/97209668232800000000000000000), (104258092180091500046776960217/699909611276160000000000000000), (1929984155366600182107475041/12442837533798400000000000000), (962529287830759371391376279/5972562016223232000000000000)]
    reserve := (681788829/5000000000) }

theorem mixed_001_019_valid : mixed_001_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_019]
  · intro i; fin_cases i <;> norm_num [mixed_001_019]
  · norm_num [mixed_001_019]
  · norm_num [mixed_001_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_019]

def mixed_001_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17378669/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1697243/20000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(19658612209052642773209/1780238182700000000000000), (1145036621882967/848621500000000), (-1167166831056026139226791/890119091350000000000000), (1145036621882967/848621500000000), (-2353992274321104921226791/1780238182700000000000000)]
    bernstein := [(47113615926382120952352321/291674223853568000000000000), (613402506993759415634069871/3645927798169600000000000000), (7969148856337952664579780369/45574097477120000000000000000), (20666193878534772149594924403/113935243692800000000000000000), (53497602430599628898265174729/284838109232000000000000000000)]
    reserve := (10095513263/62500000000) }

theorem mixed_001_020_valid : mixed_001_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_020]
  · intro i; fin_cases i <;> norm_num [mixed_001_020]
  · norm_num [mixed_001_020]
  · norm_num [mixed_001_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_020]

def mixed_001_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (18811861/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8369161/100000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(12954269949119063913043/8778412972900000000000000), (1185006088149939/836916100000000), (-5839320986794794450086957/4389206486450000000000000), (1185006088149939/836916100000000), (-11691596243538707964086957/8778412972900000000000000)]
    bernstein := [(264103190981369482436709746083/1404546075664000000000000000000), (547420567793130722633369795927/2809092151328000000000000000000), (3398275777845115843380245467489/16854552907968000000000000000000), (137668078992893016592982005391/660962859136000000000000000000), (284026349550267728010358966979/1321925718272000000000000000000)]
    reserve := (94017275601/500000000000) }

theorem mixed_001_021_valid : mixed_001_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_021]
  · intro i; fin_cases i <;> norm_num [mixed_001_021]
  · norm_num [mixed_001_021]
  · norm_num [mixed_001_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_021]

def mixed_001_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1261833/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8233003/100000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-85114001497122885053511/8635596846700000000000000), (610922227224111/411650150000000), (-5842178508393143907053511/4317798423350000000000000), (610922227224111/411650150000000), (-11599243015289164929053511/8635596846700000000000000)]
    bernstein := [(279739668186310126487183755017/1300419289856000000000000000000), (36103365111558257666917052631/162552411232000000000000000000), (19775980427494508302208915309/86355968467000000000000000000), (5091212232940435007937001899/21588992116750000000000000000), (327291505845328477274956641/1349312007296875000000000000)]
    reserve := (215114978967/1000000000000) }

theorem mixed_001_022_valid : mixed_001_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_022]
  · intro i; fin_cases i <;> norm_num [mixed_001_022]
  · norm_num [mixed_001_022]
  · norm_num [mixed_001_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_022]

def mixed_001_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (860301/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8078689/100000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-11484892126460056257429/498455111300000000000000), (1255496754111699/807868900000000), (-343788296336759314257429/249227555650000000000000), (1255496754111699/807868900000000), (-676091700547058572257429/498455111300000000000000)]
    bernstein := [(18914957637719204335994499/77883611140625000000000000), (311560148851545318614065407/1246137778250000000000000000), (1281522804391632782121316319/4984551113000000000000000000), (42125217514823336805243476859/159505635616000000000000000000), (345834960596636458573155171531/1276045084928000000000000000000)]
    reserve := (30357730851/125000000000) }

theorem mixed_001_023_valid : mixed_001_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_023]
  · intro i; fin_cases i <;> norm_num [mixed_001_023]
  · norm_num [mixed_001_023]
  · norm_num [mixed_001_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_023]

def mixed_001_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (355679/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7907263/100000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-316710299712657820801131/8293928160700000000000000), (642966360237003/395363150000000), (-5845995684886470082801131/4146964080350000000000000), (642966360237003/395363150000000), (-11375281070060282344801131/8293928160700000000000000)]
    bernstein := [(63316419345027849689255508399/233323693312000000000000000000), (84541511655674296893631070763/303320801305600000000000000000), (60724060759598289092801291477/212324560913920000000000000000), (366195732031696392814608861/1248968005376000000000000000), (37509947354744588258380773/124896800537600000000000000)]
    reserve := (135683647139/500000000000) }

theorem mixed_001_024_valid : mixed_001_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_024]
  · intro i; fin_cases i <;> norm_num [mixed_001_024]
  · norm_num [mixed_001_024]
  · norm_num [mixed_001_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_024]

def mixed_001_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (23954683/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3859927/50000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-224373922239533698935699/4048677430300000000000000), (1313146353535203/771985400000000), (-2923492182115017496935699/2024338715150000000000000), (1313146353535203/771985400000000), (-5622610441990501294935699/4048677430300000000000000)]
    bernstein := [(18334591006638448056093117/60968318950400000000000000), (187960653573170438754495471/609683189504000000000000000), (32730376526948214297491901813/103646142215680000000000000000), (335001273883739933101251705591/1036461422156800000000000000000), (3426263388417280420823494338141/10364614221568000000000000000000)]
    reserve := (300723249751/1000000000000) }

theorem mixed_001_025_valid : mixed_001_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_025]
  · intro i; fin_cases i <;> norm_num [mixed_001_025]
  · norm_num [mixed_001_025]
  · norm_num [mixed_001_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_025]

def mixed_001_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (12539659/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1879413/25000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-147638663224793269111981/1971316295700000000000000), (222859008882521/125294200000000), (-1461849513882684631111981/985658147850000000000000), (222859008882521/125294200000000), (-2776060364540575993111981/1971316295700000000000000)]
    bernstein := [(1670522742807446047587957082979/5046569716992000000000000000000), (427482237255739127791689792667/1261642429248000000000000000000), (327935811815224217180169684773/946231821936000000000000000000), (27933022056879946469937582743/78852651828000000000000000000), (7133195100383229699381553739/19713162957000000000000000000)]
    reserve := (5172209901/15625000000) }

theorem mixed_001_026_valid : mixed_001_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_026]
  · intro i; fin_cases i <;> norm_num [mixed_001_026]
  · norm_num [mixed_001_026]
  · norm_num [mixed_001_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_026]

def mixed_001_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3267003/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (912737/12500000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-92663288055956760816519/957369839300000000000000), (1680685461741/903700000000), (-730909841206824498816519/478684919650000000000000), (1680685461741/903700000000), (-1369156394357692236816519/957369839300000000000000)]
    bernstein := [(495580246525690679573276823/1367671199000000000000000000), (2026473625640590106724321333/5470684796000000000000000000), (57967556851432334861331424501/153179174288000000000000000000), (236735838225502664689345193271/612716697152000000000000000000), (966247520088043904104141285641/2450866788608000000000000000000)]
    reserve := (362353354291/1000000000000) }

theorem mixed_001_027_valid : mixed_001_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_027]
  · intro i; fin_cases i <;> norm_num [mixed_001_027]
  · norm_num [mixed_001_027]
  · norm_num [mixed_001_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_027]

def mixed_001_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (27123987/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1414771/20000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-180032909053016776556127/1483953301900000000000000), (1375723219576101/707385500000000), (-1169335100426661430556127/741976650950000000000000), (1375723219576101/707385500000000), (-2158637291800306084556127/1483953301900000000000000)]
    bernstein := [(1499852968186631902505217855153/3798920452864000000000000000000), (765798063495067791321563301267/1899460226432000000000000000000), (390775297167159436309835857513/949730113216000000000000000000), (199296118857380656720193388507/474865056608000000000000000000), (101587378285060823210708240673/237432528304000000000000000000)]
    reserve := (394810311717/1000000000000) }

theorem mixed_001_028_valid : mixed_001_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_028]
  · intro i; fin_cases i <;> norm_num [mixed_001_028]
  · norm_num [mixed_001_028]
  · norm_num [mixed_001_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_028]

def mixed_001_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 2]
    lambda := ![(33333333/100000000), (33333333/100000000), 0, 0, 0, 0, (33333333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (28042893/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1708703/25000000), (1/100000000), (1/100000000), (1/100000000), (8422667/100000000)]
    alternative := .zero
    polynomial := [(-266571696567917270336211/1792258576700000000000000), (1390417219429161/683481200000000), (-1461410735752860092336211/896129288350000000000000), (1390417219429161/683481200000000), (-2656249774937802914336211/1792258576700000000000000)]
    bernstein := [(122872486860316118120540526189/286761372272000000000000000000), (50142759787389632552025218241/114704548908800000000000000000), (20451818352461781856939431637/45881819563520000000000000000), (8337493574942095570803894057/18352727825408000000000000000), (3397250693492055739572331581/7341091130163200000000000000)]
    reserve := (428483396793/1000000000000) }

theorem mixed_001_029_valid : mixed_001_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_001_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_001_029]
  · intro i; fin_cases i <;> norm_num [mixed_001_029]
  · norm_num [mixed_001_029]
  · norm_num [mixed_001_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_001_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_001_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_001_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_001_029]

def mixedTable001 : OwnerTable where
  mode := .mixed
  owners := ![0, 0, 0, 2, 0, 2, 2]
  rows := [mixed_001_000, mixed_001_001, mixed_001_002, mixed_001_003, mixed_001_004, mixed_001_005, mixed_001_006, mixed_001_007, mixed_001_008, mixed_001_009, mixed_001_010, mixed_001_011, mixed_001_012, mixed_001_013, mixed_001_014, mixed_001_015, mixed_001_016, mixed_001_017, mixed_001_018, mixed_001_019, mixed_001_020, mixed_001_021, mixed_001_022, mixed_001_023, mixed_001_024, mixed_001_025, mixed_001_026, mixed_001_027, mixed_001_028, mixed_001_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_001_000_valid
    · exact mixed_001_001_valid
    · exact mixed_001_002_valid
    · exact mixed_001_003_valid
    · exact mixed_001_004_valid
    · exact mixed_001_005_valid
    · exact mixed_001_006_valid
    · exact mixed_001_007_valid
    · exact mixed_001_008_valid
    · exact mixed_001_009_valid
    · exact mixed_001_010_valid
    · exact mixed_001_011_valid
    · exact mixed_001_012_valid
    · exact mixed_001_013_valid
    · exact mixed_001_014_valid
    · exact mixed_001_015_valid
    · exact mixed_001_016_valid
    · exact mixed_001_017_valid
    · exact mixed_001_018_valid
    · exact mixed_001_019_valid
    · exact mixed_001_020_valid
    · exact mixed_001_021_valid
    · exact mixed_001_022_valid
    · exact mixed_001_023_valid
    · exact mixed_001_024_valid
    · exact mixed_001_025_valid
    · exact mixed_001_026_valid
    · exact mixed_001_027_valid
    · exact mixed_001_028_valid
    · exact mixed_001_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
