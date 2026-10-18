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

def quarter_030_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_030_000_valid : quarter_030_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_000]
  · intro i; fin_cases i <;> norm_num [quarter_030_000]
  · norm_num [quarter_030_000]
  · norm_num [quarter_030_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_000]

def quarter_030_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_030_001_valid : quarter_030_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_001]
  · intro i; fin_cases i <;> norm_num [quarter_030_001]
  · norm_num [quarter_030_001]
  · norm_num [quarter_030_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_001]

def quarter_030_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-382804973875870721/684552687500000000), (-39204036/10952843), (-1067357661375870721/342276343750000000), (-39204036/10952843), (-1751910348875870721/684552687500000000)]
    bernstein := [(646693971861456324660719/1752454880000000000000000), (155279285836763680907889/438113720000000000000000), (111621009402992369262377/328585290000000000000000), (8894952571565710129429/27382107500000000000000), (2121126590005779963799/6845526875000000000000)]
    reserve := (61971171211/200000000000) }

theorem quarter_030_002_valid : quarter_030_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_002]
  · intro i; fin_cases i <;> norm_num [quarter_030_002]
  · norm_num [quarter_030_002]
  · norm_num [quarter_030_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_002]

def quarter_030_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-556512809540135577/1127647700000000000), (-75237955/22552954), (-1684160509540135577/563823850000000000), (-75237955/22552954), (-2811808209540135577/1127647700000000000)]
    bernstein := [(3477032164953649209663/11276477000000000000000), (13294893098709221172331/45105908000000000000000), (152104840977384548853841/541270896000000000000000), (192793584408782748968639/721694528000000000000000), (730712026497435302482743/2886778112000000000000000)]
    reserve := (253123724147/1000000000000) }

theorem quarter_030_003_valid : quarter_030_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_003]
  · intro i; fin_cases i <;> norm_num [quarter_030_003]
  · norm_num [quarter_030_003]
  · norm_num [quarter_030_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_003]

def quarter_030_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![0, (3/100000000), (1/50000000), (1/100000000), 0, 0, (19999999/20000000)]
    cone := fun i => (![![(24999999/50000000), 0, (19999999/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17966011/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23159559/100000000)]
    alternative := .zero
    polynomial := [(-2015313824532338257/4631911800000000000), (-3593202089818567/1157977950000000), (-6647225531894102257/2315955900000000000), (-3593202089818567/1157977950000000), (-11279137239255866257/4631911800000000000)]
    bernstein := [(995172812301573076873621/3952564736000000000000000), (94512796994631703583071/395256473600000000000000), (80505043141677895269077/355730826240000000000000), (843283787993898168967/3952564736000000000000), (13967075005323793631/69751142400000000000)]
    reserve := (25030190411/125000000000) }

theorem quarter_030_004_valid : quarter_030_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_004]
  · intro i; fin_cases i <;> norm_num [quarter_030_004]
  · norm_num [quarter_030_004]
  · norm_num [quarter_030_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_004]

def quarter_030_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (68290369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-227369526439286957/593044725000000000), (-9755767/3388827), (-820414251439286957/296522362500000000), (-9755767/3388827), (-1413458976439286957/593044725000000000)]
    bernstein := [(10073437836348689809/50606483200000000000), (94768432271642857513/506064832000000000000), (7985100306579547072057/45545834880000000000000), (24779433730114407672827/151819449600000000000000), (229173926598944049100723/1518194496000000000000000)]
    reserve := (75475812619/500000000000) }

theorem quarter_030_005_valid : quarter_030_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_005]
  · intro i; fin_cases i <;> norm_num [quarter_030_005]
  · norm_num [quarter_030_005]
  · norm_num [quarter_030_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_005]

def quarter_030_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(935721/20000000), (30214263/100000000), (30214263/100000000), (30214263/100000000), 0, 0, (935721/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8949709/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3018757/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4105341/50000000), (1/100000000), (1/100000000), (314163/4000000), (1/100000000), (113391/10000000)]
    alternative := .zero
    polynomial := [(136102624518225257541698099/2407335249703884000000000000), (-79980566715535213/143675531275000000), (-703885686478421377451421901/1203667624851942000000000000), (-79980566715535213/143675531275000000), (-1543873997475068012444541901/2407335249703884000000000000)]
    bernstein := [(966823036979447668982995006088339/6162778239241943040000000000000000), (119173296656013358938165736263571/770347279905242880000000000000000), (11011997678875939936713787229933/72220057491116520000000000000000), (904038883653771216579095654983/6018338124259710000000000000000), (55634849121114990080616018731/376146132766231875000000000000)]
    reserve := (18488442481/125000000000) }

theorem quarter_030_006_valid : quarter_030_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_006]
  · intro i; fin_cases i <;> norm_num [quarter_030_006]
  · norm_num [quarter_030_006]
  · norm_num [quarter_030_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_006]

def quarter_030_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(5610497/100000000), (14796501/50000000), (14796501/50000000), (14796501/50000000), 0, 0, (5610497/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8765687/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (679633/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4064419/50000000), (1/100000000), (1/100000000), (384629/5000000), (1/100000000), (692869/50000000)]
    alternative := .zero
    polynomial := [(12802344463997503612815021569/203888479160358742400000000000), (-295800294745008020197/563221985622200000000), (-58973534258334594664381554431/101944239580179371200000000000), (-295800294745008020197/563221985622200000000), (-130749412980666692941578130431/203888479160358742400000000000)]
    bernstein := [(80080819662517832856540108431737/541578772769702909500000000000000), (54916513765287971339857725812741/376750450622402024000000000000000), (14933878431352109050821678725808239/103983124371782958624000000000000000), (6820301137811737835776018552429993/48224057679667459072000000000000000), (72654378663923268955319625703974369/521954506650518380544000000000000000)]
    reserve := (139196764733/1000000000000) }

theorem quarter_030_007_valid : quarter_030_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_007]
  · intro i; fin_cases i <;> norm_num [quarter_030_007]
  · norm_num [quarter_030_007]
  · norm_num [quarter_030_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_007]

def quarter_030_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(3266589/50000000), (28977881/100000000), (28977881/100000000), (28977881/100000000), 0, 0, (3266589/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8583483/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3687037/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8034209/100000000), (1/100000000), (1/100000000), (3766341/50000000), (1/100000000), (1640317/100000000)]
    alternative := .zero
    polynomial := [(27313381506709000148358146819227/397082306633054786184000000000000), (-323383146753896872477/658932480212650000000), (-113694750680315998475765941740773/198541153316527393092000000000000), (-323383146753896872477/658932480212650000000), (-254702882867340997099890030300773/397082306633054786184000000000000)]
    bernstein := [(141461244442725028233987652144722157627/1016530704980620252631040000000000000000), (69708757814414914233527487718482790183/508265352490310126315520000000000000000), (102995963796216184418227772575434489721/762398028735465189473280000000000000000), (16899048363419178342849073041390535103/127066338122577531578880000000000000000), (8313150039337228119911456652133191787/63533169061288765789440000000000000000)]
    reserve := (8177962553/62500000000) }

theorem quarter_030_008_valid : quarter_030_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_008]
  · intro i; fin_cases i <;> norm_num [quarter_030_008]
  · norm_num [quarter_030_008]
  · norm_num [quarter_030_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_008]

def quarter_030_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(7442389/100000000), (28371741/100000000), (28371741/100000000), (28371741/100000000), 0, 0, (7442389/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8403939/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (970041/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1585453/20000000), (1/100000000), (1/100000000), (7375119/100000000), (1/100000000), (473683/25000000)]
    alternative := .zero
    polynomial := [(109833606842840390992591063503/1476994694152399861600000000000), (-21285352026195306501/46937633337437500000), (-419139193014002493560653016497/738497347076199930800000000000), (-21285352026195306501/46937633337437500000), (-948111992870845378113897096497/1476994694152399861600000000000)]
    bernstein := [(30915421596261239786822088580661343/236319151064383977856000000000000000), (12185881568961797257864371529876101/94527660425753591142400000000000000), (14401394454846139020175818010644869/113433192510904309370880000000000000), (377983514817993244739598427155817/3024885133624114916556800000000000), (29742850592157009503142172623527/241990810689929193324544000000000)]
    reserve := (61454504217/500000000000) }

theorem quarter_030_009_valid : quarter_030_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_009]
  · intro i; fin_cases i <;> norm_num [quarter_030_009]
  · norm_num [quarter_030_009]
  · norm_num [quarter_030_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_009]

def quarter_030_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(833423/10000000), (1388859/5000000), (1388859/5000000), (1388859/5000000), 0, 0, (833423/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4113913/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1986941/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7808593/100000000), (1/100000000), (1/100000000), (1444113/20000000), (1/100000000), (134129/6250000)]
    alternative := .zero
    polynomial := [(1348903966689830965024467071/16994431642008249000000000000), (-6927634207460766311/16757740327952000000), (-4788024920725500065186432929/8497215821004124500000000000), (-6927634207460766311/16757740327952000000), (-10924953808140831095397332929/16994431642008249000000000000)]
    bernstein := [(2342635882892027603825514661147/19062209503090015764480000000000), (20840235111717622086058097424073/172089391347340420096000000000000), (3463302101258152466462986941995653/29040084789863695891200000000000000), (157795657326414175774186117992221/1344448369901097032000000000000000), (1745845958652434718486086476298119/15125044161387341610000000000000000)]
    reserve := (28856873739/250000000000) }

theorem quarter_030_010_valid : quarter_030_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_010]
  · intro i; fin_cases i <;> norm_num [quarter_030_010]
  · norm_num [quarter_030_010]
  · norm_num [quarter_030_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_010]

def quarter_030_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(9205173/100000000), (27196551/100000000), (27196551/100000000), (27196551/100000000), 0, 0, (9205173/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8055839/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1983053/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7678877/100000000), (1/100000000), (1/100000000), (7069633/100000000), (1/100000000), (597863/25000000)]
    alternative := .zero
    polynomial := [(10862525465472546132079291248453/129824377453652578732000000000000), (-340252492600891859319/918183287970200000000), (-36395786099924293496826048431547/64912188726826289366000000000000), (-340252492600891859319/918183287970200000000), (-83654097665321133125731388111547/129824377453652578732000000000000)]
    bernstein := [(149852740387550404033375761935509053/1298243774536525787320000000000000000), (590746073970238233888235640349252459/5192975098146103149280000000000000000), (2327268444618438961080660294816078377/20771900392584412597120000000000000000), (9161948550738222309555883648293163431/83087601570337650388480000000000000000), (36042015871511835810861753212877291093/332350406281350601553920000000000000000)]
    reserve := (27111457659/250000000000) }

theorem quarter_030_011_valid : quarter_030_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_011]
  · intro i; fin_cases i <;> norm_num [quarter_030_011]
  · norm_num [quarter_030_011]
  · norm_num [quarter_030_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_011]

def quarter_030_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(10052073/100000000), (26631951/100000000), (26631951/100000000), (26631951/100000000), 0, 0, (10052073/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (39443/500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (771267/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7538879/100000000), (1/100000000), (1/100000000), (6922867/100000000), (1/100000000), (131407/5000000)]
    alternative := .zero
    polynomial := [(2254542431199906134156150209/25880066482615633400000000000), (-128799710912817839769/396264589101200000000), (-7239307368498768650051865791/12940033241307816700000000000), (-128799710912817839769/396264589101200000000), (-16733157168197443434259881791/25880066482615633400000000000)]
    bernstein := [(380855574774716234895193368919628837/3511407420361289139712000000000000000), (187733759514824027752121607245548579/1755703710180644569856000000000000000), (277420200283782288000448921218211679/2633555565270966854784000000000000000), (45516502634568690543158214643971731/438925927545161142464000000000000000), (22386256032655366627171810758276677/219462963772580571232000000000000000)]
    reserve := (102004710261/1000000000000) }

theorem quarter_030_012_valid : quarter_030_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_012]
  · intro i; fin_cases i <;> norm_num [quarter_030_012]
  · norm_num [quarter_030_012]
  · norm_num [quarter_030_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_012]

def quarter_030_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(434887/4000000), (26085217/100000000), (26085217/100000000), (26085217/100000000), 0, 0, (434887/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1931663/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3645611/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7389419/100000000), (1/100000000), (1/100000000), (3390373/50000000), (1/100000000), (570707/20000000)]
    alternative := .zero
    polynomial := [(1280644061311732823248286162159/14297857788944533909000000000000), (-7295971498758687857/26357457182706250000), (-4003471289351031236073767117841/7148928894472266954500000000000), (-7295971498758687857/26357457182706250000), (-9287586640013795295395820397841/14297857788944533909000000000000)]
    bernstein := [(233432303515092593796838784625969359/2287657246231125425440000000000000000), (460500375848086511085964338813072959/4575314492462250850880000000000000000), (129681254753866748873121657100462537/1307232712132071671680000000000000000), (1788056116340923555018482564761903759/18301257969849003403520000000000000000), (3519084015388421469669565017399950959/36602515939698006807040000000000000000)]
    reserve := (48071613727/500000000000) }

theorem quarter_030_013_valid : quarter_030_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_013]
  · intro i; fin_cases i <;> norm_num [quarter_030_013]
  · norm_num [quarter_030_013]
  · norm_num [quarter_030_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_013]

def quarter_030_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(11663117/100000000), (12778961/50000000), (12778961/50000000), (12778961/50000000), 0, 0, (11663117/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (236577/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (417057/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3615677/50000000), (1/100000000), (1/100000000), (3321839/50000000), (1/100000000), (766313/25000000)]
    alternative := .zero
    polynomial := [(104579371586815230343382290001/1150494143817826117375000000000), (-4814626961079679653/21313386837700000000), (-323646502376333917756952236249/575247071908913058687500000000), (-4814626961079679653/21313386837700000000), (-751872376339483065857286762499/1150494143817826117375000000000)]
    bernstein := [(283330318536569329992452346853350701/2945265008173634860480000000000000000), (2796828199640988927229657568879491/29452650081736348604800000000000000), (517250917333858584659848860093551/5522371890325565363400000000000000), (1699259245754913373709734673891/18407906301085217878000000000000), (104579371586815230343382290001/1150494143817826117375000000000)]
    reserve := (45449762673/500000000000) }

theorem quarter_030_014_valid : quarter_030_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_014]
  · intro i; fin_cases i <;> norm_num [quarter_030_014]
  · norm_num [quarter_030_014]
  · norm_num [quarter_030_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_014]

def quarter_030_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(781457/6250000), (781181/3125000), (781181/3125000), (781181/3125000), 0, 0, (781457/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1851137/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1475871/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (220703/3125000), (1/100000000), (1/100000000), (3249037/50000000), (1/100000000), (1641127/50000000)]
    alternative := .zero
    polynomial := [(53510653838602105944117158727/588403284861051698500000000000), (328347010590542463/565940081689062500), (-167147073956557147004134281273/294201642430525849250000000000), (328347010590542463/565940081689062500), (-387804801751716399952385721273/588403284861051698500000000000)]
    bernstein := [(53510653838602105944117158727/588403284861051698500000000000), (55644277011098234568833420727/588403284861051698500000000000), (92388924602432128727344780936109/941445255777682717600000000000000), (95693423918960725890846093543927/941445255777682717600000000000000), (158313971860022988970419451212125127/1506312409244292348160000000000000000)]
    reserve := (90942139881/1000000000000) }

theorem quarter_030_015_valid : quarter_030_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_015]
  · intro i; fin_cases i <;> norm_num [quarter_030_015]
  · norm_num [quarter_030_015]
  · norm_num [quarter_030_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_015]

def quarter_030_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(13373881/100000000), (6104353/25000000), (6104353/25000000), (6104353/25000000), 0, 0, (13373881/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1446527/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2481207/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6884941/100000000), (1/100000000), (1/100000000), (6347207/100000000), (1/100000000), (437241/12500000)]
    alternative := .zero
    polynomial := [(195181096425838691863245304681/2183713761176340304800000000000), (14837803989143906549/22936217049760000000), (-630072569341632319400815759319/1091856880588170152400000000000), (14837803989143906549/22936217049760000000), (-1455326235109103330664876823319/2183713761176340304800000000000)]
    bernstein := [(588113895280766674470040097142515881/5590307228611431180288000000000000000), (101624928570379216541725170460022027/931717871435238530048000000000000000), (473307005338427475746460547016641243/4192730421458573385216000000000000000), (27171078076392385371693617743679627/232929467858809632512000000000000000), (42053149231771787696183516017581481/349394201788214448768000000000000000)]
    reserve := (105202428279/1000000000000) }

theorem quarter_030_016_valid : quarter_030_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_016]
  · intro i; fin_cases i <;> norm_num [quarter_030_016]
  · norm_num [quarter_030_016]
  · norm_num [quarter_030_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_016]

def quarter_030_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(14189331/100000000), (23873779/100000000), (23873779/100000000), (23873779/100000000), 0, 0, (14189331/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7071607/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (382001/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (670299/10000000), (1/100000000), (1/100000000), (1551473/25000000), (1/100000000), (115261/3125000)]
    alternative := .zero
    polynomial := [(23586940555886586041648011267/273978901046894736000000000000), (294897171840083947693/412049776208000000000), (-80697949926384108906241588733/136989450523447368000000000000), (294897171840083947693/412049776208000000000), (-184982840408654803854131188733/273978901046894736000000000000)]
    bernstein := [(5281745931483650472685289978164867/43836624167503157760000000000000000), (993284837992295521815847722623891/7970295303182392320000000000000000), (67705695772971675392441806213745809/526039490010037893120000000000000000), (604578646892249077887810645034717/4554454458961367040000000000000000), (95903023388561236300766812213202227/701385986680050524160000000000000000)]
    reserve := (60243529603/500000000000) }

theorem quarter_030_017_valid : quarter_030_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_017]
  · intro i; fin_cases i <;> norm_num [quarter_030_017]
  · norm_num [quarter_030_017]
  · norm_num [quarter_030_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_017]

def quarter_030_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(14950927/100000000), (23366049/100000000), (23366049/100000000), (23366049/100000000), 0, 0, (14950927/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6921213/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (249727/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (203669/3125000), (1/100000000), (1/100000000), (6073909/100000000), (1/100000000), (3852709/100000000)]
    alternative := .zero
    polynomial := [(154384563216899646497338385297/1906423622837330315600000000000), (395015680696837745007/502193529165440000000), (-576099318804010729571837870703/953211811418665157800000000000), (395015680696837745007/502193529165440000000), (-1306583200824921105641014126703/1906423622837330315600000000000)]
    bernstein := [(668061224265753466633870059694835657/4880444474463565607936000000000000000), (344829221419693568024397947406398263/2440222237231782803968000000000000000), (5554895488616127244458928217665531/38128472456746606312000000000000000), (22880526224521741590717570267574957/152513889826986425248000000000000000), (2941870554649185361357812506346447/19064236228373303156000000000000000)]
    reserve := (34221331057/250000000000) }

theorem quarter_030_018_valid : quarter_030_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_018]
  · intro i; fin_cases i <;> norm_num [quarter_030_018]
  · norm_num [quarter_030_018]
  · norm_num [quarter_030_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_018]

def quarter_030_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(7830059/50000000), (4578651/20000000), (4578651/20000000), (4578651/20000000), 0, 0, (7830059/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6781167/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (253997/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3164447/50000000), (1/100000000), (1/100000000), (5951009/100000000), (1/100000000), (798107/20000000)]
    alternative := .zero
    polynomial := [(4446250382593143372810742134187/60118694973160381844000000000000), (2099919460535570663/2442521568500000000), (-18731534333141628527730855985813/30059347486580190922000000000000), (2099919460535570663/2442521568500000000), (-41909319048876400428272454105813/60118694973160381844000000000000)]
    bernstein := [(92877250076981998674939546477721587/601186949731603818440000000000000000), (76580621734371882181607938138507847/480949559785283054752000000000000000), (189213720582414666977465604185683469/1154278943484679331404800000000000000), (10378006644565712431688797724424511/61561543652516231008256000000000000), (131227903363421338536313612515631/757680537261738227793920000000000)]
    reserve := (77244898711/500000000000) }

theorem quarter_030_019_valid : quarter_030_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_019]
  · intro i; fin_cases i <;> norm_num [quarter_030_019]
  · norm_num [quarter_030_019]
  · norm_num [quarter_030_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_019]

def quarter_030_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(509887/3125000), (350871/1562500), (350871/1562500), (350871/1562500), 0, 0, (509887/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6651573/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3069061/50000000), (1/100000000), (1/100000000), (5837279/100000000), (1/100000000), (515353/12500000)]
    alternative := .zero
    polynomial := [(2455622476945294387242235401403/36930124500578066828000000000000), (4427347291339/4795407812500), (-11862972664978194423235464438597/18465062250289033414000000000000), (4427347291339/4795407812500), (-26181567806901683233713164278597/36930124500578066828000000000000)]
    bernstein := [(1049732764892774795067764999733107/6050631598174710469099520000000000), (13499999922484773618256973190100957/75632894977183880863744000000000000), (24777647800810625571803996508699589/135058741030685501542400000000000000), (445258629309261951437711971789493801/2363527968036996276992000000000000000), (1142072431592733740320308391643215243/5908819920092490692480000000000000000)]
    reserve := (43372859009/250000000000) }

theorem quarter_030_020_valid : quarter_030_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_020]
  · intro i; fin_cases i <;> norm_num [quarter_030_020]
  · norm_num [quarter_030_020]
  · norm_num [quarter_030_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_020]

def quarter_030_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(528129/3125000), (11033291/50000000), (11033291/50000000), (11033291/50000000), 0, 0, (528129/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (65363/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5945853/100000000), (1/100000000), (1/100000000), (2868059/50000000), (1/100000000), (170813/4000000)]
    alternative := .zero
    polynomial := [(3533037496338631664357837881/58257677221935457020000000000), (747264861798/774199609375), (-19168062639469014259800204119/29128838610967728510000000000), (747264861798/774199609375), (-41869162775276660183958246119/58257677221935457020000000000)]
    bernstein := [(1803790017704647378024373140471561/9321228355509673123200000000000000), (3703500793483046972452196864731109/18642456711019346246400000000000000), (22792792394902835842289127007605763/111854740266116077478400000000000000), (15574050956492003475182109846960349/74569826844077384985600000000000000), (31901411731733710856564008180441081/149139653688154769971200000000000000)]
    reserve := (48378549181/250000000000) }

theorem quarter_030_021_valid : quarter_030_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_021]
  · intro i; fin_cases i <;> norm_num [quarter_030_021]
  · norm_num [quarter_030_021]
  · norm_num [quarter_030_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_021]

def quarter_030_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(17412691/100000000), (21724873/100000000), (21724873/100000000), (21724873/100000000), 0, 0, (17412691/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6435083/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5752223/100000000), (1/100000000), (1/100000000), (1411823/25000000), (1/100000000), (4399839/100000000)]
    alternative := .zero
    polynomial := [(30916910576617686459014414658167/571705979563034605296000000000000), (578611863887429/575222300000000), (-192834883066691902530854974781833/285852989781517302648000000000000), (578611863887429/575222300000000), (-416586676710001491520724364221833/571705979563034605296000000000000)]
    bernstein := [(313434104134179740061987119603237084567/1463567307681368589557760000000000000000), (4460805852412919450668037037935139809/20327323717796785966080000000000000000), (3854053020356139728243416361135121881/17151179386891038158880000000000000000), (36516975679867100459265251680471933/158807216545287390360000000000000000), (21006116321676123181069402322110223/89329059306724157077500000000000000)]
    reserve := (214157628753/1000000000000) }

theorem quarter_030_022_valid : quarter_030_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_022]
  · intro i; fin_cases i <;> norm_num [quarter_030_022]
  · norm_num [quarter_030_022]
  · norm_num [quarter_030_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_022]

def quarter_030_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(8930773/50000000), (5356409/25000000), (5356409/25000000), (5356409/25000000), 0, 0, (8930773/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6346447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2778653/50000000), (1/100000000), (1/100000000), (5569507/100000000), (1/100000000), (564157/12500000)]
    alternative := .zero
    polynomial := [(1633133836425506827420524341831/34922959622429972588000000000000), (36326196031463/34733162500000), (-12087112870225069325777145818169/17461479811214986294000000000000), (36326196031463/34733162500000), (-25807359576875645478974815978169/34922959622429972588000000000000)]
    bernstein := [(1284689102107282203192772806489439/5456712441004683216875000000000000), (83123380479239354234872769408359/345088533818477990000000000000000), (86012814166438059847900751510145459/349229596224299725880000000000000000), (255699148117077950664127963165660309/1015940643561599202560000000000000000), (22981807231347282135989452543039588391/89402776633420729825280000000000000000)]
    reserve := (117716401221/500000000000) }

theorem quarter_030_023_valid : quarter_030_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_023]
  · intro i; fin_cases i <;> norm_num [quarter_030_023]
  · norm_num [quarter_030_023]
  · norm_num [quarter_030_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_023]

def quarter_030_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(18253387/100000000), (21164409/100000000), (21164409/100000000), (21164409/100000000), 0, 0, (18253387/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6269069/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5361237/100000000), (1/100000000), (1/100000000), (2750801/50000000), (1/100000000), (2306133/50000000)]
    alternative := .zero
    polynomial := [(389414610345893501233706863589/10077081082107120984000000000000), (9238787549567/8509900000000), (-3582748653353683949712605776411/5038540541053560492000000000000), (9238787549567/8509900000000), (-7554911917053261400658918416411/10077081082107120984000000000000)]
    bernstein := [(6639256838086514668023461298647236229/25797327570194229719040000000000000000), (678378561974517120724568363597095421/2579732757019422971904000000000000000), (4833321551389993044375413035612877/17998135514088997478400000000000000), (7071224057624545374197163076931197/25797327570194229719040000000000000), (721420897452649442285797278777221/2579732757019422971904000000000000)]
    reserve := (8042568581/31250000000) }

theorem quarter_030_024_valid : quarter_030_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_024]
  · intro i; fin_cases i <;> norm_num [quarter_030_024]
  · norm_num [quarter_030_024]
  · norm_num [quarter_030_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_024]

def quarter_030_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(1162139/6250000), (654287/3125000), (654287/3125000), (654287/3125000), 0, 0, (1162139/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6201763/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2582103/50000000), (1/100000000), (1/100000000), (680317/12500000), (1/100000000), (4698389/100000000)]
    alternative := .zero
    polynomial := [(1565306677821116864785175745769/52821877135480481529600000000000), (9083742117461/8069071875000), (-19315925085864385049045641022231/26410938567740240764800000000000), (9083742117461/8069071875000), (-40197156849549886962876457790231/52821877135480481529600000000000)]
    bernstein := [(3785972346416295277474997720767241/13522400546683003271577600000000000), (12880096635966792339411693420914161/45074668488943344238592000000000000), (1182552829035725496227163521937034291/4056720164004900981473280000000000000), (1339810977124335524696228182843037593/4507466848894334423859200000000000000), (13656049139352289822139352840199128243/45074668488943344238592000000000000000)]
    reserve := (34997228611/125000000000) }

theorem quarter_030_025_valid : quarter_030_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_025]
  · intro i; fin_cases i <;> norm_num [quarter_030_025]
  · norm_num [quarter_030_025]
  · norm_num [quarter_030_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_025]

def quarter_030_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(4722367/25000000), (10370177/50000000), (10370177/50000000), (10370177/50000000), 0, 0, (4722367/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6143461/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1241611/25000000), (1/100000000), (1/100000000), (5391371/100000000), (1/100000000), (4772991/100000000)]
    alternative := .zero
    polynomial := [(501648202554358475334172969847/25560266184203651896800000000000), (72425152901907/62080550000000), (-9627839788971740888867290726153/12780133092101825948400000000000), (72425152901907/62080550000000), (-19757327780497840253068754422153/25560266184203651896800000000000)]
    bernstein := [(19847512742918308379120485228394816327/65434281431561348855808000000000000000), (5059280258692405707724082950849699471/16358570357890337213952000000000000000), (3867330771591299592130985746659773249/12268927768417752910464000000000000000), (328336294495244180277057016333444859/1022410647368146075872000000000000000), (83595540385520803317811098455840207/255602661842036518968000000000000000)]
    reserve := (37914974209/125000000000) }

theorem quarter_030_026_valid : quarter_030_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_026]
  · intro i; fin_cases i <;> norm_num [quarter_030_026]
  · norm_num [quarter_030_026]
  · norm_num [quarter_030_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_026]

def quarter_030_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(6501307/20000000), (34986931/100000000), 0, 0, 0, 0, (6501307/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (34986931/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4052113/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (8213751/100000000)]
    alternative := .zero
    polynomial := [(-463918790054953419789217/2560234400451000000000000), (332836901865581/162084520000000), (-2191909724643652951449217/1280117200225500000000000), (332836901865581/162084520000000), (-3919900659232352483109217/2560234400451000000000000)]
    bernstein := [(8289506784387318438679642823/25602344004510000000000000000), (34063836173092410896230419833/102409376018040000000000000000), (59935328067458191449002317847/175558930316640000000000000000), (573654867538029009598957998253/1638550016288640000000000000000), (2351188797105673705787324579663/6554200065154560000000000000000)]
    reserve := (323779212673/1000000000000) }

theorem quarter_030_027_valid : quarter_030_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_027]
  · intro i; fin_cases i <;> norm_num [quarter_030_027]
  · norm_num [quarter_030_027]
  · norm_num [quarter_030_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_027]

def quarter_030_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(8152903/25000000), (1391071/4000000), 0, 0, 0, 0, (8152903/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1391071/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1936167/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4120151/50000000)]
    alternative := .zero
    polynomial := [(-63626214572170840919407/319092016048680000000000), (409814727170233/193616700000000), (-278657177233157427711007/159546008024340000000000), (409814727170233/193616700000000), (-493688139894144014502607/319092016048680000000000)]
    bernstein := [(97868427894810665373803917291/272291853694873600000000000000), (50159207900194213027887150449/136145926847436800000000000000), (231186573383320357122887205899/612656670813465600000000000000), (13145257127609617787061002729/34036481711859200000000000000), (20166706838503104561163998193/51054722567788800000000000000)]
    reserve := (14376989479/40000000000) }

theorem quarter_030_028_valid : quarter_030_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_028]
  · intro i; fin_cases i <;> norm_num [quarter_030_028]
  · norm_num [quarter_030_028]
  · norm_num [quarter_030_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_028]

def quarter_030_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 0, 0, 2, 2]
    lambda := ![(204409/625000), (108091/312500), 0, 0, 0, 0, (204409/625000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (108091/312500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1847263/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (8264011/100000000)]
    alternative := .zero
    polynomial := [(-210248425536991627959309/954112609493312500000000), (1261388111327/577269687500), (-852314308000034504259309/477056304746656250000000), (1261388111327/577269687500), (-1494380190463077380559309/954112609493312500000000)]
    bernstein := [(60413626560486385418306746291/152658017518930000000000000000), (24726039430512713190742916879/61063207007572000000000000000), (10113014143376982046097628203/24425282803028800000000000000), (4133589852988557062619650183/9770113121211520000000000000), (1688525050394286905135442339/3908045248484608000000000000)]
    reserve := (98936216293/250000000000) }

theorem quarter_030_029_valid : quarter_030_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_030_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_030_029]
  · intro i; fin_cases i <;> norm_num [quarter_030_029]
  · norm_num [quarter_030_029]
  · norm_num [quarter_030_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_030_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_030_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_030_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_030_029]

def quarterTable030 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 0, 0, 2, 2]
  rows := [quarter_030_000, quarter_030_001, quarter_030_002, quarter_030_003, quarter_030_004, quarter_030_005, quarter_030_006, quarter_030_007, quarter_030_008, quarter_030_009, quarter_030_010, quarter_030_011, quarter_030_012, quarter_030_013, quarter_030_014, quarter_030_015, quarter_030_016, quarter_030_017, quarter_030_018, quarter_030_019, quarter_030_020, quarter_030_021, quarter_030_022, quarter_030_023, quarter_030_024, quarter_030_025, quarter_030_026, quarter_030_027, quarter_030_028, quarter_030_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_030_000_valid
    · exact quarter_030_001_valid
    · exact quarter_030_002_valid
    · exact quarter_030_003_valid
    · exact quarter_030_004_valid
    · exact quarter_030_005_valid
    · exact quarter_030_006_valid
    · exact quarter_030_007_valid
    · exact quarter_030_008_valid
    · exact quarter_030_009_valid
    · exact quarter_030_010_valid
    · exact quarter_030_011_valid
    · exact quarter_030_012_valid
    · exact quarter_030_013_valid
    · exact quarter_030_014_valid
    · exact quarter_030_015_valid
    · exact quarter_030_016_valid
    · exact quarter_030_017_valid
    · exact quarter_030_018_valid
    · exact quarter_030_019_valid
    · exact quarter_030_020_valid
    · exact quarter_030_021_valid
    · exact quarter_030_022_valid
    · exact quarter_030_023_valid
    · exact quarter_030_024_valid
    · exact quarter_030_025_valid
    · exact quarter_030_026_valid
    · exact quarter_030_027_valid
    · exact quarter_030_028_valid
    · exact quarter_030_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
