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

def quarter_026_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_026_000_valid : quarter_026_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_000]
  · intro i; fin_cases i <;> norm_num [quarter_026_000]
  · norm_num [quarter_026_000]
  · norm_num [quarter_026_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_000]

def quarter_026_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_026_001_valid : quarter_026_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_001]
  · intro i; fin_cases i <;> norm_num [quarter_026_001]
  · norm_num [quarter_026_001]
  · norm_num [quarter_026_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_001]

def quarter_026_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-382804973875870721/684552687500000000), (-39204036/10952843), (-1067357661375870721/342276343750000000), (-39204036/10952843), (-1751910348875870721/684552687500000000)]
    bernstein := [(646693971861456324660719/1752454880000000000000000), (155279285836763680907889/438113720000000000000000), (111621009402992369262377/328585290000000000000000), (8894952571565710129429/27382107500000000000000), (2121126590005779963799/6845526875000000000000)]
    reserve := (61971171211/200000000000) }

theorem quarter_026_002_valid : quarter_026_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_002]
  · intro i; fin_cases i <;> norm_num [quarter_026_002]
  · norm_num [quarter_026_002]
  · norm_num [quarter_026_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_002]

def quarter_026_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-556512809540135577/1127647700000000000), (-75237955/22552954), (-1684160509540135577/563823850000000000), (-75237955/22552954), (-2811808209540135577/1127647700000000000)]
    bernstein := [(3477032164953649209663/11276477000000000000000), (13294893098709221172331/45105908000000000000000), (152104840977384548853841/541270896000000000000000), (192793584408782748968639/721694528000000000000000), (730712026497435302482743/2886778112000000000000000)]
    reserve := (253123724147/1000000000000) }

theorem quarter_026_003_valid : quarter_026_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_003]
  · intro i; fin_cases i <;> norm_num [quarter_026_003]
  · norm_num [quarter_026_003]
  · norm_num [quarter_026_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_003]

def quarter_026_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![0, (3/100000000), (1/50000000), (1/100000000), 0, 0, (19999999/20000000)]
    cone := fun i => (![![(24999999/50000000), 0, (19999999/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17966011/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23159559/100000000)]
    alternative := .zero
    polynomial := [(-2015313824532338257/4631911800000000000), (-3593202089818567/1157977950000000), (-6647225531894102257/2315955900000000000), (-3593202089818567/1157977950000000), (-11279137239255866257/4631911800000000000)]
    bernstein := [(995172812301573076873621/3952564736000000000000000), (94512796994631703583071/395256473600000000000000), (80505043141677895269077/355730826240000000000000), (843283787993898168967/3952564736000000000000), (13967075005323793631/69751142400000000000)]
    reserve := (25030190411/125000000000) }

theorem quarter_026_004_valid : quarter_026_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_004]
  · intro i; fin_cases i <;> norm_num [quarter_026_004]
  · norm_num [quarter_026_004]
  · norm_num [quarter_026_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_004]

def quarter_026_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(307139/12500000), (196531/781250), (196531/781250), (196531/781250), (1226117/12500000), (1226117/12500000), (307139/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2119809/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (833889/12500000), (1/100000000), (1/100000000), (3411269/50000000), (1/100000000), (196527/6250000)]
    alternative := .zero
    polynomial := [(16108958905288400301632633321/186348191608991769000000000000), (-346175659483388183/780389064300000000), (-9401948473476000261848448893/31058031934831961500000000000), (-346175659483388183/780389064300000000), (-665327061891233044703883731/1709616436779741000000000000)]
    bernstein := [(8769861664325123518706700229769/47705137051901892864000000000000), (28883945362125470299024976420411/159017123506339642880000000000000), (855992929231099139002075055518793/4770513705190189286400000000000000), (2818029524371406015793230481466523/15901712350633964288000000000000000), (83476440567513900750773466488622281/477051370519018928640000000000000000)]
    reserve := (34996835027/200000000000) }

theorem quarter_026_005_valid : quarter_026_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_005]
  · intro i; fin_cases i <;> norm_num [quarter_026_005]
  · norm_num [quarter_026_005]
  · norm_num [quarter_026_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_005]

def quarter_026_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(402073/12500000), (24680757/100000000), (24680757/100000000), (24680757/100000000), (9762281/100000000), (9762281/100000000), (402073/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2312443/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6625289/100000000), (1/100000000), (1/100000000), (3353231/50000000), (1/100000000), (3328921/100000000)]
    alternative := .zero
    polynomial := [(843480755234826356487934606927/9244465406172058629875000000000), (-461477936850033241177/1102753184158450000000), (-1299471221642158021889145181823/4622232703086029314937500000000), (-461477936850033241177/1102753184158450000000), (-3442423198519142400266224970573/9244465406172058629875000000000)]
    bernstein := [(4141027243033619045283041779314968947/23665831439800470092480000000000000000), (255684422455579972629125611604265179/1479114464987529380780000000000000000), (6764395206869361471405894007535287/39619137455023108413750000000000000), (30441005490351648321385141372803/180555964964298020114746093750000), (240419544482787729824355833385663/1444447719714384160917968750000000)]
    reserve := (33288784523/200000000000) }

theorem quarter_026_006_valid : quarter_026_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_006]
  · intro i; fin_cases i <;> norm_num [quarter_026_006]
  · norm_num [quarter_026_006]
  · norm_num [quarter_026_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_006]

def quarter_026_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(496679/12500000), (24204737/100000000), (24204737/100000000), (24204737/100000000), (9719463/100000000), (9719463/100000000), (496679/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4944909/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (262717/4000000), (1/100000000), (1/100000000), (3295361/50000000), (1/100000000), (703907/20000000)]
    alternative := .zero
    polynomial := [(7287523377678315166337585957/76175703000644394875000000000), (-90958936220907483671/231160419148750000000), (-9998040139160734594985703793/38087851500322197437500000000), (-90958936220907483671/231160419148750000000), (-27283603655999784356308993543/76175703000644394875000000000)]
    bernstein := [(152387873148945523975452885441/915573353373129746093750000000), (15655372744628206362744481530831/95219628750805493593750000000000), (371071011633341097996949609693601/2285271090019331846250000000000000), (977027663724314074045788107928219/6094056240051551590000000000000000), (30862571363091964784661453067412857/195009799681649650880000000000000000)]
    reserve := (15826164333/100000000000) }

theorem quarter_026_007_valid : quarter_026_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_007]
  · intro i; fin_cases i <;> norm_num [quarter_026_007]
  · norm_num [quarter_026_007]
  · norm_num [quarter_026_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_007]

def quarter_026_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(4724519/100000000), (23730889/100000000), (23730889/100000000), (23730889/100000000), (9679149/100000000), (9679149/100000000), (4724519/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5194063/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3249729/50000000), (1/100000000), (1/100000000), (6475913/100000000), (1/100000000), (928447/25000000)]
    alternative := .zero
    polynomial := [(74945697304009107897640940543/751505080451135881500000000000), (-12696115190408852149/34482298752720000000), (-602096692560641254830793770533/2442391511466191614875000000000), (-12696115190408852149/34482298752720000000), (-3382680835194683421992507309191/9769566045864766459500000000000)]
    bernstein := [(439788506360332532898631600993530401/2778898786379311348480000000000000000), (50126959244651633736807646822970549/320642167659151309440000000000000000), (2896053516060986717697957814872403607/18757566808060351602240000000000000000), (476573733277398299225633255009844551/3126261134676725267040000000000000000), (235215167549770848046842565540845329/1563130567338362633520000000000000000)]
    reserve := (6019079211/40000000000) }

theorem quarter_026_008_valid : quarter_026_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_008]
  · intro i; fin_cases i <;> norm_num [quarter_026_008]
  · norm_num [quarter_026_008]
  · norm_num [quarter_026_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_008]

def quarter_026_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(5466947/100000000), (4652403/20000000), (4652403/20000000), (4652403/20000000), (9640031/100000000), (9640031/100000000), (5466947/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1073557/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (256817/4000000), (1/100000000), (1/100000000), (6362579/100000000), (1/100000000), (3909147/100000000)]
    alternative := .zero
    polynomial := [(12008857731844116077638648939/116138515015261642200000000000), (-7808664555363622009/22816713752250000000), (-4509289904818007859589124687/19356419169210273700000000000), (-7808664555363622009/22816713752250000000), (-39064597160752163235173397061/116138515015261642200000000000)]
    bernstein := [(75573886782096289581025466653807/502220605471401696000000000000000), (368326455132950999763893719639171/2477621653658915033600000000000000), (145515855530310229030388047096033/991048661463566013440000000000000), (11495019740277298706651712908287/79283892917085281075200000000000), (2723435172724440579047416502131/19028134300100467458048000000000)]
    reserve := (143126757977/1000000000000) }

theorem quarter_026_009_valid : quarter_026_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_009]
  · intro i; fin_cases i <;> norm_num [quarter_026_009]
  · norm_num [quarter_026_009]
  · norm_num [quarter_026_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_009]

def quarter_026_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(6198069/100000000), (22800717/100000000), (22800717/100000000), (22800717/100000000), (1200107/12500000), (1200107/12500000), (6198069/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1365659/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3165723/50000000), (1/100000000), (1/100000000), (6251209/100000000), (1/100000000), (4103081/100000000)]
    alternative := .zero
    polynomial := [(10128111213732127840369029469/94968790401112115400000000000), (-2022650878668888767/6414428588920000000), (-10525048219306782343589126531/47484395200556057700000000000), (-2022650878668888767/6414428588920000000), (-31178207652345692527547282531/94968790401112115400000000000)]
    bernstein := [(2227138393463186329409576601061/15559686619318208987136000000000), (1528245943974936891517411785573/10805337930082089574400000000000), (254764739261365169342189979071203/1823400775701352615680000000000000), (11648676497105439898105907806821/84416702578766324800000000000000), (129390735231394193930773333751269/949687904011121154000000000000000)]
    reserve := (27249106719/200000000000) }

theorem quarter_026_010_valid : quarter_026_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_010]
  · intro i; fin_cases i <;> norm_num [quarter_026_010]
  · norm_num [quarter_026_010]
  · norm_num [quarter_026_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_010]

def quarter_026_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(6915497/100000000), (22349377/100000000), (22349377/100000000), (22349377/100000000), (4780219/50000000), (4780219/50000000), (6915497/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (342271/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6233209/100000000), (1/100000000), (1/100000000), (3071119/50000000), (1/100000000), (4293103/100000000)]
    alternative := .zero
    polynomial := [(8991340326196025583986861226163/82182555576048062713000000000000), (-768662258683300126679/2675980825752700000000), (-8731090797253248984319897863837/41091277788024031356500000000000), (-768662258683300126679/2675980825752700000000), (-26453521920702523552626656953837/82182555576048062713000000000000)]
    bernstein := [(111983329579563403337089472422008763/821825555760480627130000000000000000), (442754198756794755915845825343797589/3287302223041922508520000000000000000), (1750100859562875709677059068269208767/13149208892167690034080000000000000000), (6915909304710658118311344407298710601/52596835568670760136320000000000000000), (27322182413183767321621913684256313603/210387342274683040545280000000000000000)]
    reserve := (129866094213/1000000000000) }

theorem quarter_026_011_valid : quarter_026_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_011]
  · intro i; fin_cases i <;> norm_num [quarter_026_011]
  · norm_num [quarter_026_011]
  · norm_num [quarter_026_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_011]

def quarter_026_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(3808551/50000000), (171173/781250), (171173/781250), (171173/781250), (9517683/100000000), (9517683/100000000), (3808551/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2703889/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3063223/50000000), (1/100000000), (1/100000000), (3018021/50000000), (1/100000000), (4476817/100000000)]
    alternative := .zero
    polynomial := [(2309699776920338039962132631903/20693798592629631505500000000000), (-88384011864313696337/342837220029775000000), (-2125041696990677735861048703097/10346899296314815752750000000000), (-88384011864313696337/342837220029775000000), (-6559783170901693511684230038097/20693798592629631505500000000000)]
    bernstein := [(6881160620233170863425807052132600543/52976124397131856654080000000000000000), (3402369587672399550067589267231347381/26488062198565928327040000000000000000), (5045584072950604318205383644729895781/39732093297848892490560000000000000000), (831155714548741173918139317817351709/6622015549641482081760000000000000000), (410631237707358603447424025862764303/3311007774820741040880000000000000000)]
    reserve := (2480400323/20000000000) }

theorem quarter_026_012_valid : quarter_026_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_012]
  · intro i; fin_cases i <;> norm_num [quarter_026_012]
  · norm_num [quarter_026_012]
  · norm_num [quarter_026_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_012]

def quarter_026_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(8301019/100000000), (21484921/100000000), (21484921/100000000), (21484921/100000000), (9471599/100000000), (9471599/100000000), (8301019/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1314253/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6011921/100000000), (1/100000000), (1/100000000), (5932941/100000000), (1/100000000), (290747/6250000)]
    alternative := .zero
    polynomial := [(586910254396487330154964420607/5185236162663083383500000000000), (-158608969750596508451/699179197994800000000), (-2077502193192742347678599516947/10370472325326166767000000000000), (-158608969750596508451/699179197994800000000), (-3251322701985717007988528358161/10370472325326166767000000000000)]
    bernstein := [(205844433281898392672397163298653039/1659275572052186682720000000000000000), (135789080621632303422209965386463713/1106183714701457788480000000000000000), (345417003559101112292170220381388331/2844472409232320027520000000000000000), (531392700768598920854838851346479313/4424734858805831153920000000000000000), (3152310174980336672211394166751466639/26548409152834986923520000000000000000)]
    reserve := (1187381947/10000000000) }

theorem quarter_026_013_valid : quarter_026_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_013]
  · intro i; fin_cases i <;> norm_num [quarter_026_013]
  · norm_num [quarter_026_013]
  · norm_num [quarter_026_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_013]

def quarter_026_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(4482823/50000000), (4215073/20000000), (4215073/20000000), (4215073/20000000), (9421307/100000000), (9421307/100000000), (4482823/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (502521/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1472603/25000000), (1/100000000), (1/100000000), (5833199/100000000), (1/100000000), (4816407/100000000)]
    alternative := .zero
    polynomial := [(4718634432250919460475274323397/41372870371580779779000000000000), (-18371663294854587657/94568738632280000000), (-140768787291305879599569351607/713325351234151375500000000000), (-18371663294854587657/94568738632280000000), (-4294408031715553492416765572201/13790956790526926593000000000000)]
    bernstein := [(12581344142788941066144862422399473797/105914548151246796234240000000000000000), (10382540744719653405821742494449171/88262123459372330195200000000000000), (23127608035792436726170940584608997/198589777783587742939200000000000000), (19075473168928457502900268686713/165491481486323119116000000000000), (4718634432250919460475274323397/41372870371580779779000000000000)]
    reserve := (57025707787/500000000000) }

theorem quarter_026_014_valid : quarter_026_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_014]
  · intro i; fin_cases i <;> norm_num [quarter_026_014]
  · norm_num [quarter_026_014]
  · norm_num [quarter_026_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_014]

def quarter_026_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(1219787/12500000), (2589231/12500000), (2589231/12500000), (2589231/12500000), (9170931/100000000), (9170931/100000000), (1219787/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4698737/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2892849/50000000), (1/100000000), (1/100000000), (2862011/50000000), (1/100000000), (2478173/50000000)]
    alternative := .zero
    polynomial := [(58506795101933804571794653609/512942510852527691175000000000), (27004329047798587571/59741502373975000000), (-51488882309879164547482496891/256471255426263845587500000000), (27004329047798587571/59741502373975000000), (-161484559721692133666759647391/512942510852527691175000000000)]
    bernstein := [(58506795101933804571794653609/512942510852527691175000000000), (239823681916416649543128510511/2051770043410110764700000000000), (294692731227807817794346605406309/2462124052092132917640000000000000), (402066536866316384061111304166111/3282832069456177223520000000000000), (164460787817637558990349956275061409/1313132827782470889408000000000000000)]
    reserve := (114061115747/1000000000000) }

theorem quarter_026_015_valid : quarter_026_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_015]
  · intro i; fin_cases i <;> norm_num [quarter_026_015]
  · norm_num [quarter_026_015]
  · norm_num [quarter_026_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_015]

def quarter_026_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(1333219/12500000), (5101241/25000000), (5101241/25000000), (5101241/25000000), (4363401/50000000), (4363401/50000000), (1333219/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4257821/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5697197/100000000), (1/100000000), (1/100000000), (5607673/100000000), (1/100000000), (1267077/25000000)]
    alternative := .zero
    polynomial := [(4566453106105442888170556280971/40480598540570155737000000000000), (182532740499915048413/360939364158450000000), (-4294090459893402027768403859029/20240299270285077868500000000000), (182532740499915048413/360939364158450000000), (-13154634025892246943707363999029/40480598540570155737000000000000)]
    bernstein := [(12987371992922909471753714272652068171/103630332263859598686720000000000000000), (2218108216411821033750546004427170457/17271722043976599781120000000000000000), (10221024526030885633979096975173572113/77722749197894699015040000000000000000), (581071406824322957664049426703462057/4317930510994149945280000000000000000), (297122310275306006456841985174579257/2158965255497074972640000000000000000)]
    reserve := (3133101021/25000000000) }

theorem quarter_026_016_valid : quarter_026_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_016]
  · intro i; fin_cases i <;> norm_num [quarter_026_016]
  · norm_num [quarter_026_016]
  · norm_num [quarter_026_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_016]

def quarter_026_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(11534497/100000000), (1005953/5000000), (1005953/5000000), (1005953/5000000), (8286913/100000000), (8286913/100000000), (11534497/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1858403/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1400501/25000000), (1/100000000), (1/100000000), (2749019/50000000), (1/100000000), (258103/5000000)]
    alternative := .zero
    polynomial := [(3218705312761852808122373147/29226398408686160500000000000), (203108065860491321179/361473509603000000000), (-1663288597265981154382585489/7306599602171540125000000000), (203108065860491321179/361473509603000000000), (-9871859701825777425652715103/29226398408686160500000000000)]
    bernstein := [(644026140411039958671451051552497/4676223745389785680000000000000000), (1319802104060713545241417129146191/9352447490779571360000000000000000), (8108443977279256313634918292882819/56114684944677428160000000000000000), (5531544067248583184142198527098719/37409789963118285440000000000000000), (11314039931261107247262947528850257/74819579926236570880000000000000000)]
    reserve := (137723551197/1000000000000) }

theorem quarter_026_017_valid : quarter_026_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_017]
  · intro i; fin_cases i <;> norm_num [quarter_026_017]
  · norm_num [quarter_026_017]
  · norm_num [quarter_026_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_017]

def quarter_026_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(12363977/100000000), (9928007/50000000), (9928007/50000000), (9928007/50000000), (3926001/50000000), (3926001/50000000), (12363977/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (308317/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5500603/100000000), (1/100000000), (1/100000000), (5395267/100000000), (1/100000000), (654537/12500000)]
    alternative := .zero
    polynomial := [(822990652352602950363464108429/7769935902166382614800000000000), (178805663648376141097/288027854864880000000), (-960201189979352951790856571071/3884967951083191307400000000000), (178805663648376141097/288027854864880000000), (-2743393032311308853945177250571/7769935902166382614800000000000)]
    bernstein := [(3010305588752091023991089406668698949/19891035909545939493888000000000000000), (771025311487050223470525147731360683/4972758977386484873472000000000000000), (592059284361496161644706039022261283/3729569233039863655104000000000000000), (16828075029828931009913566781832029/103599145362218434864000000000000000), (4302293196599507920848287827591743/25899786340554608716000000000000000)]
    reserve := (151339809673/1000000000000) }

theorem quarter_026_018_valid : quarter_026_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_018]
  · intro i; fin_cases i <;> norm_num [quarter_026_018]
  · norm_num [quarter_026_018]
  · norm_num [quarter_026_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_018]

def quarter_026_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(13153871/100000000), (19615597/100000000), (19615597/100000000), (19615597/100000000), (7422733/100000000), (7422733/100000000), (13153871/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1182587/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5393457/100000000), (1/100000000), (1/100000000), (5299469/100000000), (1/100000000), (2645001/50000000)]
    alternative := .zero
    polynomial := [(840447819650878955127327659821/8400070050396551037000000000000), (27051827202045231097/39626942106825000000), (-379003048592765328849662340893/1400011675066091839500000000000), (27051827202045231097/39626942106825000000), (-3114466111207470928225301705179/8400070050396551037000000000000)]
    bernstein := [(13965718815125978610409308609169021/84000700503965510370000000000000000), (11444534234443202078331380322120601/67200560403172408296000000000000000), (9372701025146882418026094444037009/53760448322537926636800000000000000), (1534302907218580335595910752538513/8601671731606068261888000000000000), (251028691250062238798395932336749/1376267477056970921902080000000000)]
    reserve := (166257170849/1000000000000) }

theorem quarter_026_019_valid : quarter_026_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_019]
  · intro i; fin_cases i <;> norm_num [quarter_026_019]
  · norm_num [quarter_026_019]
  · norm_num [quarter_026_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_019]

def quarter_026_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(3476021/25000000), (4849371/25000000), (4849371/25000000), (4849371/25000000), (699969/10000000), (699969/10000000), (3476021/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (785843/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5281003/100000000), (1/100000000), (1/100000000), (5210713/100000000), (1/100000000), (266277/5000000)]
    alternative := .zero
    polynomial := [(16925143635409845910193659853/183183870753746437575000000000), (262874755336006878191/351552408957750000000), (-2485411415526280145722717127/8326539579715747162500000000), (262874755336006878191/351552408957750000000), (-71604194776988009116093436647/183183870753746437575000000000)]
    bernstein := [(421483384378032491151941788069/2308680414176447410176000000000), (70144401551001072436114260577027/375160567303672704153600000000000), (207102733591363839889340290922663/1082193944145209723520000000000000), (58850559005280728330971009955209/300609428929224923200000000000000), (5866781534651781031268647300735193/29309419320599430012000000000000000)]
    reserve := (182564629469/1000000000000) }

theorem quarter_026_020_valid : quarter_026_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_020]
  · intro i; fin_cases i <;> norm_num [quarter_026_020]
  · norm_num [quarter_026_020]
  · norm_num [quarter_026_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_020]

def quarter_026_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(584589/4000000), (768051/4000000), (768051/4000000), (768051/4000000), (6583363/100000000), (6583363/100000000), (584589/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (712003/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5163653/100000000), (1/100000000), (1/100000000), (1282257/25000000), (1/100000000), (2672631/50000000)]
    alternative := .zero
    polynomial := [(162820811427138972152683142077/1966204204493439339000000000000), (30040365652946926969/36801437549448000000), (-325113667591803822568539170423/983102102246719669500000000000), (30040365652946926969/36801437549448000000), (-813048146610746617289761482923/1966204204493439339000000000000)]
    bernstein := [(63030811718530187554450386267657637/314592672718950294240000000000000000), (129076162511664361576198955531393753/629185345437900588480000000000000000), (792536659759893816952292925810375271/3775112072627403530880000000000000000), (540411448873021348762560957982712833/2516741381751602353920000000000000000), (1104941712733650213302687364339295477/5033482763503204707840000000000000000)]
    reserve := (200356896979/1000000000000) }

theorem quarter_026_021_valid : quarter_026_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_021]
  · intro i; fin_cases i <;> norm_num [quarter_026_021]
  · norm_num [quarter_026_021]
  · norm_num [quarter_026_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_021]

def quarter_026_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(15255393/100000000), (19016279/100000000), (19016279/100000000), (19016279/100000000), (1555047/25000000), (1555047/25000000), (15255393/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (157393/3125000), (1/100000000), (1/100000000), (1263889/25000000), (1/100000000), (5359687/100000000)]
    alternative := .zero
    polynomial := [(308881534336199189797417066577/4264751855766595996000000000000), (443770702051383/503657600000000), (-775190419096975872875670693423/2132375927883297998000000000000), (443770702051383/503657600000000), (-1859262372530150935548758453423/4264751855766595996000000000000)]
    bernstein := [(2399707638523916940958066805510074977/10917764750762485749760000000000000000), (614008506617215308130819654445562697/2729441187690621437440000000000000000), (39255967929466100625796085119452473/170590074230663839840000000000000000), (78392821145528520599235740191151/333183738731765312187500000000000), (80115929454372774373212962931069/333183738731765312187500000000000)]
    reserve := (109899218993/500000000000) }

theorem quarter_026_022_valid : quarter_026_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_022]
  · intro i; fin_cases i <;> norm_num [quarter_026_022]
  · norm_num [quarter_026_022]
  · norm_num [quarter_026_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_022]

def quarter_026_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(15726269/100000000), (18813763/100000000), (18813763/100000000), (18813763/100000000), (6053087/100000000), (6053087/100000000), (15726269/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (152641/3125000), (1/100000000), (1/100000000), (1248463/25000000), (1/100000000), (1354397/25000000)]
    alternative := .zero
    polynomial := [(67502486025030929027156465281/1032411546306291404000000000000), (449500597131703/488451200000000), (-198390242029305336306085069719/516205773153145702000000000000), (449500597131703/488451200000000), (-464282970083641601639326604719/1032411546306291404000000000000)]
    bernstein := [(19414520229192268759179813415307/80657152055179015937500000000000), (79397386944256757596087732721919/322628608220716063750000000000000), (335024334679743623693267415058731/1332143930717795360000000000000000), (169743860979223650291213721403072523/660743389636026498560000000000000000), (693290207876173394780961294102483841/2642973558544105994240000000000000000)]
    reserve := (60176065403/250000000000) }

theorem quarter_026_023_valid : quarter_026_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_023]
  · intro i; fin_cases i <;> norm_num [quarter_026_023]
  · norm_num [quarter_026_023]
  · norm_num [quarter_026_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_023]

def quarter_026_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(8064363/50000000), (9313767/50000000), (9313767/50000000), (9313767/50000000), (5929973/100000000), (5929973/100000000), (8064363/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2362779/50000000), (1/100000000), (1/100000000), (154361/3125000), (1/100000000), (5467191/100000000)]
    alternative := .zero
    polynomial := [(20460163974671160252569375827/354488707864489569600000000000), (503192058111/525062000000), (-71739767756376214522927440173/177244353932244784800000000000), (503192058111/525062000000), (-163939699487423589298424256173/354488707864489569600000000000)]
    bernstein := [(14017325842341648222413027052207491/53381828949005488128000000000000000), (24340307880296968230682299285028603/90749109213309329817600000000000000), (7455636845751994411660199227926073/27224732763992798945280000000000000), (253650909263843602261372098798971/907491092133093298176000000000000), (1522316940337333816094880957059/5338182894900548812800000000000)]
    reserve := (131293045951/500000000000) }

theorem quarter_026_024_valid : quarter_026_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_024]
  · intro i; fin_cases i <;> norm_num [quarter_026_024]
  · norm_num [quarter_026_024]
  · norm_num [quarter_026_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_024]

def quarter_026_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(16469069/100000000), (3691157/20000000), (3691157/20000000), (3691157/20000000), (5847253/100000000), (5847253/100000000), (16469069/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4560689/100000000), (1/100000000), (1/100000000), (611483/12500000), (1/100000000), (2754559/50000000)]
    alternative := .zero
    polynomial := [(189606613404803870966885249/3840934746360503466500000000), (454170200271247/456068900000000), (-3264554110036041980178086349/7681869492721006933000000000), (454170200271247/456068900000000), (-3643767336845649722111856847/7681869492721006933000000000)]
    bernstein := [(561394366887800362099338625177/1966558590136577774848000000000), (5729531349021418149103612023341/19665585901365777748480000000000), (58454140823564776082083906527189/196655859013657777484800000000000), (596163193009421383050190826466113/1966558590136577774848000000000000), (6078221309678321802528628872068273/19665585901365777748480000000000000)]
    reserve := (57094090123/200000000000) }

theorem quarter_026_025_valid : quarter_026_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_025]
  · intro i; fin_cases i <;> norm_num [quarter_026_025]
  · norm_num [quarter_026_025]
  · norm_num [quarter_026_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_025]

def quarter_026_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(16753369/100000000), (4574247/25000000), (4574247/25000000), (4574247/25000000), (5801149/100000000), (5801149/100000000), (16753369/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (439091/10000000), (1/100000000), (1/100000000), (970019/20000000), (1/100000000), (2771929/50000000)]
    alternative := .zero
    polynomial := [(47501434174927370637471267643/1180638329695284241000000000000), (56707657813019/54886375000000), (-262828285152903888933101229857/590319164847642120500000000000), (56707657813019/54886375000000), (-573158004480735148503673727357/1180638329695284241000000000000)]
    bernstein := [(935137813848189061427011827375695763/3022434124019927656960000000000000000), (238423533766745832522871753226715099/755608531004981914240000000000000000), (182307991579768748571209936778224581/566706398253736435680000000000000000), (73384861325345983353418183400861/223817692833229240000000000000000), (3944293328355579924778540383811483/11806383296952842410000000000000000)]
    reserve := (773497267/2500000000) }

theorem quarter_026_026_valid : quarter_026_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_026]
  · intro i; fin_cases i <;> norm_num [quarter_026_026]
  · norm_num [quarter_026_026]
  · norm_num [quarter_026_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_026]

def quarter_026_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(4772331/25000000), (20481421/100000000), (15518343/100000000), (15518343/100000000), (5151623/100000000), (5151623/100000000), (4772331/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2481539/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2375253/50000000), (1/100000000), (1/100000000), (2065797/50000000), (1/100000000), (2976759/50000000)]
    alternative := .zero
    polynomial := [(50477356051466082899079283/45081274217313399750000000000), (15898454940147/13195850000000), (-14065226349982655731591325717/22540637108656699875000000000), (15898454940147/13195850000000), (-28180930056016777546081730717/45081274217313399750000000000)]
    bernstein := [(150512286222977054029810823501323/450812742173133997500000000000000), (614313464107224363674647426348333/1803250968692535990000000000000000), (7519210133070218102420764682020429/21639011624310431880000000000000000), (10222631816222590954554517239866753/28852015499080575840000000000000000), (41680458158751731247708430260318163/115408061996322303360000000000000000)]
    reserve := (20866796807/62500000000) }

theorem quarter_026_027_valid : quarter_026_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_027]
  · intro i; fin_cases i <;> norm_num [quarter_026_027]
  · norm_num [quarter_026_027]
  · norm_num [quarter_026_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_027]

def quarter_026_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(680803/2500000), (29027561/100000000), (5948371/100000000), (5948371/100000000), (2305729/100000000), (2305729/100000000), (680803/2500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2307919/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6465521/100000000), (1/100000000), (1/100000000), (806001/50000000), (1/100000000), (7360279/100000000)]
    alternative := .zero
    polynomial := [(-1191495612578922640307008264181/9589001642741948589750000000000), (28565542798209/16163802500000), (-6177222725599039466827425611681/4794500821370974294875000000000), (28565542798209/16163802500000), (-11162949838619156293347842959181/9589001642741948589750000000000)]
    bernstein := [(306164655851568961316464298841737471/846477386393772013440000000000000000), (1513803371531994485052531583330516867/4091307367569898064960000000000000000), (6964567795117190022992190263891613217/18410883154064541292320000000000000000), (395358744010196718735666387765836107/1022826841892474516240000000000000000), (605649487385243372413340693754151219/1534240262838711774360000000000000000)]
    reserve := (72338531607/200000000000) }

theorem quarter_026_028_valid : quarter_026_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_028]
  · intro i; fin_cases i <;> norm_num [quarter_026_028]
  · norm_num [quarter_026_028]
  · norm_num [quarter_026_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_028]

def quarter_026_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 2]
    lambda := ![(204409/625000), (108091/312500), 0, 0, 0, 0, (204409/625000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (108091/312500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1847263/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (8264011/100000000)]
    alternative := .zero
    polynomial := [(-210248425536991627959309/954112609493312500000000), (1261388111327/577269687500), (-852314308000034504259309/477056304746656250000000), (1261388111327/577269687500), (-1494380190463077380559309/954112609493312500000000)]
    bernstein := [(60413626560486385418306746291/152658017518930000000000000000), (24726039430512713190742916879/61063207007572000000000000000), (10113014143376982046097628203/24425282803028800000000000000), (4133589852988557062619650183/9770113121211520000000000000), (1688525050394286905135442339/3908045248484608000000000000)]
    reserve := (98936216293/250000000000) }

theorem quarter_026_029_valid : quarter_026_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_026_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_026_029]
  · intro i; fin_cases i <;> norm_num [quarter_026_029]
  · norm_num [quarter_026_029]
  · norm_num [quarter_026_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_026_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_026_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_026_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_026_029]

def quarterTable026 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 0, 0, 0, 2]
  rows := [quarter_026_000, quarter_026_001, quarter_026_002, quarter_026_003, quarter_026_004, quarter_026_005, quarter_026_006, quarter_026_007, quarter_026_008, quarter_026_009, quarter_026_010, quarter_026_011, quarter_026_012, quarter_026_013, quarter_026_014, quarter_026_015, quarter_026_016, quarter_026_017, quarter_026_018, quarter_026_019, quarter_026_020, quarter_026_021, quarter_026_022, quarter_026_023, quarter_026_024, quarter_026_025, quarter_026_026, quarter_026_027, quarter_026_028, quarter_026_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_026_000_valid
    · exact quarter_026_001_valid
    · exact quarter_026_002_valid
    · exact quarter_026_003_valid
    · exact quarter_026_004_valid
    · exact quarter_026_005_valid
    · exact quarter_026_006_valid
    · exact quarter_026_007_valid
    · exact quarter_026_008_valid
    · exact quarter_026_009_valid
    · exact quarter_026_010_valid
    · exact quarter_026_011_valid
    · exact quarter_026_012_valid
    · exact quarter_026_013_valid
    · exact quarter_026_014_valid
    · exact quarter_026_015_valid
    · exact quarter_026_016_valid
    · exact quarter_026_017_valid
    · exact quarter_026_018_valid
    · exact quarter_026_019_valid
    · exact quarter_026_020_valid
    · exact quarter_026_021_valid
    · exact quarter_026_022_valid
    · exact quarter_026_023_valid
    · exact quarter_026_024_valid
    · exact quarter_026_025_valid
    · exact quarter_026_026_valid
    · exact quarter_026_027_valid
    · exact quarter_026_028_valid
    · exact quarter_026_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
