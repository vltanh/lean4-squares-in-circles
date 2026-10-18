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

def quarter_042_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_042_000_valid : quarter_042_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_000]
  · intro i; fin_cases i <;> norm_num [quarter_042_000]
  · norm_num [quarter_042_000]
  · norm_num [quarter_042_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_000]

def quarter_042_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_042_001_valid : quarter_042_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_001]
  · intro i; fin_cases i <;> norm_num [quarter_042_001]
  · norm_num [quarter_042_001]
  · norm_num [quarter_042_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_001]

def quarter_042_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-382804973875870721/684552687500000000), (-39204036/10952843), (-1067357661375870721/342276343750000000), (-39204036/10952843), (-1751910348875870721/684552687500000000)]
    bernstein := [(646693971861456324660719/1752454880000000000000000), (155279285836763680907889/438113720000000000000000), (111621009402992369262377/328585290000000000000000), (8894952571565710129429/27382107500000000000000), (2121126590005779963799/6845526875000000000000)]
    reserve := (61971171211/200000000000) }

theorem quarter_042_002_valid : quarter_042_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_002]
  · intro i; fin_cases i <;> norm_num [quarter_042_002]
  · norm_num [quarter_042_002]
  · norm_num [quarter_042_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_002]

def quarter_042_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-556512809540135577/1127647700000000000), (-75237955/22552954), (-1684160509540135577/563823850000000000), (-75237955/22552954), (-2811808209540135577/1127647700000000000)]
    bernstein := [(3477032164953649209663/11276477000000000000000), (13294893098709221172331/45105908000000000000000), (152104840977384548853841/541270896000000000000000), (192793584408782748968639/721694528000000000000000), (730712026497435302482743/2886778112000000000000000)]
    reserve := (253123724147/1000000000000) }

theorem quarter_042_003_valid : quarter_042_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_003]
  · intro i; fin_cases i <;> norm_num [quarter_042_003]
  · norm_num [quarter_042_003]
  · norm_num [quarter_042_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_003]

def quarter_042_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4491503/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (578989/2500000)]
    alternative := .zero
    polynomial := [(-31489286020192343/72373625000000000), (-8983006/2894945), (-103862911020192343/36186812500000000), (-8983006/2894945), (-176236536020192343/72373625000000000)]
    bernstein := [(46648716103417490616537/185276480000000000000000), (4430286397231575186187/18527648000000000000000), (1257891006024344017523/5558294400000000000000), (39528917639300858899/185276480000000000000), (3710003290164412873/18527648000000000000)]
    reserve := (20024146023/100000000000) }

theorem quarter_042_004_valid : quarter_042_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_004]
  · intro i; fin_cases i <;> norm_num [quarter_042_004]
  · norm_num [quarter_042_004]
  · norm_num [quarter_042_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_004]

def quarter_042_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (68290369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-227369526439286957/593044725000000000), (-9755767/3388827), (-820414251439286957/296522362500000000), (-9755767/3388827), (-1413458976439286957/593044725000000000)]
    bernstein := [(10073437836348689809/50606483200000000000), (94768432271642857513/506064832000000000000), (7985100306579547072057/45545834880000000000000), (24779433730114407672827/151819449600000000000000), (229173926598944049100723/1518194496000000000000000)]
    reserve := (75475812619/500000000000) }

theorem quarter_042_005_valid : quarter_042_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_005]
  · intro i; fin_cases i <;> norm_num [quarter_042_005]
  · norm_num [quarter_042_005]
  · norm_num [quarter_042_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_005]

def quarter_042_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (32261287/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4847213/20000000)]
    alternative := .zero
    polynomial := [(-409539937756191047/1211803250000000000), (-64522574/24236065), (-1621343187756191047/605901625000000000), (-64522574/24236065), (-2833146437756191047/1211803250000000000)]
    bernstein := [(465061375391627830838233/3102216320000000000000000), (53877066138430155648537/387777040000000000000000), (4645994352667887962951/36354097500000000000000), (352909745491428925301/3029508125000000000000), (19883491019203713057/189344257812500000000)]
    reserve := (105012379297/1000000000000) }

theorem quarter_042_006_valid : quarter_042_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_006]
  · intro i; fin_cases i <;> norm_num [quarter_042_006]
  · norm_num [quarter_042_006]
  · norm_num [quarter_042_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_006]

def quarter_042_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, (99999999/100000000)]
    cone := fun i => (![![(49999999/100000000), 0, (99999999/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (30283991/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (192961/781250)]
    alternative := .zero
    polynomial := [(-1842574939151602693/6174752000000000000), (-3028399069716009/1234950400000000), (-8017326877404082693/3087376000000000000), (-3028399069716009/1234950400000000), (-14192078815656562693/6174752000000000000)]
    bernstein := [(100447908914948367383/964805000000000000000), (1449494249414402405637/15436880000000000000000), (3867375590864660210819/46310640000000000000000), (144130865897990171127051/1975920640000000000000000), (983178212504923910031707/15807365120000000000000000)]
    reserve := (62197475989/1000000000000) }

theorem quarter_042_007_valid : quarter_042_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_007]
  · intro i; fin_cases i <;> norm_num [quarter_042_007]
  · norm_num [quarter_042_007]
  · norm_num [quarter_042_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_007]

def quarter_042_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(7525451/50000000), (21532083/100000000), (24183057/100000000), (24183057/100000000), 0, 0, (7525451/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7163217/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (530879/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6638131/100000000), (524423/25000000), (1/100000000), (6286287/100000000), (1/100000000), (3778903/100000000)]
    alternative := .zero
    polynomial := [(202699179815969409432023615665368071/110262093754557847326611324000000000000), (-145289315467813/188945150000000), (-153244933792372001240560153692819646929/55131046877278923663305662000000000000), (-145289315467813/188945150000000), (-306692566764559971890552331001304661929/110262093754557847326611324000000000000)]
    bernstein := [(14901128902441770411539693943874280307601271/282270960011668089156124989440000000000000000), (7620728116267461085000859611826899107323859/141135480005834044578062494720000000000000000), (3874223758992934889614235836612597484857711/70567740002917022289031247360000000000000000), (1958593037585740912065264296228535086723019/35283870001458511144515623680000000000000000), (984874770127776596490130612438793399054951/17641935000729255572257811840000000000000000)]
    reserve := (1055803183/20000000000) }

theorem quarter_042_008_valid : quarter_042_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_008]
  · intro i; fin_cases i <;> norm_num [quarter_042_008]
  · norm_num [quarter_042_008]
  · norm_num [quarter_042_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_008]

def quarter_042_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(7249767/50000000), (2205491/10000000), (2447301/10000000), (2447301/10000000), 0, 0, (7249767/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (453069/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3779739/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1333859/20000000), (922851/50000000), (1/100000000), (6361659/100000000), (1/100000000), (738277/20000000)]
    alternative := .zero
    polynomial := [(202649302978621328247397430669687/11895835948069631461954500000000000), (-17027202261497/23071156250000), (-18916055287376376323378891282485313/5947917974034815730977250000000000), (-17027202261497/23071156250000), (-12678253292577124658335059998546771/3965278649356543820651500000000000)]
    bernstein := [(108595967116872562675597295961232161047/1903333751691141033912720000000000000000), (44434788935815168315184178535191829229/761333500676456413565088000000000000000), (2356752214798930069373623555119272987/39721747861380334620787200000000000000), (486941682492619923982314921218051451/8120890673882201744694272000000000000), (117443697306547759159167506546758303/1949013761731728418726625280000000000)]
    reserve := (57055661951/1000000000000) }

theorem quarter_042_009_valid : quarter_042_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_009]
  · intro i; fin_cases i <;> norm_num [quarter_042_009]
  · norm_num [quarter_042_009]
  · norm_num [quarter_042_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_009]

def quarter_042_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(3495327/25000000), (903849/4000000), (1236029/5000000), (1236029/5000000), 0, 0, (3495327/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1830609/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6666491/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (671419/10000000), (787857/50000000), (1/100000000), (3213007/50000000), (1/100000000), (3600187/100000000)]
    alternative := .zero
    polynomial := [(1948282919341567688561807548756703/62438387730650152406251500000000000), (-127953767469189/180009350000000), (-117453695394108404328843663082738297/31219193865325076203125750000000000), (-127953767469189/180009350000000), (-236855673707558376346249133714233297/62438387730650152406251500000000000)]
    bernstein := [(631521131611747459650681639306236807/10229905445789720970240245760000000000), (1345780115688237787614248518124435753/21312303012061918688000512000000000000), (76912941900321991105383440176461331961/1198817044428482926200028800000000000000), (10784773222977386930448002605380964081/166502367281733739750004000000000000000), (40581346052794706803214009937239237303/624383877306501524062515000000000000000)]
    reserve := (15433210379/250000000000) }

theorem quarter_042_010_valid : quarter_042_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_010]
  · intro i; fin_cases i <;> norm_num [quarter_042_010]
  · norm_num [quarter_042_010]
  · norm_num [quarter_042_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_010]

def quarter_042_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(843469/6250000), (11578843/50000000), (12462827/50000000), (12462827/50000000), 0, 0, (843469/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (369159/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2907311/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1693153/25000000), (161009/12500000), (1/100000000), (3239661/50000000), (1/100000000), (701211/20000000)]
    alternative := .zero
    polynomial := [(218751120921653118455407793137647/4915006540474749338504500000000000), (-60213874009237/87651375000000), (-11457301435815031718001567710993603/2457503270237374669252250000000000), (-60213874009237/87651375000000), (-23133353992551716554458543215124853/4915006540474749338504500000000000)]
    bernstein := [(9849434211297311907963236055144233641/147450196214242480155135000000000000000), (40296010022978782517013751036596120023/589800784856969920620540000000000000000), (163612649535668142933446408507326667069/2359203139427879682482160000000000000000), (659551179440964755820901480741377481307/9436812557711518729928640000000000000000), (880086174453257730763612311593572400507/12582416743615358306571520000000000000000)]
    reserve := (3339918991/50000000000) }

theorem quarter_042_011_valid : quarter_042_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_011]
  · intro i; fin_cases i <;> norm_num [quarter_042_011]
  · norm_num [quarter_042_011]
  · norm_num [quarter_042_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_011]

def quarter_042_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(6520847/50000000), (23740801/100000000), (12543953/50000000), (12543953/50000000), 0, 0, (6520847/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7431241/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (250163/5000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6844371/100000000), (983211/100000000), (1/100000000), (6521499/100000000), (1/100000000), (3409783/100000000)]
    alternative := .zero
    polynomial := [(292031127464219904726352046402735677/5115976890019523892252324000000000000), (-113576472617403/170489150000000), (-15870894313954157738391176073100344323/2557988445009761946126162000000000000), (-113576472617403/170489150000000), (-32033819755372535381508704192603424323/5115976890019523892252324000000000000)]
    bernstein := [(12297623935149476805045726766909153157416681/170259710899849755134157342720000000000000000), (6289175653871947007574939791479803394154627/85129855449924877567078671360000000000000000), (9560963166793438142044522750365390276237427/127694783174887316350618007040000000000000000), (1600903617128423071433886122494957131573403/21282463862481219391769667840000000000000000), (797285954370707035132625366793142259484601/10641231931240609695884833920000000000000000)]
    reserve := (36114309927/500000000000) }

theorem quarter_042_012_valid : quarter_042_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_012]
  · intro i; fin_cases i <;> norm_num [quarter_042_012]
  · norm_num [quarter_042_012]
  · norm_num [quarter_042_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_012]

def quarter_042_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(6309873/50000000), (24346941/100000000), (25206783/100000000), (25206783/100000000), 0, 0, (6309873/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7466453/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4231599/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6929293/100000000), (661863/100000000), (1/100000000), (6552401/100000000), (1/100000000), (1656103/50000000)]
    alternative := .zero
    polynomial := [(4579926204224728464225268730657627369/66356516276594233664591036000000000000), (-107342936338773/165610300000000), (-311437286398578934225318984702894512631/33178258138297116832295518000000000000), (-107342936338773/165610300000000), (-627454499001382596914863238136446652631/66356516276594233664591036000000000000)]
    bernstein := [(827951317262029206168594532699219417482569/10617042604255077386334565760000000000000000), (1694439801271901166446240375710897805270169/21234085208510154772669131520000000000000000), (1467527832977263645997508597552748718748701/18200644464437275519430684160000000000000000), (6836134988884309125200626606985488931952969/84936340834040619090676526080000000000000000), (13481746374357077470729796029253065847968169/169872681668081238181353052160000000000000000)]
    reserve := (77983233949/1000000000000) }

theorem quarter_042_013_valid : quarter_042_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_013]
  · intro i; fin_cases i <;> norm_num [quarter_042_013]
  · norm_num [quarter_042_013]
  · norm_num [quarter_042_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_013]

def quarter_042_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(12229831/100000000), (24977339/100000000), (50563/200000), (50563/200000), 0, 0, (12229831/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1497717/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (139943/4000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7027213/100000000), (163277/50000000), (1/100000000), (6571823/100000000), (1/100000000), (3214193/100000000)]
    alternative := .zero
    polynomial := [(338073766239319347751989671364322573/4215004998205548861235972000000000000), (-203350957335679/321419300000000), (-40930649950359725881018826196507997427/2107502499102774430617986000000000000), (-203350957335679/321419300000000), (-82199373666958771109789642064380317427/4215004998205548861235972000000000000)]
    bernstein := [(905183323897945131244762406880826181196173/10790412795406205084764088320000000000000000), (580004711892370033429993414269697939123/6744007997128878177977555200000000000000), (1741824766105905013337937169424429952973/20232023991386634533932665600000000000000), (354740572292187250877969418559342323/4215004998205548861235972000000000000), (338073766239319347751989671364322573/4215004998205548861235972000000000000)]
    reserve := (16041440823/200000000000) }

theorem quarter_042_014_valid : quarter_042_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_014]
  · intro i; fin_cases i <;> norm_num [quarter_042_014]
  · norm_num [quarter_042_014]
  · norm_num [quarter_042_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_014]

def quarter_042_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(6001029/50000000), (25337239/100000000), (25329323/100000000), (25329323/100000000), 0, 0, (6001029/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(158333/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (30011/400000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2833407/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1771043/25000000), (160043/100000000), (1/100000000), (3292127/50000000), (1/100000000), (3150669/100000000)]
    alternative := .zero
    polynomial := [(176236599074546199402091888077781/2069683377998124419414000000000000), (10070359020374243/8874384350000000), (-3197653311907748166469303820197863/79603206846081708439000000000000), (10070359020374243/8874384350000000), (-83315222708675998527603991213222219/2069683377998124419414000000000000)]
    bernstein := [(176236599074546199402091888077781/2069683377998124419414000000000000), (190915402311008206979665558083531/2069683377998124419414000000000000), (315094231191018767903549115055325527/3311493404796999071062400000000000000), (310881999802727291259177260959483131/3311493404796999071062400000000000000), (468464890114851585188555442914591836981/5298389447675198513699840000000000000000)]
    reserve := (17030295643/200000000000) }

theorem quarter_042_015_valid : quarter_042_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_015]
  · intro i; fin_cases i <;> norm_num [quarter_042_015]
  · norm_num [quarter_042_015]
  · norm_num [quarter_042_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_015]

def quarter_042_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(5975441/50000000), (12706831/50000000), (25342287/100000000), (25342287/100000000), 0, 0, (5975441/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(475837/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (750659/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2217203/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1774029/25000000), (20047/12500000), (1/100000000), (823453/12500000), (1/100000000), (3125743/100000000)]
    alternative := .zero
    polynomial := [(34535242596753418213588872061515023/732305297253741374569416000000000000), (19865961855090124903/6266176992100000000), (-14756993993694452279534457870178874977/366152648626870687284708000000000000), (19865961855090124903/6266176992100000000), (-29548523229985657977282504612419264977/732305297253741374569416000000000000)]
    bernstein := [(189837568061937471601355104960310634888623/1874701560969577918897704960000000000000000), (33902180246864598513674763053847433676741/312450260161596319816284160000000000000000), (156851312125227505494881371300364315684669/1406026170727183439173278720000000000000000), (8624885009274488742868276016509826707541/78112565040399079954071040000000000000000), (12310229576757111401572840813090262033423/117168847560598619931106560000000000000000)]
    reserve := (50631410357/500000000000) }

theorem quarter_042_016_valid : quarter_042_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_016]
  · intro i; fin_cases i <;> norm_num [quarter_042_016]
  · norm_num [quarter_042_016]
  · norm_num [quarter_042_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_016]

def quarter_042_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(1493773/12500000), (12749417/50000000), (25300399/100000000), (25300399/100000000), 0, 0, (1493773/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(396869/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7494183/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1608597/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3557761/50000000), (80281/50000000), (1/100000000), (205523/3125000), (1/100000000), (388289/12500000)]
    alternative := .zero
    polynomial := [(-24895879835534500033145484698011397/583505598129028631388851200000000000), (16269589965825242127/3117222920900000000), (-11817118116602855590222845531520027397/291752799064514315694425600000000000), (16269589965825242127/3117222920900000000), (-23609340353370176680412545578342043397/583505598129028631388851200000000000)]
    bernstein := [(10963993752866259955950429986486531239003/93360895700644581022216192000000000000000), (23314145170081857965387728038422604515809/186721791401289162044432384000000000000000), (7552395038040889409910639992793446753299/58964776231986051171926016000000000000000), (94924837417796707369738770459591237984281/746887165605156648177729536000000000000000), (182039789616564394072012889672286500011243/1493774331210313296355459072000000000000000)]
    reserve := (29359170321/250000000000) }

theorem quarter_042_017_valid : quarter_042_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_017]
  · intro i; fin_cases i <;> norm_num [quarter_042_017]
  · norm_num [quarter_042_017]
  · norm_num [quarter_042_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_017]

def quarter_042_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(11998451/100000000), (25593649/100000000), (6301181/25000000), (6301181/25000000), 0, 0, (11998451/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2222429/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7465843/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (501029/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7142391/100000000), (160609/100000000), (1/100000000), (1310373/20000000), (1/100000000), (618377/20000000)]
    alternative := .zero
    polynomial := [(-76409138602714282984690262682255907/413122877190227558144844000000000000), (180859361219622358689/24829227898250000000), (-1206136463617110800297000274589829/29580615579996245034000000000000), (180859361219622358689/24829227898250000000), (-16768492712273855153963215572239295907/413122877190227558144844000000000000)]
    bernstein := [(141492093535434520531608636052726912829933/1057594565606982548850800640000000000000000), (37392984203169892307876274904546433111711/264398641401745637212700160000000000000000), (28723020808231026541597276335539998649411/198298981051309227909525120000000000000000), (2380068796322094364044660333218548257379/16524915087609102325793760000000000000000), (573983715693885900013976569418406932693/4131228771902275581448440000000000000000)]
    reserve := (133786706301/1000000000000) }

theorem quarter_042_018_valid : quarter_042_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_018]
  · intro i; fin_cases i <;> norm_num [quarter_042_018]
  · norm_num [quarter_042_018]
  · norm_num [quarter_042_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_018]

def quarter_042_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(2418819/20000000), (25698851/100000000), (25056479/100000000), (25056479/100000000), 0, 0, (2418819/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(228399/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1855483/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (392317/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3588363/50000000), (80261/50000000), (1/100000000), (651333/10000000), (1/100000000), (770459/25000000)]
    alternative := .zero
    polynomial := [(-36660567708879216945604401533731723/96352345793683558784214000000000000), (9268646279372998671/989404956784000000), (-1980866826160407617759466271128646723/48176172896841779392107000000000000), (9268646279372998671/989404956784000000), (-3925073084611936018573328140723561723/96352345793683558784214000000000000)]
    bernstein := [(144941175310291485995304188021108613677/963523457936835587842140000000000000000), (13559496971512232910157999386651506293/85646529594385385585968000000000000000), (299630307958604900536370005537885344299/1849965039238724328656908800000000000000), (1768726050118650064601617124160023909/10962755788081329355003904000000000000), (2468968787398161674192207629873580813/15786368334837114271205621760000000000)]
    reserve := (150428278747/1000000000000) }

theorem quarter_042_019_valid : quarter_042_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_019]
  · intro i; fin_cases i <;> norm_num [quarter_042_019]
  · norm_num [quarter_042_019]
  · norm_num [quarter_042_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_019]

def quarter_042_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(6116141/50000000), (6454303/25000000), (3107389/12500000), (3107389/12500000), 0, 0, (6116141/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1393599/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (736347/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (180467/2500000), (501/312500), (1/100000000), (258481/4000000), (1/100000000), (3090853/100000000)]
    alternative := .zero
    polynomial := [(-727052572998153146939075080661731/1155746224101500005296000000000000), (3063606050507/267200000000), (-24001840992166831530073120435197731/577873112050750002648000000000000), (3063606050507/267200000000), (-15758876470445169971069055263244577/385248741367166668432000000000000)]
    bernstein := [(31726548468088100496862364538388261/189357461356789760867696640000000000), (138603339791374220003756017237016137/788989422319957336948736000000000000), (325187732101663828115268180356983663/1811455306346840824627200000000000000), (13243894111322966562713627967723785423/73967758342496000338944000000000000000), (32216173977668408049219057050906344589/184919395856240000847360000000000000000)]
    reserve := (83774223209/500000000000) }

theorem quarter_042_020_valid : quarter_042_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_020]
  · intro i; fin_cases i <;> norm_num [quarter_042_020]
  · norm_num [quarter_042_020]
  · norm_num [quarter_042_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_020]

def quarter_042_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(6188171/50000000), (1623337/6250000), (12318481/50000000), (12318481/50000000), 0, 0, (6188171/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4112091/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1824417/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3634973/50000000), (80079/50000000), (1/100000000), (3202139/50000000), (1/100000000), (1563627/50000000)]
    alternative := .zero
    polynomial := [(-150831311821797796112942216632655901/161938705072477168522739000000000000), (9065593472059/667325000000), (-10217923411672730497678984177154587703/242908057608715752784108500000000000), (9065593472059/667325000000), (-19983352887880067607019141704411207703/485816115217431505568217000000000000)]
    bernstein := [(4790785771249344886513806428709613944819/25910192811596346963638240000000000000000), (10011409527453037032819732456217739739111/51820385623192693927276480000000000000000), (183909717312853066623431973143130566505331/932766941217468490690976640000000000000000), (122360599087726437326690527317991057655213/621844627478312327127317760000000000000000), (238724668461622086156493021476021063594697/1243689254956624654254635520000000000000000)]
    reserve := (46224914323/250000000000) }

theorem quarter_042_021_valid : quarter_042_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_021]
  · intro i; fin_cases i <;> norm_num [quarter_042_021]
  · norm_num [quarter_042_021]
  · norm_num [quarter_042_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_021]

def quarter_042_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(3128923/25000000), (26174813/100000000), (24396901/100000000), (24396901/100000000), 0, 0, (3128923/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2370549/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (22583/312500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1466209/20000000), (80041/50000000), (1/100000000), (10147/160000), (1/100000000), (632493/20000000)]
    alternative := .zero
    polynomial := [(-301812866640345863534497399423/233618234490217616625000000000), (63050445285709/4002050000000), (-129758022390241667033909500740623/3037037048372829016125000000000), (63050445285709/4002050000000), (-31458613780979292701990258637031/759259262093207254031250000000)]
    bernstein := [(393119823013872394590852912926992769/1943703710958610570320000000000000000), (22757808489180196812648012710522927/107983539497700587240000000000000000), (12047420903291027641127469944117713/56068376277652227990000000000000000), (5526788406836223102659114426741/25759432132085063750000000000000), (15311927802498619629265805901901/73005698278193005195312500000000)]
    reserve := (202252956969/1000000000000) }

theorem quarter_042_022_valid : quarter_042_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_022]
  · intro i; fin_cases i <;> norm_num [quarter_042_022]
  · norm_num [quarter_042_022]
  · norm_num [quarter_042_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_022]

def quarter_042_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(12649779/100000000), (5284451/20000000), (12069547/50000000), (12069547/50000000), 0, 0, (12649779/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(10744287/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1430039/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7402069/100000000), (80047/50000000), (1/100000000), (6274859/100000000), (1/100000000), (1598173/50000000)]
    alternative := .zero
    polynomial := [(-40729019051293000716792060382839524529/23767633460379671098570004000000000000), (15154663070823/842600000000), (-517182971559596390038596089159675784529/11883816730189835549285002000000000000), (15154663070823/842600000000), (-993636924067899779360400117936512044529/23767633460379671098570004000000000000)]
    bernstein := [(815833520905794150825465185664755124599/3713692728184323609151563125000000000000), (714344426420264003063197262001939132353/3127320192155219881390790000000000000000), (165924916887074636281440962627500720405757/713029003811390132957100120000000000000000), (93058324364608989605884128891367912539261/400296984595868144818021120000000000000000), (13851434365786078411766259216660948538888431/60845141658571958012339210240000000000000000)]
    reserve := (219682558741/1000000000000) }

theorem quarter_042_023_valid : quarter_042_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_023]
  · intro i; fin_cases i <;> norm_num [quarter_042_023]
  · norm_num [quarter_042_023]
  · norm_num [quarter_042_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_023]

def quarter_042_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(2555651/20000000), (6679129/25000000), (23863487/100000000), (23863487/100000000), 0, 0, (2555651/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(12012751/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3534279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (467697/6250000), (40049/25000000), (1/100000000), (387701/6250000), (1/100000000), (322881/10000000)]
    alternative := .zero
    polynomial := [(-948789340550305747160699788824163/431217523917291384624000000000000), (81258226242869/4004900000000), (-9584704959606076555040545944264163/215608761958645692312000000000000), (81258226242869/4004900000000), (-18220620578661847362920392099704163/431217523917291384624000000000000)]
    bernstein := [(261909480310212993722537242299423056957/1103916861228265944637440000000000000000), (2091200255579912952103480491871645961/8491668163294353420288000000000000000), (8303692281413291748914956655996615063/33117505836847978339123200000000000000), (1251738081173512760252702002245881/4995098919584913776640000000000000), (1595849643797000057672393716869229/6493628595460387909632000000000000)]
    reserve := (118627357507/500000000000) }

theorem quarter_042_024_valid : quarter_042_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_024]
  · intro i; fin_cases i <;> norm_num [quarter_042_024]
  · norm_num [quarter_042_024]
  · norm_num [quarter_042_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_024]

def quarter_042_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(12900973/100000000), (1352921/5000000), (11784909/50000000), (11784909/50000000), 0, 0, (12900973/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1661239/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6981571/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7574473/100000000), (160391/100000000), (1/100000000), (3063439/50000000), (1/100000000), (1629909/50000000)]
    alternative := .zero
    polynomial := [(-133745472085241511919323392537596770707/48528291171849854542536744000000000000), (181871210289963/8019550000000), (-1104820258011443672819453462022111090707/24264145585924927271268372000000000000), (181871210289963/8019550000000), (-2075895043937645833719583531506625410707/48528291171849854542536744000000000000)]
    bernstein := [(26624153024669442473978664312999088283/104396996134399687083104256000000000000), (30663056351529713840803138939803508081/115996662371555207870115840000000000000), (1002624216411315573005321299004281074938527/3726972761998068828866821939200000000000000), (33752535567429325561649924954695992677437/125487298383773361241307136000000000000000), (32810912980309734527201760121857722951768413/124232425399935627628894064640000000000000000)]
    reserve := (127513980337/500000000000) }

theorem quarter_042_025_valid : quarter_042_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_025]
  · intro i; fin_cases i <;> norm_num [quarter_042_025]
  · norm_num [quarter_042_025]
  · norm_num [quarter_042_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_025]

def quarter_042_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(13017977/100000000), (13724409/50000000), (11628807/50000000), (11628807/50000000), 0, 0, (13017977/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14578099/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3444547/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (239883/3125000), (160679/100000000), (1/100000000), (3022861/50000000), (1/100000000), (3289383/100000000)]
    alternative := .zero
    polynomial := [(-84401023695810041173923066491925163/24927348668693543986536000000000000), (101083754322437/4016975000000), (-23896461382716496226076115945983891683/511010647708217651723988000000000000), (101083754322437/4016975000000), (-44332480793904780764021386165798851683/1022021295416435303447976000000000000)]
    bernstein := [(714408839094652255380790440688641553171597/2616374516266074376826818560000000000000000), (184918681226810940117380344101405643390181/654093629066518594206704640000000000000000), (141091804897639386542425895527807744449739/490570221799888945655028480000000000000000), (11759735443751624009828864026731665117449/40880851816657412137919040000000000000000), (2889844706755797886230826474613833554277/10220212954164353034479760000000000000000)]
    reserve := (273052972597/1000000000000) }

theorem quarter_042_026_valid : quarter_042_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_026]
  · intro i; fin_cases i <;> norm_num [quarter_042_026]
  · norm_num [quarter_042_026]
  · norm_num [quarter_042_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_026]

def quarter_042_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(2625899/20000000), (1743037/6250000), (22926209/100000000), (22926209/100000000), 0, 0, (2625899/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(127037/800000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6790929/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1557753/20000000), (80531/50000000), (1/100000000), (238383/4000000), (1/100000000), (3317561/100000000)]
    alternative := .zero
    polynomial := [(-541731247799291825056392962659823243/132280132998702454206012000000000000), (22354485409269/805310000000), (-3184709914960306940347857345951863243/66140066499351227103006000000000000), (22354485409269/805310000000), (-5827688582121322055639321729243903243/132280132998702454206012000000000000)]
    bernstein := [(3536038229417040372607574121586546513/12135792018229582954680000000000000000), (14631144475074299169217506417573476323/48543168072918331818720000000000000000), (19463940887643762189721622711872776993091/63494463839377178018885760000000000000000), (25964715143007261688798933108242593615387/84659285119169570691847680000000000000000), (102181350873753825088238914417442679582277/338637140476678282767390720000000000000000)]
    reserve := (11654907151/40000000000) }

theorem quarter_042_027_valid : quarter_042_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_027]
  · intro i; fin_cases i <;> norm_num [quarter_042_027]
  · norm_num [quarter_042_027]
  · norm_num [quarter_042_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_027]

def quarter_042_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(13235931/100000000), (28378653/100000000), (11287371/50000000), (11287371/50000000), 0, 0, (13235931/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(17196771/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3343411/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1582461/20000000), (80769/50000000), (1/100000000), (1467053/25000000), (1/100000000), (668891/20000000)]
    alternative := .zero
    polynomial := [(-6990379053742061136298330619833059/1429327510335697466228000000000000), (164099136191073/5384600000000), (-461789776980491674946525410952809767/9290628817182033530482000000000000), (164099136191073/5384600000000), (-832704626262336555121172523847789767/18581257634364067060964000000000000)]
    bernstein := [(1134393903368464028934461324850311734701/3659078426459385513543680000000000000000), (7621935536303505221293619861325421339707/23784009771986005838033920000000000000000), (298093040958554600102909194097864826821/914769606614846378385920000000000000000), (1939107439090049342887453775450634303747/5946002442996501459508480000000000000000), (954621257114018174871043296931996383033/2973001221498250729754240000000000000000)]
    reserve := (310021751697/1000000000000) }

theorem quarter_042_028_valid : quarter_042_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_028]
  · intro i; fin_cases i <;> norm_num [quarter_042_028]
  · norm_num [quarter_042_028]
  · norm_num [quarter_042_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_028]

def quarter_042_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 2]
    lambda := ![(13337851/100000000), (28919943/100000000), (22202177/100000000), (22202177/100000000), 0, 0, (13337851/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18531769/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1315293/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8047219/100000000), (162109/100000000), (1/100000000), (2885683/50000000), (1/100000000), (3370209/100000000)]
    alternative := .zero
    polynomial := [(-586521414975524072202945886086338959331/101495874368547305939085096000000000000), (108052414908937/3242180000000), (-2610096747513687114905136147113234839331/50747937184273652969542548000000000000), (108052414908937/3242180000000), (-4633672080051850157607326408140130719331/101495874368547305939085096000000000000)]
    bernstein := [(5343171358428637437668397862843440252151069/16239339898967568950253615360000000000000000), (12198926981124963891138187551526602620381/35888043975618936906637824000000000000000), (2693897608174426968050954988554710324962031/7794883151504433096121735372800000000000000), (1986491994066114549230165494988931808837/5742087036099029905062051840000000000000), (141697726812035269175966232387778912205101/415727101413569765126492553216000000000000)]
    reserve := (32902638849/100000000000) }

theorem quarter_042_029_valid : quarter_042_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_042_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_042_029]
  · intro i; fin_cases i <;> norm_num [quarter_042_029]
  · norm_num [quarter_042_029]
  · norm_num [quarter_042_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_042_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_042_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_042_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_042_029]

def quarterTable042 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 0, 0, 2, 2]
  rows := [quarter_042_000, quarter_042_001, quarter_042_002, quarter_042_003, quarter_042_004, quarter_042_005, quarter_042_006, quarter_042_007, quarter_042_008, quarter_042_009, quarter_042_010, quarter_042_011, quarter_042_012, quarter_042_013, quarter_042_014, quarter_042_015, quarter_042_016, quarter_042_017, quarter_042_018, quarter_042_019, quarter_042_020, quarter_042_021, quarter_042_022, quarter_042_023, quarter_042_024, quarter_042_025, quarter_042_026, quarter_042_027, quarter_042_028, quarter_042_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_042_000_valid
    · exact quarter_042_001_valid
    · exact quarter_042_002_valid
    · exact quarter_042_003_valid
    · exact quarter_042_004_valid
    · exact quarter_042_005_valid
    · exact quarter_042_006_valid
    · exact quarter_042_007_valid
    · exact quarter_042_008_valid
    · exact quarter_042_009_valid
    · exact quarter_042_010_valid
    · exact quarter_042_011_valid
    · exact quarter_042_012_valid
    · exact quarter_042_013_valid
    · exact quarter_042_014_valid
    · exact quarter_042_015_valid
    · exact quarter_042_016_valid
    · exact quarter_042_017_valid
    · exact quarter_042_018_valid
    · exact quarter_042_019_valid
    · exact quarter_042_020_valid
    · exact quarter_042_021_valid
    · exact quarter_042_022_valid
    · exact quarter_042_023_valid
    · exact quarter_042_024_valid
    · exact quarter_042_025_valid
    · exact quarter_042_026_valid
    · exact quarter_042_027_valid
    · exact quarter_042_028_valid
    · exact quarter_042_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
