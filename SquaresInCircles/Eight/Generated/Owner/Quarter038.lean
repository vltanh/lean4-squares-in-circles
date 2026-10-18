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

def quarter_038_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_038_000_valid : quarter_038_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_000]
  · intro i; fin_cases i <;> norm_num [quarter_038_000]
  · norm_num [quarter_038_000]
  · norm_num [quarter_038_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_000]

def quarter_038_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_038_001_valid : quarter_038_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_001]
  · intro i; fin_cases i <;> norm_num [quarter_038_001]
  · norm_num [quarter_038_001]
  · norm_num [quarter_038_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_001]

def quarter_038_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-382804973875870721/684552687500000000), (-39204036/10952843), (-1067357661375870721/342276343750000000), (-39204036/10952843), (-1751910348875870721/684552687500000000)]
    bernstein := [(646693971861456324660719/1752454880000000000000000), (155279285836763680907889/438113720000000000000000), (111621009402992369262377/328585290000000000000000), (8894952571565710129429/27382107500000000000000), (2121126590005779963799/6845526875000000000000)]
    reserve := (61971171211/200000000000) }

theorem quarter_038_002_valid : quarter_038_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_002]
  · intro i; fin_cases i <;> norm_num [quarter_038_002]
  · norm_num [quarter_038_002]
  · norm_num [quarter_038_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_002]

def quarter_038_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-556512809540135577/1127647700000000000), (-75237955/22552954), (-1684160509540135577/563823850000000000), (-75237955/22552954), (-2811808209540135577/1127647700000000000)]
    bernstein := [(3477032164953649209663/11276477000000000000000), (13294893098709221172331/45105908000000000000000), (152104840977384548853841/541270896000000000000000), (192793584408782748968639/721694528000000000000000), (730712026497435302482743/2886778112000000000000000)]
    reserve := (253123724147/1000000000000) }

theorem quarter_038_003_valid : quarter_038_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_003]
  · intro i; fin_cases i <;> norm_num [quarter_038_003]
  · norm_num [quarter_038_003]
  · norm_num [quarter_038_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_003]

def quarter_038_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4491503/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (578989/2500000)]
    alternative := .zero
    polynomial := [(-31489286020192343/72373625000000000), (-8983006/2894945), (-103862911020192343/36186812500000000), (-8983006/2894945), (-176236536020192343/72373625000000000)]
    bernstein := [(46648716103417490616537/185276480000000000000000), (4430286397231575186187/18527648000000000000000), (1257891006024344017523/5558294400000000000000), (39528917639300858899/185276480000000000000), (3710003290164412873/18527648000000000000)]
    reserve := (20024146023/100000000000) }

theorem quarter_038_004_valid : quarter_038_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_004]
  · intro i; fin_cases i <;> norm_num [quarter_038_004]
  · norm_num [quarter_038_004]
  · norm_num [quarter_038_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_004]

def quarter_038_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (68290369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-227369526439286957/593044725000000000), (-9755767/3388827), (-820414251439286957/296522362500000000), (-9755767/3388827), (-1413458976439286957/593044725000000000)]
    bernstein := [(10073437836348689809/50606483200000000000), (94768432271642857513/506064832000000000000), (7985100306579547072057/45545834880000000000000), (24779433730114407672827/151819449600000000000000), (229173926598944049100723/1518194496000000000000000)]
    reserve := (75475812619/500000000000) }

theorem quarter_038_005_valid : quarter_038_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_005]
  · intro i; fin_cases i <;> norm_num [quarter_038_005]
  · norm_num [quarter_038_005]
  · norm_num [quarter_038_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_005]

def quarter_038_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (32261287/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4847213/20000000)]
    alternative := .zero
    polynomial := [(-409539937756191047/1211803250000000000), (-64522574/24236065), (-1621343187756191047/605901625000000000), (-64522574/24236065), (-2833146437756191047/1211803250000000000)]
    bernstein := [(465061375391627830838233/3102216320000000000000000), (53877066138430155648537/387777040000000000000000), (4645994352667887962951/36354097500000000000000), (352909745491428925301/3029508125000000000000), (19883491019203713057/189344257812500000000)]
    reserve := (105012379297/1000000000000) }

theorem quarter_038_006_valid : quarter_038_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_006]
  · intro i; fin_cases i <;> norm_num [quarter_038_006]
  · norm_num [quarter_038_006]
  · norm_num [quarter_038_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_006]

def quarter_038_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (60567983/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (192961/781250)]
    alternative := .zero
    polynomial := [(-1842574964421438993/6174752000000000000), (-60567983/24699008), (-8017326964421438993/3087376000000000000), (-60567983/24699008), (-14192078964421438993/6174752000000000000)]
    bernstein := [(100447916887776810183/964805000000000000000), (1449494371116907669837/15436880000000000000000), (15469503753632936448001/185242560000000000000000), (144130879977805249812401/1975920640000000000000000), (983178319156258668795407/15807365120000000000000000)]
    reserve := (3887342671/62500000000) }

theorem quarter_038_007_valid : quarter_038_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_007]
  · intro i; fin_cases i <;> norm_num [quarter_038_007]
  · norm_num [quarter_038_007]
  · norm_num [quarter_038_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_007]

def quarter_038_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(11353863/100000000), (4390509/25000000), (19989737/100000000), (19989737/100000000), (4937691/50000000), (4937691/50000000), (11353863/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8986619/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5284187/100000000), (1743689/100000000), (1/100000000), (35211/625000), (1/100000000), (5429379/100000000)]
    alternative := .zero
    polynomial := [(228719068170249564401513095764789029/4697258451656125083282312000000000000), (-19515649324699/36195860000000), (-4548122120725449471664753686248810971/2348629225828062541641156000000000000), (-19515649324699/36195860000000), (-9324963309621148507731020468262410971/4697258451656125083282312000000000000)]
    bernstein := [(10508694620870749001272304086611881249957/123968882847831754775285760000000000000000), (5305340653204122273168308247119520077753/61984441423915877387642880000000000000000), (777450579364212240040368099838437347700167/9018736227179760159902039040000000000000000), (130184673018173327109378724983109764458881/1503122704529960026650339840000000000000000), (65243534085404697305241273318433782360149/751561352264980013325169920000000000000000)]
    reserve := (42384404777/500000000000) }

theorem quarter_038_008_valid : quarter_038_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_008]
  · intro i; fin_cases i <;> norm_num [quarter_038_008]
  · norm_num [quarter_038_008]
  · norm_num [quarter_038_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_008]

def quarter_038_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(10959497/100000000), (17997597/100000000), (20189773/100000000), (20189773/100000000), (9851931/100000000), (9851931/100000000), (10959497/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6474/78125), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5324443/100000000), (766303/50000000), (1/100000000), (141913/2500000), (1/100000000), (2681357/50000000)]
    alternative := .zero
    polynomial := [(45731275507393368372759705264431563/776285606410745394127244500000000000), (-70962553444089/134067850000000), (-125921424969822360497776757755580491/55448971886481813866231750000000000), (-70962553444089/134067850000000), (-1808631225084906415341634313842558437/776285606410745394127244500000000000)]
    bernstein := [(10907318536557848811293811013105472300203/124205697025719263060359120000000000000000), (4408791764412119176109450426710191650521/49682278810287705224143648000000000000000), (5331010021599810090806825596787152987049/59618734572345246268972377600000000000000), (142855863918068453580349907989248341997/1589832921929206567172596736000000000000), (11453765911050793729969930945180184147/127186633754336525373807738880000000000)]
    reserve := (87816572007/1000000000000) }

theorem quarter_038_009_valid : quarter_038_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_009]
  · intro i; fin_cases i <;> norm_num [quarter_038_009]
  · norm_num [quarter_038_009]
  · norm_num [quarter_038_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_009]

def quarter_038_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(10594349/100000000), (576823/3125000), (4073553/20000000), (4073553/20000000), (9808717/100000000), (9808717/100000000), (10594349/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (761313/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (168053/3125000), (326911/25000000), (1/100000000), (5712227/100000000), (1/100000000), (211573/4000000)]
    alternative := .zero
    polynomial := [(7300923336868796149662256658041659/106233499557693194276948800000000000), (-27592043232877/52893250000000), (-146231878742117449983433770657061381/53116749778846597138474400000000000), (-27592043232877/52893250000000), (-299764680821103696116529797972164421/106233499557693194276948800000000000)]
    bernstein := [(122166508381262819131344691151516031/1338868966733265611564253184000000000), (772127951447337704014336005302634923/8367931042082910072276582400000000000), (189699765775484110584706059191737708733/2039683191507709330117416960000000000000), (79417024093015231182724664414985044599/849867996461545554215590400000000000000), (99434531746879991125921472137435797379/1062334995576931942769488000000000000000)]
    reserve := (45623026381/500000000000) }

theorem quarter_038_010_valid : quarter_038_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_010]
  · intro i; fin_cases i <;> norm_num [quarter_038_010]
  · norm_num [quarter_038_010]
  · norm_num [quarter_038_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_010]

def quarter_038_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(10257267/100000000), (3789113/20000000), (5130813/25000000), (5130813/25000000), (9746697/100000000), (9746697/100000000), (10257267/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3482401/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (871/16000), (1068693/100000000), (1/100000000), (574091/10000000), (1/100000000), (20351/390625)]
    alternative := .zero
    polynomial := [(68064567453625671903346777857271/870016721122601073840000000000000), (-134423582346707/260492800000000), (-3040797347022389278246919348801083/870016721122601073840000000000000), (-134423582346707/260492800000000), (-1554430957238007475075133063329177/435008360561300536920000000000000)]
    bernstein := [(413453177795056056627639181761440423/4350083605613005369200000000000000000), (257474387215699353345453746546146751/2676974526531080227200000000000000000), (20242935842545599280598027032843378871/208804013069424257721600000000000000000), (4169497102942145703341328465885226459/42831592424497283635200000000000000000), (108445564124956111631045623989871544063/1113621403036929374515200000000000000000)]
    reserve := (47522440403/500000000000) }

theorem quarter_038_011_valid : quarter_038_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_011]
  · intro i; fin_cases i <;> norm_num [quarter_038_011]
  · norm_num [quarter_038_011]
  · norm_num [quarter_038_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_011]

def quarter_038_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(4973731/50000000), (1216283/6250000), (20655487/100000000), (20655487/100000000), (9666787/100000000), (9666787/100000000), (4973731/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6340727/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1104491/20000000), (407857/50000000), (1/100000000), (2881261/50000000), (1/100000000), (512499/10000000)]
    alternative := .zero
    polynomial := [(14553301729466721686775360186416557/166297505047519351012523250000000000), (-131272081837157/256249500000000), (-132042484722440961892833492995106231/27716250841253225168753875000000000), (-131272081837157/256249500000000), (-806808210064112493043776318157053943/166297505047519351012523250000000000)]
    bernstein := [(42231360204272016581653173916568015652217/425721612921649538592059520000000000000000), (21384246942157087455138591260912893735039/212860806460824769296029760000000000000000), (3591017482579805542092647185622827733571/35476801076804128216004960000000000000000), (5400509554519755966752913239557407914671/53215201615206192324007440000000000000000), (158473733542870628133768892262538358921/1565152988682535068353160000000000000000)]
    reserve := (9919947431/100000000000) }

theorem quarter_038_012_valid : quarter_038_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_012]
  · intro i; fin_cases i <;> norm_num [quarter_038_012]
  · norm_num [quarter_038_012]
  · norm_num [quarter_038_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_012]

def quarter_038_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(9664501/100000000), (20004407/100000000), (259543/1250000), (259543/1250000), (149529/1562500), (149529/1562500), (9664501/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5739869/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (56137/1000000), (274463/50000000), (1/100000000), (1155389/20000000), (1/100000000), (629431/12500000)]
    alternative := .zero
    polynomial := [(4228486044749885957200147643387/43769279500321981789175781250000), (-23357752011731/45776800000000), (-2585252014629035222294160218796433/350154236002575854313406250000000), (-23357752011731/45776800000000), (-2619079902987034309951761399943529/350154236002575854313406250000000)]
    bernstein := [(23234614975190199670070549183213057459/224098711041648546760580000000000000000), (188431398794755013870159569191562588611/1792789688333188374084640000000000000000), (568801252367294296993038398896505018279/5378369064999565122253920000000000000000), (757563515035182153177161013076514010561/7171158753332753496338560000000000000000), (187804447518286043242538195061249981717/1792789688333188374084640000000000000000)]
    reserve := (1296003381/12500000000) }

theorem quarter_038_013_valid : quarter_038_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_013]
  · intro i; fin_cases i <;> norm_num [quarter_038_013]
  · norm_num [quarter_038_013]
  · norm_num [quarter_038_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_013]

def quarter_038_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(1176037/12500000), (643073/3125000), (4169161/20000000), (4169161/20000000), (9456731/100000000), (9456731/100000000), (1176037/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5161089/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2858703/50000000), (270179/100000000), (1/100000000), (1156797/20000000), (1/100000000), (988397/20000000)]
    alternative := .zero
    polynomial := [(456196267831051000363841757992729/4328914738757529898545750000000000), (-31494088583533/61774812500000), (-33927201597866667407985102636561271/2164457369378764949272875000000000), (-31494088583533/61774812500000), (-1288879235161592185213849943983307/81677636580330752802750000000000)]
    bernstein := [(1200561517476200878833590453381084977529/11082021731219276540277120000000000000000), (95276219087925472908321950941949663/865782947751505979709150000000000000), (2288233148395938176181232551909417929/20778790746036143513019600000000000000), (58748729629985021423641381418113/541114342344691237318218750000000), (456196267831051000363841757992729/4328914738757529898545750000000000)]
    reserve := (105383518817/1000000000000) }

theorem quarter_038_014_valid : quarter_038_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_014]
  · intro i; fin_cases i <;> norm_num [quarter_038_014]
  · norm_num [quarter_038_014]
  · norm_num [quarter_038_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_014]

def quarter_038_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(9320277/100000000), (4192281/20000000), (2619357/12500000), (2619357/12500000), (2311041/25000000), (2311041/25000000), (9320277/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(523953/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (576807/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (724563/12500000), (132403/100000000), (1/100000000), (5787203/100000000), (1/100000000), (1215123/25000000)]
    alternative := .zero
    polynomial := [(156032096887684643348601081240577/1427779438676959271867600000000000), (710516549583596547/766123478900000000), (-1810275814017654154026946508134571/54914593795267664302600000000000), (710516549583596547/766123478900000000), (-47223203261346692648049210292739423/1427779438676959271867600000000000)]
    bernstein := [(156032096887684643348601081240577/1427779438676959271867600000000000), (41077005569809836544785585415063/356944859669239817966900000000000), (804869363237581931244130985377900177/6853341305649404504964480000000000000), (66462621810730013411210004163508363/571111775470783708747040000000000000), (408885912898103034555107714791344146977/3655115363013015735981056000000000000000)]
    reserve := (109283053573/1000000000000) }

theorem quarter_038_015_valid : quarter_038_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_015]
  · intro i; fin_cases i <;> norm_num [quarter_038_015]
  · norm_num [quarter_038_015]
  · norm_num [quarter_038_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_015]

def quarter_038_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(4705807/50000000), (21141077/100000000), (21081701/100000000), (21081701/100000000), (4468073/50000000), (4468073/50000000), (4705807/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(791677/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4079817/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1169473/20000000), (133413/100000000), (1/100000000), (2892863/50000000), (1/100000000), (149843/3125000)]
    alternative := .zero
    polynomial := [(42084330864088405426208005550638381/541056554942854368133128000000000000), (83712404964162932189/31985606654400000000), (-2999621931476545452820375556834018873/90176092490475728022188000000000000), (83712404964162932189/31985606654400000000), (-18039815919723361122348461346554751619/541056554942854368133128000000000000)]
    bernstein := [(169605172763123326905303813397121561627581/1385104780653707182420807680000000000000000), (88944096328920831962494072278432143967781/692552390326853591210403840000000000000000), (45345524650178847808194922602402122598781/346276195163426795605201920000000000000000), (22510376406630447331803398064581105600581/173138097581713397802600960000000000000000), (10873063216262848290909813248620842013181/86569048790856698901300480000000000000000)]
    reserve := (61224672361/500000000000) }

theorem quarter_038_016_valid : quarter_038_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_016]
  · intro i; fin_cases i <;> norm_num [quarter_038_016]
  · norm_num [quarter_038_016]
  · norm_num [quarter_038_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_016]

def quarter_038_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(9544321/100000000), (10667637/50000000), (21169241/100000000), (21169241/100000000), (8618801/100000000), (8618801/100000000), (9544321/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(664133/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (707117/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (73823/1250000), (26869/20000000), (1/100000000), (2887693/50000000), (1/100000000), (4731433/100000000)]
    alternative := .zero
    polynomial := [(287474694916898234583830763825571/108404397324642873443612000000000000), (275767541815074685889/63564436638500000000), (-1822847428210886214930934850043506429/54202198662321436721806000000000000), (275767541815074685889/63564436638500000000), (-3645982331116689328096453530850838429/108404397324642873443612000000000000)]
    bernstein := [(2355885548748269619261820813495198738371/17344703571942859750977920000000000000000), (4926642533876043624251540713874844586713/34689407143885719501955840000000000000000), (4303302275913495216679163539515332019031/29733777551902045287390720000000000000000), (19972311368621263642395299253257507134417/138757628575542878007823360000000000000000), (38748309819544342383661309187742460132051/277515257151085756015646720000000000000000)]
    reserve := (67913687281/500000000000) }

theorem quarter_038_017_valid : quarter_038_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_017]
  · intro i; fin_cases i <;> norm_num [quarter_038_017]
  · norm_num [quarter_038_017]
  · norm_num [quarter_038_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_017]

def quarter_038_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(1943563/20000000), (2693033/12500000), (33947/160000), (33947/160000), (8293179/100000000), (8293179/100000000), (1943563/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4677/125000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (297739/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2985987/50000000), (67599/50000000), (1/100000000), (2878037/50000000), (1/100000000), (2334823/50000000)]
    alternative := .zero
    polynomial := [(-366248883707518705473661789481791/3118094425555589856889800000000000), (916139764946410567/150315904740000000), (-1540227404175603043087061917525254439/45212369170556052924902100000000000), (916139764946410567/150315904740000000), (-1023277863574562681238462547718512313/30141579447037368616601400000000000)]
    bernstein := [(34612209200866004311281555258577468624741/231487330153246990975498752000000000000000), (9025727736363777577503451794335416880047/57871832538311747743874688000000000000000), (6895799364628052273833821833252202027947/43403874403733810807906016000000000000000), (190794624327991547590661183651612098961/1205663177881494744664056000000000000000), (139301002199857613389357220482475285261/904247383411121058498042000000000000000)]
    reserve := (149520965911/1000000000000) }

theorem quarter_038_018_valid : quarter_038_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_018]
  · intro i; fin_cases i <;> norm_num [quarter_038_018]
  · norm_num [quarter_038_018]
  · norm_num [quarter_038_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_018]

def quarter_038_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(9931463/100000000), (10884117/50000000), (21224113/100000000), (21224113/100000000), (7960307/100000000), (7960307/100000000), (9931463/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4836639/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2401033/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1209163/20000000), (13597/10000000), (1/100000000), (2863851/50000000), (1/100000000), (4609279/100000000)]
    alternative := .zero
    polynomial := [(-123313348203572918033223490299058007/434051596811129668634838000000000000), (30905913034657655219/3917022910187500000), (-7503500727971150394201706460426722007/217025798405564834317419000000000000), (30905913034657655219/3917022910187500000), (-14883688107738727870370189430554386007/434051596811129668634838000000000000)]
    bernstein := [(710263860348017887712667140146272182593/4340515968111296686348380000000000000000), (197179376246479326676257391746604894911/1157470924829679116359568000000000000000), (1445931200898919888555913855887777304191/8333790658773689637788889600000000000000), (25639751680632827364466029437928044343/148156278378198926894024704000000000000), (12017533603144269218800961578733187217/71115013621535484909131857920000000000)]
    reserve := (32727162649/200000000000) }

theorem quarter_038_019_valid : quarter_038_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_019]
  · intro i; fin_cases i <;> norm_num [quarter_038_019]
  · norm_num [quarter_038_019]
  · norm_num [quarter_038_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_019]

def quarter_038_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(2546143/25000000), (2750911/12500000), (10595289/50000000), (10595289/50000000), (3810603/50000000), (3810603/50000000), (2546143/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5939707/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (360513/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1225481/20000000), (136661/100000000), (1/100000000), (2845101/50000000), (1/100000000), (284509/6250000)]
    alternative := .zero
    polynomial := [(-2577034337886339298814716975466523/5164348793921107396071200000000000), (30260233774850151861/3110502755920000000), (-90777807392085858305752483546456523/2582174396960553698035600000000000), (30260233774850151861/3110502755920000000), (-178978580446285377312690250117446523/5164348793921107396071200000000000)]
    bernstein := [(150847521799999973935968751323777613/846126906396034235772305408000000000), (1959946015420734437121198169196167763/10576586329950427947153817600000000000), (74850219105079405622401760626545066871/396621987373141048018268160000000000000), (62295609918064064588021931037489941159/330518322810950873348556800000000000000), (152488271017037219817645203561629586037/826295807027377183371392000000000000000)]
    reserve := (89140010003/500000000000) }

theorem quarter_038_020_valid : quarter_038_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_020]
  · intro i; fin_cases i <;> norm_num [quarter_038_020]
  · norm_num [quarter_038_020]
  · norm_num [quarter_038_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_020]

def quarter_038_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(10476377/100000000), (4452289/20000000), (21116009/100000000), (21116009/100000000), (7276891/100000000), (7276891/100000000), (10476377/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1762209/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1178343/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6216783/100000000), (13727/10000000), (1/100000000), (5643533/100000000), (1/100000000), (2249777/50000000)]
    alternative := .zero
    polynomial := [(-16896246991828609643302941905914177/22112396006954446037469000000000000), (71730473376963705743/6176537775800000000), (-2771667133120802197641431162224499239/77393386024340561131141500000000000), (71730473376963705743/6176537775800000000), (-5425060537298804127779741731107599239/154786772048681122262283000000000000)]
    bernstein := [(4793811037247586913392415550971041400841/24765883527788979561965280000000000000000), (9953015393109276710159374916422315960429/49531767055577959123930560000000000000000), (60817092551277138146752853301855874790003/297190602333467754743583360000000000000000), (40541201488761324065018968700778426738869/198127068222311836495722240000000000000000), (11368994631838807521831784565660965187423/56607733777803381855920640000000000000000)]
    reserve := (193565112743/1000000000000) }

theorem quarter_038_021_valid : quarter_038_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_021]
  · intro i; fin_cases i <;> norm_num [quarter_038_021]
  · norm_num [quarter_038_021]
  · norm_num [quarter_038_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_021]

def quarter_038_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(10806033/100000000), (22530643/100000000), (1050013/5000000), (1050013/5000000), (3464193/50000000), (3464193/50000000), (10806033/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2040511/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (262549/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (394623/6250000), (27559/20000000), (1/100000000), (5587677/100000000), (1/100000000), (1111757/25000000)]
    alternative := .zero
    polynomial := [(-16237343195073418993441905789446819/15013242546728950152594000000000000), (415126313510027657653/30638911163000000000), (-274352203594268667475089677575601819/7506621273364475076297000000000000), (415126313510027657653/30638911163000000000), (-532467063993463915956737449361756819/15013242546728950152594000000000000)]
    bernstein := [(8055963507200125336353102462954728098381/38433900919626112390640640000000000000000), (16575853339442103343931298024475424041/76257739919893080140160000000000000000), (99709717929741335580668271287101041883/450397276401868504577820000000000000000), (29812345714753894383835486243464149/134527262963521058715000000000000000), (511359891559625986531453554027927589/2345819147926398461342812500000000000)]
    reserve := (209605668809/1000000000000) }

theorem quarter_038_022_valid : quarter_038_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_022]
  · intro i; fin_cases i <;> norm_num [quarter_038_022]
  · norm_num [quarter_038_022]
  · norm_num [quarter_038_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_022]

def quarter_038_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(1113167/10000000), (2851279/12500000), (20839187/100000000), (20839187/100000000), (6624027/100000000), (6624027/100000000), (1113167/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4637751/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6413399/100000000), (138209/100000000), (1/100000000), (276263/5000000), (1/100000000), (1101263/25000000)]
    alternative := .zero
    polynomial := [(-195827384935708459595125805330240401/134836776207197301582039500000000000), (53663336623631/3455225000000), (-2518294215607173526068060515002419151/67418388103598650791019750000000000), (53663336623631/3455225000000), (-4840761046278638592540995224674597901/134836776207197301582039500000000000)]
    bernstein := [(367175229582726073016694128482746037/1620634329413429105553359375000000000), (3043122153304109331343652877949230283/12965074635307432844426875000000000000), (1933990979078679863724218849481401115241/8090206572431838094922370000000000000000), (10334774337067079785413507871910982614571/43147768386303136506252640000000000000000), (81481197719948664988041626514972267872339/345182147090425092050021120000000000000000)]
    reserve := (226562663099/1000000000000) }

theorem quarter_038_023_valid : quarter_038_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_023]
  · intro i; fin_cases i <;> norm_num [quarter_038_023]
  · norm_num [quarter_038_023]
  · norm_num [quarter_038_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_023]

def quarter_038_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(2264759/20000000), (23096733/100000000), (20630257/100000000), (20630257/100000000), (6497581/100000000), (6497581/100000000), (2264759/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(259629/2500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (81247/1250000), (34623/25000000), (1/100000000), (683161/12500000), (1/100000000), (2200711/50000000)]
    alternative := .zero
    polynomial := [(-3172847095396130771953081026978481/1691679555466193478380400000000000), (337499691273/19235000000), (-32324729675264840184990920028661981/845839777733096739190200000000000), (337499691273/19235000000), (-61476612255133549598028759030345481/1691679555466193478380400000000000)]
    bernstein := [(1058206077546470023499725816125921663959/4330699661993455304653824000000000000000), (109496050037010437635626207292853688191/433069966199345530465382400000000000000), (33445148915333201031588231447692119781/129920989859803659139614720000000000000), (1117583002648264594020579272464657087/4330699661993455304653824000000000000), (110287667484811051814039524714939991/433069966199345530465382400000000000)]
    reserve := (244349911131/1000000000000) }

theorem quarter_038_024_valid : quarter_038_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_024]
  · intro i; fin_cases i <;> norm_num [quarter_038_024]
  · norm_num [quarter_038_024]
  · norm_num [quarter_038_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_024]

def quarter_038_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(359389/3125000), (11705411/50000000), (20392499/100000000), (20392499/100000000), (3200821/50000000), (3200821/50000000), (359389/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2874593/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (411917/6250000), (13877/10000000), (1/100000000), (5400707/100000000), (1/100000000), (4399551/100000000)]
    alternative := .zero
    polynomial := [(-1895281423481348483420105968029311/803669658631070776677000000000000), (34047271814963/1734625000000), (-15744635424224066147059417500518311/401834829315535388338500000000000), (34047271814963/1734625000000), (-3288221047218531534522081003667479/89296628736785641853000000000000)]
    bernstein := [(54048388830384801167116580855575121/205739432609554118829312000000000000), (558690325747078395321428342995226923/2057394326095541188293120000000000000), (17060853474432814451727967438085588171/61721829782866235648793600000000000000), (57036006313462133052884101605855222499/205739432609554118829312000000000000000), (563517378346963034600507441313214740449/2057394326095541188293120000000000000000)]
    reserve := (131351555083/500000000000) }

theorem quarter_038_025_valid : quarter_038_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_025]
  · intro i; fin_cases i <;> norm_num [quarter_038_025]
  · norm_num [quarter_038_025]
  · norm_num [quarter_038_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_025]

def quarter_038_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(11662771/100000000), (2375389/10000000), (20126871/100000000), (20126871/100000000), (3166707/50000000), (3166707/50000000), (11662771/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(12615719/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3343281/50000000), (2781/2000000), (1/100000000), (5331507/100000000), (1/100000000), (274939/6250000)]
    alternative := .zero
    polynomial := [(-17591262170284636735624986279716593/6057280472867730706068000000000000), (30291581801201/1390500000000), (-121921998613427128882589861958751093/3028640236433865353034000000000000), (30291581801201/1390500000000), (-226252735056569621029554737637785593/6057280472867730706068000000000000)]
    bernstein := [(161772266144545649976003302602335899381/574319926316347800279040000000000000000), (375931243359841333432496801845397058517/1292219834211782550627840000000000000000), (860836367713267842265007197676259712769/2907494626976510738912640000000000000000), (71977173230581448201801163150791117179/242291218914709228242720000000000000000), (17796932901714354191279668767736589567/60572804728677307060680000000000000000)]
    reserve := (140838110199/500000000000) }

theorem quarter_038_026_valid : quarter_038_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_026]
  · intro i; fin_cases i <;> norm_num [quarter_038_026]
  · norm_num [quarter_038_026]
  · norm_num [quarter_038_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_026]

def quarter_038_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(36913/312500), (2412743/10000000), (19834293/100000000), (19834293/100000000), (786229/12500000), (786229/12500000), (36913/312500)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13738039/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6787927/100000000), (139341/100000000), (1/100000000), (1051539/20000000), (1/100000000), (2199709/50000000)]
    alternative := .zero
    polynomial := [(-1710006734698293781449082320351896759/486176752845681495059146000000000000), (33475541068289/1393410000000), (-10074970993541405612399858450536996759/243088376422840747529573000000000000), (33475541068289/1393410000000), (-18439935252384517443350634580722096759/486176752845681495059146000000000000)]
    bernstein := [(1464952588160292151506110428296266406321/4861767528456814950591460000000000000000), (18143523130375744073304725882953548455273/58341210341481779407097520000000000000000), (24616895164752515896644201696554252283461/77788280455309039209463360000000000000000), (296511653188245179344080557143004132994293/933459365463708470513560320000000000000000), (1174123657426527248128745790881275108477003/3733837461854833882054241280000000000000000)]
    reserve := (75330246643/250000000000) }

theorem quarter_038_027_valid : quarter_038_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_027]
  · intro i; fin_cases i <;> norm_num [quarter_038_027]
  · norm_num [quarter_038_027]
  · norm_num [quarter_038_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_027]

def quarter_038_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(2390033/20000000), (24533013/100000000), (19515601/100000000), (19515601/100000000), (391733/6250000), (391733/6250000), (2390033/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14866407/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3447659/50000000), (1091/781250), (1/100000000), (5179281/100000000), (1/100000000), (440033/10000000)]
    alternative := .zero
    polynomial := [(-230552458339238691564800044916443039/54863530375016613526636800000000000), (368055389478131/13964800000000), (-1172924389924501721524865554940284789/27431765187508306763318400000000000), (368055389478131/13964800000000), (-2115296321509764751484931064964126539/54863530375016613526636800000000000)]
    bernstein := [(740673321059828603181098867392939002761/2302469471476107059478528000000000000000), (127332602813901603806436494410290182093/383744911912684509913088000000000000000), (35564476993257967069960314825211668295823/105337978320031897971142656000000000000000), (1983947650556563886801989446791387202233/5852109906668438776174592000000000000000), (2948431321621705624195811266556900521061/8778164860002658164261888000000000000000)]
    reserve := (160843244663/500000000000) }

theorem quarter_038_028_valid : quarter_038_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_028]
  · intro i; fin_cases i <;> norm_num [quarter_038_028]
  · norm_num [quarter_038_028]
  · norm_num [quarter_038_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_028]

def quarter_038_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 2]
    lambda := ![(6039209/50000000), (12486133/50000000), (19171499/100000000), (19171499/100000000), (125279/2000000), (125279/2000000), (6039209/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3200423/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7009319/100000000), (139981/100000000), (1/100000000), (5096271/100000000), (1/100000000), (440139/10000000)]
    alternative := .zero
    polynomial := [(-105562921708816330234056657548515859/21264096470390613915026000000000000), (201495285201353/6999050000000), (-1409806446555304986027971798405947577/31896144705585920872539000000000000), (201495285201353/6999050000000), (-2502924127984160981353773624166347577/63792289411171841745078000000000000)]
    bernstein := [(3499064360972756297085279140374402929223/10206766305787494679212480000000000000000), (1443006090421459945213871621915564244787/4082706522314997871684992000000000000000), (1761816335010106229290889951016272248477/4899247826777997446021990400000000000000), (78652342156154712400455980077099995033/217744347856799886489866240000000000000), (31193173991565012086967247741291307389/87097739142719954595946496000000000000)]
    reserve := (171409056313/500000000000) }

theorem quarter_038_029_valid : quarter_038_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_038_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_038_029]
  · intro i; fin_cases i <;> norm_num [quarter_038_029]
  · norm_num [quarter_038_029]
  · norm_num [quarter_038_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_038_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_038_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_038_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_038_029]

def quarterTable038 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 0, 0, 0, 2]
  rows := [quarter_038_000, quarter_038_001, quarter_038_002, quarter_038_003, quarter_038_004, quarter_038_005, quarter_038_006, quarter_038_007, quarter_038_008, quarter_038_009, quarter_038_010, quarter_038_011, quarter_038_012, quarter_038_013, quarter_038_014, quarter_038_015, quarter_038_016, quarter_038_017, quarter_038_018, quarter_038_019, quarter_038_020, quarter_038_021, quarter_038_022, quarter_038_023, quarter_038_024, quarter_038_025, quarter_038_026, quarter_038_027, quarter_038_028, quarter_038_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_038_000_valid
    · exact quarter_038_001_valid
    · exact quarter_038_002_valid
    · exact quarter_038_003_valid
    · exact quarter_038_004_valid
    · exact quarter_038_005_valid
    · exact quarter_038_006_valid
    · exact quarter_038_007_valid
    · exact quarter_038_008_valid
    · exact quarter_038_009_valid
    · exact quarter_038_010_valid
    · exact quarter_038_011_valid
    · exact quarter_038_012_valid
    · exact quarter_038_013_valid
    · exact quarter_038_014_valid
    · exact quarter_038_015_valid
    · exact quarter_038_016_valid
    · exact quarter_038_017_valid
    · exact quarter_038_018_valid
    · exact quarter_038_019_valid
    · exact quarter_038_020_valid
    · exact quarter_038_021_valid
    · exact quarter_038_022_valid
    · exact quarter_038_023_valid
    · exact quarter_038_024_valid
    · exact quarter_038_025_valid
    · exact quarter_038_026_valid
    · exact quarter_038_027_valid
    · exact quarter_038_028_valid
    · exact quarter_038_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
