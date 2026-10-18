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

def quarter_046_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_046_000_valid : quarter_046_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_000]
  · intro i; fin_cases i <;> norm_num [quarter_046_000]
  · norm_num [quarter_046_000]
  · norm_num [quarter_046_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_000]

def quarter_046_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_046_001_valid : quarter_046_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_001]
  · intro i; fin_cases i <;> norm_num [quarter_046_001]
  · norm_num [quarter_046_001]
  · norm_num [quarter_046_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_001]

def quarter_046_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-382804973875870721/684552687500000000), (-39204036/10952843), (-1067357661375870721/342276343750000000), (-39204036/10952843), (-1751910348875870721/684552687500000000)]
    bernstein := [(646693971861456324660719/1752454880000000000000000), (155279285836763680907889/438113720000000000000000), (111621009402992369262377/328585290000000000000000), (8894952571565710129429/27382107500000000000000), (2121126590005779963799/6845526875000000000000)]
    reserve := (61971171211/200000000000) }

theorem quarter_046_002_valid : quarter_046_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_002]
  · intro i; fin_cases i <;> norm_num [quarter_046_002]
  · norm_num [quarter_046_002]
  · norm_num [quarter_046_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_002]

def quarter_046_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-556512809540135577/1127647700000000000), (-75237955/22552954), (-1684160509540135577/563823850000000000), (-75237955/22552954), (-2811808209540135577/1127647700000000000)]
    bernstein := [(3477032164953649209663/11276477000000000000000), (13294893098709221172331/45105908000000000000000), (152104840977384548853841/541270896000000000000000), (192793584408782748968639/721694528000000000000000), (730712026497435302482743/2886778112000000000000000)]
    reserve := (253123724147/1000000000000) }

theorem quarter_046_003_valid : quarter_046_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_003]
  · intro i; fin_cases i <;> norm_num [quarter_046_003]
  · norm_num [quarter_046_003]
  · norm_num [quarter_046_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_003]

def quarter_046_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4491503/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (578989/2500000)]
    alternative := .zero
    polynomial := [(-31489286020192343/72373625000000000), (-8983006/2894945), (-103862911020192343/36186812500000000), (-8983006/2894945), (-176236536020192343/72373625000000000)]
    bernstein := [(46648716103417490616537/185276480000000000000000), (4430286397231575186187/18527648000000000000000), (1257891006024344017523/5558294400000000000000), (39528917639300858899/185276480000000000000), (3710003290164412873/18527648000000000000)]
    reserve := (20024146023/100000000000) }

theorem quarter_046_004_valid : quarter_046_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_004]
  · intro i; fin_cases i <;> norm_num [quarter_046_004]
  · norm_num [quarter_046_004]
  · norm_num [quarter_046_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_004]

def quarter_046_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (68290369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-227369526439286957/593044725000000000), (-9755767/3388827), (-820414251439286957/296522362500000000), (-9755767/3388827), (-1413458976439286957/593044725000000000)]
    bernstein := [(10073437836348689809/50606483200000000000), (94768432271642857513/506064832000000000000), (7985100306579547072057/45545834880000000000000), (24779433730114407672827/151819449600000000000000), (229173926598944049100723/1518194496000000000000000)]
    reserve := (75475812619/500000000000) }

theorem quarter_046_005_valid : quarter_046_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_005]
  · intro i; fin_cases i <;> norm_num [quarter_046_005]
  · norm_num [quarter_046_005]
  · norm_num [quarter_046_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_005]

def quarter_046_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (32261287/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4847213/20000000)]
    alternative := .zero
    polynomial := [(-409539937756191047/1211803250000000000), (-64522574/24236065), (-1621343187756191047/605901625000000000), (-64522574/24236065), (-2833146437756191047/1211803250000000000)]
    bernstein := [(465061375391627830838233/3102216320000000000000000), (53877066138430155648537/387777040000000000000000), (4645994352667887962951/36354097500000000000000), (352909745491428925301/3029508125000000000000), (19883491019203713057/189344257812500000000)]
    reserve := (105012379297/1000000000000) }

theorem quarter_046_006_valid : quarter_046_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_006]
  · intro i; fin_cases i <;> norm_num [quarter_046_006]
  · norm_num [quarter_046_006]
  · norm_num [quarter_046_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_006]

def quarter_046_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(80397/1250000), (4701727/50000000), (10847609/100000000), (22295139/100000000), (22295139/100000000), (22295139/100000000), (80397/1250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9718063/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (575739/20000000), (1065419/100000000), (1252991/20000000), (1/100000000), (1/100000000), (7410801/100000000)]
    alternative := .zero
    polynomial := [(57313792088368538140045558276743887/949309745246598399906838500000000000), (-16823208457849/61756675000000), (-366341598417421137279505055462501113/474654872623299199953419250000000000), (-16823208457849/61756675000000), (-789996988923210812699055669201746113/949309745246598399906838500000000000)]
    bernstein := [(12583094766939403756283527796286881903/148329647694780999985443515625000000000), (22419804391710812651794421453053399713/263697151457388444418566250000000000000), (2424326300470402205205428997840803033591/28479292357397951997205155000000000000000), (169060408259811123026747557987842846897/1985484434502689463857440000000000000000), (12163891025687800736221407705253792787311/142954879284193641397735680000000000000000)]
    reserve := (84831960181/1000000000000) }

theorem quarter_046_007_valid : quarter_046_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_007]
  · intro i; fin_cases i <;> norm_num [quarter_046_007]
  · norm_num [quarter_046_007]
  · norm_num [quarter_046_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_007]

def quarter_046_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(1567869/25000000), (4847241/50000000), (2758353/25000000), (5560763/25000000), (5560763/25000000), (5560763/25000000), (1567869/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1168527/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (291749/10000000), (962389/100000000), (1568461/25000000), (1/100000000), (1/100000000), (461451/6250000)]
    alternative := .zero
    polynomial := [(3317437387196360050999037868595027/50804168887466065073217750000000000), (-420375044823/1538170000000), (-23302070918005127281956291120631223/25402084443733032536608875000000000), (-420375044823/1538170000000), (-49921579223206614614911620109857473/50804168887466065073217750000000000)]
    bernstein := [(11129789656630400541980211041334332560927/130058672351913126587437440000000000000000), (5582666395131780310864118117785616310883/65029336175956563293718720000000000000000), (8390959374712578591897549898171113385621/97544004263934844940578080000000000000000), (1399729923775292377290878951148561873803/16257334043989140823429680000000000000000), (699698384122084129777865390044722559087/8128667021994570411714840000000000000000)]
    reserve := (133711163/1562500000) }

theorem quarter_046_008_valid : quarter_046_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_008]
  · intro i; fin_cases i <;> norm_num [quarter_046_008]
  · norm_num [quarter_046_008]
  · norm_num [quarter_046_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_008]

def quarter_046_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(613161/10000000), (2502769/25000000), (11221279/100000000), (22168141/100000000), (22168141/100000000), (22168141/100000000), (613161/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4493043/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2966363/100000000), (170273/20000000), (1569547/25000000), (1/100000000), (1/100000000), (3675029/50000000)]
    alternative := .zero
    polynomial := [(3194217159458444555305739033611579/45522405701785475597584953125000000), (-50565788315819/183751450000000), (-4960198879187241985707764544155823/4441210312369314692447312500000000), (-50565788315819/183751450000000), (-216145022684510699635241302444835059/182089622807141902390339812500000000)]
    bernstein := [(2524327908275458889606306078773946670421/29134339649142704382454370000000000000000), (1013906205203653672594723386572436065397/11653735859657081752981748000000000000000), (58096071675103630115012133342499381183/665927763408976100170385600000000000000), (32578438568841437968832875209653887629/372919547509026616095415936000000000000), (2606350205691296270839592023019277829/29833563800722129287633274880000000000)]
    reserve := (8664441819/100000000000) }

theorem quarter_046_009_valid : quarter_046_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_009]
  · intro i; fin_cases i <;> norm_num [quarter_046_009]
  · norm_num [quarter_046_009]
  · norm_num [quarter_046_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_009]

def quarter_046_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(6010577/100000000), (5176873/50000000), (2852523/25000000), (22071669/100000000), (22071669/100000000), (22071669/100000000), (6010577/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4315023/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3025067/100000000), (18293/2500000), (1255643/20000000), (1/100000000), (1/100000000), (7311553/100000000)]
    alternative := .zero
    polynomial := [(19058273623201254042677764304222599/254018735045421004124174500000000000), (-101637740625809/365577650000000), (-178223038673319248133557395803893401/127009367522710502062087250000000000), (-101637740625809/365577650000000), (-375504350969839750309792555912009401/254018735045421004124174500000000000)]
    bernstein := [(3663926745558614393003815041314792031/41618429549841777315704750080000000000), (23015462500462592442796449935599710547/260115184686511108223154688000000000000), (432983095686090462392636653463647856513/4877159712872083279184150400000000000000), (180710300688384460937507781965152185419/2032149880363368032993396000000000000000), (225891025129614628060274287841305000399/2540187350454210041241745000000000000000)]
    reserve := (44018080273/500000000000) }

theorem quarter_046_010_valid : quarter_046_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_010]
  · intro i; fin_cases i <;> norm_num [quarter_046_010]
  · norm_num [quarter_046_010]
  · norm_num [quarter_046_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_010]

def quarter_046_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(5907207/100000000), (1340381/12500000), (2899647/25000000), (439093/2000000), (439093/2000000), (439093/2000000), (5907207/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1034839/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (773359/25000000), (602853/100000000), (627407/10000000), (1/100000000), (1/100000000), (7267919/100000000)]
    alternative := .zero
    polynomial := [(42472968267803772850965778115993231/531486230460267611572122750000000000), (-25596569258951/90848987500000), (-489747222465864546178779326227821769/265743115230133805786061375000000000), (-25596569258951/90848987500000), (-1021967413199532865208524430571636769/531486230460267611572122750000000000)]
    bernstein := [(477001192980749706500966568423364119431/5314862304602676115721227500000000000000), (1919442003692844973710952391081524441393/21259449218410704462884910000000000000000), (23120756383079114608061754732011793473537/255113390620928453554618920000000000000000), (30878533309572246075671907036944679037637/340151187494571271406158560000000000000000), (123456154269507458625665523242795944234511/1360604749978285085624634240000000000000000)]
    reserve := (89748551447/1000000000000) }

theorem quarter_046_011_valid : quarter_046_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_011]
  · intro i; fin_cases i <;> norm_num [quarter_046_011]
  · norm_num [quarter_046_011]
  · norm_num [quarter_046_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_011]

def quarter_046_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(582071/10000000), (5559793/50000000), (1473171/12500000), (174543/800000), (174543/800000), (174543/800000), (582071/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1982717/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3171369/100000000), (116057/25000000), (250633/4000000), (1/100000000), (1/100000000), (1804843/25000000)]
    alternative := .zero
    polynomial := [(7064119616339009931634972891632643/83246465474240255591713500000000000), (-25839517289533/90242150000000), (-107959059228654632195767425041766107/41623232737120127795856750000000000), (-25839517289533/90242150000000), (-222982238073648274323169822975164857/83246465474240255591713500000000000)]
    bernstein := [(19559196931807000709200157112341393444983/213110951614055054314786560000000000000000), (9847801309224270895364203600606810154861/106555475807027527157393280000000000000000), (14830390113268259877032192195658373225261/159833213710541290736089920000000000000000), (2474297514024158454257787347477708401429/26638868951756881789348320000000000000000), (1234836881398505270339425379794362229543/13319434475878440894674160000000000000000)]
    reserve := (18355881557/200000000000) }

theorem quarter_046_012_valid : quarter_046_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_012]
  · intro i; fin_cases i <;> norm_num [quarter_046_012]
  · norm_num [quarter_046_012]
  · norm_num [quarter_046_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_012]

def quarter_046_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(5750643/100000000), (2886003/25000000), (2393781/20000000), (5415483/25000000), (5415483/25000000), (5415483/25000000), (5750643/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7585391/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3258829/100000000), (157737/50000000), (156337/2500000), (1/100000000), (1/100000000), (3583063/50000000)]
    alternative := .zero
    polynomial := [(17252478658149090652974928830027751/191964140300599662375842000000000000), (-19006596793767/65146600000000), (-397477782570582554504580680341472249/95982070150299831187921000000000000), (-19006596793767/65146600000000), (-812208043799314199662136289512972249/191964140300599662375842000000000000)]
    bernstein := [(2890768367225853410316366630514785188551/30714262448095945980134720000000000000000), (5828488443892210167701301863094055398951/61428524896191891960269440000000000000000), (5013270479387791270469200429332312629779/52653021339593050251659520000000000000000), (23370604501760200909372779018034827560151/245714099584767567841077760000000000000000), (46480213289258567615887139496152809990951/491428199169535135682155520000000000000000)]
    reserve := (94118111157/1000000000000) }

theorem quarter_046_013_valid : quarter_046_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_013]
  · intro i; fin_cases i <;> norm_num [quarter_046_013]
  · norm_num [quarter_046_013]
  · norm_num [quarter_046_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_013]

def quarter_046_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(2848441/50000000), (479881/4000000), (12147547/100000000), (21487221/100000000), (21487221/100000000), (21487221/100000000), (2848441/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1448237/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (134233/4000000), (157143/100000000), (779621/12500000), (1/100000000), (1/100000000), (7108397/100000000)]
    alternative := .zero
    polynomial := [(3697010450839898490197030799925759/38966220648256012982101000000000000), (-10590570476151/35541985000000), (-527562400358529268092838347529667723/58449330972384019473151500000000000), (-10590570476151/35541985000000), (-1066215832069578231656267787459112723/116898661944768038946303000000000000)]
    bernstein := [(28934460864436155208047091149966225293677/299260574578606179702535680000000000000000), (18263286651236560515562241925787911727/187037859111628862314084800000000000000), (54799350458036850376874292978789261877/561113577334886586942254400000000000000), (3769578588558677704993207459904509/38966220648256012982101000000000000), (3697010450839898490197030799925759/38966220648256012982101000000000000)]
    reserve := (4743865827/50000000000) }

theorem quarter_046_014_valid : quarter_046_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_014]
  · intro i; fin_cases i <;> norm_num [quarter_046_014]
  · norm_num [quarter_046_014]
  · norm_num [quarter_046_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_014]

def quarter_046_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(5814771/100000000), (497799/4000000), (12441087/100000000), (4232293/20000000), (4232293/20000000), (4232293/20000000), (5814771/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(77769/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (862393/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (867729/25000000), (78609/100000000), (3101353/50000000), (1/100000000), (1/100000000), (7052521/100000000)]
    alternative := .zero
    polynomial := [(65716414153724080465192946202367/676617737872280016254600000000000), (728486321962349241/1319980055450000000), (-322320222659069612194871503976088017/16577134577870860398237700000000000), (728486321962349241/1319980055450000000), (-647860549611671704332537462316092017/33154269155741720796475400000000000)]
    bernstein := [(65716414153724080465192946202367/676617737872280016254600000000000), (119088004485514404083259746502511/1184081041276490028445550000000000), (16232034774091298479971967409102150383/159140491947560259823081920000000000000), (1344722050180548100756130319992099777/13261707662296688318590160000000000000), (8383171001623805856940739290783594413583/84874929038698805238977024000000000000000)]
    reserve := (97124876389/1000000000000) }

theorem quarter_046_015_valid : quarter_046_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_015]
  · intro i; fin_cases i <;> norm_num [quarter_046_015]
  · norm_num [quarter_046_015]
  · norm_num [quarter_046_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_015]

def quarter_046_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(3055179/50000000), (6434037/50000000), (12831933/100000000), (5173273/25000000), (5173273/25000000), (5173273/25000000), (3055179/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(771/80000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3268863/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (179973/5000000), (40603/50000000), (6152447/100000000), (1/100000000), (1/100000000), (1400381/20000000)]
    alternative := .zero
    polynomial := [(3577795816674516538588352045319/46022846133635713727875000000000), (780513131279093727/490169566750000000), (-5383575162633435261304277478771/267574686823463451906250000000), (780513131279093727/490169566750000000), (-929552723789625381482924078393931/46022846133635713727875000000000)]
    bernstein := [(12369755513534363588950797278767726869/117818486102107427143360000000000000000), (6401391803680969530240841446671444169/58909243051053713571680000000000000000), (463907899101927466666053838486868667/4207803075075265255120000000000000000), (1616183937526314105509322143912556369/14727310762763428392920000000000000000), (788863019681740000249732194370831269/7363655381381714196460000000000000000)]
    reserve := (104989937681/1000000000000) }

theorem quarter_046_016_valid : quarter_046_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_016]
  · intro i; fin_cases i <;> norm_num [quarter_046_016]
  · norm_num [quarter_046_016]
  · norm_num [quarter_046_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_016]

def quarter_046_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(6432573/100000000), (13296347/100000000), (6596437/50000000), (20215211/100000000), (20215211/100000000), (20215211/100000000), (6432573/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(206947/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1536293/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3732237/100000000), (3349/4000000), (6099523/100000000), (1/100000000), (1/100000000), (6950999/100000000)]
    alternative := .zero
    polynomial := [(3992064573999053193184690066006207/132485231672483577371525250000000000), (7145031735375212099/2645329051250000000), (-1380024694848445743410159496256011143/66242615836241788685762625000000000), (7145031735375212099/2645329051250000000), (-2764041454270890540013503682578028493/132485231672483577371525250000000000)]
    bernstein := [(2401843456500497495516695988163931133107/21197637067597372379444040000000000000000), (4969965649195532596994489569000112297521/42395274135194744758888080000000000000000), (30267899585307533277938478336337989264289/254371644811168468553328480000000000000000), (20109984203363268303734812858945827633689/169581096540778979035552320000000000000000), (39343318373240692491387193074560824317667/339162193081557958071104640000000000000000)]
    reserve := (113307131773/1000000000000) }

theorem quarter_046_017_valid : quarter_046_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_017]
  · intro i; fin_cases i <;> norm_num [quarter_046_017]
  · norm_num [quarter_046_017]
  · norm_num [quarter_046_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_017]

def quarter_046_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(3391869/50000000), (2746453/20000000), (13523587/100000000), (19725557/100000000), (19725557/100000000), (19725557/100000000), (3391869/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2384887/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1143593/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1935083/50000000), (3447/4000000), (1510787/25000000), (1/100000000), (1/100000000), (3449569/50000000)]
    alternative := .zero
    polynomial := [(-672474169336658235241773588095381/13904934513203263829641200000000000), (5766743484636811081/1486333042875000000), (-50031614853999496540830123026168327/2317489085533877304940200000000000), (5766743484636811081/1486333042875000000), (-299517214954660321009738964568914581/13904934513203263829641200000000000)]
    bernstein := [(4347947820989306390097111699844648962139/35596632353800355403881472000000000000000), (374762994396399320454286824679293701971/2966386029483362950323456000000000000000), (95142807212370668307475592758009052557/741596507370840737580864000000000000000), (23732735415193719244483441942141544519/185399126842710184395216000000000000000), (17445268416128633744523276730683511219/139049345132032638296412000000000000000)]
    reserve := (122144920277/1000000000000) }

theorem quarter_046_018_valid : quarter_046_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_018]
  · intro i; fin_cases i <;> norm_num [quarter_046_018]
  · norm_num [quarter_046_018]
  · norm_num [quarter_046_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_018]

def quarter_046_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(3582959/50000000), (7088967/50000000), (691177/5000000), (1922223/10000000), (1922223/10000000), (1922223/10000000), (3582959/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1575083/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (656553/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1003517/25000000), (88559/100000000), (5982619/100000000), (1/100000000), (1/100000000), (3422801/50000000)]
    alternative := .zero
    polynomial := [(-292174482076052345335428166459694467/1819828382050071141265457000000000000), (9721855322816178839/1894498960993750000), (-20376732554418056957885212099833904467/909914191025035570632728500000000000), (9721855322816178839/1894498960993750000), (-40461290626760061570434996033208114467/1819828382050071141265457000000000000)]
    bernstein := [(2394508145763933051972693127582261522133/18198283820500711412654570000000000000000), (1980921319826931943434516021972616785473/14558627056400569130123656000000000000000), (1610069204875430928906923714335999456057/11646901645120455304098924800000000000000), (257329682283999937041578031317370010249/1863504263219272848655827968000000000000), (40427230330319642065200897999050159077/298160682115083655784932474880000000000)]
    reserve := (131578788933/1000000000000) }

theorem quarter_046_019_valid : quarter_046_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_019]
  · intro i; fin_cases i <;> norm_num [quarter_046_019]
  · norm_num [quarter_046_019]
  · norm_num [quarter_046_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_019]

def quarter_046_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(7580919/100000000), (14635139/100000000), (14092017/100000000), (18703669/100000000), (18703669/100000000), (18703669/100000000), (7580919/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(123437/3125000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4744797/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2082341/50000000), (45441/50000000), (5917311/100000000), (1/100000000), (1/100000000), (6791291/100000000)]
    alternative := .zero
    polynomial := [(-130725907962653354737917739465194551/422507046286176850636209000000000000), (11725992560320248319/1815312084300000000), (-4912628200695682512095050676086427051/211253523143088425318104500000000000), (11725992560320248319/1815312084300000000), (-9694530493428711669452183612707659551/422507046286176850636209000000000000)]
    bernstein := [(4931315048295834453134549492851829/34803194803181103674327040000000000), (42255188861519850464442222218720632477/288431476931363396700985344000000000000), (4832051321931813812037722490446848195627/32448541154778382128860851200000000000000), (366066141226599161554395040193580803953/2458222814755938040065216000000000000000), (761674312881909183025636936495161573013/5200086723522176623214880000000000000000)]
    reserve := (141691447471/1000000000000) }

theorem quarter_046_020_valid : quarter_046_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_020]
  · intro i; fin_cases i <;> norm_num [quarter_046_020]
  · norm_num [quarter_046_020]
  · norm_num [quarter_046_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_020]

def quarter_046_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(8030289/100000000), (15105369/100000000), (716407/5000000), (18168637/100000000), (18168637/100000000), (18168637/100000000), (8030289/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(956589/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6549/156250), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2161329/50000000), (11643/12500000), (2923331/50000000), (1/100000000), (1/100000000), (6736941/100000000)]
    alternative := .zero
    polynomial := [(-54857669580074299075351630378867303/110132120269913123024586000000000000), (18284244300087484591/2324094935200000000), (-1331305565298837927663280134217342303/55066060134956561512293000000000000), (18284244300087484591/2324094935200000000), (-2607753461017601556251208638055817303/110132120269913123024586000000000000)]
    bernstein := [(2688516654627042792754837623125367186857/17621139243186099683933760000000000000000), (5558900970444619845610438939811026905433/35242278486372199367867520000000000000000), (349687212157176427309226958646179960923/2179934751734362847496960000000000000000), (1331597039788312445792276715464844628489/8292300820322870439498240000000000000000), (27050259311082909526798002601026167353/170975274645832380195840000000000000000)]
    reserve := (152573373237/1000000000000) }

theorem quarter_046_021_valid : quarter_046_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_021]
  · intro i; fin_cases i <;> norm_num [quarter_046_021]
  · norm_num [quarter_046_021]
  · norm_num [quarter_046_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_021]

def quarter_046_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(266103/3125000), (1558983/10000000), (7265449/50000000), (8808113/50000000), (8808113/50000000), (8808113/50000000), (266103/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5647637/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1794263/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4488561/100000000), (47673/50000000), (90159/1562500), (1/100000000), (1/100000000), (1669719/25000000)]
    alternative := .zero
    polynomial := [(-24194459696152612631282997558713/33141016449974367222750000000000), (8277471477352214833/884450154300000000), (-416996387650389817349266641341213/16570508224987183611375000000000), (8277471477352214833/884450154300000000), (-809798315604627022067250285123713/33141016449974367222750000000000)]
    bernstein := [(820078771206106375431933926460634511/4990647183054963534720000000000000000), (2207685115542377051911308720524501/12996477039205634205000000000000000), (343676775088813830890296905728939207/1988460986998462033365000000000000000), (4783233744163452612206810240479439/27617513708311972685625000000000000), (885012613144976901917994731361253/5178283820308494878554687500000000)]
    reserve := (82161565537/500000000000) }

theorem quarter_046_022_valid : quarter_046_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_022]
  · intro i; fin_cases i <;> norm_num [quarter_046_022]
  · norm_num [quarter_046_022]
  · norm_num [quarter_046_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_022]

def quarter_046_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(9036897/100000000), (8044733/50000000), (14699167/100000000), (8522929/50000000), (8522929/50000000), (8522929/50000000), (9036897/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(817823/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2932953/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4662863/100000000), (97487/100000000), (1137483/20000000), (1/100000000), (1/100000000), (3308087/50000000)]
    alternative := .zero
    polynomial := [(-862805590654933110978449355886498651/855246298401699709877950500000000000), (705536250719738516461/64499095473800000000), (-11214593976850921781501384644839501151/427623149200849854938975250000000000), (705536250719738516461/64499095473800000000), (-21566382363046910452024319933792503651/855246298401699709877950500000000000)]
    bernstein := [(1819945482363797356140613999017321287/10279402625020429205263828125000000000), (391300490269027287868151980169676455233/2138115746004249274694876250000000000000), (2042257209254141722404319859743764511/10962353750075193888630000000000000000), (25570931962177975378746977157786922425473/136839407744271953580472080000000000000000), (31103132619274003607623101863755609134353/168417732608334712099042560000000000000000)]
    reserve := (177047786603/1000000000000) }

theorem quarter_046_023_valid : quarter_046_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_023]
  · intro i; fin_cases i <;> norm_num [quarter_046_023]
  · norm_num [quarter_046_023]
  · norm_num [quarter_046_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_023]

def quarter_046_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(1876301/10000000), (34183773/100000000), (787259/12500000), (916339/12500000), (916339/12500000), (916339/12500000), (1876301/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15370311/100000000), 0, (6058813/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4926581/50000000), (204971/100000000), (2442059/100000000), (1/100000000), (1/100000000), (6463727/100000000)]
    alternative := .zero
    polynomial := [(-93715663081009391056136601003783158277/31879184330273300671479686000000000000), (41008228308371/1576700000000), (-907974087075161813045029173805446118277/15939592165136650335739843000000000000), (41008228308371/1576700000000), (-1722232511069314235033921746607109078277/31879184330273300671479686000000000000)]
    bernstein := [(15205284545507651837165038741574239179706203/81610711885499649718987996160000000000000000), (124277270577036319967721590438962832352719/627774706811535767069138432000000000000000), (498968932862276983996347046073323252379377/2448321356564989491569639884800000000000000), (1278987202953157769437372122763140240783/6277747068115357670691384320000000000000), (1613072190314897244328909553395846857947/8161071188549964971898799616000000000000)]
    reserve := (93157406633/500000000000) }

theorem quarter_046_024_valid : quarter_046_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_024]
  · intro i; fin_cases i <;> norm_num [quarter_046_024]
  · norm_num [quarter_046_024]
  · norm_num [quarter_046_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_024]

def quarter_046_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(21551793/100000000), (20378333/50000000), (881247/25000000), (105123/2500000), (105123/2500000), (105123/2500000), (21551793/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5004473/25000000), 0, (31976981/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (11649577/100000000), (241589/100000000), (1386449/100000000), (1/100000000), (1/100000000), (6402759/100000000)]
    alternative := .zero
    polynomial := [(-35999834259536961102694666243180738267/8327930877478130269999241000000000000), (413137945253113/12079450000000), (-286596449527658711661785712415904798267/4163965438739065134999620500000000000), (413137945253113/12079450000000), (-537193064795780462220876758588628858267/8327930877478130269999241000000000000)]
    bernstein := [(444172060036651038593221799275024520837/2131950304634401349119805696000000000000), (248986615987412871930099683567798865149/1122079107702316499536739840000000000000), (146104979099604214500532463332135946311687/639585091390320404735941708800000000000000), (25565567178154762558420883530963367562437/112207910770231649953673984000000000000000), (4689560257088848744586515898748849999210453/21319503046344013491198056960000000000000000)]
    reserve := (104170359663/500000000000) }

theorem quarter_046_025_valid : quarter_046_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_025]
  · intro i; fin_cases i <;> norm_num [quarter_046_025]
  · norm_num [quarter_046_025]
  · norm_num [quarter_046_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_025]

def quarter_046_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(22952653/100000000), (22435007/50000000), (1977083/100000000), (1207933/50000000), (1207933/50000000), (1207933/50000000), (22952653/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(23830517/100000000), 0, (36041657/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3183757/25000000), (262659/100000000), (394401/50000000), (1/100000000), (1/100000000), (3165989/50000000)]
    alternative := .zero
    polynomial := [(-797978210060967346497313099570893607/139225358529890762278707600000000000), (270333268296473/6566475000000), (-5344999140464406228672216413472583607/69612679264945381139353800000000000), (270333268296473/6566475000000), (-3297340023622615036949039909124757869/46408452843296920759569200000000000)]
    bernstein := [(83056481115411905958730068487154298689513/356416917836520351433491456000000000000000), (22083007735368798794626665055997585618849/89104229459130087858372864000000000000000), (17028930039321650092365751717681749610831/66828172094347565893779648000000000000000), (1413621468369864729153347519667370170421/5569014341195630491148304000000000000000), (340715176854728807100541544367619035233/1392253585298907622787076000000000000000)]
    reserve := (233031814593/1000000000000) }

theorem quarter_046_026_valid : quarter_046_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_026]
  · intro i; fin_cases i <;> norm_num [quarter_046_026]
  · norm_num [quarter_046_026]
  · norm_num [quarter_046_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_026]

def quarter_046_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(23493451/100000000), (11843797/25000000), (296813/25000000), (1483553/100000000), (1483553/100000000), (1483553/100000000), (23493451/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(6743799/25000000), 0, (9439547/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (13361853/100000000), (171/62500), (240063/50000000), (1/100000000), (1/100000000), (6252691/100000000)]
    alternative := .zero
    polynomial := [(-5987586245730401784454339008313/835694692251470610375000000000), (8963962487667/190000000000), (-51507840113527333000005966654907/626771019188602957781250000000), (8963962487667/190000000000), (-188068601716918126646660849594689/2507084076754411831125000000000)]
    bernstein := [(56928111280451284078958099810569/219919655855650160625000000000000), (12235959719602281309327678771964391/44570383586745099220000000000000000), (678348857670772711829736003415375211/2406800713684235357880000000000000000), (1801172249813317836651260298389801329/6418135236491294287680000000000000000), (1737442006801414798815048265843450771/6418135236491294287680000000000000000)]
    reserve := (129429338771/500000000000) }

theorem quarter_046_027_valid : quarter_046_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_027]
  · intro i; fin_cases i <;> norm_num [quarter_046_027]
  · norm_num [quarter_046_027]
  · norm_num [quarter_046_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_027]

def quarter_046_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(23498531/100000000), (6102209/12500000), (216847/25000000), (1105959/100000000), (1105959/100000000), (1105959/100000000), (23498531/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14791159/50000000), 0, (37966251/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3422477/25000000), (138941/50000000), (355149/100000000), (1/100000000), (1/100000000), (6165857/100000000)]
    alternative := .zero
    polynomial := [(-4489581887125578760221751335541718347/520648962461777959870450500000000000), (72859976735319/1389410000000), (-22360823017487140277165145055968240847/260324481230888979935225250000000000), (72859976735319/1389410000000), (-40232064147848701794108538776394763347/520648962461777959870450500000000000)]
    bernstein := [(379962359713194773497612944272565791668733/1332861343902151577268353280000000000000000), (22318481098964856522861571183086688526543/74047852439008420959352960000000000000000), (308907478753223029868918872024455764122079/999646007926613682951264960000000000000000), (5696448670862552358574942261004500212503/18511963109752105239838240000000000000000), (24765339658172367985303654209034333481453/83303833993884473579272080000000000000000)]
    reserve := (57014536651/200000000000) }

theorem quarter_046_028_valid : quarter_046_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_028]
  · intro i; fin_cases i <;> norm_num [quarter_046_028]
  · norm_num [quarter_046_028]
  · norm_num [quarter_046_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_028]

def quarter_046_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 2]
    lambda := ![(11586477/50000000), (24773211/50000000), (839309/100000000), (544727/50000000), (544727/50000000), (544727/50000000), (11586477/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(31749123/100000000), 0, (4649757/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3455251/25000000), (277729/100000000), (173751/50000000), (1/100000000), (1/100000000), (759121/12500000)]
    alternative := .zero
    polynomial := [(-2558406195106493243954964069081772973/253144878827402174129418000000000000), (792963524485419/13886450000000), (-11200766819281234878325823697673837973/126572439413701087064709000000000000), (792963524485419/13886450000000), (-19843127443455976512696683326265902973/253144878827402174129418000000000000)]
    bernstein := [(12610153881132151536541492294293808340227/40503180612384347860706880000000000000000), (5317515746823918472625538090063887247263/16201272244953739144282752000000000000000), (6534699712838449575754266164135783337073/19441526693944486973139302400000000000000), (867989177257811216995110583212964617751/2592203559192598263085240320000000000000), (19771242254719094296768646720376725699/60993024922178782660829184000000000000)]
    reserve := (38917171721/125000000000) }

theorem quarter_046_029_valid : quarter_046_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_046_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_046_029]
  · intro i; fin_cases i <;> norm_num [quarter_046_029]
  · norm_num [quarter_046_029]
  · norm_num [quarter_046_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_046_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_046_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_046_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_046_029]

def quarterTable046 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 2, 0, 0, 2]
  rows := [quarter_046_000, quarter_046_001, quarter_046_002, quarter_046_003, quarter_046_004, quarter_046_005, quarter_046_006, quarter_046_007, quarter_046_008, quarter_046_009, quarter_046_010, quarter_046_011, quarter_046_012, quarter_046_013, quarter_046_014, quarter_046_015, quarter_046_016, quarter_046_017, quarter_046_018, quarter_046_019, quarter_046_020, quarter_046_021, quarter_046_022, quarter_046_023, quarter_046_024, quarter_046_025, quarter_046_026, quarter_046_027, quarter_046_028, quarter_046_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_046_000_valid
    · exact quarter_046_001_valid
    · exact quarter_046_002_valid
    · exact quarter_046_003_valid
    · exact quarter_046_004_valid
    · exact quarter_046_005_valid
    · exact quarter_046_006_valid
    · exact quarter_046_007_valid
    · exact quarter_046_008_valid
    · exact quarter_046_009_valid
    · exact quarter_046_010_valid
    · exact quarter_046_011_valid
    · exact quarter_046_012_valid
    · exact quarter_046_013_valid
    · exact quarter_046_014_valid
    · exact quarter_046_015_valid
    · exact quarter_046_016_valid
    · exact quarter_046_017_valid
    · exact quarter_046_018_valid
    · exact quarter_046_019_valid
    · exact quarter_046_020_valid
    · exact quarter_046_021_valid
    · exact quarter_046_022_valid
    · exact quarter_046_023_valid
    · exact quarter_046_024_valid
    · exact quarter_046_025_valid
    · exact quarter_046_026_valid
    · exact quarter_046_027_valid
    · exact quarter_046_028_valid
    · exact quarter_046_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
