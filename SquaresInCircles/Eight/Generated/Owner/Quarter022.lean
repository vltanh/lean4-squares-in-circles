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

def quarter_022_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_022_000_valid : quarter_022_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_000]
  · intro i; fin_cases i <;> norm_num [quarter_022_000]
  · norm_num [quarter_022_000]
  · norm_num [quarter_022_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_000]

def quarter_022_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_022_001_valid : quarter_022_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_001]
  · intro i; fin_cases i <;> norm_num [quarter_022_001]
  · norm_num [quarter_022_001]
  · norm_num [quarter_022_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_001]

def quarter_022_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-382804973875870721/684552687500000000), (-39204036/10952843), (-1067357661375870721/342276343750000000), (-39204036/10952843), (-1751910348875870721/684552687500000000)]
    bernstein := [(646693971861456324660719/1752454880000000000000000), (155279285836763680907889/438113720000000000000000), (111621009402992369262377/328585290000000000000000), (8894952571565710129429/27382107500000000000000), (2121126590005779963799/6845526875000000000000)]
    reserve := (61971171211/200000000000) }

theorem quarter_022_002_valid : quarter_022_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_002]
  · intro i; fin_cases i <;> norm_num [quarter_022_002]
  · norm_num [quarter_022_002]
  · norm_num [quarter_022_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_002]

def quarter_022_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-556512809540135577/1127647700000000000), (-75237955/22552954), (-1684160509540135577/563823850000000000), (-75237955/22552954), (-2811808209540135577/1127647700000000000)]
    bernstein := [(3477032164953649209663/11276477000000000000000), (13294893098709221172331/45105908000000000000000), (152104840977384548853841/541270896000000000000000), (192793584408782748968639/721694528000000000000000), (730712026497435302482743/2886778112000000000000000)]
    reserve := (253123724147/1000000000000) }

theorem quarter_022_003_valid : quarter_022_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_003]
  · intro i; fin_cases i <;> norm_num [quarter_022_003]
  · norm_num [quarter_022_003]
  · norm_num [quarter_022_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_003]

def quarter_022_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4491503/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (578989/2500000)]
    alternative := .zero
    polynomial := [(-31489286020192343/72373625000000000), (-8983006/2894945), (-103862911020192343/36186812500000000), (-8983006/2894945), (-176236536020192343/72373625000000000)]
    bernstein := [(46648716103417490616537/185276480000000000000000), (4430286397231575186187/18527648000000000000000), (1257891006024344017523/5558294400000000000000), (39528917639300858899/185276480000000000000), (3710003290164412873/18527648000000000000)]
    reserve := (20024146023/100000000000) }

theorem quarter_022_004_valid : quarter_022_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_004]
  · intro i; fin_cases i <;> norm_num [quarter_022_004]
  · norm_num [quarter_022_004]
  · norm_num [quarter_022_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_004]

def quarter_022_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (68290369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-227369526439286957/593044725000000000), (-9755767/3388827), (-820414251439286957/296522362500000000), (-9755767/3388827), (-1413458976439286957/593044725000000000)]
    bernstein := [(10073437836348689809/50606483200000000000), (94768432271642857513/506064832000000000000), (7985100306579547072057/45545834880000000000000), (24779433730114407672827/151819449600000000000000), (229173926598944049100723/1518194496000000000000000)]
    reserve := (75475812619/500000000000) }

theorem quarter_022_005_valid : quarter_022_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_005]
  · intro i; fin_cases i <;> norm_num [quarter_022_005]
  · norm_num [quarter_022_005]
  · norm_num [quarter_022_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_005]

def quarter_022_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (32261287/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4847213/20000000)]
    alternative := .zero
    polynomial := [(-409539937756191047/1211803250000000000), (-64522574/24236065), (-1621343187756191047/605901625000000000), (-64522574/24236065), (-2833146437756191047/1211803250000000000)]
    bernstein := [(465061375391627830838233/3102216320000000000000000), (53877066138430155648537/387777040000000000000000), (4645994352667887962951/36354097500000000000000), (352909745491428925301/3029508125000000000000), (19883491019203713057/189344257812500000000)]
    reserve := (105012379297/1000000000000) }

theorem quarter_022_006_valid : quarter_022_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_006]
  · intro i; fin_cases i <;> norm_num [quarter_022_006]
  · norm_num [quarter_022_006]
  · norm_num [quarter_022_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_006]

def quarter_022_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(2006693/12500000), (13650153/100000000), (31599/400000), (15447669/100000000), (15447669/100000000), (15447669/100000000), (2006693/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (429923/3125000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1587851/100000000), (3985083/100000000), (43841/1000000), (1/100000000), (1/100000000), (1599777/20000000)]
    alternative := .zero
    polynomial := [(813238412622757097291055623914181/24655539688978250673904500000000000), (-219614608833197/399944250000000), (-16335955334583070017164222623429819/12327769844489125336952250000000000), (-219614608833197/399944250000000), (-33485149081788897131619500870773819/24655539688978250673904500000000000)]
    bernstein := [(354504831233072378062433568602709589/3852428076402851667797578125000000000), (1885364146150920925086506377017799357/20546283074148542228253750000000000000), (67579462366053164668233770867206604633/739666190669347520217135000000000000000), (238881918504620518615285063606065542861/2629924233491013405216480000000000000000), (37196689103628275642631520101173623277/412537134665257004739840000000000000000)]
    reserve := (45082837371/500000000000) }

theorem quarter_022_007_valid : quarter_022_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_007]
  · intro i; fin_cases i <;> norm_num [quarter_022_007]
  · norm_num [quarter_022_007]
  · norm_num [quarter_022_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_007]

def quarter_022_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(1986469/12500000), (6902507/50000000), (1988073/25000000), (15486397/100000000), (15486397/100000000), (15486397/100000000), (1986469/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2602589/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (348471/25000000), (4025609/100000000), (274929/6250000), (1/100000000), (1/100000000), (8033929/100000000)]
    alternative := .zero
    polynomial := [(5597492798343883988744853051680177/133267366757620316607372000000000000), (-107153874842413/200848225000000), (-100044840360345251364814461183919823/66633683378810158303686000000000000), (-107153874842413/200848225000000), (-68562391173011462239457925139839941/44422455585873438869124000000000000)]
    bernstein := [(30976541578186484553509868897217656978577/341164458899508010514872320000000000000000), (5154249061706301856586794162969972515911/56860743149918001752478720000000000000000), (23115723830494984254447962700938907426571/255873344174631007886154240000000000000000), (3832960326166201560197984733375540554653/42645557362438501314359040000000000000000), (61399536308366566251891698590307060927/687831570361911311521920000000000000000)]
    reserve := (11158170647/125000000000) }

theorem quarter_022_008_valid : quarter_022_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_008]
  · intro i; fin_cases i <;> norm_num [quarter_022_008]
  · norm_num [quarter_022_008]
  · norm_num [quarter_022_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_008]

def quarter_022_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(3940979/25000000), (279721/2000000), (2501/31250), (7747153/50000000), (7747153/50000000), (7747153/50000000), (3940979/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (12265083/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (300087/25000000), (1017921/25000000), (440653/10000000), (1/100000000), (1/100000000), (4029617/50000000)]
    alternative := .zero
    polynomial := [(380812868389638433859633138265571/7533369349140424126200375000000000), (-104694859379107/201480850000000), (-19750988032096965096825022997167037/11300054023710636189300562500000000), (-104694859379107/201480850000000), (-40644414669362845495228945409130787/22600108047421272378601125000000000)]
    bernstein := [(108493124197471293497267491824766489951/1205339095862467860192060000000000000000), (43378979668125911811715402477366266857/482135638344987144076824000000000000000), (155780920032410222072294292632591692999/1735688298041953718676566400000000000000), (4135564571562268480454750436241036847/46285021281118765831375104000000000000), (328693663112732429230332928466460997/3702801702489501266510008320000000000)]
    reserve := (88768907849/1000000000000) }

theorem quarter_022_009_valid : quarter_022_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_009]
  · intro i; fin_cases i <;> norm_num [quarter_022_009]
  · norm_num [quarter_022_009]
  · norm_num [quarter_022_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_009]

def quarter_022_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(15668257/100000000), (14196187/100000000), (8052881/100000000), (15471473/100000000), (15471473/100000000), (15471473/100000000), (15668257/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11511297/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1006129/100000000), (2062017/50000000), (4407187/100000000), (1/100000000), (1/100000000), (8074547/100000000)]
    alternative := .zero
    polynomial := [(173355612856099590300091936045604719/2953150259384492392254031080000000000), (-409617518103907/807454700000000), (-84064632610143599088671017487492813/39907435937628275571000420000000000), (-409617518103907/807454700000000), (-6394138426006725922861747230120072881/2953150259384492392254031080000000000)]
    bernstein := [(3337112284807204928773030283188549507/37218779884427325657453880934400000000), (3350320306019788559648167857988414827/37333652661848397650223800320000000000), (5080199054751758887801816753532752458553/56700484980182253931277396736000000000000), (26027313208390874785884120811170515619/291669161420690606642373440000000000000), (201398651000810701018955399587340403763/2271654045680378763272331600000000000000)]
    reserve := (11082159021/125000000000) }

theorem quarter_022_010_valid : quarter_022_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_010]
  · intro i; fin_cases i <;> norm_num [quarter_022_010]
  · norm_num [quarter_022_010]
  · norm_num [quarter_022_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_010]

def quarter_022_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(15602883/100000000), (7219177/50000000), (4050809/50000000), (15418087/100000000), (15418087/100000000), (15418087/100000000), (15602883/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5374551/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5063/625000), (4183379/100000000), (220047/5000000), (1/100000000), (1/100000000), (161591/2000000)]
    alternative := .zero
    polynomial := [(400766586239431946762024970856841/6025009651317547827432000000000000), (-200513893491233/403977500000000), (-8019995949286016655444765780340459/3012504825658773913716000000000000), (-200513893491233/403977500000000), (-16440758484811465257651556531537759/6025009651317547827432000000000000)]
    bernstein := [(5407639488924709784774107372056044441/60250096513175478274320000000000000000), (21678942372944287599872449640767513423/241000386052701913097280000000000000000), (259921457239243386841417183436102825807/2892004632632422957167360000000000000000), (345194486834089048566766178161688824907/3856006176843230609556480000000000000000), (1371062255240163507342826949865335294321/15424024707372922438225920000000000000000)]
    reserve := (88891341997/1000000000000) }

theorem quarter_022_011_valid : quarter_022_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_011]
  · intro i; fin_cases i <;> norm_num [quarter_022_011]
  · norm_num [quarter_022_011]
  · norm_num [quarter_022_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_011]

def quarter_022_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(7782859/50000000), (7357737/50000000), (8149571/100000000), (7667253/50000000), (7667253/50000000), (7667253/50000000), (7782859/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9976241/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3819/625000), (4250441/100000000), (4387929/100000000), (1/100000000), (1/100000000), (403693/5000000)]
    alternative := .zero
    polynomial := [(478847403265767722565988044711/6467329718075912640500000000000), (-196454353962659/403693000000000), (-23387393473136011129873000008703/6467329718075912640500000000000), (-196454353962659/403693000000000), (-11933120438200889426219494026707/3233664859037956320250000000000)]
    bernstein := [(747407313847763947374114698625065133/8278182039137168179840000000000000000), (375095626954425915961802700739888661/4139091019568584089920000000000000000), (562382921377025543137835265445725311/6208636529352876134880000000000000000), (93298162573554758550097347117994629/1034772754892146022480000000000000000), (46238975000297069245707104500627693/517386377446073011240000000000000000)]
    reserve := (17874059703/200000000000) }

theorem quarter_022_012_valid : quarter_022_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_012]
  · intro i; fin_cases i <;> norm_num [quarter_022_012]
  · norm_num [quarter_022_012]
  · norm_num [quarter_022_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_012]

def quarter_022_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(7777217/50000000), (939403/6250000), (8196771/100000000), (1902663/12500000), (1902663/12500000), (1902663/12500000), (7777217/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9190757/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (203977/50000000), (2162967/50000000), (2184167/50000000), (1/100000000), (1/100000000), (8057037/100000000)]
    alternative := .zero
    polynomial := [(70129900162824224981437166587263687/862680106766807200420429000000000000), (-38515877449169/80570370000000), (-2409226181242917522842625263064196313/431340053383403600210214500000000000), (-38515877449169/80570370000000), (-4888582262648659270666687692715656313/862680106766807200420429000000000000)]
    bernstein := [(37787786168942804924893816990002389639861/414086451248067456201805920000000000000000), (284600662772917488194221076964106866383/3101771170397509035219520000000000000000), (151836378820076100970447979448059168243461/1656345804992269824807223680000000000000000), (1129095575121839254279378233667043685983/12407084681590036140878080000000000000000), (594683875060356418205312210037597960586261/6625383219969079299228894720000000000000000)]
    reserve := (359033647/4000000000) }

theorem quarter_022_013_valid : quarter_022_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_013]
  · intro i; fin_cases i <;> norm_num [quarter_022_013]
  · norm_num [quarter_022_013]
  · norm_num [quarter_022_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_013]

def quarter_022_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(15566381/100000000), (769307/5000000), (1648627/20000000), (15079321/100000000), (15079321/100000000), (15079321/100000000), (15566381/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8391091/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (200699/100000000), (441057/10000000), (4342387/100000000), (1/100000000), (1/100000000), (1003573/12500000)]
    alternative := .zero
    polynomial := [(68031863513592595347461065652443537/771520406997281754390186000000000000), (-377676754363191/802858400000000), (-4542796693958366208528822489668090213/385760203498640877195093000000000000), (-377676754363191/802858400000000), (-9153625251430325012405106044988623963/771520406997281754390186000000000000)]
    bernstein := [(182857817756923605270800600127328240514437/1975092241913041291238876160000000000000000), (921587999213716564480611760569314530771/9875461209565206456194380800000000000000), (343786241433039461265909754038115537387/3703297953586952421072892800000000000000), (562401652493535237618543076382927171/6172163255978254035121488000000000000), (68031863513592595347461065652443537/771520406997281754390186000000000000)]
    reserve := (88178955341/1000000000000) }

theorem quarter_022_014_valid : quarter_022_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_014]
  · intro i; fin_cases i <;> norm_num [quarter_022_014]
  · norm_num [quarter_022_014]
  · norm_num [quarter_022_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_014]

def quarter_022_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(8180061/50000000), (4091309/25000000), (8211389/100000000), (14234377/100000000), (14234377/100000000), (14234377/100000000), (8180061/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(409067/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (236863/3125000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (25843/25000000), (2313257/50000000), (2076149/50000000), (1/100000000), (1/100000000), (8011529/100000000)]
    alternative := .zero
    polynomial := [(451920514032114222254903533457077/4963494248019176648613000000000000), (16978093109171042819/20704194394700000000), (-38414048242795316312616750982479656723/1491530021529762582908206500000000000), (16978093109171042819/20704194394700000000), (-77099700714523933272808698988567016723/2983060043059525165816413000000000000)]
    bernstein := [(451920514032114222254903533457077/4963494248019176648613000000000000), (573786000631485011554424709620019179/5966120086119050331632826000000000000), (1412058455908489630787676141876636672877/14318688206685720795918782400000000000000), (939108218915178162071148183784236385579/9545792137790480530612521600000000000000), (728959639084642377539987858224108320989677/7636633710232384424490017280000000000000000)]
    reserve := (91048864257/1000000000000) }

theorem quarter_022_015_valid : quarter_022_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_015]
  · intro i; fin_cases i <;> norm_num [quarter_022_015]
  · norm_num [quarter_022_015]
  · norm_num [quarter_022_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_015]

def quarter_022_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(8965799/50000000), (8991051/50000000), (320949/4000000), (6355163/50000000), (6355163/50000000), (6355163/50000000), (8965799/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(336691/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3323071/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (56739/50000000), (2487763/50000000), (3798047/100000000), (1/100000000), (1/100000000), (2002201/25000000)]
    alternative := .zero
    polynomial := [(1319022277457707703769760387578233/21046918251494300156629000000000000), (8875993524443476559/3786762751300000000), (-298484407351047328814376735888866767/10523459125747150078314500000000000), (8875993524443476559/3786762751300000000), (-598287836979552365332523232165311767/21046918251494300156629000000000000)]
    bernstein := [(5580233000044759774233994154742036313833/53880110723825408400970240000000000000000), (2946433705212489675164142454988184137433/26940055361912704200485120000000000000000), (4535023881561146916722636396428936536299/40410083042869056300727680000000000000000), (755202667128462172863915288770445877833/6735013840478176050121280000000000000000), (367308290589987017036125689447127954633/3367506920239088025060640000000000000000)]
    reserve := (5178379299/50000000000) }

theorem quarter_022_016_valid : quarter_022_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_016]
  · intro i; fin_cases i <;> norm_num [quarter_022_016]
  · norm_num [quarter_022_016]
  · norm_num [quarter_022_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_016]

def quarter_022_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(9750977/50000000), (1965491/10000000), (7729097/100000000), (2801007/25000000), (2801007/25000000), (2801007/25000000), (9750977/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(305913/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5551111/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (30941/25000000), (2668301/50000000), (3439319/100000000), (1/100000000), (1/100000000), (7994753/100000000)]
    alternative := .zero
    polynomial := [(-2094992130907752178321487407268679/174623754693518800982299000000000000), (10243861402635560601/2473656525730000000), (-2716421080192224925230003719597573679/87311877346759400491149500000000000), (10243861402635560601/2473656525730000000), (-5430747168253542098281685951787878679/174623754693518800982299000000000000)]
    bernstein := [(3285886350965612871318362030368090538121/27939800750963008157167840000000000000000), (6936918185655442168700325004710858225963/55879601501926016314335680000000000000000), (14243738601393238586786432663948202715489/111759203003852032628671360000000000000000), (28504689184631344056123741958389485507667/223518406007704065257342720000000000000000), (55589556621969116281333877711265245631801/447036812015408130514685440000000000000000)]
    reserve := (58802966783/500000000000) }

theorem quarter_022_017_valid : quarter_022_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_017]
  · intro i; fin_cases i <;> norm_num [quarter_022_017]
  · norm_num [quarter_022_017]
  · norm_num [quarter_022_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_017]

def quarter_022_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(2631471/12500000), (2137661/10000000), (7326669/100000000), (4865531/50000000), (4865531/50000000), (4865531/50000000), (2631471/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3712483/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4299461/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (67073/50000000), (1141979/20000000), (3077863/100000000), (1/100000000), (1/100000000), (3982819/50000000)]
    alternative := .zero
    polynomial := [(-81025806283428766951778524519916143/563374200589977983907719400000000000), (33250189922850995513/5342792375740000000), (-9576853209983871636504705602998364143/281687100294988991953859700000000000), (33250189922850995513/5342792375740000000), (-19072680613684314506057632681476812143/563374200589977983907719400000000000)]
    bernstein := [(192171108787779592395798638407486717218017/1442237953510343638803761664000000000000000), (50682824877882273795642367477398968375939/360559488377585909700940416000000000000000), (39041727437332307618648977464634393638239/270419616283189432275705312000000000000000), (3259729563854211773918087095583959918471/22534968023599119356308776000000000000000), (796447292694404196664985160935189229257/5633742005899779839077194000000000000000)]
    reserve := (133245078123/1000000000000) }

theorem quarter_022_018_valid : quarter_022_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_018]
  · intro i; fin_cases i <;> norm_num [quarter_022_018]
  · norm_num [quarter_022_018]
  · norm_num [quarter_022_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_018]

def quarter_022_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(22562497/100000000), (23140931/100000000), (426097/6250000), (8305507/100000000), (8305507/100000000), (8305507/100000000), (22562497/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1285409/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1450459/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (28909/20000000), (380983/6250000), (2715111/100000000), (1/100000000), (1/100000000), (7917959/100000000)]
    alternative := .zero
    polynomial := [(-46562384666599798489984687785908491/135301139915481859556916000000000000), (246070348594935308811/28612534591375000000), (-2504714172417090828186128712945716491/67650569957740929778458000000000000), (246070348594935308811/28612534591375000000), (-4962865960167581857882272738105524491/135301139915481859556916000000000000)]
    bernstein := [(203708338354576138340610526175217947309/1353011399154818595569160000000000000000), (19089478909254418796198339400670541681/120267679924872764050592000000000000000), (423629239754193951981196099174784433683/2597781886377251703492787200000000000000), (2518209657747474909333676745469637753/15394263030383713798475776000000000000), (3551486524402996850574382123172517821/22167738763752547869805117440000000000)]
    reserve := (2352487783/15625000000) }

theorem quarter_022_019_valid : quarter_022_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_019]
  · intro i; fin_cases i <;> norm_num [quarter_022_019]
  · norm_num [quarter_022_019]
  · norm_num [quarter_022_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_019]

def quarter_022_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(3291053/10000000), (1708947/5000000), 0, 0, 0, 0, (3291053/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4612401/50000000), 0, 0, 0, 0], ![0, 0, (8925983/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (42449/20000000), (278937/3125000), (1/100000000), (1/100000000), (1/100000000), (8315833/100000000)]
    alternative := .zero
    polynomial := [(-42789327479441415617484106441/46336199946191496000000000000), (16463207247479/1061225000000), (-21860162844237082752805437009497/393857699542627716000000000000), (16463207247479/1061225000000), (-42992907121323661440113644209497/787715399085255432000000000000)]
    bernstein := [(21354978305834162344725237459007/129059290986128249978880000000000), (286482819835302433791136839947857/1613241137326603124736000000000000), (11130718551669198186070493368510669/60496542649747617177600000000000000), (9308501342833868615564616157783501/50413785541456347648000000000000000), (22619754672519462495884510146332343/126034463853640869120000000000000000)]
    reserve := (33093283161/200000000000) }

theorem quarter_022_020_valid : quarter_022_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_020]
  · intro i; fin_cases i <;> norm_num [quarter_022_020]
  · norm_num [quarter_022_020]
  · norm_num [quarter_022_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_020]

def quarter_022_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(32741317/100000000), (17258683/50000000), 0, 0, 0, 0, (32741317/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(85387/781250), 0, 0, 0, 0], ![0, 0, (1802873/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (106421/50000000), (1802873/20000000), (1/100000000), (1/100000000), (1/100000000), (2068269/25000000)]
    alternative := .zero
    polynomial := [(-148364572538677299641379/111670580400066406250000), (97799062277001/5321050000000), (-100789043539045033137727253/1786729286401062500000000), (97799062277001/5321050000000), (-98415210378426196343465189/1786729286401062500000000)]
    bernstein := [(55255038947507033901767943891/285876685824170000000000000000), (16784529184133333054296459947/81679053092620000000000000000), (103854359541096411865148494379/490074318555720000000000000000), (485969845394769994801021172569/2287013486593360000000000000000), (947470127732136529497630156011/4574026973186720000000000000000)]
    reserve := (193282774313/1000000000000) }

theorem quarter_022_021_valid : quarter_022_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_021]
  · intro i; fin_cases i <;> norm_num [quarter_022_021]
  · norm_num [quarter_022_021]
  · norm_num [quarter_022_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_021]

def quarter_022_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(32542819/100000000), (34914361/100000000), 0, 0, 0, 0, (32542819/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(12648221/100000000), 0, 0, 0, 0], ![0, 0, (4559021/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (53383/25000000), (4559021/50000000), (1/100000000), (1/100000000), (1/100000000), (205573/2500000)]
    alternative := .zero
    polynomial := [(-544614330714869411131440335317/300187008754521834000000000000), (455502420455197/21353200000000), (-8628834954706046172781766397817/150093504377260917000000000000), (455502420455197/21353200000000), (-16713055578697222934432092460317/300187008754521834000000000000)]
    bernstein := [(169296948096664595342623570439353283/768478742411575895040000000000000000), (7449630433907447726874524825290173/32019947600482328960000000000000000), (2153447135638292655253920709186919/9005610262635655020000000000000000), (59945659998100346624037500764401/250155840628768195000000000000000), (10980114569868341616245226256427/46904220117894036562500000000000)]
    reserve := (220301406861/1000000000000) }

theorem quarter_022_022_valid : quarter_022_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_022]
  · intro i; fin_cases i <;> norm_num [quarter_022_022]
  · norm_num [quarter_022_022]
  · norm_num [quarter_022_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_022]

def quarter_022_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(16157263/50000000), (8842737/25000000), 0, 0, 0, 0, (16157263/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14383163/100000000), 0, 0, 0, 0], ![0, 0, (9237281/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (107157/50000000), (4618641/50000000), (1/100000000), (1/100000000), (1/100000000), (4082617/50000000)]
    alternative := .zero
    polynomial := [(-803254200683635393617173813561/336761272754924671500000000000), (43549751766571/1785950000000), (-9892278769410035953325862593561/168380636377462335750000000000), (43549751766571/1785950000000), (-18981303338136436513034551373561/336761272754924671500000000000)]
    bernstein := [(12976323017416246555886277143191/52618948867956979921875000000000), (19834871553708520638797060355433/76536652898846516250000000000000), (383469497418022979430380234979709/1443262597521105735000000000000000), (2607405724458029386927038883347721/9796691571052354080000000000000000), (224509051366237171813321476880095079/862108858252607159040000000000000000)]
    reserve := (12330465827/50000000000) }

theorem quarter_022_023_valid : quarter_022_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_023]
  · intro i; fin_cases i <;> norm_num [quarter_022_023]
  · norm_num [quarter_022_023]
  · norm_num [quarter_022_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_023]

def quarter_022_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(16027921/50000000), (35888317/100000000), 0, 0, 0, 0, (16027921/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(16136737/100000000), 0, 0, 0, 0], ![0, 0, (4686197/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (26899/12500000), (1874479/20000000), (1/100000000), (1/100000000), (1/100000000), (809987/10000000)]
    alternative := .zero
    polynomial := [(-373336509904409773251236683321/122522547366215781000000000000), (592916654304957/21519200000000), (-3687679085431798738464878057071/61261273683107890500000000000), (592916654304957/21519200000000), (-7002021660959187703678519430821/122522547366215781000000000000)]
    bernstein := [(2083003340740549001583552465735859/7650188323353960960000000000000000), (218080628523601022089369613787541/765018832335396096000000000000000), (2744901181515395372524168447598621/9409731637725371980800000000000000), (91624822374310684434027027800017/313657721257512399360000000000000), (8976114498084587120521125867731/31365772125751239936000000000000)]
    reserve := (27228131553/100000000000) }

theorem quarter_022_024_valid : quarter_022_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_024]
  · intro i; fin_cases i <;> norm_num [quarter_022_024]
  · norm_num [quarter_022_024]
  · norm_num [quarter_022_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_024]

def quarter_022_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(15883043/50000000), (36467829/100000000), 0, 0, 0, 0, (15883043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(17911403/100000000), 0, 0, 0, 0], ![0, 0, (9523737/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (108083/50000000), (9523737/100000000), (1/100000000), (1/100000000), (1/100000000), (1605331/20000000)]
    alternative := .zero
    polynomial := [(-116474029439703911029118398093/30600999859265881500000000000), (666923477246639/21616600000000), (-946153230922874177700068405593/15300499929632940750000000000), (666923477246639/21616600000000), (-1775832432406044444371018413093/30600999859265881500000000000)]
    bernstein := [(80332237445640859189135728487/270132964274898816000000000000), (8106740806002107337247007370383/26112853213240218880000000000000), (745521611685827884783023320288273/2350156789191619699200000000000000), (829317519503326380960628169148479/2611285321324021888000000000000000), (24396544983590621596341072405115787/78338559639720656640000000000000000)]
    reserve := (14869017867/50000000000) }

theorem quarter_022_025_valid : quarter_022_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_025]
  · intro i; fin_cases i <;> norm_num [quarter_022_025]
  · norm_num [quarter_022_025]
  · norm_num [quarter_022_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_025]

def quarter_022_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(15722243/50000000), (9277757/25000000), 0, 0, 0, 0, (15722243/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1970971/10000000), 0, 0, 0, 0], ![0, 0, (9691711/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5431/2500000), (9691711/100000000), (1/100000000), (1/100000000), (1/100000000), (7945393/100000000)]
    alternative := .zero
    polynomial := [(-2929476629426754590776540691641/627316774225416469500000000000), (18627739998979/543100000000), (-19975363257504271761569552371141/313658387112708234750000000000), (18627739998979/543100000000), (-37021249885581788932362564050641/627316774225416469500000000000)]
    bernstein := [(517041849981456012383754812584009919/1605930942017066161920000000000000000), (134641206332102064125632924375293787/401482735504266540480000000000000000), (103066553403546041443996265923069553/301112051628199905360000000000000000), (8597189961607499432140785161134223/25092670969016658780000000000000000), (2109106841173195157256250416284279/6273167742254164695000000000000000)]
    reserve := (80489427729/250000000000) }

theorem quarter_022_026_valid : quarter_022_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_026]
  · intro i; fin_cases i <;> norm_num [quarter_022_026]
  · norm_num [quarter_022_026]
  · norm_num [quarter_022_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_026]

def quarter_022_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(1243607/4000000), (756393/2000000), 0, 0, 0, 0, (1243607/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(269179/1250000), 0, 0, 0, 0], ![0, 0, (9876771/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (43683/20000000), (9876771/100000000), (1/100000000), (1/100000000), (1/100000000), (1571173/20000000)]
    alternative := .zero
    polynomial := [(-28351312969421607657963474737/5021317465462641400000000000), (1104002088711/29122000000), (-165071737342059673328290674737/2510658732731320700000000000), (1104002088711/29122000000), (-301792161714697738998617874737/5021317465462641400000000000)]
    bernstein := [(17376421537038714857386029249703/50213174654626414000000000000000), (72273779736979641013589391709813/200852698618505656000000000000000), (884412934004735394064083403458169/2410232383422067872000000000000000), (1180171800317896083547433894368433/3213643177896090496000000000000000), (4634956823957967124957335571146943/12854572711584361984000000000000000)]
    reserve := (86513259003/250000000000) }

theorem quarter_022_027_valid : quarter_022_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_027]
  · intro i; fin_cases i <;> norm_num [quarter_022_027]
  · norm_num [quarter_022_027]
  · norm_num [quarter_022_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_027]

def quarter_022_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(15351091/50000000), (9648909/25000000), 0, 0, 0, 0, (15351091/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(11694007/50000000), 0, 0, 0, 0], ![0, 0, (10079423/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (13731/6250000), (10079423/100000000), (1/100000000), (1/100000000), (1/100000000), (7757827/100000000)]
    alternative := .zero
    polynomial := [(-147781337612132904853706399/21911991419633799000000000), (38173565344177/915400000000), (-1490880611757435103603232413/21911991419633799000000000), (38173565344177/915400000000), (-671549637072651099374763007/10955995709816899500000000)]
    bernstein := [(10368947676988181668620560799773/28047349017131262720000000000000), (326286948172994002560997899943/849919667185795840000000000000), (2057344527866682690265948064231/5258877940712111760000000000000), (83180991851993422232457138553/212479916796448960000000000000), (674049796145539679284926145643/1752959313570703920000000000000)]
    reserve := (369694393243/1000000000000) }

theorem quarter_022_028_valid : quarter_022_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_028]
  · intro i; fin_cases i <;> norm_num [quarter_022_028]
  · norm_num [quarter_022_028]
  · norm_num [quarter_022_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_028]

def quarter_022_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 2]
    lambda := ![(30279427/100000000), (19720573/50000000), 0, 0, 0, 0, (30279427/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(6318427/25000000), 0, 0, 0, 0], ![0, 0, (1287529/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (44217/20000000), (1287529/12500000), (1/100000000), (1/100000000), (1/100000000), (3825503/50000000)]
    alternative := .zero
    polynomial := [(-102161024246493474881623242169/12811085181478287000000000000), (505106330712979/11054250000000), (-150684756163650715381384964723/2135180863579714500000000000), (505106330712979/11054250000000), (-47173383102082989259216855657/753593245969311000000000000)]
    bernstein := [(805352474013891388482239873543431/2049773629036525920000000000000000), (334181015976840754367499366587539/819909451614610368000000000000000), (136144713633548823613832818809823/327963780645844147200000000000000), (54487833252092015796219849361003/131185512258337658880000000000000), (21413641754435591520298899305399/52474204903335063552000000000000)]
    reserve := (392898251107/1000000000000) }

theorem quarter_022_029_valid : quarter_022_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_022_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_022_029]
  · intro i; fin_cases i <;> norm_num [quarter_022_029]
  · norm_num [quarter_022_029]
  · norm_num [quarter_022_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_022_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_022_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_022_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_022_029]

def quarterTable022 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 2, 0, 0, 2]
  rows := [quarter_022_000, quarter_022_001, quarter_022_002, quarter_022_003, quarter_022_004, quarter_022_005, quarter_022_006, quarter_022_007, quarter_022_008, quarter_022_009, quarter_022_010, quarter_022_011, quarter_022_012, quarter_022_013, quarter_022_014, quarter_022_015, quarter_022_016, quarter_022_017, quarter_022_018, quarter_022_019, quarter_022_020, quarter_022_021, quarter_022_022, quarter_022_023, quarter_022_024, quarter_022_025, quarter_022_026, quarter_022_027, quarter_022_028, quarter_022_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_022_000_valid
    · exact quarter_022_001_valid
    · exact quarter_022_002_valid
    · exact quarter_022_003_valid
    · exact quarter_022_004_valid
    · exact quarter_022_005_valid
    · exact quarter_022_006_valid
    · exact quarter_022_007_valid
    · exact quarter_022_008_valid
    · exact quarter_022_009_valid
    · exact quarter_022_010_valid
    · exact quarter_022_011_valid
    · exact quarter_022_012_valid
    · exact quarter_022_013_valid
    · exact quarter_022_014_valid
    · exact quarter_022_015_valid
    · exact quarter_022_016_valid
    · exact quarter_022_017_valid
    · exact quarter_022_018_valid
    · exact quarter_022_019_valid
    · exact quarter_022_020_valid
    · exact quarter_022_021_valid
    · exact quarter_022_022_valid
    · exact quarter_022_023_valid
    · exact quarter_022_024_valid
    · exact quarter_022_025_valid
    · exact quarter_022_026_valid
    · exact quarter_022_027_valid
    · exact quarter_022_028_valid
    · exact quarter_022_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
