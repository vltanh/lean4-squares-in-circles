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

def quarter_014_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_014_000_valid : quarter_014_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_000]
  · intro i; fin_cases i <;> norm_num [quarter_014_000]
  · norm_num [quarter_014_000]
  · norm_num [quarter_014_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_000]

def quarter_014_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_014_001_valid : quarter_014_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_001]
  · intro i; fin_cases i <;> norm_num [quarter_014_001]
  · norm_num [quarter_014_001]
  · norm_num [quarter_014_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_001]

def quarter_014_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-382804973875870721/684552687500000000), (-39204036/10952843), (-1067357661375870721/342276343750000000), (-39204036/10952843), (-1751910348875870721/684552687500000000)]
    bernstein := [(646693971861456324660719/1752454880000000000000000), (155279285836763680907889/438113720000000000000000), (111621009402992369262377/328585290000000000000000), (8894952571565710129429/27382107500000000000000), (2121126590005779963799/6845526875000000000000)]
    reserve := (61971171211/200000000000) }

theorem quarter_014_002_valid : quarter_014_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_002]
  · intro i; fin_cases i <;> norm_num [quarter_014_002]
  · norm_num [quarter_014_002]
  · norm_num [quarter_014_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_002]

def quarter_014_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-556512809540135577/1127647700000000000), (-75237955/22552954), (-1684160509540135577/563823850000000000), (-75237955/22552954), (-2811808209540135577/1127647700000000000)]
    bernstein := [(3477032164953649209663/11276477000000000000000), (13294893098709221172331/45105908000000000000000), (152104840977384548853841/541270896000000000000000), (192793584408782748968639/721694528000000000000000), (730712026497435302482743/2886778112000000000000000)]
    reserve := (253123724147/1000000000000) }

theorem quarter_014_003_valid : quarter_014_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_003]
  · intro i; fin_cases i <;> norm_num [quarter_014_003]
  · norm_num [quarter_014_003]
  · norm_num [quarter_014_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_003]

def quarter_014_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4491503/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (578989/2500000)]
    alternative := .zero
    polynomial := [(-31489286020192343/72373625000000000), (-8983006/2894945), (-103862911020192343/36186812500000000), (-8983006/2894945), (-176236536020192343/72373625000000000)]
    bernstein := [(46648716103417490616537/185276480000000000000000), (4430286397231575186187/18527648000000000000000), (1257891006024344017523/5558294400000000000000), (39528917639300858899/185276480000000000000), (3710003290164412873/18527648000000000000)]
    reserve := (20024146023/100000000000) }

theorem quarter_014_004_valid : quarter_014_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_004]
  · intro i; fin_cases i <;> norm_num [quarter_014_004]
  · norm_num [quarter_014_004]
  · norm_num [quarter_014_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_004]

def quarter_014_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (68290369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-227369526439286957/593044725000000000), (-9755767/3388827), (-820414251439286957/296522362500000000), (-9755767/3388827), (-1413458976439286957/593044725000000000)]
    bernstein := [(10073437836348689809/50606483200000000000), (94768432271642857513/506064832000000000000), (7985100306579547072057/45545834880000000000000), (24779433730114407672827/151819449600000000000000), (229173926598944049100723/1518194496000000000000000)]
    reserve := (75475812619/500000000000) }

theorem quarter_014_005_valid : quarter_014_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_005]
  · intro i; fin_cases i <;> norm_num [quarter_014_005]
  · norm_num [quarter_014_005]
  · norm_num [quarter_014_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_005]

def quarter_014_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (32261287/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4847213/20000000)]
    alternative := .zero
    polynomial := [(-409539937756191047/1211803250000000000), (-64522574/24236065), (-1621343187756191047/605901625000000000), (-64522574/24236065), (-2833146437756191047/1211803250000000000)]
    bernstein := [(465061375391627830838233/3102216320000000000000000), (53877066138430155648537/387777040000000000000000), (4645994352667887962951/36354097500000000000000), (352909745491428925301/3029508125000000000000), (19883491019203713057/189344257812500000000)]
    reserve := (105012379297/1000000000000) }

theorem quarter_014_006_valid : quarter_014_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_006]
  · intro i; fin_cases i <;> norm_num [quarter_014_006]
  · norm_num [quarter_014_006]
  · norm_num [quarter_014_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_006]

def quarter_014_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(5765367/25000000), (19628063/100000000), (2879453/25000000), (2879453/25000000), (5606689/100000000), (5606689/100000000), (5765367/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7716039/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2280107/100000000), (287523/5000000), (1/100000000), (161841/5000000), (1/100000000), (894991/12500000)]
    alternative := .zero
    polynomial := [(171940707979631658496215722454773/63305840811426765370794000000000000), (-79619676086179/89499100000000), (-71549318541387146909971510154000227/31652920405713382685397000000000000), (-79619676086179/89499100000000), (-143270577790753925478439236030455227/63305840811426765370794000000000000)]
    bernstein := [(927009428820536045169843380646391637/9891537626785432089186562500000000000), (71558413035076397015938017498719549/764563294823994750855000000000000000), (177067345286225293037366724908658419789/1899175224342802961123820000000000000000), (114762312566836770011299247150713363/1238786097942675039360000000000000000), (14880287354930905937410294068674419486373/162062952477252519349232640000000000000000)]
    reserve := (91817945603/1000000000000) }

theorem quarter_014_007_valid : quarter_014_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_007]
  · intro i; fin_cases i <;> norm_num [quarter_014_007]
  · norm_num [quarter_014_007]
  · norm_num [quarter_014_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_007]

def quarter_014_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(4564983/20000000), (9923247/50000000), (5805759/50000000), (5805759/50000000), (5640321/100000000), (5640321/100000000), (4564983/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (14354369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1000513/50000000), (5810051/100000000), (1/100000000), (326183/10000000), (1/100000000), (1440701/20000000)]
    alternative := .zero
    polynomial := [(762524756876599118783855031295011/42026623974821071057786600000000000), (-24542635593063/28814020000000), (-52644726494704193622778380736480989/21013311987410535528893300000000000), (-24542635593063/28814020000000), (-106051977746284986364340616504256989/42026623974821071057786600000000000)]
    bernstein := [(9970748326167585413522498353647126854211/107588157375541941907933696000000000000000), (4985689193378203981801839212562896389119/53794078687770970953966848000000000000000), (2485936559448344855286921550262507712251/26897039343885485476983424000000000000000), (1236029534633005123450299226689715370679/13448519671942742738491712000000000000000), (612820428148511723714331815875640423091/6724259835971371369245856000000000000000)]
    reserve := (18227148953/200000000000) }

theorem quarter_014_008_valid : quarter_014_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_008]
  · intro i; fin_cases i <;> norm_num [quarter_014_008]
  · norm_num [quarter_014_008]
  · norm_num [quarter_014_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_008]

def quarter_014_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(11302289/50000000), (20073613/100000000), (5847467/50000000), (5847467/50000000), (2831841/50000000), (2831841/50000000), (11302289/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (663211/5000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1720177/100000000), (2935119/50000000), (1/100000000), (328337/10000000), (1/100000000), (7233651/100000000)]
    alternative := .zero
    polynomial := [(1016550012243442059082420303887619/31228059869869656077500992187500000), (-295121558550643/361682550000000), (-355730491112115475104842445299503423/124912239479478624310003968750000000), (-295121558550643/361682550000000), (-359796691161089243341172126515053899/124912239479478624310003968750000000)]
    bernstein := [(1842044698220481307990825291307381933881/19985958316716579889600635000000000000000), (368963350211819781945815736591534051121/3997191663343315977920127000000000000000), (883975129533700557202716123464104981273/9593259992023958347008304800000000000000), (108593198554493041708745138681190459/1184353085435056586050408000000000000), (206796982269694875096647217487011341/2273957924035308645216783360000000000)]
    reserve := (18188285727/200000000000) }

theorem quarter_014_009_valid : quarter_014_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_009]
  · intro i; fin_cases i <;> norm_num [quarter_014_009]
  · norm_num [quarter_014_009]
  · norm_num [quarter_014_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_009]

def quarter_014_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(11199333/50000000), (20312081/100000000), (5884277/50000000), (5884277/50000000), (5676739/100000000), (5676739/100000000), (11199333/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3040629/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (287441/20000000), (1482921/25000000), (1/100000000), (660311/20000000), (1/100000000), (1449977/20000000)]
    alternative := .zero
    polynomial := [(1707627812366694406997989768105951/37100835580250603789397000000000000), (-283472318162513/362494250000000), (-62072466235175523502645321280182049/18550417790125301894698500000000000), (-283472318162513/362494250000000), (-125852560282717741412288632328470049/37100835580250603789397000000000000)]
    bernstein := [(560403825608655669259617593457425719/6078600901468258924854804480000000000), (130113372877815154060163021532826089/1407083542006541417790464000000000000), (65817339284643950760840993266217501337/712336043140811592756422400000000000000), (1011067895097818050796813469020937153/10992840171926104826488000000000000000), (33839101860078106535883427749406350151/371008355802506037893970000000000000000)]
    reserve := (91208462911/1000000000000) }

theorem quarter_014_010_valid : quarter_014_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_010]
  · intro i; fin_cases i <;> norm_num [quarter_014_010]
  · norm_num [quarter_014_010]
  · norm_num [quarter_014_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_010]

def quarter_014_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(22205309/100000000), (822583/4000000), (11832891/100000000), (11832891/100000000), (5679513/100000000), (5679513/100000000), (22205309/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11050527/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (575879/50000000), (749383/12500000), (1/100000000), (829127/25000000), (1/100000000), (1450351/20000000)]
    alternative := .zero
    polynomial := [(15214135832682218116387559468717929/259477233888097946902044500000000000), (-77662697972299/103596500000000), (-534221336585275876068498799468461821/129738616944048973451022250000000000), (-77662697972299/103596500000000), (-1083656809003233970253385158405641571/259477233888097946902044500000000000)]
    bernstein := [(240679715075120793371829604051656554229/2594772338880979469020445000000000000000), (74395036553735506626553679045143083699/798391488886455221237060000000000000000), (11604869793126732156833058027545686809283/124549072266287014512981360000000000000000), (1184698113993636532718804684455188542591/12774263822183283539792960000000000000000), (61032965265412809502865529325070937987949/664261718753530744069233920000000000000000)]
    reserve := (9188090107/100000000000) }

theorem quarter_014_011_valid : quarter_014_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_011]
  · intro i; fin_cases i <;> norm_num [quarter_014_011]
  · norm_num [quarter_014_011]
  · norm_num [quarter_014_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_011]

def quarter_014_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(22022531/100000000), (10416893/50000000), (11888487/100000000), (11888487/100000000), (5672089/100000000), (5672089/100000000), (22022531/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4964961/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (86351/10000000), (606107/10000000), (1/100000000), (332837/10000000), (1/100000000), (7238839/100000000)]
    alternative := .zero
    polynomial := [(8880335852028395166956219981376023/126100610020415915762351000000000000), (-52030686030149/72388390000000), (-343018273914600355893753883585961977/63050305010207957881175500000000000), (-52030686030149/72388390000000), (-694916883681229106954463987153299977/126100610020415915762351000000000000)]
    bernstein := [(30298729856139908942811266293177924644263/322817561652264744351618560000000000000000), (15244654263895272031690959023461137116621/161408780826132372175809280000000000000000), (22872096087648533244144959882034932801021/242113171239198558263713920000000000000000), (3790045874901727863320499753039519006069/40352195206533093043952320000000000000000), (1872656789612850734669110279469322798423/20176097603266546521976160000000000000000)]
    reserve := (23203902291/250000000000) }

theorem quarter_014_012_valid : quarter_014_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_012]
  · intro i; fin_cases i <;> norm_num [quarter_014_012]
  · norm_num [quarter_014_012]
  · norm_num [quarter_014_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_012]

def quarter_014_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(21848229/100000000), (10561207/50000000), (11935929/100000000), (11935929/100000000), (1130927/20000000), (1130927/20000000), (21848229/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8802787/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (286159/50000000), (766301/12500000), (1/100000000), (1668651/50000000), (1/100000000), (180269/2500000)]
    alternative := .zero
    polynomial := [(671241942040130724930439447219823/8245241441999218848527625000000000), (-496942622163503/721076000000000), (-269332145854156236939053638067899541/32980965767996875394110500000000000), (-496942622163503/721076000000000), (-272017113622316759838775395856778833/32980965767996875394110500000000000)]
    bernstein := [(503880008769302053043551980058087442267/5276954522879500063057680000000000000000), (169349776529578814755326431439727013907/1758984840959833354352560000000000000000), (6092623207333928772834288649278580925651/63323454274554000756692160000000000000000), (167635872693678838900828032669637524483/1758984840959833354352560000000000000000), (7897906834771584153850677458444088110567/84431272366072001008922880000000000000000)]
    reserve := (3741697413/40000000000) }

theorem quarter_014_013_valid : quarter_014_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_013]
  · intro i; fin_cases i <;> norm_num [quarter_014_013]
  · norm_num [quarter_014_013]
  · norm_num [quarter_014_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_013]

def quarter_014_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(10840073/50000000), (5358291/25000000), (748491/6250000), (748491/6250000), (703427/12500000), (703427/12500000), (10840073/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3835821/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (279319/100000000), (1550951/25000000), (1/100000000), (835873/25000000), (1/100000000), (1791799/25000000)]
    alternative := .zero
    polynomial := [(91860611421592190916632188224423/1004374376785997332590500000000000), (-23677684659801/35835980000000), (-8394773422245033630952071396555577/502187188392998666295250000000000), (-23677684659801/35835980000000), (-16881407455911659452820774981335577/1004374376785997332590500000000000)]
    bernstein := [(250780852554006407498852981276182698023/2571198404572153171431680000000000000000), (633979095594348619762120117404096767/6427996011430382928579200000000000000), (472353004318359148631568904909174823/4820997008572787196434400000000000000), (384032796901769457775981449909567/4017497507143989330362000000000000), (91860611421592190916632188224423/1004374376785997332590500000000000)]
    reserve := (2858141519/31250000000) }

theorem quarter_014_014_valid : quarter_014_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_014]
  · intro i; fin_cases i <;> norm_num [quarter_014_014]
  · norm_num [quarter_014_014]
  · norm_num [quarter_014_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_014]

def quarter_014_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(2191463/10000000), (548037/2500000), (5880129/50000000), (5880129/50000000), (1341093/25000000), (1341093/25000000), (2191463/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(547951/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1314893/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (34617/25000000), (6285869/100000000), (1/100000000), (3266129/100000000), (1/100000000), (1788361/25000000)]
    alternative := .zero
    polynomial := [(30452688377152991218512548353117241/317748337361741858703359250000000000), (911585632496073287/825435903160000000), (-5525054838337347356275265115670245259/158874168680870929351679625000000000), (911585632496073287/825435903160000000), (-11080562365051847703769042779693607759/317748337361741858703359250000000000)]
    bernstein := [(30452688377152991218512548353117241/317748337361741858703359250000000000), (522334148061887093938717851710476481/5083973397787869739253748000000000000), (161702529788460551158095213815652886541/1525192019336360921776124400000000000000), (859660479507454782052041487758021046081/8134357436460591582805996800000000000000), (82739988431639179868595443161064298773441/813435743646059158280599680000000000000000)]
    reserve := (95839017223/1000000000000) }

theorem quarter_014_015_valid : quarter_014_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_015]
  · intro i; fin_cases i <;> norm_num [quarter_014_015]
  · norm_num [quarter_014_015]
  · norm_num [quarter_014_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_015]

def quarter_014_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(2816059/12500000), (11295961/50000000), (11289497/100000000), (11289497/100000000), (4886071/100000000), (4886071/100000000), (2816059/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(338403/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1363911/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (142569/100000000), (6381597/100000000), (1/100000000), (3108339/100000000), (1/100000000), (3584013/50000000)]
    alternative := .zero
    polynomial := [(123795108789934643863022756581993/2018253543646868007070500000000000), (8403518862718788259/2838717496650000000), (-12067016281010036169055162644962669/336375590607811334511750000000000), (8403518862718788259/2838717496650000000), (-72525892794850151658193998626358007/2018253543646868007070500000000000)]
    bernstein := [(64846463643297103068922054500787922177/574081007970664677566720000000000000000), (310699053244574922262675314624238515193/2583364535867991049050240000000000000000), (159979445466962671225011107483316183193/1291682267933995524525120000000000000000), (79895552480474939292326969581226543593/645841133966997762262560000000000000000), (12896931571713011422575880822663572131/107640188994499627043760000000000000000)]
    reserve := (28239247921/250000000000) }

theorem quarter_014_016_valid : quarter_014_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_016]
  · intro i; fin_cases i <;> norm_num [quarter_014_016]
  · norm_num [quarter_014_016]
  · norm_num [quarter_014_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_016]

def quarter_014_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(4622707/20000000), (23294817/100000000), (2703063/25000000), (2703063/25000000), (885361/20000000), (885361/20000000), (4622707/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1450261/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4267359/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (36671/25000000), (648927/10000000), (1/100000000), (2952157/100000000), (1/100000000), (1432779/20000000)]
    alternative := .zero
    polynomial := [(-20065880990769419800258904773637/860302912824967046403000000000000), (17271752036079623279/3502762580600000000), (-5315609406993507660241462964464129/143383818804161174400500000000000), (17271752036079623279/3502762580600000000), (-31873590560970276541648518882011137/860302912824967046403000000000000)]
    bernstein := [(6007155316062987436099941790886686421/45882822017331575808160000000000000000), (38180083413213495540160610221029577589/275296932103989454848960000000000000000), (26172924378004715148277222266083120189/183531288069326303232640000000000000000), (157112702154110847305933013154259170301/1101187728415957819395840000000000000000), (305838402477794777847304774667592232303/2202375456831915638791680000000000000000)]
    reserve := (130923841471/1000000000000) }

theorem quarter_014_017_valid : quarter_014_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_017]
  · intro i; fin_cases i <;> norm_num [quarter_014_017]
  · norm_num [quarter_014_017]
  · norm_num [quarter_014_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_017]

def quarter_014_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(4733479/20000000), (12016299/50000000), (10328509/100000000), (10328509/100000000), (3987797/100000000), (3987797/100000000), (4733479/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4173749/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (754507/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (150813/100000000), (3304809/50000000), (1/100000000), (349697/12500000), (1/100000000), (1785007/25000000)]
    alternative := .zero
    polynomial := [(-938303108316470296661723149706701/5761336134830363182504500000000000), (63032167103828382253/8973408689700000000), (-1316250562987719905311992839331739/34293667469228352276812500000000), (63032167103828382253/8973408689700000000), (-220191791473620473795753073858025451/5761336134830363182504500000000000)]
    bernstein := [(2209689196990025656670999398746083789669/14749020505165729747211520000000000000000), (14945325696750632065281497132045322357/94545003238241857353920000000000000000), (49890225832929858518739520626834061447/307271260524286036400240000000000000000), (137317617366823353456988162511935139/844151814627159440660000000000000000), (9157978314998618767952600858133799349/57613361348303631825045000000000000000)]
    reserve := (74909693027/500000000000) }

theorem quarter_014_018_valid : quarter_014_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_018]
  · intro i; fin_cases i <;> norm_num [quarter_014_018]
  · norm_num [quarter_014_018]
  · norm_num [quarter_014_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_018]

def quarter_014_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(24187649/100000000), (24807747/100000000), (98383/1000000), (98383/1000000), (1785089/50000000), (1785089/50000000), (24187649/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2755991/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (214623/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (38739/25000000), (842921/12500000), (1/100000000), (2644563/100000000), (1/100000000), (7095659/100000000)]
    alternative := .zero
    polynomial := [(-49352967857898833892190573951759161/136166231846621717237894000000000000), (169502242044830567897/18325248933400000000), (-2710406941214357746866444075619606661/68083115923310858618947000000000000), (169502242044830567897/18325248933400000000), (-5371460914570816659840697577287454161/136166231846621717237894000000000000)]
    bernstein := [(231103133386508559748946175906507303639/1361662318466217172378940000000000000000), (194463849511739561343973824200775373859/1089329854772973737903152000000000000000), (478977952931799771893799938269767112393/2614391651455136970967564800000000000000), (25623758740909483432874044259156297467/139434221410940638451603456000000000000), (4019275445172537166182203214278310791/22309475425750502152256552960000000000)]
    reserve := (84860662681/500000000000) }

theorem quarter_014_019_valid : quarter_014_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_019]
  · intro i; fin_cases i <;> norm_num [quarter_014_019]
  · norm_num [quarter_014_019]
  · norm_num [quarter_014_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_019]

def quarter_014_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(12335951/50000000), (12811393/50000000), (9341733/100000000), (9341733/100000000), (793743/25000000), (793743/25000000), (12335951/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(21611/312500), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (74869/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (159113/100000000), (6891243/100000000), (1/100000000), (99723/4000000), (1/100000000), (7035743/100000000)]
    alternative := .zero
    polynomial := [(-1547900289477889524670318125400351/2465777792439773816701125000000000), (650233737769738371763/55973908797950000000), (-51002202362177009010965165645500351/1232888896219886908350562500000000), (650233737769738371763/55973908797950000000), (-100456504434876128497260013165600351/2465777792439773816701125000000000)]
    bernstein := [(5926411807582696345103082533007437/31076387193333272471408640000000000), (91855948001792730884286799225016521/459082992628786979691264000000000000), (38861640351150723338441940934618452227/189371734459374629122646400000000000000), (32517318466542055437467326490338542383/157809778716145524268872000000000000000), (79913573099719645607162319336005234369/394524446790363810672180000000000000000)]
    reserve := (95352329257/500000000000) }

theorem quarter_014_020_valid : quarter_014_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_020]
  · intro i; fin_cases i <;> norm_num [quarter_014_020]
  · norm_num [quarter_014_020]
  · norm_num [quarter_014_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_020]

def quarter_014_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(5000253/20000000), (1647341/6250000), (8901031/100000000), (8901031/100000000), (45609/1562500), (45609/1562500), (5000253/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(130403/1562500), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (162527/100000000), (7029519/100000000), (1/100000000), (2366963/100000000), (1/100000000), (43911/625000)]
    alternative := .zero
    polynomial := [(-14388353325132467068005596997818033/15078750748360763449944000000000000), (114050303309231/8126350000000), (-323060940168862328502771172187738033/7539375374180381724972000000000000), (114050303309231/8126350000000), (-90247646716084598562505249625379719/2154107249765823349992000000000000)]
    bernstein := [(513923562030294606406660563776396181727/2412600119737722151991040000000000000000), (1074935850391026983647141829986896356963/4825200239475444303982080000000000000000), (6604912498881372988030775418067247722741/28951201436852665823892480000000000000000), (4421146212056711768183455342071638841643/19300800957901777215928320000000000000000), (512024011288461613131380670261535047551/2270682465635503201873920000000000000000)]
    reserve := (42603294083/200000000000) }

theorem quarter_014_021_valid : quarter_014_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_021]
  · intro i; fin_cases i <;> norm_num [quarter_014_021]
  · norm_num [quarter_014_021]
  · norm_num [quarter_014_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_021]

def quarter_014_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(25203183/100000000), (6759963/25000000), (8521873/100000000), (8521873/100000000), (2755017/100000000), (2755017/100000000), (25203183/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(9795569/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (41343/25000000), (1790929/25000000), (1/100000000), (1131519/50000000), (1/100000000), (1756771/25000000)]
    alternative := .zero
    polynomial := [(-33039945602355342749239398038977289/24530483624222184537400500000000000), (4553442292899/275620000000), (-16982981038892742930360674920876927/383288806628471633396882812500000), (4553442292899/275620000000), (-1053870840886780204793843796897146039/24530483624222184537400500000000000)]
    bernstein := [(14790874155896386339163611798416120605161/62798038078008792415745280000000000000000), (642608848522276154196784783811544255291/2616584919917033017322720000000000000000), (739200216506004611031044562117730645567/2943658034906662144488060000000000000000), (10305030232156376644226077974323427909/40884139373703640895667500000000000000), (59490201816564276022622118861651799/239555504142794770873051757812500000)]
    reserve := (23553083199/100000000000) }

theorem quarter_014_022_valid : quarter_014_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_022]
  · intro i; fin_cases i <;> norm_num [quarter_014_022]
  · norm_num [quarter_014_022]
  · norm_num [quarter_014_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_022]

def quarter_014_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(25315387/100000000), (13854903/50000000), (1023851/12500000), (1023851/12500000), (1319451/50000000), (1319451/50000000), (25315387/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(11267853/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (33579/20000000), (1825299/25000000), (1/100000000), (135901/6250000), (1/100000000), (3508443/50000000)]
    alternative := .zero
    polynomial := [(-46705350164735528746254728680267/25770675199736953804500000000000), (2227296350467/116593750000), (-590366641276418432602747587998767/12885337599868476902250000000000), (2227296350467/116593750000), (-1134027932388101336459240447317267/25770675199736953804500000000000)]
    bernstein := [(79915462218629647253959184358029/309743692304530694765625000000000), (17291043297628806526741889888466811/64426687999342384511250000000000000), (7567814025615248989586444751516887/27611437714003879076250000000000000), (2268151351990944952765924745846982157/8246616063915825217440000000000000000), (436348453238411379953204074567921093/1609095817349429310720000000000000000)]
    reserve := (129002565999/500000000000) }

theorem quarter_014_023_valid : quarter_014_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_023]
  · intro i; fin_cases i <;> norm_num [quarter_014_023]
  · norm_num [quarter_014_023]
  · norm_num [quarter_014_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_023]

def quarter_014_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(1013539/4000000), (3545981/12500000), (3955459/50000000), (3955459/50000000), (1283341/50000000), (1283341/50000000), (1013539/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3188813/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (85049/50000000), (744149/10000000), (1/100000000), (2101509/100000000), (1/100000000), (1748523/25000000)]
    alternative := .zero
    polynomial := [(-6517070037048444644441749266818771/2768550384810934769991750000000000), (92614774444699/4252450000000), (-16396596915590032953183529697396099/346068798101366846248968750000000), (92614774444699/4252450000000), (-124655705287671818981026488312350021/2768550384810934769991750000000000)]
    bernstein := [(1987589289508928908528921230012000909019/7087488985115993011178880000000000000000), (206353933821868987423331982121103399131/708748898511599301117888000000000000000), (63157988180152964841774539687459410321/212624669553479790335366400000000000000), (2112251158444170879696272844104824667/7087488985115993011178880000000000000), (208385040540663346701556046727123931/708748898511599301117888000000000000)]
    reserve := (35054539303/125000000000) }

theorem quarter_014_024_valid : quarter_014_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_024]
  · intro i; fin_cases i <;> norm_num [quarter_014_024]
  · norm_num [quarter_014_024]
  · norm_num [quarter_014_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_024]

def quarter_014_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(25272917/100000000), (29013597/100000000), (1537/20000), (1537/20000), (633821/25000000), (633821/25000000), (25272917/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1425021/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (171981/100000000), (7583971/100000000), (1/100000000), (2044787/100000000), (1/100000000), (434859/6250000)]
    alternative := .zero
    polynomial := [(-4600345541313536000071930950253920379/1546366413300879006368244000000000000), (11726188143959/477725000000), (-37885395698344670533858858799420265379/773183206650439503184122000000000000), (11726188143959/477725000000), (-71170445855375805067645786648586610379/1546366413300879006368244000000000000)]
    bernstein := [(119880971034572662693873171520056960469/395869801805025025630270464000000000000), (414218321980374872660785898358100062749/1319566006016750085434234880000000000000), (38003070671868969345346309097382241636919/118760940541507507689081139200000000000000), (42360658158051694605759962614406789171237/131956600601675008543423488000000000000000), (1254403827565325952807565113562348934852261/3958698018050250256302704640000000000000000)]
    reserve := (151414645027/500000000000) }

theorem quarter_014_025_valid : quarter_014_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_025]
  · intro i; fin_cases i <;> norm_num [quarter_014_025]
  · norm_num [quarter_014_025]
  · norm_num [quarter_014_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_025]

def quarter_014_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(30601963/100000000), (9029169/25000000), (491167/50000000), (491167/50000000), (71473/20000000), (71473/20000000), (30601963/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(19181609/100000000), 0, 0, 0, 0], ![0, 0, (4224849/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (211419/100000000), (294751/3125000), (1/100000000), (264131/100000000), (1/100000000), (3905121/50000000)]
    alternative := .zero
    polynomial := [(-97225171484277671467176193568917651/21425546951475642748773000000000000), (39206423902371/1174550000000), (-663666544773343990168348515499800151/10712773475737821374386500000000000), (39206423902371/1174550000000), (-72359289297788841698207108084157803/1260326291263273102869000000000000)]
    bernstein := [(17687609334306390929859850698759572679509/54849400195777645436858880000000000000000), (354016568511394455710139840256738369489/1054796157611108566093440000000000000000), (270932533669128994500083530842042724991/791097118208331424570080000000000000000), (293884567189543312211761382610428420753/857021878059025709950920000000000000000), (5550817909348263119506169372531394113/16481189962673571345210000000000000000)]
    reserve := (322475893467/1000000000000) }

theorem quarter_014_026_valid : quarter_014_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_026]
  · intro i; fin_cases i <;> norm_num [quarter_014_026]
  · norm_num [quarter_014_026]
  · norm_num [quarter_014_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_026]

def quarter_014_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(1243607/4000000), (756393/2000000), 0, 0, 0, 0, (1243607/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(269179/1250000), 0, 0, 0, 0], ![0, 0, (9876771/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (43683/20000000), (9876771/100000000), (1/100000000), (1/100000000), (1/100000000), (1571173/20000000)]
    alternative := .zero
    polynomial := [(-28351312969421607657963474737/5021317465462641400000000000), (1104002088711/29122000000), (-165071737342059673328290674737/2510658732731320700000000000), (1104002088711/29122000000), (-301792161714697738998617874737/5021317465462641400000000000)]
    bernstein := [(17376421537038714857386029249703/50213174654626414000000000000000), (72273779736979641013589391709813/200852698618505656000000000000000), (884412934004735394064083403458169/2410232383422067872000000000000000), (1180171800317896083547433894368433/3213643177896090496000000000000000), (4634956823957967124957335571146943/12854572711584361984000000000000000)]
    reserve := (86513259003/250000000000) }

theorem quarter_014_027_valid : quarter_014_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_027]
  · intro i; fin_cases i <;> norm_num [quarter_014_027]
  · norm_num [quarter_014_027]
  · norm_num [quarter_014_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_027]

def quarter_014_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(15351091/50000000), (9648909/25000000), 0, 0, 0, 0, (15351091/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(11694007/50000000), 0, 0, 0, 0], ![0, 0, (10079423/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (13731/6250000), (10079423/100000000), (1/100000000), (1/100000000), (1/100000000), (7757827/100000000)]
    alternative := .zero
    polynomial := [(-147781337612132904853706399/21911991419633799000000000), (38173565344177/915400000000), (-1490880611757435103603232413/21911991419633799000000000), (38173565344177/915400000000), (-671549637072651099374763007/10955995709816899500000000)]
    bernstein := [(10368947676988181668620560799773/28047349017131262720000000000000), (326286948172994002560997899943/849919667185795840000000000000), (2057344527866682690265948064231/5258877940712111760000000000000), (83180991851993422232457138553/212479916796448960000000000000), (674049796145539679284926145643/1752959313570703920000000000000)]
    reserve := (369694393243/1000000000000) }

theorem quarter_014_028_valid : quarter_014_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_028]
  · intro i; fin_cases i <;> norm_num [quarter_014_028]
  · norm_num [quarter_014_028]
  · norm_num [quarter_014_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_028]

def quarter_014_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 2]
    lambda := ![(30279427/100000000), (19720573/50000000), 0, 0, 0, 0, (30279427/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(6318427/25000000), 0, 0, 0, 0], ![0, 0, (1287529/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (44217/20000000), (1287529/12500000), (1/100000000), (1/100000000), (1/100000000), (3825503/50000000)]
    alternative := .zero
    polynomial := [(-102161024246493474881623242169/12811085181478287000000000000), (505106330712979/11054250000000), (-150684756163650715381384964723/2135180863579714500000000000), (505106330712979/11054250000000), (-47173383102082989259216855657/753593245969311000000000000)]
    bernstein := [(805352474013891388482239873543431/2049773629036525920000000000000000), (334181015976840754367499366587539/819909451614610368000000000000000), (136144713633548823613832818809823/327963780645844147200000000000000), (54487833252092015796219849361003/131185512258337658880000000000000), (21413641754435591520298899305399/52474204903335063552000000000000)]
    reserve := (392898251107/1000000000000) }

theorem quarter_014_029_valid : quarter_014_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_014_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_014_029]
  · intro i; fin_cases i <;> norm_num [quarter_014_029]
  · norm_num [quarter_014_029]
  · norm_num [quarter_014_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_014_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_014_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_014_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_014_029]

def quarterTable014 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 0, 0, 0, 2]
  rows := [quarter_014_000, quarter_014_001, quarter_014_002, quarter_014_003, quarter_014_004, quarter_014_005, quarter_014_006, quarter_014_007, quarter_014_008, quarter_014_009, quarter_014_010, quarter_014_011, quarter_014_012, quarter_014_013, quarter_014_014, quarter_014_015, quarter_014_016, quarter_014_017, quarter_014_018, quarter_014_019, quarter_014_020, quarter_014_021, quarter_014_022, quarter_014_023, quarter_014_024, quarter_014_025, quarter_014_026, quarter_014_027, quarter_014_028, quarter_014_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_014_000_valid
    · exact quarter_014_001_valid
    · exact quarter_014_002_valid
    · exact quarter_014_003_valid
    · exact quarter_014_004_valid
    · exact quarter_014_005_valid
    · exact quarter_014_006_valid
    · exact quarter_014_007_valid
    · exact quarter_014_008_valid
    · exact quarter_014_009_valid
    · exact quarter_014_010_valid
    · exact quarter_014_011_valid
    · exact quarter_014_012_valid
    · exact quarter_014_013_valid
    · exact quarter_014_014_valid
    · exact quarter_014_015_valid
    · exact quarter_014_016_valid
    · exact quarter_014_017_valid
    · exact quarter_014_018_valid
    · exact quarter_014_019_valid
    · exact quarter_014_020_valid
    · exact quarter_014_021_valid
    · exact quarter_014_022_valid
    · exact quarter_014_023_valid
    · exact quarter_014_024_valid
    · exact quarter_014_025_valid
    · exact quarter_014_026_valid
    · exact quarter_014_027_valid
    · exact quarter_014_028_valid
    · exact quarter_014_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
