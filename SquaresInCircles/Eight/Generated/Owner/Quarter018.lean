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

def quarter_018_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_018_000_valid : quarter_018_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_000]
  · intro i; fin_cases i <;> norm_num [quarter_018_000]
  · norm_num [quarter_018_000]
  · norm_num [quarter_018_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_000]

def quarter_018_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_018_001_valid : quarter_018_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_001]
  · intro i; fin_cases i <;> norm_num [quarter_018_001]
  · norm_num [quarter_018_001]
  · norm_num [quarter_018_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_001]

def quarter_018_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-382804973875870721/684552687500000000), (-39204036/10952843), (-1067357661375870721/342276343750000000), (-39204036/10952843), (-1751910348875870721/684552687500000000)]
    bernstein := [(646693971861456324660719/1752454880000000000000000), (155279285836763680907889/438113720000000000000000), (111621009402992369262377/328585290000000000000000), (8894952571565710129429/27382107500000000000000), (2121126590005779963799/6845526875000000000000)]
    reserve := (61971171211/200000000000) }

theorem quarter_018_002_valid : quarter_018_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_002]
  · intro i; fin_cases i <;> norm_num [quarter_018_002]
  · norm_num [quarter_018_002]
  · norm_num [quarter_018_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_002]

def quarter_018_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-556512809540135577/1127647700000000000), (-75237955/22552954), (-1684160509540135577/563823850000000000), (-75237955/22552954), (-2811808209540135577/1127647700000000000)]
    bernstein := [(3477032164953649209663/11276477000000000000000), (13294893098709221172331/45105908000000000000000), (152104840977384548853841/541270896000000000000000), (192793584408782748968639/721694528000000000000000), (730712026497435302482743/2886778112000000000000000)]
    reserve := (253123724147/1000000000000) }

theorem quarter_018_003_valid : quarter_018_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_003]
  · intro i; fin_cases i <;> norm_num [quarter_018_003]
  · norm_num [quarter_018_003]
  · norm_num [quarter_018_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_003]

def quarter_018_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4491503/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (578989/2500000)]
    alternative := .zero
    polynomial := [(-31489286020192343/72373625000000000), (-8983006/2894945), (-103862911020192343/36186812500000000), (-8983006/2894945), (-176236536020192343/72373625000000000)]
    bernstein := [(46648716103417490616537/185276480000000000000000), (4430286397231575186187/18527648000000000000000), (1257891006024344017523/5558294400000000000000), (39528917639300858899/185276480000000000000), (3710003290164412873/18527648000000000000)]
    reserve := (20024146023/100000000000) }

theorem quarter_018_004_valid : quarter_018_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_004]
  · intro i; fin_cases i <;> norm_num [quarter_018_004]
  · norm_num [quarter_018_004]
  · norm_num [quarter_018_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_004]

def quarter_018_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6829037/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-454739064020719039/1186089450000000000), (-68290370/23721789), (-1640828514020719039/593044725000000000), (-68290370/23721789), (-2826917964020719039/1186089450000000000)]
    bernstein := [(60440627198012197729/303638899200000000000), (568610594668474200953/3036388992000000000000), (15970200621588399076739/91091669760000000000000), (16519622470939316309843/101212966400000000000000), (35257527074680688279717/233568384000000000000000)]
    reserve := (75475812417/500000000000) }

theorem quarter_018_005_valid : quarter_018_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_005]
  · intro i; fin_cases i <;> norm_num [quarter_018_005]
  · norm_num [quarter_018_005]
  · norm_num [quarter_018_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_005]

def quarter_018_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (32261287/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4847213/20000000)]
    alternative := .zero
    polynomial := [(-409539937756191047/1211803250000000000), (-64522574/24236065), (-1621343187756191047/605901625000000000), (-64522574/24236065), (-2833146437756191047/1211803250000000000)]
    bernstein := [(465061375391627830838233/3102216320000000000000000), (53877066138430155648537/387777040000000000000000), (4645994352667887962951/36354097500000000000000), (352909745491428925301/3029508125000000000000), (19883491019203713057/189344257812500000000)]
    reserve := (105012379297/1000000000000) }

theorem quarter_018_006_valid : quarter_018_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_006]
  · intro i; fin_cases i <;> norm_num [quarter_018_006]
  · norm_num [quarter_018_006]
  · norm_num [quarter_018_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_006]

def quarter_018_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(1/100000000), (1/100000000), (1/50000000), (3/100000000), 0, 0, (12499999/12500000)]
    cone := fun i => (![![(24999997/50000000), 0, (99999991/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (30283989/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (24699007/100000000)]
    alternative := .zero
    polynomial := [(-921287218613779987/3087375875000000000), (-605679736485419/246990070000000), (-2004331431030294681/771843968750000000), (-605679736485419/246990070000000), (-7096038505507398737/3087375875000000000)]
    bernstein := [(3138998102291508067/30150155029296875000), (1449494753717903450591/15436879375000000000000), (10313005761909595200687/123495035000000000000000), (36032733840251940684667/493980140000000000000000), (491589394251495315450863/7903682240000000000000000)]
    reserve := (31098757473/500000000000) }

theorem quarter_018_007_valid : quarter_018_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_007]
  · intro i; fin_cases i <;> norm_num [quarter_018_007]
  · norm_num [quarter_018_007]
  · norm_num [quarter_018_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_007]

def quarter_018_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(13291081/50000000), (573941/2500000), (5969509/50000000), (5969509/50000000), 0, 0, (13291081/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1768217/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15001799/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5847/250000), (261539/4000000), (1/100000000), (3103499/100000000), (1/100000000), (104283/1562500)]
    alternative := .zero
    polynomial := [(-35181841712680207949615818639153/2639571355859592318192000000000000), (-352611986270399/333705600000000), (-4180557252845885979152882968735153/1319785677929796159096000000000000), (-352611986270399/333705600000000), (-8325932663979091750356150118831153/2639571355859592318192000000000000)]
    bernstein := [(174074795840066222569591511718312443749/2252434223666852111523840000000000000000), (87196086927802899814497144606426546721/1126217111833426055761920000000000000000), (391411148237421026253618506824995590981/5067977003250417250928640000000000000000), (64796225763999285680709391711405390283/844662833875069541821440000000000000000), (32041463210188492531322441213386795007/422331416937534770910720000000000000000)]
    reserve := (37934027549/500000000000) }

theorem quarter_018_008_valid : quarter_018_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_008]
  · intro i; fin_cases i <;> norm_num [quarter_018_008]
  · norm_num [quarter_018_008]
  · norm_num [quarter_018_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_008]

def quarter_018_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(2632431/10000000), (23245449/100000000), (2410593/20000000), (2410593/20000000), 0, 0, (2632431/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1785093/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3431111/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (502749/25000000), (1654071/25000000), (1/100000000), (3133119/100000000), (1/100000000), (6701813/100000000)]
    alternative := .zero
    polynomial := [(5565490145518124310269528841877/1134582129722031966246700000000000), (-17706837448203/17636350000000), (-2019299703172402211863230974399373/567291064861015983123350000000000), (-17706837448203/17636350000000), (-4044164896490322548036731477640623/1134582129722031966246700000000000)]
    bernstein := [(1075220596930541411588009399340614149/13964087750425008815344000000000000000), (5611214679495201256345531148402500459/72613256302210045839788800000000000000), (2241654344277080153146484084984926857/29045302520884018335915520000000000000), (178247439781864485390769313808312263/2323624201670721466873241600000000000), (1084992062699605819807444233849501/14299225856435209026912256000000000)]
    reserve := (3035107141/40000000000) }

theorem quarter_018_009_valid : quarter_018_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_009]
  · intro i; fin_cases i <;> norm_num [quarter_018_009]
  · norm_num [quarter_018_009]
  · norm_num [quarter_018_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_009]

def quarter_018_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(26074779/100000000), (23538741/100000000), (12155851/100000000), (12155851/100000000), 0, 0, (26074779/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3600661/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6216417/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1679929/100000000), (6694051/100000000), (1/100000000), (394983/12500000), (1/100000000), (1342851/20000000)]
    alternative := .zero
    polynomial := [(1385234006036437743272957801994620429/63623110630341371661141408000000000000), (-53356134816633/55952125000000), (-131428893158266230938741088714306339571/31811555315170685830570704000000000000), (-53356134816633/55952125000000), (-264243020322568899620755135230607299571/63623110630341371661141408000000000000)]
    bernstein := [(61956331285514482239299329111897259177/801846957359625410227800637440000000000), (14419485475828893963413281774256898087/185612721611024400515694592000000000000), (94880121403287408285990373324674579617723/1221563724102554335893915033600000000000000), (1455827238604361949473079320898958725987/18851292038619665677375232000000000000000), (48580243079319485870393143426487112436229/636231106303413716611414080000000000000000)]
    reserve := (76356284057/1000000000000) }

theorem quarter_018_010_valid : quarter_018_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_010]
  · intro i; fin_cases i <;> norm_num [quarter_018_010]
  · norm_num [quarter_018_010]
  · norm_num [quarter_018_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_010]

def quarter_018_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(1614479/6250000), (11920147/50000000), (12248189/100000000), (12248189/100000000), 0, 0, (1614479/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3628013/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5564867/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (336377/25000000), (6772473/100000000), (1/100000000), (3183867/100000000), (1/100000000), (3355459/50000000)]
    alternative := .zero
    polynomial := [(404082424576378123609521932227055933/10816777872320567421206628000000000000), (-15187001633929/16777295000000), (-27144084667832888073962407500660144067/5408388936160283710603314000000000000), (-15187001633929/16777295000000), (-54692251760242154271534336933547344067/10816777872320567421206628000000000000)]
    bernstein := [(8446702321791506682122482505734319172533/108167778723205674212066280000000000000000), (34034605827690948390270572092326636440899/432671114892822696848265120000000000000000), (408657215284566344342746665967158901861091/5192053378713872362179181440000000000000000), (541586943574176537950052461509648098667391/6922737838285163149572241920000000000000000), (2138808813339198423364585473035984392480973/27690951353140652598288967680000000000000000)]
    reserve := (19309636441/250000000000) }

theorem quarter_018_011_valid : quarter_018_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_011]
  · intro i; fin_cases i <;> norm_num [quarter_018_011]
  · norm_num [quarter_018_011]
  · norm_num [quarter_018_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_011]

def quarter_018_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(25592991/100000000), (24152929/100000000), (2466109/20000000), (2466109/20000000), 0, 0, (25592991/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3652407/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4909193/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (251923/25000000), (6852271/100000000), (1/100000000), (128211/4000000), (1/100000000), (133827/2000000)]
    alternative := .zero
    polynomial := [(21962566905189537226700817605883/424646127560797948876000000000000), (-95752211243471/111522500000000), (-1389164529739691782171584247389117/212323063780398974438000000000000), (-95752211243471/111522500000000), (-400041660912081871652838473197731/60663732508685421268000000000000)]
    bernstein := [(86385861632159525983172150290187404923/1087094086555642749122560000000000000000), (43598730346684950533207790444726792841/543547043277821374561280000000000000000), (21816211305133715419400036378779325747/271773521638910687280640000000000000000), (349164395625950820058133880960043279/4383443897401785278720000000000000000), (5323949374214233571341033763748354283/67943380409727671820160000000000000000)]
    reserve := (313434471/4000000000) }

theorem quarter_018_012_valid : quarter_018_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_012]
  · intro i; fin_cases i <;> norm_num [quarter_018_012]
  · norm_num [quarter_018_012]
  · norm_num [quarter_018_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_012]

def quarter_018_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(12678347/50000000), (12239757/50000000), (12403549/100000000), (12403549/100000000), 0, 0, (12678347/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (229627/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8502497/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (41667/6250000), (6934189/100000000), (1/100000000), (806063/25000000), (1/100000000), (6655173/100000000)]
    alternative := .zero
    polynomial := [(11173665420999674480707131708389213/172216093599868690980293000000000000), (-270713007958381/332758650000000), (-834222444077175164064194981318582037/86108046799934345490146500000000000), (-270713007958381/332758650000000), (-1679618553575350002609097094345553287/172216093599868690980293000000000000)]
    bernstein := [(6727111972635582960488856739748093891339/82663724927936971670540640000000000000000), (4537798420693645502677993433833294662313/55109149951957981113693760000000000000000), (9070202824410987440332583739505367835913/110218299903915962227387520000000000000000), (17907580252266784480090681258235364897913/220436599807831924454775040000000000000000), (104717140665571646657488155474006022024939/1322619598846991546728650240000000000000000)]
    reserve := (79174042753/1000000000000) }

theorem quarter_018_013_valid : quarter_018_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_013]
  · intro i; fin_cases i <;> norm_num [quarter_018_013]
  · norm_num [quarter_018_013]
  · norm_num [quarter_018_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_013]

def quarter_018_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(785019/3125000), (12411481/50000000), (12467911/100000000), (12467911/100000000), 0, 0, (785019/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (461637/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7186227/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (324233/100000000), (1403799/20000000), (1/100000000), (3240983/100000000), (1/100000000), (6602093/100000000)]
    alternative := .zero
    polynomial := [(373390717591281314418807840113365517/4869569161825722784643986500000000000), (-127072349696237/165052325000000), (-47675876418301766605782996395733994483/2434784580912861392321993250000000000), (-127072349696237/165052325000000), (-95725143554194814525984800631581354483/4869569161825722784643986500000000000)]
    bernstein := [(1043310161782686796582043538179318845419917/12466097054273850328688605440000000000000000), (25470918144440369238192378535578910667/299665794573890632901168400000000000000), (1969541905088361796467324468212208887117/23373931976763469366291135200000000000000), (198411105517959055848092973810005071/2434784580912861392321993250000000000), (373390717591281314418807840113365517/4869569161825722784643986500000000000)]
    reserve := (76678388823/1000000000000) }

theorem quarter_018_014_valid : quarter_018_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_014]
  · intro i; fin_cases i <;> norm_num [quarter_018_014]
  · norm_num [quarter_018_014]
  · norm_num [quarter_018_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_014]

def quarter_018_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(25173203/100000000), (25181071/100000000), (12236261/100000000), (12236261/100000000), 0, 0, (25173203/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(157357/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (22653/625000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5942809/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (159057/100000000), (3537097/50000000), (1/100000000), (3180767/100000000), (1/100000000), (1321647/20000000)]
    alternative := .zero
    polynomial := [(64433607736364834355649034337357373/788362274070072568523907000000000000), (44620634099161546537/35036201146500000000), (-1760364709971180521368213103238796403/43797904115004031584661500000000000), (44620634099161546537/35036201146500000000), (-31750998387217614218983484892635692627/788362274070072568523907000000000000)]
    bernstein := [(64433607736364834355649034337357373/788362274070072568523907000000000000), (141417528940567529799141215520946321/1576724548140145137047814000000000000), (39297726598936923715160950194675309197/420459879504038703212750400000000000000), (234755034935975791636184022030003049921/2522759277024232219276502400000000000000), (178517547117963689246076016968078507820973/2018207421619385775421201920000000000000000)]
    reserve := (20432740713/250000000000) }

theorem quarter_018_015_valid : quarter_018_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_015]
  · intro i; fin_cases i <;> norm_num [quarter_018_015]
  · norm_num [quarter_018_015]
  · norm_num [quarter_018_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_015]

def quarter_018_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(12747421/50000000), (25566647/100000000), (2344367/20000000), (2344367/20000000), 0, 0, (12747421/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(957403/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1736051/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1182491/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (161341/100000000), (7106801/100000000), (1/100000000), (761761/25000000), (1/100000000), (1333631/20000000)]
    alternative := .zero
    polynomial := [(3543248640118326587013782791732943/82711873268679129262788000000000000), (180920841628445743961/53792339792750000000), (-1688323816226768434016910900838387057/41355936634339564631394000000000000), (180920841628445743961/53792339792750000000), (-3380190881093655194620835584468507057/82711873268679129262788000000000000)]
    bernstein := [(1652289413407331091878091435281060020811/16287876582139890070210560000000000000000), (297876838098408980914009255221118377337/2714646097023315011701760000000000000000), (2581153772051342244364857134765060460347/22686685239409132597793280000000000000000), (1002012064609852457660184482656182528181/8822599815325773788030720000000000000000), (1443936118074867152906674307681301367343/13233899722988660682046080000000000000000)]
    reserve := (101442898653/1000000000000) }

theorem quarter_018_016_valid : quarter_018_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_016]
  · intro i; fin_cases i <;> norm_num [quarter_018_016]
  · norm_num [quarter_018_016]
  · norm_num [quarter_018_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_016]

def quarter_018_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(6447091/25000000), (12995313/50000000), (11216323/100000000), (11216323/100000000), 0, 0, (6447091/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3236187/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1661183/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1735667/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (163659/100000000), (7152757/100000000), (1/100000000), (1457819/50000000), (1/100000000), (1340677/20000000)]
    alternative := .zero
    polynomial := [(-13681325388785791902605486816014703/269167241390847834891714000000000000), (100959620771940795801/18284488095250000000), (-95113087235423150790503646549146809951/2287921551822206596579569000000000000), (100959620771940795801/18284488095250000000), (-189993591939236943118662999822421369951/4575843103644413193159138000000000000)]
    bernstein := [(89139435865448360160207813210171298349249/732134896583106110905462080000000000000000), (17359507186513226529667658449835459384377/133115435742382929255538560000000000000000), (1183924481757532811360713685487431506216523/8785618758997273330865544960000000000000000), (71767803462953915051146602513925976825393/532461742969531717022154240000000000000000), (1528296412893224772551763637305552419245169/11714158345329697774487393280000000000000000)]
    reserve := (121752748409/1000000000000) }

theorem quarter_018_017_valid : quarter_018_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_017]
  · intro i; fin_cases i <;> norm_num [quarter_018_017]
  · norm_num [quarter_018_017]
  · norm_num [quarter_018_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_017]

def quarter_018_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(2605341/10000000), (26455431/100000000), (85751/800000), (85751/800000), 0, 0, (2605341/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1148631/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3175017/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1087933/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (166017/100000000), (1442521/20000000), (1/100000000), (348291/12500000), (1/100000000), (6713711/100000000)]
    alternative := .zero
    polynomial := [(-1208397986095381413035697095329737197/5973217439155528023991008000000000000), (72059898707170881867/9288251325725000000), (-126759912982645369240518924032857737197/2986608719577764011995504000000000000), (72059898707170881867/9288251325725000000), (-252311427979195357068002150970385737197/5973217439155528023991008000000000000)]
    bernstein := [(2182952533669638399862976376348405448493443/15291436644238151741416980480000000000000000), (580416286943170836040182072202759890560881/3822859161059537935354245120000000000000000), (448740402904458456352241785164052927397581/2867144370794653451515683840000000000000000), (37461093989473585759291930108422398070509/238928697566221120959640320000000000000000), (9116417634201887236444788122075088453403/59732174391555280239910080000000000000000)]
    reserve := (71378268257/500000000000) }

theorem quarter_018_018_valid : quarter_018_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_018]
  · intro i; fin_cases i <;> norm_num [quarter_018_018]
  · norm_num [quarter_018_018]
  · norm_num [quarter_018_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_018]

def quarter_018_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(5257907/20000000), (26963519/100000000), (5114353/50000000), (5114353/50000000), 0, 0, (5257907/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(5990969/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (121193/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (426399/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (168421/100000000), (7286907/100000000), (1/100000000), (2658911/100000000), (1/100000000), (6699139/100000000)]
    alternative := .zero
    polynomial := [(-12100599055938322915006864691773272899/29147478782552861471171684000000000000), (103428238529155584039/10257051722900000000), (-633149863740884149741488760655365972899/14573739391276430735585842000000000000), (103428238529155584039/10257051722900000000), (-1254199128425829976567970656618958672899/29147478782552861471171684000000000000)]
    bernstein := [(47961135011207229621098692145083402157301/291474787825528614711716840000000000000000), (40591547956512880858067963267973409193281/233179830260422891769373472000000000000000), (33415764974927828393327019576194641239129/186543864208338313415498777600000000000000), (5362801927909311525402991727492838249353/29847018273334130146479804416000000000000), (838915837542741631705230727377231192069/4775522923733460823436768706560000000000)]
    reserve := (16454642739/100000000000) }

theorem quarter_018_019_valid : quarter_018_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_019]
  · intro i; fin_cases i <;> norm_num [quarter_018_019]
  · norm_num [quarter_018_019]
  · norm_num [quarter_018_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_019]

def quarter_018_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(26494723/100000000), (27515861/100000000), (9747347/100000000), (9747347/100000000), 0, 0, (26494723/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1485291/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2887243/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (42717/25000000), (115251/1562500), (1/100000000), (316723/12500000), (1/100000000), (6694687/100000000)]
    alternative := .zero
    polynomial := [(-76934052250570399318483887615833303/111348417743873840041248000000000000), (71133168053961/5695600000000), (-827276782171882035527710546538971101/18558069623978973340208000000000000), (71133168053961/5695600000000), (-4886726640780721813847779391617993303/111348417743873840041248000000000000)]
    bernstein := [(1139376612435430869706019449472819931/6081108254385429984119357440000000000), (44988898023537783164931084361129294943/228041559539453624404475904000000000000), (577572199747748329569546236363872874977/2850519494243170305055948800000000000000), (1449026096872457576180035948267321988899/7126298735607925762639872000000000000000), (3552011270880095470778120139791513480857/17815746839019814406599680000000000000000)]
    reserve := (46840829203/250000000000) }

theorem quarter_018_020_valid : quarter_018_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_020]
  · intro i; fin_cases i <;> norm_num [quarter_018_020]
  · norm_num [quarter_018_020]
  · norm_num [quarter_018_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_020]

def quarter_018_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(26651919/100000000), (561953/2000000), (1162407/12500000), (1162407/12500000), 0, 0, (26651919/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1779361/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (550903/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (173257/100000000), (7478449/100000000), (1/100000000), (302163/12500000), (1/100000000), (6734407/100000000)]
    alternative := .zero
    polynomial := [(-5796951686183510782988886563628280433/5624730117985129802961094400000000000), (4628831715511/309387500000), (-128852885972286563475487328790743416433/2812365058992564901480547200000000000), (4628831715511/309387500000), (-251908820258389616167985771017858552433/5624730117985129802961094400000000000)]
    bernstein := [(189460357435175648334850821992006736535327/899956818877620768473775104000000000000000), (397162664417338356228559717422473591155363/1799913637755241536947550208000000000000000), (2441658773721941289268238991060129544431541/10799481826531449221685301248000000000000000), (1632713473149334540489089702408482246984043/7199654551020966147790200832000000000000000), (3206025228990904646106935510662850894273967/14399309102041932295580401664000000000000000)]
    reserve := (105260804441/500000000000) }

theorem quarter_018_021_valid : quarter_018_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_021]
  · intro i; fin_cases i <;> norm_num [quarter_018_021]
  · norm_num [quarter_018_021]
  · norm_num [quarter_018_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_021]

def quarter_018_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(5351111/20000000), (28705353/100000000), (1111471/12500000), (1111471/12500000), 0, 0, (5351111/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(259973/2500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1316907/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (87779/50000000), (7593279/100000000), (1/100000000), (2311379/100000000), (1/100000000), (3380297/50000000)]
    alternative := .zero
    polynomial := [(-312987568800897376000096299490413851/216987525828894458182582625000000000), (15394948643407/877790000000), (-10234814747188266709744259304487643327/216987525828894458182582625000000000), (15394948643407/877790000000), (-2480456794596842333436040751249307369/54246881457223614545645656250000000)]
    bernstein := [(1906450262040280950829430172830200531343/8168942148852497249226640000000000000000), (995619006822651289849780922646430773271/4084471074426248624613320000000000000000), (12983163904353216426441305024720444951581/52077006198934669963819830000000000000000), (542405902804648179595773803479248154711/2169875258288944581825826250000000000000), (16658856769892418733688315330180827737/67808601821529518182057070312500000000)]
    reserve := (46675572609/200000000000) }

theorem quarter_018_022_valid : quarter_018_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_022]
  · intro i; fin_cases i <;> norm_num [quarter_018_022]
  · norm_num [quarter_018_022]
  · norm_num [quarter_018_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_022]

def quarter_018_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(26804537/100000000), (5867961/20000000), (213139/2500000), (213139/2500000), 0, 0, (13402269/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(11930673/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (126267/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (44443/25000000), (7720229/100000000), (1/100000000), (443237/20000000), (1/100000000), (6772971/100000000)]
    alternative := .zero
    polynomial := [(-33149636178220320461649835768609869/17167123135549125642746150000000000), (359573811997437/17777200000000), (-119279043006542501332743022876164909/2452446162221303663249450000000000), (359573811997437/17777200000000), (-400901832433788594433775662182272247/8583561567774562821373075000000000)]
    bernstein := [(686564645053972463068863467765369889/2682362989929550881679085937500000000), (4160825092564871519378160591489418053/15606475577771932402496500000000000000), (3338917289446411381131713705959696431/12262230811106518316247250000000000000), (545232789508353980406515219351715268911/1997628873954807347519552000000000000000), (5899232489450540159041721032669125877533/21973917613502880822715072000000000000000)]
    reserve := (127977579401/500000000000) }

theorem quarter_018_023_valid : quarter_018_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_023]
  · intro i; fin_cases i <;> norm_num [quarter_018_023]
  · norm_num [quarter_018_023]
  · norm_num [quarter_018_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_023]

def quarter_018_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(6699441/25000000), (30001603/100000000), (1640287/20000000), (1640287/20000000), 0, 0, (6699441/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(269797/2000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2429331/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (89947/50000000), (1964739/25000000), (1/100000000), (213193/10000000), (1/100000000), (6771259/100000000)]
    alternative := .zero
    polynomial := [(-321622570396371167834688562819927/128577473082485473816000000000000), (18834483551981/817700000000), (-41980221958292424071405399262499051/835753575036155579804000000000000), (18834483551981/817700000000), (-79779350501432022960959847208339051/1671507150072311159608000000000000)]
    bernstein := [(1190742751245876234507959814170161307189/4279058304185116568596480000000000000000), (123763521718785469271301166894819900461/427905830418511656859648000000000000000), (37878186580786724687954687241966548351/128371749125553497057894400000000000000), (1265322750013773382812097486132706477/4279058304185116568596480000000000000), (7325717776781115870462225870076133/25170931201088920991744000000000000)]
    reserve := (27827214929/100000000000) }

theorem quarter_018_024_valid : quarter_018_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_024]
  · intro i; fin_cases i <;> norm_num [quarter_018_024]
  · norm_num [quarter_018_024]
  · norm_num [quarter_018_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_024]

def quarter_018_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(15883043/50000000), (36467829/100000000), 0, 0, 0, 0, (15883043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(17911403/100000000), 0, 0, 0, 0], ![0, 0, (9523737/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (108083/50000000), (9523737/100000000), (1/100000000), (1/100000000), (1/100000000), (1605331/20000000)]
    alternative := .zero
    polynomial := [(-116474029439703911029118398093/30600999859265881500000000000), (666923477246639/21616600000000), (-946153230922874177700068405593/15300499929632940750000000000), (666923477246639/21616600000000), (-1775832432406044444371018413093/30600999859265881500000000000)]
    bernstein := [(80332237445640859189135728487/270132964274898816000000000000), (8106740806002107337247007370383/26112853213240218880000000000000), (745521611685827884783023320288273/2350156789191619699200000000000000), (829317519503326380960628169148479/2611285321324021888000000000000000), (24396544983590621596341072405115787/78338559639720656640000000000000000)]
    reserve := (14869017867/50000000000) }

theorem quarter_018_025_valid : quarter_018_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_025]
  · intro i; fin_cases i <;> norm_num [quarter_018_025]
  · norm_num [quarter_018_025]
  · norm_num [quarter_018_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_025]

def quarter_018_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(15722243/50000000), (9277757/25000000), 0, 0, 0, 0, (15722243/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1970971/10000000), 0, 0, 0, 0], ![0, 0, (9691711/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5431/2500000), (9691711/100000000), (1/100000000), (1/100000000), (1/100000000), (7945393/100000000)]
    alternative := .zero
    polynomial := [(-2929476629426754590776540691641/627316774225416469500000000000), (18627739998979/543100000000), (-19975363257504271761569552371141/313658387112708234750000000000), (18627739998979/543100000000), (-37021249885581788932362564050641/627316774225416469500000000000)]
    bernstein := [(517041849981456012383754812584009919/1605930942017066161920000000000000000), (134641206332102064125632924375293787/401482735504266540480000000000000000), (103066553403546041443996265923069553/301112051628199905360000000000000000), (8597189961607499432140785161134223/25092670969016658780000000000000000), (2109106841173195157256250416284279/6273167742254164695000000000000000)]
    reserve := (80489427729/250000000000) }

theorem quarter_018_026_valid : quarter_018_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_026]
  · intro i; fin_cases i <;> norm_num [quarter_018_026]
  · norm_num [quarter_018_026]
  · norm_num [quarter_018_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_026]

def quarter_018_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(1243607/4000000), (756393/2000000), 0, 0, 0, 0, (1243607/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(269179/1250000), 0, 0, 0, 0], ![0, 0, (9876771/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (43683/20000000), (9876771/100000000), (1/100000000), (1/100000000), (1/100000000), (1571173/20000000)]
    alternative := .zero
    polynomial := [(-28351312969421607657963474737/5021317465462641400000000000), (1104002088711/29122000000), (-165071737342059673328290674737/2510658732731320700000000000), (1104002088711/29122000000), (-301792161714697738998617874737/5021317465462641400000000000)]
    bernstein := [(17376421537038714857386029249703/50213174654626414000000000000000), (72273779736979641013589391709813/200852698618505656000000000000000), (884412934004735394064083403458169/2410232383422067872000000000000000), (1180171800317896083547433894368433/3213643177896090496000000000000000), (4634956823957967124957335571146943/12854572711584361984000000000000000)]
    reserve := (86513259003/250000000000) }

theorem quarter_018_027_valid : quarter_018_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_027]
  · intro i; fin_cases i <;> norm_num [quarter_018_027]
  · norm_num [quarter_018_027]
  · norm_num [quarter_018_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_027]

def quarter_018_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(15351091/50000000), (9648909/25000000), 0, 0, 0, 0, (15351091/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(11694007/50000000), 0, 0, 0, 0], ![0, 0, (10079423/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (13731/6250000), (10079423/100000000), (1/100000000), (1/100000000), (1/100000000), (7757827/100000000)]
    alternative := .zero
    polynomial := [(-147781337612132904853706399/21911991419633799000000000), (38173565344177/915400000000), (-1490880611757435103603232413/21911991419633799000000000), (38173565344177/915400000000), (-671549637072651099374763007/10955995709816899500000000)]
    bernstein := [(10368947676988181668620560799773/28047349017131262720000000000000), (326286948172994002560997899943/849919667185795840000000000000), (2057344527866682690265948064231/5258877940712111760000000000000), (83180991851993422232457138553/212479916796448960000000000000), (674049796145539679284926145643/1752959313570703920000000000000)]
    reserve := (369694393243/1000000000000) }

theorem quarter_018_028_valid : quarter_018_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_028]
  · intro i; fin_cases i <;> norm_num [quarter_018_028]
  · norm_num [quarter_018_028]
  · norm_num [quarter_018_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_028]

def quarter_018_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 2]
    lambda := ![(30279427/100000000), (19720573/50000000), 0, 0, 0, 0, (30279427/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(6318427/25000000), 0, 0, 0, 0], ![0, 0, (1287529/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (44217/20000000), (1287529/12500000), (1/100000000), (1/100000000), (1/100000000), (3825503/50000000)]
    alternative := .zero
    polynomial := [(-102161024246493474881623242169/12811085181478287000000000000), (505106330712979/11054250000000), (-150684756163650715381384964723/2135180863579714500000000000), (505106330712979/11054250000000), (-47173383102082989259216855657/753593245969311000000000000)]
    bernstein := [(805352474013891388482239873543431/2049773629036525920000000000000000), (334181015976840754367499366587539/819909451614610368000000000000000), (136144713633548823613832818809823/327963780645844147200000000000000), (54487833252092015796219849361003/131185512258337658880000000000000), (21413641754435591520298899305399/52474204903335063552000000000000)]
    reserve := (392898251107/1000000000000) }

theorem quarter_018_029_valid : quarter_018_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_018_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_018_029]
  · intro i; fin_cases i <;> norm_num [quarter_018_029]
  · norm_num [quarter_018_029]
  · norm_num [quarter_018_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_018_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_018_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_018_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_018_029]

def quarterTable018 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 0, 0, 2, 2]
  rows := [quarter_018_000, quarter_018_001, quarter_018_002, quarter_018_003, quarter_018_004, quarter_018_005, quarter_018_006, quarter_018_007, quarter_018_008, quarter_018_009, quarter_018_010, quarter_018_011, quarter_018_012, quarter_018_013, quarter_018_014, quarter_018_015, quarter_018_016, quarter_018_017, quarter_018_018, quarter_018_019, quarter_018_020, quarter_018_021, quarter_018_022, quarter_018_023, quarter_018_024, quarter_018_025, quarter_018_026, quarter_018_027, quarter_018_028, quarter_018_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_018_000_valid
    · exact quarter_018_001_valid
    · exact quarter_018_002_valid
    · exact quarter_018_003_valid
    · exact quarter_018_004_valid
    · exact quarter_018_005_valid
    · exact quarter_018_006_valid
    · exact quarter_018_007_valid
    · exact quarter_018_008_valid
    · exact quarter_018_009_valid
    · exact quarter_018_010_valid
    · exact quarter_018_011_valid
    · exact quarter_018_012_valid
    · exact quarter_018_013_valid
    · exact quarter_018_014_valid
    · exact quarter_018_015_valid
    · exact quarter_018_016_valid
    · exact quarter_018_017_valid
    · exact quarter_018_018_valid
    · exact quarter_018_019_valid
    · exact quarter_018_020_valid
    · exact quarter_018_021_valid
    · exact quarter_018_022_valid
    · exact quarter_018_023_valid
    · exact quarter_018_024_valid
    · exact quarter_018_025_valid
    · exact quarter_018_026_valid
    · exact quarter_018_027_valid
    · exact quarter_018_028_valid
    · exact quarter_018_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
