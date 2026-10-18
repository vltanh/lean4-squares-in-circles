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

def quarter_034_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-45817252649015643/64076356250000000), (-42064340/10252217), (-109893608899015643/32038178125000000), (-42064340/10252217), (-173969965149015643/64076356250000000)]
    bernstein := [(132248051520895638453/262456755200000000000), (319594416411056309041/656141888000000000000), (2313698804266911308743/4921064160000000000000), (1858227021179647709033/4100886800000000000000), (4469735798493297355557/10252217000000000000000)]
    reserve := (217988743239/500000000000) }

theorem quarter_034_000_valid : quarter_034_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_000]
  · intro i; fin_cases i <;> norm_num [quarter_034_000]
  · norm_num [quarter_034_000]
  · norm_num [quarter_034_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_000]

def quarter_034_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3357228017379484783/5305390750000000000), (-81371960/21221563), (-8662618767379484783/2652695375000000000), (-81371960/21221563), (-13968009517379484783/5305390750000000000)]
    bernstein := [(368492022086778488262417/848862520000000000000000), (710392326336680697197803/1697725040000000000000000), (42284096226730102361323/105013920000000000000000), (2626338989756321054215843/6790900160000000000000000), (5034921367483818119986337/13581800320000000000000000)]
    reserve := (74142179223/200000000000) }

theorem quarter_034_001_valid : quarter_034_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_001]
  · intro i; fin_cases i <;> norm_num [quarter_034_001]
  · norm_num [quarter_034_001]
  · norm_num [quarter_034_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_001]

def quarter_034_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-382804973875870721/684552687500000000), (-39204036/10952843), (-1067357661375870721/342276343750000000), (-39204036/10952843), (-1751910348875870721/684552687500000000)]
    bernstein := [(646693971861456324660719/1752454880000000000000000), (155279285836763680907889/438113720000000000000000), (111621009402992369262377/328585290000000000000000), (8894952571565710129429/27382107500000000000000), (2121126590005779963799/6845526875000000000000)]
    reserve := (61971171211/200000000000) }

theorem quarter_034_002_valid : quarter_034_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_002]
  · intro i; fin_cases i <;> norm_num [quarter_034_002]
  · norm_num [quarter_034_002]
  · norm_num [quarter_034_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_002]

def quarter_034_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-556512809540135577/1127647700000000000), (-75237955/22552954), (-1684160509540135577/563823850000000000), (-75237955/22552954), (-2811808209540135577/1127647700000000000)]
    bernstein := [(3477032164953649209663/11276477000000000000000), (13294893098709221172331/45105908000000000000000), (152104840977384548853841/541270896000000000000000), (192793584408782748968639/721694528000000000000000), (730712026497435302482743/2886778112000000000000000)]
    reserve := (253123724147/1000000000000) }

theorem quarter_034_003_valid : quarter_034_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_003]
  · intro i; fin_cases i <;> norm_num [quarter_034_003]
  · norm_num [quarter_034_003]
  · norm_num [quarter_034_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_003]

def quarter_034_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4491503/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (578989/2500000)]
    alternative := .zero
    polynomial := [(-31489286020192343/72373625000000000), (-8983006/2894945), (-103862911020192343/36186812500000000), (-8983006/2894945), (-176236536020192343/72373625000000000)]
    bernstein := [(46648716103417490616537/185276480000000000000000), (4430286397231575186187/18527648000000000000000), (1257891006024344017523/5558294400000000000000), (39528917639300858899/185276480000000000000), (3710003290164412873/18527648000000000000)]
    reserve := (20024146023/100000000000) }

theorem quarter_034_004_valid : quarter_034_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_004]
  · intro i; fin_cases i <;> norm_num [quarter_034_004]
  · norm_num [quarter_034_004]
  · norm_num [quarter_034_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_004]

def quarter_034_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (68290369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-227369526439286957/593044725000000000), (-9755767/3388827), (-820414251439286957/296522362500000000), (-9755767/3388827), (-1413458976439286957/593044725000000000)]
    bernstein := [(10073437836348689809/50606483200000000000), (94768432271642857513/506064832000000000000), (7985100306579547072057/45545834880000000000000), (24779433730114407672827/151819449600000000000000), (229173926598944049100723/1518194496000000000000000)]
    reserve := (75475812619/500000000000) }

theorem quarter_034_005_valid : quarter_034_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_005]
  · intro i; fin_cases i <;> norm_num [quarter_034_005]
  · norm_num [quarter_034_005]
  · norm_num [quarter_034_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_005]

def quarter_034_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(653359/25000000), (7273709/50000000), (7273709/50000000), (21892763/100000000), (21892763/100000000), (21892763/100000000), (653359/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (148073/2000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (250213/6250000), (1/100000000), (3320893/50000000), (1/100000000), (1/100000000), (6350677/100000000)]
    alternative := .zero
    polynomial := [(9304814189536539921547255539/105539437026869829860000000000), (-14393358842558438597/63560877768040000000), (-4052457248814568905955087661/52769718513434914930000000000), (-14393358842558438597/63560877768040000000), (-17409728687165677733457430861/105539437026869829860000000000)]
    bernstein := [(37118664480363428461175821926409779/270180958788786764441600000000000000), (1148413924135121532955060766744089/8443154962149586388800000000000000), (852669306050259252246319719237101/6332366221612189791600000000000000), (35168473272812496458998413049413/263848592567174574650000000000000), (2175599644517642670434196440741/16490537035448410915625000000000)]
    reserve := (32982546897/250000000000) }

theorem quarter_034_006_valid : quarter_034_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_006]
  · intro i; fin_cases i <;> norm_num [quarter_034_006]
  · norm_num [quarter_034_006]
  · norm_num [quarter_034_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_006]

def quarter_034_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(748021/25000000), (2855561/20000000), (2855561/20000000), (10910037/50000000), (10910037/50000000), (10910037/50000000), (748021/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1502131/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3960473/100000000), (1/100000000), (131779/2000000), (1/100000000), (1/100000000), (1609323/25000000)]
    alternative := .zero
    polynomial := [(18998849287007076225476966519/209979303726696710250000000000), (-27100772459167200209/127473605795580000000), (-6616214802296879608120008481/104989651863348355125000000000), (-27100772459167200209/127473605795580000000), (-32231278891600835441716983481/209979303726696710250000000000)]
    bernstein := [(84875597612524234554562889911/643318945241105117187500000000), (22858693774834802255881968536293/174982753105580591875000000000000), (1629484555611697205948258280018559/12598758223601802615000000000000000), (1433933418354740635616306388016357/11198896198757157880000000000000000), (4007886800349613284057589215763607/31620412796490798720000000000000000)]
    reserve := (7921873969/62500000000) }

theorem quarter_034_007_valid : quarter_034_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_007]
  · intro i; fin_cases i <;> norm_num [quarter_034_007]
  · norm_num [quarter_034_007]
  · norm_num [quarter_034_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_007]

def quarter_034_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(673727/20000000), (7000557/50000000), (7000557/50000000), (43507/200000), (43507/200000), (43507/200000), (673727/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7582133/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3909713/100000000), (1/100000000), (3268389/50000000), (1/100000000), (1/100000000), (1305329/20000000)]
    alternative := .zero
    polynomial := [(308957332205517238093746055031/3336019656038100090600000000000), (-101314862876435934929/510346176057700000000), (-83220773976439546158110038969/1668009828019050045300000000000), (-101314862876435934929/510346176057700000000), (-475398880158396330409966132969/3336019656038100090600000000000)]
    bernstein := [(11160050538422951669100188215200023/88043405355232332288000000000000000), (536025065738396835471361114461161699/4270105159728768115968000000000000000), (796200299966990364432913438926719213/6405157739593152173952000000000000000), (131396551591137578568642457798702459/1067526289932192028992000000000000000), (65047649966359238262818211687092711/533763144966096014496000000000000000)]
    reserve := (121866132159/1000000000000) }

theorem quarter_034_008_valid : quarter_034_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_008]
  · intro i; fin_cases i <;> norm_num [quarter_034_008]
  · norm_num [quarter_034_008]
  · norm_num [quarter_034_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_008]

def quarter_034_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(3741369/100000000), (6860181/50000000), (6860181/50000000), (21692179/100000000), (21692179/100000000), (21692179/100000000), (3741369/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (761561/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (48147/1250000), (1/100000000), (3242779/50000000), (1/100000000), (1/100000000), (413583/6250000)]
    alternative := .zero
    polynomial := [(325570089834580315677957293/3443879844736430880000000000), (-203767190075888209/1106265594500000000), (-64603032673632575266989457/1721939922368215440000000000), (-203767190075888209/1106265594500000000), (-454776155181845466211936207/3443879844736430880000000000)]
    bernstein := [(67155965926838024273893514619233/551020775157828940800000000000000), (26609483245976542397932214687771/220408310063131576320000000000000), (31628654966601656282334990665819/264489972075757891584000000000000), (835375477774765836631438462871/7053065922020210442240000000000), (13237347907893518593684301893/112849054752323367075840000000)]
    reserve := (117301362753/1000000000000) }

theorem quarter_034_009_valid : quarter_034_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_009]
  · intro i; fin_cases i <;> norm_num [quarter_034_009]
  · norm_num [quarter_034_009]
  · norm_num [quarter_034_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_009]

def quarter_034_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(4108863/100000000), (1679819/12500000), (1679819/12500000), (1352191/6250000), (1352191/6250000), (1352191/6250000), (4108863/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7609257/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1893673/50000000), (1/100000000), (6435509/100000000), (1/100000000), (1/100000000), (1341583/20000000)]
    alternative := .zero
    polynomial := [(82798257700590608405935441819/860501901840941249000000000000), (-215419429761225556003/1270259752179500000000), (-11179320423312113310309924181/430250950920470624500000000000), (-215419429761225556003/1270259752179500000000), (-105156898547214835026555290181/860501901840941249000000000000)]
    bernstein := [(16539563252867864590530830497011/140984631597619814236160000000000), (102435571932356463306550959546007/881153947485123838976000000000000), (1903148891963454422761969563492653/16521636515346071980800000000000000), (785695342514537304742153129536239/6884015214727529992000000000000000), (9633967480988935391553631551719/85198208103063490000000000000000)]
    reserve := (113077113891/1000000000000) }

theorem quarter_034_010_valid : quarter_034_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_010]
  · intro i; fin_cases i <;> norm_num [quarter_034_010]
  · norm_num [quarter_034_010]
  · norm_num [quarter_034_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_010]

def quarter_034_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(894003/20000000), (13158641/100000000), (13158641/100000000), (674403/3125000), (674403/3125000), (674403/3125000), (894003/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3780941/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (23233/625000), (1/100000000), (6386783/100000000), (1/100000000), (1/100000000), (3398499/50000000)]
    alternative := .zero
    polynomial := [(3029989179650604957508357471/31032819416265357600000000000), (-13026572691500373757/84221149084800000000), (-238501147789567253020858529/15516409708132678800000000000), (-13026572691500373757/84221149084800000000), (-3506991475229739463550074529/31032819416265357600000000000)]
    bernstein := [(35096561803039188303529445332171/310328194162653576000000000000000), (69588817809651847268146040289619/620656388325307152000000000000000), (1655665915404850008346792637609767/14895753319807371648000000000000000), (68384644205709316858719289521281/620656388325307152000000000000000), (8676379930340208330414682904557951/79444017705639315456000000000000000)]
    reserve := (54606880297/500000000000) }

theorem quarter_034_011_valid : quarter_034_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_011]
  · intro i; fin_cases i <;> norm_num [quarter_034_011]
  · norm_num [quarter_034_011]
  · norm_num [quarter_034_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_011]

def quarter_034_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(4824061/100000000), (12883509/100000000), (12883509/100000000), (21528287/100000000), (21528287/100000000), (21528287/100000000), (4824061/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7472891/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3642427/100000000), (1/100000000), (6339459/100000000), (1/100000000), (1/100000000), (6883211/100000000)]
    alternative := .zero
    polynomial := [(15696596832442859524534071692287/158940339648101114523000000000000), (-87382809767971172321/626789839827425000000), (-457429452829938064941847152713/79470169824050557261500000000000), (-87382809767971172321/626789839827425000000), (-16611455738102735654417765997713/158940339648101114523000000000000)]
    bernstein := [(44447110257543627481837504118175570847/406887269499138853178880000000000000000), (22044618714770761291065855606184665749/203443634749569426589440000000000000000), (32799225479578891028095994316950949349/305165452124354139884160000000000000000), (5422016017213238326866158329554220861/50860908687392356647360000000000000000), (2688783222709951436181424895228951887/25430454343696178323680000000000000000)]
    reserve := (52865418493/500000000000) }

theorem quarter_034_012_valid : quarter_034_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_012]
  · intro i; fin_cases i <;> norm_num [quarter_034_012]
  · norm_num [quarter_034_012]
  · norm_num [quarter_034_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_012]

def quarter_034_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(2585289/50000000), (6307967/50000000), (6307967/50000000), (10737829/50000000), (10737829/50000000), (10737829/50000000), (2585289/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (45889/625000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (445461/12500000), (1/100000000), (6293537/100000000), (1/100000000), (1/100000000), (6965261/100000000)]
    alternative := .zero
    polynomial := [(194392677031529728162966684387/1952728533400403537700000000000), (-25603396539201092751/206850142021400000000), (2724299429587549346806894387/976364266700201768850000000000), (-25603396539201092751/206850142021400000000), (-188944078172354629469352895613/1952728533400403537700000000000)]
    bernstein := [(33043283979555216543778914617143987/312436565344064566032000000000000000), (21866211284934617607939825278990429/208291043562709710688000000000000000), (390671972507075984347582147599910561/3749238784128774792384000000000000000), (86168530339199933669661285023020229/833164174250838842752000000000000000), (513132498820952186598344783309082787/4998985045505033056512000000000000000)]
    reserve := (102647336239/1000000000000) }

theorem quarter_034_013_valid : quarter_034_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_013]
  · intro i; fin_cases i <;> norm_num [quarter_034_013]
  · norm_num [quarter_034_013]
  · norm_num [quarter_034_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_013]

def quarter_034_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(550949/10000000), (12358561/100000000), (12358561/100000000), (21421299/100000000), (21421299/100000000), (21421299/100000000), (550949/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3585181/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (139279/4000000), (1/100000000), (3124473/50000000), (1/100000000), (1/100000000), (7041941/100000000)]
    alternative := .zero
    polynomial := [(19149477102208032020931974543/191529120967661934187500000000), (-943338117988182157/8757093754812500000), (976756645236451931642467043/95764560483830967093750000000), (-943338117988182157/8757093754812500000), (-17195963811735128157647040457/191529120967661934187500000000)]
    bernstein := [(50347045735434924335635629918657143/490314549677214551520000000000000000), (1237989319252942324267286694347/12136498754386498800000000000000), (93156389328644243729228989893443/919339780644777284100000000000000), (77113709442748983740737843847/766116483870647736750000000000), (19149477102208032020931974543/191529120967661934187500000000)]
    reserve := (49991032709/500000000000) }

theorem quarter_034_014_valid : quarter_034_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_014]
  · intro i; fin_cases i <;> norm_num [quarter_034_014]
  · norm_num [quarter_034_014]
  · norm_num [quarter_034_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_014]

def quarter_034_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(759721/12500000), (770619/6250000), (770619/6250000), (1316347/6250000), (1316347/6250000), (1316347/6250000), (759721/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3467569/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1736731/50000000), (1/100000000), (1233343/20000000), (1/100000000), (1/100000000), (7095457/100000000)]
    alternative := .zero
    polynomial := [(47474388106440662762477155401/474948831760955218156250000000), (1070152172926634043/3850906290958437500), (2889484117370066587611627901/237474415880477609078125000000), (1070152172926634043/3850906290958437500), (-41695419871700529587253899599/474948831760955218156250000000)]
    bernstein := [(47474388106440662762477155401/474948831760955218156250000000), (24149651769287160634518499263/237474415880477609078125000000), (235799140543515672989452451552701/2279754392452585047150000000000000), (39961164722048062488272433556313/379959065408764174525000000000000), (129996051690058127706107064377943601/1215869009308045358480000000000000000)]
    reserve := (24989211959/250000000000) }

theorem quarter_034_015_valid : quarter_034_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_015]
  · intro i; fin_cases i <;> norm_num [quarter_034_015]
  · norm_num [quarter_034_015]
  · norm_num [quarter_034_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_015]

def quarter_034_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(861759/12500000), (6263531/50000000), (6263531/50000000), (20385911/100000000), (20385911/100000000), (20385911/100000000), (861759/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (825363/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1767969/50000000), (1/100000000), (3022967/50000000), (1/100000000), (1/100000000), (7126631/100000000)]
    alternative := .zero
    polynomial := [(3770822666288292338406990070279/38088364500144576513000000000000), (5569210413764184213/17499531503387500000), (129270695560543957014225730279/19044182250072288256500000000000), (5569210413764184213/17499531503387500000), (-3512281275167204424378538609721/38088364500144576513000000000000)]
    bernstein := [(10429982693973857757682405202557323079/97506213120370115873280000000000000000), (84321389485350650977142052083180633/773858834288651713280000000000000000), (8114486490142553705723835803878101637/73129659840277586904960000000000000000), (152980015731710955214321731331667231/1354252960005140498240000000000000000), (700646668997120038970421053832653479/6094138320023132242080000000000000000)]
    reserve := (53483682527/500000000000) }

theorem quarter_034_016_valid : quarter_034_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_016]
  · intro i; fin_cases i <;> norm_num [quarter_034_016]
  · norm_num [quarter_034_016]
  · norm_num [quarter_034_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_016]

def quarter_034_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(7724049/100000000), (6365461/50000000), (6365461/50000000), (19696687/100000000), (19696687/100000000), (19696687/100000000), (7724049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6183601/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5613/156250), (1/100000000), (1185213/20000000), (1/100000000), (1/100000000), (3575619/50000000)]
    alternative := .zero
    polynomial := [(8197736861760030899481264689/84576586645074528000000000000), (25791339879873125399/71359820256000000000), (-105805959780747416618975311/42288293322537264000000000000), (25791339879873125399/71359820256000000000), (-8409348781321525732719215311/84576586645074528000000000000)]
    bernstein := [(1556702058895612438377644846515889/13532253863211924480000000000000000), (3174948372154315050408562232497067/27064507726423848960000000000000000), (19419805255613566402824368633613803/162387046358543093760000000000000000), (167012543649975134260433976646957/1370354821591080960000000000000000), (26884592099135254907505265348403009/216516061811390791680000000000000000)]
    reserve := (115036421473/1000000000000) }

theorem quarter_034_017_valid : quarter_034_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_017]
  · intro i; fin_cases i <;> norm_num [quarter_034_017]
  · norm_num [quarter_034_017]
  · norm_num [quarter_034_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_017]

def quarter_034_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(8562669/100000000), (1617447/12500000), (1617447/12500000), (18998503/100000000), (18998503/100000000), (18998503/100000000), (8562669/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5676661/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1820781/50000000), (1/100000000), (580821/10000000), (1/100000000), (1/100000000), (1791903/25000000)]
    alternative := .zero
    polynomial := [(6569052980879005208795318083/70186042566355389000000000000), (19706277743388129873/48335747203600000000), (-557723041078743640383430667/35093021283177694500000000000), (19706277743388129873/48335747203600000000), (-7684499063036492489562179417/70186042566355389000000000000)]
    bernstein := [(22324988050587468892493476271837623/179676268969869795840000000000000000), (5696915556196572827980799703891691/44919067242467448960000000000000000), (4359691248599390613473647936864141/33689300431850586720000000000000000), (370583194465941960527332847996099/2807441702654215560000000000000000), (94471996063122170244325408342183/701860425663553890000000000000000)]
    reserve := (62125588923/500000000000) }

theorem quarter_034_018_valid : quarter_034_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_018]
  · intro i; fin_cases i <;> norm_num [quarter_034_018]
  · norm_num [quarter_034_018]
  · norm_num [quarter_034_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_018]

def quarter_034_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(9404539/100000000), (105211/800000), (105211/800000), (9148029/50000000), (9148029/50000000), (9148029/50000000), (9404539/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (158849/3125000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1841363/50000000), (1/100000000), (5693461/100000000), (1/100000000), (1/100000000), (71741/1000000)]
    alternative := .zero
    polynomial := [(66834703990477908363434921977/752113161106014163000000000000), (302049937184520864637/660506114915000000000), (-12616637746187213683046654723/376056580553007081500000000000), (302049937184520864637/660506114915000000000), (-92067979482852335729528231423/752113161106014163000000000000)]
    bernstein := [(1013112970933387696554412169307977/7521131611060141630000000000000000), (827932638631238791771642394872737/6016905288848113304000000000000000), (2029044611673808634305972044949999/14440572693235471929600000000000000), (110465001315855343027556684083761/770163876972558502912000000000000), (18035909672996188360206478428393/123226220315609360465920000000000)]
    reserve := (5388087981/40000000000) }

theorem quarter_034_019_valid : quarter_034_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_019]
  · intro i; fin_cases i <;> norm_num [quarter_034_019]
  · norm_num [quarter_034_019]
  · norm_num [quarter_034_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_019]

def quarter_034_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(320129/3125000), (13364991/100000000), (13364991/100000000), (17593921/100000000), (17593921/100000000), (17593921/100000000), (320129/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2202943/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (743003/20000000), (1/100000000), (5582851/100000000), (1/100000000), (1/100000000), (896423/12500000)]
    alternative := .zero
    polynomial := [(614133670943127547009654580663/7436859745948129838000000000000), (21250346822189239923/41627811141812500000), (-18828294200802588425765232667/338039079361278629000000000000), (21250346822189239923/41627811141812500000), (-1028356143360784492376489699337/7436859745948129838000000000000)]
    bernstein := [(178483250188595351249488379832847/1218455100776141592657920000000000), (2280484048410201971445986197383297/15230688759701769908224000000000000), (87379584259894849294267232314284349/571150828488816371558400000000000000), (6761311024712989113139915725073111/43269002158243664512000000000000000), (189850561313372194590311743050647303/1189897559351700774080000000000000000)]
    reserve := (14648323937/100000000000) }

theorem quarter_034_020_valid : quarter_034_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_020]
  · intro i; fin_cases i <;> norm_num [quarter_034_020]
  · norm_num [quarter_034_020]
  · norm_num [quarter_034_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_020]

def quarter_034_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(11075997/100000000), (13579451/100000000), (13579451/100000000), (1056023/6250000), (1056023/6250000), (1056023/6250000), (11075997/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1824593/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1868899/50000000), (1/100000000), (1369331/25000000), (1/100000000), (1/100000000), (1790081/25000000)]
    alternative := .zero
    polynomial := [(341719652607808166550675261/4581070282906772089000000000), (3796880519981545329/6690961181638000000), (-189103428011842735515298679/2290535141453386044500000000), (3796880519981545329/6690961181638000000), (-719926508631493637581272619/4581070282906772089000000000)]
    bernstein := [(117049300353859930681276918919061/732971245265083534240000000000000), (239402369846132661536291764745109/1465942490530167068480000000000000), (1468375717899303791062868056535263/8795654943181002410880000000000000), (1000328238661867461783154805911349/5863769962120668273920000000000000), (21069138923592649613706826627573/120902473445786974720000000000000)]
    reserve := (6387661241/40000000000) }

theorem quarter_034_021_valid : quarter_034_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_021]
  · intro i; fin_cases i <;> norm_num [quarter_034_021]
  · norm_num [quarter_034_021]
  · norm_num [quarter_034_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_021]

def quarter_034_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(743437/6250000), (13794139/100000000), (13794139/100000000), (8103623/50000000), (8103623/50000000), (8103623/50000000), (743437/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2818893/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (187531/5000000), (1/100000000), (336107/6250000), (1/100000000), (1/100000000), (178397/2500000)]
    alternative := .zero
    polynomial := [(2912493937867073038904747259/44977795458829396000000000000), (5255678530882120691/8363741951750000000), (-2566243201351981814682940741/22488897729414698000000000000), (5255678530882120691/8363741951750000000), (-8044980340571036668270628741/44977795458829396000000000000)]
    bernstein := [(69495212957519730600273499935931/398419226209699840000000000000000), (151076316052649332426410256689461/846640855695612160000000000000000), (246220727907310788748635159778037/1349333863764881880000000000000000), (20974328378814930768952963037969/112444488647073490000000000000000), (1339552471558870038805029582771/7027780540442093125000000000000)]
    reserve := (87213678941/500000000000) }

theorem quarter_034_022_valid : quarter_034_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_022]
  · intro i; fin_cases i <;> norm_num [quarter_034_022]
  · norm_num [quarter_034_022]
  · norm_num [quarter_034_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_022]

def quarter_034_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(1520123/6250000), (6856857/25000000), (266447/5000000), (3099949/50000000), (3099949/50000000), (3099949/50000000), (1520123/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2762311/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3641303/50000000), (1/100000000), (516437/25000000), (1/100000000), (1/100000000), (7615631/100000000)]
    alternative := .zero
    polynomial := [(-439706079954816758501565425597/7160610746027365670500000000000), (398962361842/284476796875), (-3436358555048108131935001845597/3580305373013682835250000000000), (398962361842/284476796875), (-6433011030141399505368438265597/7160610746027365670500000000000)]
    bernstein := [(213109407010218612663299361614107/1118845429066775886015625000000000), (3539320564471215599590371131622951/17901526865068414176250000000000000), (14673071599740927410467488442269367/71606107460273656705000000000000000), (485969962295491310629135203854071587/2291395438728757014560000000000000000), (4018666890861304642301422322008355683/18331163509830056116480000000000000000)]
    reserve := (190472608167/1000000000000) }

theorem quarter_034_023_valid : quarter_034_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_023]
  · intro i; fin_cases i <;> norm_num [quarter_034_023]
  · norm_num [quarter_034_023]
  · norm_num [quarter_034_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_023]

def quarter_034_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(7856841/25000000), (1094089/3125000), (115817/25000000), (139263/25000000), (139263/25000000), (139263/25000000), (7856841/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1727379/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1801583/20000000), (1/100000000), (183071/100000000), (1/100000000), (1/100000000), (8068483/100000000)]
    alternative := .zero
    polynomial := [(-796104361002227212949959839/5940017209687939328125000000), (208311088902099/112598937500000), (-2339051756545012405607750857/1485004302421984832031250000), (208311088902099/112598937500000), (-8560102665177822409481043589/5940017209687939328125000000)]
    bernstein := [(3343465592835221057436312872193771/15206444056801124680000000000000000), (347239141394612786364033806134329/1520644405680112468000000000000000), (108003207988094046461221370752789/456193321704033740400000000000000), (3726645000812012602738204064053/15206444056801124680000000000000), (385202990847586633801117199779/1520644405680112468000000000000)]
    reserve := (109935813407/500000000000) }

theorem quarter_034_024_valid : quarter_034_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_024]
  · intro i; fin_cases i <;> norm_num [quarter_034_024]
  · norm_num [quarter_034_024]
  · norm_num [quarter_034_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_024]

def quarter_034_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(32258247/100000000), (7096701/20000000), 0, 0, 0, 0, (32258247/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7096701/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8834299/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4075507/50000000)]
    alternative := .zero
    polynomial := [(-188654368461226106541261/1241525772917000000000000), (1714593667143441/883429900000000), (-1029685678566743412381261/620762886458500000000000), (1714593667143441/883429900000000), (-1870716988672260718221261/1241525772917000000000000)]
    bernstein := [(2341361041129583321238611559/9217087338135808000000000000), (24209274777363133830134323917/92170873381358080000000000000), (249975639359866501212873677503/921708733813580800000000000000), (2577863416308892700661692162421/9217087338135808000000000000000), (26552587483799837911333831656471/92170873381358080000000000000000)]
    reserve := (254023961717/1000000000000) }

theorem quarter_034_025_valid : quarter_034_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_025]
  · intro i; fin_cases i <;> norm_num [quarter_034_025]
  · norm_num [quarter_034_025]
  · norm_num [quarter_034_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_025]

def quarter_034_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(16194567/50000000), (8805433/25000000), 0, 0, 0, 0, (16194567/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8805433/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4233753/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4092043/50000000)]
    alternative := .zero
    polynomial := [(-1433394236187601364294839/8662349663689500000000000), (35193995217077/17640637500000), (-7290083859756159865364839/4331174831844750000000000), (35193995217077/17640637500000), (-13146773483324718366434839/8662349663689500000000000)]
    bernstein := [(6401809662529245639751570821401/22175615139045120000000000000000), (1648812092541204242537204121073/5543903784761280000000000000000), (1272564427219956124238551128287/4157927838570960000000000000000), (109017556116498441145654403717/346493986547580000000000000000), (27990638148990405756950077841/86623496636895000000000000000)]
    reserve := (144343451633/500000000000) }

theorem quarter_034_026_valid : quarter_034_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_026]
  · intro i; fin_cases i <;> norm_num [quarter_034_026]
  · norm_num [quarter_034_026]
  · norm_num [quarter_034_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_026]

def quarter_034_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(6501307/20000000), (34986931/100000000), 0, 0, 0, 0, (6501307/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (34986931/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4052113/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (8213751/100000000)]
    alternative := .zero
    polynomial := [(-463918790054953419789217/2560234400451000000000000), (332836901865581/162084520000000), (-2191909724643652951449217/1280117200225500000000000), (332836901865581/162084520000000), (-3919900659232352483109217/2560234400451000000000000)]
    bernstein := [(8289506784387318438679642823/25602344004510000000000000000), (34063836173092410896230419833/102409376018040000000000000000), (59935328067458191449002317847/175558930316640000000000000000), (573654867538029009598957998253/1638550016288640000000000000000), (2351188797105673705787324579663/6554200065154560000000000000000)]
    reserve := (323779212673/1000000000000) }

theorem quarter_034_027_valid : quarter_034_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_027]
  · intro i; fin_cases i <;> norm_num [quarter_034_027]
  · norm_num [quarter_034_027]
  · norm_num [quarter_034_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_027]

def quarter_034_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(8152903/25000000), (1391071/4000000), 0, 0, 0, 0, (8152903/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1391071/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1936167/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4120151/50000000)]
    alternative := .zero
    polynomial := [(-63626214572170840919407/319092016048680000000000), (409814727170233/193616700000000), (-278657177233157427711007/159546008024340000000000), (409814727170233/193616700000000), (-493688139894144014502607/319092016048680000000000)]
    bernstein := [(97868427894810665373803917291/272291853694873600000000000000), (50159207900194213027887150449/136145926847436800000000000000), (231186573383320357122887205899/612656670813465600000000000000), (13145257127609617787061002729/34036481711859200000000000000), (20166706838503104561163998193/51054722567788800000000000000)]
    reserve := (14376989479/40000000000) }

theorem quarter_034_028_valid : quarter_034_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_028]
  · intro i; fin_cases i <;> norm_num [quarter_034_028]
  · norm_num [quarter_034_028]
  · norm_num [quarter_034_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_028]

def quarter_034_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 2]
    lambda := ![(204409/625000), (108091/312500), 0, 0, 0, 0, (204409/625000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (108091/312500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1847263/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (8264011/100000000)]
    alternative := .zero
    polynomial := [(-210248425536991627959309/954112609493312500000000), (1261388111327/577269687500), (-852314308000034504259309/477056304746656250000000), (1261388111327/577269687500), (-1494380190463077380559309/954112609493312500000000)]
    bernstein := [(60413626560486385418306746291/152658017518930000000000000000), (24726039430512713190742916879/61063207007572000000000000000), (10113014143376982046097628203/24425282803028800000000000000), (4133589852988557062619650183/9770113121211520000000000000), (1688525050394286905135442339/3908045248484608000000000000)]
    reserve := (98936216293/250000000000) }

theorem quarter_034_029_valid : quarter_034_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_034_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_034_029]
  · intro i; fin_cases i <;> norm_num [quarter_034_029]
  · norm_num [quarter_034_029]
  · norm_num [quarter_034_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_034_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_034_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_034_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_034_029]

def quarterTable034 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 2, 0, 0, 2]
  rows := [quarter_034_000, quarter_034_001, quarter_034_002, quarter_034_003, quarter_034_004, quarter_034_005, quarter_034_006, quarter_034_007, quarter_034_008, quarter_034_009, quarter_034_010, quarter_034_011, quarter_034_012, quarter_034_013, quarter_034_014, quarter_034_015, quarter_034_016, quarter_034_017, quarter_034_018, quarter_034_019, quarter_034_020, quarter_034_021, quarter_034_022, quarter_034_023, quarter_034_024, quarter_034_025, quarter_034_026, quarter_034_027, quarter_034_028, quarter_034_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_034_000_valid
    · exact quarter_034_001_valid
    · exact quarter_034_002_valid
    · exact quarter_034_003_valid
    · exact quarter_034_004_valid
    · exact quarter_034_005_valid
    · exact quarter_034_006_valid
    · exact quarter_034_007_valid
    · exact quarter_034_008_valid
    · exact quarter_034_009_valid
    · exact quarter_034_010_valid
    · exact quarter_034_011_valid
    · exact quarter_034_012_valid
    · exact quarter_034_013_valid
    · exact quarter_034_014_valid
    · exact quarter_034_015_valid
    · exact quarter_034_016_valid
    · exact quarter_034_017_valid
    · exact quarter_034_018_valid
    · exact quarter_034_019_valid
    · exact quarter_034_020_valid
    · exact quarter_034_021_valid
    · exact quarter_034_022_valid
    · exact quarter_034_023_valid
    · exact quarter_034_024_valid
    · exact quarter_034_025_valid
    · exact quarter_034_026_valid
    · exact quarter_034_027_valid
    · exact quarter_034_028_valid
    · exact quarter_034_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
