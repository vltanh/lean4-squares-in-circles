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

def mixed_009_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-44023114674015643/64076356250000000), (-42064340/10252217), (-108099470924015643/32038178125000000), (-42064340/10252217), (-172175827174015643/64076356250000000)]
    bernstein := [(141809012789670638453/262456755200000000000), (343300361474731309041/656141888000000000000), (830020257690478769581/1640354720000000000000), (2004034820269922709033/4100886800000000000000), (4831435808391272355557/10252217000000000000000)]
    reserve := (235628830739/500000000000) }

theorem mixed_009_000_valid : mixed_009_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_000]
  · intro i; fin_cases i <;> norm_num [mixed_009_000]
  · norm_num [mixed_009_000]
  · norm_num [mixed_009_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_000]

def mixed_009_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3208677076379484783/5305390750000000000), (-81371960/21221563), (-8514067826379484783/2652695375000000000), (-81371960/21221563), (-13819458576379484783/5305390750000000000)]
    bernstein := [(398440040343319488262417/848862520000000000000000), (769821467242199697197803/1697725040000000000000000), (45932083125209102361323/105013920000000000000000), (2860481863390760054215843/6790900160000000000000000), (5499790888762519119986337/13581800320000000000000000)]
    reserve := (101234570513/250000000000) }

theorem mixed_009_001_valid : mixed_009_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_001]
  · intro i; fin_cases i <;> norm_num [mixed_009_001]
  · norm_num [mixed_009_001]
  · norm_num [mixed_009_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_001]

def mixed_009_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-363637498625870721/684552687500000000), (-39204036/10952843), (-1048190186125870721/342276343750000000), (-39204036/10952843), (-1732742873625870721/684552687500000000)]
    bernstein := [(706675921377271574660719/1752454880000000000000000), (170164574608636430907889/438113720000000000000000), (122704851143483119262377/328585290000000000000000), (9812135429753460129429/27382107500000000000000), (2348855363451029963799/6845526875000000000000)]
    reserve := (68624531211/200000000000) }

theorem mixed_009_002_valid : mixed_009_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_002]
  · intro i; fin_cases i <;> norm_num [mixed_009_002]
  · norm_num [mixed_009_002]
  · norm_num [mixed_009_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_002]

def mixed_009_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-524938673940135577/1127647700000000000), (-75237955/22552954), (-1652586373940135577/563823850000000000), (-75237955/22552954), (-2780234073940135577/1127647700000000000)]
    bernstein := [(3852164470017249209663/11276477000000000000000), (14785097576622421172331/45105908000000000000000), (56622469239823249617947/180423632000000000000000), (216322409238953548968639/721694528000000000000000), (824229595857074902482743/2886778112000000000000000)]
    reserve := (57103772017/200000000000) }

theorem mixed_009_003_valid : mixed_009_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_003]
  · intro i; fin_cases i <;> norm_num [mixed_009_003]
  · norm_num [mixed_009_003]
  · norm_num [mixed_009_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_003]

def mixed_009_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4491503/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (578989/2500000)]
    alternative := .zero
    polynomial := [(-29462824520192343/72373625000000000), (-8983006/2894945), (-101836449520192343/36186812500000000), (-8983006/2894945), (-174210074520192343/72373625000000000)]
    bernstein := [(52650772859038990616537/185276480000000000000000), (5026655778528075186187/18527648000000000000000), (1435690711572844017523/5558294400000000000000), (45419841219800858899/185276480000000000000), (4295650663664412873/18527648000000000000)]
    reserve := (23185083523/100000000000) }

theorem mixed_009_004_valid : mixed_009_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_004]
  · intro i; fin_cases i <;> norm_num [mixed_009_004]
  · norm_num [mixed_009_004]
  · norm_num [mixed_009_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_004]

def mixed_009_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (68290369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-210764274139286957/593044725000000000), (-9755767/3388827), (-803808999139286957/296522362500000000), (-9755767/3388827), (-1396853724139286957/593044725000000000)]
    bernstein := [(11673077141248689809/50606483200000000000), (110670728890942857513/506064832000000000000), (9408153823437247072057/45545834880000000000000), (29496803250769107672827/151819449600000000000000), (276096400943444349100723/1518194496000000000000000)]
    reserve := (7274335447/40000000000) }

theorem mixed_009_005_valid : mixed_009_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_005]
  · intro i; fin_cases i <;> norm_num [mixed_009_005]
  · norm_num [mixed_009_005]
  · norm_num [mixed_009_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_005]

def mixed_009_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (32261287/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4847213/20000000)]
    alternative := .zero
    polynomial := [(-375609446756191047/1211803250000000000), (-64522574/24236065), (-1587412696756191047/605901625000000000), (-64522574/24236065), (-2799215946756191047/1211803250000000000)]
    bernstein := [(560940833570278830838233/3102216320000000000000000), (65797831610969155648537/387777040000000000000000), (5757794751264887962951/36354097500000000000000), (445098889538428925301/3029508125000000000000), (25617743998203713057/189344257812500000000)]
    reserve := (135297179297/1000000000000) }

theorem mixed_009_006_valid : mixed_009_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_006]
  · intro i; fin_cases i <;> norm_num [mixed_009_006]
  · norm_num [mixed_009_006]
  · norm_num [mixed_009_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_006]

def mixed_009_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(17/100000000), (9/25000000), (9/50000000), 0, 0, 0, (99999929/100000000)]
    cone := fun i => (![![(1562499/3125000), 0, (99999917/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (60567937/100000000), 0, 0]] i.1) i.2
    mu := ![(3/100000000), (3/25000000), (1/20000000), (1/20000000), (1/100000000), (1/100000000), (24698991/100000000)]
    alternative := .zero
    polynomial := [(-333936501160168537819/1234949550000000000000), (-1514197479588821/617474775000000), (-1568885618927826037819/617474775000000000000), (-1514197479588821/617474775000000), (-2803834736695483537819/1234949550000000000000)]
    bernstein := [(8644409648741778202863/64320289062500000000000), (127649246319647395326357/1029124625000000000000000), (4205335606716985772008883/37048486500000000000000000), (13543026292538984665916361/131727952000000000000000000), (290659805330780428719037381/3161470848000000000000000000)]
    reserve := (45969078841/500000000000) }

theorem mixed_009_007_valid : mixed_009_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_007]
  · intro i; fin_cases i <;> norm_num [mixed_009_007]
  · norm_num [mixed_009_007]
  · norm_num [mixed_009_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_007]

def mixed_009_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![0, (1/100000000), (1/50000000), (1/50000000), (1/100000000), 0, (49999997/50000000)]
    cone := fun i => (![![(24999999/50000000), 0, (49999997/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (56435581/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (627687/2500000)]
    alternative := .zero
    polynomial := [(-3709771359457449581/15692175000000000000), (-2821778905800737/1255374000000000), (-19401945574848699581/7846087500000000000), (-2821778905800737/1255374000000000), (-35094119790239949581/15692175000000000000)]
    bernstein := [(4195184681403482766203/46016000000000000000000), (545921555306227041755617/6695328000000000000000000), (2161149925288745703962137/30128976000000000000000000), (310037608622930388333091/5021496000000000000000000), (129480629999264068890739/2510748000000000000000000)]
    reserve := (25785269967/500000000000) }

theorem mixed_009_008_valid : mixed_009_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_008]
  · intro i; fin_cases i <;> norm_num [mixed_009_008]
  · norm_num [mixed_009_008]
  · norm_num [mixed_009_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_008]

def mixed_009_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(1059113/20000000), (1519621/12500000), (1519621/12500000), (2874351/20000000), (2874351/20000000), (7311881/50000000), (27023227/100000000)]
    cone := fun i => (![![(10863831/100000000), 0, (10863831/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (738607/20000000), (1/100000000), (4756423/100000000), (1/100000000), (41447/800000), (691789/10000000)]
    alternative := .zero
    polynomial := [(-17219087635351766858640999967003/828920503499521965962500000000000), (-23360440109574293267/36497156994500000000), (-341991757301446297190582126842003/414460251749760982981250000000000), (-23360440109574293267/36497156994500000000), (-666764426967540827522523253717003/828920503499521965962500000000000)]
    bernstein := [(7748550674614204085606332258934521157/132627280559923514554000000000000000000), (2958549510408682370396286896682535999/53050912223969405821600000000000000000), (482418935008902137005727933907402833/9094442095537612426560000000000000000), (85314255226520182732388772802055643/1697629191167020986291200000000000000), (6436813518545463565235316565946493/135810335293361678903296000000000000)]
    reserve := (4739560877/100000000000) }

theorem mixed_009_009_valid : mixed_009_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_009]
  · intro i; fin_cases i <;> norm_num [mixed_009_009]
  · norm_num [mixed_009_009]
  · norm_num [mixed_009_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_009]

def mixed_009_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(8588137/100000000), (4505359/25000000), (4505359/25000000), (4242629/20000000), (4242629/20000000), (1088641/25000000), (8588137/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8429291/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5505427/100000000), (1/100000000), (1758317/25000000), (1/100000000), (4568227/100000000), (446057/20000000)]
    alternative := .zero
    polynomial := [(520151947542643529972854901008920209/20763598079114611794169580000000000000), (-37908228623561957857/153483390708687500000), (-5004952840745956849063309232884479791/10381799039557305897084790000000000000), (-37908228623561957857/153483390708687500000), (-10530057629034557228099473366777879791/20763598079114611794169580000000000000)]
    bernstein := [(165844092768814596037326611157519947321/3401907909282137996356743987200000000000), (1018708219172483026469994813295769412077/21261924433013362477229649920000000000000), (18748555636939797636714560626909917834583/398661083119000546448055936000000000000000), (7657581023843839457424037784151259509829/166108784632916894353356640000000000000000), (9369597316885740481213326548178734652009/207635980791146117941695800000000000000000)]
    reserve := (45125114063/1000000000000) }

theorem mixed_009_010_valid : mixed_009_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_010]
  · intro i; fin_cases i <;> norm_num [mixed_009_010]
  · norm_num [mixed_009_010]
  · norm_num [mixed_009_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_010]

def mixed_009_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(900339/10000000), (222253/1250000), (222253/1250000), (422633/2000000), (422633/2000000), (26059/625000), (900339/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1696221/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2711449/50000000), (1/100000000), (3489097/50000000), (1/100000000), (452059/10000000), (2360179/100000000)]
    alternative := .zero
    polynomial := [(33036133689462731344457109688366551/1187505472400053815766498000000000000), (-1755540105832123241/7999381236713750000), (-285020938267919802471323378589033449/593752736200026907883249000000000000), (-1755540105832123241/7999381236713750000), (-603078010225302336287103866866433449/1187505472400053815766498000000000000)]
    bernstein := [(535969506926859694141513652477856386751/11875054724000538157664980000000000000000), (2105876293909079105477860396876247325353/47500218896002152630659920000000000000000), (24788092533605264953789220769532022599177/570002626752025831567919040000000000000000), (32372308024758825208217874855034777965277/760003502336034442090558720000000000000000), (9741038593093128369999954809050226009187/233847231488010597566325760000000000000000)]
    reserve := (20827782589/500000000000) }

theorem mixed_009_011_valid : mixed_009_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_011]
  · intro i; fin_cases i <;> norm_num [mixed_009_011]
  · norm_num [mixed_009_011]
  · norm_num [mixed_009_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_011]

def mixed_009_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(942279/10000000), (17549221/100000000), (17549221/100000000), (21059409/100000000), (21059409/100000000), (98429/2500000), (942279/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2140281/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5336847/100000000), (1/100000000), (6926723/100000000), (1/100000000), (4466181/100000000), (155449/6250000)]
    alternative := .zero
    polynomial := [(25698393455303970625815222636704025433/855491247019394161865016300000000000000), (-5262322749940244647/27653584310100000000), (-205044799794804194845774778951088974567/427745623509697080932508150000000000000), (-5262322749940244647/27653584310100000000), (-435787993044912360317364780538881974567/855491247019394161865016300000000000000)]
    bernstein := [(91279797236938284301115686759642435081010473/2190057592369649054374441728000000000000000000), (44813550246489590702791933330297989251122691/1095028796184824527187220864000000000000000000), (65903169107322196332886677748445144644455091/1642543194277236790780831296000000000000000000), (10751356449896690511159577206826751398502299/273757199046206131796805216000000000000000000), (5252888905318870131429531946803489227651833/136878599523103065898402608000000000000000000)]
    reserve := (19188130663/500000000000) }

theorem mixed_009_012_valid : mixed_009_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_012]
  · intro i; fin_cases i <;> norm_num [mixed_009_012]
  · norm_num [mixed_009_012]
  · norm_num [mixed_009_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_012]

def mixed_009_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(4922527/50000000), (4332703/25000000), (4332703/25000000), (20996041/100000000), (20996041/100000000), (1828093/50000000), (4922527/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8669927/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (524773/10000000), (1/100000000), (6879167/100000000), (1/100000000), (4404657/100000000), (2610021/100000000)]
    alternative := .zero
    polynomial := [(43755703105683303579569490159341490931/1383382177655010404975250900000000000000), (-6822318586546563851/42802142194781250000), (-332190383761724266362562027588452509069/691691088827505202487625450000000000000), (-6822318586546563851/42802142194781250000), (-708136470629131836304693545336246509069/1383382177655010404975250900000000000000)]
    bernstein := [(2834287450386499658737582804299328322398577/73780382808267221598680048000000000000000000), (5565000472496845805537350739777092693509377/147560765616534443197360096000000000000000000), (98177283234169588094016040891399771424833993/2656093781097619977552481728000000000000000000), (21345684634671243603893119376636049299801777/590243062466137772789440384000000000000000000), (125071704963427726321651929626754814651830131/3541458374796826636736642304000000000000000000)]
    reserve := (17658220389/500000000000) }

theorem mixed_009_013_valid : mixed_009_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_013]
  · intro i; fin_cases i <;> norm_num [mixed_009_013]
  · norm_num [mixed_009_013]
  · norm_num [mixed_009_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_013]

def mixed_009_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(5134653/50000000), (3425417/20000000), (3425417/20000000), (10470397/50000000), (10470397/50000000), (332563/10000000), (5134653/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4403791/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5155991/100000000), (1/100000000), (6835701/100000000), (1/100000000), (1083931/25000000), (1363761/50000000)]
    alternative := .zero
    polynomial := [(28225490943257596047734300890099130881/868328112952559638153621350000000000000), (-28266752307405137/223223474354000000), (-209665074044147286929016984815379369119/434164056476279819076810675000000000000), (-28266752307405137/223223474354000000), (-447555639031552169905768270520857869119/868328112952559638153621350000000000000)]
    bernstein := [(78627479139746124908032574730003627216310081/2222919969158552673673270656000000000000000000), (48250495099687749917274047358760103009231/1389324980724095421045794160000000000000000), (141870066329532646561847898903240948859681/4167974942172286263137382480000000000000000), (28912717492834714049781412516722099631/868328112952559638153621350000000000000), (28225490943257596047734300890099130881/868328112952559638153621350000000000000)]
    reserve := (4063194909/125000000000) }

theorem mixed_009_014_valid : mixed_009_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_014]
  · intro i; fin_cases i <;> norm_num [mixed_009_014]
  · norm_num [mixed_009_014]
  · norm_num [mixed_009_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_014]

def mixed_009_015 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(5448311/50000000), (4264299/25000000), (4264299/25000000), (5141893/25000000), (5141893/25000000), (1478609/50000000), (5448311/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8805177/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (511441/10000000), (1/100000000), (6751679/100000000), (1/100000000), (840643/20000000), (1444381/50000000)]
    alternative := .zero
    polynomial := [(3407163113727227263051127891022967759/104819166813080221082313425000000000000), (86762147254296317133/184678915755250000000), (-25893796006317617932296397123043532241/52409583406540110541156712500000000000), (86762147254296317133/184678915755250000000), (-55194755126362463127643922137110032241/104819166813080221082313425000000000000)]
    bernstein := [(3407163113727227263051127891022967759/104819166813080221082313425000000000000), (464367295768374973223962805828292923/13102395851635027635289178125000000000), (19283131573114189463022633213579607710959/503132000702785061195104440000000000000000), (862899521603071735578375833745688907223/20963833362616044216462685000000000000000), (11793010575560316230573434412837349053836559/268337067041485365970722368000000000000000000)]
    reserve := (8126288391/250000000000) }

theorem mixed_009_015_valid : mixed_009_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_015]
  · intro i; fin_cases i <;> norm_num [mixed_009_015]
  · norm_num [mixed_009_015]
  · norm_num [mixed_009_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_015]

def mixed_009_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(11736199/100000000), (4281009/25000000), (4281009/25000000), (9942053/50000000), (9942053/50000000), (1255659/50000000), (11736199/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4343197/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1280477/25000000), (1/100000000), (6630673/100000000), (1/100000000), (400143/10000000), (386739/12500000)]
    alternative := .zero
    polynomial := [(339996610450015401603255032187403379/10949173571180280945368475000000000000), (7023233513662704781/13205610520080000000), (-2819960612750505952890308468728846621/5474586785590140472684237500000000000), (7023233513662704781/13205610520080000000), (-5979917835951027307383871969645096621/10949173571180280945368475000000000000)]
    bernstein := [(1234277701260553880388705938462388933456179/28029884342221519220143296000000000000000000), (73505850332889891103470669012764822882831/1557215796790084401119072000000000000000000), (151129223072688452811020166647057012047991/3003201893809448487872496000000000000000000), (20786559460672179801392776475472982630631/389303949197521100279768000000000000000000), (98839385962044797088616571205358436996579/1751867771388844951258956000000000000000000)]
    reserve := (1376073397/31250000000) }

theorem mixed_009_016_valid : mixed_009_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_016]
  · intro i; fin_cases i <;> norm_num [mixed_009_016]
  · norm_num [mixed_009_016]
  · norm_num [mixed_009_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_016]

def mixed_009_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(12589557/100000000), (17211797/100000000), (17211797/100000000), (2402267/12500000), (2402267/12500000), (98051/5000000), (12589557/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4314279/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5125813/100000000), (1/100000000), (407429/6250000), (1/100000000), (3784117/100000000), (329171/10000000)]
    alternative := .zero
    polynomial := [(658149779586822664925378240134520511/23648746919023793885294900000000000000), (101156841617171616699/168726899102300000000), (-6389497006315551495061708852811479489/11824373459511896942647450000000000000), (101156841617171616699/168726899102300000000), (-13437143792217925655048795945757479489/23648746919023793885294900000000000000)]
    bernstein := [(213887562842433704750702474095475080689311/3783799507043807021647184000000000000000000), (26692637017095474719615037185167168653149/445152883181624355487904000000000000000000), (2876476431157551756071979536917215682736597/45405594084525684259766208000000000000000000), (2018812867092167796864778143731146533265797/30270396056350456173177472000000000000000000), (4237271582154135079876074448918839503038191/60540792112700912346354944000000000000000000)]
    reserve := (56527192427/1000000000000) }

theorem mixed_009_017_valid : mixed_009_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_017]
  · intro i; fin_cases i <;> norm_num [mixed_009_017]
  · norm_num [mixed_009_017]
  · norm_num [mixed_009_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_017]

def mixed_009_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(8118627/50000000), (20957841/100000000), (20957841/100000000), (4518871/20000000), (1501513/100000000), (1513943/100000000), (8118627/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(527321/50000000), 0, (10546421/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1549097/25000000), (1/100000000), (3893519/50000000), (1/100000000), (269391/50000000), (4195371/100000000)]
    alternative := .zero
    polynomial := [(554542980250526636286464030997954649/45444685943232403217132820000000000000), (32114639563811622437/39388100787800000000), (-16348651128786411811109144644181045351/22722342971616201608566410000000000000), (32114639563811622437/39388100787800000000), (-33251845237823350258504753319360045351/45444685943232403217132820000000000000)]
    bernstein := [(8100251514649084080968423471371075155657769/116338396014674952235860019200000000000000000), (2155932341123005505769980750406508049437123/29084599003668738058965004800000000000000000), (1713827219168427937615467910741271123733223/21813449252751553544223753600000000000000000), (150790151568833484704066451970198033828247/1817787437729296128685312800000000000000000), (39665783123849391674011908558709980374449/454446859432324032171328200000000000000000)]
    reserve := (17406659779/250000000000) }

theorem mixed_009_018_valid : mixed_009_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_018]
  · intro i; fin_cases i <;> norm_num [mixed_009_018]
  · norm_num [mixed_009_018]
  · norm_num [mixed_009_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_018]

def mixed_009_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(8703119/50000000), (21370137/100000000), (21370137/100000000), (22447251/100000000), 0, 0, (8703119/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1122363/100000000), 0, (22447251/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (112927/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (781589/12500000), (1/100000000), (3915647/50000000), (1/100000000), (1/100000000), (1108871/25000000)]
    alternative := .zero
    polynomial := [(394558088003498554393694036691/169680916498233464650000000000000), (319239127112764303519/346672550407600000000), (-65401550396788378073782743463309/84840458249116732325000000000000), (319239127112764303519/346672550407600000000), (-131197658881580254701959180963309/169680916498233464650000000000000)]
    bernstein := [(148550074099962148280612733859534891/1696809164982334646500000000000000000), (125552842254461170218228513174606571/1357447331985867717200000000000000000), (317253902708610477771369642786710717/3257873596766082521280000000000000000), (17760275693111681392250005230248123/173753258494191067801600000000000000), (2974612651692130434857297479000779/27800521359070570848256000000000000)]
    reserve := (87546718373/1000000000000) }

theorem mixed_009_019_valid : mixed_009_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_019]
  · intro i; fin_cases i <;> norm_num [mixed_009_019]
  · norm_num [mixed_009_019]
  · norm_num [mixed_009_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_019]

def mixed_009_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(18042407/100000000), (21144847/100000000), (21144847/100000000), (21625491/100000000), 0, 0, (18042407/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(43251/4000000), 0, (21625491/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6110551/100000000), (1/100000000), (7642333/100000000), (1/100000000), (1/100000000), (1139739/25000000)]
    alternative := .zero
    polynomial := [(-1712553961723522104256113652687/332653239558378993356250000000000), (602002031799243/611055100000000), (-132070223886693976513412926027687/166326619779189496678125000000000), (602002031799243/611055100000000), (-262427893811664430922569738402687/332653239558378993356250000000000)]
    bernstein := [(5849394869994271560631634651645897/54501906769244814271488000000000000), (76637456316134611054203503925743747/681273834615560178393600000000000000), (3004578608374629710931274421190459299/25547768798083506689760000000000000000), (2611653990110148238636099266506128271/21289807331736255574800000000000000000), (6796196315738532904202394001868865953/53224518329340638937000000000000000000)]
    reserve := (26831147829/250000000000) }

theorem mixed_009_020_valid : mixed_009_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_020]
  · intro i; fin_cases i <;> norm_num [mixed_009_020]
  · norm_num [mixed_009_020]
  · norm_num [mixed_009_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_020]

def mixed_009_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(15876379/50000000), (36494483/100000000), 0, 0, 0, 0, (15876379/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (36494483/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (10295289/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (8023287/100000000)]
    alternative := .zero
    polynomial := [(-138546693056225069308601599/1376700973249050000000000000), (906304063674119/514764450000000), (-1078107124118849753019101599/688350486624525000000000000), (906304063674119/514764450000000), (-2017667555181474436729601599/1376700973249050000000000000)]
    bernstein := [(29387904412550692550382654917681/220272155719848000000000000000000), (62602514186130254297864573673389/440544311439696000000000000000000), (398307743537681013195058275185723/2643265868638176000000000000000000), (93498206122964170115835990609143/587392415252928000000000000000000), (225493304443487534353075495379/1345687091072000000000000000000)]
    reserve := (2668326763/20000000000) }

theorem mixed_009_021_valid : mixed_009_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_021]
  · intro i; fin_cases i <;> norm_num [mixed_009_021]
  · norm_num [mixed_009_021]
  · norm_num [mixed_009_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_021]

def mixed_009_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(15968879/50000000), (9031121/25000000), 0, 0, 0, 0, (15968879/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9031121/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (9920329/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (8070033/100000000)]
    alternative := .zero
    polynomial := [(-400276330651101476783911/3730539720450000000000000), (446850290407909/248008225000000), (-2939365303089903965783911/1865269860225000000000000), (446850290407909/248008225000000), (-5478454275528706454783911/3730539720450000000000000)]
    bernstein := [(1604707514675894874826494424889/9550181684352000000000000000000), (3056761782605539957781492283/17301053776000000000000000000), (20731200007684022545755748727/111916191613500000000000000000), (26182151136336403605927471/135164482625000000000000000), (117794610698521851351519041/582896831320312500000000000)]
    reserve := (33605800763/200000000000) }

theorem mixed_009_022_valid : mixed_009_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_022]
  · intro i; fin_cases i <;> norm_num [mixed_009_022]
  · norm_num [mixed_009_022]
  · norm_num [mixed_009_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_022]

def mixed_009_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(32104747/100000000), (7158101/20000000), 0, 0, 0, 0, (32104747/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7158101/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (298369/3125000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (2028057/25000000)]
    alternative := .zero
    polynomial := [(-1745616842324566660841269/15127733475825000000000000), (1762105028516387/954780800000000), (-12016629607624309489841269/7563866737912500000000000), (1762105028516387/954780800000000), (-22287642372924052318841269/15127733475825000000000000)]
    bernstein := [(1915358061076768615691974031/9454833422390625000000000000), (31954661748407875513380354133/151277334758250000000000000000), (1596020996357948793388312796957/7261312068396000000000000000000), (8840563227343722677570016037367/38726997698112000000000000000000), (9165825750477376673628892806791/38726997698112000000000000000000)]
    reserve := (50644944641/250000000000) }

theorem mixed_009_023_valid : mixed_009_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_023]
  · intro i; fin_cases i <;> norm_num [mixed_009_023]
  · norm_num [mixed_009_023]
  · norm_num [mixed_009_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_023]

def mixed_009_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(16127609/50000000), (8872391/25000000), 0, 0, 0, 0, (16127609/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8872391/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (9177887/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (8150249/100000000)]
    alternative := .zero
    polynomial := [(-12643632144423867826007891/101083870734950000000000000), (434198278868421/229447175000000), (-81122680010977543135007891/50541935367475000000000000), (434198278868421/229447175000000), (-149601727877531218444007891/101083870734950000000000000)]
    bernstein := [(61383484232894811462422057919949/258774709081472000000000000000000), (6363169192406468208569488253701/25877470908147200000000000000000), (1975768447436280970782315749191/7763241272444160000000000000000), (68065819666663450486055329157/258774709081472000000000000000), (7025272304103364713689719501/25877470908147200000000000000)]
    reserve := (23720820497/100000000000) }

theorem mixed_009_024_valid : mixed_009_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_024]
  · intro i; fin_cases i <;> norm_num [mixed_009_024]
  · norm_num [mixed_009_024]
  · norm_num [mixed_009_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_024]

def mixed_009_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(16195269/50000000), (8804731/25000000), 0, 0, 0, 0, (16195269/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8804731/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8810757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (8184441/100000000)]
    alternative := .zero
    polynomial := [(-164105370633925836098864651/1201852013863950000000000000), (142627517914637/73422975000000), (-976671051243507843047864651/600926006931975000000000000), (142627517914637/73422975000000), (-1789236731853089849996864651/1201852013863950000000000000)]
    bernstein := [(83702719473505025687874115861/307674115549171200000000000000), (95996625376283893881202717727/341860128387968000000000000000), (26720375332190525069203480385911/92302234664751360000000000000000), (10190681077302511932215268776951/34186012838796800000000000000000), (943419650965237351511507365217509/3076741155491712000000000000000000)]
    reserve := (54409984619/200000000000) }

theorem mixed_009_025_valid : mixed_009_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_025]
  · intro i; fin_cases i <;> norm_num [mixed_009_025]
  · norm_num [mixed_009_025]
  · norm_num [mixed_009_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_025]

def mixed_009_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(1015999/3125000), (546501/1562500), 0, 0, 0, 0, (1015999/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (546501/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8446633/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (2053781/25000000)]
    alternative := .zero
    polynomial := [(-2032705765179011594017763/13552761226072656250000000), (5269918741067/2639572812500), (-11179197598314518187267763/6776380613036328125000000), (5269918741067/2639572812500), (-20325689431450024780517763/13552761226072656250000000)]
    bernstein := [(819970083910228365218199101409/2668851441442000000000000000000), (2741738788752109546526332886741/8673767184686500000000000000000), (2113468193340688523135426122379/6505325388514875000000000000000), (180848183096085520195671889689/542110449042906250000000000000), (46384148004715675688743457797/135527612260726562500000000000)]
    reserve := (61447413009/200000000000) }

theorem mixed_009_026_valid : mixed_009_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_026]
  · intro i; fin_cases i <;> norm_num [mixed_009_026]
  · norm_num [mixed_009_026]
  · norm_num [mixed_009_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_026]

def mixed_009_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(32620671/100000000), (17379329/50000000), 0, 0, 0, 0, (32620671/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17379329/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4042873/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (8242591/100000000)]
    alternative := .zero
    polynomial := [(-551952464411939462141283353/3332374860394300000000000000), (33227513342613/16171492000000), (-2797284285110305556388283353/1666187430197150000000000000), (33227513342613/16171492000000), (-5042616105808671650635283353/3332374860394300000000000000)]
    bernstein := [(11426667336780552599022048483007/33323748603943000000000000000000), (46905262296022011622475868775597/133294994415772000000000000000000), (27482785703734660312153567497341/76168568237584000000000000000000), (788410108160444736278909853110377/2132719910652352000000000000000000), (3228645004607131752027887651172567/8530879642609408000000000000000000)]
    reserve := (342898617817/1000000000000) }

theorem mixed_009_027_valid : mixed_009_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_027]
  · intro i; fin_cases i <;> norm_num [mixed_009_027]
  · norm_num [mixed_009_027]
  · norm_num [mixed_009_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_027]

def mixed_009_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(32717723/100000000), (34564553/100000000), 0, 0, 0, 0, (32717723/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (34564553/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3864167/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4133557/50000000)]
    alternative := .zero
    polynomial := [(-293501666111533314942737937/1597275455201900000000000000), (1636580452799783/772833400000000), (-1368184946360732030186737937/798637727600950000000000000), (1636580452799783/772833400000000), (-2442868226609930745430737937/1597275455201900000000000000)]
    bernstein := [(25416360857781776744008653093963/67033199431424000000000000000000), (793920495278881399870471221697277/2044512582658432000000000000000000), (1218765646679067349019227517334709/3066768873987648000000000000000000), (207742461821707139712751329161717/511128145664608000000000000000000), (106162319493764117893919931162863/255564072832304000000000000000000)]
    reserve := (94790197519/250000000000) }

theorem mixed_009_028_valid : mixed_009_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_028]
  · intro i; fin_cases i <;> norm_num [mixed_009_028]
  · norm_num [mixed_009_028]
  · norm_num [mixed_009_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_028]

def mixed_009_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 2]
    lambda := ![(16402061/50000000), (34391757/100000000), 0, 0, 0, 0, (16402061/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (34391757/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3687321/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4144473/50000000)]
    alternative := .zero
    polynomial := [(-52121080037480187748054171/254700038780550000000000000), (268671450695167/122910700000000), (-223269009909411641282554171/127350019390275000000000000), (268671450695167/122910700000000), (-394416939781343094817054171/254700038780550000000000000)]
    bernstein := [(16958841381233794443756592072229/40752006204888000000000000000000), (6935991585166493182834495077001/16300802481955200000000000000000), (8504921172250660615761941044871/19560962978346240000000000000000), (1158058539102148146748570738577/2608128397112832000000000000000), (472785762819159104650402322741/1043251358845132800000000000000)]
    reserve := (208073699439/500000000000) }

theorem mixed_009_029_valid : mixed_009_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_009_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_009_029]
  · intro i; fin_cases i <;> norm_num [mixed_009_029]
  · norm_num [mixed_009_029]
  · norm_num [mixed_009_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_009_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_009_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_009_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_009_029]

def mixedTable009 : OwnerTable where
  mode := .mixed
  owners := ![0, 2, 0, 2, 0, 2, 2]
  rows := [mixed_009_000, mixed_009_001, mixed_009_002, mixed_009_003, mixed_009_004, mixed_009_005, mixed_009_006, mixed_009_007, mixed_009_008, mixed_009_009, mixed_009_010, mixed_009_011, mixed_009_012, mixed_009_013, mixed_009_014, mixed_009_015, mixed_009_016, mixed_009_017, mixed_009_018, mixed_009_019, mixed_009_020, mixed_009_021, mixed_009_022, mixed_009_023, mixed_009_024, mixed_009_025, mixed_009_026, mixed_009_027, mixed_009_028, mixed_009_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_009_000_valid
    · exact mixed_009_001_valid
    · exact mixed_009_002_valid
    · exact mixed_009_003_valid
    · exact mixed_009_004_valid
    · exact mixed_009_005_valid
    · exact mixed_009_006_valid
    · exact mixed_009_007_valid
    · exact mixed_009_008_valid
    · exact mixed_009_009_valid
    · exact mixed_009_010_valid
    · exact mixed_009_011_valid
    · exact mixed_009_012_valid
    · exact mixed_009_013_valid
    · exact mixed_009_014_valid
    · exact mixed_009_015_valid
    · exact mixed_009_016_valid
    · exact mixed_009_017_valid
    · exact mixed_009_018_valid
    · exact mixed_009_019_valid
    · exact mixed_009_020_valid
    · exact mixed_009_021_valid
    · exact mixed_009_022_valid
    · exact mixed_009_023_valid
    · exact mixed_009_024_valid
    · exact mixed_009_025_valid
    · exact mixed_009_026_valid
    · exact mixed_009_027_valid
    · exact mixed_009_028_valid
    · exact mixed_009_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
