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

def mixed_013_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-44023114674015643/64076356250000000), (-42064340/10252217), (-108099470924015643/32038178125000000), (-42064340/10252217), (-172175827174015643/64076356250000000)]
    bernstein := [(141809012789670638453/262456755200000000000), (343300361474731309041/656141888000000000000), (830020257690478769581/1640354720000000000000), (2004034820269922709033/4100886800000000000000), (4831435808391272355557/10252217000000000000000)]
    reserve := (235628830739/500000000000) }

theorem mixed_013_000_valid : mixed_013_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_000]
  · intro i; fin_cases i <;> norm_num [mixed_013_000]
  · norm_num [mixed_013_000]
  · norm_num [mixed_013_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_000]

def mixed_013_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3208677076379484783/5305390750000000000), (-81371960/21221563), (-8514067826379484783/2652695375000000000), (-81371960/21221563), (-13819458576379484783/5305390750000000000)]
    bernstein := [(398440040343319488262417/848862520000000000000000), (769821467242199697197803/1697725040000000000000000), (45932083125209102361323/105013920000000000000000), (2860481863390760054215843/6790900160000000000000000), (5499790888762519119986337/13581800320000000000000000)]
    reserve := (101234570513/250000000000) }

theorem mixed_013_001_valid : mixed_013_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_001]
  · intro i; fin_cases i <;> norm_num [mixed_013_001]
  · norm_num [mixed_013_001]
  · norm_num [mixed_013_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_001]

def mixed_013_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-363637498625870721/684552687500000000), (-39204036/10952843), (-1048190186125870721/342276343750000000), (-39204036/10952843), (-1732742873625870721/684552687500000000)]
    bernstein := [(706675921377271574660719/1752454880000000000000000), (170164574608636430907889/438113720000000000000000), (122704851143483119262377/328585290000000000000000), (9812135429753460129429/27382107500000000000000), (2348855363451029963799/6845526875000000000000)]
    reserve := (68624531211/200000000000) }

theorem mixed_013_002_valid : mixed_013_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_002]
  · intro i; fin_cases i <;> norm_num [mixed_013_002]
  · norm_num [mixed_013_002]
  · norm_num [mixed_013_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_002]

def mixed_013_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-524938673940135577/1127647700000000000), (-75237955/22552954), (-1652586373940135577/563823850000000000), (-75237955/22552954), (-2780234073940135577/1127647700000000000)]
    bernstein := [(3852164470017249209663/11276477000000000000000), (14785097576622421172331/45105908000000000000000), (56622469239823249617947/180423632000000000000000), (216322409238953548968639/721694528000000000000000), (824229595857074902482743/2886778112000000000000000)]
    reserve := (57103772017/200000000000) }

theorem mixed_013_003_valid : mixed_013_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_003]
  · intro i; fin_cases i <;> norm_num [mixed_013_003]
  · norm_num [mixed_013_003]
  · norm_num [mixed_013_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_003]

def mixed_013_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4491503/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (578989/2500000)]
    alternative := .zero
    polynomial := [(-29462824520192343/72373625000000000), (-8983006/2894945), (-101836449520192343/36186812500000000), (-8983006/2894945), (-174210074520192343/72373625000000000)]
    bernstein := [(52650772859038990616537/185276480000000000000000), (5026655778528075186187/18527648000000000000000), (1435690711572844017523/5558294400000000000000), (45419841219800858899/185276480000000000000), (4295650663664412873/18527648000000000000)]
    reserve := (23185083523/100000000000) }

theorem mixed_013_004_valid : mixed_013_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_004]
  · intro i; fin_cases i <;> norm_num [mixed_013_004]
  · norm_num [mixed_013_004]
  · norm_num [mixed_013_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_004]

def mixed_013_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (68290369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-210764274139286957/593044725000000000), (-9755767/3388827), (-803808999139286957/296522362500000000), (-9755767/3388827), (-1396853724139286957/593044725000000000)]
    bernstein := [(11673077141248689809/50606483200000000000), (110670728890942857513/506064832000000000000), (9408153823437247072057/45545834880000000000000), (29496803250769107672827/151819449600000000000000), (276096400943444349100723/1518194496000000000000000)]
    reserve := (7274335447/40000000000) }

theorem mixed_013_005_valid : mixed_013_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_005]
  · intro i; fin_cases i <;> norm_num [mixed_013_005]
  · norm_num [mixed_013_005]
  · norm_num [mixed_013_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_005]

def mixed_013_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (32261287/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4847213/20000000)]
    alternative := .zero
    polynomial := [(-375609446756191047/1211803250000000000), (-64522574/24236065), (-1587412696756191047/605901625000000000), (-64522574/24236065), (-2799215946756191047/1211803250000000000)]
    bernstein := [(560940833570278830838233/3102216320000000000000000), (65797831610969155648537/387777040000000000000000), (5757794751264887962951/36354097500000000000000), (445098889538428925301/3029508125000000000000), (25617743998203713057/189344257812500000000)]
    reserve := (135297179297/1000000000000) }

theorem mixed_013_006_valid : mixed_013_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_006]
  · intro i; fin_cases i <;> norm_num [mixed_013_006]
  · norm_num [mixed_013_006]
  · norm_num [mixed_013_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_006]

def mixed_013_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (60567983/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (192961/781250)]
    alternative := .zero
    polynomial := [(-1669681908421438993/6174752000000000000), (-60567983/24699008), (-7844433908421438993/3087376000000000000), (-60567983/24699008), (-14019185908421438993/6174752000000000000)]
    bernstein := [(129666843351776810183/964805000000000000000), (1914749584812907669837/15436880000000000000000), (7008935084213645482667/61747520000000000000000), (203146714392013249812401/1975920640000000000000000), (1453309289924514668795407/15807365120000000000000000)]
    reserve := (91938743673/1000000000000) }

theorem mixed_013_007_valid : mixed_013_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_007]
  · intro i; fin_cases i <;> norm_num [mixed_013_007]
  · norm_num [mixed_013_007]
  · norm_num [mixed_013_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_007]

def mixed_013_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (440903/781250), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (12553741/50000000)]
    alternative := .zero
    polynomial := [(-46372160077035607/196152203125000000), (-28217792/12553741), (-242524363202035607/98076101562500000), (-28217792/12553741), (-438676566327035607/196152203125000000)]
    bernstein := [(45779920776958450409993/502149640000000000000000), (20472042148535711210797/251074820000000000000000), (27014349568794963023539/376612230000000000000000), (3875465983361040561077/62768705000000000000000), (1618505790747156625433/31384352500000000000000)]
    reserve := (6446308677/125000000000) }

theorem mixed_013_008_valid : mixed_013_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_008]
  · intro i; fin_cases i <;> norm_num [mixed_013_008]
  · norm_num [mixed_013_008]
  · norm_num [mixed_013_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_008]

def mixed_013_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26068003/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (6364661/25000000)]
    alternative := .zero
    polynomial := [(-13219915452392959/63646610000000000), (-26068003/12729322), (-76866525452392959/31823305000000000), (-26068003/12729322), (-140513135452392959/63646610000000000)]
    bernstein := [(518536948488253425521/10183457600000000000000), (170966330030318602347/4073383040000000000000), (53503020752958709881/1629353216000000000000), (3064861981379319879/130348257280000000000), (145944228545589929/10427860582400000000)]
    reserve := (13995606039/1000000000000) }

theorem mixed_013_009_valid : mixed_013_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_009]
  · intro i; fin_cases i <;> norm_num [mixed_013_009]
  · norm_num [mixed_013_009]
  · norm_num [mixed_013_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_009]

def mixed_013_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(7484743/100000000), (9824619/100000000), (421513/4000000), (7066841/50000000), (7066841/50000000), (14716129/100000000), (729233/2500000)]
    cone := fun i => (![![(677643/6250000), 0, (677643/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (390103/12500000), (331381/50000000), (1113669/25000000), (1/100000000), (5155697/100000000), (1513897/20000000)]
    alternative := .zero
    polynomial := [(-590854328546139812511479650601970745605241/16052722548077853733866271092900000000000000), (-57799408826471/75694850000000), (-1047724176299330172575641825037364509962073/472138898472878050996066796850000000000000), (-57799408826471/75694850000000), (-35031767665631086055060342400668422593105241/16052722548077853733866271092900000000000000)]
    bernstein := [(649084263838825955830597534779223194697171/26040376854228470849075741147136000000000000), (4769830184388480418366146531544577987831867/202938122089280521277519279001600000000000000), (6737217912361818458278132318661871507010120433/308212272923094791690232404983680000000000000000), (31697685746445598588088504753635461724370659/1585454078822504072480619367200000000000000000), (28458889310735658695694315190388047786370659/1589378470106718191471908029000000000000000000)]
    reserve := (17905671837/1000000000000) }

theorem mixed_013_010_valid : mixed_013_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_010]
  · intro i; fin_cases i <;> norm_num [mixed_013_010]
  · norm_num [mixed_013_010]
  · norm_num [mixed_013_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_010]

def mixed_013_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(11255147/100000000), (1891419/12500000), (15999039/100000000), (5125117/25000000), (5125117/25000000), (2679189/50000000), (11255147/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1514209/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (14891/312500), (406267/50000000), (6570839/100000000), (1/100000000), (924049/20000000), (2961847/100000000)]
    alternative := .zero
    polynomial := [(-798883518592108155880966446667022725529/6216927604261725143145919442800000000000000), (-74971415562927/148092350000000), (-9961907469400817517627356674712301226725529/3108463802130862571572959721400000000000000), (-74971415562927/148092350000000), (-19923016055283042927098832382977935430725529/6216927604261725143145919442800000000000000)]
    bernstein := [(11470150274192600475438941873751049256721571/615537386560566845856031628000000000000000000), (47917062531928741491588374664739534837611813/2462149546242267383424126512000000000000000000), (59534920835025613671465386625115475251260129017/2984125250045628068710041332544000000000000000000), (79992870310077834737250993762389047521437407117/3978833666727504091613388443392000000000000000000), (45302842651485156768536594800849265363820250993/2273619238130002338064793396224000000000000000000)]
    reserve := (9317184077/500000000000) }

theorem mixed_013_011_valid : mixed_013_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_011]
  · intro i; fin_cases i <;> norm_num [mixed_013_011]
  · norm_num [mixed_013_011]
  · norm_num [mixed_013_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_011]

def mixed_013_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(2198713/20000000), (7819189/50000000), (4078931/25000000), (20680313/100000000), (20680313/100000000), (2349071/50000000), (2198713/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (3995543/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1207551/25000000), (313761/50000000), (6655987/100000000), (1/100000000), (4534413/100000000), (1454979/50000000)]
    alternative := .zero
    polynomial := [(41281108060926740613912480624419652437143/4740100937038797839294491878900000000000000), (-71331687896239/145497900000000), (-10116488473782653975756428392430246114562857/2370050468519398919647245939450000000000000), (-71331687896239/145497900000000), (-6758086018542078230708923088494970627187619/1580033645679599279764830626300000000000000)]
    bernstein := [(261376960103276354201327475540818484450189206983/12134658398819322468593899209984000000000000000000), (2546784330516268754821218861648143012213617/113338112928654497866679424000000000000000000), (208899424507565858006603033846001730595032079261/9100993799114491851445424407488000000000000000000), (34873776091544732328245429702806325126810357429/1516832299852415308574237401248000000000000000000), (17129015564486994501860271998536556807391031543/758416149926207654287118700624000000000000000000)]
    reserve := (5384926207/250000000000) }

theorem mixed_013_012_valid : mixed_013_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_012]
  · intro i; fin_cases i <;> norm_num [mixed_013_012]
  · norm_num [mixed_013_012]
  · norm_num [mixed_013_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_012]

def mixed_013_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(10764871/100000000), (8086723/50000000), (1661541/10000000), (10405231/50000000), (10405231/50000000), (4060477/100000000), (10764871/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (523437/6250000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4909169/100000000), (107127/25000000), (3364411/50000000), (1/100000000), (2221867/50000000), (1429383/50000000)]
    alternative := .zero
    polynomial := [(1599863710264796848549184695813303517673479/93655091248018302736294864514550000000000000), (-136182706158739/285876600000000), (-302149621567123492936709194572298605986576521/46827545624009151368147432257275000000000000), (-136182706158739/285876600000000), (-605899106844511782721967573840410515490826521/93655091248018302736294864514550000000000000)]
    bernstein := [(371459826866281596687898630586946322130519596679/14984814599682928437807178322328000000000000000000), (258162483464118881359196539057790168839508126093/9989876399788618958538118881552000000000000000000), (4714992367398875955631193324830122719717226791237/179817775196195141253686139867936000000000000000000), (1036065590762558804790310137152877161757143297693/39959505599154475834152475526208000000000000000000), (5985270522698466221611664385610944768422600546279/239757033594926855004914853157248000000000000000000)]
    reserve := (4957816787/200000000000) }

theorem mixed_013_013_valid : mixed_013_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_013]
  · intro i; fin_cases i <;> norm_num [mixed_013_013]
  · norm_num [mixed_013_013]
  · norm_num [mixed_013_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_013]

def mixed_013_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(2113667/20000000), (8368899/50000000), (8448661/50000000), (10446239/50000000), (10446239/50000000), (688651/20000000), (2113667/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8724611/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5001811/100000000), (54049/25000000), (6789597/100000000), (1/100000000), (1087027/25000000), (2808567/100000000)]
    alternative := .zero
    polynomial := [(2332268808107257162642176561313594955571139/93396974397089903386512628842450000000000000), (-130407926561357/280856700000000), (-618439973014141066513806784527769939511678861/46698487198544951693256314421225000000000000), (-130407926561357/280856700000000), (-1239212214836389390190255745616853473978928861/93396974397089903386512628842450000000000000)]
    bernstein := [(6767536564862199018716522685304311153918344555939/239096254456550152669472329836672000000000000000000), (2207224538477865058784042321995226173937288957/74717579517671922709210103073960000000000000000), (13178426141598109133581747506694402206599788339/448305477106031536255260618443760000000000000000), (48209406623316135379587194802329143388991/1729573599946109321972456089675000000000000), (2332268808107257162642176561313594955571139/93396974397089903386512628842450000000000000)]
    reserve := (12485783523/500000000000) }

theorem mixed_013_014_valid : mixed_013_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_014]
  · intro i; fin_cases i <;> norm_num [mixed_013_014]
  · norm_num [mixed_013_014]
  · norm_num [mixed_013_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_014]

def mixed_013_015 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(2115371/20000000), (861341/5000000), (17221437/100000000), (20763877/100000000), (20763877/100000000), (71757/2500000), (2115371/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(430603/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4473399/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1021569/20000000), (54407/50000000), (213011/3125000), (1/100000000), (1055689/25000000), (1401989/50000000)]
    alternative := .zero
    polynomial := [(25024910904754376954330926946517780209327/876143257712024721722791393650000000000000), (59876259853599789/76278015523000000), (-12011232637160604022930276359984821084790673/438071628856012360861395696825000000000000), (59876259853599789/76278015523000000), (-586524150859169815190606918217467315848553/21369347749073773700555887650000000000000)]
    bernstein := [(25024910904754376954330926946517780209327/876143257712024721722791393650000000000000), (29323346453979434856817710297069604896827/876143257712024721722791393650000000000000), (149373320978220961221731293148598040919978927/4205487637017718664269398689520000000000000000), (48665413882275902093838253620442937574820027/1401829212339239554756466229840000000000000000), (69647269998651679459328050670581390182597175727/2242926739742783287610345967744000000000000000000)]
    reserve := (228500631/8000000000) }

theorem mixed_013_015_valid : mixed_013_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_015]
  · intro i; fin_cases i <;> norm_num [mixed_013_015]
  · norm_num [mixed_013_015]
  · norm_num [mixed_013_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_015]

def mixed_013_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(10803213/100000000), (881489/5000000), (8790133/50000000), (4086983/20000000), (4086983/20000000), (1156849/50000000), (10803213/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1320377/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9060609/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (163267/3125000), (22251/20000000), (3405681/50000000), (1/100000000), (812907/20000000), (2848111/100000000)]
    alternative := .zero
    polynomial := [(15667121149005945185777884535793909/8846596028825345204067640000000000000), (439773106158384167/198041618315625000), (-372495293415941812594952102397333818273/13269894043238017806101460000000000000), (439773106158384167/198041618315625000), (-745037588195330643025461538448275018273/26539788086476035612202920000000000000)]
    bernstein := [(900586436903032997531405603299229266542709/22647285833792883722413158400000000000000000), (217838710213325160983971612282752722812361/4852989821527046511945676800000000000000000), (2399620553488108320083308220376913547765581/50956393126033988375429606400000000000000000), (393857500397345639860186806496838415694127/8492732187672331395904934400000000000000000), (181433688028694287920292503830096082683327/4246366093836165697952467200000000000000000)]
    reserve := (39765755751/1000000000000) }

theorem mixed_013_016_valid : mixed_013_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_016]
  · intro i; fin_cases i <;> norm_num [mixed_013_016]
  · norm_num [mixed_013_016]
  · norm_num [mixed_013_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_016]

def mixed_013_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(2770123/25000000), (18049753/100000000), (2238661/12500000), (20073123/100000000), (20073123/100000000), (1733729/100000000), (2770123/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(28093/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9169697/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2675817/50000000), (113657/100000000), (6797387/100000000), (1/100000000), (3896269/100000000), (724431/25000000)]
    alternative := .zero
    polynomial := [(-534183040887980379861530847999905355227939/8456515759646203563865941729300000000000000), (30665884663440825029/8233665416700000000), (-121729451686071383126175474931764352779227939/4228257879823101781932970864650000000000000), (30665884663440825029/8233665416700000000), (-242924720331254785872489419015528800203227939/8456515759646203563865941729300000000000000)]
    bernstein := [(69501184029633695564316354071008150907764180861/1353042521543392570218550676688000000000000000000), (153531860623536425863160718353483478015498958183/2706085043086785140437101353376000000000000000000), (959892440687822786068926162632951922040246468447/16236510258520710842622608120256000000000000000000), (633326580809348828190395623085318507066370657647/10824340172347140561748405413504000000000000000000), (1188230791730903580777964516375258033380530053741/21648680344694281123496810827008000000000000000000)]
    reserve := (80260301/1562500000) }

theorem mixed_013_017_valid : mixed_013_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_017]
  · intro i; fin_cases i <;> norm_num [mixed_013_017]
  · norm_num [mixed_013_017]
  · norm_num [mixed_013_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_017]

def mixed_013_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(2798889/20000000), (22710107/100000000), (22365001/100000000), (605743/2500000), (54029/4000000), (338889/25000000), (2798889/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(493009/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22879/2000000), 0, (4575799/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3370209/50000000), (71257/50000000), (520739/6250000), (1/100000000), (483537/100000000), (904887/25000000)]
    alternative := .zero
    polynomial := [(-4251616422793367887103011191046884931/18975512602722898138876092500000000000), (4665807604673617861/716439255100000000), (-345045222890287668828837064193754053681/9487756301361449069438046250000000000), (4665807604673617861/716439255100000000), (-685838829357781969770571117196461222431/18975512602722898138876092500000000000)]
    bernstein := [(2983436252039217122805116721427308060610289/48577312262970619235522796800000000000000000), (829828675535709579592403076282037361796463/12144328065742654808880699200000000000000000), (651077092616117391749054297851633118368063/9108246049306991106660524400000000000000000), (53779748288007593511619403881707180953507/759020504108915925555043700000000000000000), (12602677014519397545735905431378405481369/189755126027228981388760925000000000000000)]
    reserve := (12283249579/200000000000) }

theorem mixed_013_018_valid : mixed_013_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_018]
  · intro i; fin_cases i <;> norm_num [mixed_013_018]
  · norm_num [mixed_013_018]
  · norm_num [mixed_013_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_018]

def mixed_013_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(290819/2000000), (2947379/12500000), (22989647/100000000), (24349421/100000000), 0, 0, (290819/2000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(81859/1562500), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1217471/100000000), 0, (24349421/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (471689/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6999783/100000000), (147281/100000000), (4230821/50000000), (1/100000000), (1/100000000), (3705347/100000000)]
    alternative := .zero
    polynomial := [(-47886855713628740957042739069367659289/115440128580835453701267150000000000000), (236291031679466786127/27286360575350000000), (-2189083042638440676020030080519570659289/57720064290417726850633575000000000000), (236291031679466786127/27286360575350000000), (-4330279229563252611083017421969773659289/115440128580835453701267150000000000000)]
    bernstein := [(88655363871630636127278298149879731592911/1154401285808354537012671500000000000000000), (25919929634988614235546671934454050618897/307840342882227876536712400000000000000000), (194352526873054466313164568751517622577457/2216450468752040711064329280000000000000000), (3437341623380614750233103073154457689561/39403563888925168196699187200000000000000), (1566121828541705089265045124987648380159/18913710666684080734415609856000000000000)]
    reserve := (76797700211/1000000000000) }

theorem mixed_013_019_valid : mixed_013_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_019]
  · intro i; fin_cases i <;> norm_num [mixed_013_019]
  · norm_num [mixed_013_019]
  · norm_num [mixed_013_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_019]

def mixed_013_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(14756791/100000000), (23814347/100000000), (1433161/6250000), (11870747/50000000), 0, 0, (14756791/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(6427427/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(47483/4000000), 0, (11870747/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7079037/100000000), (147883/100000000), (8340239/100000000), (1/100000000), (1/100000000), (1864373/50000000)]
    alternative := .zero
    polynomial := [(-1106086325565165573253762758892185739/1709884545316971263064037500000000000), (6297181357683/591532000000), (-32928235858756638751077470382555810739/854942272658485631532018750000000000), (6297181357683/591532000000), (-64750385391948111928901178006219435739/1709884545316971263064037500000000000)]
    bernstein := [(26211463212302270527952289034164760109/280147483904732571740411904000000000000), (20843713109327377678755191191645940827/205990796988773949809126400000000000000), (1966900605239852686877753957581884118529/18759876154334770429045440000000000000000), (11436402506658271329307605205059994463087/109432610900286160836098400000000000000000), (27391269059046364290210570384252232644341/273581527250715402090246000000000000000000)]
    reserve := (11695385787/125000000000) }

theorem mixed_013_020_valid : mixed_013_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_020]
  · intro i; fin_cases i <;> norm_num [mixed_013_020]
  · norm_num [mixed_013_020]
  · norm_num [mixed_013_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_020]

def mixed_013_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(1102797/4000000), (44860149/100000000), 0, 0, 0, 0, (1102797/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7102231/50000000), 0, (10637981/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3326207/25000000), (138309/50000000), (1/100000000), (1/100000000), (1/100000000), (6966369/100000000)]
    alternative := .zero
    polynomial := [(-2609386121757510761319973028899/1424372798105137932000000000000), (108744492802023/4610300000000), (-52148647688415900651210256148899/712186399052568966000000000000), (108744492802023/4610300000000), (-101687909255074290541100539268899/1424372798105137932000000000000)]
    bernstein := [(23264003236553184602383424128106381/227899647696822069120000000000000000), (52933858344054358472678774013473689/455799295393644138240000000000000000), (335456967418027262179414154575387823/2734795772361864829440000000000000000), (221682582358355062291958433116735729/1823197181574576552960000000000000000), (411362646838255844097399110172970301/3646394363149153105920000000000000000)]
    reserve := (102080031591/1000000000000) }

theorem mixed_013_021_valid : mixed_013_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_021]
  · intro i; fin_cases i <;> norm_num [mixed_013_021]
  · norm_num [mixed_013_021]
  · norm_num [mixed_013_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_021]

def mixed_013_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(13594453/50000000), (11405547/25000000), 0, 0, 0, 0, (13594453/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(16527283/100000000), 0, (21261661/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (209683/1562500), (279019/100000000), (1/100000000), (1/100000000), (1/100000000), (6870093/100000000)]
    alternative := .zero
    polynomial := [(-7651221553879746943369344892807/3091834673286929700000000000000), (24036976715051/871934375000), (-1507724642877612046204014641606491/20096925376365043050000000000000), (24036976715051/871934375000), (-2915983405554787382144227799606491/40193850752730086100000000000000)]
    bernstein := [(13559334670330526689547812550390066309/102896257926989020416000000000000000000), (626254373946502251005948852453847529/4287344080291209184000000000000000000), (184089819859350427604438955986059787/1205815522581902583000000000000000000), (5073789763005888070755989967977573/33494875627275071750000000000000000), (68786198941542726016085075115617/483099167701082765625000000000000)]
    reserve := (5271070083/40000000000) }

theorem mixed_013_022_valid : mixed_013_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_022]
  · intro i; fin_cases i <;> norm_num [mixed_013_022]
  · norm_num [mixed_013_022]
  · norm_num [mixed_013_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_022]

def mixed_013_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(13404303/50000000), (46382789/100000000), 0, 0, 0, 0, (13404303/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18860993/100000000), 0, (10593707/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (13536821/100000000), (56207/20000000), (1/100000000), (1/100000000), (1/100000000), (6773999/100000000)]
    alternative := .zero
    polynomial := [(-104053501251717890669375813600473/32213078991430500331250000000000), (889893771823897/28103500000000), (-1239125683840733677140478578900473/16106539495715250165625000000000), (889893771823897/28103500000000), (-2374197866429749463611581344200473/32213078991430500331250000000000)]
    bernstein := [(809769710618642633356818593838813/5033293592411015676757812500000000), (14130549124882944104127299153721109/80532697478576250828125000000000000), (352089507784070616557950088212093043/1932784739485830019875000000000000000), (932305229454465157284824288121159129/5154092638628880053000000000000000000), (14141708771241960623517221768300715047/82465482218062080848000000000000000000)]
    reserve := (160882669717/1000000000000) }

theorem mixed_013_023_valid : mixed_013_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_023]
  · intro i; fin_cases i <;> norm_num [mixed_013_023]
  · norm_num [mixed_013_023]
  · norm_num [mixed_013_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_023]

def mixed_013_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(6607579/25000000), (47139369/100000000), 0, 0, 0, 0, (6607579/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(10597817/50000000), 0, (8421081/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (13655669/100000000), (56531/20000000), (1/100000000), (1/100000000), (1/100000000), (1669603/25000000)]
    alternative := .zero
    polynomial := [(-16524596939357561596667838948921/4027753534172834740625000000000), (507045067126453/14132750000000), (-19875613990500178878080002851037/251734595885802171289062500000), (507045067126453/14132750000000), (-301485226908645300452612206667671/4027753534172834740625000000000)]
    bernstein := [(1953539438118762751327204540834827369/10311049047482456936000000000000000000), (16210096177811186604549298483298137/79315761903711207200000000000000000), (65336206168687787387425224395087971/309331471424473708080000000000000000), (166458017558540731474020161532209/793157619037112072000000000000000), (206398476842270619690198157893081/1031104904748245693600000000000000)]
    reserve := (94730392083/500000000000) }

theorem mixed_013_024_valid : mixed_013_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_024]
  · intro i; fin_cases i <;> norm_num [mixed_013_024]
  · norm_num [mixed_013_024]
  · norm_num [mixed_013_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_024]

def mixed_013_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(1628459/6250000), (1496541/3125000), 0, 0, 0, 0, (1628459/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1470071/6250000), 0, (20857507/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2755147/20000000), (70967/25000000), (1/100000000), (1/100000000), (1/100000000), (411479/6250000)]
    alternative := .zero
    polynomial := [(-24879443216157076672279931363/4881931601453481250000000000), (8915652947497/221771875000), (-197932890967261705887581431363/2440965800726740625000000000), (8915652947497/221771875000), (-370986338718366335102882931363/4881931601453481250000000000)]
    bernstein := [(271905960362782057528280836093/1249774489972091200000000000000), (2910143526992457498531728527759/12497744899720912000000000000000), (89934516086731817054715753141743/374932346991627360000000000000000), (298033339768252990630951300251367/1249774489972091200000000000000000), (2855573891387047266803904248880717/12497744899720912000000000000000000)]
    reserve := (27195502323/125000000000) }

theorem mixed_013_025_valid : mixed_013_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_025]
  · intro i; fin_cases i <;> norm_num [mixed_013_025]
  · norm_num [mixed_013_025]
  · norm_num [mixed_013_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_025]

def mixed_013_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(5137/20000), (48630001/100000000), 0, 0, 0, 0, (5137/20000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(516549/2000000), 0, (41204609/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1737059/12500000), (284669/100000000), (1/100000000), (1/100000000), (1/100000000), (3245043/50000000)]
    alternative := .zero
    polynomial := [(-19943979603061919804257472363941/3209262172445758506000000000000), (330029185937/7394000000), (-133717983750332365441551542693941/1604631086222879253000000000000), (330029185937/7394000000), (-247491987897602811078845613023941/3209262172445758506000000000000)]
    bernstein := [(2014779658904472142557948281053564619/8215711161461141775360000000000000000), (535955442790958870394591075973834387/2053927790365285443840000000000000000), (413084042864694469442627238934583453/1540445842773964082880000000000000000), (34240141638336248295760742198556623/128370486897830340240000000000000000), (8230651646511049697246517366556979/32092621724457585060000000000000000)]
    reserve := (122617483703/500000000000) }

theorem mixed_013_026_valid : mixed_013_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_026]
  · intro i; fin_cases i <;> norm_num [mixed_013_026]
  · norm_num [mixed_013_026]
  · norm_num [mixed_013_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_026]

def mixed_013_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(12660291/50000000), (9871767/20000000), 0, 0, 0, 0, (12660291/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1124187/4000000), 0, (324609/800000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (14017311/100000000), (2227/781250), (1/100000000), (1/100000000), (1/100000000), (1279601/20000000)]
    alternative := .zero
    polynomial := [(-26490943971544245111384882757923/3550642723562026400000000000000), (10699615142739/217600000000), (-8948426137372523967700705164069/104430668340059600000000000000), (10699615142739/217600000000), (-277755544699121569790439092820423/3550642723562026400000000000000)]
    bernstein := [(9675713595350563064243229317429337/35506427235620264000000000000000000), (40998407531301999038221699816970277/142025708942481056000000000000000000), (24032014166911215248087954048704631/81157547967132032000000000000000000), (669614503845891695268366035743475757/2272411343079696896000000000000000000), (2582650433428798965347449459955760297/9089645372318787584000000000000000000)]
    reserve := (6812649391/25000000000) }

theorem mixed_013_027_valid : mixed_013_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_027]
  · intro i; fin_cases i <;> norm_num [mixed_013_027]
  · norm_num [mixed_013_027]
  · norm_num [mixed_013_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_027]

def mixed_013_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(12481683/50000000), (50073269/100000000), 0, 0, 0, 0, (12481683/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(30343179/100000000), 0, (19916223/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1413767/10000000), (285029/100000000), (1/100000000), (1/100000000), (1/100000000), (6307743/100000000)]
    alternative := .zero
    polynomial := [(-187211897787431618876476945657007/21181642488201029575000000000000), (1533612730877379/28502900000000), (-933610976053902201435961652407007/10590821244100514787500000000000), (1533612730877379/28502900000000), (-1680010054320372783995446359157007/21181642488201029575000000000000)]
    bernstein := [(16234914048362855611436540283479417473/54225004769794635712000000000000000000), (8569033589097442578551678933336613747/27112502384897317856000000000000000000), (13166768886888104303188525526273074699/40668753577345976784000000000000000000), (2184668102358021860817211199683186587/6778125596224329464000000000000000000), (1055681427169639360302215619783231793/3389062798112164732000000000000000000)]
    reserve := (29939903403/100000000000) }

theorem mixed_013_028_valid : mixed_013_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_028]
  · intro i; fin_cases i <;> norm_num [mixed_013_028]
  · norm_num [mixed_013_028]
  · norm_num [mixed_013_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_028]

def mixed_013_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 2]
    lambda := ![(3076823/12500000), (3173177/6250000), 0, 0, 0, 0, (3076823/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32533719/100000000), 0, (38977359/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3564241/25000000), (17787/6250000), (1/100000000), (1/100000000), (1/100000000), (6219613/100000000)]
    alternative := .zero
    polynomial := [(-102023261932304805290492379087241/9857644183247096775000000000000), (4957661336499/84700000000), (-447175752580446759588268422462241/4928822091623548387500000000000), (4957661336499/84700000000), (-792328243228588713886044465837241/9857644183247096775000000000000)]
    bernstein := [(514057708885098796836462469551377159/1577223069319535484000000000000000000), (216463237488063898472384614767511171/630889227727814193600000000000000000), (265797064596976673654194367163546941/757067073273377032320000000000000000), (35294874341078577317789280449284667/100942276436450270976000000000000000), (13670181998989851207095455715342711/40376910574580108390400000000000000)]
    reserve := (325925811563/1000000000000) }

theorem mixed_013_029_valid : mixed_013_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_013_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_013_029]
  · intro i; fin_cases i <;> norm_num [mixed_013_029]
  · norm_num [mixed_013_029]
  · norm_num [mixed_013_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_013_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_013_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_013_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_013_029]

def mixedTable013 : OwnerTable where
  mode := .mixed
  owners := ![0, 3, 0, 2, 0, 2, 2]
  rows := [mixed_013_000, mixed_013_001, mixed_013_002, mixed_013_003, mixed_013_004, mixed_013_005, mixed_013_006, mixed_013_007, mixed_013_008, mixed_013_009, mixed_013_010, mixed_013_011, mixed_013_012, mixed_013_013, mixed_013_014, mixed_013_015, mixed_013_016, mixed_013_017, mixed_013_018, mixed_013_019, mixed_013_020, mixed_013_021, mixed_013_022, mixed_013_023, mixed_013_024, mixed_013_025, mixed_013_026, mixed_013_027, mixed_013_028, mixed_013_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_013_000_valid
    · exact mixed_013_001_valid
    · exact mixed_013_002_valid
    · exact mixed_013_003_valid
    · exact mixed_013_004_valid
    · exact mixed_013_005_valid
    · exact mixed_013_006_valid
    · exact mixed_013_007_valid
    · exact mixed_013_008_valid
    · exact mixed_013_009_valid
    · exact mixed_013_010_valid
    · exact mixed_013_011_valid
    · exact mixed_013_012_valid
    · exact mixed_013_013_valid
    · exact mixed_013_014_valid
    · exact mixed_013_015_valid
    · exact mixed_013_016_valid
    · exact mixed_013_017_valid
    · exact mixed_013_018_valid
    · exact mixed_013_019_valid
    · exact mixed_013_020_valid
    · exact mixed_013_021_valid
    · exact mixed_013_022_valid
    · exact mixed_013_023_valid
    · exact mixed_013_024_valid
    · exact mixed_013_025_valid
    · exact mixed_013_026_valid
    · exact mixed_013_027_valid
    · exact mixed_013_028_valid
    · exact mixed_013_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
