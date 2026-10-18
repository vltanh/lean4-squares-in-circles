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

def mixed_005_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2103217/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10252217/50000000)]
    alternative := .zero
    polynomial := [(-44023114674015643/64076356250000000), (-42064340/10252217), (-108099470924015643/32038178125000000), (-42064340/10252217), (-172175827174015643/64076356250000000)]
    bernstein := [(141809012789670638453/262456755200000000000), (343300361474731309041/656141888000000000000), (830020257690478769581/1640354720000000000000), (2004034820269922709033/4100886800000000000000), (4831435808391272355557/10252217000000000000000)]
    reserve := (235628830739/500000000000) }

theorem mixed_005_000_valid : mixed_005_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_000]
  · intro i; fin_cases i <;> norm_num [mixed_005_000]
  · norm_num [mixed_005_000]
  · norm_num [mixed_005_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_000]

def mixed_005_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2034299/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (21221563/100000000)]
    alternative := .zero
    polynomial := [(-3208677076379484783/5305390750000000000), (-81371960/21221563), (-8514067826379484783/2652695375000000000), (-81371960/21221563), (-13819458576379484783/5305390750000000000)]
    bernstein := [(398440040343319488262417/848862520000000000000000), (769821467242199697197803/1697725040000000000000000), (45932083125209102361323/105013920000000000000000), (2860481863390760054215843/6790900160000000000000000), (5499790888762519119986337/13581800320000000000000000)]
    reserve := (101234570513/250000000000) }

theorem mixed_005_001_valid : mixed_005_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_001]
  · intro i; fin_cases i <;> norm_num [mixed_005_001]
  · norm_num [mixed_005_001]
  · norm_num [mixed_005_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_001]

def mixed_005_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9801009/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (10952843/50000000)]
    alternative := .zero
    polynomial := [(-363637498625870721/684552687500000000), (-39204036/10952843), (-1048190186125870721/342276343750000000), (-39204036/10952843), (-1732742873625870721/684552687500000000)]
    bernstein := [(706675921377271574660719/1752454880000000000000000), (170164574608636430907889/438113720000000000000000), (122704851143483119262377/328585290000000000000000), (9812135429753460129429/27382107500000000000000), (2348855363451029963799/6845526875000000000000)]
    reserve := (68624531211/200000000000) }

theorem mixed_005_002_valid : mixed_005_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_002]
  · intro i; fin_cases i <;> norm_num [mixed_005_002]
  · norm_num [mixed_005_002]
  · norm_num [mixed_005_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_002]

def mixed_005_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15047591/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (11276477/50000000)]
    alternative := .zero
    polynomial := [(-524938673940135577/1127647700000000000), (-75237955/22552954), (-1652586373940135577/563823850000000000), (-75237955/22552954), (-2780234073940135577/1127647700000000000)]
    bernstein := [(3852164470017249209663/11276477000000000000000), (14785097576622421172331/45105908000000000000000), (56622469239823249617947/180423632000000000000000), (216322409238953548968639/721694528000000000000000), (824229595857074902482743/2886778112000000000000000)]
    reserve := (57103772017/200000000000) }

theorem mixed_005_003_valid : mixed_005_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_003]
  · intro i; fin_cases i <;> norm_num [mixed_005_003]
  · norm_num [mixed_005_003]
  · norm_num [mixed_005_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_003]

def mixed_005_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4491503/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (578989/2500000)]
    alternative := .zero
    polynomial := [(-29462824520192343/72373625000000000), (-8983006/2894945), (-101836449520192343/36186812500000000), (-8983006/2894945), (-174210074520192343/72373625000000000)]
    bernstein := [(52650772859038990616537/185276480000000000000000), (5026655778528075186187/18527648000000000000000), (1435690711572844017523/5558294400000000000000), (45419841219800858899/185276480000000000000), (4295650663664412873/18527648000000000000)]
    reserve := (23185083523/100000000000) }

theorem mixed_005_004_valid : mixed_005_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_004]
  · intro i; fin_cases i <;> norm_num [mixed_005_004]
  · norm_num [mixed_005_004]
  · norm_num [mixed_005_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_004]

def mixed_005_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (68290369/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (23721789/100000000)]
    alternative := .zero
    polynomial := [(-210764274139286957/593044725000000000), (-9755767/3388827), (-803808999139286957/296522362500000000), (-9755767/3388827), (-1396853724139286957/593044725000000000)]
    bernstein := [(11673077141248689809/50606483200000000000), (110670728890942857513/506064832000000000000), (9408153823437247072057/45545834880000000000000), (29496803250769107672827/151819449600000000000000), (276096400943444349100723/1518194496000000000000000)]
    reserve := (7274335447/40000000000) }

theorem mixed_005_005_valid : mixed_005_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_005]
  · intro i; fin_cases i <;> norm_num [mixed_005_005]
  · norm_num [mixed_005_005]
  · norm_num [mixed_005_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_005]

def mixed_005_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (32261287/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4847213/20000000)]
    alternative := .zero
    polynomial := [(-375609446756191047/1211803250000000000), (-64522574/24236065), (-1587412696756191047/605901625000000000), (-64522574/24236065), (-2799215946756191047/1211803250000000000)]
    bernstein := [(560940833570278830838233/3102216320000000000000000), (65797831610969155648537/387777040000000000000000), (5757794751264887962951/36354097500000000000000), (445098889538428925301/3029508125000000000000), (25617743998203713057/189344257812500000000)]
    reserve := (135297179297/1000000000000) }

theorem mixed_005_006_valid : mixed_005_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_006]
  · intro i; fin_cases i <;> norm_num [mixed_005_006]
  · norm_num [mixed_005_006]
  · norm_num [mixed_005_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_006]

def mixed_005_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(1/2), 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (60567983/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (192961/781250)]
    alternative := .zero
    polynomial := [(-1669681908421438993/6174752000000000000), (-60567983/24699008), (-7844433908421438993/3087376000000000000), (-60567983/24699008), (-14019185908421438993/6174752000000000000)]
    bernstein := [(129666843351776810183/964805000000000000000), (1914749584812907669837/15436880000000000000000), (7008935084213645482667/61747520000000000000000), (203146714392013249812401/1975920640000000000000000), (1453309289924514668795407/15807365120000000000000000)]
    reserve := (91938743673/1000000000000) }

theorem mixed_005_007_valid : mixed_005_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_007]
  · intro i; fin_cases i <;> norm_num [mixed_005_007]
  · norm_num [mixed_005_007]
  · norm_num [mixed_005_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_007]

def mixed_005_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![0, 0, 0, 0, 0, 0, (99999999/100000000)]
    cone := fun i => (![![(49999999/100000000), 0, (99999999/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (440903/781250), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (12553741/50000000)]
    alternative := .zero
    polynomial := [(-5935636584719577481/25107482000000000000), (-44090299559097/19615220312500), (-31043118333644757481/12553741000000000000), (-44090299559097/19615220312500), (-56150600082569937481/25107482000000000000)]
    bernstein := [(5859829381509754810927319/64275153920000000000000000), (2620421160027097054035251/32137576960000000000000000), (3457836398323225342515437/48206365440000000000000000), (496059589125786925592491/8034394240000000000000000), (207168713346644870640839/4017197120000000000000000)]
    reserve := (25785231239/500000000000) }

theorem mixed_005_008_valid : mixed_005_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_008]
  · intro i; fin_cases i <;> norm_num [mixed_005_008]
  · norm_num [mixed_005_008]
  · norm_num [mixed_005_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_008]

def mixed_005_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(4602229/20000000), (1999543/10000000), (725643/10000000), (8732369/100000000), (8732369/100000000), (9261113/100000000), (4602229/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2735979/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1779447/100000000), (5374861/100000000), (2868893/100000000), (1/100000000), (643263/20000000), (2929163/50000000)]
    alternative := .zero
    polynomial := [(-74490244579715440598073370563218402319/68346854149434325039516821820000000000000), (-124474711827/142886000000), (-312495873747732854658296527132192037206957/102520281224151487559275232730000000000000), (-124474711827/142886000000), (-624768276761726562994798834152694419206957/205040562448302975118550465460000000000000)]
    bernstein := [(682338190600390312784993436122038831613675361/10935496663909492006322691491200000000000000000), (273635881696030319431288821453832066846599227/4374198665563796802529076596480000000000000000), (982579703731256481736965023026559814295767089/15747115196029668489104675747328000000000000000), (26002598813042193902070714947689807663258117/419923071894124493042791353262080000000000000), (2053722791421358703983137580690204859624267/33593845751529959443423308260966400000000000)]
    reserve := (30566949771/500000000000) }

theorem mixed_005_009_valid : mixed_005_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_009]
  · intro i; fin_cases i <;> norm_num [mixed_005_009]
  · norm_num [mixed_005_009]
  · norm_num [mixed_005_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_009]

def mixed_005_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(22780207/100000000), (2029513/10000000), (914633/12500000), (8769287/100000000), (8769287/100000000), (464441/5000000), (22780207/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (786557/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (743439/50000000), (1090257/20000000), (577173/20000000), (1/100000000), (3227809/100000000), (5865903/100000000)]
    alternative := .zero
    polynomial := [(437042735316785944177344068577878953909247/32806445001471712763162722287900000000000000), (-242767816422559/293295150000000), (-58040228451823708732402204915943263376590753/16403222500735856381581361143950000000000000), (-242767816422559/293295150000000), (-116517499638964203408981753900464405707090753/32806445001471712763162722287900000000000000)]
    bernstein := [(8579402135046320585224058882321253489006737/137820716642080138951707190247424000000000000), (53867877481773141658038632806841585287949669/861379479013000868448169939046400000000000000), (39337580095206393068883375278696820044604345689/629883744028256885052724267927680000000000000000), (5424023011416879415963860223844424598244516569/87483853337257900701767259434400000000000000000), (20072135984467723351583085812909915525807228647/328064450014717127631627222879000000000000000000)]
    reserve := (61183514347/1000000000000) }

theorem mixed_005_010_valid : mixed_005_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_010]
  · intro i; fin_cases i <;> norm_num [mixed_005_010]
  · norm_num [mixed_005_010]
  · norm_num [mixed_005_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_010]

def mixed_005_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(4516299/20000000), (20626807/100000000), (3683979/50000000), (4389713/50000000), (4389713/50000000), (4641697/50000000), (4516299/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (89197/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (298091/25000000), (5534511/100000000), (2896083/100000000), (1/100000000), (807143/25000000), (5866543/100000000)]
    alternative := .zero
    polynomial := [(4007779078241846705128795772186430699132089/150827525888149076910176066835780000000000000), (-461720023678007/586654300000000), (-324647064085692907311503489811326626455242911/75413762944074538455088033417890000000000000), (-461720023678007/586654300000000), (-653301907249627661328135775394839683609617911/150827525888149076910176066835780000000000000)]
    bernstein := [(94389347203089826431416735986919641764584689889/1508275258881490769101760668357800000000000000000), (380108293346145710365949799901533553362631168567/6033101035525963076407042673431200000000000000000), (4559266370416170071238425791363326217570312786103/72397212426311556916884512081174400000000000000000), (208039384688165548132654617110929289687863942207/3328607467876393421465954578444800000000000000000), (23777147552706428713501253242210517982335148952409/386118466273661636890050731099596800000000000000000)]
    reserve := (30789964259/500000000000) }

theorem mixed_005_011_valid : mixed_005_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_011]
  · intro i; fin_cases i <;> norm_num [mixed_005_011]
  · norm_num [mixed_005_011]
  · norm_num [mixed_005_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_011]

def mixed_005_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(22729073/100000000), (21282663/100000000), (7342031/100000000), (4264997/50000000), (4264997/50000000), (8857173/100000000), (22729073/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (908077/100000000), (1422177/25000000), (568763/20000000), (1/100000000), (1553573/50000000), (5952197/100000000)]
    alternative := .zero
    polynomial := [(25852341061837208317515596576863437733072849/679229632556296111178365563968700000000000000), (-454672537411851/595219700000000), (-1937668044752689578989239012004177183652427151/339614816278148055589182781984350000000000000), (-454672537411851/595219700000000), (-3901188430567216366295993620585217805037927151/679229632556296111178365563968700000000000000)]
    bernstein := [(110239845548573852945105517499361135048903199391969/1738827859344118044616615843759872000000000000000000), (55602184014941685905188477613960628023967101874923/869413929672059022308307921879936000000000000000000), (4386769246890031922939085550942971585055914432217/68637941816215185971708520148416000000000000000000), (79499797205850521966574127038257271223179182639/1256378511086790494665184858208000000000000000000), (6743479824177044025015585684947742280503096192049/108676741209007377788538490234992000000000000000000)]
    reserve := (15512702509/250000000000) }

theorem mixed_005_012_valid : mixed_005_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_012]
  · intro i; fin_cases i <;> norm_num [mixed_005_012]
  · norm_num [mixed_005_012]
  · norm_num [mixed_005_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_012]

def mixed_005_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(23106341/100000000), (22192479/100000000), (1812681/25000000), (8097833/100000000), (8097833/100000000), (162969/2000000), (23106341/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (123273/20000000), (2949651/50000000), (2746527/100000000), (1/100000000), (1451383/50000000), (19041/312500)]
    alternative := .zero
    polynomial := [(6615599624618881091016275393956142416753/136291643636489380589211169200000000000000), (-15290791320347/20310400000000), (-591817927071884399152239937489058545183247/68145821818244690294605584600000000000000), (-15290791320347/20310400000000), (-1190251453768387679395496150372073232783247/136291643636489380589211169200000000000000)]
    bernstein := [(1406766542690569985620486775167578935108599153/21806662981838300894273787072000000000000000000), (316077292211124660309403146347357669963072817/4845925107075177976505286016000000000000000000), (2431132765388295200302317647773511885592610837/37382850826008515818755063552000000000000000000), (1239368967801564532257695819823622368076043217/19383700428300711906021144064000000000000000000), (21611936042269129117125233001191518822683506353/348906607709412814308380593152000000000000000000)]
    reserve := (15485473451/250000000000) }

theorem mixed_005_013_valid : mixed_005_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_013]
  · intro i; fin_cases i <;> norm_num [mixed_005_013]
  · norm_num [mixed_005_013]
  · norm_num [mixed_005_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_013]

def mixed_005_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(11616703/50000000), (5729563/25000000), (3670017/50000000), (8096351/100000000), (8096351/100000000), (7082201/100000000), (11616703/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (20283/4000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (151063/50000000), (1216147/20000000), (552271/20000000), (1/100000000), (2711979/100000000), (6137309/100000000)]
    alternative := .zero
    polynomial := [(4958432241912692136942677632712468494686877/84436599181455840020586005677050000000000000), (-222928219867171/306865450000000), (-758717439468281715552315446445127330651313123/42218299590727920010293002838525000000000000), (-222928219867171/306865450000000), (-1522393311178476123241573570522967129797313123/84436599181455840020586005677050000000000000)]
    bernstein := [(14192418261103876641705864782970527607599565813277/216157693904526950452700174533248000000000000000000), (9015374541166679025937358939913873560180058827/135098558690329344032937609083280000000000000000), (26722191351772351413437054097590529082585696477/405295676070988032098812827249840000000000000000), (5341810786710578686074398143859948457055627/84436599181455840020586005677050000000000000), (4958432241912692136942677632712468494686877/84436599181455840020586005677050000000000000)]
    reserve := (58723732243/1000000000000) }

theorem mixed_005_014_valid : mixed_005_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_014]
  · intro i; fin_cases i <;> norm_num [mixed_005_014]
  · norm_num [mixed_005_014]
  · norm_num [mixed_005_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_014]

def mixed_005_015 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(24251487/100000000), (24259067/100000000), (7398089/100000000), (7983203/100000000), (1475577/25000000), (148859/2500000), (24251487/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(303191/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(20809/20000000), 0, (416179/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (153233/100000000), (1281697/20000000), (275019/10000000), (1/100000000), (264809/12500000), (319123/5000000)]
    alternative := .zero
    polynomial := [(7144413959666182997182845452700689658151/114111976218563770727734845825000000000000), (4767862779022351/3912013972720000), (-2211120913665122261183264234224148031716849/57055988109281885363867422912500000000000), (4767862779022351/3912013972720000), (-4429386241289910705363711313900996753091849/114111976218563770727734845825000000000000)]
    bernstein := [(7144413959666182997182845452700689658151/114111976218563770727734845825000000000000), (1001705466834169952937972512193308131097/14263997027320471340966855728125000000000), (40426671932801451737975366529258606077407951/547737485849106099493127259960000000000000000), (837069598225639094829755982500095191982211/11411197621856377072773484582500000000000000), (20116159393409281910231099843030343789119551351/292126659119523253063001205312000000000000000000)]
    reserve := (7826100069/125000000000) }

theorem mixed_005_015_valid : mixed_005_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_015]
  · intro i; fin_cases i <;> norm_num [mixed_005_015]
  · norm_num [mixed_005_015]
  · norm_num [mixed_005_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_015]

def mixed_005_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(349323/1250000), (7006137/25000000), (7859373/100000000), (8224399/100000000), 0, 0, (349323/1250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(209889/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(20561/5000000), 0, (8224399/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5184689/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (44213/25000000), (7354443/100000000), (359307/12500000), (1/100000000), (1/100000000), (7309211/100000000)]
    alternative := .zero
    polynomial := [(42888985370423918070225016059311/2591281723532024717460000000000000), (916452233126944743/248586266110000000), (-58057289945509865176741199215940689/1295640861766012358730000000000000), (916452233126944743/248586266110000000), (-116157468876390154271552623447940689/2591281723532024717460000000000000)]
    bernstein := [(6963854072585339429359991887840874188643/86237855759145782597068800000000000000000), (430307594717457069739666960974039146027/4790991986619210144281600000000000000000), (320749838279401880769906311440473805091/3404125885229438786726400000000000000000), (16079292721411649234773010558033107661/171106856664971790867200000000000000000), (68559476856008709822920795216320069349/769980854992373058902400000000000000000)]
    reserve := (80751707139/1000000000000) }

theorem mixed_005_016_valid : mixed_005_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_016]
  · intro i; fin_cases i <;> norm_num [mixed_005_016]
  · norm_num [mixed_005_016]
  · norm_num [mixed_005_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_016]

def mixed_005_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(6649283/20000000), (33507171/100000000), 0, 0, 0, 0, (6649283/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4172099/100000000), 0, 0, 0, 0], ![0, 0, (2187637/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4475251/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (210989/100000000), (2187637/25000000), (1/100000000), (1/100000000), (1/100000000), (8642019/100000000)]
    alternative := .zero
    polynomial := [(-3237060170055266757756680989087/26592491652833485780000000000000), (324490486945973288749/45584273669775000000), (-714101861899484780848196714489087/13296245826416742890000000000000), (324490486945973288749/45584273669775000000), (-1424966663628914294938636747989087/26592491652833485780000000000000)]
    bernstein := [(1282600958652658461901544161228463939/12764395993360073174400000000000000000), (2848311024405385849876578088982056217/25528791986720146348800000000000000000), (1992867852474452374005291027959589017/17019194657813430899200000000000000000), (11951261290487457598573754799523671953/102115167946880585395200000000000000000), (7581222496092671640983353580208458353/68076778631253723596800000000000000000)]
    reserve := (100482698853/1000000000000) }

theorem mixed_005_017_valid : mixed_005_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_017]
  · intro i; fin_cases i <;> norm_num [mixed_005_017]
  · norm_num [mixed_005_017]
  · norm_num [mixed_005_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_017]

def mixed_005_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(33162759/100000000), (16837241/50000000), 0, 0, 0, 0, (33162759/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(5848259/100000000), 0, 0, 0, 0], ![0, 0, (4397121/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2769607/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (211319/100000000), (4397121/50000000), (1/100000000), (1/100000000), (1/100000000), (8545721/100000000)]
    alternative := .zero
    polynomial := [(-247332963459119654164291722986561/794064304140673887900000000000000), (1783335735675945017233/180587321599900000000), (-21492271735776783045213118362986561/397032152070336943950000000000000), (1783335735675945017233/180587321599900000000), (-42737210508094446436261945002986561/794064304140673887900000000000000)]
    bernstein := [(258433598528689352051620944899588971759/2032804618600125153024000000000000000000), (70424673585279051390220210400570710453/508201154650031288256000000000000000000), (55047581796379886296857741158363187553/381150865987523466192000000000000000000), (4594516063219196003901479666460507617/31762572165626955516000000000000000000), (1105437251270410903299989207464091239/7940643041406738879000000000000000000)]
    reserve := (127131548287/1000000000000) }

theorem mixed_005_018_valid : mixed_005_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_018]
  · intro i; fin_cases i <;> norm_num [mixed_005_018]
  · norm_num [mixed_005_018]
  · norm_num [mixed_005_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_018]

def mixed_005_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(8262723/25000000), (4237277/12500000), 0, 0, 0, 0, (8262723/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(301271/4000000), 0, 0, 0, 0], ![0, 0, (8852671/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1072127/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (211737/100000000), (8852671/100000000), (1/100000000), (1/100000000), (1/100000000), (4211039/50000000)]
    alternative := .zero
    polynomial := [(-5388733181028227902011081670289/9396823237012117325000000000000), (80737370781967606997/6368805462450000000), (-257102028733967205355239796670289/4698411618506058662500000000000), (80737370781967606997/6368805462450000000), (-508815324286906182808468511670289/9396823237012117325000000000000)]
    bernstein := [(43494738729486959665976454789145733/281904697110363519750000000000000000), (12489656874709006534958824613115691/75174585896096938600000000000000000), (10365242798658352271319875189506819/60139668716877550880000000000000000), (1663571108502671602153788706035683/9622346994700408140800000000000000), (774495228345668762388099103963477/4618726557456195907584000000000000)]
    reserve := (38572201151/250000000000) }

theorem mixed_005_019_valid : mixed_005_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_019]
  · intro i; fin_cases i <;> norm_num [mixed_005_019]
  · norm_num [mixed_005_019]
  · norm_num [mixed_005_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_019]

def mixed_005_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(3291053/10000000), (1708947/5000000), 0, 0, 0, 0, (3291053/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4612401/50000000), 0, 0, 0, 0], ![0, 0, (8925983/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (42449/20000000), (278937/3125000), (1/100000000), (1/100000000), (1/100000000), (8315833/100000000)]
    alternative := .zero
    polynomial := [(-210172465121074543147340396849/231680999730957480000000000000), (16463207247479/1061225000000), (-109236653292491160670045822746433/1969288497713138580000000000000), (16463207247479/1061225000000), (-214900374677924054106586858746433/3938576995426277160000000000000)]
    bernstein := [(117618088478499584606476416172823/645296454930641249894400000000000), (1568371107079634475102190915668473/8066205686633015623680000000000000), (60768694476637930341828613569321941/302482713248738085888000000000000000), (50819923347429114094278561313151189/252068927707281738240000000000000000), (123831677675500664293718817813941327/630172319268204345600000000000000000)]
    reserve := (18226985067/100000000000) }

theorem mixed_005_020_valid : mixed_005_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_020]
  · intro i; fin_cases i <;> norm_num [mixed_005_020]
  · norm_num [mixed_005_020]
  · norm_num [mixed_005_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_020]

def mixed_005_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(32741317/100000000), (17258683/50000000), 0, 0, 0, 0, (32741317/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(85387/781250), 0, 0, 0, 0], ![0, 0, (1802873/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (106421/50000000), (1802873/20000000), (1/100000000), (1/100000000), (1/100000000), (2068269/25000000)]
    alternative := .zero
    polynomial := [(-3751802095980339365327070089/2858766858241700000000000000), (97799062277001/5321050000000), (-80584903870226227004689570089/1429383429120850000000000000), (97799062277001/5321050000000), (-157418005644472114644052070089/2858766858241700000000000000)]
    bernstein := [(96158351804691525321074823441991/457402697318672000000000000000000), (29077736275544699479693078126397/130686484948192000000000000000000), (59851155291176311339825205113593/261372969896384000000000000000000), (840275951244567846402677253479219/3659221578549376000000000000000000), (1641935399880226272330191841921111/7318443157098752000000000000000000)]
    reserve := (210226901521/1000000000000) }

theorem mixed_005_021_valid : mixed_005_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_021]
  · intro i; fin_cases i <;> norm_num [mixed_005_021]
  · norm_num [mixed_005_021]
  · norm_num [mixed_005_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_021]

def mixed_005_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(32542819/100000000), (34914361/100000000), 0, 0, 0, 0, (32542819/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(12648221/100000000), 0, 0, 0, 0], ![0, 0, (4559021/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (53383/25000000), (4559021/50000000), (1/100000000), (1/100000000), (1/100000000), (205573/2500000)]
    alternative := .zero
    polynomial := [(-26988940365780983549465355832373/15009350437726091700000000000000), (455502420455197/21353200000000), (-431199971565339821631981658957373/7504675218863045850000000000000), (455502420455197/21353200000000), (-835411002764898659714497962082373/15009350437726091700000000000000)]
    bernstein := [(9122285407971394399342618038939256027/38423937120578794752000000000000000000), (399991056089874120499329228936455187/1600997380024116448000000000000000000), (115443768213018852632125437844097161/450280513131782751000000000000000000), (3214156224361368176576549895548919/12507792031438409750000000000000000), (589865901217077385013287010578963/2345211005894701828125000000000000)]
    reserve := (59352880597/250000000000) }

theorem mixed_005_022_valid : mixed_005_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_022]
  · intro i; fin_cases i <;> norm_num [mixed_005_022]
  · norm_num [mixed_005_022]
  · norm_num [mixed_005_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_022]

def mixed_005_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(16157263/50000000), (8842737/25000000), 0, 0, 0, 0, (16157263/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14383163/100000000), 0, 0, 0, 0], ![0, 0, (9237281/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (107157/50000000), (4618641/50000000), (1/100000000), (1/100000000), (1/100000000), (4082617/50000000)]
    alternative := .zero
    polynomial := [(-79786758045884954400023510238809/33676127275492467150000000000000), (43549751766571/1785950000000), (-988689214918525010370892388238809/16838063637746233575000000000000), (43549751766571/1785950000000), (-1897591671791165066341761266238809/33676127275492467150000000000000)]
    bernstein := [(1388666183540505514114891933141279/5261894886795697992187500000000000), (2116536674923062549418092201514177/7653665289884651625000000000000000), (40868426669024554148727034198010071/144326259752110573500000000000000000), (277944898781746463784244437949929349/979669157105235408000000000000000000), (23973035271924825901273182630276841351/86210885825260715904000000000000000000)]
    reserve := (26390990573/100000000000) }

theorem mixed_005_023_valid : mixed_005_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_023]
  · intro i; fin_cases i <;> norm_num [mixed_005_023]
  · norm_num [mixed_005_023]
  · norm_num [mixed_005_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_023]

def mixed_005_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(16027921/50000000), (35888317/100000000), 0, 0, 0, 0, (16027921/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(8068369/50000000), 0, 0, 0, 0], ![0, 0, (4686197/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (26899/12500000), (1874479/20000000), (1/100000000), (1/100000000), (1/100000000), (809987/10000000)]
    alternative := .zero
    polynomial := [(-1160601405932145502754800252561/382882960519424315625000000000), (296458345096637/10759600000000), (-46071687817820944076189718182119/765765921038848631250000000000), (296458345096637/10759600000000), (-43750485005956653070680117676997/765765921038848631250000000000)]
    bernstein := [(13856205727554599584579712875564763/47813677020962256000000000000000000), (180899477413873343151178593645739/597670962762028200000000000000000), (18196931979376915980033143928252847/58810822735783574880000000000000000), (303782005741899809239670415360997/980180378929726248000000000000000), (1611142184905645947117185886091/5298272318539060800000000000000)]
    reserve := (289795861579/1000000000000) }

theorem mixed_005_024_valid : mixed_005_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_024]
  · intro i; fin_cases i <;> norm_num [mixed_005_024]
  · norm_num [mixed_005_024]
  · norm_num [mixed_005_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_024]

def mixed_005_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(15883043/50000000), (36467829/100000000), 0, 0, 0, 0, (15883043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(17911403/100000000), 0, 0, 0, 0], ![0, 0, (9523737/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (108083/50000000), (9523737/100000000), (1/100000000), (1/100000000), (1/100000000), (1605331/20000000)]
    alternative := .zero
    polynomial := [(-11599286253380220637854285358609/3060099985926588150000000000000), (666923477246639/21616600000000), (-94567206401697247304949286108609/1530049992963294075000000000000), (666923477246639/21616600000000), (-177535126550014273972044286858609/3060099985926588150000000000000)]
    bernstein := [(8512731454238543312073339615931/27013296427489881600000000000000), (857299153782085914365470999757879/2611285321324021888000000000000000), (78773871484273754911987101978004949/235015678919161969920000000000000000), (87651854947156590206813735864282927/261128532132402188800000000000000000), (2582168485333343240030639372300660831/7833855963972065664000000000000000000)]
    reserve := (157565580289/500000000000) }

theorem mixed_005_025_valid : mixed_005_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_025]
  · intro i; fin_cases i <;> norm_num [mixed_005_025]
  · norm_num [mixed_005_025]
  · norm_num [mixed_005_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_025]

def mixed_005_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(15722243/50000000), (37111027/100000000), 0, 0, 0, 0, (15722243/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1970971/10000000), 0, 0, 0, 0], ![0, 0, (9691711/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5431/2500000), (9691711/100000000), (1/100000000), (1/100000000), (1/100000000), (7945393/100000000)]
    alternative := .zero
    polynomial := [(-145985627031792748642044872746451/31365838711270823475000000000000), (14902191604989/434480000000), (-998279935735367644310827960677701/15682919355635411737500000000000), (14902191604989/434480000000), (-1850574244438942539979611048608951/31365838711270823475000000000000)]
    bernstein := [(27298064329578792289112972609133461209/80296547100853308096000000000000000000), (7095863799125857784372187603941696207/20074136775213327024000000000000000000), (5427973074446919930231957933776700283/15055602581409995268000000000000000000), (452901089940288857291343195110995903/1254633548450832939000000000000000000), (111255650486730480536965834025178169/313658387112708234750000000000000000)]
    reserve := (10623925201/31250000000) }

theorem mixed_005_026_valid : mixed_005_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_026]
  · intro i; fin_cases i <;> norm_num [mixed_005_026]
  · norm_num [mixed_005_026]
  · norm_num [mixed_005_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_026]

def mixed_005_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(1243607/4000000), (756393/2000000), 0, 0, 0, 0, (1243607/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(269179/1250000), 0, 0, 0, 0], ![0, 0, (9876771/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (43683/20000000), (9876771/100000000), (1/100000000), (1/100000000), (1/100000000), (1571173/20000000)]
    alternative := .zero
    polynomial := [(-565480765587715178744091286889/100426349309252828000000000000), (1104002088711/29122000000), (-3299889253040476492150635286889/50213174654626414000000000000), (1104002088711/29122000000), (-6034297740493237805557179286889/100426349309252828000000000000)]
    bernstein := [(365890442587092670174452872471791/1004263493092528280000000000000000), (1519429018597700763012480258074461/4017053972370113120000000000000000), (18581960561778707657525864075706193/48204647668441357440000000000000000), (24803652582550517549006337500584601/64272863557921809920000000000000000), (97535544504864814272003203121752071/257091454231687239680000000000000000)]
    reserve := (364337093903/1000000000000) }

theorem mixed_005_027_valid : mixed_005_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_027]
  · intro i; fin_cases i <;> norm_num [mixed_005_027]
  · norm_num [mixed_005_027]
  · norm_num [mixed_005_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_027]

def mixed_005_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(15351091/50000000), (9648909/25000000), 0, 0, 0, 0, (15351091/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(11694007/50000000), 0, 0, 0, 0], ![0, 0, (10079423/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (13731/6250000), (10079423/100000000), (1/100000000), (1/100000000), (1/100000000), (7757827/100000000)]
    alternative := .zero
    polynomial := [(-7372416754753055643764281979209/1095599570981689950000000000000), (38173565344177/915400000000), (-37255365168082287991159772354209/547799785490844975000000000000), (38173565344177/915400000000), (-67138313581411520338555262729209/1095599570981689950000000000000)]
    bernstein := [(1088999022190133167731194385289794551/2804734901713126272000000000000000000), (17109607369794700141315431596040533/42495983359289792000000000000000000), (862599126885335205089045276749306013/2103551176284844704000000000000000000), (4360899068322737819342600247549293/10623995839822448000000000000000000), (70761661636763484660572790513736391/175295931357070392000000000000000000)]
    reserve := (388271640761/1000000000000) }

theorem mixed_005_028_valid : mixed_005_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_028]
  · intro i; fin_cases i <;> norm_num [mixed_005_028]
  · norm_num [mixed_005_028]
  · norm_num [mixed_005_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_028]

def mixed_005_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 2]
    lambda := ![(30279427/100000000), (19720573/50000000), 0, 0, 0, 0, (30279427/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(6318427/25000000), 0, 0, 0, 0], ![0, 0, (1287529/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (44217/20000000), (1287529/12500000), (1/100000000), (1/100000000), (1/100000000), (3825503/50000000)]
    alternative := .zero
    polynomial := [(-10196901152793770031122440842949/1281108518147828700000000000000), (505106330712979/11054250000000), (-15062075192413212385791868680983/213518086357971450000000000000), (505106330712979/11054250000000), (-4716208823628559075507574778997/75359324596931100000000000000)]
    bernstein := [(84406243008745409764921515426238651/204977362903652592000000000000000000), (34978569760114999792924218576377719/81990945161461036800000000000000000), (14243626637398685177904447139652083/32796378064584414720000000000000000), (5702489730236946519489963956114863/13118551225833765888000000000000000), (2243687753161931420595428430324779/5247420490333506355200000000000000)]
    reserve := (411783241881/1000000000000) }

theorem mixed_005_029_valid : mixed_005_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_005_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_005_029]
  · intro i; fin_cases i <;> norm_num [mixed_005_029]
  · norm_num [mixed_005_029]
  · norm_num [mixed_005_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_005_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_005_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_005_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_005_029]

def mixedTable005 : OwnerTable where
  mode := .mixed
  owners := ![0, 1, 0, 2, 0, 2, 2]
  rows := [mixed_005_000, mixed_005_001, mixed_005_002, mixed_005_003, mixed_005_004, mixed_005_005, mixed_005_006, mixed_005_007, mixed_005_008, mixed_005_009, mixed_005_010, mixed_005_011, mixed_005_012, mixed_005_013, mixed_005_014, mixed_005_015, mixed_005_016, mixed_005_017, mixed_005_018, mixed_005_019, mixed_005_020, mixed_005_021, mixed_005_022, mixed_005_023, mixed_005_024, mixed_005_025, mixed_005_026, mixed_005_027, mixed_005_028, mixed_005_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_005_000_valid
    · exact mixed_005_001_valid
    · exact mixed_005_002_valid
    · exact mixed_005_003_valid
    · exact mixed_005_004_valid
    · exact mixed_005_005_valid
    · exact mixed_005_006_valid
    · exact mixed_005_007_valid
    · exact mixed_005_008_valid
    · exact mixed_005_009_valid
    · exact mixed_005_010_valid
    · exact mixed_005_011_valid
    · exact mixed_005_012_valid
    · exact mixed_005_013_valid
    · exact mixed_005_014_valid
    · exact mixed_005_015_valid
    · exact mixed_005_016_valid
    · exact mixed_005_017_valid
    · exact mixed_005_018_valid
    · exact mixed_005_019_valid
    · exact mixed_005_020_valid
    · exact mixed_005_021_valid
    · exact mixed_005_022_valid
    · exact mixed_005_023_valid
    · exact mixed_005_024_valid
    · exact mixed_005_025_valid
    · exact mixed_005_026_valid
    · exact mixed_005_027_valid
    · exact mixed_005_028_valid
    · exact mixed_005_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
