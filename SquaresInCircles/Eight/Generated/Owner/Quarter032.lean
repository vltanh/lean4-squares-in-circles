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

def quarter_032_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_032_000_valid : quarter_032_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_000]
  · intro i; fin_cases i <;> norm_num [quarter_032_000]
  · norm_num [quarter_032_000]
  · norm_num [quarter_032_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_000]

def quarter_032_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_032_001_valid : quarter_032_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_001]
  · intro i; fin_cases i <;> norm_num [quarter_032_001]
  · norm_num [quarter_032_001]
  · norm_num [quarter_032_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_001]

def quarter_032_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_032_002_valid : quarter_032_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_002]
  · intro i; fin_cases i <;> norm_num [quarter_032_002]
  · norm_num [quarter_032_002]
  · norm_num [quarter_032_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_002]

def quarter_032_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_032_003_valid : quarter_032_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_003]
  · intro i; fin_cases i <;> norm_num [quarter_032_003]
  · norm_num [quarter_032_003]
  · norm_num [quarter_032_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_003]

def quarter_032_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_032_004_valid : quarter_032_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_004]
  · intro i; fin_cases i <;> norm_num [quarter_032_004]
  · norm_num [quarter_032_004]
  · norm_num [quarter_032_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_004]

def quarter_032_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_032_005_valid : quarter_032_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_005]
  · intro i; fin_cases i <;> norm_num [quarter_032_005]
  · norm_num [quarter_032_005]
  · norm_num [quarter_032_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_005]

def quarter_032_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_032_006_valid : quarter_032_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_006]
  · intro i; fin_cases i <;> norm_num [quarter_032_006]
  · norm_num [quarter_032_006]
  · norm_num [quarter_032_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_006]

def quarter_032_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_032_007_valid : quarter_032_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_007]
  · intro i; fin_cases i <;> norm_num [quarter_032_007]
  · norm_num [quarter_032_007]
  · norm_num [quarter_032_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_007]

def quarter_032_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_032_008_valid : quarter_032_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_008]
  · intro i; fin_cases i <;> norm_num [quarter_032_008]
  · norm_num [quarter_032_008]
  · norm_num [quarter_032_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_008]

def quarter_032_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1067647938911762121/3859681000000000000), (-13528061/3859681), (-8309344188911762121/1929840500000000000), (-13528061/3859681), (-15551040438911762121/3859681000000000000)]
    bernstein := [(100068034278401520636999/617548960000000000000000), (36328949888069554679293/247019584000000000000000), (265685575963521009711/2016486400000000000000), (917720443345976065601/7904626688000000000000), (63294346623912201551/632370135040000000000)]
    reserve := (100090663863/1000000000000) }

theorem quarter_032_009_valid : quarter_032_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_009]
  · intro i; fin_cases i <;> norm_num [quarter_032_009]
  · norm_num [quarter_032_009]
  · norm_num [quarter_032_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_009]

def quarter_032_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![(238053/10000000), (421129/3125000), (421129/3125000), (11334029/50000000), (11334029/50000000), (11334029/50000000), (1331519/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8582903/100000000), 0, 0]] i.1) i.2
    mu := ![(808893/100000000), (900181/25000000), (1/100000000), (6663507/100000000), (1/100000000), (1/100000000), (1183973/20000000)]
    alternative := .zero
    polynomial := [(2767871251472828595151460981613793/34194502884323520078600375000000000), (-1570378773401153509/6067917580275000000), (-2750836331902932287377184016258707/17097251442161760039300187500000000), (-1570378773401153509/6067917580275000000), (-8269543915278693169905829014131207/34194502884323520078600375000000000)]
    bernstein := [(623143538560814819538603875078522017/5602427352567565529677885440000000000), (142391529811805001018869456027838427/1296858183464714242980992000000000000), (71140873784755523246155372641416012791/656534455379011585509127200000000000000), (1083175389962330505716006775478716779/10131704558318080023289000000000000000), (36058318120798543444264819222644907393/341945028843235200786003750000000000000)]
    reserve := (3295332133/31250000000) }

theorem quarter_032_010_valid : quarter_032_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_010]
  · intro i; fin_cases i <;> norm_num [quarter_032_010]
  · norm_num [quarter_032_010]
  · norm_num [quarter_032_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_010]

def quarter_032_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![(2533071/100000000), (6567687/50000000), (6567687/50000000), (22805481/100000000), (22805481/100000000), (22805481/100000000), (138987/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8735493/100000000), 0, 0]] i.1) i.2
    mu := ![(876871/100000000), (3502439/100000000), (1/100000000), (6649989/100000000), (1/100000000), (1/100000000), (2977877/50000000)]
    alternative := .zero
    polynomial := [(51915596624898215622559942985049513/633523510864039984902200593750000000), (-38084025021125428269/153559359418450000000), (-24455196172958066490104035009469931/158380877716009996225550148437500000), (-38084025021125428269/153559359418450000000), (-149736381316730481582976083022929237/633523510864039984902200593750000000)]
    bernstein := [(667914553493775527205158506721166847113/6335235108640399849022005937500000000000), (5272481586034420841884188898668769054653/50681880869123198792176047500000000000000), (5201149500747202181825238509640957431021/50681880869123198792176047500000000000000), (82068636630129428560749988695244615232727/810910093905971180674816760000000000000000), (161819756479190625641728134043793798311203/1621820187811942361349633520000000000000000)]
    reserve := (12472079033/125000000000) }

theorem quarter_032_011_valid : quarter_032_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_011]
  · intro i; fin_cases i <;> norm_num [quarter_032_011]
  · norm_num [quarter_032_011]
  · norm_num [quarter_032_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_011]

def quarter_032_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![(106927/4000000), (12780457/100000000), (12780457/100000000), (5741877/25000000), (5741877/25000000), (5741877/25000000), (1431693/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4430727/50000000), 0, 0]] i.1) i.2
    mu := ![(93927/10000000), (849109/25000000), (1/100000000), (6641431/100000000), (1/100000000), (1/100000000), (1499517/25000000)]
    alternative := .zero
    polynomial := [(912909343438969312741423865190101/11031497165276954242591125000000000), (-2515050879511890121/10633901472400000000), (-812840753646407924151370861743649/5515748582638477121295562500000000), (-2515050879511890121/10633901472400000000), (-2538590850731785161044165588677399/11031497165276954242591125000000000)]
    bernstein := [(2817195044026310516310136900584631136981/28240632743109002861033280000000000000000), (2778715372194628761783615155136566807579/28240632743109002861033280000000000000000), (27038840952741178860020652541481618627/278690454701733580865460000000000000000), (675209525493972569904805061051157913981/7060158185777250715258320000000000000000), (166337563424892385663967931712109369651/1765039546444312678814580000000000000000)]
    reserve := (94240134029/1000000000000) }

theorem quarter_032_012_valid : quarter_032_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_012]
  · intro i; fin_cases i <;> norm_num [quarter_032_012]
  · norm_num [quarter_032_012]
  · norm_num [quarter_032_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_012]

def quarter_032_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![(560241/20000000), (3103101/25000000), (3103101/25000000), (18089/78125), (18089/78125), (18089/78125), (2912227/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8958977/100000000), 0, 0]] i.1) i.2
    mu := ![(199041/20000000), (3283393/100000000), (1/100000000), (6638187/100000000), (1/100000000), (1/100000000), (24187/400000)]
    alternative := .zero
    polynomial := [(2914579439456442341524623199509053/34976443349063788022499000000000000), (-977345027569360569/4356865507420000000), (-2445431440711625127545545529180947/17488221674531894011249500000000000), (-977345027569360569/4356865507420000000), (-7805442320879692596615714257870947/34976443349063788022499000000000000)]
    bernstein := [(527293638425994372442206663651606851453/5596230935850206083599840000000000000000), (346587841665246912745930687666841067551/3730820623900137389066560000000000000000), (6148872430527379376394250018617591722759/67154771230202473003198080000000000000000), (1346300081285733569056413219175059148751/14923282495600549556266240000000000000000), (7955949286244043431041359893137460778653/89539694973603297337597440000000000000000)]
    reserve := (88853879707/1000000000000) }

theorem quarter_032_013_valid : quarter_032_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_013]
  · intro i; fin_cases i <;> norm_num [quarter_032_013]
  · norm_num [quarter_032_013]
  · norm_num [quarter_032_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_013]

def quarter_032_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (12928073/100000000), (12928073/100000000), (12357309/50000000), (12357309/50000000), (12357309/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1754919/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6454333/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (338523/10000000), (1/100000000), (7047677/100000000), (1/100000000), (1/100000000), (3227167/50000000)]
    alternative := .zero
    polynomial := [(53377355192143411772494331567/615950198776257268560000000000), (-7025593206901/56420500000000), (-298075547687744728550291387/3241843151453985624000000000), (-7025593206901/56420500000000), (-110011709252814910197049695097/615950198776257268560000000000)]
    bernstein := [(141467130523821576133856159389309703/1576832508867218607513600000000000000), (10959613865569949052437273069939/123190039755251453712000000000000), (52156989718347192638071932163807/591312190825206977817600000000000), (13464181528412882173113144011/153987549694064317140000000000), (53377355192143411772494331567/615950198776257268560000000000)]
    reserve := (43329278323/500000000000) }

theorem quarter_032_014_valid : quarter_032_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_014]
  · intro i; fin_cases i <;> norm_num [quarter_032_014]
  · norm_num [quarter_032_014]
  · norm_num [quarter_032_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_014]

def quarter_032_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (12962477/100000000), (12962477/100000000), (12345841/50000000), (12345841/50000000), (12345841/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4157603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6448343/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (847433/25000000), (1/100000000), (7046579/100000000), (1/100000000), (1/100000000), (806043/12500000)]
    alternative := .zero
    polynomial := [(6675249004963802438070157644911/77012618584157686416000000000000), (53892833262631/338973200000000), (-3613596942127848836506102682089/38506309292078843208000000000000), (53892833262631/338973200000000), (-13902442889219500111082363009089/77012618584157686416000000000000)]
    bernstein := [(6675249004963802438070157644911/77012618584157686416000000000000), (6751774748969423820362691646661/77012618584157686416000000000000), (414838338852380874986184519110009/4679247711442492339200000000000000), (11044184907970944308462201871577261/123220189734652298265600000000000000), (17861173423428834837204893355557666111/197152303575443677224960000000000000000)]
    reserve := (43338670517/500000000000) }

theorem quarter_032_015_valid : quarter_032_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_015]
  · intro i; fin_cases i <;> norm_num [quarter_032_015]
  · norm_num [quarter_032_015]
  · norm_num [quarter_032_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_015]

def quarter_032_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (13264361/100000000), (13264361/100000000), (12245213/50000000), (12245213/50000000), (12245213/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4896693/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (799473/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (863843/25000000), (1/100000000), (8797/125000), (1/100000000), (1/100000000), (1279157/20000000)]
    alternative := .zero
    polynomial := [(13373640006992256453528008193/155529667946043952000000000000), (64951503658173/345537200000000), (-7987259262931526807035028807/77764833973021976000000000000), (64951503658173/345537200000000), (-29348158532855310067598065807/155529667946043952000000000000)]
    bernstein := [(36083158840078221861594678911031793/398155949941872517120000000000000000), (18269495916607327858203068863637393/199077974970936258560000000000000000), (27743340234530120463157002487766179/298616962456404387840000000000000000), (4679975910432098425124206826125793/49769493742734064640000000000000000), (2367830400138003377964900183368593/24884746871367032320000000000000000)]
    reserve := (18125138577/200000000000) }

theorem quarter_032_016_valid : quarter_032_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_016]
  · intro i; fin_cases i <;> norm_num [quarter_032_016]
  · norm_num [quarter_032_016]
  · norm_num [quarter_032_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_016]

def quarter_032_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (3396331/25000000), (3396331/25000000), (24276451/100000000), (24276451/100000000), (24276451/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (707409/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (99061/1562500), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (879131/25000000), (1/100000000), (878669/12500000), (1/100000000), (1/100000000), (99061/1562500)]
    alternative := .zero
    polynomial := [(409011957371251643643712773/4839283534027888000000000000), (2402595116379/10989137500000), (-274871144183085037058591227/2419641767013944000000000000), (2402595116379/10989137500000), (-958754245737421717760895227/4839283534027888000000000000)]
    bernstein := [(73706459450109766382524437003173/774285365444462080000000000000000), (2047040307877358735334924753703/21213297683409920000000000000000), (908648712483852206697778341829271/9291424385333544960000000000000000), (8407481126912413074654100977327/84853190733639680000000000000000), (1243361127491539588216043707829013/12388565847111393280000000000000000)]
    reserve := (19038577439/200000000000) }

theorem quarter_032_017_valid : quarter_032_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_017]
  · intro i; fin_cases i <;> norm_num [quarter_032_017]
  · norm_num [quarter_032_017]
  · norm_num [quarter_032_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_017]

def quarter_032_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (2784801/20000000), (2784801/20000000), (24050663/100000000), (24050663/100000000), (24050663/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (64441/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3140469/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (111633/3125000), (1/100000000), (3511053/50000000), (1/100000000), (1/100000000), (6280939/100000000)]
    alternative := .zero
    polynomial := [(60220828643773693914249227/732681590486641818750000000), (59818453747/238150400000), (-5939027725366191976217323319/46891621791145076400000000000), (59818453747/238150400000), (-9793160758567708386729273847/46891621791145076400000000000)]
    bernstein := [(12054401203721703360250433047204793/120042551785331395584000000000000000), (235221433124321929221804410316737/2308510611256372992000000000000000), (2326436747691306864253060189494281/22507978459749636672000000000000000), (15123718752354997980209279085043/144281913203523312000000000000000), (49833621776141066297715048049253/468916217911450764000000000000000)]
    reserve := (20083547083/200000000000) }

theorem quarter_032_018_valid : quarter_032_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_018]
  · intro i; fin_cases i <;> norm_num [quarter_032_018]
  · norm_num [quarter_032_018]
  · norm_num [quarter_032_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_018]

def quarter_032_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (3569749/25000000), (3569749/25000000), (23814003/100000000), (23814003/100000000), (23814003/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1449893/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6219133/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (226353/6250000), (1/100000000), (7016121/100000000), (1/100000000), (1/100000000), (3109567/50000000)]
    alternative := .zero
    polynomial := [(8314124974925592560300150390459/105351800708299376448000000000000), (5175754086857/18108240000000), (-7481854006425943459352546349541/52675900354149688224000000000000), (5175754086857/18108240000000), (-23277832987777479479005243089541/105351800708299376448000000000000)]
    bernstein := [(112034703835317013531812509655592259/1053518007082993764480000000000000000), (30341412513478553006973298382821693/280938135222131670528000000000000000), (221795055264033112161287415391166333/2022754573599348027801600000000000000), (4002112834284417434295120053155109/35960081308432853827584000000000000), (1949277274200930150718569830059571/17260839028047769837240320000000000)]
    reserve := (106343416137/1000000000000) }

theorem quarter_032_019_valid : quarter_032_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_019]
  · intro i; fin_cases i <;> norm_num [quarter_032_019]
  · norm_num [quarter_032_019]
  · norm_num [quarter_032_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_019]

def quarter_032_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (457777/3125000), (457777/3125000), (368241/1562500), (368241/1562500), (368241/1562500), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (31536/390625), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3077369/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3663813/100000000), (1/100000000), (7011643/100000000), (1/100000000), (1/100000000), (6154739/100000000)]
    alternative := .zero
    polynomial := [(2948563745201983396034830464889/39527809197152858225250000000000), (153988858368/477058984375), (-3160788709908452223525214223111/19763904598576429112625000000000), (153988858368/477058984375), (-9270141165018887843085258911111/39527809197152858225250000000000)]
    bernstein := [(731927873281058855005432411484641/6476236258861524291624960000000000), (9298914263944371253225307417646991/80952953235769053645312000000000000), (354308131263336008892166539091705747/3035735746341339511699200000000000000), (299908472420759605331520730988962963/2529779788617782926416000000000000000), (761369897763655107024301357088840809/6324449471544457316040000000000000000)]
    reserve := (56508737793/500000000000) }

theorem quarter_032_020_valid : quarter_032_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_020]
  · intro i; fin_cases i <;> norm_num [quarter_032_020]
  · norm_num [quarter_032_020]
  · norm_num [quarter_032_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_020]

def quarter_032_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (15032171/100000000), (15032171/100000000), (11655943/50000000), (11655943/50000000), (11655943/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (8912819/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6088003/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3697913/100000000), (1/100000000), (70089/1000000), (1/100000000), (1/100000000), (1522001/25000000)]
    alternative := .zero
    polynomial := [(2320231308253138766263048901/33572495498057724000000000000), (133979019300049/369791300000000), (-3030534743911541478137254099/16786247749028862000000000000), (133979019300049/369791300000000), (-8381300796076221722537557099/33572495498057724000000000000)]
    bernstein := [(647234117122498540522411413322181/5371599279689235840000000000000000), (1316574679072774936873196867883889/10743198559378471680000000000000000), (8031742962416003711010106185859223/64459191356270830080000000000000000), (5442498387260294143354776103617929/42972794237513886720000000000000000), (11060678873822348714119353963642101/85945588475027773440000000000000000)]
    reserve := (60245941983/500000000000) }

theorem quarter_032_021_valid : quarter_032_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_021]
  · intro i; fin_cases i <;> norm_num [quarter_032_021]
  · norm_num [quarter_032_021]
  · norm_num [quarter_032_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_021]

def quarter_032_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (1928437/12500000), (1928437/12500000), (1440521/6250000), (1440521/6250000), (1440521/6250000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9765407/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (752397/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (232699/6250000), (1/100000000), (3504047/50000000), (1/100000000), (1/100000000), (6019177/100000000)]
    alternative := .zero
    polynomial := [(19582360172107149920797955069089/314109830224603006784000000000000), (18831972178859/46539800000000), (-32054474503781719639336869738911/157054915112301503392000000000000), (18831972178859/46539800000000), (-83691309179670589199471694546911/314109830224603006784000000000000)]
    bernstein := [(103589351819827458787429702290757861889/804121165374983697367040000000000000000), (13177763718773079193327996710081358527/100515145671872962170880000000000000000), (1256853109974351448999687705533489727/9423294906738090203520000000000000000), (106521585844547093727756346642562499/785274575561507516960000000000000000), (6768959155395437606782646702572041/49079660972594219810000000000000000)]
    reserve := (128823063339/1000000000000) }

theorem quarter_032_022_valid : quarter_032_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_022]
  · intro i; fin_cases i <;> norm_num [quarter_032_022]
  · norm_num [quarter_032_022]
  · norm_num [quarter_032_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_022]

def quarter_032_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (3166689/20000000), (3166689/20000000), (22777703/100000000), (22777703/100000000), (22777703/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (212557/2000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5948499/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (747789/20000000), (1/100000000), (54761/781250), (1/100000000), (1/100000000), (11897/200000)]
    alternative := .zero
    polynomial := [(60298835442067421670407777/1113550319508144000000000000), (224367304591/498526000000), (-128543692064857867402992223/556775159754072000000000000), (224367304591/498526000000), (-317386219571783156476392223/1113550319508144000000000000)]
    bernstein := [(24023445488482115310724714313/173992237423147500000000000000), (391380043639312556869639830109/2783875798770360000000000000000), (4780517762073871954047029778959/33406509585244320000000000000000), (51886957060565695016686626685633/356336102242606080000000000000000), (422249742233393483965867355543297/2850688817940848640000000000000000)]
    reserve := (27614387681/200000000000) }

theorem quarter_032_023_valid : quarter_032_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_023]
  · intro i; fin_cases i <;> norm_num [quarter_032_023]
  · norm_num [quarter_032_023]
  · norm_num [quarter_032_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_023]

def quarter_032_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (1624867/10000000), (1624867/10000000), (22500887/100000000), (22500887/100000000), (22500887/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5748411/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5876207/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1872307/50000000), (1/100000000), (7012993/100000000), (1/100000000), (1/100000000), (367263/6250000)]
    alternative := .zero
    polynomial := [(316588283410475888988486493/7133636042748569250000000000), (9340403336337/18723070000000), (-465750931742350150732621441/1783409010687142312500000000), (9340403336337/18723070000000), (-2179592010379876491918972257/7133636042748569250000000000)]
    bernstein := [(2708343670857486450218428393087423/18262108269436337280000000000000000), (21222532242977887459040760692779/140477755918741056000000000000000), (1960103680726522261716721431799/12741005769374188800000000000000), (12941257441443374699472065659/82633974069847680000000000000), (17120887293452096659857511631/107424166290801984000000000000)]
    reserve := (148303998141/1000000000000) }

theorem quarter_032_024_valid : quarter_032_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_024]
  · intro i; fin_cases i <;> norm_num [quarter_032_024]
  · norm_num [quarter_032_024]
  · norm_num [quarter_032_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_024]

def quarter_032_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (16671873/100000000), (16671873/100000000), (22218751/100000000), (22218751/100000000), (22218751/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1236887/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2901263/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3739711/100000000), (1/100000000), (7018977/100000000), (1/100000000), (1/100000000), (5802527/100000000)]
    alternative := .zero
    polynomial := [(294389180973060658990893905327/8959424409412947057000000000000), (20621222979351/37397110000000), (-1322823077884143005411193047173/4479712204706473528500000000000), (20621222979351/37397110000000), (-2940035336741346669813279999673/8959424409412947057000000000000)]
    bernstein := [(21531535525047957554330517285559/134918391106453790976000000000000), (1243374072838270578153723556696863/7645375496032381488640000000000000), (113996158673837080713009017362530653/688083794642914333977600000000000000), (128987675136799126317369341848777719/764537549603238148864000000000000000), (3939414176414236427744342477884522007/22936126488097144465920000000000000000)]
    reserve := (159589329137/1000000000000) }

theorem quarter_032_025_valid : quarter_032_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_025]
  · intro i; fin_cases i <;> norm_num [quarter_032_025]
  · norm_num [quarter_032_025]
  · norm_num [quarter_032_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_025]

def quarter_032_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (17101819/100000000), (17101819/100000000), (21932121/100000000), (21932121/100000000), (21932121/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3310121/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5727671/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3723869/100000000), (1/100000000), (3513729/50000000), (1/100000000), (1/100000000), (715959/12500000)]
    alternative := .zero
    polynomial := [(60550174620478887956393370971/3122694913628106153000000000000), (56609090210099/93096725000000), (-520957687469161756500036362029/1561347456814053076500000000000), (56609090210099/93096725000000), (-1102465549558802400956466095029/3122694913628106153000000000000)]
    bernstein := [(1375006712111167627277859149815611611/7994098978887951751680000000000000000), (350411024947919627291390421314754403/1998524744721987937920000000000000000), (267803996824696926052485473914920557/1498893558541490953440000000000000000), (22733519107847707375521064972116287/124907796545124246120000000000000000), (5787584288315266816546266024760451/31226949136281061530000000000000000)]
    reserve := (21500339121/125000000000) }

theorem quarter_032_026_valid : quarter_032_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_026]
  · intro i; fin_cases i <;> norm_num [quarter_032_026]
  · norm_num [quarter_032_026]
  · norm_num [quarter_032_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_026]

def quarter_032_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (3507467/20000000), (3507467/20000000), (21641777/100000000), (21641777/100000000), (21641777/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3527039/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5651847/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3696833/100000000), (1/100000000), (7038509/100000000), (1/100000000), (1/100000000), (5651847/100000000)]
    alternative := .zero
    polynomial := [(276154705889080683243968898739/73531073013769359229500000000000), (12370972900213/18484165000000), (-13849546966018952829060900423761/36765536506884679614750000000000), (12370972900213/18484165000000), (-27975248637926986341365769746261/73531073013769359229500000000000)]
    bernstein := [(136491055125627201125603283948173059/735310730137693592295000000000000000), (556678975268015641704778240700664889/2941242920550774369180000000000000000), (234786173583294603162550705012883633/1217066036089975601040000000000000000), (1321438850885498446655971386683739107/6722840961258912843840000000000000000), (185653506379710527841892554775817393/927288408449505219840000000000000000)]
    reserve := (92811820589/500000000000) }

theorem quarter_032_027_valid : quarter_032_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_027]
  · intro i; fin_cases i <;> norm_num [quarter_032_027]
  · norm_num [quarter_032_027]
  · norm_num [quarter_032_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_027]

def quarter_032_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, (17977319/100000000), (17977319/100000000), (10674227/50000000), (10674227/50000000), (10674227/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2993689/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1393811/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3658457/100000000), (1/100000000), (3526087/50000000), (1/100000000), (1/100000000), (1115049/20000000)]
    alternative := .zero
    polynomial := [(-164540975715895772112409301239/11507339281117604152800000000000), (53818502139791/73169140000000), (-2444853489003398199706630766239/5753669640558802076400000000000), (53818502139791/73169140000000), (-4725166002290900627300852231239/11507339281117604152800000000000)]
    bernstein := [(5907559523255326852230627277711291721/29458788559661066631168000000000000000), (1004110509949796984293909210605648073/4909798093276844438528000000000000000), (4606398582014293723456146722497958723/22094091419745799973376000000000000000), (260799495234460405026760363038985633/1227449523319211109632000000000000000), (398540679797977973427649221733186361/1841174284978816664448000000000000000)]
    reserve := (25067050497/125000000000) }

theorem quarter_032_028_valid : quarter_032_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_028]
  · intro i; fin_cases i <;> norm_num [quarter_032_028]
  · norm_num [quarter_032_028]
  · norm_num [quarter_032_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_028]

def quarter_032_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 0]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (85870743/100000000), 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (19590439/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-15187964623384429949/15672351200000000000), (85870743/19590439), (-32577730683384429949/7836175600000000000), (85870743/19590439), (-49967496743384429949/15672351200000000000)]
    bernstein := [(491174581772955537851651/2507576192000000000000000), (212375570386690762474719/1003030476800000000000000), (24881778954383083676659/109421506560000000000000), (38974676531101527083863/160484876288000000000000), (16569617307944372801779/64193950515200000000000)]
    reserve := (7835049373/40000000000) }

theorem quarter_032_029_valid : quarter_032_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_032_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_032_029]
  · intro i; fin_cases i <;> norm_num [quarter_032_029]
  · norm_num [quarter_032_029]
  · norm_num [quarter_032_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_032_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_032_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_032_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_032_029]

def quarterTable032 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 2, 0, 0, 0]
  rows := [quarter_032_000, quarter_032_001, quarter_032_002, quarter_032_003, quarter_032_004, quarter_032_005, quarter_032_006, quarter_032_007, quarter_032_008, quarter_032_009, quarter_032_010, quarter_032_011, quarter_032_012, quarter_032_013, quarter_032_014, quarter_032_015, quarter_032_016, quarter_032_017, quarter_032_018, quarter_032_019, quarter_032_020, quarter_032_021, quarter_032_022, quarter_032_023, quarter_032_024, quarter_032_025, quarter_032_026, quarter_032_027, quarter_032_028, quarter_032_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_032_000_valid
    · exact quarter_032_001_valid
    · exact quarter_032_002_valid
    · exact quarter_032_003_valid
    · exact quarter_032_004_valid
    · exact quarter_032_005_valid
    · exact quarter_032_006_valid
    · exact quarter_032_007_valid
    · exact quarter_032_008_valid
    · exact quarter_032_009_valid
    · exact quarter_032_010_valid
    · exact quarter_032_011_valid
    · exact quarter_032_012_valid
    · exact quarter_032_013_valid
    · exact quarter_032_014_valid
    · exact quarter_032_015_valid
    · exact quarter_032_016_valid
    · exact quarter_032_017_valid
    · exact quarter_032_018_valid
    · exact quarter_032_019_valid
    · exact quarter_032_020_valid
    · exact quarter_032_021_valid
    · exact quarter_032_022_valid
    · exact quarter_032_023_valid
    · exact quarter_032_024_valid
    · exact quarter_032_025_valid
    · exact quarter_032_026_valid
    · exact quarter_032_027_valid
    · exact quarter_032_028_valid
    · exact quarter_032_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
