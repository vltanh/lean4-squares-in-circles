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

def quarter_044_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_044_000_valid : quarter_044_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_000]
  · intro i; fin_cases i <;> norm_num [quarter_044_000]
  · norm_num [quarter_044_000]
  · norm_num [quarter_044_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_000]

def quarter_044_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_044_001_valid : quarter_044_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_001]
  · intro i; fin_cases i <;> norm_num [quarter_044_001]
  · norm_num [quarter_044_001]
  · norm_num [quarter_044_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_001]

def quarter_044_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_044_002_valid : quarter_044_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_002]
  · intro i; fin_cases i <;> norm_num [quarter_044_002]
  · norm_num [quarter_044_002]
  · norm_num [quarter_044_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_002]

def quarter_044_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_044_003_valid : quarter_044_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_003]
  · intro i; fin_cases i <;> norm_num [quarter_044_003]
  · norm_num [quarter_044_003]
  · norm_num [quarter_044_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_003]

def quarter_044_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_044_004_valid : quarter_044_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_004]
  · intro i; fin_cases i <;> norm_num [quarter_044_004]
  · norm_num [quarter_044_004]
  · norm_num [quarter_044_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_004]

def quarter_044_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_044_005_valid : quarter_044_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_005]
  · intro i; fin_cases i <;> norm_num [quarter_044_005]
  · norm_num [quarter_044_005]
  · norm_num [quarter_044_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_005]

def quarter_044_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_044_006_valid : quarter_044_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_006]
  · intro i; fin_cases i <;> norm_num [quarter_044_006]
  · norm_num [quarter_044_006]
  · norm_num [quarter_044_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_006]

def quarter_044_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_044_007_valid : quarter_044_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_007]
  · intro i; fin_cases i <;> norm_num [quarter_044_007]
  · norm_num [quarter_044_007]
  · norm_num [quarter_044_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_007]

def quarter_044_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_044_008_valid : quarter_044_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_008]
  · intro i; fin_cases i <;> norm_num [quarter_044_008]
  · norm_num [quarter_044_008]
  · norm_num [quarter_044_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_008]

def quarter_044_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1067647938911762121/3859681000000000000), (-13528061/3859681), (-8309344188911762121/1929840500000000000), (-13528061/3859681), (-15551040438911762121/3859681000000000000)]
    bernstein := [(100068034278401520636999/617548960000000000000000), (36328949888069554679293/247019584000000000000000), (265685575963521009711/2016486400000000000000), (917720443345976065601/7904626688000000000000), (63294346623912201551/632370135040000000000)]
    reserve := (100090663863/1000000000000) }

theorem quarter_044_009_valid : quarter_044_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_009]
  · intro i; fin_cases i <;> norm_num [quarter_044_009]
  · norm_num [quarter_044_009]
  · norm_num [quarter_044_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_009]

def quarter_044_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![(4424707/100000000), (4914861/50000000), (5481607/50000000), (23222217/100000000), (23222217/100000000), (23222217/100000000), (1023141/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11180291/100000000), 0, 0]] i.1) i.2
    mu := ![(766249/50000000), (2723809/100000000), (710949/100000000), (1622207/25000000), (1/100000000), (1/100000000), (3032293/50000000)]
    alternative := .zero
    polynomial := [(3495554332878997535960494404562963755997/60322187623410090371176281879000000000000), (-52763554334547/153249800000000), (-45308408048127459550060512232398713534003/30161093811705045185588140939500000000000), (-52763554334547/153249800000000), (-94112370429133916636081518869360390824003/60322187623410090371176281879000000000000)]
    bernstein := [(768958924873668501492833182615258206303493/9883187220219509206413522023055360000000000), (1605511635634897646796650317841808157702447/20589973375457310846694837548032000000000000), (90324381891685791241683039554369248615807939/1158186002369473735126584612076800000000000000), (12521861489567838232548269680572901543846319/160859166995760240989803418344000000000000000), (46776227977020686538266714473736363019195397/603221876234100903711762818790000000000000000)]
    reserve := (77543984759/1000000000000) }

theorem quarter_044_010_valid : quarter_044_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_010]
  · intro i; fin_cases i <;> norm_num [quarter_044_010]
  · norm_num [quarter_044_010]
  · norm_num [quarter_044_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_010]

def quarter_044_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![(4109193/100000000), (10191811/100000000), (2228021/20000000), (23307501/100000000), (23307501/100000000), (23307501/100000000), (1159097/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5361623/50000000), 0, 0]] i.1) i.2
    mu := ![(1444879/100000000), (555341/20000000), (146737/25000000), (6527471/100000000), (1/100000000), (1/100000000), (6086859/100000000)]
    alternative := .zero
    polynomial := [(15641794545005228496483417819977562692903/246215531114911358977556844933000000000000), (-24251840243311/72243950000000), (-233910487512854843159901763888022752215847/123107765557455679488778422466500000000000), (-24251840243311/72243950000000), (-483462769570714914816286945596023067124597/246215531114911358977556844933000000000000)]
    bernstein := [(192631922540984007191649509541174134998136003/2462155311149113589775568449330000000000000000), (773119052307573018109577687094011409066703309/9848621244596454359102273797320000000000000000), (9284923331463875035703520459971125969726492781/118183454935157452309227285567840000000000000000), (12358698687966317019512525846133230077242191081/157577939913543269745636380757120000000000000000), (49225854158094287249762555985636396343113394043/630311759654173078982545523028480000000000000000)]
    reserve := (39048814657/500000000000) }

theorem quarter_044_011_valid : quarter_044_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_011]
  · intro i; fin_cases i <;> norm_num [quarter_044_011]
  · norm_num [quarter_044_011]
  · norm_num [quarter_044_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_011]

def quarter_044_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![(474007/12500000), (10598443/100000000), (11326529/100000000), (11688849/50000000), (11688849/50000000), (11688849/50000000), (2074939/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2563767/25000000), 0, 0]] i.1) i.2
    mu := ![(337009/25000000), (2844269/100000000), (28321/6250000), (6563881/100000000), (1/100000000), (1/100000000), (6105191/100000000)]
    alternative := .zero
    polynomial := [(1873153301570464124060395907132711931049/27196982003868790182121948955275000000000), (-5538841898133/16850450000000), (-564483926038736064422716758017825758707341/217575856030950321456975591642200000000000), (-5538841898133/16850450000000), (-579469152451299777415199925274887454155733/217575856030950321456975591642200000000000)]
    bernstein := [(43995458715924279103893101165000823845397435227/556994191439232822929857514604032000000000000000), (762107938437486705686165808284484876961753421/9603348128262634878100991631104000000000000000), (33193206735919734193303016690158396120788711809/417745643579424617197393135953024000000000000000), (5520315949289779995244222771759344151301171801/69624273929904102866232189325504000000000000000), (2744841251395954476056934145756639787350187867/34812136964952051433116094662752000000000000000)]
    reserve := (78847249571/1000000000000) }

theorem quarter_044_012_valid : quarter_044_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_012]
  · intro i; fin_cases i <;> norm_num [quarter_044_012]
  · norm_num [quarter_044_012]
  · norm_num [quarter_044_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_012]

def quarter_044_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![(3470177/100000000), (1105391/10000000), (2880801/25000000), (11715783/50000000), (11715783/50000000), (11715783/50000000), (3658011/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9777269/100000000), 0, 0]] i.1) i.2
    mu := ![(620927/50000000), (2927503/100000000), (308521/100000000), (824739/12500000), (1/100000000), (1/100000000), (6119259/100000000)]
    alternative := .zero
    polynomial := [(69826176693199247113711929905459502480473/943445324108794269349791819267000000000000), (-40148630336227/124185400000000), (-1912246676683188059312668680136192348289527/471722662054397134674895909633500000000000), (-40148630336227/124185400000000), (-3894319530059575365739049290177844199059527/943445324108794269349791819267000000000000)]
    bernstein := [(12084692871688318359123668973094690802781698873/150951251857407083095966691082720000000000000000), (8107859849379903497460700987267583667955247691/100634167904938055397311127388480000000000000000), (146099208848234248091337822125550341500180591019/1811415022288884997151600292992640000000000000000), (32331791783938359105145227687784090097970246891/402536671619752221589244509553920000000000000000), (192164897302574216227665739661298231784838734073/2415220029718513329535467057323520000000000000000)]
    reserve := (19891034247/250000000000) }

theorem quarter_044_013_valid : quarter_044_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_013]
  · intro i; fin_cases i <;> norm_num [quarter_044_013]
  · norm_num [quarter_044_013]
  · norm_num [quarter_044_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_013]

def quarter_044_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (1560613/12500000), (791447/6250000), (3118831/12500000), (3118831/12500000), (3118831/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (369813/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6515973/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (16227/500000), (165071/100000000), (7070031/100000000), (1/100000000), (1/100000000), (3257987/50000000)]
    alternative := .zero
    polynomial := [(1490788060251665571537977664582871/18281250782668746852696000000000000), (-1560613/6250000), (-86054374928531617904723258902457129/9140625391334373426348000000000000), (-1560613/6250000), (-173599537917314901380984495469497129/18281250782668746852696000000000000)]
    bernstein := [(3833199192771439141643283355225284650071/46800002003631991942901760000000000000000), (2436178848044687490530800051603184471/29250001252269994964313600000000000000), (7343615907505316127385023572516123671/87750003756809984892940800000000000000), (1519318017879358592570004127230871/18281250782668746852696000000000000), (1490788060251665571537977664582871/18281250782668746852696000000000000)]
    reserve := (40773688791/500000000000) }

theorem quarter_044_014_valid : quarter_044_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_014]
  · intro i; fin_cases i <;> norm_num [quarter_044_014]
  · norm_num [quarter_044_014]
  · norm_num [quarter_044_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_014]

def quarter_044_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (16351/125000), (13076713/100000000), (12307081/50000000), (12307081/50000000), (12307081/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3874639/100000000), 0, 0], ![(326969/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6428099/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3400301/100000000), (661/800000), (3521369/50000000), (1/100000000), (1/100000000), (6428099/100000000)]
    alternative := .zero
    polynomial := [(17028328312580081620708534215065031/203503980051717978861164000000000000), (5346270119/10328125000), (-2089485609433577479096472515455718969/101751990025858989430582000000000000), (5346270119/10328125000), (-4195999547179735039813653565126502969/203503980051717978861164000000000000)]
    bernstein := [(17028328312580081620708534215065031/203503980051717978861164000000000000), (17686716964712046464884337387687431/203503980051717978861164000000000000), (85967021351417676804392202174031469831/976819104248246298533587200000000000000), (28316763609580116330925213260408473031/325606368082748766177862400000000000000), (43648084015675345860228271515501211516231/520970188932398025884579840000000000000000)]
    reserve := (83675652477/1000000000000) }

theorem quarter_044_015_valid : quarter_044_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_015]
  · intro i; fin_cases i <;> norm_num [quarter_044_015]
  · norm_num [quarter_044_015]
  · norm_num [quarter_044_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_015]

def quarter_044_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (6803389/50000000), (6784281/50000000), (24274887/100000000), (24274887/100000000), (24274887/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2015219/50000000), 0, 0], ![(40763/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1267899/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3537027/100000000), (85867/100000000), (351347/5000000), (1/100000000), (1/100000000), (792437/12500000)]
    alternative := .zero
    polynomial := [(10695630995352572181278204717053879/169120266910235645004702000000000000), (277326545807/171734000000), (-1807449270526273605046208110010026121/84560133455117822502351000000000000), (277326545807/171734000000), (-3625594172047899782273694424737106121/169120266910235645004702000000000000)]
    bernstein := [(39083043042053121571617590201231949546679/432947883290203251212037120000000000000000), (132566612640823985757430592778896407343/1414862363693474677163520000000000000000), (30814190602709901928699883232174490532437/324710912467652438409027840000000000000000), (564482784885346969477573798232638647631/6013165045697267377944960000000000000000), (144236700225897429689843270953369566887/1591720159155159011808960000000000000000)]
    reserve := (22567983671/250000000000) }

theorem quarter_044_016_valid : quarter_044_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_016]
  · intro i; fin_cases i <;> norm_num [quarter_044_016]
  · norm_num [quarter_044_016]
  · norm_num [quarter_044_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_016]

def quarter_044_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (707019/5000000), (7015169/50000000), (11971547/50000000), (11971547/50000000), (11971547/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (837699/20000000), 0, 0], ![(176067/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3126423/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1837867/50000000), (1113/1250000), (3506071/50000000), (1/100000000), (1/100000000), (6252847/100000000)]
    alternative := .zero
    polynomial := [(4552556854495815621769663593186239/358754815991095706496216000000000000), (41494238091/14840000000), (-3992241832302755695708224280174193761/179377407995547853248108000000000000), (41494238091/14840000000), (-7989036221460007207038218223941573761/358754815991095706496216000000000000)]
    bernstein := [(5571625729644877757690739691468369657439/57400770558575313039394560000000000000000), (11559646644885754554241792410900921236717/114801541117150626078789120000000000000000), (70265480654278814365274242772031118725653/688809246702903756472734720000000000000000), (46385233956361765318393525011037865296453/459206164468602504315156480000000000000000), (89712718342468249230432741779165596048559/918412328937205008630312960000000000000000)]
    reserve := (97065347301/1000000000000) }

theorem quarter_044_017_valid : quarter_044_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_017]
  · intro i; fin_cases i <;> norm_num [quarter_044_017]
  · norm_num [quarter_044_017]
  · norm_num [quarter_044_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_017]

def quarter_044_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (1835777/12500000), (7231521/50000000), (11808457/50000000), (11808457/50000000), (11808457/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (135943/3125000), 0, 0], ![(15941/625000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6167663/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1908811/50000000), (92161/100000000), (6997631/100000000), (1/100000000), (1/100000000), (6167663/100000000)]
    alternative := .zero
    polynomial := [(-1591810885660722364134845266791501/22330727085252137143286950000000000), (29264121157/7200078125), (-258924671906658095465740097544723501/11165363542626068571643475000000000), (29264121157/7200078125), (-516257532927655468567345349822655501/22330727085252137143286950000000000)]
    bernstein := [(5950326015810434104566147275631967115619/57166661338245471086814592000000000000000), (1542559115522455069720652923718478253073/14291665334561367771703648000000000000000), (390803319728609306725225888790885021391/3572916333640341942925912000000000000000), (96836481528457633204368287764539942797/893229083410085485731478000000000000000), (23449703720135078164813783212152834299/223307270852521371432869500000000000000)]
    reserve := (20817469051/200000000000) }

theorem quarter_044_018_valid : quarter_044_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_018]
  · intro i; fin_cases i <;> norm_num [quarter_044_018]
  · norm_num [quarter_044_018]
  · norm_num [quarter_044_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_018]

def quarter_044_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (15248507/100000000), (14867353/100000000), (11647357/50000000), (11647357/50000000), (11647357/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4516731/100000000), 0, 0], ![(1694017/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6083519/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (990947/25000000), (47623/50000000), (174569/2500000), (1/100000000), (1/100000000), (6083519/100000000)]
    alternative := .zero
    polynomial := [(-154120959554136964273373376357747201/801879577668533128337456000000000000), (25831230082619/4762300000000), (-9697306949998744309730507266318027201/400939788834266564168728000000000000), (25831230082619/4762300000000), (-19240492940443351655187641156278307201/801879577668533128337456000000000000)]
    bernstein := [(893064862362636145970982832908761042599/8018795776685331283374560000000000000000), (740655950869843575220207199780942148619/6415036621348265026699648000000000000000), (1801975630401492570267423967239421813913/15396087891235836064079155200000000000000), (7333897751811574123263360399715212719/63163437502505994109042688000000000000), (1138323570559680292292608497355062387/10106150000400959057446830080000000000)]
    reserve := (111371443697/1000000000000) }

theorem quarter_044_019_valid : quarter_044_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_019]
  · intro i; fin_cases i <;> norm_num [quarter_044_019]
  · norm_num [quarter_044_019]
  · norm_num [quarter_044_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_019]

def quarter_044_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (989449/6250000), (609747/4000000), (22975047/100000000), (22975047/100000000), (22975047/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (187573/4000000), 0, 0], ![(4272793/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1500009/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1028813/25000000), (98309/100000000), (3483463/50000000), (1/100000000), (1/100000000), (6000037/100000000)]
    alternative := .zero
    polynomial := [(-11969266887241621585574841420048261559/33823211006899659476982832000000000000), (4227710761057/614431250000), (-427109321673911431078645744898736261559/16911605503449829738491416000000000000), (4227710761057/614431250000), (-842249376460581240571716648377424261559/33823211006899659476982832000000000000)]
    bernstein := [(659187604822742692769211114578171604529/5541594891370440208708867194880000000000), (8540662517531311638735278508190556540479/69269936142130502608860839936000000000000), (324788243931837206228924038752936265811843/2597622605329893847832281497600000000000000), (268731557527590298597698778790679203286147/2164685504441578206526901248000000000000000), (652629026935734347985243375933868332548921/5411713761103945516317253120000000000000000)]
    reserve := (59476343701/500000000000) }

theorem quarter_044_020_valid : quarter_044_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_020]
  · intro i; fin_cases i <;> norm_num [quarter_044_020]
  · norm_num [quarter_044_020]
  · norm_num [quarter_044_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_020]

def quarter_044_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (4109491/25000000), (1949021/12500000), (22656623/100000000), (22656623/100000000), (22656623/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2434529/50000000), 0, 0], ![(5204897/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2958439/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2136491/50000000), (101361/100000000), (1389913/20000000), (1/100000000), (1/100000000), (5916879/100000000)]
    alternative := .zero
    polynomial := [(-3657968688948823748785563242909/6526144425802508652600000000000), (21389477377427/2534025000000), (-86168679587111664267459326858909/3263072212901254326300000000000), (21389477377427/2534025000000), (-168679390485274504786133090474909/6526144425802508652600000000000)]
    bernstein := [(132472620986684475968581992191067571/1044183108128401384416000000000000000), (274598371391834458361504136588901799/2088366216256802768832000000000000000), (1671444983377037335437735342737144593/12530197297540816612992000000000000000), (11415050234723164610509629701095087/86118194484816609024000000000000000), (22205529737011781771336332668556003/172236388969633218048000000000000000)]
    reserve := (63433616171/500000000000) }

theorem quarter_044_021_valid : quarter_044_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_021]
  · intro i; fin_cases i <;> norm_num [quarter_044_021]
  · norm_num [quarter_044_021]
  · norm_num [quarter_044_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_021]

def quarter_044_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (8536209/50000000), (7956391/50000000), (22338267/100000000), (22338267/100000000), (22338267/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1264247/25000000), 0, 0], ![(247389/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2916869/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2218953/50000000), (104413/100000000), (6930137/100000000), (1/100000000), (1/100000000), (5833739/100000000)]
    alternative := .zero
    polynomial := [(-15300194909293133807084503215892377977/18733610587899621679816254000000000000), (2111764208301/208826000000), (-259012842209925644874695767878864417977/9366805293949810839908127000000000000), (2111764208301/208826000000), (-502725489510558155942307032541836457977/18733610587899621679816254000000000000)]
    bernstein := [(6481626941659098252286207798863082184483623/47958043105023031500329610240000000000000000), (279910262042928834914241124351904788668963/1998251796042626312513733760000000000000000), (79896259638322647692007178936522918620289/562008317636988650394487620000000000000000), (2207000621759474261540910906731082194631/15611342156583018066513545000000000000000), (402953747212633267140627162982119101887/2927126654359315887471289687500000000000)]
    reserve := (5406081251/40000000000) }

theorem quarter_044_022_valid : quarter_044_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_022]
  · intro i; fin_cases i <;> norm_num [quarter_044_022]
  · norm_num [quarter_044_022]
  · norm_num [quarter_044_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_022]

def quarter_044_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (8869011/50000000), (1620527/10000000), (22018903/100000000), (22018903/100000000), (22018903/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2627073/50000000), 0, 0], ![(144259/2000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1150067/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4610927/100000000), (26869/25000000), (172703/2500000), (1/100000000), (1/100000000), (89849/1562500)]
    alternative := .zero
    polynomial := [(-1020150364793100951868817392002433/904677824612367279464000000000000), (1279434657849/107476000000), (-13118159699148202543114033517802433/452338912306183639732000000000000), (1279434657849/107476000000), (-25216169033503304134359249643602433/904677824612367279464000000000000)]
    bernstein := [(20333263324261331209768297661188823/141355910095682387416250000000000000), (337215561220260345448841851539689539/2261694561530918198660000000000000000), (4108479332074860014853100653509077889/27140334738371018383920000000000000000), (43611332267496978209982825291003316543/289496903875957529428480000000000000000), (340090750822030196228140950491465323487/2315975231007660235427840000000000000000)]
    reserve := (143844451289/1000000000000) }

theorem quarter_044_023_valid : quarter_044_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_023]
  · intro i; fin_cases i <;> norm_num [quarter_044_023]
  · norm_num [quarter_044_023]
  · norm_num [quarter_044_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_023]

def quarter_044_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (288097/1562500), (16469211/100000000), (21697527/100000000), (21697527/100000000), (21697527/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5461547/100000000), 0, 0], ![(518157/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2833203/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4792937/100000000), (110559/100000000), (6883003/100000000), (1/100000000), (1/100000000), (5666407/100000000)]
    alternative := .zero
    polynomial := [(-123916360715537785117372946266585526363/82668781783276365034616172000000000000), (199039302972/14395703125), (-1259211932518029109139169169378213046363/41334390891638182517308086000000000000), (199039302972/14395703125), (-2394507504320520433160965392489840566363/82668781783276365034616172000000000000)]
    bernstein := [(32375919063131146934263623540206912966322757/211632081365187494488617400320000000000000000), (3356322275662000644281432265456833606821693/21163208136518749448861740032000000000000000), (1022721967364784667979908238663123991257263/6348962440955624834658522009600000000000000), (33948326995576091238131114899113437799101/211632081365187494488617400320000000000000), (3312349196519198967310331797650289441093/21163208136518749448861740032000000000000)]
    reserve := (1195172613/7812500000) }

theorem quarter_044_024_valid : quarter_044_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_024]
  · intro i; fin_cases i <;> norm_num [quarter_044_024]
  · norm_num [quarter_044_024]
  · norm_num [quarter_044_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_024]

def quarter_044_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (19176407/100000000), (16704021/100000000), (21373191/100000000), (21373191/100000000), (21373191/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5680207/100000000), 0, 0], ![(2354653/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (697713/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4984829/100000000), (11367/10000000), (171357/2500000), (1/100000000), (1/100000000), (1116341/20000000)]
    alternative := .zero
    polynomial := [(-27993905640917799953622215998427161/14452187489772673810788000000000000), (107253644351/6750000000), (-231625891834590337272526088322581161/7226093744886336905394000000000000), (107253644351/6750000000), (-435257878028262874591429960646735161/14452187489772673810788000000000000)]
    bernstein := [(601590012419428338391556850171682471/3699759997381804495561728000000000000), (693081228128458079680268147744814997/4110844441535338328401920000000000000), (190152893584209116206845782341423709021/1109927999214541348668518400000000000000), (23392370794098981625983322303651011487/137028148051177944280064000000000000000), (685307841259695126265813889643802116511/4110844441535338328401920000000000000000)]
    reserve := (162602442549/1000000000000) }

theorem quarter_044_025_valid : quarter_044_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_025]
  · intro i; fin_cases i <;> norm_num [quarter_044_025]
  · norm_num [quarter_044_025]
  · norm_num [quarter_044_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_025]

def quarter_044_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (9978043/50000000), (105681/625000), (4208997/20000000), (4208997/20000000), (4208997/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2955577/50000000), 0, 0], ![(10598701/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (686999/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5187503/100000000), (116819/100000000), (1705361/25000000), (1/100000000), (1/100000000), (686999/12500000)]
    alternative := .zero
    polynomial := [(-1738598349370312136611098353688143743/709976995233981122436523000000000000), (105754294322143/5840950000000), (-11992592387124860023041547766505743743/354988497616990561218261500000000000), (105754294322143/5840950000000), (-22246586424879407909471997179323343743/709976995233981122436523000000000000)]
    bernstein := [(313966703084916390667922783399118533689137/1817541107798991673437498880000000000000000), (81405700949171338722191340681273050972601/454385276949747918359374720000000000000000), (62066068461333315574695105550844199231719/340788957712310938769531040000000000000000), (5156862823350355446452987535647648111629/28399079809359244897460920000000000000000), (1259941240353222833519338386729900389417/7099769952339811224365230000000000000000)]
    reserve := (17274255957/100000000000) }

theorem quarter_044_026_valid : quarter_044_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_026]
  · intro i; fin_cases i <;> norm_num [quarter_044_026]
  · norm_num [quarter_044_026]
  · norm_num [quarter_044_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_026]

def quarter_044_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (20780791/100000000), (17083141/100000000), (20712023/100000000), (20712023/100000000), (20712023/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3077719/50000000), 0, 0], ![(11832479/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5409037/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2700941/50000000), (120013/100000000), (6783983/100000000), (1/100000000), (1/100000000), (2704519/50000000)]
    alternative := .zero
    polynomial := [(-4523242654036506708559139827735728081/1486819286505370588458060250000000000), (245888273110889/12001300000000), (-26513468931055923707208328489484186831/743409643252685294229030125000000000), (245888273110889/12001300000000), (-48503695208075340705857517151232645581/1486819286505370588458060250000000000)]
    bernstein := [(2727402476764377161471909907177502877139/14868192865053705884580602500000000000000), (11317861502551057127240398142532798847319/59472771460214823538322410000000000000000), (138123229857832983066144574225081978581697/713673257522577882459868920000000000000000), (183719971366456065932057496464484869436879/951564343363437176613158560000000000000000), (718685193318823592692320698962939132096259/3806257373453748706452634240000000000000000)]
    reserve := (183438734049/1000000000000) }

theorem quarter_044_027_valid : quarter_044_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_027]
  · intro i; fin_cases i <;> norm_num [quarter_044_027]
  · norm_num [quarter_044_027]
  · norm_num [quarter_044_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_027]

def quarter_044_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (21654179/100000000), (269149/1562500), (5093357/25000000), (5093357/25000000), (5093357/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6414143/100000000), 0, 0], ![(820119/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1330153/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1407229/25000000), (123261/100000000), (52667/781250), (1/100000000), (1/100000000), (1330153/25000000)]
    alternative := .zero
    polynomial := [(-724413353205115310751639663562269407/194424336293084917347504000000000000), (5919667875767/256793750000), (-3666188060313258857935027888120349407/97212168146542458673752000000000000), (5919667875767/256793750000), (-2202654255807134135039472037559476469/64808112097694972449168000000000000)]
    bernstein := [(96920319096096634255217207248226707681073/497726300910297388409610240000000000000000), (4571810944416875887480780421211376700377/22623922768649881291345920000000000000000), (76749460564675741458165648638022866461499/373294725682723041307207680000000000000000), (1160654030080663687748793581057311296817/5655980692162470322836480000000000000000), (6246685632550544303933531426890775519393/31107893806893586775600640000000000000000)]
    reserve := (97363067733/500000000000) }

theorem quarter_044_028_valid : quarter_044_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_028]
  · intro i; fin_cases i <;> norm_num [quarter_044_028]
  · norm_num [quarter_044_028]
  · norm_num [quarter_044_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_028]

def quarter_044_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 0]
    lambda := ![0, (11290031/50000000), (17334977/100000000), (125177/625000), (125177/625000), (125177/625000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6688397/100000000), 0, 0], ![(7234601/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1046097/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1173919/20000000), (126571/100000000), (209159/3125000), (1/100000000), (1/100000000), (2615243/50000000)]
    alternative := .zero
    polynomial := [(-62386849797067678113611734612619171/13834169016468917226232000000000000), (81678869562631/3164275000000), (-276299894935598766962914202305659171/6917084508234458613116000000000000), (81678869562631/3164275000000), (-490212940074129855812216669998699171/13834169016468917226232000000000000)]
    bernstein := [(457387009835364416708864136835045227229/2213467042635026756197120000000000000000), (189931381870719943044893227994791952001/885386817054010702478848000000000000000), (77328644186549218486349150148576249957/354154726821604280991539200000000000000), (30886910388815995090917484460883533577/141661890728641712396615680000000000000), (12096100169433200142549235911798037741/56664756291456684958646272000000000000)]
    reserve := (103319137133/500000000000) }

theorem quarter_044_029_valid : quarter_044_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_044_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_044_029]
  · intro i; fin_cases i <;> norm_num [quarter_044_029]
  · norm_num [quarter_044_029]
  · norm_num [quarter_044_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_044_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_044_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_044_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_044_029]

def quarterTable044 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 2, 0, 0, 0]
  rows := [quarter_044_000, quarter_044_001, quarter_044_002, quarter_044_003, quarter_044_004, quarter_044_005, quarter_044_006, quarter_044_007, quarter_044_008, quarter_044_009, quarter_044_010, quarter_044_011, quarter_044_012, quarter_044_013, quarter_044_014, quarter_044_015, quarter_044_016, quarter_044_017, quarter_044_018, quarter_044_019, quarter_044_020, quarter_044_021, quarter_044_022, quarter_044_023, quarter_044_024, quarter_044_025, quarter_044_026, quarter_044_027, quarter_044_028, quarter_044_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_044_000_valid
    · exact quarter_044_001_valid
    · exact quarter_044_002_valid
    · exact quarter_044_003_valid
    · exact quarter_044_004_valid
    · exact quarter_044_005_valid
    · exact quarter_044_006_valid
    · exact quarter_044_007_valid
    · exact quarter_044_008_valid
    · exact quarter_044_009_valid
    · exact quarter_044_010_valid
    · exact quarter_044_011_valid
    · exact quarter_044_012_valid
    · exact quarter_044_013_valid
    · exact quarter_044_014_valid
    · exact quarter_044_015_valid
    · exact quarter_044_016_valid
    · exact quarter_044_017_valid
    · exact quarter_044_018_valid
    · exact quarter_044_019_valid
    · exact quarter_044_020_valid
    · exact quarter_044_021_valid
    · exact quarter_044_022_valid
    · exact quarter_044_023_valid
    · exact quarter_044_024_valid
    · exact quarter_044_025_valid
    · exact quarter_044_026_valid
    · exact quarter_044_027_valid
    · exact quarter_044_028_valid
    · exact quarter_044_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
