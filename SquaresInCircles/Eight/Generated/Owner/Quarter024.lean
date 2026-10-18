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

def quarter_024_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_024_000_valid : quarter_024_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_000]
  · intro i; fin_cases i <;> norm_num [quarter_024_000]
  · norm_num [quarter_024_000]
  · norm_num [quarter_024_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_000]

def quarter_024_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_024_001_valid : quarter_024_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_001]
  · intro i; fin_cases i <;> norm_num [quarter_024_001]
  · norm_num [quarter_024_001]
  · norm_num [quarter_024_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_001]

def quarter_024_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_024_002_valid : quarter_024_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_002]
  · intro i; fin_cases i <;> norm_num [quarter_024_002]
  · norm_num [quarter_024_002]
  · norm_num [quarter_024_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_002]

def quarter_024_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_024_003_valid : quarter_024_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_003]
  · intro i; fin_cases i <;> norm_num [quarter_024_003]
  · norm_num [quarter_024_003]
  · norm_num [quarter_024_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_003]

def quarter_024_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_024_004_valid : quarter_024_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_004]
  · intro i; fin_cases i <;> norm_num [quarter_024_004]
  · norm_num [quarter_024_004]
  · norm_num [quarter_024_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_004]

def quarter_024_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_024_005_valid : quarter_024_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_005]
  · intro i; fin_cases i <;> norm_num [quarter_024_005]
  · norm_num [quarter_024_005]
  · norm_num [quarter_024_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_005]

def quarter_024_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_024_006_valid : quarter_024_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_006]
  · intro i; fin_cases i <;> norm_num [quarter_024_006]
  · norm_num [quarter_024_006]
  · norm_num [quarter_024_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_006]

def quarter_024_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_024_007_valid : quarter_024_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_007]
  · intro i; fin_cases i <;> norm_num [quarter_024_007]
  · norm_num [quarter_024_007]
  · norm_num [quarter_024_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_007]

def quarter_024_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_024_008_valid : quarter_024_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_008]
  · intro i; fin_cases i <;> norm_num [quarter_024_008]
  · norm_num [quarter_024_008]
  · norm_num [quarter_024_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_008]

def quarter_024_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![(3126827/100000000), (3033959/12500000), (3033959/12500000), (3033959/12500000), (5148471/50000000), (5148471/50000000), (3464273/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1230673/20000000), 0, 0]] i.1) i.2
    mu := ![(512347/50000000), (6409437/100000000), (1/100000000), (1/100000000), (3331021/50000000), (1/100000000), (2689093/100000000)]
    alternative := .zero
    polynomial := [(4568394912888390852813968276399611/56895344371793967670851000000000000), (-600540515831207219/1270350413400000000), (-11212066509632979533691046115550389/28447672185896983835425500000000000), (-600540515831207219/1270350413400000000), (-26992527932154349920196060507500389/56895344371793967670851000000000000)]
    bernstein := [(1308069627646517340067601370789816327691/9103255099487034827336160000000000000000), (171526569347018104812218710894093227179/1213767346598271310311488000000000000000), (607006160375966688550002797529123217753/4369562447753776717121356800000000000000), (15904046484274316055148528206355624709/116521665273434045789902848000000000000), (1249447206263982289931233320090922259/9321733221874723663192227840000000000)]
    reserve := (26807186529/200000000000) }

theorem quarter_024_009_valid : quarter_024_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_009]
  · intro i; fin_cases i <;> norm_num [quarter_024_009]
  · norm_num [quarter_024_009]
  · norm_num [quarter_024_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_009]

def quarter_024_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![(3594429/100000000), (23902569/100000000), (23902569/100000000), (23902569/100000000), (10382767/100000000), (10382767/100000000), (3932329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1328767/20000000), 0, 0]] i.1) i.2
    mu := ![(603071/50000000), (1581207/25000000), (1/100000000), (1/100000000), (1316979/20000000), (1/100000000), (2711507/100000000)]
    alternative := .zero
    polynomial := [(3719916100917966149482848400237031/45403098268307573908973880000000000), (-58409893044956789649/127144011559600000000), (-8917989990905213374354643944405369/22701549134153786954486940000000000), (-58409893044956789649/127144011559600000000), (-21555896082728392898192136289047769/45403098268307573908973880000000000)]
    bernstein := [(996798433714707415955057562047639519/7438843620279512909246280499200000000), (75553776576195635336252785691746933/573984847243789576330731520000000000), (112658209828640757135654386786668167197/871739486751505419052298496000000000000), (568643494833793689683692525819822481/4484256619092106065083840000000000000), (559017312248035371192598060753752331/4495356264188868703858800000000000000)]
    reserve := (7772149739/62500000000) }

theorem quarter_024_010_valid : quarter_024_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_010]
  · intro i; fin_cases i <;> norm_num [quarter_024_010]
  · norm_num [quarter_024_010]
  · norm_num [quarter_024_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_010]

def quarter_024_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![(50621/1250000), (5885493/25000000), (5885493/25000000), (5885493/25000000), (2620701/25000000), (2620701/25000000), (1089699/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1774107/25000000), 0, 0]] i.1) i.2
    mu := ![(1387053/100000000), (1558113/25000000), (1/100000000), (1/100000000), (1302333/20000000), (1/100000000), (85551/3125000)]
    alternative := .zero
    polynomial := [(74307424269151739568423879731527/891816244157847112658100000000000), (-1336124881292762063/3001646265262500000), (-174516156999642737129011234476473/445908122078923556329050000000000), (-1336124881292762063/3001646265262500000), (-423339738268437213826446348684473/891816244157847112658100000000000)]
    bernstein := [(1108692201900475107061951431786730927/8918162441578471126581000000000000000), (4350422756540734788457240829728675481/35672649766313884506324000000000000000), (51180153452577889228784602131088586329/428071797195766614075888000000000000000), (66856053320768657520013088210434526029/570762396261022152101184000000000000000), (261814541297974274999082402598906775287/2283049585044088608404736000000000000000)]
    reserve := (5733877683/50000000000) }

theorem quarter_024_011_valid : quarter_024_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_011]
  · intro i; fin_cases i <;> norm_num [quarter_024_011]
  · norm_num [quarter_024_011]
  · norm_num [quarter_024_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_011]

def quarter_024_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![(719/16000), (927663/4000000), (927663/4000000), (927663/4000000), (662281/6250000), (662281/6250000), (4738533/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1501171/20000000), 0, 0]] i.1) i.2
    mu := ![(391447/25000000), (3066533/50000000), (1/100000000), (1/100000000), (644277/10000000), (1/100000000), (2767323/100000000)]
    alternative := .zero
    polynomial := [(803070221935308660436419869786437/9511972236250760200138760000000000), (-4128353803035864777/9603081146008000000), (-1853633896579543814283351948074363/4755986118125380100069380000000000), (-4128353803035864777/9603081146008000000), (-4510338015094396289003123765935163/9511972236250760200138760000000000)]
    bernstein := [(2791649843157648739831489833578156517397/24350648924801946112355225600000000000000), (1367069002878668268153487844061529329599/12175324462400973056177612800000000000000), (2006881741305860517247213359172069968199/18262986693601459584266419200000000000000), (327091928782659533376006754296465633511/3043831115600243264044403200000000000000), (159799091258243952565914573743790794437/1521915557800121632022201600000000000000)]
    reserve := (20999731613/200000000000) }

theorem quarter_024_012_valid : quarter_024_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_012]
  · intro i; fin_cases i <;> norm_num [quarter_024_012]
  · norm_num [quarter_024_012]
  · norm_num [quarter_024_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_012]

def quarter_024_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (12703313/50000000), (12703313/50000000), (12703313/50000000), (11890061/100000000), (11890061/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5629873/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3105143/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6644931/100000000), (1/100000000), (1/100000000), (7087979/100000000), (1/100000000), (3105143/100000000)]
    alternative := .zero
    polynomial := [(52996195533222638807899987649899/584998152498008484828000000000000), (-97307237843557/332246550000000), (-32926735052788795940560916045367/97499692083001414138000000000000), (-97307237843557/332246550000000), (-250556605849955414451265483922101/584998152498008484828000000000000)]
    bernstein := [(9774201339857899677642025252677437099/93599704399681357572480000000000000000), (19242930801903853300227374775858436699/187199408799362715144960000000000000000), (12621069973406428816212688793961709833/124799605866241810096640000000000000000), (74457094512607307749606882307381355499/748797635197450860579840000000000000000), (146326031682186648039130602812954794699/1497595270394901721159680000000000000000)]
    reserve := (9770732759/100000000000) }

theorem quarter_024_013_valid : quarter_024_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_013]
  · intro i; fin_cases i <;> norm_num [quarter_024_013]
  · norm_num [quarter_024_013]
  · norm_num [quarter_024_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_013]

def quarter_024_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (12650513/50000000), (12650513/50000000), (12650513/50000000), (12048461/100000000), (12048461/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6868967/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3146509/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6625101/100000000), (1/100000000), (1/100000000), (7080937/100000000), (1/100000000), (314651/10000000)]
    alternative := .zero
    polynomial := [(5423335396513641856848165066949/59043533683314326748000000000000), (-2306454180673/9464430000000), (-3300832316147352858399541189017/9840588947219054458000000000000), (-2306454180673/9464430000000), (-25228329293397759007245412201051/59043533683314326748000000000000)]
    bernstein := [(14773480188290132644965499057874675749/151151446229284676474880000000000000000), (3033062070631010389715692311481283/31489884631100974265600000000000000), (8961810565309776269139838621929383/94469653893302922796800000000000000), (1837755003338307353432843986483/19681177894438108916000000000000), (5423335396513641856848165066949/59043533683314326748000000000000)]
    reserve := (22963291059/250000000000) }

theorem quarter_024_014_valid : quarter_024_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_014]
  · intro i; fin_cases i <;> norm_num [quarter_024_014]
  · norm_num [quarter_024_014]
  · norm_num [quarter_024_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_014]

def quarter_024_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (25316541/100000000), (25316541/100000000), (25316541/100000000), (3006297/25000000), (3006297/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (31719/390625), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (196277/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3310181/50000000), (1/100000000), (1/100000000), (7081951/100000000), (1/100000000), (196277/6250000)]
    alternative := .zero
    polynomial := [(6606852530226291440753686673/71894239898981613859375000000), (803015363979/2586078906250), (-48609550173214805654472736183/143788479797963227718750000000), (803015363979/2586078906250), (-61823255233667388535980109529/143788479797963227718750000000)]
    bernstein := [(6606852530226291440753686673/71894239898981613859375000000), (3373189434221389970277032899/35947119949490806929687500000), (132160770417684739249150869785417/1380369406060446986100000000000000), (44914710442384495565335602687517/460123135353482328700000000000000), (36608533195029090348932392740557671/368098508282785862960000000000000000)]
    reserve := (45948413527/500000000000) }

theorem quarter_024_015_valid : quarter_024_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_015]
  · intro i; fin_cases i <;> norm_num [quarter_024_015]
  · norm_num [quarter_024_015]
  · norm_num [quarter_024_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_015]

def quarter_024_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (12726637/50000000), (12726637/50000000), (12726637/50000000), (11820089/100000000), (11820089/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2349093/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3086869/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6630589/100000000), (1/100000000), (1/100000000), (886399/12500000), (1/100000000), (308687/10000000)]
    alternative := .zero
    polynomial := [(65827137447936353727047449961/725704302031891422800000000000), (4270864841463/11840337500000), (-125432489957729181655107208439/362852151015945711400000000000), (4270864841463/11840337500000), (-316692117363394717037261866839/725704302031891422800000000000)]
    bernstein := [(184879196631536138831067884253528361/1857803013201642042368000000000000000), (94437139805035230888743060688919561/928901506600821021184000000000000000), (20657933985738613530103010194096669/199050322843033075968000000000000000), (24585101294885056150554814645926361/232225376650205255296000000000000000), (12531033959474236501009066362261961/116112688325102627648000000000000000)]
    reserve := (49757481099/500000000000) }

theorem quarter_024_016_valid : quarter_024_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_016]
  · intro i; fin_cases i <;> norm_num [quarter_024_016]
  · norm_num [quarter_024_016]
  · norm_num [quarter_024_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_016]

def quarter_024_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (25599793/100000000), (25599793/100000000), (25599793/100000000), (1160031/10000000), (1160031/10000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1066417/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3029473/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1656609/25000000), (1/100000000), (1/100000000), (3550843/50000000), (1/100000000), (3029473/100000000)]
    alternative := .zero
    polynomial := [(6290309671975638912158836394149/71281784661552756204000000000000), (27300054451681/66264360000000), (-4230619617304515456123596491117/11880297443592126034000000000000), (27300054451681/66264360000000), (-31674027375802731648900415340851/71281784661552756204000000000000)]
    bernstein := [(1231789074994553643487786872787818349/11405085545848440992640000000000000000), (17855635292548481926818160014606067/161774263061680014080000000000000000), (5141991754826361995502800805333760741/45620342183393763970560000000000000000), (3498214458578653027944142120935268341/30413561455595842647040000000000000000), (21405314456093501133859490695318322269/182481368733575055882240000000000000000)]
    reserve := (108003492831/1000000000000) }

theorem quarter_024_017_valid : quarter_024_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_017]
  · intro i; fin_cases i <;> norm_num [quarter_024_017]
  · norm_num [quarter_024_017]
  · norm_num [quarter_024_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_017]

def quarter_024_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (25755647/100000000), (25755647/100000000), (25755647/100000000), (1136653/10000000), (1136653/10000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2979961/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (148421/5000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1651927/25000000), (1/100000000), (1/100000000), (88919/1250000), (1/100000000), (2968421/100000000)]
    alternative := .zero
    polynomial := [(147301538449725843313574942869/1744098096632737492000000000000), (76750823589767/165192700000000), (-322160515852936725186740830131/872049048316368746000000000000), (76750823589767/165192700000000), (-791622570155599293687056603131/1744098096632737492000000000000)]
    bernstein := [(524208536868857749436562677117613589/4464891127379807979520000000000000000), (133956224401917475870332182770275063/1116222781844951994880000000000000000), (34206933420877683885315621781559721/279055695461237998720000000000000000), (8729255885974163828363983206758907/69763923865309499680000000000000000), (2226227188845234359220072539260669/17440980966327374920000000000000000)]
    reserve := (58703395213/500000000000) }

theorem quarter_024_018_valid : quarter_024_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_018]
  · intro i; fin_cases i <;> norm_num [quarter_024_018]
  · norm_num [quarter_024_018]
  · norm_num [quarter_024_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_018]

def quarter_024_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (25920337/100000000), (25920337/100000000), (25920337/100000000), (2223899/20000000), (2223899/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3289947/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1451953/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1314859/20000000), (1/100000000), (1/100000000), (1781693/25000000), (1/100000000), (1451953/50000000)]
    alternative := .zero
    polynomial := [(16853331329332798508485901753/212590881565008656937500000000), (85276534952139/164357375000000), (-82017003457267181937311246019/212590881565008656937500000000), (85276534952139/164357375000000), (-24717583696649995111449286943/53147720391252164234375000000)]
    bernstein := [(4244346432260056817332733897427/33217325244532602646484375000000), (6942223971493068017584220411149/53147720391252164234375000000000), (6982956351552969563359438707387/52330063154463669400000000000000), (14828639450609048696098574536997/108846531361284432352000000000000), (93108105515259300521147354421/669824808377134968320000000000)]
    reserve := (15971885157/125000000000) }

theorem quarter_024_019_valid : quarter_024_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_019]
  · intro i; fin_cases i <;> norm_num [quarter_024_019]
  · norm_num [quarter_024_019]
  · norm_num [quarter_024_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_019]

def quarter_024_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (2609333/10000000), (2609333/10000000), (2609333/10000000), (2172001/20000000), (2172001/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (14380439/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2836139/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (203943/3125000), (1/100000000), (1/100000000), (1428303/20000000), (1/100000000), (2836139/100000000)]
    alternative := .zero
    polynomial := [(2559819058390696976824978431601/35248884584058339456000000000000), (37523354037187/65261760000000), (-7144462294616452424911989298399/17624442292029169728000000000000), (37523354037187/65261760000000), (-5616247882541200608882985676133/11749628194686113152000000000000)]
    bernstein := [(803699574037563952003341320504569/5775177250252118336471040000000000), (10270412279782189953639662929574519/72189715628151479205888000000000000), (393480598528366924620635419136626523/2707114336055680470220800000000000000), (334798451842576165993896647225723867/2255928613379733725184000000000000000), (854116955935572939340041224676386881/5639821533449334312960000000000000000)]
    reserve := (139164486077/1000000000000) }

theorem quarter_024_020_valid : quarter_024_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_020]
  · intro i; fin_cases i <;> norm_num [quarter_024_020]
  · norm_num [quarter_024_020]
  · norm_num [quarter_024_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_020]

def quarter_024_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (26274061/100000000), (26274061/100000000), (26274061/100000000), (10588909/100000000), (10588909/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (7789159/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2765341/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (807927/12500000), (1/100000000), (1/100000000), (7157811/100000000), (1/100000000), (2765341/100000000)]
    alternative := .zero
    polynomial := [(915411175974612017668249857457/14215054170780910024000000000000), (204652838704699/323170800000000), (-9133524975733661633279484539129/21322581256171365036000000000000), (204652838704699/323170800000000), (-21013283479391159319563718650629/42645162512342730072000000000000)]
    bernstein := [(344884592816804317256267848554443417/2274408667324945603840000000000000000), (2115437137059960204717920999830238719/13646452003949673623040000000000000000), (12967610047640145579963635232473083033/81878712023698041738240000000000000000), (2942425555603985743745436154390763853/18195269338599564830720000000000000000), (18016839870803133141694681545829372571/109171616031597388984320000000000000000)]
    reserve := (151637037693/1000000000000) }

theorem quarter_024_021_valid : quarter_024_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_021]
  · intro i; fin_cases i <;> norm_num [quarter_024_021]
  · norm_num [quarter_024_021]
  · norm_num [quarter_024_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_021]

def quarter_024_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (26461941/100000000), (26461941/100000000), (26461941/100000000), (10307089/100000000), (10307089/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (16750069/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1345871/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6386173/100000000), (1/100000000), (1/100000000), (3587857/50000000), (1/100000000), (2691743/100000000)]
    alternative := .zero
    polynomial := [(13442993897114095556520530288657/246700135567163151692000000000000), (443239337623929/638617300000000), (-56119273759369032453232138110343/123350067783581575846000000000000), (443239337623929/638617300000000), (-125681541415852160462984806509343/246700135567163151692000000000000)]
    bernstein := [(104370777134064600388963391371946405057/631552347051937668331520000000000000000), (13336304010787171632477330769970382351/78944043381492208541440000000000000000), (1277319959230579793683676151497706701/7401004067014894550760000000000000000), (8360443428241083953363838403928499/47442333762915990710000000000000000), (533258986584040057752526893253541/2965145860182249419375000000000000)]
    reserve := (82630345387/500000000000) }

theorem quarter_024_022_valid : quarter_024_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_022]
  · intro i; fin_cases i <;> norm_num [quarter_024_022]
  · norm_num [quarter_024_022]
  · norm_num [quarter_024_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_022]

def quarter_024_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (13328183/50000000), (13328183/50000000), (13328183/50000000), (10015451/100000000), (10015451/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1118281/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (130779/5000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6294693/100000000), (1/100000000), (1/100000000), (1439053/20000000), (1/100000000), (130779/5000000)]
    alternative := .zero
    polynomial := [(1535436335930785518972777521/35898426699624027000000000000), (14904653813423/19670915625000), (-8713785668767971940202018479/17949213349812013500000000000), (14904653813423/19670915625000), (-18963007673466729399376814479/35898426699624027000000000000)]
    bernstein := [(1010256648738051963287895853049/5609129171816254218750000000000), (1501973341081470703394118473687/8158733340823642500000000000000), (28933428931610397583993453748801/153850400141245830000000000000000), (200524849260020365870172212355219/1044317867625426240000000000000000), (18008184608470331024155197430606481/91899972351037509120000000000000000)]
    reserve := (22513669631/125000000000) }

theorem quarter_024_023_valid : quarter_024_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_023]
  · intro i; fin_cases i <;> norm_num [quarter_024_023]
  · norm_num [quarter_024_023]
  · norm_num [quarter_024_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_023]

def quarter_024_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (13428361/50000000), (13428361/50000000), (13428361/50000000), (4857459/50000000), (4857459/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (19002599/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1268547/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6189309/100000000), (1/100000000), (1/100000000), (1443299/20000000), (1/100000000), (507419/20000000)]
    alternative := .zero
    polynomial := [(47942566914702295399002763517/1648285762352985756000000000000), (36453394187177/44209350000000), (-142903614766981243118883498161/274714293725497626000000000000), (36453394187177/44209350000000), (-905364255516589754112303752483/1648285762352985756000000000000)]
    bernstein := [(828153331419580783602167604716685437/4219611551623643535360000000000000000), (6510526018973119685999814188109001/32458550397104950272000000000000000), (8645260940061417736659941455442461/42196115516236435353600000000000000), (67894762224207057488081719325257/324585503971049502720000000000000), (5298178615906484023013330543789/24821244421315550208000000000000)]
    reserve := (98131465573/500000000000) }

theorem quarter_024_024_valid : quarter_024_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_024]
  · intro i; fin_cases i <;> norm_num [quarter_024_024]
  · norm_num [quarter_024_024]
  · norm_num [quarter_024_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_024]

def quarter_024_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (6765597/25000000), (6765597/25000000), (6765597/25000000), (9406417/100000000), (9406417/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (20077599/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (153533/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3035217/50000000), (1/100000000), (1/100000000), (7239419/100000000), (1/100000000), (153533/6250000)]
    alternative := .zero
    polynomial := [(23855860278318622378912312717/1799259992189922644800000000000), (45278981187201/50586950000000), (-503328557537381212944990892883/899629996094961322400000000000), (45278981187201/50586950000000), (-1030512975353081048268894098483/1799259992189922644800000000000)]
    bernstein := [(98481890888041988090574787336813/460610558000620197068800000000000), (1006334029160843587389440814999519/4606105580006201970688000000000000), (30833992494815479858991269853929663/138183167400186059120640000000000000), (104922187042872377113498503097419447/460610558000620197068800000000000000), (1070605160001778228312653270846692797/4606105580006201970688000000000000000)]
    reserve := (213807280743/1000000000000) }

theorem quarter_024_025_valid : quarter_024_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_025]
  · intro i; fin_cases i <;> norm_num [quarter_024_025]
  · norm_num [quarter_024_025]
  · norm_num [quarter_024_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_025]

def quarter_024_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (27272749/100000000), (27272749/100000000), (27272749/100000000), (2272719/25000000), (2272719/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2111497/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2374123/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2969279/50000000), (1/100000000), (1/100000000), (3632021/50000000), (1/100000000), (2374123/100000000)]
    alternative := .zero
    polynomial := [(-251706356793168510501322516743/51207381509200515314000000000000), (57586327695253/59385580000000), (-15458764750520534181865375624243/25603690754600257657000000000000), (57586327695253/59385580000000), (-30665823144247899853229428731743/51207381509200515314000000000000)]
    bernstein := [(30522461448890522884056496827645581137/131090896663553319203840000000000000000), (7796079125987803746826448707638488601/32772724165888329800960000000000000000), (5970963866289759052251039173605785719/24579543124416247350720000000000000000), (507892078636320879846040339038425629/2048295260368020612560000000000000000), (129548055901238470257108994154661417/512073815092005153140000000000000000)]
    reserve := (232834332709/1000000000000) }

theorem quarter_024_026_valid : quarter_024_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_026]
  · intro i; fin_cases i <;> norm_num [quarter_024_026]
  · norm_num [quarter_024_026]
  · norm_num [quarter_024_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_026]

def quarter_024_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (27487193/100000000), (27487193/100000000), (27487193/100000000), (876921/10000000), (876921/10000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (22112459/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1145059/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5794241/100000000), (1/100000000), (1/100000000), (3645177/50000000), (1/100000000), (2290119/100000000)]
    alternative := .zero
    polynomial := [(-42454646831057710018014443843/1653664318694139596000000000000), (607809428237587/579424100000000), (-540367436046299942947187116843/826832159347069798000000000000), (607809428237587/579424100000000), (-1038280225261542175876359789843/1653664318694139596000000000000)]
    bernstein := [(4191080184925187611598930612675317/16536643186941395960000000000000000), (17124936399623141156350755992422607/66146572747765583840000000000000000), (209822614800314258967103112291117291/793758872973187006080000000000000000), (4680719109877358160321783850808767/17349920720725399040000000000000000), (19100398857585182351492669933264257/69399682882901596160000000000000000)]
    reserve := (31680251983/125000000000) }

theorem quarter_024_027_valid : quarter_024_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_027]
  · intro i; fin_cases i <;> norm_num [quarter_024_027]
  · norm_num [quarter_024_027]
  · norm_num [quarter_024_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_027]

def quarter_024_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (173157/625000), (173157/625000), (173157/625000), (8442321/100000000), (8442321/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11534049/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8819/400000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5638103/100000000), (1/100000000), (1/100000000), (1829583/25000000), (1/100000000), (8819/400000)]
    alternative := .zero
    polynomial := [(-249109924285680419097453333/5053961849991729500000000000), (1997201322693/1761907187500), (-1792538466410501394617013333/2526980924995864750000000000), (1997201322693/1761907187500), (-3335967008535322370136573333/5053961849991729500000000000)]
    bernstein := [(3567490133556733398381404018069787/12938142335978827520000000000000000), (1821792003923148759858594068565393/6469071167989413760000000000000000), (929911898900759079425242341380227/3234535583994706880000000000000000), (474461852274321373759115448973353/1617267791997353440000000000000000), (241983516313844637453178535493867/808633895998676720000000000000000)]
    reserve := (275734339669/1000000000000) }

theorem quarter_024_028_valid : quarter_024_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_028]
  · intro i; fin_cases i <;> norm_num [quarter_024_028]
  · norm_num [quarter_024_028]
  · norm_num [quarter_024_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_028]

def quarter_024_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 0]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (28623581/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6530147/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-791352488847721368036173/5803367759488000000000000), (954119357125473/653014700000000), (-2937790811621204592324173/2901683879744000000000000), (954119357125473/653014700000000), (-5084229134394687816612173/5803367759488000000000000)]
    bernstein := [(279023570419861849652590111027/928538841518080000000000000000), (114253662594494344577861152463/371415536607232000000000000000), (140271802598845565369771974273/445698643928678400000000000000), (19124525956096234960326270151/59426485857157120000000000000), (7818190784798868847520642083/23770594342862848000000000000)]
    reserve := (300497467573/1000000000000) }

theorem quarter_024_029_valid : quarter_024_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_024_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_024_029]
  · intro i; fin_cases i <;> norm_num [quarter_024_029]
  · norm_num [quarter_024_029]
  · norm_num [quarter_024_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_024_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_024_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_024_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_024_029]

def quarterTable024 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 0, 0, 0, 0]
  rows := [quarter_024_000, quarter_024_001, quarter_024_002, quarter_024_003, quarter_024_004, quarter_024_005, quarter_024_006, quarter_024_007, quarter_024_008, quarter_024_009, quarter_024_010, quarter_024_011, quarter_024_012, quarter_024_013, quarter_024_014, quarter_024_015, quarter_024_016, quarter_024_017, quarter_024_018, quarter_024_019, quarter_024_020, quarter_024_021, quarter_024_022, quarter_024_023, quarter_024_024, quarter_024_025, quarter_024_026, quarter_024_027, quarter_024_028, quarter_024_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_024_000_valid
    · exact quarter_024_001_valid
    · exact quarter_024_002_valid
    · exact quarter_024_003_valid
    · exact quarter_024_004_valid
    · exact quarter_024_005_valid
    · exact quarter_024_006_valid
    · exact quarter_024_007_valid
    · exact quarter_024_008_valid
    · exact quarter_024_009_valid
    · exact quarter_024_010_valid
    · exact quarter_024_011_valid
    · exact quarter_024_012_valid
    · exact quarter_024_013_valid
    · exact quarter_024_014_valid
    · exact quarter_024_015_valid
    · exact quarter_024_016_valid
    · exact quarter_024_017_valid
    · exact quarter_024_018_valid
    · exact quarter_024_019_valid
    · exact quarter_024_020_valid
    · exact quarter_024_021_valid
    · exact quarter_024_022_valid
    · exact quarter_024_023_valid
    · exact quarter_024_024_valid
    · exact quarter_024_025_valid
    · exact quarter_024_026_valid
    · exact quarter_024_027_valid
    · exact quarter_024_028_valid
    · exact quarter_024_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
