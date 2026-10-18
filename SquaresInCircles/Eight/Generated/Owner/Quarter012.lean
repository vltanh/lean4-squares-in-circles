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

def quarter_012_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_012_000_valid : quarter_012_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_000]
  · intro i; fin_cases i <;> norm_num [quarter_012_000]
  · norm_num [quarter_012_000]
  · norm_num [quarter_012_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_000]

def quarter_012_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_012_001_valid : quarter_012_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_001]
  · intro i; fin_cases i <;> norm_num [quarter_012_001]
  · norm_num [quarter_012_001]
  · norm_num [quarter_012_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_001]

def quarter_012_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_012_002_valid : quarter_012_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_002]
  · intro i; fin_cases i <;> norm_num [quarter_012_002]
  · norm_num [quarter_012_002]
  · norm_num [quarter_012_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_002]

def quarter_012_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_012_003_valid : quarter_012_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_003]
  · intro i; fin_cases i <;> norm_num [quarter_012_003]
  · norm_num [quarter_012_003]
  · norm_num [quarter_012_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_003]

def quarter_012_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_012_004_valid : quarter_012_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_004]
  · intro i; fin_cases i <;> norm_num [quarter_012_004]
  · norm_num [quarter_012_004]
  · norm_num [quarter_012_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_004]

def quarter_012_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_012_005_valid : quarter_012_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_005]
  · intro i; fin_cases i <;> norm_num [quarter_012_005]
  · norm_num [quarter_012_005]
  · norm_num [quarter_012_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_005]

def quarter_012_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_012_006_valid : quarter_012_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_006]
  · intro i; fin_cases i <;> norm_num [quarter_012_006]
  · norm_num [quarter_012_006]
  · norm_num [quarter_012_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_006]

def quarter_012_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_012_007_valid : quarter_012_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_007]
  · intro i; fin_cases i <;> norm_num [quarter_012_007]
  · norm_num [quarter_012_007]
  · norm_num [quarter_012_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_007]

def quarter_012_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_012_008_valid : quarter_012_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_008]
  · intro i; fin_cases i <;> norm_num [quarter_012_008]
  · norm_num [quarter_012_008]
  · norm_num [quarter_012_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_008]

def quarter_012_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1067647938911762121/3859681000000000000), (-13528061/3859681), (-8309344188911762121/1929840500000000000), (-13528061/3859681), (-15551040438911762121/3859681000000000000)]
    bernstein := [(100068034278401520636999/617548960000000000000000), (36328949888069554679293/247019584000000000000000), (265685575963521009711/2016486400000000000000), (917720443345976065601/7904626688000000000000), (63294346623912201551/632370135040000000000)]
    reserve := (100090663863/1000000000000) }

theorem quarter_012_009_valid : quarter_012_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_009]
  · intro i; fin_cases i <;> norm_num [quarter_012_009]
  · norm_num [quarter_012_009]
  · norm_num [quarter_012_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_009]

def quarter_012_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (32317707/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(20098469/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-24605763504485237/100492345000000000), (-64635414/20098469), (-205892376004485237/50246172500000000), (-64635414/20098469), (-387178988504485237/100492345000000000)]
    bernstein := [(1621018638741994947/16464665804800000000), (8644294675777045439/102904161280000000000), (44514715284066379727/643151008000000000000), (43476776959806276103/803938760000000000000), (38785551465746097363/1004923450000000000000)]
    reserve := (38595528311/1000000000000) }

theorem quarter_012_010_valid : quarter_012_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_010]
  · intro i; fin_cases i <;> norm_num [quarter_012_010]
  · norm_num [quarter_012_010]
  · norm_num [quarter_012_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_010]

def quarter_012_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![(19367191/100000000), (18214801/100000000), (6387743/50000000), (6387743/50000000), (1759593/25000000), (1759593/25000000), (2279029/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3078549/12500000), 0, 0]] i.1) i.2
    mu := ![(6978777/100000000), (494167/50000000), (562173/10000000), (1/100000000), (1842797/50000000), (1/100000000), (1838103/100000000)]
    alternative := .zero
    polynomial := [(-2003544422819003070683913797704402807109/145934465408560941942829455198600000000000), (-43476122995759/43617356250000), (-295706941807817062845668777888983784591609/72967232704280470971414727599300000000000), (-43476122995759/43617356250000), (-589410339192815122620653641980263166376109/145934465408560941942829455198600000000000)]
    bernstein := [(22383435038670488229477397654803440900710697/486448218028536473142764850662000000000000000), (87101626109664676655978989514814539195541791/1945792872114145892571059402648000000000000000), (3018945438060307020796981843171417580817259357/70048543396109252132558138495328000000000000000), (3830992875391547740198622436064733359147369457/93398057861479002843410851327104000000000000000), (14392613320519283074105141890396914387469515971/373592231445916011373643405308416000000000000000)]
    reserve := (9631231667/250000000000) }

theorem quarter_012_011_valid : quarter_012_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_011]
  · intro i; fin_cases i <;> norm_num [quarter_012_011]
  · norm_num [quarter_012_011]
  · norm_num [quarter_012_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_011]

def quarter_012_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![(19034483/100000000), (2279893/12500000), (1634147/12500000), (1634147/12500000), (1826853/25000000), (1826853/25000000), (4393039/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (23873559/100000000), 0, 0]] i.1) i.2
    mu := ![(3486093/50000000), (183087/25000000), (354391/6250000), (1/100000000), (118261/3125000), (1/100000000), (477091/25000000)]
    alternative := .zero
    polynomial := [(-28464172557660200003370544430051797/9089810401849342824439745250000000000), (-51725349208981/53632200000000), (-212133372084393385295787547549710536173/40904146808322042709978853625000000000), (-51725349208981/53632200000000), (-424010566615767828791544760199550606173/81808293616644085419957707250000000000)]
    bernstein := [(312383207511713788236712706051224679940281/7756638209578105876855249280000000000000000), (123944508213248159979502752669005991785563/3173170176645588767804420160000000000000000), (5860581425717535724076658582748327763675429/157071923743956644006318797920000000000000000), (83365258119589607937450013102693909304021/2379877632484191575853315120000000000000000), (421656187954367649108614252914746868000427/13089326978663053667193233160000000000000000)]
    reserve := (8053435227/250000000000) }

theorem quarter_012_012_valid : quarter_012_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_012]
  · intro i; fin_cases i <;> norm_num [quarter_012_012]
  · norm_num [quarter_012_012]
  · norm_num [quarter_012_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_012]

def quarter_012_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![(18725717/100000000), (1826453/10000000), (1672631/12500000), (1672631/12500000), (1897113/25000000), (1897113/25000000), (21070751/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2305251/10000000), 0, 0]] i.1) i.2
    mu := ![(3471931/50000000), (120261/25000000), (5721099/100000000), (1/100000000), (194349/5000000), (1/100000000), (1981759/100000000)]
    alternative := .zero
    polynomial := [(114071331876609431410708251025117119889/17037848378714699076303262298500000000000), (-648217671833187/694386200000000), (-192133331333013247195854050635590393414083/25556772568072048614454893447750000000000), (-648217671833187/694386200000000), (-384608876661656322685940226024256138187833/51113545136144097228909786895500000000000)]
    bernstein := [(283338024111576148668843997952758992137615767/8178167221783055556625565903280000000000000000), (547768073998473131656270103185862352753790067/16356334443566111113251131806560000000000000000), (3096584892317804983896745267818280027594419901/98138006661396666679506790839360000000000000000), (1886803122950164657609348646928749911052385467/65425337774264444453004527226240000000000000000), (3316531218348137567677280427361186225444966567/130850675548528888906009054452480000000000000000)]
    reserve := (5069184709/200000000000) }

theorem quarter_012_013_valid : quarter_012_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_013]
  · intro i; fin_cases i <;> norm_num [quarter_012_013]
  · norm_num [quarter_012_013]
  · norm_num [quarter_012_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_013]

def quarter_012_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![(18443447/100000000), (4573697/25000000), (1712301/12500000), (1712301/12500000), (7879921/100000000), (7879921/100000000), (5026277/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2770373/12500000), 0, 0]] i.1) i.2
    mu := ![(6893933/100000000), (235023/100000000), (1443743/25000000), (1/100000000), (199657/5000000), (1/100000000), (2057877/100000000)]
    alternative := .zero
    polynomial := [(2516335692727336175089062525322409090779/160184326511656116196440071665500000000000), (-155763394817421/172348325000000), (-1179559923991853658359174559519879729879221/80092163255828058098220035832750000000000), (-155763394817421/172348325000000), (-2361636183676434652893438181565081868849221/160184326511656116196440071665500000000000)]
    bernstein := [(11935932129721832502910607933866674184309483579/410071875869839657462886583463680000000000000000), (3595289908881420797710614390286831524067777/128147461209324892957152057332400000000000000), (19585047043789047711067257383720207762259979/768884767255949357742912343994400000000000000), (1710573869420422656763225628374356829577/80092163255828058098220035832750000000000), (2516335692727336175089062525322409090779/160184326511656116196440071665500000000000)]
    reserve := (15709000671/1000000000000) }

theorem quarter_012_014_valid : quarter_012_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_014]
  · intro i; fin_cases i <;> norm_num [quarter_012_014]
  · norm_num [quarter_012_014]
  · norm_num [quarter_012_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_014]

def quarter_012_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![(18408463/100000000), (18414217/100000000), (13752843/100000000), (13752843/100000000), (1974539/25000000), (1974539/25000000), (19875321/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(115071/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (21937959/100000000), 0, 0]] i.1) i.2
    mu := ![(70137/1000000), (58157/50000000), (362961/6250000), (1/100000000), (4007361/100000000), (1/100000000), (2062639/100000000)]
    alternative := .zero
    polynomial := [(18084170711097691477582766368702515133/906477581565809060906345346000000000000), (249083125276270311/412015910000000000), (-13370957263333945581665068894451028239867/453238790782904530453172673000000000000), (249083125276270311/412015910000000000), (-26759998697378988854807720555270758994867/906477581565809060906345346000000000000)]
    bernstein := [(18084170711097691477582766368702515133/906477581565809060906345346000000000000), (86036898268674196944437355650236794697/3625910326263236243625381384000000000000), (106313579168215207992587306096345206394533/4351092391515883492350457660800000000000000), (128029597749674195524613728314115734617897/5801456522021177989800610214400000000000000), (2269183859405207192317383919673705873586749/136504859341674776230602593280000000000000000)]
    reserve := (16623465789/1000000000000) }

theorem quarter_012_015_valid : quarter_012_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_015]
  · intro i; fin_cases i <;> norm_num [quarter_012_015]
  · norm_num [quarter_012_015]
  · norm_num [quarter_012_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_015]

def quarter_012_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![(9280779/50000000), (4653459/25000000), (6776321/50000000), (6776321/50000000), (7654443/100000000), (7654443/100000000), (10205217/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1394077/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11204713/50000000), 0, 0]] i.1) i.2
    mu := ![(1461791/20000000), (23493/20000000), (1454487/25000000), (1/100000000), (3932927/100000000), (1/100000000), (1998993/100000000)]
    alternative := .zero
    polynomial := [(-16818174450982905977388279915235117363/2181665982458378294838873934950000000000), (73254476899168203/34900260125000000), (-32546961428564469429388988271649228049563/1090832991229189147419436967475000000000), (73254476899168203/34900260125000000), (-65077104682677955952800588263383220981763/2181665982458378294838873934950000000000)]
    bernstein := [(145984893631720928965020046973315860461328637/5585064915093448434787517273472000000000000000), (27874992765535571408010027113920072564181679/930844152515574739131252878912000000000000000), (128387360923314243279654309955168070009699111/4188798686320086326090637955104000000000000000), (6573549286616805604036258170624353266650879/232711038128893684782813219728000000000000000), (7931981235321843663844631744443490711183837/349066557193340527174219829592000000000000000)]
    reserve := (22723406387/1000000000000) }

theorem quarter_012_016_valid : quarter_012_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_016]
  · intro i; fin_cases i <;> norm_num [quarter_012_016]
  · norm_num [quarter_012_016]
  · norm_num [quarter_012_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_016]

def quarter_012_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![(2385791/10000000), (24045031/100000000), (16808743/100000000), (16808743/100000000), (4619893/50000000), (4619893/50000000), 0]
    cone := fun i => (![![0, 0, 0, (2385791/20000000), 0], ![(1496967/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2413011/100000000), 0, 0]] i.1) i.2
    mu := ![(852547/20000000), (9463/6250000), (1853259/25000000), (1/100000000), (2423317/50000000), (1/100000000), (603253/25000000)]
    alternative := .zero
    polynomial := [(-9696502323425157216412116854170010755577/87428494324149216798208153596000000000000), (35994617920977/7570400000000), (-1665969486244587700259110798018812126168077/43714247162074608399104076798000000000000), (35994617920977/7570400000000), (-3322242470165750243301809479183454241580577/87428494324149216798208153596000000000000)]
    bernstein := [(446312200173613805461487994996701829943737823/13988559091863874687713304575360000000000000000), (1060533884928573646428162596494930450267739269/27977118183727749375426609150720000000000000000), (352988234592558958179970043222619525602852359/8834879426440341908029455521280000000000000000), (4256400114644340421258326860164158214296865421/111908472734910997501706436602880000000000000000), (7189756131552131774785261669886459497967635663/223816945469821995003412873205760000000000000000)]
    reserve := (31905516303/1000000000000) }

theorem quarter_012_017_valid : quarter_012_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_017]
  · intro i; fin_cases i <;> norm_num [quarter_012_017]
  · norm_num [quarter_012_017]
  · norm_num [quarter_012_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_017]

def quarter_012_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (33134521/100000000), (4374083/20000000), (4374083/20000000), (2890581/25000000), (2890581/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3693017/50000000), 0, (32631003/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3019553/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (207931/100000000), (10031783/100000000), (1/100000000), (625097/10000000), (1/100000000), (3019553/100000000)]
    alternative := .zero
    polynomial := [(-3321771775172259783741409971966231473/9449279271611907825664063200000000000), (3813441319439717/415862000000000), (-248996546606900252970129259646950899473/4724639635805953912832031600000000000), (3813441319439717/415862000000000), (-494671321438628246156517109321935567473/9449279271611907825664063200000000000)]
    bernstein := [(1015398274059786663960624280348537862228287/24190154935326484033700001792000000000000000), (304161890611572844767478377848878161440029/6047538733831621008425000448000000000000000), (241096054908894051052076555722222949363329/4535654050373715756318750336000000000000000), (19099608550064258820239195309572692835481/377971170864476313026562528000000000000000), (4004388031780393939014286969779944419927/94492792716119078256640632000000000000000)]
    reserve := (41975682949/1000000000000) }

theorem quarter_012_018_valid : quarter_012_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_018]
  · intro i; fin_cases i <;> norm_num [quarter_012_018]
  · norm_num [quarter_012_018]
  · norm_num [quarter_012_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_018]

def quarter_012_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (34929533/100000000), (21611889/100000000), (21611889/100000000), (2184669/20000000), (2184669/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4731871/50000000), 0, (34056429/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (71317/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (218179/100000000), (10378801/100000000), (1/100000000), (6118787/100000000), (1/100000000), (2852681/100000000)]
    alternative := .zero
    polynomial := [(-23114657107983241539541144302821526397/36485186493567153004599612000000000000), (5421706609232063/436358000000000), (-1017753728312139366561845564164492506397/18242593246783576502299806000000000000), (5421706609232063/436358000000000), (-2012392799516295491584149984026163486397/36485186493567153004599612000000000000)]
    bernstein := [(21148508982347656850976261862594383084203/364851864935671530045996120000000000000000), (6502496651591352559680561296709090738381/97293830649512408012265632000000000000000), (48990307468918922725466600018544661256261/700515580676489337688312550400000000000000), (64404457527751449804545472643398378681/957970024856737555813076992000000000000), (2074906096290917727140848287297272003/35371200917787232830021304320000000000)]
    reserve := (57964645421/1000000000000) }

theorem quarter_012_019_valid : quarter_012_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_019]
  · intro i; fin_cases i <;> norm_num [quarter_012_019]
  · norm_num [quarter_012_019]
  · norm_num [quarter_012_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_019]

def quarter_012_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (183849/500000), (5330753/25000000), (5330753/25000000), (1286511/12500000), (1286511/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1169433/10000000), 0, (35405241/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (107513/4000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (228333/100000000), (2148041/20000000), (1/100000000), (1495673/25000000), (1/100000000), (107513/4000000)]
    alternative := .zero
    polynomial := [(-2183710099251380734545565877363267/2146107835213267749404000000000000), (12163533123597/761110000000), (-63364021654859229347324200769363267/1073053917606633874702000000000000), (12163533123597/761110000000), (-124544333210467077960102835661363267/2146107835213267749404000000000000)]
    bernstein := [(3743665069901234773205898606835411/50231186817334541151764480000000000), (369174492065566474946102933380757227/4395228846516772350779392000000000000), (2057120875300548407298503917444952137/23545868820625566164889600000000000000), (11619097222904735367078278579556278911/137350901453649135961856000000000000000), (25960679951135265177986155765723332973/343377253634122839904640000000000000000)]
    reserve := (74528700337/1000000000000) }

theorem quarter_012_020_valid : quarter_012_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_020]
  · intro i; fin_cases i <;> norm_num [quarter_012_020]
  · norm_num [quarter_012_020]
  · norm_num [quarter_012_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_020]

def quarter_012_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (38646681/100000000), (21004097/100000000), (21004097/100000000), (4836281/50000000), (4836281/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2813989/20000000), 0, (36658163/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2526033/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (47661/20000000), (1389287/12500000), (1/100000000), (2921517/50000000), (1/100000000), (2526033/100000000)]
    alternative := .zero
    polynomial := [(-20715855471510681485111770189781/13670303169986360676000000000000), (3152805730181299/158870000000000), (-427063639982360872102975318537781/6835151584993180338000000000000), (3152805730181299/158870000000000), (-833411424493211062720838866885781/13670303169986360676000000000000)]
    bernstein := [(200550227948261528630159520896876539/2187248507197817708160000000000000000), (445325697640610147415663195959601791/4374497014395635416320000000000000000), (2768394153650915968141280760336142537/26246982086373812497920000000000000000), (1796137973915844629272710677309444551/17497988057582541665280000000000000000), (3262735828022276337207388433276763019/34995976115165083330560000000000000000)]
    reserve := (91690645707/1000000000000) }

theorem quarter_012_021_valid : quarter_012_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_021]
  · intro i; fin_cases i <;> norm_num [quarter_012_021]
  · norm_num [quarter_012_021]
  · norm_num [quarter_012_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_021]

def quarter_012_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (20274879/50000000), (10328153/50000000), (10328153/50000000), (1813763/20000000), (1813763/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2072437/12500000), 0, (7559087/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1184181/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (247997/100000000), (11498927/100000000), (1/100000000), (5700309/100000000), (1/100000000), (1184181/50000000)]
    alternative := .zero
    polynomial := [(-18300030283928642362135756017054215303/8555348655354425692303756000000000000), (1191329526848463/49599400000000), (-282655867793628288074297280530644415303/4277674327677212846151878000000000000), (1191329526848463/49599400000000), (-547011705303327933786458805044234615303/8555348655354425692303756000000000000)]
    bernstein := [(2397497090885194973240611446779093979867097/21901692557707329772297615360000000000000000), (329257169137997375799219115119325144603071/2737711569713416221537201920000000000000000), (31896480603070711340890052982111050503171/256660459660632770769112680000000000000000), (2596728413934643588332917107762226769627/21388371638386064230759390000000000000000), (149132496614350198710726020800017663793/1336773227399129014422461875000000000000)]
    reserve := (4378651713/40000000000) }

theorem quarter_012_022_valid : quarter_012_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_022]
  · intro i; fin_cases i <;> norm_num [quarter_012_022]
  · norm_num [quarter_012_022]
  · norm_num [quarter_012_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_022]

def quarter_012_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (4246681/10000000), (10140869/50000000), (10140869/50000000), (8484857/100000000), (8484857/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1920847/10000000), 0, (38797231/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1107929/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (64327/25000000), (2972871/25000000), (1/100000000), (2777589/50000000), (1/100000000), (2215859/100000000)]
    alternative := .zero
    polynomial := [(-6067909386242780165747891504948600761/2092458922157237035306608000000000000), (1466685428021089/51461600000000), (-73060076344373800697945701381900400761/1046229461078618517653304000000000000), (1466685428021089/51461600000000), (-140052243302504821230143511258852200761/2092458922157237035306608000000000000)]
    bernstein := [(41804636726016129082146104235009721391/326946706587068286766657500000000000000), (66293838501969060180133282950647162033/475558845944826598933320000000000000000), (9025236501194948074499065147439411651813/62773767664717111059198240000000000000000), (8575707576602955237826603755971173969421/60871532280937804663464960000000000000000), (699595945534794041344416447939574876595879/5356694840722526810384916480000000000000000)]
    reserve := (63931882297/500000000000) }

theorem quarter_012_023_valid : quarter_012_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_023]
  · intro i; fin_cases i <;> norm_num [quarter_012_023]
  · norm_num [quarter_012_023]
  · norm_num [quarter_012_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_023]

def quarter_012_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (2219193/5000000), (3976701/20000000), (3976701/20000000), (1584913/20000000), (1584913/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(21938861/100000000), 0, (7928831/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (413907/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (66533/25000000), (6144439/50000000), (1/100000000), (5408489/100000000), (1/100000000), (64673/3125000)]
    alternative := .zero
    polynomial := [(-3734653128682012345098628247512133663/980531383876462837040496000000000000), (177150660783309/5322640000000), (-36149101879254991909706711263474133663/490265691938231418520248000000000000), (177150660783309/5322640000000), (-68563550629827971474314794279436133663/980531383876462837040496000000000000)]
    bernstein := [(368699295287448189542748041096190920307457/2510160342723744862823669760000000000000000), (39962353776567191934651473699517867211993/251016034272374486282366976000000000000000), (12347664737982423591184002726226204814563/75304810281712345884710092800000000000000), (404304428997384331392989810454604586201/2510160342723744862823669760000000000000), (37741106061766226720699528866342171393/251016034272374486282366976000000000000)]
    reserve := (9180172901/62500000000) }

theorem quarter_012_024_valid : quarter_012_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_024]
  · intro i; fin_cases i <;> norm_num [quarter_012_024]
  · norm_num [quarter_012_024]
  · norm_num [quarter_012_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_024]

def quarter_012_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (11571329/25000000), (4866439/25000000), (4866439/25000000), (3695793/50000000), (3695793/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(12374607/50000000), 0, (40317819/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (965173/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6859/2500000), (12687571/100000000), (1/100000000), (1315319/25000000), (1/100000000), (965173/50000000)]
    alternative := .zero
    polynomial := [(-17236063788343988450493085074064892021/3535293906794014096622176000000000000), (5261095205496669/137180000000000), (-137466659464389702862593181109383724021/1767646953397007048311088000000000000), (5261095205496669/137180000000000), (-257697255140435417274693277144702556021/3535293906794014096622176000000000000)]
    bernstein := [(150701213391511875298408069798763172331/905035240139267608735277056000000000000), (1625958829152699527004131015838124698153/9050352401392676087352770560000000000000), (50188115994375262723761838068657020342281/271510572041780282620583116800000000000000), (164672612097567274882622780587948386652689/905035240139267608735277056000000000000000), (1545846770468177370167712281874253764397339/9050352401392676087352770560000000000000000)]
    reserve := (166514193821/1000000000000) }

theorem quarter_012_025_valid : quarter_012_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_025]
  · intro i; fin_cases i <;> norm_num [quarter_012_025]
  · norm_num [quarter_012_025]
  · norm_num [quarter_012_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_025]

def quarter_012_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (48154213/100000000), (4758413/25000000), (4758413/25000000), (6889241/100000000), (6889241/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1725927/6250000), 0, (4080147/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (449789/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (70471/25000000), (13083623/100000000), (1/100000000), (5114767/100000000), (1/100000000), (1799157/100000000)]
    alternative := .zero
    polynomial := [(-29613328302449442923218712384206394551/4848365191134541549136244000000000000), (2463064736465121/56376800000000), (-198581538141577414077934676447531444551/2424182595567270774568122000000000000), (2463064736465121/56376800000000), (-367549747980705385232650640510856494551/4848365191134541549136244000000000000)]
    bernstein := [(2317779854270524232758239090360460970771609/12411814889304426365788784640000000000000000), (622899681451003321755592055388431453019157/3102953722326106591447196160000000000000000), (480306511549420572373149194958894721102583/2327215291744579943585397120000000000000000), (39468172387342765837939526594142398613953/193934607645381661965449760000000000000000), (9305825237405616986397444197772478089569/48483651911345415491362440000000000000000)]
    reserve := (3734796039/20000000000) }

theorem quarter_012_026_valid : quarter_012_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_026]
  · intro i; fin_cases i <;> norm_num [quarter_012_026]
  · norm_num [quarter_012_026]
  · norm_num [quarter_012_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_026]

def quarter_012_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (49972563/100000000), (18593287/100000000), (18593287/100000000), (6420431/100000000), (6420431/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(30508161/100000000), 0, (5135081/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (419181/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1443/500000), (13472767/100000000), (1/100000000), (2485183/50000000), (1/100000000), (67069/4000000)]
    alternative := .zero
    polynomial := [(-973741231830344435783742604997269/129617406277152180867480000000000), (2369876223456003/48100000000000), (-1116758837024087331611616171873257/12961740627715218086748000000000), (2369876223456003/48100000000000), (-10193847138410528880332419113735301/129617406277152180867480000000000)]
    bernstein := [(20692137308340469467707793804667259/99705697136270908359600000000000000), (288311010461522986987079169834557957/1296174062771521808674800000000000000), (2031389994025224223298329472095030841/8888050716147578116627200000000000000), (1872444807463590063386775361727143957/8295514001737739575518720000000000000), (70916658435828229880415455836597099451/331820560069509583020748800000000000000)]
    reserve := (51883036533/250000000000) }

theorem quarter_012_027_valid : quarter_012_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_027]
  · intro i; fin_cases i <;> norm_num [quarter_012_027]
  · norm_num [quarter_012_027]
  · norm_num [quarter_012_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_027]

def quarter_012_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (51721811/100000000), (1134471/6250000), (1134471/6250000), (5987559/100000000), (5987559/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(33399347/100000000), 0, (41143833/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (781839/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (294413/100000000), (2770103/20000000), (1/100000000), (4829621/100000000), (1/100000000), (781839/50000000)]
    alternative := .zero
    polynomial := [(-118525175960814156336139860160706661/13035012879146902505495200000000000), (32421460706906777/588826000000000), (-589614169768756268997364367839982661/6517506439573451252747600000000000), (32421460706906777/588826000000000), (-1060703163576698381658588875519258661/13035012879146902505495200000000000)]
    bernstein := [(7636800844610481304117185899284653306379/33369632970616070414067712000000000000000), (4082445919596305306876151740840185953681/16684816485308035207033856000000000000000), (2096467793636994787376354087348953219859/8342408242654017603516928000000000000000), (1036640867857035449866374640183062533001/4171204121327008801758464000000000000000), (492436658320852746950116239252777427739/2085602060663504400879232000000000000000)]
    reserve := (114427402473/500000000000) }

theorem quarter_012_028_valid : quarter_012_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_028]
  · intro i; fin_cases i <;> norm_num [quarter_012_028]
  · norm_num [quarter_012_028]
  · norm_num [quarter_012_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_028]

def quarter_012_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 0]
    lambda := ![0, (427067/800000), (17715841/100000000), (17715841/100000000), (699059/12500000), (699059/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(36256977/100000000), 0, (40983039/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1460499/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (299237/100000000), (14212291/100000000), (1/100000000), (938837/20000000), (1/100000000), (2921/200000)]
    alternative := .zero
    polynomial := [(-22007801783707077386179835552179797/2028305146259690448532000000000000), (292180664412567/4787792000000), (-96155588394266762057444036844679797/1014152573129845224266000000000000), (292180664412567/4787792000000), (-170303375004826446728708238137179797/2028305146259690448532000000000000)]
    bernstein := [(81347341477994959012070053721060745003/324528823401550471765120000000000000000), (34716501501065349783182103001778327607/129811529360620188706048000000000000000), (14257585355966719306340399235604544899/51924611744248075482419200000000000000), (5646825760973995445840848682105092239/20769844697699230192967680000000000000), (2152299232866393050729433685202861787/8307937879079692077187072000000000000)]
    reserve := (31332864607/125000000000) }

theorem quarter_012_029_valid : quarter_012_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_012_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_012_029]
  · intro i; fin_cases i <;> norm_num [quarter_012_029]
  · norm_num [quarter_012_029]
  · norm_num [quarter_012_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_012_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_012_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_012_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_012_029]

def quarterTable012 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 0, 0, 0, 0]
  rows := [quarter_012_000, quarter_012_001, quarter_012_002, quarter_012_003, quarter_012_004, quarter_012_005, quarter_012_006, quarter_012_007, quarter_012_008, quarter_012_009, quarter_012_010, quarter_012_011, quarter_012_012, quarter_012_013, quarter_012_014, quarter_012_015, quarter_012_016, quarter_012_017, quarter_012_018, quarter_012_019, quarter_012_020, quarter_012_021, quarter_012_022, quarter_012_023, quarter_012_024, quarter_012_025, quarter_012_026, quarter_012_027, quarter_012_028, quarter_012_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_012_000_valid
    · exact quarter_012_001_valid
    · exact quarter_012_002_valid
    · exact quarter_012_003_valid
    · exact quarter_012_004_valid
    · exact quarter_012_005_valid
    · exact quarter_012_006_valid
    · exact quarter_012_007_valid
    · exact quarter_012_008_valid
    · exact quarter_012_009_valid
    · exact quarter_012_010_valid
    · exact quarter_012_011_valid
    · exact quarter_012_012_valid
    · exact quarter_012_013_valid
    · exact quarter_012_014_valid
    · exact quarter_012_015_valid
    · exact quarter_012_016_valid
    · exact quarter_012_017_valid
    · exact quarter_012_018_valid
    · exact quarter_012_019_valid
    · exact quarter_012_020_valid
    · exact quarter_012_021_valid
    · exact quarter_012_022_valid
    · exact quarter_012_023_valid
    · exact quarter_012_024_valid
    · exact quarter_012_025_valid
    · exact quarter_012_026_valid
    · exact quarter_012_027_valid
    · exact quarter_012_028_valid
    · exact quarter_012_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
