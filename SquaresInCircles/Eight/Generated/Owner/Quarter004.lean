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

def quarter_004_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_004_000_valid : quarter_004_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_000]
  · intro i; fin_cases i <;> norm_num [quarter_004_000]
  · norm_num [quarter_004_000]
  · norm_num [quarter_004_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_000]

def quarter_004_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_004_001_valid : quarter_004_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_001]
  · intro i; fin_cases i <;> norm_num [quarter_004_001]
  · norm_num [quarter_004_001]
  · norm_num [quarter_004_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_001]

def quarter_004_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_004_002_valid : quarter_004_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_002]
  · intro i; fin_cases i <;> norm_num [quarter_004_002]
  · norm_num [quarter_004_002]
  · norm_num [quarter_004_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_002]

def quarter_004_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_004_003_valid : quarter_004_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_003]
  · intro i; fin_cases i <;> norm_num [quarter_004_003]
  · norm_num [quarter_004_003]
  · norm_num [quarter_004_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_003]

def quarter_004_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_004_004_valid : quarter_004_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_004]
  · intro i; fin_cases i <;> norm_num [quarter_004_004]
  · norm_num [quarter_004_004]
  · norm_num [quarter_004_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_004]

def quarter_004_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_004_005_valid : quarter_004_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_005]
  · intro i; fin_cases i <;> norm_num [quarter_004_005]
  · norm_num [quarter_004_005]
  · norm_num [quarter_004_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_005]

def quarter_004_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_004_006_valid : quarter_004_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_006]
  · intro i; fin_cases i <;> norm_num [quarter_004_006]
  · norm_num [quarter_004_006]
  · norm_num [quarter_004_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_006]

def quarter_004_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_004_007_valid : quarter_004_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_007]
  · intro i; fin_cases i <;> norm_num [quarter_004_007]
  · norm_num [quarter_004_007]
  · norm_num [quarter_004_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_007]

def quarter_004_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_004_008_valid : quarter_004_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_008]
  · intro i; fin_cases i <;> norm_num [quarter_004_008]
  · norm_num [quarter_004_008]
  · norm_num [quarter_004_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_008]

def quarter_004_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1067647938911762121/3859681000000000000), (-13528061/3859681), (-8309344188911762121/1929840500000000000), (-13528061/3859681), (-15551040438911762121/3859681000000000000)]
    bernstein := [(100068034278401520636999/617548960000000000000000), (36328949888069554679293/247019584000000000000000), (265685575963521009711/2016486400000000000000), (917720443345976065601/7904626688000000000000), (63294346623912201551/632370135040000000000)]
    reserve := (100090663863/1000000000000) }

theorem quarter_004_009_valid : quarter_004_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_009]
  · intro i; fin_cases i <;> norm_num [quarter_004_009]
  · norm_num [quarter_004_009]
  · norm_num [quarter_004_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_009]

def quarter_004_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(27031457/100000000), (27031457/100000000), (463979/6250000), (463979/6250000), 0, 0, (194311/625000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2198949/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (194311/625000), 0, 0]] i.1) i.2
    mu := ![(4666789/50000000), (1/100000000), (7515279/100000000), (1/100000000), (241219/12500000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-9524110098606000015706768433419/270722757326093142048000000000000), (-2058768198914124459451/1753611068456550000000), (-166871471352487992727543092593419/135361378663046571024000000000000), (-2058768198914124459451/1753611068456550000000), (-324218832606369985439379416753419/270722757326093142048000000000000)]
    bernstein := [(464793862777989592187905800672021/4928357395589677821460480000000000), (2729485952527406269165898175273977/30802233722435486384128000000000000), (430499329635778527259861148166800147/5197876940660988327321600000000000000), (260756601019120663355803418248199/3389330295162355456000000000000000), (11298334088330772660296635224233693/159248680780054789440000000000000000)]
    reserve := (35473870279/500000000000) }

theorem quarter_004_010_valid : quarter_004_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_010]
  · intro i; fin_cases i <;> norm_num [quarter_004_010]
  · norm_num [quarter_004_010]
  · norm_num [quarter_004_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_010]

def quarter_004_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(5167151/20000000), (5167151/20000000), (9269159/100000000), (9269159/100000000), 0, 0, (29790173/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (429/15625), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (29790173/100000000), 0, 0]] i.1) i.2
    mu := ![(9198859/100000000), (1/100000000), (7359217/100000000), (1/100000000), (60237/2500000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-34985103861712718749813221889/1631131207477438604400000000000), (-695910501424613819333/676963995334030000000), (-942316974918643333077562053889/815565603738719302200000000000), (-695910501424613819333/676963995334030000000), (-1849648845975573947405310885889/1631131207477438604400000000000)]
    bernstein := [(1153386176875472862399491667846311/16311312074774386044000000000000000), (4277854576834292391710960401360033/65245248299097544176000000000000000), (47231344446495117628318574590571297/782942979589170530112000000000000000), (57402731110723243032399554957953397/1043923972785560706816000000000000000), (206902736224339948341987082897599791/4175695891142242827264000000000000000)]
    reserve := (4954928271/100000000000) }

theorem quarter_004_011_valid : quarter_004_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_011]
  · intro i; fin_cases i <;> norm_num [quarter_004_011]
  · norm_num [quarter_004_011]
  · norm_num [quarter_004_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_011]

def quarter_004_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(23174477/100000000), (23174477/100000000), (5135213/50000000), (5135213/50000000), (391997/12500000), (1657779/50000000), (26658661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11671551/50000000), 0, 0]] i.1) i.2
    mu := ![(4236609/50000000), (1/100000000), (6749641/100000000), (1/100000000), (678353/25000000), (576577/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-7400813750260854336193468488009479/860337336235466362136253000000000000), (-4803957660820783826393/5719117961473800000000), (-436133905782004811523132174007149479/430168668117733181068126500000000000), (-4803957660820783826393/5719117961473800000000), (-864866997813748768710070879526289479/860337336235466362136253000000000000)]
    bernstein := [(107955963725411023421496147757162560717001/2202463580762793887068807680000000000000000), (49157473909994647123334194348042028841067/1101231790381396943534403840000000000000000), (66357677586085387806300018784081295464867/1651847685572095415301605760000000000000000), (3268216605405498522752497677542285889521/91769315865116411961200320000000000000000), (1420632002454022823963506744327150529107/45884657932558205980600160000000000000000)]
    reserve := (1935058561/62500000000) }

theorem quarter_004_012_valid : quarter_004_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_012]
  · intro i; fin_cases i <;> norm_num [quarter_004_012]
  · norm_num [quarter_004_012]
  · norm_num [quarter_004_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_012]

def quarter_004_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(10957837/50000000), (10957837/50000000), (2910581/25000000), (2910581/25000000), (23711/625000), (4113537/100000000), (4995341/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (325987/1562500), 0, 0]] i.1) i.2
    mu := ![(409277/5000000), (1/100000000), (50973/781250), (1/100000000), (3094029/100000000), (706983/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8370944106527449829644475128151/3120290366074712668728000000000000), (-2172599555245678417/3034483857600000000), (-1471549328466769137610592714248151/1560145183037356334364000000000000), (-2172599555245678417/3034483857600000000), (-2934727712827010825391540953368151/3120290366074712668728000000000000)]
    bernstein := [(6902296656848321924723468217081084953/223800136601220770722560000000000000000), (38833653530109258157029308045371891493/1442267546985644966878720000000000000000), (1785140107213421608622749640514335124511/77882447537224828211450880000000000000000), (108607932976130730247635846440233493093/5769070187942579867514880000000000000000), (1520038733007617933859805193891218052437/103843263382966437615267840000000000000000)]
    reserve := (14637817451/1000000000000) }

theorem quarter_004_013_valid : quarter_004_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_013]
  · intro i; fin_cases i <;> norm_num [quarter_004_013]
  · norm_num [quarter_004_013]
  · norm_num [quarter_004_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_013]

def quarter_004_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(21073179/100000000), (21073179/100000000), (6279349/50000000), (6279349/50000000), (1068689/25000000), (943501/20000000), (1483999/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (237831/1250000), 0, 0]] i.1) i.2
    mu := ![(1584319/20000000), (1/100000000), (1266679/20000000), (1/100000000), (1676063/50000000), (160861/10000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-119459837361402039102094591923141/270533037347093335787021500000000000), (-14486497377045830469/22804813711375000000), (-121364692154059098100908853091968141/135266518673546667893510750000000000), (-14486497377045830469/22804813711375000000), (-242609924470756794162715611592013141/270533037347093335787021500000000000)]
    bernstein := [(10311040674043306183810220902641722895659/692564575608558939614775040000000000000000), (16927557201879636082401426020679083777/1298152906482772145482240000000000000000), (92823354168403830854390986413022061747777/8310774907302707275377300480000000000000000), (1301783616504951061465380511058019821/140340854754894285998080000000000000000), (2204208365597891392144939436661824331407/299487384046944406319902720000000000000000)]
    reserve := (7359937289/1000000000000) }

theorem quarter_004_014_valid : quarter_004_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_014]
  · intro i; fin_cases i <;> norm_num [quarter_004_014]
  · norm_num [quarter_004_014]
  · norm_num [quarter_004_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_014]

def quarter_004_015 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/80), 0⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(1027819/5000000), (1027819/5000000), (13122521/100000000), (13122521/100000000), (4588517/100000000), (5120633/100000000), (2866631/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8906207/50000000), 0, 0]] i.1) i.2
    mu := ![(3890963/50000000), (1/100000000), (3115891/50000000), (1/100000000), (1756331/50000000), (868677/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(1637090144607080392709100812736649/9248558583286319809472935500000000000), (-70809432160860563963/121238165930330000000), (-4020508135971517006997760362946203351/4624279291643159904736467750000000000), (-70809432160860563963/121238165930330000000), (-8042653362087641094388229826705143351/9248558583286319809472935500000000000)]
    bernstein := [(2781657553672350668090989313693095759003849/378820959571407659396011438080000000000000000), (1322289100422529308435993807998355889121/236763099732129787122507148800000000000000), (675608675009577262153144361262283457449/177572324799097340341880361600000000000000), (74068886866875491947933005961434721/36994234333145279237891742000000000000), (1637090144607080392709100812736649/9248558583286319809472935500000000000)]
    reserve := (177010301/1000000000000) }

theorem quarter_004_015_valid : quarter_004_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_015]
  · intro i; fin_cases i <;> norm_num [quarter_004_015]
  · norm_num [quarter_004_015]
  · norm_num [quarter_004_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_015]

def quarter_004_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(20119009/100000000), (20119009/100000000), (13588141/100000000), (13588141/100000000), (2374481/50000000), (5298577/100000000), (22538161/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (538737/3125000), 0, 0]] i.1) i.2
    mu := ![(7821087/100000000), (1/100000000), (6134517/100000000), (1/100000000), (1818551/50000000), (224737/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(129958341336020637018542756521273/2614485828186826957506956400000000000), (126596478475656218459/399821592999825000000), (-1115135706014226672232551610617358727/1307242914093413478753478200000000000), (126596478475656218459/399821592999825000000), (-2230401370369789365102121763991238727/2614485828186826957506956400000000000)]
    bernstein := [(129958341336020637018542756521273/2614485828186826957506956400000000000), (5303901930613143725739657103514573/2614485828186826957506956400000000000), (49178522789459054037179151351820431673/12549531975296769396033390720000000000000), (2659211201360319366216354086636834597/464797480566547014667903360000000000000), (16592108095457810568843409408662356278291/2231027906719425670405936128000000000000000)]
    reserve := (12426759/250000000000) }

theorem quarter_004_016_valid : quarter_004_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_016]
  · intro i; fin_cases i <;> norm_num [quarter_004_016]
  · norm_num [quarter_004_016]
  · norm_num [quarter_004_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_016]

def quarter_004_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(19752867/100000000), (19752867/100000000), (6981763/50000000), (6981763/50000000), (2376113/50000000), (5244107/100000000), (11285441/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2165847/12500000), 0, 0]] i.1) i.2
    mu := ![(7944631/100000000), (1/100000000), (2983313/50000000), (1/100000000), (3727041/100000000), (27941/1562500), (1/100000000)]
    alternative := .zero
    polynomial := [(-1385748391739306595484520969297459/1579641885115379129184155520000000000), (835483029736753778821/2370132094250300000000), (-669949414946840729629772251023742259/789820942557689564592077760000000000), (835483029736753778821/2370132094250300000000), (-1338513081501942152664059981078187059/1579641885115379129184155520000000000)]
    bernstein := [(1762752397674592119747686076077419611773/237875483876198268865378713600000000000000), (6303256772110563110765371673820045698447/673980537649228428451906355200000000000000), (33993586698954459926010533162795157788023/3032912419421527928033578598400000000000000), (2186947727470047386391854309650817994047/168495134412307107112976588800000000000000), (218045299641885354286909342803313052573/14867217742262391804086169600000000000000)]
    reserve := (7410399629/1000000000000) }

theorem quarter_004_017_valid : quarter_004_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_017]
  · intro i; fin_cases i <;> norm_num [quarter_004_017]
  · norm_num [quarter_004_017]
  · norm_num [quarter_004_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_017]

def quarter_004_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(9704797/50000000), (9704797/50000000), (7158321/50000000), (7158321/50000000), (4746197/100000000), (647729/12500000), (45239/200000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17437669/100000000), 0, 0]] i.1) i.2
    mu := ![(2016843/25000000), (1/100000000), (181143/3125000), (1/100000000), (3811137/100000000), (355113/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-732414896857564766951078698631/277464279567911017279500000000000), (4195321587031657133/10824799749600000000), (-117348137772877680055708376428631/138732139783955508639750000000000), (4195321587031657133/10824799749600000000), (-233963860648897795344465674158631/277464279567911017279500000000000)]
    bernstein := [(651137058764051172459757703159239069/44394284730865762764720000000000000000), (66899328824887289679188387088105181/4035844066442342069520000000000000000), (9803363027423027201142214687033364413/532731416770389153176640000000000000000), (162606896126810291719433195968631377/8071688132884684139040000000000000000), (15489423805888189353099924278495393089/710308555693852204235520000000000000000)]
    reserve := (7333568529/500000000000) }

theorem quarter_004_018_valid : quarter_004_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_018]
  · intro i; fin_cases i <;> norm_num [quarter_004_018]
  · norm_num [quarter_004_018]
  · norm_num [quarter_004_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_018]

def quarter_004_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(948921/4000000), (948921/4000000), (17876777/100000000), (17876777/100000000), (2726251/50000000), (5673947/100000000), (5673947/100000000)]
    cone := fun i => (![![0, 0, 0, (2390087/25000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(135829/2500000), (1/100000000), (6946841/100000000), (1/100000000), (4722541/100000000), (248547/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(-38205824459895276092493593683721731/2215103995126002240380406000000000000), (2174226261904674541561/3774329864756000000000), (-578800848234220463858589873590918731/1107551997563001120190203000000000000), (2174226261904674541561/3774329864756000000000), (-1119395872008545651624686153498115731/2215103995126002240380406000000000000)]
    bernstein := [(131807759260035805127836660909730859192989/5670666227522565735373839360000000000000000), (2880004032427621080640272690690823509701/109051273606203187218727680000000000000000), (31400709981053012220995791623637587661463/1063249917660481075382594880000000000000000), (222293139369345644583281224292628629989/6815704600387699201170480000000000000000), (789846908267669082816339908426844563069/22151039951260022403804060000000000000000)]
    reserve := (726368351/31250000000) }

theorem quarter_004_019_valid : quarter_004_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_019]
  · intro i; fin_cases i <;> norm_num [quarter_004_019]
  · norm_num [quarter_004_019]
  · norm_num [quarter_004_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_019]

def quarter_004_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![(28221143/100000000), (28221143/100000000), (21778857/100000000), (21778857/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, (14110571/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3225537/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5042321/100000000), (1/100000000), (202473/2500000), (1/100000000), (226453/4000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-7655406841808595779855693567/231193535360762349000000000000), (68291581974839/89988000000000), (-72900865062724904181304763567/115596767680381174500000000000), (68291581974839/89988000000000), (-138146323283641212582753833567/231193535360762349000000000000)]
    bernstein := [(85934106388235089063946607440533/2311935353607623490000000000000000), (1412915096781157339992650709037/34250894127520348000000000000000), (201031198985858575754495109516721/4438915878926637100800000000000000), (1687922114991161094443821927/34250894127520348000000000000), (2016360928467476681156479150777/37878748833507303260160000000000)]
    reserve := (37169770449/1000000000000) }

theorem quarter_004_020_valid : quarter_004_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_020]
  · intro i; fin_cases i <;> norm_num [quarter_004_020]
  · norm_num [quarter_004_020]
  · norm_num [quarter_004_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_020]

def quarter_004_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, (38920699/100000000), (610793/2000000), (610793/2000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(389207/20000000), 0, (38920699/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2261523/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1363039/12500000), (1/100000000), (3969329/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-35948678385398736845663/519393622159776000000000), (766854532397/703504000000), (-238100306691402452879903/259696811079888000000000), (766854532397/703504000000), (-440251934997406168914143/519393622159776000000000)]
    bernstein := [(71534110978546154924297/1309191554687041536000000), (4933862248077388824685363/81824472167940096000000000), (375502778455266131363692093/5698490025981542400000000000), (2374536304449554913482944219/33241191818225664000000000000), (6391918330316596240718292817/83102979545564160000000000000)]
    reserve := (13659977931/250000000000) }

theorem quarter_004_021_valid : quarter_004_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_021]
  · intro i; fin_cases i <;> norm_num [quarter_004_021]
  · norm_num [quarter_004_021]
  · norm_num [quarter_004_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_021]

def quarter_004_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, (19300679/50000000), (30699321/100000000), (30699321/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(482517/25000000), 0, (19300679/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9093387/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (5265723/50000000), (1/100000000), (7980163/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-12457616137553962782672239/168085311411396000000000000), (197505913379653/175524100000000), (-77340828940881785540352239/84042655705698000000000000), (197505913379653/175524100000000), (-142224041744209608298032239/168085311411396000000000000)]
    bernstein := [(2079793107036981738272932227841/26893649825823360000000000000000), (4466741517946037403638466698429/53787299651646720000000000000000), (28625626747533343538439367081003/322723797909880320000000000000000), (20289219141514199617669760906869/215149198606586880000000000000000), (42967635789486593528298871278961/430298397213173760000000000000000)]
    reserve := (77333984807/1000000000000) }

theorem quarter_004_022_valid : quarter_004_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_022]
  · intro i; fin_cases i <;> norm_num [quarter_004_022]
  · norm_num [quarter_004_022]
  · norm_num [quarter_004_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_022]

def quarter_004_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, (38275717/100000000), (15431071/50000000), (15431071/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(956893/50000000), 0, (38275717/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (571351/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2031009/20000000), (1/100000000), (1002811/12500000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-218167323388092266674921/2715624221732000000000000), (590635306602907/507752250000000), (-1257591965281685085114921/1357812110866000000000000), (590635306602907/507752250000000), (-2297016607175277903554921/2715624221732000000000000)]
    bernstein := [(2091953746548771609039760825637/20855994022901760000000000000000), (92203895318036779863681021097/868999750954240000000000000000), (3037513232078093544579758099/27156242217320000000000000000), (798095800879717535017567589/6789060554330000000000000000), (156845308882266342096695053/1272948853936875000000000000)]
    reserve := (100304677123/1000000000000) }

theorem quarter_004_023_valid : quarter_004_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_023]
  · intro i; fin_cases i <;> norm_num [quarter_004_023]
  · norm_num [quarter_004_023]
  · norm_num [quarter_004_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_023]

def quarter_004_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, (3794859/10000000), (6205141/20000000), (6205141/20000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1897429/100000000), 0, (3794859/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1838013/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (9776501/100000000), (1/100000000), (4032503/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-83301152114362114265431159/946170470688072000000000000), (23547635170119/19553002000000), (-442359504736848736450231159/473085235344036000000000000), (23547635170119/19553002000000), (-801417857359335358635031159/946170470688072000000000000)]
    bernstein := [(18287151400480523964969734129/147839136045011250000000000000), (16137103192512857152870544263/124496114564220000000000000000), (3846156684558971687814771513047/28385114120642160000000000000000), (2252285158014844111752443838931/15935502664220160000000000000000), (356393582469622046871897317113001/2422196404961464320000000000000000)]
    reserve := (61848140789/500000000000) }

theorem quarter_004_024_valid : quarter_004_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_024]
  · intro i; fin_cases i <;> norm_num [quarter_004_024]
  · norm_num [quarter_004_024]
  · norm_num [quarter_004_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_024]

def quarter_004_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, (37623949/100000000), (1247521/4000000), (1247521/4000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1881197/100000000), 0, (37623949/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4619073/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (9397071/100000000), (1/100000000), (5067/62500), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-10992466565673409051661/112865087424000000000000), (46936666480429/37588284000000), (-53456769496884582811661/56432543712000000000000), (46936666480429/37588284000000), (-95921072428095756571661/112865087424000000000000)]
    bernstein := [(42662276558871550727138640979/288934623805440000000000000000), (13326002306016362546608994513/86680387141632000000000000000), (1385004817804155829471783961/8668038714163200000000000000), (143709844023331523083573841/866803871416320000000000000), (14888946021165516004689913/86680387141632000000000000)]
    reserve := (147653735633/1000000000000) }

theorem quarter_004_025_valid : quarter_004_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_025]
  · intro i; fin_cases i <;> norm_num [quarter_004_025]
  · norm_num [quarter_004_025]
  · norm_num [quarter_004_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_025]

def quarter_004_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, (9326257/25000000), (15673743/50000000), (15673743/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1865251/100000000), 0, (9326257/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9285379/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4508941/50000000), (1/100000000), (8148651/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5319720875589001917391239/48989048784788000000000000), (146177355369951/112723525000000), (-23595099241687825058031239/24494524392394000000000000), (146177355369951/112723525000000), (-41870477607786648198671239/48989048784788000000000000)]
    bernstein := [(2161135466766834344685131929/12541196488905728000000000000), (22398992831913094271639828227/125411964889057280000000000000), (695476964305009053854877921379/3762358946671718400000000000000), (2396228917672216159445022723451/12541196488905728000000000000000), (24738338635393261459885119609001/125411964889057280000000000000000)]
    reserve := (34464581887/200000000000) }

theorem quarter_004_026_valid : quarter_004_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_026]
  · intro i; fin_cases i <;> norm_num [quarter_004_026]
  · norm_num [quarter_004_026]
  · norm_num [quarter_004_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_026]

def quarter_004_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, (18497209/50000000), (31502791/100000000), (31502791/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1849721/100000000), 0, (18497209/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4665691/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8639939/100000000), (1/100000000), (4094511/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8620129557683961896953993/70752650549658000000000000), (582713709210319/431996950000000), (-34794660848103739987393993/35376325274829000000000000), (582713709210319/431996950000000), (-60969192138523518077833993/70752650549658000000000000)]
    bernstein := [(35836121135881466594900262738887/181126785407124480000000000000000), (9254003883535920909843599554351/45281696351781120000000000000000), (7160807188386803798463834659969/33961272263835840000000000000000), (615019894650041213663799532379/2830106021986320000000000000000), (158309152474742025727223529167/707526505496580000000000000000)]
    reserve := (39570206091/200000000000) }

theorem quarter_004_027_valid : quarter_004_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_027]
  · intro i; fin_cases i <;> norm_num [quarter_004_027]
  · norm_num [quarter_004_027]
  · norm_num [quarter_004_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_027]

def quarter_004_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, (18347079/50000000), (31652921/100000000), (31652921/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(458677/25000000), 0, (18347079/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9375851/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1652827/20000000), (1/100000000), (514253/6250000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-22416600006866766580804681/163194478700352000000000000), (15695638977507/11167750000000), (-82299439868450276016964681/81597239350176000000000000), (15695638977507/11167750000000), (-142182279730033785453124681/163194478700352000000000000)]
    bernstein := [(366187341137210436331360385039/1631944787003520000000000000000), (1509042595285333601704661449469/6527779148014080000000000000000), (18638282272836485630623218590897/78333349776168960000000000000000), (25555221205042992801932361897529/104444466368225280000000000000000), (105029309429560144952754414821159/417777865472901120000000000000000)]
    reserve := (56096772399/250000000000) }

theorem quarter_004_028_valid : quarter_004_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_028]
  · intro i; fin_cases i <;> norm_num [quarter_004_028]
  · norm_num [quarter_004_028]
  · norm_num [quarter_004_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_028]

def quarter_004_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, (36405811/100000000), (6359419/20000000), (6359419/20000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1820291/100000000), 0, (36405811/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9418557/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7891253/100000000), (1/100000000), (330621/4000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-270347461424974101335953/1739342638742000000000000), (231519806183809/157825060000000), (-903569255127799398955953/869671319371000000000000), (231519806183809/157825060000000), (-1536791048830624696575953/1739342638742000000000000)]
    bernstein := [(1122451276963051263800119143967/4452717155179520000000000000000), (577020514566640413942499476413/2226358577589760000000000000000), (296388138174701441262521396007/1113179288794880000000000000000), (152123923059908922026598318773/556589644397440000000000000000), (78022595281454633229113299247/278294822198720000000000000000)]
    reserve := (63020580347/250000000000) }

theorem quarter_004_029_valid : quarter_004_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_029]
  · intro i; fin_cases i <;> norm_num [quarter_004_029]
  · norm_num [quarter_004_029]
  · norm_num [quarter_004_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_029]

def quarter_004_030 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 0]
    lambda := ![0, (18065267/50000000), (31934733/100000000), (31934733/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1806527/100000000), 0, (18065267/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4729663/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7521979/100000000), (1/100000000), (1037663/12500000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-33033068582385389662375369/187326703081848000000000000), (576909478218711/376098950000000), (-100715206730451529130695369/93663351540924000000000000), (576909478218711/376098950000000), (-168397344878517668599015369/187326703081848000000000000)]
    bernstein := [(8424924075555363969161956994231/29972272493095680000000000000000), (3459195350074546588027607016739/11988908997238272000000000000000), (4257917371100188346554632722669/14386690796685926400000000000000), (581950384830825093161923369403/1918225439558123520000000000000), (238462740826374681457846458599/767290175823249408000000000000)]
    reserve := (28109060057/100000000000) }

theorem quarter_004_030_valid : quarter_004_030.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_004_030]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_004_030]
  · intro i; fin_cases i <;> norm_num [quarter_004_030]
  · norm_num [quarter_004_030]
  · norm_num [quarter_004_030, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_004_030, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_004_030, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_004_030, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_004_030]

def quarterTable004 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 0, 0, 2, 0]
  rows := [quarter_004_000, quarter_004_001, quarter_004_002, quarter_004_003, quarter_004_004, quarter_004_005, quarter_004_006, quarter_004_007, quarter_004_008, quarter_004_009, quarter_004_010, quarter_004_011, quarter_004_012, quarter_004_013, quarter_004_014, quarter_004_015, quarter_004_016, quarter_004_017, quarter_004_018, quarter_004_019, quarter_004_020, quarter_004_021, quarter_004_022, quarter_004_023, quarter_004_024, quarter_004_025, quarter_004_026, quarter_004_027, quarter_004_028, quarter_004_029, quarter_004_030]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_004_000_valid
    · exact quarter_004_001_valid
    · exact quarter_004_002_valid
    · exact quarter_004_003_valid
    · exact quarter_004_004_valid
    · exact quarter_004_005_valid
    · exact quarter_004_006_valid
    · exact quarter_004_007_valid
    · exact quarter_004_008_valid
    · exact quarter_004_009_valid
    · exact quarter_004_010_valid
    · exact quarter_004_011_valid
    · exact quarter_004_012_valid
    · exact quarter_004_013_valid
    · exact quarter_004_014_valid
    · exact quarter_004_015_valid
    · exact quarter_004_016_valid
    · exact quarter_004_017_valid
    · exact quarter_004_018_valid
    · exact quarter_004_019_valid
    · exact quarter_004_020_valid
    · exact quarter_004_021_valid
    · exact quarter_004_022_valid
    · exact quarter_004_023_valid
    · exact quarter_004_024_valid
    · exact quarter_004_025_valid
    · exact quarter_004_026_valid
    · exact quarter_004_027_valid
    · exact quarter_004_028_valid
    · exact quarter_004_029_valid
    · exact quarter_004_030_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
