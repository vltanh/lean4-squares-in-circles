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

def quarter_016_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_016_000_valid : quarter_016_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_000]
  · intro i; fin_cases i <;> norm_num [quarter_016_000]
  · norm_num [quarter_016_000]
  · norm_num [quarter_016_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_000]

def quarter_016_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_016_001_valid : quarter_016_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_001]
  · intro i; fin_cases i <;> norm_num [quarter_016_001]
  · norm_num [quarter_016_001]
  · norm_num [quarter_016_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_001]

def quarter_016_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_016_002_valid : quarter_016_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_002]
  · intro i; fin_cases i <;> norm_num [quarter_016_002]
  · norm_num [quarter_016_002]
  · norm_num [quarter_016_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_002]

def quarter_016_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_016_003_valid : quarter_016_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_003]
  · intro i; fin_cases i <;> norm_num [quarter_016_003]
  · norm_num [quarter_016_003]
  · norm_num [quarter_016_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_003]

def quarter_016_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_016_004_valid : quarter_016_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_004]
  · intro i; fin_cases i <;> norm_num [quarter_016_004]
  · norm_num [quarter_016_004]
  · norm_num [quarter_016_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_004]

def quarter_016_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_016_005_valid : quarter_016_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_005]
  · intro i; fin_cases i <;> norm_num [quarter_016_005]
  · norm_num [quarter_016_005]
  · norm_num [quarter_016_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_005]

def quarter_016_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_016_006_valid : quarter_016_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_006]
  · intro i; fin_cases i <;> norm_num [quarter_016_006]
  · norm_num [quarter_016_006]
  · norm_num [quarter_016_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_006]

def quarter_016_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_016_007_valid : quarter_016_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_007]
  · intro i; fin_cases i <;> norm_num [quarter_016_007]
  · norm_num [quarter_016_007]
  · norm_num [quarter_016_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_007]

def quarter_016_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_016_008_valid : quarter_016_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_008]
  · intro i; fin_cases i <;> norm_num [quarter_016_008]
  · norm_num [quarter_016_008]
  · norm_num [quarter_016_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_008]

def quarter_016_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1067647938911762121/3859681000000000000), (-13528061/3859681), (-8309344188911762121/1929840500000000000), (-13528061/3859681), (-15551040438911762121/3859681000000000000)]
    bernstein := [(100068034278401520636999/617548960000000000000000), (36328949888069554679293/247019584000000000000000), (265685575963521009711/2016486400000000000000), (917720443345976065601/7904626688000000000000), (63294346623912201551/632370135040000000000)]
    reserve := (100090663863/1000000000000) }

theorem quarter_016_009_valid : quarter_016_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_009]
  · intro i; fin_cases i <;> norm_num [quarter_016_009]
  · norm_num [quarter_016_009]
  · norm_num [quarter_016_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_009]

def quarter_016_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (32317707/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(20098469/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-24605763504485237/100492345000000000), (-64635414/20098469), (-205892376004485237/50246172500000000), (-64635414/20098469), (-387178988504485237/100492345000000000)]
    bernstein := [(1621018638741994947/16464665804800000000), (8644294675777045439/102904161280000000000), (44514715284066379727/643151008000000000000), (43476776959806276103/803938760000000000000), (38785551465746097363/1004923450000000000000)]
    reserve := (38595528311/1000000000000) }

theorem quarter_016_010_valid : quarter_016_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_010]
  · intro i; fin_cases i <;> norm_num [quarter_016_010]
  · norm_num [quarter_016_010]
  · norm_num [quarter_016_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_010]

def quarter_016_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(2139611/10000000), (4004329/20000000), (12209249/100000000), (12209249/100000000), (1996027/50000000), (1083603/25000000), (25837281/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (21502869/100000000), 0, 0]] i.1) i.2
    mu := ![(3915401/50000000), (548597/50000000), (1185101/20000000), (1/100000000), (811439/25000000), (744481/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-9025871157369706901457298316453301585689/219683022987529076639934493489000000000000), (-86638838179549/78308020000000), (-494648078575731730621647695019278998550689/109841511493764538319967246744500000000000), (-86638838179549/78308020000000), (-980270285994093754341838091722104695515689/219683022987529076639934493489000000000000)]
    bernstein := [(55315998999112152119019445727646341317956511/2196830229875290766399344934890000000000000000), (209122654716459402311734954819237850162035633/8787320919501163065597379739560000000000000000), (2315015953362294072626865689521764419481076697/105447851034013956787168556874720000000000000000), (2762772958148262280051879549330699717058703797/140597134712018609049558075832960000000000000000), (9497380416133688112351199213950438208933545991/562388538848074436198232303331840000000000000000)]
    reserve := (16887578177/1000000000000) }

theorem quarter_016_011_valid : quarter_016_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_011]
  · intro i; fin_cases i <;> norm_num [quarter_016_011]
  · norm_num [quarter_016_011]
  · norm_num [quarter_016_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_011]

def quarter_016_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(21052969/100000000), (20099907/100000000), (3132807/25000000), (3132807/25000000), (4193047/100000000), (2297561/50000000), (49993/200000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (10200689/50000000), 0, 0]] i.1) i.2
    mu := ![(7841491/100000000), (813937/100000000), (5985039/100000000), (1/100000000), (834737/25000000), (1228/78125), (1/100000000)]
    alternative := .zero
    polynomial := [(-24735028138659115123404290668968067119103/835339800845927369682079894784000000000000), (-60105501377941/56010650000000), (-2404990505954023004504533809554591044399103/417669900422963684841039947392000000000000), (-60105501377941/56010650000000), (-4785245983769386893885663328440214021679103/835339800845927369682079894784000000000000)]
    bernstein := [(40105876444506047963121019853946824699666946257/2138469890165574066386124530647040000000000000000), (18597219341010187053173265077118410121466388219/1069234945082787033193062265323520000000000000000), (24758292535543275272743544054897932540622179819/1603852417624180549789593397985280000000000000000), (3445140272080491788386600728843576053500596691/267308736270696758298265566330880000000000000000), (1302827591238825882612130373967686840317758497/133654368135348379149132783165440000000000000000)]
    reserve := (9747736713/1000000000000) }

theorem quarter_016_012_valid : quarter_016_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_012]
  · intro i; fin_cases i <;> norm_num [quarter_016_012]
  · norm_num [quarter_016_012]
  · norm_num [quarter_016_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_012]

def quarter_016_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(20734917/100000000), (4035933/20000000), (1608259/12500000), (1608259/12500000), (176217/4000000), (4873593/100000000), (4814851/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9600331/50000000), 0, 0]] i.1) i.2
    mu := ![(3913727/50000000), (534949/100000000), (1511803/25000000), (1/100000000), (429537/12500000), (207501/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3561495857290880450424603420129957265777/188073508242193518838723667502000000000000), (-163017695661531/156549080000000), (-784370676310126117987818476999277154315777/94036754121096759419361833751000000000000), (-163017695661531/156549080000000), (-1565179856762961355525212350578424351365777/188073508242193518838723667502000000000000)]
    bernstein := [(371773554820291654121421783671215841674692623/30091761318750963014195786800320000000000000000), (221411153216742870286140297705526755341603941/20061174212500642009463857866880000000000000000), (456707198472805168705165481998548886232217467/51585876546430222310049920229120000000000000000), (465957885887167740224173388072735721667153141/80244696850002568037855431467520000000000000000), (912914798640822438062089150467456312655027823/481468181100015408227132588805120000000000000000)]
    reserve := (189610619/100000000000) }

theorem quarter_016_013_valid : quarter_016_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_013]
  · intro i; fin_cases i <;> norm_num [quarter_016_013]
  · norm_num [quarter_016_013]
  · norm_num [quarter_016_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_013]

def quarter_016_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(4102889/20000000), (2024279/10000000), (525017/4000000), (525017/4000000), (17858/390625), (5093479/100000000), (5831697/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (18233309/100000000), 0, 0]] i.1) i.2
    mu := ![(3875691/50000000), (133187/50000000), (6096071/100000000), (1/100000000), (70239/2000000), (1729401/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-36310404097460578363694470886386681/3947119204761292063099700325000000000), (-13205921758737/12918970000000), (-15862143867740215143550986087938425403/986779801190323015774925081250000000), (-13205921758737/12918970000000), (-63412265066863399995840249880867314931/3947119204761292063099700325000000000)]
    bernstein := [(63852265507432175416477861419291624045869/10104625164188907681535232832000000000000000), (37949699859129855100902150280310226240423/6736416776125938454356821888000000000000000), (549254999143798789884523806439586048820407/121255501970266892178422793984000000000000000), (81053997256911277072289010930130217780823/26945667104503753817427287552000000000000000), (172727467107964750281710614757671703208269/161674002627022522904563725312000000000000000)]
    reserve := (534184421/500000000000) }

theorem quarter_016_014_valid : quarter_016_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_014]
  · intro i; fin_cases i <;> norm_num [quarter_016_014]
  · norm_num [quarter_016_014]
  · norm_num [quarter_016_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_014]

def quarter_016_015 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(5102609/25000000), (4055211/20000000), (6628819/50000000), (6628819/50000000), (4656793/100000000), (520671/10000000), (22934729/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (886401/5000000), 0, 0]] i.1) i.2
    mu := ![(1927343/25000000), (132909/100000000), (47823/781250), (1/100000000), (887647/25000000), (1765067/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-302402095888461486092523403522108220259/68243166755615871968326206752000000000000), (-195184779951691/192734300000000), (-1078408747139408769176544876647209237500259/34121583377807935984163103376000000000000), (-195184779951691/192734300000000), (-2156515092182929076866997229890896366780259/68243166755615871968326206752000000000000)]
    bernstein := [(9198095617057064547541048499350989748560464541/2795240110310026115822641428561920000000000000000), (16449830811908144877942086915287696972874966941/5590480220620052231645282857123840000000000000000), (80120830110871552217371679268119578814460830423/33542881323720313389871697142743040000000000000000), (36429229713789506348423619464972785517307754141/22361920882480208926581131428495360000000000000000), (29690096416399053452828659877186229881440118941/44723841764960417853162262856990720000000000000000)]
    reserve := (663853891/1000000000000) }

theorem quarter_016_015_valid : quarter_016_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_015]
  · intro i; fin_cases i <;> norm_num [quarter_016_015]
  · norm_num [quarter_016_015]
  · norm_num [quarter_016_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_015]

def quarter_016_016 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(2545007/12500000), (20293221/100000000), (13324357/100000000), (13324357/100000000), (939967/20000000), (5264093/100000000), (22734081/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4367497/25000000), 0, 0]] i.1) i.2
    mu := ![(768739/10000000), (13277/20000000), (6134211/100000000), (1/100000000), (3570101/100000000), (2853/160000), (1/100000000)]
    alternative := .zero
    polynomial := [(-18368674708097374230647022560131747/8857014548857037737183832625000000000), (-193717742658729/192184750000000), (-277656135712949504778928060347348828997/4428507274428518868591916312500000000), (-193717742658729/192184750000000), (-555293902751190912183625473672137526247/8857014548857037737183832625000000000)]
    bernstein := [(10314495883066089463547168690112807085587353/5804533054738948251440796549120000000000000000), (2066060547291941434396532446787167633196017/1289896234386432944764621455360000000000000000), (92253068194125821193314256456083985083739659/69654396656867379017289558589440000000000000000), (4876418059177252323896728983841541767901617/5159584937545731779058485821440000000000000000), (381154892963491577633494665445529375863081/821880786511709486929670307840000000000000000)]
    reserve := (231879671/500000000000) }

theorem quarter_016_016_valid : quarter_016_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_016]
  · intro i; fin_cases i <;> norm_num [quarter_016_016]
  · norm_num [quarter_016_016]
  · norm_num [quarter_016_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_016]

def quarter_016_017 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/320), (-1/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(254191/1250000), (20301951/100000000), (6678933/50000000), (6678933/50000000), (1180367/25000000), (5292969/100000000), (22632599/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1733963/10000000), 0, 0]] i.1) i.2
    mu := ![(3838079/50000000), (1327/4000000), (1228141/20000000), (1/100000000), (715981/20000000), (1792209/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1034380476889548985320097782214905209/1146634946978790475663992591000000000000), (-27568650177187/27414850000000), (-71606966456572609147299063281602227843209/573317473489395237831996295500000000000), (-27568650177187/27414850000000), (-143212898532668328745612806465422240781209/1146634946978790475663992591000000000000)]
    bernstein := [(12272575642753350322552816530891360940976575591/12023338861632322018098466951004160000000000000000), (393537554717564885014687124099032152586767263/421871539004642877828016384245760000000000000000), (114576350182416271546165584519071669591068555573/144280066339587864217181603412049920000000000000000), (1020239807851375013736244658367165864519720863/1687486156018571511312065536983040000000000000000), (70069697228783046332018392312420683332841765991/192373421786117152289575471216066560000000000000000)]
    reserve := (364237931/1000000000000) }

theorem quarter_016_017_valid : quarter_016_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_017]
  · intro i; fin_cases i <;> norm_num [quarter_016_017]
  · norm_num [quarter_016_017]
  · norm_num [quarter_016_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_017]

def quarter_016_018 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/640), (-1/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(20322997/100000000), (4061271/20000000), (6687329/50000000), (6687329/50000000), (591539/12500000), (1326863/25000000), (352837/1562500)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4318529/25000000), 0, 0]] i.1) i.2
    mu := ![(7670481/100000000), (16583/100000000), (191999/3125000), (1/100000000), (3584819/100000000), (449191/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-157026271756020848608491546479734619/493893714888735765360763272000000000000), (-385222079566403/383524050000000), (-61567097400504044648653402516727644894619/246946857444367882680381636000000000000), (-385222079566403/383524050000000), (-123134037774736333276458196541908810054619/493893714888735765360763272000000000000)]
    bernstein := [(230811930348888369858615101562501383977264555851/359066999881665222436589878032465920000000000000000), (430019313916031630596578349016233572276964165451/718133999763330444873179756064931840000000000000000), (6843634717034865746197208684517979459844992164259/12926411995739948007717235609168773120000000000000000), (178383858588627324787995808092654557848370324893/410362285579045968498959860608532480000000000000000), (5422290385060368307291290320023931502631607760353/17235215994319930676956314145558364160000000000000000)]
    reserve := (62921061/200000000000) }

theorem quarter_016_018_valid : quarter_016_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_018]
  · intro i; fin_cases i <;> norm_num [quarter_016_018]
  · norm_num [quarter_016_018]
  · norm_num [quarter_016_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_018]

def quarter_016_019 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/1280), (-1/2560)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(10158441/50000000), (10154283/50000000), (13383063/100000000), (13383063/100000000), (236887/5000000), (1062941/20000000), (22555981/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4310319/25000000), 0, 0]] i.1) i.2
    mu := ![(1916907/25000000), (8291/100000000), (6145603/100000000), (1/100000000), (1793639/50000000), (449761/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2073587790386664889209134804467799119/78793300494317783082633318069000000000000), (-128284043829023/127793800000000), (-19623761150504289866978640945425426656229119/39396650247158891541316659034500000000000), (-128284043829023/127793800000000), (-39247520227420789347292392681716048844659119/78793300494317783082633318069000000000000)]
    bernstein := [(96006105503810372517266267759907209804532252761681/211509155479372195106957604166450544640000000000000000), (60898295790155547914850878658748948419549382784027/141006103652914796737971736110967029760000000000000000), (23444508052367887136254836784779652457518561984601/59025810831452705611243982558079221760000000000000000), (197312634008486658618959750918600970886951820134427/564024414611659186951886944443868119040000000000000000), (980731114735573044112004887871213865588634218944081/3384146487669955121711321666663208714240000000000000000)]
    reserve := (144900807/500000000000) }

theorem quarter_016_019_valid : quarter_016_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_019]
  · intro i; fin_cases i <;> norm_num [quarter_016_019]
  · norm_num [quarter_016_019]
  · norm_num [quarter_016_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_019]

def quarter_016_020 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/2560), 0⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(4062563/20000000), (5077511/25000000), (1338867/10000000), (1338867/10000000), (2370681/50000000), (664943/12500000), (4507779/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17219351/100000000), 0, 0]] i.1) i.2
    mu := ![(3833357/50000000), (4071/100000000), (3073347/50000000), (1/100000000), (3588919/100000000), (900283/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(6146817398377718042666201241647590649/51655125170597833848858252831000000000000), (-769251001790257/766671400000000), (-26185226504521177156422240085273425547159351/25827562585298916924429126415500000000000), (-769251001790257/766671400000000), (-52370459155859752690562522836748092741909351/51655125170597833848858252831000000000000)]
    bernstein := [(790333996467884812207974048087577507892631640503449/2218570732785041171492880028488444149760000000000000000), (29084186318321695082772256725661571088925065919/86662919249415670761440626112829849600000000000000), (293689204495580134273526330747282382879899849/1015581084954089891735632337259724800000000000000), (2869308453815924155750001433622010147519/13223712043673045465307712724736000000000000), (6146817398377718042666201241647590649/51655125170597833848858252831000000000000)]
    reserve := (118997241/1000000000000) }

theorem quarter_016_020_valid : quarter_016_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_020]
  · intro i; fin_cases i <;> norm_num [quarter_016_020]
  · norm_num [quarter_016_020]
  · norm_num [quarter_016_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_020]

def quarter_016_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(253919/1250000), (20313527/100000000), (13387717/100000000), (13387717/100000000), (2369939/50000000), (1063467/20000000), (11270153/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1587/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4305743/25000000), 0, 0]] i.1) i.2
    mu := ![(7673053/100000000), (4011/100000000), (6147297/100000000), (1/100000000), (3588567/100000000), (17999/1000000), (1/100000000)]
    alternative := .zero
    polynomial := [(16659790497811249772151177459649319/135778805191167160746936548700000000000), (337417644149542241/512943593050000000), (-69873099608309942113125810549163568212681/67889402595583580373468274350000000000), (337417644149542241/512943593050000000), (-139746215876410382037501393249504596074681/135778805191167160746936548700000000000)]
    bernstein := [(16659790497811249772151177459649319/135778805191167160746936548700000000000), (2182678897576151306371255720681180091/8689843532234698287803939116800000000000), (183500176804545043665421600697797361016119/667379983275624828503342524170240000000000000), (67380847870248353996356745988784937008451/347254625444227553042389606072320000000000000), (74882957083584993576170332664351883209458159/8889718411372225357885173915451392000000000000000)]
    reserve := (4211773/500000000000) }

theorem quarter_016_021_valid : quarter_016_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_021]
  · intro i; fin_cases i <;> norm_num [quarter_016_021]
  · norm_num [quarter_016_021]
  · norm_num [quarter_016_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_021]

def quarter_016_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(406379/2000000), (10159503/50000000), (6690109/50000000), (6690109/50000000), (47333/1000000), (5308097/100000000), (2256021/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(47623/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1078257/6250000), 0, 0]] i.1) i.2
    mu := ![(1536733/20000000), (1003/25000000), (614741/10000000), (1/100000000), (1793113/50000000), (1797051/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1206978556581692474002943624849769091/1526615247636233380039214608500000000000), (698693511608589237/308268639800000000), (-785838753491467480057036348600566486556591/763307623818116690019607304250000000000), (698693511608589237/308268639800000000), (-1571676300004378378421598694257508123344091/1526615247636233380039214608500000000000)]
    bernstein := [(1441335424532915816997527575805631678334081507109/4097976601357852294932478713145589760000000000000000), (19293145172055489893550055347202152909649116359/40176241189782865636592928560250880000000000000000), (221281510225572498574784559036672167292115241561/439068921574055603028479862122741760000000000000000), (72229784322973146669550689946101700906182171703/170749025056577178955519946381066240000000000000000), (60785059772674138455090469564142148120604348709/256123537584865768433279919571599360000000000000000)]
    reserve := (237327113/1000000000000) }

theorem quarter_016_022_valid : quarter_016_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_022]
  · intro i; fin_cases i <;> norm_num [quarter_016_022]
  · norm_num [quarter_016_022]
  · norm_num [quarter_016_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_022]

def quarter_016_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(20326991/100000000), (10163607/50000000), (6684503/50000000), (6684503/50000000), (4723471/100000000), (5294299/100000000), (5647503/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(95283/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8647857/50000000), 0, 0]] i.1) i.2
    mu := ![(3851267/50000000), (4013/50000000), (1229517/20000000), (1/100000000), (3582727/100000000), (448199/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-11289747107299994951341563669571910999/6102698599906334166596937442200000000000), (3506544694872727533/1545513447100000000), (-1572272473730581050078360633787837033613999/3051349299953167083298468721100000000000), (3506544694872727533/1545513447100000000), (-3144533657714054800161769926012004495316999/6102698599906334166596937442200000000000)]
    bernstein := [(447575649238083305641898472783759783059140702201/1023862925935261480811768044062769152000000000000000), (16928489185747668630358434680065517005747101781/24377688712744320971708762953875456000000000000000), (81401906447901150070566784938588823938624620029/109699599207349444372689433292439552000000000000000), (3534752757278569485272390849008855566135338581/6094422178186080242927190738468864000000000000000), (13328405077662600022176567854393616361365367801/63991432870953842550735502753923072000000000000000)]
    reserve := (20828421/100000000000) }

theorem quarter_016_023_valid : quarter_016_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_023]
  · intro i; fin_cases i <;> norm_num [quarter_016_023]
  · norm_num [quarter_016_023]
  · norm_num [quarter_016_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_023]

def quarter_016_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/320), (1/160)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(20342701/100000000), (4068719/20000000), (13346713/100000000), (13346713/100000000), (4703941/100000000), (1316727/25000000), (22649429/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(190717/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17382521/100000000), 0, 0]] i.1) i.2
    mu := ![(387009/5000000), (251/1562500), (384247/6250000), (1/100000000), (3575773/100000000), (1784347/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-15160249771253309340576887187994092989/3810434583288817963116188208000000000000), (7065442840889159051/3108456288000000000), (-491703722834536270981911860355000931081739/1905217291644408981558094104000000000000), (7065442840889159051/3108456288000000000), (-983392285419301288654483143822813868070489/3810434583288817963116188208000000000000)]
    bernstein := [(24138488163003172526539165738367065788848262311/39955302536066555844925201663918080000000000000000), (7456702162376274835009909069973902341918493037/6659217089344425974154200277319680000000000000000), (36419139812974698355354372995536376893651089333/29966476902049916883693901247938560000000000000000), (1483088249232894352027985003437505797130331437/1664804272336106493538550069329920000000000000000), (121765286756297399255449454657756437054804237/832402136168053246769275034664960000000000000000)]
    reserve := (36570451/250000000000) }

theorem quarter_016_024_valid : quarter_016_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_024]
  · intro i; fin_cases i <;> norm_num [quarter_016_024]
  · norm_num [quarter_016_024]
  · norm_num [quarter_016_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_024]

def quarter_016_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/160), (1/80)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(20372633/100000000), (4075243/20000000), (2660531/20000000), (2660531/20000000), (4665399/100000000), (104259/2000000), (5691873/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(19101/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8777271/50000000), 0, 0]] i.1) i.2
    mu := ![(781509/10000000), (32177/100000000), (6148753/100000000), (1/100000000), (3562041/100000000), (441923/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-134283948823620874665310644259603508209/16226350090436232014293509829800000000000), (4779944966670062579/2095551257750000000), (-1050513548140694229704753708544539894639209/8113175045218116007146754914900000000000), (4779944966670062579/2095551257750000000), (-2100892812332564838534842106444820185770209/16226350090436232014293509829800000000000)]
    bernstein := [(9815361805343754393702301369986767824022536991/10634100795268289012887394602057728000000000000000), (3470849387646622754069728134610059702748025397/1772350132544714835481232433676288000000000000000), (188499796614430744404871548057259620378011303/87643687873090294062258746720256000000000000000), (664724099684127946436240665335768838790738997/443087533136178708870308108419072000000000000000), (4286514983347504391578494068564069403938591/664631299704268063305462162628608000000000000000)]
    reserve := (6449463/1000000000000) }

theorem quarter_016_025_valid : quarter_016_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_025]
  · intro i; fin_cases i <;> norm_num [quarter_016_025]
  · norm_num [quarter_016_025]
  · norm_num [quarter_016_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_025]

def quarter_016_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/80), (3/160)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(816379/4000000), (20419443/100000000), (13245023/100000000), (13245023/100000000), (2307541/50000000), (2571349/50000000), (22923257/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2492/390625), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17780559/100000000), 0, 0]] i.1) i.2
    mu := ![(3949209/50000000), (32241/100000000), (1229993/20000000), (1/100000000), (1772049/50000000), (1745987/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-126510514837344149160778502479325581739/4894437637860133625820218529000000000000), (602913140564115157/154335087720000000), (-317578215259738357384376083399461389236739/2447218818930066812910109264500000000000), (602913140564115157/154335087720000000), (-635029920004639370619591388296443452891739/4894437637860133625820218529000000000000)]
    bernstein := [(543575174297130702803896554197938437129409061/200476165646751073313596150947840000000000000000), (25466950196870393489482870186967192769869437/6795802225313595705545632235520000000000000000), (9475587406747044562502202901426792147103847847/2405713987761012879763153811374080000000000000000), (29767925666433204252385569193415122724480311/9061069633751460940727509647360000000000000000), (5730447642710267745271037220900225113023397941/3207618650348017173017538415165440000000000000000)]
    reserve := (1786511511/1000000000000) }

theorem quarter_016_026_valid : quarter_016_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_026]
  · intro i; fin_cases i <;> norm_num [quarter_016_026]
  · norm_num [quarter_016_026]
  · norm_num [quarter_016_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_026]

def quarter_016_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/160), (1/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(10221417/50000000), (2557801/12500000), (3297171/25000000), (3297171/25000000), (142687/3125000), (5074357/100000000), (23077049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(447401/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4500673/25000000), 0, 0]] i.1) i.2
    mu := ![(3990437/50000000), (16151/50000000), (768919/12500000), (1/100000000), (176329/5000000), (34497/2000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3235526425682175588559813677898093703/60288646949790149657109637800000000000), (35696969477731272039/6444954798700000000), (-3920826218557092826183083044217788719703/30144323474895074828554818900000000000), (35696969477731272039/6444954798700000000), (-7838416910688503476777606274757679345703/60288646949790149657109637800000000000)]
    bernstein := [(176908526786917245619246542805985906364895657/39510767665014472479283372228608000000000000000), (54468939353206257186827653476155820547162819/9877691916253618119820843057152000000000000000), (42261537537416096224127885666829940510875619/7408268937190213589865632292864000000000000000), (3116495263080491902827110883617331555149291/617355744765851132488802691072000000000000000), (547032228901418081320965547162934556564697/154338936191462783122200672768000000000000000)]
    reserve := (3544356611/1000000000000) }

theorem quarter_016_027_valid : quarter_016_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_027]
  · intro i; fin_cases i <;> norm_num [quarter_016_027]
  · norm_num [quarter_016_027]
  · norm_num [quarter_016_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_027]

def quarter_016_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (3/80)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(2560801/12500000), (20526459/100000000), (6553329/50000000), (6553329/50000000), (561827/12500000), (4975377/100000000), (1456489/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(320413/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (143191/781250), 0, 0]] i.1) i.2
    mu := ![(1625243/20000000), (64781/100000000), (6153783/100000000), (1/100000000), (350111/10000000), (8471/500000), (1/100000000)]
    alternative := .zero
    polynomial := [(-202192472433368728072323877314903591353/3843072371036130814078050018000000000000), (51847712533000368897/13160608347875000000), (-125830604556493745036609051332366883991353/1921536185518065407039025009000000000000), (51847712533000368897/13160608347875000000), (-251459016640554121345145778787418864391353/3843072371036130814078050018000000000000)]
    bernstein := [(49057594075645934364088873506913099447439047/9838265269852494884039808046080000000000000000), (139232495528722930542913736137778728283201941/19676530539704989768079616092160000000000000000), (880923886323129311356456201099248357255575869/118059183238229938608477696552960000000000000000), (483418522094529878928174705654504365528809469/78706122158819959072318464368640000000000000000), (490223978863362814000220470961570361224914807/157412244317639918144636928737280000000000000000)]
    reserve := (3114268403/1000000000000) }

theorem quarter_016_028_valid : quarter_016_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_028]
  · intro i; fin_cases i <;> norm_num [quarter_016_028]
  · norm_num [quarter_016_028]
  · norm_num [quarter_016_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_028]

def quarter_016_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/80), (1/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(20532617/100000000), (20611369/100000000), (13002063/100000000), (13002063/100000000), (2201843/50000000), (38799/800000), (2949791/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1800049/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (18748453/100000000), 0, 0]] i.1) i.2
    mu := ![(2071297/25000000), (32497/50000000), (1231547/20000000), (1/100000000), (1734341/50000000), (1655271/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-25958180957265664068229158699283884533221/237979876360536040641375731553000000000000), (4431111800065969037/791893395400000000), (-7830090788955365270464429125885601777815721/118989938180268020320687865776500000000000), (4431111800065969037/791893395400000000), (-15634223396953464876860629093071919671098221/237979876360536040641375731553000000000000)]
    bernstein := [(4807798786853919480306527353723640415001307347/573391513866326836745338233200640000000000000000), (214582935126485889484485847301182478876411407/20478268352368815598047794042880000000000000000), (536479407494260708551307271958542812780458509/49396904066186940327723395089920000000000000000), (5603504304105846789055514568477224431395643/588058381740320718187183274880000000000000000), (2772157030685785442642304054093033671576011/427828991209952432613709180320000000000000000)]
    reserve := (6479591349/1000000000000) }

theorem quarter_016_029_valid : quarter_016_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_029]
  · intro i; fin_cases i <;> norm_num [quarter_016_029]
  · norm_num [quarter_016_029]
  · norm_num [quarter_016_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_029]

def quarter_016_030 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(20577109/100000000), (10369249/50000000), (6427923/50000000), (6427923/50000000), (66817/1562500), (2337567/50000000), (150133/625000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(103289/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9673073/50000000), 0, 0]] i.1) i.2
    mu := ![(1712191/20000000), (130587/100000000), (3082691/50000000), (1/100000000), (3423413/100000000), (1600953/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-136003633150088699328215320850230527794647/1259211763903509746159307620961000000000000), (44761320836908595711/11179494305850000000), (-7004346409596906547590791750978383872941549/209868627317251624359884603493500000000000), (44761320836908595711/11179494305850000000), (-1444485338773494847800570178793795610684643/43421095307017577453769228309000000000000)]
    bernstein := [(1821764620563789268267348473377325396672107753/201473882224561559385489219353760000000000000000), (1785169203798716254856552574042867193584467353/134315921483041039590326146235840000000000000000), (11341760615666786394920352034424924819191302977/805895528898246237541956877415040000000000000000), (6113969297477695726635204976779336633050100177/537263685932164158361304584943360000000000000000), (16719127924293524784521725615398907697256419993/3223582115592984950167827509660160000000000000000)]
    reserve := (5186505981/1000000000000) }

theorem quarter_016_030_valid : quarter_016_030.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_030]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_030]
  · intro i; fin_cases i <;> norm_num [quarter_016_030]
  · norm_num [quarter_016_030]
  · norm_num [quarter_016_030, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_030, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_030, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_030, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_030]

def quarter_016_031 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(13194723/50000000), (6699163/25000000), (1983463/12500000), (1983463/12500000), (2439973/50000000), (203971/4000000), (203971/4000000)]
    cone := fun i => (![![0, 0, 0, (11126627/100000000), 0], ![(581723/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5788579/100000000), (84079/50000000), (7869043/100000000), (1/100000000), (4194777/100000000), (445859/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-16556572750525273480125306828571857594971/55099097377281614049832759179300000000000), (359354577858915298911/48669793374100000000), (-1175197193268521183732855536675354508198471/27549548688640807024916379589650000000000), (359354577858915298911/48669793374100000000), (-2333837813786517093985585766522137158801971/55099097377281614049832759179300000000000)]
    bernstein := [(2130320690820459476075697190603850519530555549/141053689285840931967571863499008000000000000000), (761352844596921516165510416021482555388262883/35263422321460232991892965874752000000000000000), (625712853570205783718771524309794884787373483/26447566741095174743919724406064000000000000000), (46914983661083716406951946693304828213671887/2203963895091264561993310367172000000000000000), (7954747999638064791630833810726359136823829/550990973772816140498327591793000000000000000)]
    reserve := (14437165721/1000000000000) }

theorem quarter_016_031_valid : quarter_016_031.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_031]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_031]
  · intro i; fin_cases i <;> norm_num [quarter_016_031]
  · norm_num [quarter_016_031]
  · norm_num [quarter_016_031, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_031, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_031, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_031, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_031]

def quarter_016_032 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![(3136297/10000000), (32167021/100000000), (3647001/20000000), (3647001/20000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, (3136297/20000000), 0], ![(1786781/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1350339/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5603677/100000000), (50231/25000000), (9343123/100000000), (1/100000000), (1185029/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5697692356721269609966404736653613621/9349474856142127021762287000000000000), (57475421949401/5023100000000), (-240419495090690233461213336026237976121/4674737428071063510881143500000000000), (57475421949401/5023100000000), (-475141297824659197312460267315822338621/9349474856142127021762287000000000000)]
    bernstein := [(2512584321261062335705611701945553927179/93494748561421270217622870000000000000000), (872018488816796173666711023203969435533/24931932949712338724699432000000000000000), (6778396662397976345649213583213526008373/179509917237928838817835910400000000000000), (112311496776578053159960809684891771029/3191287417563179356761527296000000000000), (41694837945267277313387180615283029051/1531817960430326091245533102080000000000)]
    reserve := (2687406897/100000000000) }

theorem quarter_016_032_valid : quarter_016_032.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_032]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_032]
  · intro i; fin_cases i <;> norm_num [quarter_016_032]
  · norm_num [quarter_016_032]
  · norm_num [quarter_016_032, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_032, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_032, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_032, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_032]

def quarter_016_033 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, (24052909/50000000), (25947091/100000000), (25947091/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15299657/100000000), 0, (46320569/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3842869/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (37341/12500000), (1726351/12500000), (1/100000000), (6744841/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-19323397952206206806506401421687/13913511122458788192000000000000), (6245880720059039/298728000000000), (-19935024423165401158859173698581/257657613378866448000000000000), (6245880720059039/298728000000000), (-1057167920898725455771888978301687/13913511122458788192000000000000)]
    bernstein := [(86820082477905141539128284403697/2279589662303647857377280000000000), (477639571687416856659334503922549/9498290259598532739072000000000000), (19413301708379899452140133984738433/356185884734944977715200000000000000), (15039436269207271120704353033892257/296821570612454148096000000000000000), (86120062679039797158710955717336953/2226161779593406110720000000000000000)]
    reserve := (38085837953/1000000000000) }

theorem quarter_016_033_valid : quarter_016_033.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_033]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_033]
  · intro i; fin_cases i <;> norm_num [quarter_016_033]
  · norm_num [quarter_016_033]
  · norm_num [quarter_016_033, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_033, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_033, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_033, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_033]

def quarter_016_034 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, (1982549/4000000), (25218137/100000000), (25218137/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(18044471/100000000), 0, (47013483/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (933727/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (152811/50000000), (14051637/100000000), (1/100000000), (819419/12500000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-625139814042680081708595436103/312798774425974459200000000000), (622274425023413/24449760000000), (-12549547052562777693096604336103/156399387212987229600000000000), (622274425023413/24449760000000), (-24473954291082875304484613236103/312798774425974459200000000000)]
    bernstein := [(3003586712626906203899791934854057/50047803908155913472000000000000000), (7283841903155484264787769919859733/100095607816311826944000000000000000), (46398944570004378111518383122152131/600573646897870961664000000000000000), (29386863577537489944830762933661613/400382431265247307776000000000000000), (48904431604918809002006520356686297/800764862530494615552000000000000000)]
    reserve := (60014355837/1000000000000) }

theorem quarter_016_034_valid : quarter_016_034.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_034]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_034]
  · intro i; fin_cases i <;> norm_num [quarter_016_034]
  · norm_num [quarter_016_034]
  · norm_num [quarter_016_034, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_034, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_034, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_034, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_034]

def quarter_016_035 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, (51016369/100000000), (3061477/12500000), (3061477/12500000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(20858957/100000000), 0, (23775553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3627337/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (31201/10000000), (3574841/25000000), (1/100000000), (1591637/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5844425779765097880364759698589/2130347820436501404000000000000), (9428540087644273/312010000000000), (-88661936957529995640089094126589/1065173910218250702000000000000), (9428540087644273/312010000000000), (-4182425564275485204873498257429/51959702937475644000000000000)]
    bernstein := [(448211650958356473246042547804860611/5453690420317443594240000000000000000), (21709817210914424735895718802798491/227237100846560149760000000000000000), (6412305550912543986176928734382023/63910434613095042120000000000000000), (171256002709965491507659652224667/1775289850363751170000000000000000), (27896279362434475416875057273459/332866846943203344375000000000000)]
    reserve := (41092509513/500000000000) }

theorem quarter_016_035_valid : quarter_016_035.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_035]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_035]
  · intro i; fin_cases i <;> norm_num [quarter_016_035]
  · norm_num [quarter_016_035]
  · norm_num [quarter_016_035, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_035, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_035, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_035, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_035]

def quarter_016_036 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, (10491247/20000000), (23771883/100000000), (23771883/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(23726859/100000000), 0, (5990433/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (440089/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (63567/20000000), (3638043/25000000), (1/100000000), (1544851/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-91522601557173648216339319/25203628781743720000000000), (124325274115107/3531500000000), (-3264751932096707703712357157/37805443172615580000000000), (124325274115107/3531500000000), (-6254936059521894462775696357/75610886345231160000000000)]
    bernstein := [(1235964657144135851506516267/11814200991442368750000000000), (2038276898290092061588482821/17184292351188900000000000000), (1858907054311770682932489481/15022030399714800000000000000), (87905614234093052487917022359/733196473650726400000000000000), (6897603499633330876582964208041/64521289681263923200000000000000)]
    reserve := (52308431947/500000000000) }

theorem quarter_016_036_valid : quarter_016_036.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_036]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_036]
  · intro i; fin_cases i <;> norm_num [quarter_016_036]
  · norm_num [quarter_016_036]
  · norm_num [quarter_016_036, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_036, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_036, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_036, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_036]

def quarter_016_037 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, (53874957/100000000), (23062521/100000000), (23062521/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(26630293/100000000), 0, (12030427/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3415653/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (161521/50000000), (14807977/100000000), (1/100000000), (5995009/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-200864227258375760836734089210903/43016574144090576459000000000000), (3262695357022683/80760500000000), (-1926999407788365499641526551020903/21508287072045288229500000000000), (3262695357022683/80760500000000), (-3653134588318355238446319012830903/43016574144090576459000000000000)]
    bernstein := [(14020982959092214274493725589850947817/110122429808871875735040000000000000000), (1563770987500650171985681649574523633/11012242980887187573504000000000000000), (487308409008303141296052765901727803/3303672894266156272051200000000000000), (15823194565932059746573544199209681/110122429808871875735040000000000000), (1435729986841308497677871769061033/11012242980887187573504000000000000)]
    reserve := (63660886267/500000000000) }

theorem quarter_016_037_valid : quarter_016_037.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_037]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_037]
  · intro i; fin_cases i <;> norm_num [quarter_016_037]
  · norm_num [quarter_016_037]
  · norm_num [quarter_016_037, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_037, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_037, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_037, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_037]

def quarter_016_038 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, (27631693/50000000), (22368307/100000000), (22368307/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7387469/25000000), 0, (1203459/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3312837/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (163789/50000000), (15064439/100000000), (1/100000000), (5814551/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-6821417524347967874024727621943/1163250932392057899000000000000), (375002941283947/8189450000000), (-54055715801945626553488971021943/581625466196028949500000000000), (375002941283947/8189450000000), (-101290014079543285232953214421943/1163250932392057899000000000000)]
    bernstein := [(44759407462582567387258890378473/297792238692366822144000000000000), (8657442306486637931078644460907/52244252402169617920000000000000), (15331467355525430363857983420383123/89337671607710046643200000000000000), (876908666018130331728851099928291/5224425240216961792000000000000000), (459259768655299314698292903847522937/2977922386923668221440000000000000000)]
    reserve := (30060828757/200000000000) }

theorem quarter_016_038_valid : quarter_016_038.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_038]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_038]
  · intro i; fin_cases i <;> norm_num [quarter_016_038]
  · norm_num [quarter_016_038]
  · norm_num [quarter_016_038, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_038, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_038, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_038, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_038]

def quarter_016_039 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, (442279/781250), (338971/1562500), (338971/1562500), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1298597/4000000), 0, (2398379/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6425981/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2589/781250), (7659499/50000000), (1/100000000), (1127861/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1291930438926933224673566333977/178927865376346968000000000000), (2216300316389/43150000000), (-2874292381062509639517721844659/29821310896057828000000000000), (2216300316389/43150000000), (-15953823847448124612432764733977/178927865376346968000000000000)]
    bernstein := [(26500134273467877986152557777342781/152685111787816079360000000000000000), (21726798716428920603162804165877439/114513833840862059520000000000000000), (5612909641458511741010488900520347/28628458460215514880000000000000000), (1376795173841122553758957276487531/7157114615053878720000000000000000), (319268209929382399190706597219263/1789278653763469680000000000000000)]
    reserve := (173560696017/1000000000000) }

theorem quarter_016_039_valid : quarter_016_039.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_039]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_039]
  · intro i; fin_cases i <;> norm_num [quarter_016_039]
  · norm_num [quarter_016_039]
  · norm_num [quarter_016_039, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_039, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_039, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_039, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_039]

def quarter_016_040 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, (1447741/2500000), (1052259/5000000), (1052259/5000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(8838433/25000000), 0, (47605433/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6233753/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (167219/50000000), (7784457/50000000), (1/100000000), (5470609/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-33202198401267665860309670516121/3797942186856050958400000000000), (954740609211387/16721900000000), (-189736716665527990413233776596121/1898971093428025479200000000000), (954740609211387/16721900000000), (-346271234929788314966157882676121/3797942186856050958400000000000)]
    bernstein := [(7485000203682858547032473633646399/37979421868560509584000000000000000), (32517745513971879228719150998654029/151917687474242038336000000000000000), (402580883570592038237752837572242177/1823012249690904460032000000000000000), (40616543064055849603545113381076653/186975615352913277952000000000000000), (1973689211263731000126116028511471319/9722731998351490453504000000000000000)]
    reserve := (197080414483/1000000000000) }

theorem quarter_016_040_valid : quarter_016_040.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_040]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_040]
  · intro i; fin_cases i <;> norm_num [quarter_016_040]
  · norm_num [quarter_016_040]
  · norm_num [quarter_016_040, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_040, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_040, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_040, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_040]

def quarter_016_041 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, (462083/781250), (319167/1562500), (319167/1562500), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(19096959/50000000), 0, (11762537/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (121011/2000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (336677/100000000), (7905667/50000000), (1/100000000), (1061967/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-35740294053701733533061011971/3426171031895097640000000000), (82808532671399/1315144531250), (-177338108189709254314797255171/1713085515947548820000000000), (82808532671399/1315144531250), (-318935922325716775096533498371/3426171031895097640000000000)]
    bernstein := [(1937028073880658348488252040619469/8770997841651449958400000000000000), (1046562680635799224570887220343591/4385498920825724979200000000000000), (539207991622645946794906833734949/2192749460412862489600000000000000), (1102779576270763195532928775871/4549272739445772800000000000000), (124924920533752048260995743656829/548187365103215622400000000000000)]
    reserve := (27605583037/125000000000) }

theorem quarter_016_041_valid : quarter_016_041.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_041]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_041]
  · intro i; fin_cases i <;> norm_num [quarter_016_041]
  · norm_num [quarter_016_041]
  · norm_num [quarter_016_041, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_041, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_041, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_041, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_041]

def quarter_016_042 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 0]
    lambda := ![0, (60312151/100000000), (4960981/25000000), (4960981/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(40962871/100000000), 0, (46302341/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5877931/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (84519/25000000), (16043363/100000000), (1/100000000), (5158347/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-91687146745926825344881620201299/7460862517136877609600000000000), (15539527813621643/225384000000000), (-399830260632341639650408442669299/3730431258568438804800000000000), (15539527813621643/225384000000000), (-78663708279861828217326140570811/828984724126319734400000000000)]
    bernstein := [(292259686510284861677971006880896301/1193738002741900417536000000000000000), (41936859269511776296985842504494923/159165067032253389004800000000000000), (155421557592774676173316340060198399/572994241316112200417280000000000000), (20465095249981495171559876748719113/76399232175481626722304000000000000), (7733781157205017625837313749564029/30559692870192650688921600000000000)]
    reserve := (24482732881/100000000000) }

theorem quarter_016_042_valid : quarter_016_042.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_016_042]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_016_042]
  · intro i; fin_cases i <;> norm_num [quarter_016_042]
  · norm_num [quarter_016_042]
  · norm_num [quarter_016_042, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_016_042, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_016_042, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_016_042, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_016_042]

def quarterTable016 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 0, 0, 2, 0]
  rows := [quarter_016_000, quarter_016_001, quarter_016_002, quarter_016_003, quarter_016_004, quarter_016_005, quarter_016_006, quarter_016_007, quarter_016_008, quarter_016_009, quarter_016_010, quarter_016_011, quarter_016_012, quarter_016_013, quarter_016_014, quarter_016_015, quarter_016_016, quarter_016_017, quarter_016_018, quarter_016_019, quarter_016_020, quarter_016_021, quarter_016_022, quarter_016_023, quarter_016_024, quarter_016_025, quarter_016_026, quarter_016_027, quarter_016_028, quarter_016_029, quarter_016_030, quarter_016_031, quarter_016_032, quarter_016_033, quarter_016_034, quarter_016_035, quarter_016_036, quarter_016_037, quarter_016_038, quarter_016_039, quarter_016_040, quarter_016_041, quarter_016_042]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_016_000_valid
    · exact quarter_016_001_valid
    · exact quarter_016_002_valid
    · exact quarter_016_003_valid
    · exact quarter_016_004_valid
    · exact quarter_016_005_valid
    · exact quarter_016_006_valid
    · exact quarter_016_007_valid
    · exact quarter_016_008_valid
    · exact quarter_016_009_valid
    · exact quarter_016_010_valid
    · exact quarter_016_011_valid
    · exact quarter_016_012_valid
    · exact quarter_016_013_valid
    · exact quarter_016_014_valid
    · exact quarter_016_015_valid
    · exact quarter_016_016_valid
    · exact quarter_016_017_valid
    · exact quarter_016_018_valid
    · exact quarter_016_019_valid
    · exact quarter_016_020_valid
    · exact quarter_016_021_valid
    · exact quarter_016_022_valid
    · exact quarter_016_023_valid
    · exact quarter_016_024_valid
    · exact quarter_016_025_valid
    · exact quarter_016_026_valid
    · exact quarter_016_027_valid
    · exact quarter_016_028_valid
    · exact quarter_016_029_valid
    · exact quarter_016_030_valid
    · exact quarter_016_031_valid
    · exact quarter_016_032_valid
    · exact quarter_016_033_valid
    · exact quarter_016_034_valid
    · exact quarter_016_035_valid
    · exact quarter_016_036_valid
    · exact quarter_016_037_valid
    · exact quarter_016_038_valid
    · exact quarter_016_039_valid
    · exact quarter_016_040_valid
    · exact quarter_016_041_valid
    · exact quarter_016_042_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
