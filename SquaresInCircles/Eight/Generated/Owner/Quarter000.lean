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

def quarter_000_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_000_000_valid : quarter_000_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_000]
  · intro i; fin_cases i <;> norm_num [quarter_000_000]
  · norm_num [quarter_000_000]
  · norm_num [quarter_000_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_000]

def quarter_000_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_000_001_valid : quarter_000_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_001]
  · intro i; fin_cases i <;> norm_num [quarter_000_001]
  · norm_num [quarter_000_001]
  · norm_num [quarter_000_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_001]

def quarter_000_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_000_002_valid : quarter_000_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_002]
  · intro i; fin_cases i <;> norm_num [quarter_000_002]
  · norm_num [quarter_000_002]
  · norm_num [quarter_000_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_002]

def quarter_000_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_000_003_valid : quarter_000_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_003]
  · intro i; fin_cases i <;> norm_num [quarter_000_003]
  · norm_num [quarter_000_003]
  · norm_num [quarter_000_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_003]

def quarter_000_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_000_004_valid : quarter_000_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_004]
  · intro i; fin_cases i <;> norm_num [quarter_000_004]
  · norm_num [quarter_000_004]
  · norm_num [quarter_000_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_004]

def quarter_000_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_000_005_valid : quarter_000_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_005]
  · intro i; fin_cases i <;> norm_num [quarter_000_005]
  · norm_num [quarter_000_005]
  · norm_num [quarter_000_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_005]

def quarter_000_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_000_006_valid : quarter_000_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_006]
  · intro i; fin_cases i <;> norm_num [quarter_000_006]
  · norm_num [quarter_000_006]
  · norm_num [quarter_000_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_006]

def quarter_000_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_000_007_valid : quarter_000_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_007]
  · intro i; fin_cases i <;> norm_num [quarter_000_007]
  · norm_num [quarter_000_007]
  · norm_num [quarter_000_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_007]

def quarter_000_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_000_008_valid : quarter_000_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_008]
  · intro i; fin_cases i <;> norm_num [quarter_000_008]
  · norm_num [quarter_000_008]
  · norm_num [quarter_000_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_008]

def quarter_000_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1067647938911762121/3859681000000000000), (-13528061/3859681), (-8309344188911762121/1929840500000000000), (-13528061/3859681), (-15551040438911762121/3859681000000000000)]
    bernstein := [(100068034278401520636999/617548960000000000000000), (36328949888069554679293/247019584000000000000000), (265685575963521009711/2016486400000000000000), (917720443345976065601/7904626688000000000000), (63294346623912201551/632370135040000000000)]
    reserve := (100090663863/1000000000000) }

theorem quarter_000_009_valid : quarter_000_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_009]
  · intro i; fin_cases i <;> norm_num [quarter_000_009]
  · norm_num [quarter_000_009]
  · norm_num [quarter_000_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_009]

def quarter_000_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![(12029497/50000000), (12029497/50000000), (8260757/100000000), (8260757/100000000), (398793/10000000), (398793/10000000), (13692319/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (28426103/100000000), 0, 0]] i.1) i.2
    mu := ![(8256971/100000000), (1/100000000), (107757/1562500), (1/100000000), (2317831/100000000), (1/100000000), (520733/50000000)]
    alternative := .zero
    polynomial := [(-124311205425147672145586812408253669/17182371381840777782204496000000000000), (-2821343411051261623121/2847188556950400000000), (-8963547107972632220360629222102973669/8591185690920388891102248000000000000), (-2821343411051261623121/2847188556950400000000), (-17802783010520116768575671631797693669/17182371381840777782204496000000000000)]
    bernstein := [(2454499936448573628484886276342875367/24061194249579427622533201920000000000), (190038854520783751458771795221295770227/1954972032778328494330822656000000000000), (30458195767864467649230533106391307823397/329901530531342933418326323200000000000000), (1334273289316445384429360425704499987379/15273219006080691361959552000000000000000), (14143039400005293577502210505111180032531/171823713818407777822044960000000000000000)]
    reserve := (41155667881/500000000000) }

theorem quarter_000_010_valid : quarter_000_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_010]
  · intro i; fin_cases i <;> norm_num [quarter_000_010]
  · norm_num [quarter_000_010]
  · norm_num [quarter_000_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_010]

def quarter_000_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![(11216351/50000000), (11216351/50000000), (984389/10000000), (984389/10000000), (2496779/50000000), (2496779/50000000), (25459701/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2676379/10000000), 0, 0]] i.1) i.2
    mu := ![(7914339/100000000), (1/100000000), (6625729/100000000), (1/100000000), (1394543/50000000), (1/100000000), (130409/10000000)]
    alternative := .zero
    polynomial := [(16998572820852147606053821497845399/2384118297795078225436349250000000000), (-731521916075571887977/873971090468850000000), (-1124812970355906830285171069799632101/1192059148897539112718174625000000000), (-731521916075571887977/873971090468850000000), (-2266624513532665808176395961097109601/2384118297795078225436349250000000000)]
    bernstein := [(1958240948888801330451028546790415310199/23841182977950782254363492500000000000000), (7433862961549144585778586905452975422997/95364731911803129017453970000000000000000), (84327797297157624356478555837717720498473/1144376782941637548209447640000000000000000), (105810465564798907316566907505067488689873/1525835710588850064279263520000000000000000), (396234904144272878355803496695767054853519/6103342842355400257117054080000000000000000)]
    reserve := (64920964523/1000000000000) }

theorem quarter_000_011_valid : quarter_000_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_011]
  · intro i; fin_cases i <;> norm_num [quarter_000_011]
  · norm_num [quarter_000_011]
  · norm_num [quarter_000_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_011]

def quarter_000_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![(21030381/100000000), (21030381/100000000), (2240177/20000000), (2240177/20000000), (1483827/25000000), (1483827/25000000), (23666851/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (25216883/100000000), 0, 0]] i.1) i.2
    mu := ![(3796723/50000000), (1/100000000), (1276481/20000000), (1/100000000), (3203039/100000000), (1/100000000), (1550033/100000000)]
    alternative := .zero
    polynomial := [(56173853161951878188809658820803327/3437386753474705145992283000000000000), (-685283411494438476021/969288954352600000000), (-1480242878775905142231299775785756673/1718693376737352572996141500000000000), (-685283411494438476021/969288954352600000000), (-3016659610713762162651409210392316673/3437386753474705145992283000000000000)]
    bernstein := [(570156342065815362457107498800992556687087/8799710088895245173740244480000000000000000), (268901649902861693233076961725520319458829/4399855044447622586870122240000000000000000), (6641834971856870178850565196389028662797/115785659064411120707108480000000000000000), (8411956500429746550651623378944678731283/157137680158843663816790080000000000000000), (3898708477026766923530816526108665823561/78568840079421831908395040000000000000000)]
    reserve := (1984862433/40000000000) }

theorem quarter_000_012_valid : quarter_000_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_012]
  · intro i; fin_cases i <;> norm_num [quarter_000_012]
  · norm_num [quarter_000_012]
  · norm_num [quarter_000_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_012]

def quarter_000_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![(9910451/50000000), (9910451/50000000), (2474791/20000000), (2474791/20000000), (1703919/25000000), (1703919/25000000), (2747367/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (148493/625000), 0, 0]] i.1) i.2
    mu := ![(3645089/50000000), (1/100000000), (3081539/50000000), (1/100000000), (446197/12500000), (1/100000000), (355989/20000000)]
    alternative := .zero
    polynomial := [(908720664879589312361012725566617/41980740970869578334231600000000000), (-5626031186507777397/9439062110900000000), (-16639161052143521622630894619241383/20990370485434789167115800000000000), (-5626031186507777397/9439062110900000000), (-34187042769166632557622801964049383/41980740970869578334231600000000000)]
    bernstein := [(332726864169687895854138721055838124217/6716918555339132533477056000000000000000), (207241363531508821271725415555648810339/4477945703559421688984704000000000000000), (494565593417035346307797048823711402893/11514717523438512914532096000000000000000), (708317736903130454377078468220964457139/17911782814237686755938816000000000000000), (3875459339588222853600111236822220165017/107470696885426120535632896000000000000000)]
    reserve := (36060614213/1000000000000) }

theorem quarter_000_013_valid : quarter_000_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_013]
  · intro i; fin_cases i <;> norm_num [quarter_000_013]
  · norm_num [quarter_000_013]
  · norm_num [quarter_000_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_013]

def quarter_000_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![(4694617/25000000), (4694617/25000000), (13396713/100000000), (13396713/100000000), (7638179/100000000), (7638179/100000000), (127333/625000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (894721/4000000), 0, 0]] i.1) i.2
    mu := ![(875139/12500000), (1/100000000), (5964769/100000000), (1/100000000), (3896631/100000000), (1/100000000), (398949/20000000)]
    alternative := .zero
    polynomial := [(67507114042067727571081804957567/2817635704104013896712753125000000), (-13056909689850449131/26100009889455000000), (-517823258193380725577437791202279/704408926026003474178188281250000), (-13056909689850449131/26100009889455000000), (-2138800146815590629880832969766683/2817635704104013896712753125000000)]
    bernstein := [(259770435224001821705623009037320192717/7213147402506275575584648000000000000000), (4776686189060393132203236642771949669/144262948050125511511692960000000000000), (203786148129633418111155248436727271/6762325689849633352110607500000000000), (2442140300591928966715526787507269/90164342531328444694808100000000000), (67507114042067727571081804957567/2817635704104013896712753125000000)]
    reserve := (2395878003/100000000000) }

theorem quarter_000_014_valid : quarter_000_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_014]
  · intro i; fin_cases i <;> norm_num [quarter_000_014]
  · norm_num [quarter_000_014]
  · norm_num [quarter_000_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_014]

def quarter_000_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![(18175261/100000000), (18175261/100000000), (6997519/50000000), (6997519/50000000), (8025889/100000000), (8025889/100000000), (19607623/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1085181/5000000), 0, 0]] i.1) i.2
    mu := ![(6921837/100000000), (1/100000000), (2898123/50000000), (1/100000000), (815301/20000000), (1/100000000), (2095997/100000000)]
    alternative := .zero
    polynomial := [(10200642945088018501837498724931889/423215723460485053606287000000000000), (203265220762109483/642959455511250000), (-149702462919747835139563735192148111/211607861730242526803143500000000000), (203265220762109483/642959455511250000), (-309605568784583688780964969109228111/423215723460485053606287000000000000)]
    bernstein := [(10200642945088018501837498724931889/423215723460485053606287000000000000), (33110593166325620786434533734830667/1269647170381455160818861000000000000), (56841109532899749872630950336592919089/2031435472610328257310177600000000000000), (60558076201089820217108004999824657867/2031435472610328257310177600000000000000), (102607643559329271620145401109867581970067/3250296756176525211696284160000000000000000)]
    reserve := (753209473/31250000000) }

theorem quarter_000_015_valid : quarter_000_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_015]
  · intro i; fin_cases i <;> norm_num [quarter_000_015]
  · norm_num [quarter_000_015]
  · norm_num [quarter_000_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_015]

def quarter_000_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![(8954861/50000000), (8954861/50000000), (14255883/100000000), (14255883/100000000), (8015269/100000000), (8015269/100000000), (19638251/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (10865737/50000000), 0, 0]] i.1) i.2
    mu := ![(7041511/100000000), (1/100000000), (5641459/100000000), (1/100000000), (2066247/50000000), (1/100000000), (261653/12500000)]
    alternative := .zero
    polynomial := [(501490784924116722029327994119438111/21476586366718774834497759000000000000), (686938464449364394243/1986219780227450000000), (-7562532065373129838758685240805631889/10738293183359387417248879500000000000), (686938464449364394243/1986219780227450000000), (-15626554915670376399546698475730701889/21476586366718774834497759000000000000)]
    bernstein := [(1735272155170638230064302656968294621813311/54980061098800063576314263040000000000000000), (102345716696263183028241932187326870438279/3054447838822225754239681280000000000000000), (208422131077972980536648825596038328370219/5890720832014292526033671040000000000000000), (28395580200631025889292116390978744783479/763611959705556438559920320000000000000000), (133743223613790238978532012565281026746911/3436253818675003973519641440000000000000000)]
    reserve := (15780922397/500000000000) }

theorem quarter_000_016_valid : quarter_000_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_016]
  · intro i; fin_cases i <;> norm_num [quarter_000_016]
  · norm_num [quarter_000_016]
  · norm_num [quarter_000_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_016]

def quarter_000_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![(11115623/50000000), (11115623/50000000), (1797751/10000000), (1797751/10000000), (2447811/25000000), (2447811/25000000), 0]
    cone := fun i => (![![0, 0, 0, (11115623/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2557027/100000000), 0, 0]] i.1) i.2
    mu := ![(15516/390625), (1/100000000), (1715721/25000000), (1/100000000), (5172597/100000000), (1/100000000), (639257/25000000)]
    alternative := .zero
    polynomial := [(431595950602956554389227780520411/34775672182001549328768000000000000), (19983122363873/34314420000000), (-7299469280331375600700535068759589/17387836091000774664384000000000000), (19983122363873/34314420000000), (-15030534511265707755790297918039589/34775672182001549328768000000000000)]
    bernstein := [(32231379184124965744991432396274864173/794872507017178270371840000000000000000), (69873104958676372933948407058330603319/1589745014034356540743680000000000000000), (3159547637772155016400487837066400133897/66769290589442974711234560000000000000000), (751599307154299571892116276729666647699/14837620130987327713607680000000000000000), (4803648281112949702264534907366150790091/89025720785923966281646080000000000000000)]
    reserve := (2534319883/62500000000) }

theorem quarter_000_017_valid : quarter_000_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_017]
  · intro i; fin_cases i <;> norm_num [quarter_000_017]
  · norm_num [quarter_000_017]
  · norm_num [quarter_000_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_017]

def quarter_000_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (28883937/100000000), (11691303/50000000), (11691303/50000000), (6087713/50000000), (6087713/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1444197/100000000), 0, (28883937/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3179667/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (271193/3125000), (1/100000000), (1332261/20000000), (1/100000000), (3179667/100000000)]
    alternative := .zero
    polynomial := [(23353711259853437449450813/3063501956249692776000000000000), (25976219946147/33377600000000), (-884836621325668970675941669187/1531750978124846388000000000000), (25976219946147/33377600000000), (-1769696596362597794789332789187/3063501956249692776000000000000)]
    bernstein := [(434770586537529962059560478955370253/7842565007999213506560000000000000000), (9024349898955219215470226060454127/150818557846138721280000000000000000), (94390690051763935774752425319791851/1470480938999852532480000000000000000), (645723047881283453974427366543003/9426159865383670080000000000000000), (2229518142347752586700267257453413/30635019562496927760000000000000000)]
    reserve := (5543729457/100000000000) }

theorem quarter_000_018_valid : quarter_000_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_018]
  · intro i; fin_cases i <;> norm_num [quarter_000_018]
  · norm_num [quarter_000_018]
  · norm_num [quarter_000_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_018]

def quarter_000_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (2917131/10000000), (591473/2500000), (591473/2500000), (470217/4000000), (470217/4000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(291713/20000000), 0, (2917131/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1534991/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2130411/25000000), (1/100000000), (3337707/50000000), (1/100000000), (1534991/50000000)]
    alternative := .zero
    polynomial := [(-10165827135246403862977721791/3638280544980442269000000000000), (575134741321/710137000000), (-1071499923581180657524001621791/1819140272490221134500000000000), (575134741321/710137000000), (-2132834020027114911185025521791/3638280544980442269000000000000)]
    bernstein := [(2657991772079360147490979202210009/36382805449804422690000000000000000), (752095870730493127212643296575943/9702081453281179384000000000000000), (5724062366367131129150561079100583/69854986463624491564800000000000000), (107207422310162732515649058391359/1241866426019990961152000000000000), (54052665173115805169470162337321/596095884489595661352960000000000)]
    reserve := (73056262133/1000000000000) }

theorem quarter_000_019_valid : quarter_000_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_019]
  · intro i; fin_cases i <;> norm_num [quarter_000_019]
  · norm_num [quarter_000_019]
  · norm_num [quarter_000_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_019]

def quarter_000_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (29403767/100000000), (5986759/25000000), (5986759/25000000), (283777/2500000), (283777/2500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(367547/25000000), 0, (29403767/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (592877/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1043449/12500000), (1/100000000), (1339259/20000000), (1/100000000), (1482193/50000000)]
    alternative := .zero
    polynomial := [(-163236846514029021827870732147/24855459979594441956000000000000), (6070112645557/7196200000000), (-7471678385692226279520353252147/12427729989797220978000000000000), (6070112645557/7196200000000), (-14780119924870423537212835772147/24855459979594441956000000000000)]
    bernstein := [(370501624698396943069232310891157/4072318563056753370071040000000000), (4862917792570204399018671630592507/50903982038209417125888000000000000), (190978463884896697089019338887324719/1908899326432853142220800000000000000), (166278207788574082620061838987815951/1590749438694044285184000000000000000), (433394172875697418163693283939877693/3976873596735110712960000000000000000)]
    reserve := (18196102243/200000000000) }

theorem quarter_000_020_valid : quarter_000_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_020]
  · intro i; fin_cases i <;> norm_num [quarter_000_020]
  · norm_num [quarter_000_020]
  · norm_num [quarter_000_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_020]

def quarter_000_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (5918093/20000000), (6061129/25000000), (6061129/25000000), (10960251/100000000), (10960251/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1479523/100000000), 0, (5918093/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2862319/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8158161/100000000), (1/100000000), (1344603/20000000), (1/100000000), (2862319/100000000)]
    alternative := .zero
    polynomial := [(-159530593894410350119531927853/13954743654062852212000000000000), (35870325106997/40790805000000), (-4288804130689599711913117727853/6977371827031426106000000000000), (35870325106997/40790805000000), (-8418077667484789073706703527853/13954743654062852212000000000000)]
    bernstein := [(244054552709370112854476200709222307/2232758984650056353920000000000000000), (1526804216540542605177499579693306949/13396553907900338123520000000000000000), (3177723851902012459349833029608166881/26793107815800676247040000000000000000), (6602110086585035726388652752590902589/53586215631601352494080000000000000000), (13694599392046582281011137106163783641/107172431263202704988160000000000000000)]
    reserve := (109306268337/1000000000000) }

theorem quarter_000_021_valid : quarter_000_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_021]
  · intro i; fin_cases i <;> norm_num [quarter_000_021]
  · norm_num [quarter_000_021]
  · norm_num [quarter_000_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_021]

def quarter_000_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (29739637/100000000), (196393/800000), (196393/800000), (165329/1562500), (165329/1562500), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(743491/50000000), 0, (29739637/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (276329/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1591069/20000000), (1/100000000), (6754729/100000000), (1/100000000), (2763291/100000000)]
    alternative := .zero
    polynomial := [(-693813447920694318220290107357/39597001777056020788000000000000), (5840656529341/6364276000000), (-12469818039300704187216029667357/19798500888528010394000000000000), (5840656529341/6364276000000), (-24245822630680714056211769227357/39597001777056020788000000000000)]
    bernstein := [(764051527550954973660109768480565779/5962842620544906659840000000000000000), (99086345093659596594132361827648797/745355327568113332480000000000000000), (54530698302843476127298832652562983/395970017770560207880000000000000000), (14102946423482668421730137309182313/98992504442640051970000000000000000), (910680387828331655160383180076667/6187031527665003248125000000000000)]
    reserve := (128135450853/1000000000000) }

theorem quarter_000_022_valid : quarter_000_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_022]
  · intro i; fin_cases i <;> norm_num [quarter_000_022]
  · norm_num [quarter_000_022]
  · norm_num [quarter_000_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_022]

def quarter_000_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (3732323/12500000), (24858847/100000000), (24858847/100000000), (10211861/100000000), (10211861/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1492929/100000000), 0, (3732323/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2666873/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3870493/50000000), (1/100000000), (271627/4000000), (1/100000000), (1333437/50000000)]
    alternative := .zero
    polynomial := [(-17513741817570612647708274119/700941428699842753500000000000), (92781246411581/96762325000000), (-226804927096713269069418714119/350470714349921376750000000000), (92781246411581/96762325000000), (-436096112375855925491129154119/700941428699842753500000000000)]
    bernstein := [(16162729814832018789541338303889/109522098234350430234375000000000), (267312364556601006654502261008677/1752353571749606883750000000000000), (473109744940763685266697373106461/3004034694427897515000000000000000), (36430309570028747965884224076200849/224301257183949681120000000000000000), (300245424214740438465522268416340441/1794410057471597448960000000000000000)]
    reserve := (36893764079/250000000000) }

theorem quarter_000_023_valid : quarter_000_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_023]
  · intro i; fin_cases i <;> norm_num [quarter_000_023]
  · norm_num [quarter_000_023]
  · norm_num [quarter_000_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_023]

def quarter_000_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (29953703/100000000), (25171881/100000000), (25171881/100000000), (9851267/100000000), (9851267/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(299537/20000000), 0, (29953703/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2572703/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7516771/100000000), (1/100000000), (273207/4000000), (1/100000000), (2572703/100000000)]
    alternative := .zero
    polynomial := [(-14084687125850369313817804177/414383648803534564000000000000), (753991047425343/751677100000000), (-138207934569024166116722724177/207191824401767282000000000000), (753991047425343/751677100000000), (-262331182012197962919627644177/414383648803534564000000000000)]
    bernstein := [(177938918688241401901710897165956303/1060822140937048483840000000000000000), (1078929914764748853306389237981191/6240130240806167552000000000000000), (1888771112778063434803200688371759/10608221409370484838400000000000000), (194317791603790014940382465679479/1060822140937048483840000000000000), (1174950939817222382519295968991/6240130240806167552000000000000)]
    reserve := (83868403487/500000000000) }

theorem quarter_000_024_valid : quarter_000_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_024]
  · intro i; fin_cases i <;> norm_num [quarter_000_024]
  · norm_num [quarter_000_024]
  · norm_num [quarter_000_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_024]

def quarter_000_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (15015269/50000000), (25486643/100000000), (25486643/100000000), (9498089/100000000), (9498089/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1501527/100000000), 0, (15015269/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (620117/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7284229/100000000), (1/100000000), (687263/10000000), (1/100000000), (2480469/100000000)]
    alternative := .zero
    polynomial := [(-555262639442624994516519953971/12417676965487241463000000000000), (382688800551967/364211450000000), (-4284357839280517927214490893971/6208838482743620731500000000000), (382688800551967/364211450000000), (-8013453039118410859912461833971/12417676965487241463000000000000)]
    bernstein := [(599980504385136028529676907982381/3178925303164733814528000000000000), (108265742797133013719910692847479/557706193537672599040000000000000), (190260384905282832168334270449738431/953677590949420144358400000000000000), (11425354137025961287937658059947727/55770619353767259904000000000000000), (6682506751804553027263015263672699389/31789253031647338145280000000000000000)]
    reserve := (188736899161/1000000000000) }

theorem quarter_000_025_valid : quarter_000_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_025]
  · intro i; fin_cases i <;> norm_num [quarter_000_025]
  · norm_num [quarter_000_025]
  · norm_num [quarter_000_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_025]

def quarter_000_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (6018769/20000000), (25801747/100000000), (25801747/100000000), (915133/10000000), (915133/10000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(376173/25000000), 0, (6018769/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2389911/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (880593/12500000), (1/100000000), (3458757/50000000), (1/100000000), (2389911/100000000)]
    alternative := .zero
    polynomial := [(-185594548897684243768286516783/3235150507796591916000000000000), (155294754989443/140894880000000), (-1159175728230703530251856716783/1617575253898295958000000000000), (155294754989443/140894880000000), (-2132756907563722816735426916783/3235150507796591916000000000000)]
    bernstein := [(581660042222744045279862603102507499/2760661766653091768320000000000000000), (149311370087734301286761537122721127/690165441663272942080000000000000000), (344700176089700084829463336182763039/1552872243742364119680000000000000000), (29452903414749209814012769972655249/129406020311863676640000000000000000), (7544926344107428750181998407451177/32351505077965919160000000000000000)]
    reserve := (210695873449/1000000000000) }

theorem quarter_000_026_valid : quarter_000_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_026]
  · intro i; fin_cases i <;> norm_num [quarter_000_026]
  · norm_num [quarter_000_026]
  · norm_num [quarter_000_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_026]

def quarter_000_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (15073833/50000000), (13058001/50000000), (13058001/50000000), (1762033/20000000), (1762033/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1507383/100000000), 0, (15073833/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1150407/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6799557/100000000), (1/100000000), (696437/10000000), (1/100000000), (1150407/50000000)]
    alternative := .zero
    polynomial := [(-1541939612754997933748030947/21363568131934362600000000000), (65611375462611/56662975000000), (-7982556778853008909624946947/10681784065967181300000000000), (65611375462611/56662975000000), (-14423173944951019885501862947/21363568131934362600000000000)]
    bernstein := [(49934930947319711472292168646693/213635681319343626000000000000000), (204809646661957858730705610583103/854542725277374504000000000000000), (359782904968604270743174366411277/1464930386189784864000000000000000), (56375613998090372665756079561743/224142354171114624000000000000000), (230805595884299472499030019835953/896569416684458496000000000000000)]
    reserve := (233738721167/1000000000000) }

theorem quarter_000_027_valid : quarter_000_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_027]
  · intro i; fin_cases i <;> norm_num [quarter_000_027]
  · norm_num [quarter_000_027]
  · norm_num [quarter_000_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_027]

def quarter_000_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (30195401/100000000), (6607097/25000000), (6607097/25000000), (1059239/12500000), (1059239/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(150977/10000000), 0, (30195401/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2213/100000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3274889/50000000), (1/100000000), (7012801/100000000), (1/100000000), (2213001/100000000)]
    alternative := .zero
    polynomial := [(-18174190912367543131803592456249/203296406112975244356000000000000), (199503943360897/163744450000000), (-79560355956768931195827660016249/101648203056487622178000000000000), (199503943360897/163744450000000), (-140946521001170319259851727576249/203296406112975244356000000000000)]
    bernstein := [(134270547016186968505767755009538653111/520438799649216625551360000000000000000), (848919345627624874485994064507770709/3212585183019855713280000000000000000), (105583101842481753648088152322310703293/390329099736912469163520000000000000000), (222266662100678749578300958392506189/803146295754963928320000000000000000), (9204963839318639919568000282166225351/32527424978076039096960000000000000000)]
    reserve := (1289974413/5000000000) }

theorem quarter_000_028_valid : quarter_000_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_028]
  · intro i; fin_cases i <;> norm_num [quarter_000_028]
  · norm_num [quarter_000_028]
  · norm_num [quarter_000_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_028]

def quarter_000_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 0]
    lambda := ![0, (7559971/25000000), (5347609/20000000), (5347609/20000000), (2035503/25000000), (2035503/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(755997/50000000), 0, (7559971/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2126323/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (15741/250000), (1/100000000), (110351/1562500), (1/100000000), (2126323/100000000)]
    alternative := .zero
    polynomial := [(-6460682003404520594859143923/59095962652806288000000000000), (40427768959339/31482000000000), (-24331232558296464830765063923/29547981326403144000000000000), (40427768959339/31482000000000), (-42201783113188409066670983923/59095962652806288000000000000)]
    bernstein := [(99315686655200965124614642277751/350198297201815040000000000000000), (3695622310549625261077540240329/12734483534611456000000000000000), (1347108300080161062675308375817023/4538569931735522918400000000000000), (183613582215573400729987237769401/605142657564736389120000000000000), (75045560896047120766540292306333/242057063025894555648000000000000)]
    reserve := (283598428229/1000000000000) }

theorem quarter_000_029_valid : quarter_000_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_000_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_000_029]
  · intro i; fin_cases i <;> norm_num [quarter_000_029]
  · norm_num [quarter_000_029]
  · norm_num [quarter_000_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_000_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_000_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_000_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_000_029]

def quarterTable000 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 0, 0, 0, 0]
  rows := [quarter_000_000, quarter_000_001, quarter_000_002, quarter_000_003, quarter_000_004, quarter_000_005, quarter_000_006, quarter_000_007, quarter_000_008, quarter_000_009, quarter_000_010, quarter_000_011, quarter_000_012, quarter_000_013, quarter_000_014, quarter_000_015, quarter_000_016, quarter_000_017, quarter_000_018, quarter_000_019, quarter_000_020, quarter_000_021, quarter_000_022, quarter_000_023, quarter_000_024, quarter_000_025, quarter_000_026, quarter_000_027, quarter_000_028, quarter_000_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_000_000_valid
    · exact quarter_000_001_valid
    · exact quarter_000_002_valid
    · exact quarter_000_003_valid
    · exact quarter_000_004_valid
    · exact quarter_000_005_valid
    · exact quarter_000_006_valid
    · exact quarter_000_007_valid
    · exact quarter_000_008_valid
    · exact quarter_000_009_valid
    · exact quarter_000_010_valid
    · exact quarter_000_011_valid
    · exact quarter_000_012_valid
    · exact quarter_000_013_valid
    · exact quarter_000_014_valid
    · exact quarter_000_015_valid
    · exact quarter_000_016_valid
    · exact quarter_000_017_valid
    · exact quarter_000_018_valid
    · exact quarter_000_019_valid
    · exact quarter_000_020_valid
    · exact quarter_000_021_valid
    · exact quarter_000_022_valid
    · exact quarter_000_023_valid
    · exact quarter_000_024_valid
    · exact quarter_000_025_valid
    · exact quarter_000_026_valid
    · exact quarter_000_027_valid
    · exact quarter_000_028_valid
    · exact quarter_000_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
