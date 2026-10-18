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

def quarter_040_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_040_000_valid : quarter_040_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_000]
  · intro i; fin_cases i <;> norm_num [quarter_040_000]
  · norm_num [quarter_040_000]
  · norm_num [quarter_040_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_000]

def quarter_040_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_040_001_valid : quarter_040_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_001]
  · intro i; fin_cases i <;> norm_num [quarter_040_001]
  · norm_num [quarter_040_001]
  · norm_num [quarter_040_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_001]

def quarter_040_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_040_002_valid : quarter_040_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_002]
  · intro i; fin_cases i <;> norm_num [quarter_040_002]
  · norm_num [quarter_040_002]
  · norm_num [quarter_040_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_002]

def quarter_040_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_040_003_valid : quarter_040_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_003]
  · intro i; fin_cases i <;> norm_num [quarter_040_003]
  · norm_num [quarter_040_003]
  · norm_num [quarter_040_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_003]

def quarter_040_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_040_004_valid : quarter_040_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_004]
  · intro i; fin_cases i <;> norm_num [quarter_040_004]
  · norm_num [quarter_040_004]
  · norm_num [quarter_040_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_004]

def quarter_040_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_040_005_valid : quarter_040_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_005]
  · intro i; fin_cases i <;> norm_num [quarter_040_005]
  · norm_num [quarter_040_005]
  · norm_num [quarter_040_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_005]

def quarter_040_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_040_006_valid : quarter_040_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_006]
  · intro i; fin_cases i <;> norm_num [quarter_040_006]
  · norm_num [quarter_040_006]
  · norm_num [quarter_040_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_006]

def quarter_040_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_040_007_valid : quarter_040_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_007]
  · intro i; fin_cases i <;> norm_num [quarter_040_007]
  · norm_num [quarter_040_007]
  · norm_num [quarter_040_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_007]

def quarter_040_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_040_008_valid : quarter_040_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_008]
  · intro i; fin_cases i <;> norm_num [quarter_040_008]
  · norm_num [quarter_040_008]
  · norm_num [quarter_040_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_008]

def quarter_040_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1067647938911762121/3859681000000000000), (-13528061/3859681), (-8309344188911762121/1929840500000000000), (-13528061/3859681), (-15551040438911762121/3859681000000000000)]
    bernstein := [(100068034278401520636999/617548960000000000000000), (36328949888069554679293/247019584000000000000000), (265685575963521009711/2016486400000000000000), (917720443345976065601/7904626688000000000000), (63294346623912201551/632370135040000000000)]
    reserve := (100090663863/1000000000000) }

theorem quarter_040_009_valid : quarter_040_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_009]
  · intro i; fin_cases i <;> norm_num [quarter_040_009]
  · norm_num [quarter_040_009]
  · norm_num [quarter_040_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_009]

def quarter_040_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (32317707/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(20098469/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-24605763504485237/100492345000000000), (-64635414/20098469), (-205892376004485237/50246172500000000), (-64635414/20098469), (-387178988504485237/100492345000000000)]
    bernstein := [(1621018638741994947/16464665804800000000), (8644294675777045439/102904161280000000000), (44514715284066379727/643151008000000000000), (43476776959806276103/803938760000000000000), (38785551465746097363/1004923450000000000000)]
    reserve := (38595528311/1000000000000) }

theorem quarter_040_010_valid : quarter_040_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_010]
  · intro i; fin_cases i <;> norm_num [quarter_040_010]
  · norm_num [quarter_040_010]
  · norm_num [quarter_040_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_010]

def quarter_040_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![(4702763/50000000), (4132829/20000000), (4479837/20000000), (4479837/20000000), (1705983/25000000), (7208541/100000000), (5549743/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (778189/20000000), 0, 0]] i.1) i.2
    mu := ![(169747/5000000), (2868421/50000000), (1167301/100000000), (1/100000000), (118333/2000000), (627037/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(193246838737511913655546340829465889827/21086131282290504863777152713500000000000), (-61175892253059/84873500000000), (-43952733089906699783196368474290053657673/10543065641145252431888576356750000000000), (-61175892253059/84873500000000), (-88098713018550911480048283289409573205173/21086131282290504863777152713500000000000)]
    bernstein := [(8404462823945239422452757494750172192720227/210861312822905048637771527135000000000000000), (1102824842249083439579927934339860726450351/27207911331987748211325358340000000000000000), (412655877434428531549360627090648944513392429/10121343015499442334613033302480000000000000000), (17663092493016251531254899111215067842183859/435326581311803971381205733440000000000000000), (2156293165080074083369812012243708659495038587/53980496082663692451269510946560000000000000000)]
    reserve := (3985777529/100000000000) }

theorem quarter_040_011_valid : quarter_040_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_011]
  · intro i; fin_cases i <;> norm_num [quarter_040_011]
  · norm_num [quarter_040_011]
  · norm_num [quarter_040_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_011]

def quarter_040_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![(8707651/100000000), (10746771/50000000), (4568129/20000000), (4568129/20000000), (6889883/100000000), (3625571/50000000), (9976493/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2725351/100000000), 0, 0]] i.1) i.2
    mu := ![(635273/20000000), (1171951/20000000), (225993/25000000), (1/100000000), (1205647/20000000), (1263713/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(95106008914954803962530856034421553141/4660910594466579366398042467800000000000), (-223414488317603/317636500000000), (-13026055113492986340902596794360865343359/2330455297233289683199021233900000000000), (-223414488317603/317636500000000), (-26147216235900927485767724444756152239859/4660910594466579366398042467800000000000)]
    bernstein := [(499181622366639663446964630204697484372520221/11931931121834443177978988717568000000000000000), (23139743229499562412655214675183244530199437/542360505537929235362681305344000000000000000), (383985918566044578967107590648300081365750607/8948948341375832383484241538176000000000000000), (5772135248924159697348832382481308463465493/135590126384482308840670326336000000000000000), (31062118356627094354321047933375200396664941/745745695114652698623686794848000000000000000)]
    reserve := (10413106827/250000000000) }

theorem quarter_040_012_valid : quarter_040_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_012]
  · intro i; fin_cases i <;> norm_num [quarter_040_012]
  · norm_num [quarter_040_012]
  · norm_num [quarter_040_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_012]

def quarter_040_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![(9309501/100000000), (13061571/50000000), (2714621/10000000), (2714621/10000000), 0, 0, (10274937/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8040927/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (10274937/100000000), 0, 0]] i.1) i.2
    mu := ![(1707609/50000000), (350371/5000000), (720047/100000000), (1/100000000), (7056547/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(23571947109525142851997347296078709/810659364354928012479133600000000000), (-2228349478263/2776600000000), (-4051646001961093798048158272305833291/405329682177464006239566800000000000), (-2228349478263/2776600000000), (-8126863951031712738948313891907745291/810659364354928012479133600000000000)]
    bernstein := [(5739811738714027086345595306848606021909/129705498296788481996661376000000000000000), (11797466860440272703012863363382604885509/259410996593576963993322752000000000000000), (3384111438724511124360862097323192107187/74117427598164846855235072000000000000000), (46486445917286556712337725893000715056309/1037643986374307855973291008000000000000000), (89034670483287846208220129198483198683509/2075287972748615711946582016000000000000000)]
    reserve := (42902320859/1000000000000) }

theorem quarter_040_013_valid : quarter_040_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_013]
  · intro i; fin_cases i <;> norm_num [quarter_040_013]
  · norm_num [quarter_040_013]
  · norm_num [quarter_040_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_013]

def quarter_040_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![(844059/10000000), (6826839/25000000), (27677217/100000000), (27677217/100000000), 0, 0, (8897619/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1024777/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8897619/100000000), 0, 0]] i.1) i.2
    mu := ![(774731/25000000), (180553/2500000), (359579/100000000), (1/100000000), (359729/5000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(3811801534564881474949244287413/93266071448388330464500000000000), (-122173997862549/154946200000000), (-95511703032256302290150275131465939/4523404465246834027528250000000000), (-122173997862549/154946200000000), (-191393150813365398083370626958810939/9046808930493668055056500000000000)]
    bernstein := [(1097537175083711259604301112924199044261/23159830862063790220944640000000000000000), (5680998804763923653086587420882869163/115799154310318951104723200000000000000), (702421278522006102255589909595692287/14474894288789868888090400000000000000), (34171394614189720135681169623179/746128571587106643716000000000000), (3811801534564881474949244287413/93266071448388330464500000000000)]
    reserve := (40870184359/1000000000000) }

theorem quarter_040_014_valid : quarter_040_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_014]
  · intro i; fin_cases i <;> norm_num [quarter_040_014]
  · norm_num [quarter_040_014]
  · norm_num [quarter_040_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_014]

def quarter_040_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (33340277/100000000), (16664931/50000000), (1666493/5000000), 0, 0, (1/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2468911/25000000), 0, 0], ![(166673/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2468139/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2166667/25000000), (6581/3125000), (1/100000000), (216599/2500000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(583584763109330399970005807/12353798065250692000000000000), (27784620363289/21059200000000), (-325351680718172117688327877943/6176899032625346000000000000), (27784620363289/21059200000000), (-651286946199453565776625761693/12353798065250692000000000000)]
    bernstein := [(583584763109330399970005807/12353798065250692000000000000), (10967264227564420057417347537/197660769044011072000000000000), (3453799992895693996906052770657/59298230713203321600000000000000), (17559331437638561047783622066737/316257230470417715200000000000000), (1495993422924347188272190892590707/31625723047041771520000000000000000)]
    reserve := (47239299203/1000000000000) }

theorem quarter_040_015_valid : quarter_040_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_015]
  · intro i; fin_cases i <;> norm_num [quarter_040_015]
  · norm_num [quarter_040_015]
  · norm_num [quarter_040_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_015]

def quarter_040_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (33395863/100000000), (33302069/100000000), (33302069/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (79137/800000), 0, 0], ![(625293/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4932171/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8681119/100000000), (52687/25000000), (1/100000000), (8656737/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1641884147243693832309393073/833565619628213676000000000000), (1099063124361/277300000000), (-21995945882204080461362430588073/416782809814106838000000000000), (1099063124361/277300000000), (-43990249880260917228892551783073/833565619628213676000000000000)]
    bernstein := [(136940532833435394509548573832303327/2133927986248227010560000000000000000), (25777133053688872417640319666533909/355654664374704501760000000000000000), (120506983682288843534064657245311181/1600445989686170257920000000000000000), (6457046677331210329069685740723109/88913666093676125440000000000000000), (8592955110668920369672673672478527/133370499140514188160000000000000000)]
    reserve := (64172986959/1000000000000) }

theorem quarter_040_016_valid : quarter_040_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_016]
  · intro i; fin_cases i <;> norm_num [quarter_040_016]
  · norm_num [quarter_040_016]
  · norm_num [quarter_040_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_016]

def quarter_040_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (33507171/100000000), (6649283/20000000), (6649283/20000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1985019/20000000), 0, 0], ![(4172099/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9847857/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8710053/100000000), (210989/100000000), (1/100000000), (864227/10000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-502354664585921049564789107909/4235231694474204424000000000000), (139795234621929/21098900000000), (-112309600177623056401467601307909/2117615847237102212000000000000), (139795234621929/21098900000000), (-224116845690660191753370413507909/4235231694474204424000000000000)]
    bernstein := [(54604088399840264026189195487524891/677637071115872707840000000000000000), (10963999278845591712812430876179843/123206740202885946880000000000000000), (747244496163463772311707478680953257/8131644853390472494080000000000000000), (43999089545395384560154390178732587/492826960811543787520000000000000000), (879402125597597061099121676482240171/10842193137853963325440000000000000000)]
    reserve := (1611602751/20000000000) }

theorem quarter_040_017_valid : quarter_040_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_017]
  · intro i; fin_cases i <;> norm_num [quarter_040_017]
  · norm_num [quarter_040_017]
  · norm_num [quarter_040_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_017]

def quarter_040_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (16837241/50000000), (33162759/100000000), (33162759/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4987327/50000000), 0, 0], ![(5848259/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4911539/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1094193/12500000), (211319/100000000), (1/100000000), (2155131/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-134627794245424826661206512079/442948903009626024000000000000), (98468546213419/10565950000000), (-11838691220909077208893802752079/221474451504813012000000000000), (98468546213419/10565950000000), (-23542754647572729591126398992079/442948903009626024000000000000)]
    bernstein := [(109531169316043217448279260337926401/1133949191704642621440000000000000000), (29808202035797643574485546801190267/283487297926160655360000000000000000), (22998051598270191562069117530317167/212615473444620491520000000000000000), (1871440976126372745869457149008463/17717956120385040960000000000000000), (431749059553815624883857934602121/4429489030096260240000000000000000)]
    reserve := (19318532103/200000000000) }

theorem quarter_040_018_valid : quarter_040_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_018]
  · intro i; fin_cases i <;> norm_num [quarter_040_018]
  · norm_num [quarter_040_018]
  · norm_num [quarter_040_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_018]

def quarter_040_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (4237277/12500000), (8262723/25000000), (8262723/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5020463/50000000), 0, 0], ![(301271/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4894971/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8811703/100000000), (211737/100000000), (1/100000000), (1718289/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-398856997773311486740558744873/712426888556220462000000000000), (1276568679067/105868500000), (-19247217465244228275575270104873/356213444278110231000000000000), (1276568679067/105868500000), (-38095577932715145064409981464873/712426888556220462000000000000)]
    bernstein := [(800281667849622926243993388830527/7124268885562204620000000000000000), (230023963691490043405185212891329/1899805036149921232000000000000000), (1699398227188068548568147131285249/13678596260279432870400000000000000), (29612787328011806333208409045577/243175044627189917696000000000000), (4421266263846078582487873414821/38908007140350386831360000000000)]
    reserve := (28082940183/250000000000) }

theorem quarter_040_019_valid : quarter_040_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_019]
  · intro i; fin_cases i <;> norm_num [quarter_040_019]
  · norm_num [quarter_040_019]
  · norm_num [quarter_040_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_019]

def quarter_040_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (1708947/5000000), (3291053/10000000), (3291053/10000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10124079/100000000), 0, 0], ![(4612401/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1949673/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2221169/25000000), (42449/20000000), (1/100000000), (4277479/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-337442807510334332325344389521/379584101937898352000000000000), (7882348851747/530612500000), (-10395961260017558030662217989521/189792050968949176000000000000), (7882348851747/530612500000), (-20454479712524781728999091589521/379584101937898352000000000000)]
    bernstein := [(7954774143804130540935625434951/62191059261505265991680000000000), (106414909511493600727779600077001/777388240768815824896000000000000), (1362519324658474023100045959352439/9717353009610197811200000000000000), (3348683706567641559905159912123493/24293382524025494528000000000000000), (7877409083534635929990491512537599/60733456310063736320000000000000000)]
    reserve := (63954322681/500000000000) }

theorem quarter_040_020_valid : quarter_040_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_020]
  · intro i; fin_cases i <;> norm_num [quarter_040_020]
  · norm_num [quarter_040_020]
  · norm_num [quarter_040_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_020]

def quarter_040_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (17258683/50000000), (32741317/100000000), (32741317/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10224323/100000000), 0, 0], ![(85387/781250), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9698243/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8972649/100000000), (106421/50000000), (1/100000000), (2127743/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-6012198133711551225963951509447/4643967027386400336000000000000), (1473667165321/83141406250), (-129304395522991623624323400389447/2321983513693200168000000000000), (1473667165321/83141406250), (-252596592912271696022682849269447/4643967027386400336000000000000)]
    bernstein := [(15224297668399449863668274562405199/106147817768832007680000000000000000), (226894147838926295983238707416861317/1486069448763648107520000000000000000), (1392755120415949223152664679861445219/8916416692581888645120000000000000000), (914994914011538352069613367177837437/5944277795054592430080000000000000000), (1733157144156703846372358702032048153/11888555590109184860160000000000000000)]
    reserve := (71712720941/500000000000) }

theorem quarter_040_021_valid : quarter_040_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_021]
  · intro i; fin_cases i <;> norm_num [quarter_040_021]
  · norm_num [quarter_040_021]
  · norm_num [quarter_040_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_021]

def quarter_040_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (34914361/100000000), (32542819/100000000), (32542819/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2585479/25000000), 0, 0], ![(12648221/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9639447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4537923/50000000), (53383/25000000), (1/100000000), (8459373/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1084906244690857865820446053/609220576031381600000000000), (441604554001781/21353200000000), (-17293333200913729839346317053/304610288015690800000000000), (441604554001781/21353200000000), (-33501760157136601812872188053/609220576031381600000000000)]
    bernstein := [(247939312296245145766976149054347/1559604674640336896000000000000000), (32858999968443855434139242902321/194950584330042112000000000000000), (3148873672477164757451072749921/18276617280941448000000000000000), (19931374212420788902173400529/117157803082958000000000000000), (1185949137472181599175775311/7322362692684875000000000000)]
    reserve := (15897574323/100000000000) }

theorem quarter_040_022_valid : quarter_040_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_022]
  · intro i; fin_cases i <;> norm_num [quarter_040_022]
  · norm_num [quarter_040_022]
  · norm_num [quarter_040_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_022]

def quarter_040_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (8842737/25000000), (16157263/50000000), (16157263/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10477161/100000000), 0, 0], ![(14383163/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (598239/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4597267/50000000), (107157/50000000), (1/100000000), (8400029/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-77873722197546883566566035225213/33104805932563661208000000000000), (42395509212377/1785950000000), (-960658830050364019988310264505213/16552402966281830604000000000000), (42395509212377/1785950000000), (-1843443937903181156410054493785213/33104805932563661208000000000000)]
    bernstein := [(903374143861895220207428397899003/5172625926963072063750000000000000), (1388769605769629120653550195052389/7523819530128104820000000000000000), (187274115021840695041040351573625629/993144177976909836240000000000000000), (179623453229712439315891613865881993/963048899856397416960000000000000000), (15112786586261557969312628737703527907/84748303187362972692480000000000000000)]
    reserve := (43661292959/250000000000) }

theorem quarter_040_023_valid : quarter_040_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_023]
  · intro i; fin_cases i <;> norm_num [quarter_040_023]
  · norm_num [quarter_040_023]
  · norm_num [quarter_040_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_023]

def quarter_040_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (35888317/100000000), (16027921/50000000), (16027921/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1063041/10000000), 0, 0], ![(8068369/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11869/125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4664511/50000000), (26899/12500000), (1/100000000), (4166393/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5794096913512966776615734609/1921912384721911312500000000), (289560184344973/10759600000000), (-457339445150699468253631303747/7687649538887645250000000000), (289560184344973/10759600000000), (-434163057496647601147168365311/7687649538887645250000000000)]
    bernstein := [(3749340215277918525581340551498329/19680382819552371840000000000000000), (197647295239060906226489699135723/984019140977618592000000000000000), (2816279390548937428441861161427/13730499641548166400000000000000), (499833162188817794146192893859/2460047852444046480000000000000), (10369372086785850954094202233/53190223836628032000000000000)]
    reserve := (19051154897/100000000000) }

theorem quarter_040_024_valid : quarter_040_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_024]
  · intro i; fin_cases i <;> norm_num [quarter_040_024]
  · norm_num [quarter_040_024]
  · norm_num [quarter_040_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_024]

def quarter_040_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (36467829/100000000), (15883043/50000000), (15883043/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5401033/50000000), 0, 0], ![(17911403/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2352343/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (592479/6250000), (108083/50000000), (1/100000000), (1651493/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-6386805025936356762464391877439/1692104078437299216000000000000), (653189981754087/21616600000000), (-51726992056443817457429440597439/846052039218649608000000000000), (653189981754087/21616600000000), (-97067179086951278152394489317439/1692104078437299216000000000000)]
    bernstein := [(3086699134941805056539940106901/14937194623446503424000000000000), (104657924588572098994631481267203/481309604533276221440000000000000), (28848945801298878061541055775459579/129953593223984579788800000000000000), (10597933306593419549233002796342139/48130960453327622144000000000000000), (917912298990240571547668151719954801/4331786440799485992960000000000000000)]
    reserve := (206645170847/1000000000000) }

theorem quarter_040_025_valid : quarter_040_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_025]
  · intro i; fin_cases i <;> norm_num [quarter_040_025]
  · norm_num [quarter_040_025]
  · norm_num [quarter_040_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_025]

def quarter_040_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (9277757/25000000), (15722243/50000000), (15722243/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10992587/100000000), 0, 0], ![(1970971/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9314111/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (9646861/100000000), (5431/2500000), (1/100000000), (4086933/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-118597833625114211294884972747/25566926683591272000000000000), (18286189992047/543100000000), (-805280715386472568798710484747/12783463341795636000000000000), (18286189992047/543100000000), (-1491963597147830926302535996747/25566926683591272000000000000)]
    bernstein := [(14602763282212854945483211658868773/65451332309993656320000000000000000), (3835572340589528190314924384712829/16362833077498414080000000000000000), (2936473009933712603670033916030451/12272124808123810560000000000000000), (242994689763121589147601747331841/1022677067343650880000000000000000), (58610962754307702238180617048893/255669266835912720000000000000000)]
    reserve := (223108724709/1000000000000) }

theorem quarter_040_026_valid : quarter_040_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_026]
  · intro i; fin_cases i <;> norm_num [quarter_040_026]
  · norm_num [quarter_040_026]
  · norm_num [quarter_040_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_026]

def quarter_040_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (756393/2000000), (1243607/4000000), (1243607/4000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11202487/100000000), 0, 0], ![(269179/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4604581/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1228883/12500000), (43683/20000000), (1/100000000), (2020441/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-19490474642466906879295103037451/3470716529643367968000000000000), (67868370449/1820125000), (-112912087231596094705537223037451/1735358264821683984000000000000), (67868370449/1820125000), (-206333699820725282531779343037451/3470716529643367968000000000000)]
    bernstein := [(8328232418962804003142579292044669/34707165296433679680000000000000000), (34957625587007847844259144474932199/138828661185734718720000000000000000), (428189324206617640954910705134472387/1665943934228816624640000000000000000), (567502680411304651923314000642890459/2221258578971755499520000000000000000), (2194902829288820418259190353459301189/8885034315887021998080000000000000000)]
    reserve := (47991429711/200000000000) }

theorem quarter_040_027_valid : quarter_040_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_027]
  · intro i; fin_cases i <;> norm_num [quarter_040_027]
  · norm_num [quarter_040_027]
  · norm_num [quarter_040_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_027]

def quarter_040_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (9648909/25000000), (15351091/50000000), (15351091/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (571617/5000000), 0, 0], ![(11694007/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1818847/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5016389/50000000), (13731/6250000), (1/100000000), (7980907/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2952891921884274992970590175719/439780137854963690400000000000), (37611469796121/915400000000), (-14813061790412771300755979649719/219890068927481845200000000000), (37611469796121/915400000000), (-26673231658941267608541369123719/439780137854963690400000000000)]
    bernstein := [(289607216084096504557827853289266441/1125837152908707047424000000000000000), (4600269966678541350906261206909403/17058138680434955264000000000000000), (232438801164546206321781028624982083/844377864681530285568000000000000000), (1167965567649276431619821422774563/4264534670108738816000000000000000), (18668663250540358251881234838485881/70364822056794190464000000000000000)]
    reserve := (128618608533/500000000000) }

theorem quarter_040_028_valid : quarter_040_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_028]
  · intro i; fin_cases i <;> norm_num [quarter_040_028]
  · norm_num [quarter_040_028]
  · norm_num [quarter_040_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_028]

def quarter_040_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 0]
    lambda := ![0, (19720573/50000000), (30279427/100000000), (30279427/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11682787/100000000), 0, 0], ![(6318427/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8969011/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2050513/20000000), (44217/20000000), (1/100000000), (3935507/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-22680415425699938123471916482143/2854581696460229976000000000000), (124603000898671/2763562500000), (-33259901940493286369482729819381/475763616076704996000000000000), (124603000898671/2763562500000), (-10404646836309398829024968378479/167916570380013528000000000000)]
    bernstein := [(125595674631704441966965824124417057/456733071433636796160000000000000000), (52630386664879708104060371205200533/182693228573454718464000000000000000), (21490539329017527592283827192235081/73077291429381887385600000000000000), (8559427822631408010058551107844541/29230916571752754954240000000000000), (3322013469597050272138188119811953/11692366628701101981696000000000000)]
    reserve := (274987038353/1000000000000) }

theorem quarter_040_029_valid : quarter_040_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_040_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_040_029]
  · intro i; fin_cases i <;> norm_num [quarter_040_029]
  · norm_num [quarter_040_029]
  · norm_num [quarter_040_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_040_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_040_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_040_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_040_029]

def quarterTable040 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 0, 0, 2, 0]
  rows := [quarter_040_000, quarter_040_001, quarter_040_002, quarter_040_003, quarter_040_004, quarter_040_005, quarter_040_006, quarter_040_007, quarter_040_008, quarter_040_009, quarter_040_010, quarter_040_011, quarter_040_012, quarter_040_013, quarter_040_014, quarter_040_015, quarter_040_016, quarter_040_017, quarter_040_018, quarter_040_019, quarter_040_020, quarter_040_021, quarter_040_022, quarter_040_023, quarter_040_024, quarter_040_025, quarter_040_026, quarter_040_027, quarter_040_028, quarter_040_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_040_000_valid
    · exact quarter_040_001_valid
    · exact quarter_040_002_valid
    · exact quarter_040_003_valid
    · exact quarter_040_004_valid
    · exact quarter_040_005_valid
    · exact quarter_040_006_valid
    · exact quarter_040_007_valid
    · exact quarter_040_008_valid
    · exact quarter_040_009_valid
    · exact quarter_040_010_valid
    · exact quarter_040_011_valid
    · exact quarter_040_012_valid
    · exact quarter_040_013_valid
    · exact quarter_040_014_valid
    · exact quarter_040_015_valid
    · exact quarter_040_016_valid
    · exact quarter_040_017_valid
    · exact quarter_040_018_valid
    · exact quarter_040_019_valid
    · exact quarter_040_020_valid
    · exact quarter_040_021_valid
    · exact quarter_040_022_valid
    · exact quarter_040_023_valid
    · exact quarter_040_024_valid
    · exact quarter_040_025_valid
    · exact quarter_040_026_valid
    · exact quarter_040_027_valid
    · exact quarter_040_028_valid
    · exact quarter_040_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
