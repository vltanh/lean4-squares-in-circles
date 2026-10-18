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

def quarter_008_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_008_000_valid : quarter_008_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_000]
  · intro i; fin_cases i <;> norm_num [quarter_008_000]
  · norm_num [quarter_008_000]
  · norm_num [quarter_008_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_000]

def quarter_008_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_008_001_valid : quarter_008_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_001]
  · intro i; fin_cases i <;> norm_num [quarter_008_001]
  · norm_num [quarter_008_001]
  · norm_num [quarter_008_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_001]

def quarter_008_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_008_002_valid : quarter_008_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_002]
  · intro i; fin_cases i <;> norm_num [quarter_008_002]
  · norm_num [quarter_008_002]
  · norm_num [quarter_008_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_002]

def quarter_008_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_008_003_valid : quarter_008_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_003]
  · intro i; fin_cases i <;> norm_num [quarter_008_003]
  · norm_num [quarter_008_003]
  · norm_num [quarter_008_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_003]

def quarter_008_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_008_004_valid : quarter_008_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_004]
  · intro i; fin_cases i <;> norm_num [quarter_008_004]
  · norm_num [quarter_008_004]
  · norm_num [quarter_008_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_004]

def quarter_008_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_008_005_valid : quarter_008_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_005]
  · intro i; fin_cases i <;> norm_num [quarter_008_005]
  · norm_num [quarter_008_005]
  · norm_num [quarter_008_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_005]

def quarter_008_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_008_006_valid : quarter_008_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_006]
  · intro i; fin_cases i <;> norm_num [quarter_008_006]
  · norm_num [quarter_008_006]
  · norm_num [quarter_008_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_006]

def quarter_008_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_008_007_valid : quarter_008_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_007]
  · intro i; fin_cases i <;> norm_num [quarter_008_007]
  · norm_num [quarter_008_007]
  · norm_num [quarter_008_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_007]

def quarter_008_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_008_008_valid : quarter_008_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_008]
  · intro i; fin_cases i <;> norm_num [quarter_008_008]
  · norm_num [quarter_008_008]
  · norm_num [quarter_008_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_008]

def quarter_008_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1067647938911762121/3859681000000000000), (-13528061/3859681), (-8309344188911762121/1929840500000000000), (-13528061/3859681), (-15551040438911762121/3859681000000000000)]
    bernstein := [(100068034278401520636999/617548960000000000000000), (36328949888069554679293/247019584000000000000000), (265685575963521009711/2016486400000000000000), (917720443345976065601/7904626688000000000000), (63294346623912201551/632370135040000000000)]
    reserve := (100090663863/1000000000000) }

theorem quarter_008_009_valid : quarter_008_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_009]
  · intro i; fin_cases i <;> norm_num [quarter_008_009]
  · norm_num [quarter_008_009]
  · norm_num [quarter_008_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_009]

def quarter_008_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![(3733159/20000000), (3733159/20000000), (191723/3125000), (2936479/25000000), (2936479/25000000), (2936479/25000000), (21295527/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (974521/4000000), 0, 0]] i.1) i.2
    mu := ![(6414721/100000000), (1/100000000), (5314873/100000000), (3348429/100000000), (1/100000000), (1/100000000), (3067499/100000000)]
    alternative := .zero
    polynomial := [(23092058228161086891851068526949461/2001050915842564636476129960000000000), (-530163420445956447079/681868548908660000000), (-776554341635635180548504677927121739/1000525457921282318238064980000000000), (-530163420445956447079/681868548908660000000), (-1576200741499431447988860424381192939/2001050915842564636476129960000000000)]
    bernstein := [(32106040450450227787084116004223307869/327852182051645790040249132646400000000), (64267451125824238929498547439287252531/683025379274262062583852359680000000000), (3465426767560444389079810791070085688707/38420177584177241020341695232000000000000), (460210688804672558211373377985794378347/5336135775580172363936346560000000000000), (1645440259755031138859938517037444809261/20010509158425646364761299600000000000000)]
    reserve := (8222880521/100000000000) }

theorem quarter_008_010_valid : quarter_008_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_010]
  · intro i; fin_cases i <;> norm_num [quarter_008_010]
  · norm_num [quarter_008_010]
  · norm_num [quarter_008_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_010]

def quarter_008_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![(3079259/20000000), (3079259/20000000), (3494503/50000000), (7466547/50000000), (7466547/50000000), (7466547/50000000), (17419121/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4263793/20000000), 0, 0]] i.1) i.2
    mu := ![(5422119/100000000), (1/100000000), (4579771/100000000), (4166107/100000000), (1/100000000), (1/100000000), (779969/20000000)]
    alternative := .zero
    polynomial := [(498368240289636462693919126489127047/16138031733995080261896713400000000000), (-11275567750773315097/19865650683799200000), (-4797394007432862544781376866048616953/8069015866997540130948356700000000000), (-11275567750773315097/19865650683799200000), (-10093156255155361552256672858586360953/16138031733995080261896713400000000000)]
    bernstein := [(13265512667407508606739424669838838218447/161380317339950802618967134000000000000000), (51193233650163016140557887985713267805041/645521269359803210475868536000000000000000), (591520377761549947730321060870728263307369/7746255232317638525710422432000000000000000), (252595433399419867132484849622014883018023/3442780103252283789204632192000000000000000), (2905415193231710068284973186184405346836407/41313361239027405470455586304000000000000000)]
    reserve := (70326284429/1000000000000) }

theorem quarter_008_011_valid : quarter_008_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_011]
  · intro i; fin_cases i <;> norm_num [quarter_008_011]
  · norm_num [quarter_008_011]
  · norm_num [quarter_008_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_011]

def quarter_008_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![(6446593/50000000), (6446593/50000000), (741037/10000000), (87413/500000), (87413/500000), (87413/500000), (717773/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (18921119/100000000), 0, 0]] i.1) i.2
    mu := ![(4627483/100000000), (1/100000000), (998107/25000000), (119949/2500000), (1/100000000), (1/100000000), (228283/5000000)]
    alternative := .zero
    polynomial := [(475582640628278472754917307213847/11497394974834323265557000000000000), (-2510469278623080581/5998341785300000000), (-2657301815286115360372349551006153/5748697487417161632778500000000000), (-2510469278623080581/5998341785300000000), (-5790186271200509193499616409226153/11497394974834323265557000000000000)]
    bernstein := [(2069587950023482077366275323950084995207/29433331135575867559825920000000000000000), (91100388093924182016413966993829697079/1337878687980721252719360000000000000000), (1453236378869584180916188390131896569469/22074998351681900669869440000000000000000), (21248603433349042855197866144632273231/334469671995180313179840000000000000000), (112553611852360273579318877109119171447/1839583195973491722489120000000000000000)]
    reserve := (15296075233/250000000000) }

theorem quarter_008_012_valid : quarter_008_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_012]
  · intro i; fin_cases i <;> norm_num [quarter_008_012]
  · norm_num [quarter_008_012]
  · norm_num [quarter_008_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_012]

def quarter_008_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![(10952361/100000000), (10952361/100000000), (7567779/100000000), (9770201/50000000), (9770201/50000000), (9770201/50000000), (11906293/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17009357/100000000), 0, 0]] i.1) i.2
    mu := ![(996169/25000000), (1/100000000), (1758629/50000000), (5294829/100000000), (1/100000000), (1/100000000), (637883/12500000)]
    alternative := .zero
    polynomial := [(27531223074048014778829697395378739/591698161783665578935310700000000000), (-217692544519426494483/700756676920400000000), (-107723012452440328427089859342599261/295849080891832789467655350000000000), (-217692544519426494483/700756676920400000000), (-242977247978928671633009416080577261/591698161783665578935310700000000000)]
    bernstein := [(5792755610362356372577915595270412158939/94671705885386492629649712000000000000000), (3752819981739540162965201675020448390263/63114470590257661753099808000000000000000), (65550148275461944527800771859728732563517/1136060470624637911555796544000000000000000), (14113382000931775029973400748198965983363/252457882361030647012399232000000000000000), (81906367322617219251696521347165693437539/1514747294166183882074395392000000000000000)]
    reserve := (10814525649/200000000000) }

theorem quarter_008_013_valid : quarter_008_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_013]
  · intro i; fin_cases i <;> norm_num [quarter_008_013]
  · norm_num [quarter_008_013]
  · norm_num [quarter_008_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_013]

def quarter_008_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![(94291/1000000), (94291/1000000), (7565017/100000000), (21217309/100000000), (21217309/100000000), (21217309/100000000), (1240607/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15465851/100000000), 0, 0]] i.1) i.2
    mu := ![(172957/5000000), (1/100000000), (782049/25000000), (227671/4000000), (1/100000000), (1/100000000), (1385249/25000000)]
    alternative := .zero
    polynomial := [(413701828953508337319133525116391/8531741035386012477509400000000000), (-625153520227827829/2705216977860000000), (-1237527577069044947732545646747609/4265870517693006238754700000000000), (-625153520227827829/2705216977860000000), (-2888756983091598232784224818611609/8531741035386012477509400000000000)]
    bernstein := [(1181375966886960316679125110287186399591/21841257050588191942424064000000000000000), (1439692377516562360637479506063992357/27301571313235239928030080000000000000), (2102828186224489595583034249006529191/40952356969852859892045120000000000000), (284016284220722129143236646889719/5687827356924008318339600000000000), (413701828953508337319133525116391/8531741035386012477509400000000000)]
    reserve := (48489731139/1000000000000) }

theorem quarter_008_014_valid : quarter_008_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_014]
  · intro i; fin_cases i <;> norm_num [quarter_008_014]
  · norm_num [quarter_008_014]
  · norm_num [quarter_008_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_014]

def quarter_008_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![(4464793/50000000), (4464793/50000000), (1918029/25000000), (10860763/50000000), (10860763/50000000), (10860763/50000000), (9304133/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (14976807/100000000), 0, 0]] i.1) i.2
    mu := ![(3338891/100000000), (1/100000000), (92961/3125000), (2910447/50000000), (1/100000000), (1/100000000), (2836337/50000000)]
    alternative := .zero
    polynomial := [(27687175680494672146681807490892047/569387646002549990103642000000000000), (6934133437990742573/41384886166800000000), (-76133367712325025883344083555087953/284693823001274995051821000000000000), (6934133437990742573/41384886166800000000), (-179953911105144723913369974601067953/569387646002549990103642000000000000)]
    bernstein := [(27687175680494672146681807490892047/569387646002549990103642000000000000), (10284887105628321369188050700779483/207050053091836360037688000000000000), (138546442954500932816608518460741437647/2733060700812239952497481600000000000000), (188344042051434197558542906111263155113/3644080934416319936663308800000000000000), (76744921026407794996627557890940447602447/1457632373766527974665323520000000000000000)]
    reserve := (24313115919/500000000000) }

theorem quarter_008_015_valid : quarter_008_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_015]
  · intro i; fin_cases i <;> norm_num [quarter_008_015]
  · norm_num [quarter_008_015]
  · norm_num [quarter_008_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_015]

def quarter_008_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (590619/5000000), (10004943/100000000), (6515223/25000000), (6515223/25000000), (6515223/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(590619/100000000), 0, (590619/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6805919/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3813881/100000000), (7053661/100000000), (1/100000000), (1/100000000), (6805919/100000000)]
    alternative := .zero
    polynomial := [(1668578638940527777338042022023/36618326567802342075800000000000), (5909109429717/19069405000000), (-2656917244889242517555342017977/18309163283901171037900000000000), (5909109429717/19069405000000), (-6982413128719012812448726057977/36618326567802342075800000000000)]
    bernstein := [(4989717974636042684345527037840095623/93742916013573995714048000000000000000), (29030074775192513534512943952409407/526645595581876380416000000000000000), (1335947895401416395850075360474435223/23435729003393498928512000000000000000), (7751600109122982261719669535761007/131661398895469095104000000000000000), (355843494002259888386917924625640423/5858932250848374732128000000000000000)]
    reserve := (53227680413/1000000000000) }

theorem quarter_008_016_valid : quarter_008_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_016]
  · intro i; fin_cases i <;> norm_num [quarter_008_016]
  · norm_num [quarter_008_016]
  · norm_num [quarter_008_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_016]

def quarter_008_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (12876577/100000000), (10693827/100000000), (6369133/25000000), (6369133/25000000), (6369133/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(643829/100000000), 0, (12876577/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (665331/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4016681/100000000), (1745381/25000000), (1/100000000), (1/100000000), (6653311/100000000)]
    alternative := .zero
    polynomial := [(4934788190759863863246856081747/111945502998726903290400000000000), (137699886790179/401668100000000), (-9479960700908514858657033526253/55972751499363451645200000000000), (137699886790179/401668100000000), (-23894709592576893580560923134253/111945502998726903290400000000000)]
    bernstein := [(1089743113359736434368770564930103347/17911280479796304526464000000000000000), (204818212355467102687111746261691931/3256596450872055368448000000000000000), (13956374317156184732850158756562270769/214935365757555654317568000000000000000), (872259772853251066387117656302325379/13026385803488221473792000000000000000), (19767962514495660598334508786417239107/286580487676740872423424000000000000000)]
    reserve := (3042058089/50000000000) }

theorem quarter_008_017_valid : quarter_008_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_017]
  · intro i; fin_cases i <;> norm_num [quarter_008_017]
  · norm_num [quarter_008_017]
  · norm_num [quarter_008_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_017]

def quarter_008_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (554669/4000000), (88729/781250), (24925321/100000000), (24925321/100000000), (24925321/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(86667/12500000), 0, (554669/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6509359/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4184829/100000000), (6921127/100000000), (1/100000000), (1/100000000), (81367/1250000)]
    alternative := .zero
    polynomial := [(551282189834841834527828803/13184291253535221600000000000), (49215225701/130775906250), (-1276947221491940122884771197/6592145626767610800000000000), (49215225701/130775906250), (-3105176632818722080297371197/13184291253535221600000000000)]
    bernstein := [(2332255495685758971166550062139443/33751785609050167296000000000000000), (601692200487638860906972246842881/8437946402262541824000000000000000), (465163279454378786888875798679581/6328459801696906368000000000000000), (4435072677689435184195881796501/58596850015712096000000000000000), (1140624615362919908231862713267/14649212503928024000000000000000)]
    reserve := (34550105329/500000000000) }

theorem quarter_008_018_valid : quarter_008_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_018]
  · intro i; fin_cases i <;> norm_num [quarter_008_018]
  · norm_num [quarter_008_018]
  · norm_num [quarter_008_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_018]

def quarter_008_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (14779979/100000000), (5998779/50000000), (381367/1562500), (381367/1562500), (381367/1562500), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(738999/100000000), 0, (14779979/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (50993/800000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (863799/20000000), (1718023/25000000), (1/100000000), (1/100000000), (50993/800000)]
    alternative := .zero
    polynomial := [(11726639675797891699821119111/302699863329525444000000000000), (29553942548547/71983250000000), (-33012336557334669723035640889/151349931664762722000000000000), (29553942548547/71983250000000), (-77751312790467231145892400889/302699863329525444000000000000)]
    bernstein := [(236107519751344532666163562371311/3026998633295254440000000000000000), (64870188148103014208783562991697/807199635545401184000000000000000), (480737459039971938635974294146257/5811837375926888524800000000000000), (8788439811480760473550078566361/103321553349811351552000000000000), (4334153394784246209899698284959/49594345607909448744960000000000)]
    reserve := (39000268641/500000000000) }

theorem quarter_008_019_valid : quarter_008_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_019]
  · intro i; fin_cases i <;> norm_num [quarter_008_019]
  · norm_num [quarter_008_019]
  · norm_num [quarter_008_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_019]

def quarter_008_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (1561701/10000000), (6308401/50000000), (23922063/100000000), (23922063/100000000), (23922063/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15617/2000000), 0, (1561701/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3123677/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (884123/20000000), (6833809/100000000), (1/100000000), (1/100000000), (3123677/50000000)]
    alternative := .zero
    polynomial := [(33992750382390717152182702867/976191239869038736500000000000), (229112468607/514025000000), (-118459133167081049230895947133/488095619934519368250000000000), (229112468607/514025000000), (-270911016716552815613974597133/976191239869038736500000000000)]
    bernstein := [(14002319779794441496039513020523/159939172740143306588160000000000), (180074246048249674062781196903173/1999239659251791332352000000000000), (6941187858421816689658333316325841/74971487221942174963200000000000000), (5940740156717494445850051615714289/62476239351618479136000000000000000), (15241597885086204924363410927794627/156190598379046197840000000000000000)]
    reserve := (1367934089/15625000000) }

theorem quarter_008_020_valid : quarter_008_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_020]
  · intro i; fin_cases i <;> norm_num [quarter_008_020]
  · norm_num [quarter_008_020]
  · norm_num [quarter_008_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_020]

def quarter_008_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (3276207/20000000), (6608597/50000000), (23467257/100000000), (23467257/100000000), (23467257/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(204763/25000000), 0, (3276207/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6128579/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4491627/100000000), (1701381/25000000), (1/100000000), (1/100000000), (306429/5000000)]
    alternative := .zero
    polynomial := [(2081417606486182198589050603/69384322036102119200000000000), (7217043917193/14972090000000), (-9284452470760418583304669397/34692161018051059600000000000), (7217043917193/14972090000000), (-20650322548007019365198389397/69384322036102119200000000000)]
    bernstein := [(1085259740146605398679007120880443/11101491525776339072000000000000000), (2230226815691535171366408350370767/22202983051552678144000000000000000), (13738343665828699995351091455211369/133217898309316068864000000000000000), (9396148741285657273793602907048887/88811932206210712576000000000000000), (19265522213116549325381679694088203/177623864412421425152000000000000000)]
    reserve := (97758011851/1000000000000) }

theorem quarter_008_021_valid : quarter_008_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_021]
  · intro i; fin_cases i <;> norm_num [quarter_008_021]
  · norm_num [quarter_008_021]
  · norm_num [quarter_008_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_021]

def quarter_008_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (17076973/100000000), (13800691/100000000), (23040779/100000000), (23040779/100000000), (23040779/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(853849/100000000), 0, (17076973/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3008601/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1133567/25000000), (3393203/50000000), (1/100000000), (1/100000000), (6017203/100000000)]
    alternative := .zero
    polynomial := [(6718247846398249744332359298979/277736492214366870036000000000000), (235674027588343/453426800000000), (-40710737940196282772660450981021/138868246107183435018000000000000), (235674027588343/453426800000000), (-88139723726790815289653261261021/277736492214366870036000000000000)]
    bernstein := [(77256105498895511028361941592923635779/711005420068779187292160000000000000000), (3303826166076583746037117575374182099/29625225836199132803840000000000000000), (952989014013488117764485395603095747/8332094766431006101080000000000000000), (27131066314960583805995340443539163/231447076845305725030000000000000000), (5210405640140535846743180957712451/43396326908494823443125000000000000)]
    reserve := (54328773957/500000000000) }

theorem quarter_008_022_valid : quarter_008_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_022]
  · intro i; fin_cases i <;> norm_num [quarter_008_022]
  · norm_num [quarter_008_022]
  · norm_num [quarter_008_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_022]

def quarter_008_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (17710741/100000000), (718451/5000000), (283001/1250000), (283001/1250000), (283001/1250000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(885537/100000000), 0, (17710741/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2956279/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4550911/100000000), (1693901/25000000), (1/100000000), (1/100000000), (5912559/100000000)]
    alternative := .zero
    polynomial := [(3152886573912270340799369129747/182314766483705889396000000000000), (12724299582191/22754555000000), (-29136409522771686931872655230253/91157383241852944698000000000000), (12724299582191/22754555000000), (-61425705619455644204544679590253/182314766483705889396000000000000)]
    bernstein := [(3426453159706812525719149660247243/28486682263079045218125000000000000), (5110223474341593402199341472707509/41435174200842247590000000000000000), (691182975041700692136225770225929949/5469442994511176681880000000000000000), (686337575330433713661629351989909433/5303702297707807691520000000000000000), (61812302160554709287612714360911092467/466725802198287076853760000000000000000)]
    reserve := (120282633409/1000000000000) }

theorem quarter_008_023_valid : quarter_008_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_023]
  · intro i; fin_cases i <;> norm_num [quarter_008_023]
  · norm_num [quarter_008_023]
  · norm_num [quarter_008_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_023]

def quarter_008_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (18288719/100000000), (7461833/50000000), (11131269/50000000), (11131269/50000000), (11131269/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(228609/25000000), 0, (18288719/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5813961/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (567993/12500000), (6772279/100000000), (1/100000000), (1/100000000), (2906981/50000000)]
    alternative := .zero
    polynomial := [(411057043506989487542402845423/44728054621857496428000000000000), (136467366961927/227197200000000), (-7769131180451040614609554474577/22364027310928748214000000000000), (136467366961927/227197200000000), (-15949319404409070716761511794577/44728054621857496428000000000000)]
    bernstein := [(15192238497762004323623176274195101903/114503819831955190855680000000000000000), (518795985633288027538962121289561549/3816793994398506361856000000000000000), (478047633609605861051460577628645677/3435114594958655725670400000000000000), (16305488269606819883221932139390279/114503819831955190855680000000000000), (1667569018541926189457717455087247/11450381983195519085568000000000000)]
    reserve := (207310749/1562500000) }

theorem quarter_008_024_valid : quarter_008_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_024]
  · intro i; fin_cases i <;> norm_num [quarter_008_024]
  · norm_num [quarter_008_024]
  · norm_num [quarter_008_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_024]

def quarter_008_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (9408677/50000000), (15465897/100000000), (21905583/100000000), (21905583/100000000), (21905583/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(235217/25000000), 0, (9408677/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5720741/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (564461/12500000), (1355127/20000000), (1/100000000), (1/100000000), (5720741/100000000)]
    alternative := .zero
    polynomial := [(-2307621423309990874109662057/8751776553315852654000000000000), (145513629388269/225784400000000), (-1649160396749752722895684822057/4375888276657926327000000000000), (145513629388269/225784400000000), (-3296013172076195454917259982057/8751776553315852654000000000000)]
    bernstein := [(326883821528707768582343918445527/2240454797648858279424000000000000), (1115440754329892623286221538901767/7468182658829527598080000000000000), (102711756807711276699429768305050877/672136439294657483827200000000000000), (116702351681515430569670441384459471/746818265882952759808000000000000000), (3578378380898058045890263670230913063/22404547976488582794240000000000000000)]
    reserve := (145900654577/1000000000000) }

theorem quarter_008_025_valid : quarter_008_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_025]
  · intro i; fin_cases i <;> norm_num [quarter_008_025]
  · norm_num [quarter_008_025]
  · norm_num [quarter_008_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_025]

def quarter_008_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (3860579/20000000), (7998389/50000000), (2695847/12500000), (2695847/12500000), (2695847/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(193029/20000000), 0, (3860579/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (281613/5000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (893669/20000000), (678493/10000000), (1/100000000), (1/100000000), (5632261/100000000)]
    alternative := .zero
    polynomial := [(-30688519622984753259636512289/2732088878873053789600000000000), (4411201801033/6383350000000), (-558060767218527509559645432289/1366044439436526894800000000000), (4411201801033/6383350000000), (-1085433014814070265859654352289/2732088878873053789600000000000)]
    bernstein := [(1119137183916955628365291941339915951/6994147529915017701376000000000000000), (286233034279966618088764751561943223/1748536882478754425344000000000000000), (219508777794906875050700021275914137/1311402661859065819008000000000000000), (18695127461884592847450832827616067/109283555154922151584000000000000000), (4774461015370825055897229480614391/27320888788730537896000000000000000)]
    reserve := (160010520099/1000000000000) }

theorem quarter_008_026_valid : quarter_008_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_026]
  · intro i; fin_cases i <;> norm_num [quarter_008_026]
  · norm_num [quarter_008_026]
  · norm_num [quarter_008_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_026]

def quarter_008_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (3950243/20000000), (2064651/12500000), (21243859/100000000), (21243859/100000000), (21243859/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(987561/100000000), 0, (3950243/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5547929/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2201983/50000000), (3399743/50000000), (1/100000000), (1/100000000), (5547929/100000000)]
    alternative := .zero
    polynomial := [(-794310798909964032513080722673/33226219632360476640800000000000), (8155873160193/11009915000000), (-7356892874869691348862266442673/16613109816180238320400000000000), (8155873160193/11009915000000), (-13919474950829418665211452162673/33226219632360476640800000000000)]
    bernstein := [(8310292927834416022929667745497441/47466028046229252344000000000000000), (33988569651050692182911426602790611/189864112184917009376000000000000000), (2917817354849640706280750325360223001/15948585423533028787584000000000000000), (3974141022798087673164304475998012257/21264780564710705050112000000000000000), (16231558978109516218913507865258258047/85059122258842820200448000000000000000)]
    reserve := (7003150059/40000000000) }

theorem quarter_008_027_valid : quarter_008_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_027]
  · intro i; fin_cases i <;> norm_num [quarter_008_027]
  · norm_num [quarter_008_027]
  · norm_num [quarter_008_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_027]

def quarter_008_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (20167713/100000000), (17027943/100000000), (20934781/100000000), (20934781/100000000), (20934781/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(504193/50000000), 0, (20167713/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1366803/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4324437/100000000), (681869/10000000), (1/100000000), (1/100000000), (1366803/25000000)]
    alternative := .zero
    polynomial := [(-68965333188182650916084497607/1791240607762399404000000000000), (38157185267151/48049300000000), (-430217598101159084628515017607/895620303881199702000000000000), (38157185267151/48049300000000), (-791469863014135518340945537607/1791240607762399404000000000000)]
    bernstein := [(876683831746738474135613989391020873/4585575955871742474240000000000000000), (49775994142256787924033572064348483/254754219770652359680000000000000000), (686443943885029147268585454724808899/3439181966903806855680000000000000000), (564347741062353808976374274436141/2769067606202743040000000000000000), (59617177546417855923131525897691193/286598497241983904640000000000000000)]
    reserve := (191182926677/1000000000000) }

theorem quarter_008_028_valid : quarter_008_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_028]
  · intro i; fin_cases i <;> norm_num [quarter_008_028]
  · norm_num [quarter_008_028]
  · norm_num [quarter_008_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_028]

def quarter_008_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 0, 0]
    lambda := ![0, (20557271/100000000), (8764813/50000000), (20637701/100000000), (20637701/100000000), (20637701/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(128483/12500000), 0, (20557271/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1347407/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (264467/6250000), (1710499/25000000), (1/100000000), (1/100000000), (1347407/25000000)]
    alternative := .zero
    polynomial := [(-577498433198115406966802171/10449038243774355960000000000), (25740090872189/30224800000000), (-2725535541864450390168653771/5224519121887177980000000000), (25740090872189/30224800000000), (-4873572650530785373370505371/10449038243774355960000000000)]
    bernstein := [(348425445690203422960212164954029/1671846119003896953600000000000000), (142377099761428925528062200894251/668738447601558781440000000000000), (174463308779454141758385402683371/802486137121870537728000000000000), (23743627175444063298862574818327/106998151616249405030400000000000), (9690383002825532373642685463941/42799260646499762012160000000000)]
    reserve := (208407605059/1000000000000) }

theorem quarter_008_029_valid : quarter_008_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_008_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_008_029]
  · intro i; fin_cases i <;> norm_num [quarter_008_029]
  · norm_num [quarter_008_029]
  · norm_num [quarter_008_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_008_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_008_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_008_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_008_029]

def quarterTable008 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 2, 0, 0, 0]
  rows := [quarter_008_000, quarter_008_001, quarter_008_002, quarter_008_003, quarter_008_004, quarter_008_005, quarter_008_006, quarter_008_007, quarter_008_008, quarter_008_009, quarter_008_010, quarter_008_011, quarter_008_012, quarter_008_013, quarter_008_014, quarter_008_015, quarter_008_016, quarter_008_017, quarter_008_018, quarter_008_019, quarter_008_020, quarter_008_021, quarter_008_022, quarter_008_023, quarter_008_024, quarter_008_025, quarter_008_026, quarter_008_027, quarter_008_028, quarter_008_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_008_000_valid
    · exact quarter_008_001_valid
    · exact quarter_008_002_valid
    · exact quarter_008_003_valid
    · exact quarter_008_004_valid
    · exact quarter_008_005_valid
    · exact quarter_008_006_valid
    · exact quarter_008_007_valid
    · exact quarter_008_008_valid
    · exact quarter_008_009_valid
    · exact quarter_008_010_valid
    · exact quarter_008_011_valid
    · exact quarter_008_012_valid
    · exact quarter_008_013_valid
    · exact quarter_008_014_valid
    · exact quarter_008_015_valid
    · exact quarter_008_016_valid
    · exact quarter_008_017_valid
    · exact quarter_008_018_valid
    · exact quarter_008_019_valid
    · exact quarter_008_020_valid
    · exact quarter_008_021_valid
    · exact quarter_008_022_valid
    · exact quarter_008_023_valid
    · exact quarter_008_024_valid
    · exact quarter_008_025_valid
    · exact quarter_008_026_valid
    · exact quarter_008_027_valid
    · exact quarter_008_028_valid
    · exact quarter_008_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
