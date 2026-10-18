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

def quarter_020_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_020_000_valid : quarter_020_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_000]
  · intro i; fin_cases i <;> norm_num [quarter_020_000]
  · norm_num [quarter_020_000]
  · norm_num [quarter_020_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_000]

def quarter_020_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_020_001_valid : quarter_020_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_001]
  · intro i; fin_cases i <;> norm_num [quarter_020_001]
  · norm_num [quarter_020_001]
  · norm_num [quarter_020_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_001]

def quarter_020_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_020_002_valid : quarter_020_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_002]
  · intro i; fin_cases i <;> norm_num [quarter_020_002]
  · norm_num [quarter_020_002]
  · norm_num [quarter_020_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_002]

def quarter_020_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_020_003_valid : quarter_020_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_003]
  · intro i; fin_cases i <;> norm_num [quarter_020_003]
  · norm_num [quarter_020_003]
  · norm_num [quarter_020_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_003]

def quarter_020_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_020_004_valid : quarter_020_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_004]
  · intro i; fin_cases i <;> norm_num [quarter_020_004]
  · norm_num [quarter_020_004]
  · norm_num [quarter_020_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_004]

def quarter_020_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_020_005_valid : quarter_020_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_005]
  · intro i; fin_cases i <;> norm_num [quarter_020_005]
  · norm_num [quarter_020_005]
  · norm_num [quarter_020_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_005]

def quarter_020_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_020_006_valid : quarter_020_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_006]
  · intro i; fin_cases i <;> norm_num [quarter_020_006]
  · norm_num [quarter_020_006]
  · norm_num [quarter_020_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_006]

def quarter_020_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_020_007_valid : quarter_020_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_007]
  · intro i; fin_cases i <;> norm_num [quarter_020_007]
  · norm_num [quarter_020_007]
  · norm_num [quarter_020_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_007]

def quarter_020_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_020_008_valid : quarter_020_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_008]
  · intro i; fin_cases i <;> norm_num [quarter_020_008]
  · norm_num [quarter_020_008]
  · norm_num [quarter_020_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_008]

def quarter_020_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1067647938911762121/3859681000000000000), (-13528061/3859681), (-8309344188911762121/1929840500000000000), (-13528061/3859681), (-15551040438911762121/3859681000000000000)]
    bernstein := [(100068034278401520636999/617548960000000000000000), (36328949888069554679293/247019584000000000000000), (265685575963521009711/2016486400000000000000), (917720443345976065601/7904626688000000000000), (63294346623912201551/632370135040000000000)]
    reserve := (100090663863/1000000000000) }

theorem quarter_020_009_valid : quarter_020_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_009]
  · intro i; fin_cases i <;> norm_num [quarter_020_009]
  · norm_num [quarter_020_009]
  · norm_num [quarter_020_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_009]

def quarter_020_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, (49999999/50000000)]
    cone := fun i => (![![0, 0, (64635413/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (49999999/50000000), 0, 0]] i.1) i.2
    mu := ![(20098469/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-39369220089951593/160787752000000000), (-3231770585364587/1004923450000000), (-329427792288780033/80393876000000000), (-3231770585364587/1004923450000000), (-619486364487608473/160787752000000000)]
    bernstein := [(2593629737457618431/26343465287680000000), (13830871045147754459/164646658048000000000), (71223542314157778683/1029041612800000000000), (69562841203257245827/1286302016000000000000), (62056880873157714127/1607877520000000000000)]
    reserve := (9648881849/250000000000) }

theorem quarter_020_010_valid : quarter_020_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_010]
  · intro i; fin_cases i <;> norm_num [quarter_020_010]
  · norm_num [quarter_020_010]
  · norm_num [quarter_020_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_010]

def quarter_020_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![(2656387/25000000), (10028349/100000000), (7684811/100000000), (19794737/100000000), (19794737/100000000), (19794737/100000000), (306927/2500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4361641/25000000), 0, 0]] i.1) i.2
    mu := ![(3787779/100000000), (108113/20000000), (3192421/100000000), (2682719/50000000), (1/100000000), (1/100000000), (1033897/20000000)]
    alternative := .zero
    polynomial := [(9780908443475225572512219038192740495541/362606153429395120189439055908100000000000), (-34403507055597/63129650000000), (-392122944399463773531234725246291923476859/181303076714697560094719527954050000000000), (-34403507055597/63129650000000), (-794026797242402772634981669530776587449259/362606153429395120189439055908100000000000)]
    bernstein := [(218174540449606427646473929888307437973568941/3626061534293951201894390559081000000000000000), (66293878857980455696741092645230963480975071/1115711241321215754429043248948000000000000000), (10172682007153733767593328511549366752227349307/174050953646109657690930746835888000000000000000), (1022062939755980682353989073361000396552005339/17851379861139452070864691983168000000000000000), (51835819697786970045127610179760757978405870821/928271752779251507684963983124736000000000000000)]
    reserve := (55841211953/1000000000000) }

theorem quarter_020_011_valid : quarter_020_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_011]
  · intro i; fin_cases i <;> norm_num [quarter_020_011]
  · norm_num [quarter_020_011]
  · norm_num [quarter_020_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_011]

def quarter_020_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![(629007/6250000), (2417741/25000000), (7653563/100000000), (4083821/20000000), (4083821/20000000), (4083821/20000000), (5677023/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8343293/50000000), 0, 0]] i.1) i.2
    mu := ![(3638979/100000000), (77177/20000000), (19477/625000), (5510029/100000000), (1/100000000), (1/100000000), (5332541/100000000)]
    alternative := .zero
    polynomial := [(4818603474728683152273068653082422384457/142864745488586742058963138488000000000000), (-2564628616787/5054137500000), (-191572295727427003714628203993803933487543/71432372744293371029481569244000000000000), (-2564628616787/5054137500000), (-387963194929582690581529476640690289359543/142864745488586742058963138488000000000000)]
    bernstein := [(20784073440610301837663150113235054244416958617/365733748450782059670945634529280000000000000000), (3422436148846054245482050009197407947834712113/60955624741797009945157605754880000000000000000), (15137884822600446132072950689641961005465095939/274300311338086544753209225896960000000000000000), (2466525125079308731762359667463922815317475371/45716718556347757458868204316160000000000000000), (1198733224389648801939210776233496116235326057/22858359278173878729434102158080000000000000000)]
    reserve := (52441787697/1000000000000) }

theorem quarter_020_012_valid : quarter_020_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_012]
  · intro i; fin_cases i <;> norm_num [quarter_020_012]
  · norm_num [quarter_020_012]
  · norm_num [quarter_020_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_012]

def quarter_020_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![(9529861/100000000), (9312801/100000000), (1902417/25000000), (21038419/100000000), (21038419/100000000), (21038419/100000000), (5216207/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15926691/100000000), 0, 0]] i.1) i.2
    mu := ![(1740183/50000000), (24399/10000000), (1519421/50000000), (2826523/50000000), (1/100000000), (1/100000000), (2747139/50000000)]
    alternative := .zero
    polynomial := [(550344641609370055834946225300198169559/13914760338815475366317985095250000000000), (-82121683622393/174018300000000), (-6552074199330658005385144422256352721329/1739345042351934420789748136906250000000), (-82121683622393/174018300000000), (-52966938236254634098916101603351019940191/13914760338815475366317985095250000000000)]
    bernstein := [(119699438806404371666735248061530316063797009/2226361654210476058610877615240000000000000000), (78901174142448788379521665431486253171582703/1484241102806984039073918410160000000000000000), (199086254435971359946507073961775078780184461/3816619978646530386190075911840000000000000000), (301460312503074994370183020268524820121761303/5936964411227936156295673640640000000000000000), (1745485981493781191012213340921783167663188609/35621786467367616937774041843840000000000000000)]
    reserve := (49000517789/1000000000000) }

theorem quarter_020_013_valid : quarter_020_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_013]
  · intro i; fin_cases i <;> norm_num [quarter_020_013]
  · norm_num [quarter_020_013]
  · norm_num [quarter_020_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_013]

def quarter_020_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![(4513979/50000000), (2240353/25000000), (3777611/50000000), (10822183/50000000), (10822183/50000000), (10822183/50000000), (9522311/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7587417/50000000), 0, 0]] i.1) i.2
    mu := ![(1657793/50000000), (114841/100000000), (740433/25000000), (5792713/100000000), (1/100000000), (1/100000000), (5652523/100000000)]
    alternative := .zero
    polynomial := [(25657543031897771431705532065956474379291/576962247096458644276894746471375000000000), (-72695844052901/165779300000000), (-2061576010199322994954745790668282899581959/288481123548229322138447373235687500000000), (-72695844052901/165779300000000), (-4148809563430543761341197113402522273543209/576962247096458644276894746471375000000000)]
    bernstein := [(75284467826682509458986504139115624152801497991/1477023352566934129348850550966720000000000000000), (745314907540198158217736112662947051512219131/14770233525669341293488505509667200000000000000), (136274845758923857505061479997427126609539841/2769418786063001492529094783062600000000000000), (435821047203720805620337966174477477549531/9231395953543338308430315943542000000000000), (25657543031897771431705532065956474379291/576962247096458644276894746471375000000000)]
    reserve := (8894011059/200000000000) }

theorem quarter_020_014_valid : quarter_020_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_014]
  · intro i; fin_cases i <;> norm_num [quarter_020_014]
  · norm_num [quarter_020_014]
  · norm_num [quarter_020_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_014]

def quarter_020_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![(904187/10000000), (1130587/12500000), (7590597/100000000), (4326353/20000000), (4326353/20000000), (5407941/25000000), (1178443/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(113041/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1884597/12500000), 0, 0]] i.1) i.2
    mu := ![(422759/12500000), (57131/100000000), (298359/10000000), (289633/5000000), (1/100000000), (1/100000000), (353077/6250000)]
    alternative := .zero
    polynomial := [(34326772585341749261583872966475299603/736921625172346522731530151000000000000), (71112643422047069/241526444290000000), (-5309530442797942580382934621593415740397/368460812586173261365765075500000000000), (71112643422047069/241526444290000000), (-10653387658181226910027453116153306780397/736921625172346522731530151000000000000)]
    bernstein := [(34326772585341749261583872966475299603/736921625172346522731530151000000000000), (17841423392745549332393585249468996989/368460812586173261365765075500000000000), (172477290288276208145971311929129888354003/3537223800827263309111344724800000000000000), (28061908964332941361465146789060229659389/589537300137877218185224120800000000000000), (84770265698273574350501564388587434951629203/1886519360441207098192717186560000000000000000)]
    reserve := (11233686157/250000000000) }

theorem quarter_020_015_valid : quarter_020_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_015]
  · intro i; fin_cases i <;> norm_num [quarter_020_015]
  · norm_num [quarter_020_015]
  · norm_num [quarter_020_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_015]

def quarter_020_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (12374313/100000000), (9762173/100000000), (5190901/20000000), (5190901/20000000), (5190901/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(385937/25000000), 0, (12339559/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1355627/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7809/10000000), (1991303/50000000), (7006741/100000000), (1/100000000), (1/100000000), (847267/12500000)]
    alternative := .zero
    polynomial := [(319735940994809581603014021174819/12956397333438995958536000000000000), (76454284518171/52060000000000), (-126351957163608386336838599984709181/6478198666719497979268000000000000), (76454284518171/52060000000000), (-253023650268211582255280213990593181/12956397333438995958536000000000000)]
    bernstein := [(1632466361240364639878033221918271371619/33168377173603829653852160000000000000000), (867530583006740350769519993814474458419/16584188586801914826926080000000000000000), (189685262873288747919114356471254834751/3553754697171838891484160000000000000000), (217300934385735589531331855872274559619/4146047146700478706731520000000000000000), (102423778662666183514255429619128054019/2073023573350239353365760000000000000000)]
    reserve := (49217552993/1000000000000) }

theorem quarter_020_016_valid : quarter_020_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_016]
  · intro i; fin_cases i <;> norm_num [quarter_020_016]
  · norm_num [quarter_020_016]
  · norm_num [quarter_020_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_016]

def quarter_020_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (3523747/25000000), (10295459/100000000), (5040637/20000000), (5040637/20000000), (5040637/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2454283/100000000), 0, (13985299/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1645481/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (44377/50000000), (1102611/25000000), (1719799/25000000), (1/100000000), (1/100000000), (263277/4000000)]
    alternative := .zero
    polynomial := [(-8474731950023857961849300112013/296883819584460748584000000000000), (123684791772667/44377000000000), (-3305369340733394125484474275872013/148441909792230374292000000000000), (123684791772667/44377000000000), (-6602263949516764393007099251632013/296883819584460748584000000000000)]
    bernstein := [(2629341999285267365938992838125957587/47501411133513719773440000000000000000), (5597257769944619564149065021593437961/95002822267027439546880000000000000000), (34297858398752208647260083126333983249/570016933602164637281280000000000000000), (22460894568331919723202326254774059649/380011289068109758187520000000000000000), (42340463742351720040891133209243672547/760022578136219516375040000000000000000)]
    reserve := (55352923977/1000000000000) }

theorem quarter_020_017_valid : quarter_020_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_017]
  · intro i; fin_cases i <;> norm_num [quarter_020_017]
  · norm_num [quarter_020_017]
  · norm_num [quarter_020_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_017]

def quarter_020_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (15986529/100000000), (2159377/20000000), (24405529/100000000), (24405529/100000000), (24405529/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1781783/50000000), 0, (3148719/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6373613/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (100321/100000000), (974889/20000000), (6743303/100000000), (1/100000000), (1/100000000), (3186807/50000000)]
    alternative := .zero
    polynomial := [(-27603307095978718718886093838720199/215561324740306399509564000000000000), (2731371033897/617360000000), (-2731605781152726671884027502190820199/107780662370153199754782000000000000), (2731371033897/617360000000), (-5435608255209474625049168910542920199/215561324740306399509564000000000000)]
    bernstein := [(34365939009418701530956431004302966292681/551836991335184382744483840000000000000000), (704311814143098364700059864738881519079/10612249833368930437393920000000000000000), (7018862800938676930615133599378871431927/103469435875347071764590720000000000000000), (44216744016001424148840611896310731931/663265614585558152337120000000000000000), (135449988981662604061282237903406550001/2155613247403063995095640000000000000000)]
    reserve := (12455105239/200000000000) }

theorem quarter_020_018_valid : quarter_020_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_018]
  · intro i; fin_cases i <;> norm_num [quarter_020_018]
  · norm_num [quarter_020_018]
  · norm_num [quarter_020_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_018]

def quarter_020_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (18056407/100000000), (11257853/100000000), (23561913/100000000), (23561913/100000000), (23561913/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4892169/100000000), 0, (8802533/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6153299/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (22557/20000000), (5376643/100000000), (3299151/50000000), (1/100000000), (1/100000000), (6153299/100000000)]
    alternative := .zero
    polynomial := [(-236536056382198918652676164022799841/820694452815445589461833000000000000), (724407827288899/112785000000000), (-11802162243764740930815320911891677841/410347226407722794730916500000000000), (724407827288899/112785000000000), (-7789262810382427647659321886586851947/273564817605148529820611000000000000)]
    bernstein := [(574797706653707568554251741281215327959/8206944528154455894618330000000000000000), (490590534191619303941106668557846453679/6565555622523564715694664000000000000000), (1204372931386170237472682732546168189633/15757333494056555317667193600000000000000), (63155885576243996301863908085015882287/840391119683016283608916992000000000000), (3175356026175918874715264145783826077/44820859716427535125808906240000000000)]
    reserve := (17509491647/250000000000) }

theorem quarter_020_019_valid : quarter_020_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_019]
  · intro i; fin_cases i <;> norm_num [quarter_020_019]
  · norm_num [quarter_020_019]
  · norm_num [quarter_020_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_019]

def quarter_020_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (2538807/12500000), (291737/2500000), (4534671/20000000), (4534671/20000000), (4534671/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1614893/25000000), 0, (19556717/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (185039/3125000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (31531/25000000), (2959409/50000000), (6443379/100000000), (1/100000000), (1/100000000), (5921249/100000000)]
    alternative := .zero
    polynomial := [(-29943408693317641842529350884848445347/56962588868118273292502544000000000000), (278341402195461/31531000000000), (-926912778817515180680977995173079005347/28481294434059136646251272000000000000), (278341402195461/31531000000000), (-1823882148941712719519426639461309565347/56962588868118273292502544000000000000)]
    bernstein := [(734394426611020924646836683633399795557/9332750560152497896243616808960000000000), (9803355831086920851560000996427086431307/116659382001906223703045210112000000000000), (376314303672378140931047790693837714513119/4374726825071483388864195379200000000000000), (308491697633488995670999003643696367507551/3645605687559569490720162816000000000000000), (727240827773191982413996551121748433748493/9114014218898923726800407040000000000000000)]
    reserve := (78690030541/1000000000000) }

theorem quarter_020_020_valid : quarter_020_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_020]
  · intro i; fin_cases i <;> norm_num [quarter_020_020]
  · norm_num [quarter_020_020]
  · norm_num [quarter_020_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_020]

def quarter_020_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (22752159/100000000), (46964/390625), (10870843/50000000), (10870843/50000000), (10870843/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(8283289/100000000), 0, (10790737/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5677939/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (28059/20000000), (6502317/100000000), (784713/12500000), (1/100000000), (1/100000000), (5677939/100000000)]
    alternative := .zero
    polynomial := [(-25872886027269561354714553299571369/30107738347417273621423000000000000), (546371506586109/46765000000000), (-552750396732980253950976502206873369/15053869173708636810711500000000000), (546371506586109/46765000000000), (-1079627907438690946547238451114175369/30107738347417273621423000000000000)]
    bernstein := [(425251759510302174720546765873372150311/4817238135586763779427680000000000000000), (19341672076058333033299715796076387997/204988856833479309762880000000000000000), (1862363378658669974956633376307139228671/19268952542347055117710720000000000000000), (3666011208492819840987525607682589037099/38537905084694110235421440000000000000000), (6916135602453938724548480894963189775831/77075810169388220470842880000000000000000)]
    reserve := (3531083559/40000000000) }

theorem quarter_020_021_valid : quarter_020_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_021]
  · intro i; fin_cases i <;> norm_num [quarter_020_021]
  · norm_num [quarter_020_021]
  · norm_num [quarter_020_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_021]

def quarter_020_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (5076353/20000000), (6154481/50000000), (10384879/50000000), (10384879/50000000), (10384879/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1037779/10000000), 0, (23657721/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1084823/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4851/3125000), (1781959/25000000), (12201/200000), (1/100000000), (1/100000000), (1356029/25000000)]
    alternative := .zero
    polynomial := [(-163182482039200230051082784811593/124533450514070446464000000000000), (933531565025887/62092800000000), (-2571809188764138799625060241711593/62266725257035223232000000000000), (933531565025887/62092800000000), (-4980435895489077369199037698611593/124533450514070446464000000000000)]
    bernstein := [(10503401434515901156296607536743634269/106268544438673447649280000000000000000), (66878191236383855571231076278517827/632550859754008616960000000000000000), (404876490689581775612892725765472451/3736003515422113393920000000000000000), (3691690608521937588639922127858693/34592625142797346240000000000000000), (1959531747594818019968496207215783/19458351642823507260000000000000000)]
    reserve := (98838292083/1000000000000) }

theorem quarter_020_022_valid : quarter_020_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_022]
  · intro i; fin_cases i <;> norm_num [quarter_020_022]
  · norm_num [quarter_020_022]
  · norm_num [quarter_020_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_022]

def quarter_020_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (7048811/25000000), (12519761/100000000), (3952333/20000000), (3952333/20000000), (3952333/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2550639/20000000), 0, (12879439/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5160847/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (170837/100000000), (487197/6250000), (2955567/50000000), (1/100000000), (1/100000000), (322553/6250000)]
    alternative := .zero
    polynomial := [(-201196215727471493273380357114499663/105795494473468910254452000000000000), (808163880714421/42709250000000), (-2450033537434172402859374800093859663/52897747236734455127226000000000000), (808163880714421/42709250000000), (-4698870859140873312445369243073219663/105795494473468910254452000000000000)]
    bernstein := [(1825046639946318648505359930180956953/16530546011479517227258125000000000000), (2841756899663625012222682074624143239/24044430562152025057830000000000000000), (54961655162158865465686190854744487497/453409262029152472519080000000000000000), (8965251991263795661959635843809222523/75065539315986809936640000000000000000), (744777572884058246455196525936292246377/6605767459806839274424320000000000000000)]
    reserve := (22080899671/200000000000) }

theorem quarter_020_023_valid : quarter_020_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_023]
  · intro i; fin_cases i <;> norm_num [quarter_020_023]
  · norm_num [quarter_020_023]
  · norm_num [quarter_020_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_023]

def quarter_020_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (15591553/50000000), (6323983/50000000), (585093/3125000), (585093/3125000), (585093/3125000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15413753/100000000), 0, (3481637/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4889589/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (186979/100000000), (2125703/25000000), (5709231/100000000), (1/100000000), (1/100000000), (4889589/100000000)]
    alternative := .zero
    polynomial := [(-4915354187788985281869230074454124137/1849243660872480171200830500000000000), (1093053478517523/46744750000000), (-3681957846398961565988186294334929549/71124756187403083507724250000000000), (1093053478517523/46744750000000), (-90815549818584015433823613578254044137/1849243660872480171200830500000000000)]
    bernstein := [(582271363504047466266347752471404837626743/4734063771833549238274126080000000000000000), (62374875524275078694049935073413761489807/473406377183354923827412608000000000000000), (1477212349508947183256562695060402368249/10924762550385113626786444800000000000000), (631016229137731101089709237058821788399/4734063771833549238274126080000000000000), (59594564974479882537198976792980836407/473406377183354923827412608000000000000)]
    reserve := (24599219257/200000000000) }

theorem quarter_020_024_valid : quarter_020_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_024]
  · intro i; fin_cases i <;> norm_num [quarter_020_024]
  · norm_num [quarter_020_024]
  · norm_num [quarter_020_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_024]

def quarter_020_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (2145573/6250000), (12687997/100000000), (3532189/20000000), (3532189/20000000), (3532189/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1147259/6250000), 0, (747579/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (922447/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (203489/100000000), (4623901/50000000), (5494813/100000000), (1/100000000), (1/100000000), (922447/20000000)]
    alternative := .zero
    polynomial := [(-25785144665641513816090628983590574537/7153771489222046126842618500000000000), (18088238157489/635903125000), (-206229995213786382146240587330168174537/3576885744611023063421309250000000000), (18088238157489/635903125000), (-386674845761931250476390545676745774537/7153771489222046126842618500000000000)]
    bernstein := [(250202245775264553952902255026224118807/1831365501240843808471710336000000000000), (81271322774348552455884526284703184877/554959242800255699536881920000000000000), (82617773309287561302484740320508689818157/549409650372253142541513100800000000000000), (6964376853621062256305862481288089714147/46958089775406251499274624000000000000000), (2566278703406946312737455935480584460357383/18313655012408438084717103360000000000000000)]
    reserve := (8538787233/62500000000) }

theorem quarter_020_025_valid : quarter_020_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_025]
  · intro i; fin_cases i <;> norm_num [quarter_020_025]
  · norm_num [quarter_020_025]
  · norm_num [quarter_020_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_025]

def quarter_020_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (18804687/50000000), (12636607/100000000), (16584673/100000000), (16584673/100000000), (16584673/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(539193/2500000), 0, (31866739/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4331161/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (220157/100000000), (10025217/100000000), (1053691/20000000), (1/100000000), (1/100000000), (2165581/50000000)]
    alternative := .zero
    polynomial := [(-96006474147084764519340222304861277519/20145310930854737130729996000000000000), (7512240425467107/220157000000000), (-644340515908516756927289768215599317519/10072655465427368565364998000000000000), (7512240425467107/220157000000000), (-1192674557669948749335239314126337357519/20145310930854737130729996000000000000)]
    bernstein := [(7801316911545547748068607493498256831607521/51571995982988127054668789760000000000000000), (2091795085395218510759169456677210009973833/12892998995747031763667197440000000000000000), (1611808194748241071323752035674545338068727/9669749246810273822750398080000000000000000), (132538462581742034496067422917615069625757/805812437234189485229199840000000000000000), (31321078004697363374851420700574156236761/201453109308547371307299960000000000000000)]
    reserve := (151270408733/1000000000000) }

theorem quarter_020_026_valid : quarter_020_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_026]
  · intro i; fin_cases i <;> norm_num [quarter_020_026]
  · norm_num [quarter_020_026]
  · norm_num [quarter_020_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_026]

def quarter_020_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (20495427/50000000), (1561703/12500000), (7752587/50000000), (7752587/50000000), (7752587/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(25024843/100000000), 0, (8424277/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2024623/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (236729/100000000), (10827981/100000000), (5031449/100000000), (1/100000000), (1/100000000), (2024623/50000000)]
    alternative := .zero
    polynomial := [(-80489331281251106827131520541818785077/13055881332353702135909161500000000000), (1195907530091763/29591125000000), (-461383506349101397216088653554802245077/6527940666176851067954580750000000000), (1195907530091763/29591125000000), (-842277681416951687605045786567785705077/13055881332353702135909161500000000000)]
    bernstein := [(21792983634787188684305715106064093460163/130558813323537021359091615000000000000000), (93542862077863728728279316435187781150473/522235253294148085436366460000000000000000), (1153829679201608531179587688939081565558749/6266823039529777025236397520000000000000000), (1518804570641983918373388836361181488157493/8355764052706369366981863360000000000000000), (5745449999566446995797052230197389975654203/33423056210825477467927453440000000000000000)]
    reserve := (166920815837/1000000000000) }

theorem quarter_020_027_valid : quarter_020_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_027]
  · intro i; fin_cases i <;> norm_num [quarter_020_027]
  · norm_num [quarter_020_027]
  · norm_num [quarter_020_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_027]

def quarter_020_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, (44431431/100000000), (12262653/100000000), (7217653/50000000), (7217653/50000000), (7217653/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(5738317/20000000), 0, (17672229/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (753969/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (126457/50000000), (1164667/10000000), (239297/5000000), (1/100000000), (1/100000000), (753969/20000000)]
    alternative := .zero
    polynomial := [(-138565315647193650608806565762228021/17715121271399935234978000000000000), (11962879368651651/252914000000000), (-688552906435138945995660623751458021/8857560635699967617489000000000000), (11962879368651651/252914000000000), (-1238540497223084241382514681740688021/17715121271399935234978000000000000)]
    bernstein := [(8323130396103100359081521313661214675419/45350710454783834201543680000000000000000), (4467655404044495405240351640735632573241/22675355227391917100771840000000000000000), (6891608309763113604548031044147626563097/34013032841087875651157760000000000000000), (1134488683728111141363180081503949601761/5668838806847979275192960000000000000000), (536727856059392967864838972030467498379/2834419403423989637596480000000000000000)]
    reserve := (11470507177/62500000000) }

theorem quarter_020_028_valid : quarter_020_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_028]
  · intro i; fin_cases i <;> norm_num [quarter_020_028]
  · norm_num [quarter_020_028]
  · norm_num [quarter_020_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_028]

def quarter_020_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 0]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(13583621/20000000), 0, (19192791/25000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (560543/100000000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-225687117940091736631685173/10979123676198000000000000), (320397734/2802715), (-977529620943143736631685173/5489561838099000000000000), (320397734/2802715), (-1729372123946195736631685173/10979123676198000000000000)]
    bernstein := [(314235498496942627315637438027/1756659788191680000000000000000), (146182140136763496479577675463/702663915276672000000000000000), (184737751281415488041979179273/843196698332006400000000000000), (23792104293952627085543809151/112426226444267520000000000000), (8326718578362657089749713083/44970490577707008000000000000)]
    reserve := (44720597097/250000000000) }

theorem quarter_020_029_valid : quarter_020_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_020_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_020_029]
  · intro i; fin_cases i <;> norm_num [quarter_020_029]
  · norm_num [quarter_020_029]
  · norm_num [quarter_020_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_020_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_020_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_020_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_020_029]

def quarterTable020 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 2, 0, 0, 0]
  rows := [quarter_020_000, quarter_020_001, quarter_020_002, quarter_020_003, quarter_020_004, quarter_020_005, quarter_020_006, quarter_020_007, quarter_020_008, quarter_020_009, quarter_020_010, quarter_020_011, quarter_020_012, quarter_020_013, quarter_020_014, quarter_020_015, quarter_020_016, quarter_020_017, quarter_020_018, quarter_020_019, quarter_020_020, quarter_020_021, quarter_020_022, quarter_020_023, quarter_020_024, quarter_020_025, quarter_020_026, quarter_020_027, quarter_020_028, quarter_020_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_020_000_valid
    · exact quarter_020_001_valid
    · exact quarter_020_002_valid
    · exact quarter_020_003_valid
    · exact quarter_020_004_valid
    · exact quarter_020_005_valid
    · exact quarter_020_006_valid
    · exact quarter_020_007_valid
    · exact quarter_020_008_valid
    · exact quarter_020_009_valid
    · exact quarter_020_010_valid
    · exact quarter_020_011_valid
    · exact quarter_020_012_valid
    · exact quarter_020_013_valid
    · exact quarter_020_014_valid
    · exact quarter_020_015_valid
    · exact quarter_020_016_valid
    · exact quarter_020_017_valid
    · exact quarter_020_018_valid
    · exact quarter_020_019_valid
    · exact quarter_020_020_valid
    · exact quarter_020_021_valid
    · exact quarter_020_022_valid
    · exact quarter_020_023_valid
    · exact quarter_020_024_valid
    · exact quarter_020_025_valid
    · exact quarter_020_026_valid
    · exact quarter_020_027_valid
    · exact quarter_020_028_valid
    · exact quarter_020_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
