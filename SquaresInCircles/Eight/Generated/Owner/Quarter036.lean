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

def quarter_036_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-653426202301735789/535495700000000000), (-43020979/5354957), (-2264446377301735789/267747850000000000), (-43020979/5354957), (-3875466552301735789/535495700000000000)]
    bernstein := [(1938286778784049980419/2193390387200000000000), (4723931688737165019943/5483475968000000000000), (34492426568691673677089/41126069760000000000000), (27943455951890234163759/34271724800000000000000), (67810388443417763201811/85679312000000000000000)]
    reserve := (49465258051/62500000000) }

theorem quarter_036_000_valid : quarter_036_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_000]
  · intro i; fin_cases i <;> norm_num [quarter_036_000]
  · norm_num [quarter_036_000]
  · norm_num [quarter_036_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_000]

def quarter_036_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-476730880704451349/469515760000000000), (-84778313/11737894), (-1794029770704451349/234757880000000000), (-84778313/11737894), (-3111328660704451349/469515760000000000)]
    bernstein := [(59093382168521903590251/75122521600000000000000), (115002485983437897770409/150245043200000000000000), (670446406386786595273993/901470259200000000000000), (433614861958518577184529/600980172800000000000000), (839929970018857422042011/1201960345600000000000000)]
    reserve := (139760013397/200000000000) }

theorem quarter_036_001_valid : quarter_036_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_001]
  · intro i; fin_cases i <;> norm_num [quarter_036_001]
  · norm_num [quarter_036_001]
  · norm_num [quarter_036_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_001]

def quarter_036_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2706868470840210799/3189246750000000000), (-27774452/4252329), (-11103824970840210799/1594623375000000000), (-27774452/4252329), (-19500781470840210799/3189246750000000000)]
    bernstein := [(5670378530150007093830561/8164471680000000000000000), (1376318882176229855393791/2041117920000000000000000), (1000569538752527182737863/1530838440000000000000000), (80682965091325073057051/127569870000000000000000), (19481710574947455497081/31892467500000000000000)]
    reserve := (9544627669/15625000000) }

theorem quarter_036_002_valid : quarter_036_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_002]
  · intro i; fin_cases i <;> norm_num [quarter_036_002]
  · norm_num [quarter_036_002]
  · norm_num [quarter_036_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_002]

def quarter_036_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1225266842759553839/1720405125000000000), (-81673514/13763241), (-610885475584394871/95578062500000000), (-81673514/13763241), (-9770671717759553839/1720405125000000000)]
    bernstein := [(10443611306298740838841/17204051250000000000000), (13482075519592445820239/22938735000000000000000), (156353967720053691818429/275264820000000000000000), (201074550154826598684691/367019760000000000000000), (2322257240269325297942401/4404237120000000000000000)]
    reserve := (527277977319/1000000000000) }

theorem quarter_036_003_valid : quarter_036_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_003]
  · intro i; fin_cases i <;> norm_num [quarter_036_003]
  · norm_num [quarter_036_003]
  · norm_num [quarter_036_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_003]

def quarter_036_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1769629581402685609/2950514000000000000), (-11403767/2107510), (-8711462031402685609/1475257000000000000), (-11403767/2107510), (-15653294481402685609/2950514000000000000)]
    bernstein := [(3957034220859788253153831/7553315840000000000000000), (381779216287322249441781/755331584000000000000000), (110265669102209767351949/226599475200000000000000), (3530237175962392934637/7553315840000000000000), (338193366074623858999/755331584000000000000)]
    reserve := (22387079611/50000000000) }

theorem quarter_036_004_valid : quarter_036_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_004]
  · intro i; fin_cases i <;> norm_num [quarter_036_004]
  · norm_num [quarter_036_004]
  · norm_num [quarter_036_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_004]

def quarter_036_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1992806601681522413/3930199000000000000), (-38890387/7860398), (-1540614853811646059/280728500000000000), (-38890387/7860398), (-19575801351681522413/3930199000000000000)]
    bernstein := [(34418549181849232511/77394688000000000000), (4297077382118986107451/10061309440000000000000), (123477696011245210728313/301839283200000000000000), (56156430778378282744749/143732992000000000000000), (3742139974731069544718707/10061309440000000000000000)]
    reserve := (37193369283/100000000000) }

theorem quarter_036_005_valid : quarter_036_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_005]
  · intro i; fin_cases i <;> norm_num [quarter_036_005]
  · norm_num [quarter_036_005]
  · norm_num [quarter_036_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_005]

def quarter_036_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-89710426553007943/208296125000000000), (-37768474/8331845), (-534059514053007943/104148062500000000), (-37768474/8331845), (-978408601553007943/208296125000000000)]
    bernstein := [(196892986292970721980377/533238080000000000000000), (809891718837785254957/2298440000000000000000), (2094171639178213731719/6248883750000000000000), (165347317549227418869/520740312500000000000), (9749284900041657633/32546269531250000000)]
    reserve := (292530793/976562500) }

theorem quarter_036_006_valid : quarter_036_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_006]
  · intro i; fin_cases i <;> norm_num [quarter_036_006]
  · norm_num [quarter_036_006]
  · norm_num [quarter_036_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_006]

def quarter_036_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-808764259374583569/2197127875000000000), (-73096558/17577023), (-5290159571874583569/1098563937500000000), (-73096558/17577023), (-9771554884374583569/2197127875000000000)]
    bernstein := [(102015467978195376839/343301230468750000000), (1543361539116745615821/5492819687500000000000), (5810148976427378447211/21971278750000000000000), (174049499353239020806833/703080920000000000000000), (1295372816823747984591631/5624647360000000000000000)]
    reserve := (115151469409/500000000000) }

theorem quarter_036_007_valid : quarter_036_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_007]
  · intro i; fin_cases i <;> norm_num [quarter_036_007]
  · norm_num [quarter_036_007]
  · norm_num [quarter_036_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_007]

def quarter_036_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-46846541701193777/147652952000000000), (-3708567/971401), (-335425039701193777/73826476000000000), (-3708567/971401), (-624003537701193777/147652952000000000)]
    bernstein := [(86252546922256180387823/377991557120000000000000), (40187731712930530077867/188995778560000000000000), (55775871530528458560629/283493667840000000000000), (8528546721213842814947/47248944640000000000000), (3872200350766603789663/23624472320000000000000)]
    reserve := (32781264261/200000000000) }

theorem quarter_036_008_valid : quarter_036_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_008]
  · intro i; fin_cases i <;> norm_num [quarter_036_008]
  · norm_num [quarter_036_008]
  · norm_num [quarter_036_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_008]

def quarter_036_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1067647938911762121/3859681000000000000), (-13528061/3859681), (-8309344188911762121/1929840500000000000), (-13528061/3859681), (-15551040438911762121/3859681000000000000)]
    bernstein := [(100068034278401520636999/617548960000000000000000), (36328949888069554679293/247019584000000000000000), (265685575963521009711/2016486400000000000000), (917720443345976065601/7904626688000000000000), (63294346623912201551/632370135040000000000)]
    reserve := (100090663863/1000000000000) }

theorem quarter_036_009_valid : quarter_036_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_009]
  · intro i; fin_cases i <;> norm_num [quarter_036_009]
  · norm_num [quarter_036_009]
  · norm_num [quarter_036_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_009]

def quarter_036_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![(33363/390625), (18695757/100000000), (4164627/20000000), (4164627/20000000), (10595101/100000000), (10595101/100000000), (4963421/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (63469/500000), 0, 0]] i.1) i.2
    mu := ![(370921/12500000), (2596829/50000000), (674269/50000000), (1/100000000), (2951761/50000000), (1/100000000), (2766959/100000000)]
    alternative := .zero
    polynomial := [(12077954746618512074074165739026553960517/331529286690476220859201403554937500000000), (-12233676556533/18546050000000), (-1997488143216708675830837564815841041793557/663058573380952441718402807109875000000000), (-12233676556533/18546050000000), (-2021644052709945699978985896293894149714591/663058573380952441718402807109875000000000)]
    bernstein := [(604672482290514760850846441834355402914317/8356578204825788311626393532067840000000000), (3807405096383688453461922553958274141970879/52228613780161176947664959575424000000000000), (930883249100331321967201108045965135870990733/12730724608914286880993333896509600000000000000), (387378547321645377853820728057580151105103529/5304468587047619533747222456879000000000000000), (481540953953152360490825839875024953370444709/6630585733809524417184028071098750000000000000)]
    reserve := (72358861183/1000000000000) }

theorem quarter_036_010_valid : quarter_036_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_010]
  · intro i; fin_cases i <;> norm_num [quarter_036_010]
  · norm_num [quarter_036_010]
  · norm_num [quarter_036_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_010]

def quarter_036_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![(7907819/100000000), (9693639/50000000), (10587357/50000000), (10587357/50000000), (5349009/50000000), (5349009/50000000), (8959439/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5876637/50000000), 0, 0]] i.1) i.2
    mu := ![(557431/20000000), (661327/12500000), (34827/3125000), (1/100000000), (1498629/25000000), (1/100000000), (698459/25000000)]
    alternative := .zero
    polynomial := [(7415510952302394254924867400202957763/157178222300600520706004318000000000000), (-178920319581721/278715500000000), (-296154881184941726567958751996686800987/78589111150300260353002159000000000000), (-178920319581721/278715500000000), (-599725273322185847390842371393576559737/157178222300600520706004318000000000000)]
    bernstein := [(116233349363170540713058400390191955632863/1571782223006005207060043180000000000000000), (469166875797228510662228217960132031119889/6287128892024020828240172720000000000000000), (5650903084891804756556687674146029624862001/75445546704288249938882072640000000000000000), (7522884135961659441741427691150472383066301/100594062272384333251842763520000000000000000), (1573033184247069314694153681119361888505037/21177697320501964895124792320000000000000000)]
    reserve := (36975017169/500000000000) }

theorem quarter_036_011_valid : quarter_036_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_011]
  · intro i; fin_cases i <;> norm_num [quarter_036_011]
  · norm_num [quarter_036_011]
  · norm_num [quarter_036_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_011]

def quarter_036_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![(1452619/20000000), (1007321/5000000), (21523243/100000000), (21523243/100000000), (5393543/50000000), (5393543/50000000), (7969827/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (10786923/100000000), 0, 0]] i.1) i.2
    mu := ![(103431/4000000), (5411311/100000000), (430251/50000000), (1/100000000), (60833/1000000), (1/100000000), (352137/12500000)]
    alternative := .zero
    polynomial := [(51301471185587675740270070654134483/892788244788409296882449500000000000), (-10804921932371/17238500000000), (-6807841856055045495372726211270716551/1339182367182613945323674250000000000), (-10804921932371/17238500000000), (-13769588125666854017966262634503836551/2678364734365227890647348500000000000)]
    bernstein := [(173650511552542760042522591367153893163523/2285537906658327800019070720000000000000000), (87781220645034876333528466934568906692041/1142768953329163900009535360000000000000000), (396576798117856484336384391476808777488323/5142460289981237550042909120000000000000000), (65902659569571706145814899180153995773347/857076714996872925007151520000000000000000), (32628419532407862937381194251000951382649/428538357498436462503575760000000000000000)]
    reserve := (75977961707/1000000000000) }

theorem quarter_036_012_valid : quarter_036_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_012]
  · intro i; fin_cases i <;> norm_num [quarter_036_012]
  · norm_num [quarter_036_012]
  · norm_num [quarter_036_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_012]

def quarter_036_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![(6601483/100000000), (10489047/50000000), (10933731/50000000), (10933731/50000000), (10860461/100000000), (10860461/100000000), (217643/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4900417/50000000), 0, 0]] i.1) i.2
    mu := ![(147717/6250000), (5557007/100000000), (292687/50000000), (1/100000000), (3084703/50000000), (1/100000000), (1418129/50000000)]
    alternative := .zero
    polynomial := [(283000017092214245626959365141149756502509/4204011945445485460978685161644000000000000), (-4535587675967/7385850000000), (-16482496721185931266872669959718149829777491/2102005972722742730489342580822000000000000), (-4535587675967/7385850000000), (-33247993459464076779372299284577449416057491/4204011945445485460978685161644000000000000)]
    bernstein := [(52765574203360182093633445617922132486460989709/672641911271277673756589625863040000000000000000), (35651791466350509340662081713457134012098611103/448427940847518449171059750575360000000000000000), (643662309118990820736875576926786391702245354327/8071702935255332085079075510356480000000000000000), (142001686276593217882269429385084968248660094703/1793711763390073796684239002301440000000000000000), (93003504800970798045345225792621585808728245701/1195807842260049197789492668200960000000000000000)]
    reserve := (3110984943/40000000000) }

theorem quarter_036_013_valid : quarter_036_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_013]
  · intro i; fin_cases i <;> norm_num [quarter_036_013]
  · norm_num [quarter_036_013]
  · norm_num [quarter_036_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_013]

def quarter_036_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (2490497/10000000), (12631003/50000000), (12631003/50000000), (12285509/100000000), (12285509/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3688527/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (100263/3125000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3236973/50000000), (329393/100000000), (1/100000000), (7098027/100000000), (1/100000000), (100263/3125000)]
    alternative := .zero
    polynomial := [(580001460087322363593610597592611/7099955994483341250014400000000000), (-2490497/5000000), (-67225534405836510641900943231687389/3549977997241670625007200000000000), (-2490497/5000000), (-135031070271760343647395497060967389/7099955994483341250014400000000000)]
    bernstein := [(1496023420543659356169532861310917947811/18175887345877353600036864000000000000000), (966893419384116429679115113248736211/11359929591173346000023040000000000000), (2928970503266024169805075283094445411/34079788773520038000069120000000000000), (602104483967813336010031989038611/7099955994483341250014400000000000), (580001460087322363593610597592611/7099955994483341250014400000000000)]
    reserve := (81690852807/1000000000000) }

theorem quarter_036_014_valid : quarter_036_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_014]
  · intro i; fin_cases i <;> norm_num [quarter_036_014]
  · norm_num [quarter_036_014]
  · norm_num [quarter_036_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_014]

def quarter_036_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (5074861/20000000), (3170797/12500000), (3170797/12500000), (11946471/100000000), (11946471/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3758037/50000000), 0, 0], ![(634259/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1559937/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6595947/100000000), (80139/50000000), (1/100000000), (708483/10000000), (1/100000000), (24959/800000)]
    alternative := .zero
    polynomial := [(178860867827494066751767836068651/2077137169420931028378000000000000), (3218776262999/3205560000000), (-41528609366120494694388801437331349/1038568584710465514189000000000000), (3218776262999/3205560000000), (-83236079600068483455529370710731349/2077137169420931028378000000000000)]
    bernstein := [(178860867827494066751767836068651/2077137169420931028378000000000000), (383792998616549549887622480917927/4154274338841862056756000000000000), (942145618421345824357713493839193451/9970258413220468936214400000000000000), (614465691794196384276880241500801127/6646838942146979290809600000000000000), (458477329991870607797979505110473511851/5317471153717583432647680000000000000000)]
    reserve := (10763664917/125000000000) }

theorem quarter_036_015_valid : quarter_036_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_015]
  · intro i; fin_cases i <;> norm_num [quarter_036_015]
  · norm_num [quarter_036_015]
  · norm_num [quarter_036_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_015]

def quarter_036_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (25647901/100000000), (6393967/25000000), (6393967/25000000), (5800091/50000000), (5800091/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1899279/25000000), 0, 0], ![(1920891/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3029439/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1666767/25000000), (80927/50000000), (1/100000000), (7096167/100000000), (1/100000000), (9467/312500)]
    alternative := .zero
    polynomial := [(178902874849751607836628769291927/3717576505974544711344000000000000), (7038117457113/2312200000000), (-75154692105168230483270770948948073/1858788252987272355672000000000000), (7038117457113/2312200000000), (-150488287085186212574378170667188073/3717576505974544711344000000000000)]
    bernstein := [(942019308851389465500816889488022498327/9516995855294834461040640000000000000000), (55723110848077815874407094661095066303/528721991960824136724480000000000000000), (768004507455517765324237100306226696181/7137746891471125845780480000000000000000), (13957667001283332803188972267082862703/132180497990206034181120000000000000000), (59104138790536613498027922400637873527/594812240955927153815040000000000000000)]
    reserve := (98982843239/1000000000000) }

theorem quarter_036_016_valid : quarter_036_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_016]
  · intro i; fin_cases i <;> norm_num [quarter_036_016]
  · norm_num [quarter_036_016]
  · norm_num [quarter_036_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_016]

def quarter_036_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (649029/2500000), (3219891/12500000), (3219891/12500000), (2815073/25000000), (2815073/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3844953/50000000), 0, 0], ![(1616259/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (735169/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3374249/50000000), (81737/50000000), (1/100000000), (710353/10000000), (1/100000000), (735169/25000000)]
    alternative := .zero
    polynomial := [(-12359044121777524290999325450264727/288062829319027892638082000000000000), (1048998962511/204342500000), (-5904373284900318057681999894293464727/144031414659513946319041000000000000), (1048998962511/204342500000), (-11796387525678858591073000463136664727/288062829319027892638082000000000000)]
    bernstein := [(5147073797592613867379520881263303233673/46090052691044462822093120000000000000000), (10900343662169963596141591874975159911819/92180105382088925644186240000000000000000), (3509813857863707656917423040811580855409/29109506962764923887637760000000000000000), (43740990546166461978796767902445534768371/368720421528355702576744960000000000000000), (82882238014479466318793373914733116899513/737440843056711405153489920000000000000000)]
    reserve := (111674287553/1000000000000) }

theorem quarter_036_017_valid : quarter_036_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_017]
  · intro i; fin_cases i <;> norm_num [quarter_036_017]
  · norm_num [quarter_036_017]
  · norm_num [quarter_036_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_017]

def quarter_036_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (26315417/100000000), (6478881/25000000), (6478881/25000000), (10926767/100000000), (10926767/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (194871/2500000), 0, 0], ![(4570207/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1426787/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3420293/50000000), (82569/50000000), (1/100000000), (3553297/50000000), (1/100000000), (114143/4000000)]
    alternative := .zero
    polynomial := [(-43357332535523216896953959891393489/229082083387306584585414000000000000), (120266902981319/16513800000000), (-4773610212565416681368891982094013489/114541041693653292292707000000000000), (120266902981319/16513800000000), (-9503863092595310145840830004296633489/229082083387306584585414000000000000)]
    bernstein := [(4287219611667127532259722659138542821423/34497066674794403325803520000000000000000), (6404753847585274717802413139601354834399/48870844455958738044888320000000000000000), (14681250081700145968414633271518472256097/109959400025907160600998720000000000000000), (1206246378452444183952503965366609622233/9163283335492263383416560000000000000000), (287246162859689309369247871526431478711/2290820833873065845854140000000000000000)]
    reserve := (62138900853/500000000000) }

theorem quarter_036_018_valid : quarter_036_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_018]
  · intro i; fin_cases i <;> norm_num [quarter_036_018]
  · norm_num [quarter_036_018]
  · norm_num [quarter_036_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_018]

def quarter_036_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (3339007/12500000), (26044357/100000000), (26044357/100000000), (2119923/20000000), (2119923/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (7912327/100000000), 0, 0], ![(741887/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2768137/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (694369/10000000), (3337/2000000), (1/100000000), (7105029/100000000), (1/100000000), (2768137/100000000)]
    alternative := .zero
    polynomial := [(-4950243528964749860285420081748157/12571640533456372242888000000000000), (2477165886209/260703125000), (-267044017347080972000205918769408957/6285820266728186121444000000000000), (2477165886209/260703125000), (-529137791165197194140126417457069757/12571640533456372242888000000000000)]
    bernstein := [(17208194324370500429757934362887216843/125716405334563722428880000000000000000), (4823910042873540428021058846652615861/33524374755883659314368000000000000000), (35364571328600819959719954834447098741/241375498242362347063449600000000000000), (47767624042506748464679960523672081/330086151442546799403008000000000000), (21935773506468223359202044969865319/158441352692422463713443840000000000)]
    reserve := (34220264011/250000000000) }

theorem quarter_036_019_valid : quarter_036_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_019]
  · intro i; fin_cases i <;> norm_num [quarter_036_019]
  · norm_num [quarter_036_019]
  · norm_num [quarter_036_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_019]

def quarter_036_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (27152517/100000000), (26144863/100000000), (26144863/100000000), (5139439/50000000), (5139439/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1608559/20000000), 0, 0], ![(732839/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (859/32000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3529093/50000000), (42153/25000000), (1/100000000), (3549253/50000000), (1/100000000), (859/32000)]
    alternative := .zero
    polynomial := [(-11968884148465608750907315942646171/18141855562390413835320000000000000), (6632807801921/562040000000), (-393877709322117776695978700306696171/9070927781195206917660000000000000), (6632807801921/562040000000), (-775786534495769944641050084670746171/18141855562390413835320000000000000)]
    bernstein := [(444563730642749187053163246534137101/2972361615342045402778828800000000000), (5827559100083240791414905989792983651/37154520191775567534735360000000000000), (222436093456270458588264529331965809367/1393294507191583782552576000000000000000), (183370826384954401604153423593534017943/1161078755992986485460480000000000000000), (440176559557960292402240942522289768949/2902696889982466213651200000000000000000)]
    reserve := (149565829523/1000000000000) }

theorem quarter_036_020_valid : quarter_036_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_020]
  · intro i; fin_cases i <;> norm_num [quarter_036_020]
  · norm_num [quarter_036_020]
  · norm_num [quarter_036_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_020]

def quarter_036_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (27638311/100000000), (5243243/20000000), (5243243/20000000), (9964629/100000000), (9964629/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2046673/25000000), 0, 0], ![(8751361/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (650577/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7184467/100000000), (6817/4000000), (1/100000000), (7086689/100000000), (1/100000000), (650577/25000000)]
    alternative := .zero
    polynomial := [(-149197832755212289691105001426534931/150535409694329028181378000000000000), (14227813940663/1002500000000), (-3349248539319842894971164876516416931/75267704847164514090689000000000000), (14227813940663/1002500000000), (-6549299245884473500251224751606298931/150535409694329028181378000000000000)]
    bernstein := [(3911714617723147752327811313504524347389/24085665551092644509020480000000000000000), (8188817838107347949360460357094262262441/48171331102185289018040960000000000000000), (16666996176781981227796259722082055547029/96342662204370578036081920000000000000000), (1942406722990930358064771619355017531953/11334430847573009180715520000000000000000), (3741623160036345005793423887559143985757/22668861695146018361431040000000000000000)]
    reserve := (40602102207/250000000000) }

theorem quarter_036_021_valid : quarter_036_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_021]
  · intro i; fin_cases i <;> norm_num [quarter_036_021]
  · norm_num [quarter_036_021]
  · norm_num [quarter_036_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_021]

def quarter_036_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (7042757/25000000), (6564381/25000000), (6564381/25000000), (4828481/50000000), (4828481/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (8344487/100000000), 0, 0], ![(10205353/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2521959/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (114421/1562500), (17229/10000000), (1/100000000), (7069237/100000000), (1/100000000), (2521959/100000000)]
    alternative := .zero
    polynomial := [(-4176066171567778551238924072300817237/2999128572668356487487744000000000000), (71873821278221/4307250000000), (-68557624456686465845509369193584913237/1499564286334178243743872000000000000), (71873821278221/4307250000000), (-132939182741805153139779814314869009237/2999128572668356487487744000000000000)]
    bernstein := [(449098003270324706130405189134104467940121/2559256382010330869322874880000000000000000), (58672782727191301356126074211729225444903/319907047751291358665359360000000000000000), (16792123314567444578048809677493304895109/89973857180050694624632320000000000000000), (462632520676601837909225118723630234411/2499273810556963739573120000000000000000), (83765958852063035089801970282517918947/468613839479430701169960000000000000000)]
    reserve := (87739940091/500000000000) }

theorem quarter_036_022_valid : quarter_036_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_022]
  · intro i; fin_cases i <;> norm_num [quarter_036_022]
  · norm_num [quarter_036_022]
  · norm_num [quarter_036_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_022]

def quarter_036_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (14376173/50000000), (26267841/100000000), (26267841/100000000), (4677993/50000000), (4677993/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4258339/50000000), 0, 0], ![(1169179/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1221679/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1494811/20000000), (43553/25000000), (1/100000000), (1761451/25000000), (1/100000000), (1221679/50000000)]
    alternative := .zero
    polynomial := [(-2111437502601256375680995594262421/1129822840859748931174250000000000), (16808319571967/871060000000), (-13301033632489091720687278687992773/282455710214937232793562500000000), (16808319571967/871060000000), (-51092697027355110507068119157708671/1129822840859748931174250000000000)]
    bernstein := [(4167244087126120477453416961761747/22066852360541971311997070312500000), (1113722960395961669093738574808722411/5649114204298744655871250000000000000), (877430192922085339554844563273754637/4373507771069995862610000000000000000), (9002520720337188515726880338362163827/45192913634389957246970000000000000000), (557646812097592912645153404627525626369/2892346472600957263806080000000000000000)]
    reserve := (188846330189/1000000000000) }

theorem quarter_036_023_valid : quarter_036_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_023]
  · intro i; fin_cases i <;> norm_num [quarter_036_023]
  · norm_num [quarter_036_023]
  · norm_num [quarter_036_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_023]

def quarter_036_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (29384049/100000000), (13123079/50000000), (13123079/50000000), (9061817/100000000), (9061817/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (8703793/100000000), 0, 0], ![(6606087/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1183267/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (954783/12500000), (176191/100000000), (1/100000000), (3508017/50000000), (1/100000000), (473307/20000000)]
    alternative := .zero
    polynomial := [(-2409475476006741540488196045645642557/993117155095368866403936000000000000), (194113584106263/8809550000000), (-24144700775510029205831275066817802557/496558577547684433201968000000000000), (194113584106263/8809550000000), (-45879926075013316871174354087989962557/993117155095368866403936000000000000)]
    bernstein := [(515007188540992121631011941927568240569123/2542379917044144297994076160000000000000000), (53717684629651122274081053949269729384427/254237991704414429799407616000000000000000), (16400758753422607986450126234157567147657/76271397511324328939822284800000000000000), (543358433556511060161422944722747973739/2542379917044144297994076160000000000000), (52693630026050039937102557374861141027/254237991704414429799407616000000000000)]
    reserve := (25321116697/125000000000) }

theorem quarter_036_024_valid : quarter_036_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_024]
  · intro i; fin_cases i <;> norm_num [quarter_036_024]
  · norm_num [quarter_036_024]
  · norm_num [quarter_036_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_024]

def quarter_036_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (30068033/100000000), (13095703/50000000), (13095703/50000000), (8774577/100000000), (8774577/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1781279/20000000), 0, 0], ![(14768103/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7161/312500), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7816063/100000000), (178231/100000000), (1/100000000), (1744891/25000000), (1/100000000), (2291521/100000000)]
    alternative := .zero
    polynomial := [(-68424235846996335557360886771754168019/22280422937930644315750732000000000000), (444047808351399/17823100000000), (-560660971569508818655208787559286448019/11140211468965322157875366000000000000), (444047808351399/17823100000000), (-1052897707292021301753056688346818728019/22280422937930644315750732000000000000)]
    bernstein := [(1236032995940810521941481486859974962509/5703788272110244944832187392000000000000), (12883724901643286091877925247286517048767/57037882721102449448321873920000000000000), (393414916605567701802077876324151232500959/1711136481633073483449656217600000000000000), (1304566892122243340743061172262342310440471/5703788272110244944832187392000000000000000), (12673209113233940396102004689521417668677021/57037882721102449448321873920000000000000000)]
    reserve := (216703870651/1000000000000) }

theorem quarter_036_025_valid : quarter_036_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_025]
  · intro i; fin_cases i <;> norm_num [quarter_036_025]
  · norm_num [quarter_036_025]
  · norm_num [quarter_036_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_025]

def quarter_036_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (1232253/4000000), (26102459/100000000), (26102459/100000000), (8494379/100000000), (8494379/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9125083/100000000), 0, 0], ![(654451/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (443669/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8007979/100000000), (180333/100000000), (1/100000000), (3468011/50000000), (1/100000000), (1109173/50000000)]
    alternative := .zero
    polynomial := [(-84675452296940722030186774774525837057/22219684093204284380341284000000000000), (29868489189/1068640000), (-580073159097390875407396868685375337057/11109842046602142190170642000000000000), (29868489189/1068640000), (-1075470865897841028784606962596224837057/22219684093204284380341284000000000000)]
    bernstein := [(13157023327929315511047832402560239786258063/56882391278602968013673687040000000000000000), (3426825758913662941727991527780389211482999/14220597819650742003418421760000000000000000), (2616507611252953664588122731943498316354681/10665448364738056502563816320000000000000000), (217087753491234622954055383620682602920771/888787363728171375213651360000000000000000), (52802088583925546581990227420571060925783/222196840932042843803412840000000000000000)]
    reserve := (46260443811/200000000000) }

theorem quarter_036_026_valid : quarter_036_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_026]
  · intro i; fin_cases i <;> norm_num [quarter_036_026]
  · norm_num [quarter_036_026]
  · norm_num [quarter_036_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_026]

def quarter_036_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (31601097/100000000), (12989063/50000000), (12989063/50000000), (328853/4000000), (328853/4000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9360501/100000000), 0, 0], ![(17993507/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (536759/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8214577/100000000), (91251/50000000), (1/100000000), (6885023/100000000), (1/100000000), (536759/25000000)]
    alternative := .zero
    polynomial := [(-51566053001737589024376888553120711801/11080709243565573515211756000000000000), (63179395564131/2027800000000), (-300784343828634786869279466058030291801/5540354621782786757605878000000000000), (63179395564131/2027800000000), (-550002634655531984714182043562939871801/11080709243565573515211756000000000000)]
    bernstein := [(27303917439014261505922441449866874532319/110807092435655735152117560000000000000000), (113743187619235838942353037678637385900349/443228369742622940608470240000000000000000), (198550806538804108721670660071421810891191/759820062415925041043091840000000000000000), (1846413379195097361009488033840911098739609/7091653915881967049735523840000000000000000), (7195136565931505714239099137977779910550839/28366615663527868198942095360000000000000000)]
    reserve := (24640947469/100000000000) }

theorem quarter_036_027_valid : quarter_036_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_027]
  · intro i; fin_cases i <;> norm_num [quarter_036_027]
  · norm_num [quarter_036_027]
  · norm_num [quarter_036_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_027]

def quarter_036_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (32454687/100000000), (25817159/100000000), (25817159/100000000), (7955497/100000000), (7955497/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9613341/100000000), 0, 0], ![(4916687/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1038807/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (527279/6250000), (9237/5000000), (1/100000000), (106659/1562500), (1/100000000), (1038807/50000000)]
    alternative := .zero
    polynomial := [(-93173425690335524545312937833063/16612281367291358784000000000000), (53189845887323/1539500000000), (-469898231631983458912512163897063/8306140683645679392000000000000), (53189845887323/1539500000000), (-846623037573631393279711389961063/16612281367291358784000000000000)]
    bernstein := [(11144966957699935585774071315931209257/42527440300265878487040000000000000000), (644683219982000528299987220892275747/2362635572236993249280000000000000000), (8864374305585048555808222957055768291/31895580225199408865280000000000000000), (163670885524730980456734444899028587/590658893059248312320000000000000000), (718349927775541421594091584462298137/2657965018766617405440000000000000000)]
    reserve := (262065313101/1000000000000) }

theorem quarter_036_028_valid : quarter_036_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_028]
  · intro i; fin_cases i <;> norm_num [quarter_036_028]
  · norm_num [quarter_036_028]
  · norm_num [quarter_036_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_028]

def quarter_036_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 0]
    lambda := ![0, (19720573/50000000), (30279427/100000000), (30279427/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11682787/100000000), 0, 0], ![(6318427/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8969011/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2050513/20000000), (44217/20000000), (1/100000000), (3935507/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-22680415425699938123471916482143/2854581696460229976000000000000), (124603000898671/2763562500000), (-33259901940493286369482729819381/475763616076704996000000000000), (124603000898671/2763562500000), (-10404646836309398829024968378479/167916570380013528000000000000)]
    bernstein := [(125595674631704441966965824124417057/456733071433636796160000000000000000), (52630386664879708104060371205200533/182693228573454718464000000000000000), (21490539329017527592283827192235081/73077291429381887385600000000000000), (8559427822631408010058551107844541/29230916571752754954240000000000000), (3322013469597050272138188119811953/11692366628701101981696000000000000)]
    reserve := (274987038353/1000000000000) }

theorem quarter_036_029_valid : quarter_036_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_036_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_036_029]
  · intro i; fin_cases i <;> norm_num [quarter_036_029]
  · norm_num [quarter_036_029]
  · norm_num [quarter_036_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_036_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_036_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_036_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_036_029]

def quarterTable036 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 0, 0, 0, 0]
  rows := [quarter_036_000, quarter_036_001, quarter_036_002, quarter_036_003, quarter_036_004, quarter_036_005, quarter_036_006, quarter_036_007, quarter_036_008, quarter_036_009, quarter_036_010, quarter_036_011, quarter_036_012, quarter_036_013, quarter_036_014, quarter_036_015, quarter_036_016, quarter_036_017, quarter_036_018, quarter_036_019, quarter_036_020, quarter_036_021, quarter_036_022, quarter_036_023, quarter_036_024, quarter_036_025, quarter_036_026, quarter_036_027, quarter_036_028, quarter_036_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_036_000_valid
    · exact quarter_036_001_valid
    · exact quarter_036_002_valid
    · exact quarter_036_003_valid
    · exact quarter_036_004_valid
    · exact quarter_036_005_valid
    · exact quarter_036_006_valid
    · exact quarter_036_007_valid
    · exact quarter_036_008_valid
    · exact quarter_036_009_valid
    · exact quarter_036_010_valid
    · exact quarter_036_011_valid
    · exact quarter_036_012_valid
    · exact quarter_036_013_valid
    · exact quarter_036_014_valid
    · exact quarter_036_015_valid
    · exact quarter_036_016_valid
    · exact quarter_036_017_valid
    · exact quarter_036_018_valid
    · exact quarter_036_019_valid
    · exact quarter_036_020_valid
    · exact quarter_036_021_valid
    · exact quarter_036_022_valid
    · exact quarter_036_023_valid
    · exact quarter_036_024_valid
    · exact quarter_036_025_valid
    · exact quarter_036_026_valid
    · exact quarter_036_027_valid
    · exact quarter_036_028_valid
    · exact quarter_036_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
