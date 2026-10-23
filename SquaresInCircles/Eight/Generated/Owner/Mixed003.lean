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

def mixed_003_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-638432322701735789/535495700000000000), (-43020979/5354957), (-2249452497701735789/267747850000000000), (-43020979/5354957), (-3860472672701735789/535495700000000000)]
    bernstein := [(2018189163172449980419/2193390387200000000000), (4922045819891965019943/5483475968000000000000), (35966309939492073677089/41126069760000000000000), (29161993553102634163759/34271724800000000000000), (70833169564657363201811/85679312000000000000000)]
    reserve := (103340537977/125000000000) }

theorem mixed_003_000_valid : mixed_003_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_000]
  · intro i; fin_cases i <;> norm_num [mixed_003_000]
  · norm_num [mixed_003_000]
  · norm_num [mixed_003_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_000]

def mixed_003_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-463584439424451349/469515760000000000), (-84778313/11737894), (-1780883329424451349/234757880000000000), (-84778313/11737894), (-3098182219424451349/469515760000000000)]
    bernstein := [(61743717877011183590251/75122521600000000000000), (120261838135473417770409/150245043200000000000000), (701761794812721635273993/901470259200000000000000), (454336006628787697184529/600980172800000000000000), (881069930649279502042011/1201960345600000000000000)]
    reserve := (366513726461/500000000000) }

theorem mixed_003_001_valid : mixed_003_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_001]
  · intro i; fin_cases i <;> norm_num [mixed_003_001]
  · norm_num [mixed_003_001]
  · norm_num [mixed_003_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_001]

def mixed_003_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2617569561840210799/3189246750000000000), (-27774452/4252329), (-11014526061840210799/1594623375000000000), (-27774452/4252329), (-19411482561840210799/3189246750000000000)]
    bernstein := [(5949827053317156093830561/8164471680000000000000000), (1445667611215448855393791/2041117920000000000000000), (1052207793767594182737863/1530838440000000000000000), (84956007185884073057051/127569870000000000000000), (20542670912776455497081/31892467500000000000000)]
    reserve := (10064421419/15625000000) }

theorem mixed_003_002_valid : mixed_003_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_002]
  · intro i; fin_cases i <;> norm_num [mixed_003_002]
  · norm_num [mixed_003_002]
  · norm_num [mixed_003_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_002]

def mixed_003_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1177095499259553839/1720405125000000000), (-81673514/13763241), (-605533104084394871/95578062500000000), (-81673514/13763241), (-9722500374259553839/1720405125000000000)]
    bernstein := [(11015935038422240838841/17204051250000000000000), (14239923152648945820239/22938735000000000000000), (165387170452975191818429/275264820000000000000000), (213040199480425098684691/367019760000000000000000), (2464933100472708797942401/4404237120000000000000000)]
    reserve := (559673113257/1000000000000) }

theorem mixed_003_003_valid : mixed_003_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_003]
  · intro i; fin_cases i <;> norm_num [mixed_003_003]
  · norm_num [mixed_003_003]
  · norm_num [mixed_003_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_003]

def mixed_003_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1687015189402685609/2950514000000000000), (-11403767/2107510), (-8628847639402685609/1475257000000000000), (-11403767/2107510), (-15570680089402685609/2950514000000000000)]
    bernstein := [(4201724914275460253153831/7553315840000000000000000), (406091888323394249441781/755331584000000000000000), (117514173241897767351949/226599475200000000000000), (3770397213506392934637/7553315840000000000000), (362068925362623858999/755331584000000000000)]
    reserve := (23967548361/50000000000) }

theorem mixed_003_004_valid : mixed_003_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_004]
  · intro i; fin_cases i <;> norm_num [mixed_003_004]
  · norm_num [mixed_003_004]
  · norm_num [mixed_003_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_004]

def mixed_003_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1882761029681522413/3930199000000000000), (-38890387/7860398), (-1524894057811646059/280728500000000000), (-38890387/7860398), (-19465755779681522413/3930199000000000000)]
    bernstein := [(36864946897849232511/77394688000000000000), (4613238310474986107451/10061309440000000000000), (132908491486073210728313/301839283200000000000000), (60622535993222282744749/143732992000000000000000), (4053102460311361544718707/10061309440000000000000000)]
    reserve := (50355056721/125000000000) }

theorem mixed_003_005_valid : mixed_003_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_005]
  · intro i; fin_cases i <;> norm_num [mixed_003_005]
  · norm_num [mixed_003_005]
  · norm_num [mixed_003_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_005]

def mixed_003_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-83878135053007943/208296125000000000), (-37768474/8331845), (-528227222553007943/104148062500000000), (-37768474/8331845), (-972576310053007943/208296125000000000)]
    bernstein := [(213373648154302221980377/533238080000000000000000), (880548723679285254957/2298440000000000000000), (2285278334758713731719/6248883750000000000000), (181193653554727418869/520740312500000000000), (10734942163541657633/32546269531250000000)]
    reserve := (322105793/976562500) }

theorem mixed_003_006_valid : mixed_003_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_006]
  · intro i; fin_cases i <;> norm_num [mixed_003_006]
  · norm_num [mixed_003_006]
  · norm_num [mixed_003_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_006]

def mixed_003_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-747244678874583569/2197127875000000000), (-73096558/17577023), (-5228639991374583569/1098563937500000000), (-73096558/17577023), (-9710035303874583569/2197127875000000000)]
    bernstein := [(112412277082695376839/343301230468750000000), (1708910730242245615821/5492819687500000000000), (19407870805293635341633/65913836250000000000000), (195048777519850520806833/703080920000000000000000), (1462656921638928484591631/5624647360000000000000000)]
    reserve := (52008839951/200000000000) }

theorem mixed_003_007_valid : mixed_003_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_007]
  · intro i; fin_cases i <;> norm_num [mixed_003_007]
  · norm_num [mixed_003_007]
  · norm_num [mixed_003_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_007]

def mixed_003_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-42712259045193777/147652952000000000), (-3708567/971401), (-331290757045193777/73826476000000000), (-3708567/971401), (-619869255045193777/147652952000000000)]
    bernstein := [(97494492454734036387823/377991557120000000000000), (45784843466820354077867/188995778560000000000000), (64137553290789546560629/283493667840000000000000), (9916793359989426814947/47248944640000000000000), (4563787287744939789663/23624472320000000000000)]
    reserve := (38636099261/200000000000) }

theorem mixed_003_008_valid : mixed_003_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_008]
  · intro i; fin_cases i <;> norm_num [mixed_003_008]
  · norm_num [mixed_003_008]
  · norm_num [mixed_003_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_008]

def mixed_003_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-959576870911762121/3859681000000000000), (-13528061/3859681), (-8201273120911762121/1929840500000000000), (-13528061/3859681), (-15442969370911762121/3859681000000000000)]
    bernstein := [(118146270604509520636999/617548960000000000000000), (43533723778425554679293/247019584000000000000000), (972888355526563029133/6049459200000000000000), (1146723036437976065601/7904626688000000000000), (81558357115912201551/632370135040000000000)]
    reserve := (128972499801/1000000000000) }

theorem mixed_003_009_valid : mixed_003_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_009]
  · intro i; fin_cases i <;> norm_num [mixed_003_009]
  · norm_num [mixed_003_009]
  · norm_num [mixed_003_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_009]

def mixed_003_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (32317707/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(20098469/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-21791977844485237/100492345000000000), (-64635414/20098469), (-203078590344485237/50246172500000000), (-64635414/20098469), (-384365202844485237/100492345000000000)]
    bernstein := [(2096548415281994947/16464665804800000000), (11607210975757045439/102904161280000000000), (188939144140619139181/1929453024000000000000), (66496357444266276103/803938760000000000000), (67488978983406097363/1004923450000000000000)]
    reserve := (67158328311/1000000000000) }

theorem mixed_003_010_valid : mixed_003_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_010]
  · intro i; fin_cases i <;> norm_num [mixed_003_010]
  · norm_num [mixed_003_010]
  · norm_num [mixed_003_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_010]

def mixed_003_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (61455887/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(10426557/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-804772475004034841/4170622800000000000), (-61455887/20853114), (-2682729875001344947/695103800000000000), (-61455887/20853114), (-15291606775004034841/4170622800000000000)]
    bernstein := [(2741434892183840586959/41706228000000000000000), (8620871957510769866777/166824912000000000000000), (24881908677869571013331/667299648000000000000000), (60217446936958700154893/2669198592000000000000000), (79936515032779276797079/10676794368000000000000000)]
    reserve := (1871734911/250000000000) }

theorem mixed_003_011_valid : mixed_003_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_011]
  · intro i; fin_cases i <;> norm_num [mixed_003_011]
  · norm_num [mixed_003_011]
  · norm_num [mixed_003_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_011]

def mixed_003_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(3236689/20000000), (3074597/20000000), (1628949/20000000), (12819283/100000000), (12819283/100000000), (7306763/50000000), (20046733/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5433207/100000000), 0, 0]] i.1) i.2
    mu := ![(38653/625000), (157587/25000000), (2197973/50000000), (3837667/100000000), (1/100000000), (4911941/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-58074087886553423298829576723252501888627/2523750262588357310097112861410000000000000), (-102914607496157/123689600000000), (-5544414544116229142375750867613655055626127/1261875131294178655048556430705000000000000), (-102914607496157/123689600000000), (-3676918333448634953817557386168019203121209/841250087529452436699037620470000000000000)]
    bernstein := [(96198555517859256355793257997499374930821843613/6460800672226194713848608925209600000000000000000), (11118107935057999077054246629248334110956950299/807600084028274339231076115651200000000000000000), (59070648840838940956650682449467538646282443721/4845600504169646035386456693907200000000000000000), (1367888627311445089819181240341459160611708249/134600014004712389871846019275200000000000000000), (3102455835380143612322407501006791389336227273/403800042014137169615538057825600000000000000000)]
    reserve := (7683148867/1000000000000) }

theorem mixed_003_012_valid : mixed_003_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_012]
  · intro i; fin_cases i <;> norm_num [mixed_003_012]
  · norm_num [mixed_003_012]
  · norm_num [mixed_003_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_012]

def mixed_003_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(15479293/100000000), (15022207/100000000), (8290691/100000000), (13482687/100000000), (13482687/100000000), (15479293/100000000), (9381571/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3283849/100000000), 0, 0]] i.1) i.2
    mu := ![(187299/3125000), (40179/10000000), (4335523/100000000), (1999681/50000000), (1/100000000), (518697/10000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-132047946487416966365398721564768833579/9284381988692926846730827800000000000000), (-235256705473879/299678400000000), (-9580148140058454566887611326273911311193/1547396998115487807788471300000000000000), (-235256705473879/299678400000000), (-57348840893863310434960269236078699033579/9284381988692926846730827800000000000000)]
    bernstein := [(128489257907585515343204582757149262210668989/13369510063717814659292392032000000000000000000), (76260959367560496670464743046523042996799863/8913006709145209772861594688000000000000000000), (40758419448955664265816430692590736688452821/5942004472763473181907729792000000000000000000), (23031539632091463799036102154986431582092209/5093146690940119870206625536000000000000000000), (330187890413337101901143498366820605116462589/213912161019485034548678272512000000000000000000)]
    reserve := (385891911/250000000000) }

theorem mixed_003_013_valid : mixed_003_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_013]
  · intro i; fin_cases i <;> norm_num [mixed_003_013]
  · norm_num [mixed_003_013]
  · norm_num [mixed_003_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_013]

def mixed_003_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(1871589/12500000), (2950931/20000000), (8390893/100000000), (13983473/100000000), (13983473/100000000), (201687/1250000), (8889917/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (822437/50000000), 0, 0]] i.1) i.2
    mu := ![(2900311/50000000), (195643/100000000), (2144459/50000000), (4120657/100000000), (1/100000000), (2697513/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-32850370539484661163403069358441478962179/4830572576506575554354506364602500000000000), (-109346171670157/145015550000000), (-4023539416580905974180293974936497815044597/345040898321898253882464740328750000000000), (-109346171670157/145015550000000), (-56296701461593198977360712579752527931662179/4830572576506575554354506364602500000000000)]
    bernstein := [(58978758466283694587654385139765082214825125021/12366265795856833419147536293382400000000000000000), (359758712826756553732913859724699293319865631/84991517497297824186581005452800000000000000000), (71931190859543829268896718783225011145082258609/21199312792897428718538633645798400000000000000000), (764980025002632911437595653015503802173814431/339966069989191296746324021811200000000000000000), (159083511752431300527952767167070978765488606621/197860252733709334706360580694118400000000000000000)]
    reserve := (804019551/1000000000000) }

theorem mixed_003_014_valid : mixed_003_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_014]
  · intro i; fin_cases i <;> norm_num [mixed_003_014]
  · norm_num [mixed_003_014]
  · norm_num [mixed_003_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_014]

def mixed_003_015 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(14715913/100000000), (7304777/50000000), (27/320), (2848601/20000000), (2848601/20000000), (2060131/12500000), (690799/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (788927/100000000), 0, 0]] i.1) i.2
    mu := ![(2848839/50000000), (48219/50000000), (4262963/100000000), (836603/20000000), (1/100000000), (1100813/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-66217746091984038929514178095237608627/20063254016422622303832913591406250000000), (-420624518443399/569767800000000), (-908680153238091084602019279686662510012633/40126508032845244607665827182812500000000), (-420624518443399/569767800000000), (-302849239248635705508053417110157344931793/13375502677615081535888609060937500000000)]
    bernstein := [(1309430673502379360046517307918472338611212807/547860589675113739709997427136000000000000000000), (6971756334590241918679495950156941751737654071/3287163538050682438259984562816000000000000000000), (33614624387390132180369974691202174396713063563/19722981228304094629559907376896000000000000000000), (2142117858974410857117784396065692790801414253/1878379164600389964719991178752000000000000000000), (1612032404928819537718663444963647777343801403/3756758329200779929439982357504000000000000000000)]
    reserve := (429101971/1000000000000) }

theorem mixed_003_015_valid : mixed_003_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_015]
  · intro i; fin_cases i <;> norm_num [mixed_003_015]
  · norm_num [mixed_003_015]
  · norm_num [mixed_003_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_015]

def mixed_003_016 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(364733/2500000), (14536797/100000000), (2114983/25000000), (14372777/100000000), (14372777/100000000), (16654491/100000000), (8506953/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (71883/20000000), 0, 0]] i.1) i.2
    mu := ![(70571/1250000), (47873/100000000), (4249901/100000000), (4214133/100000000), (1/100000000), (2779333/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3861452604833614351341911873499331802431/2402406590857041735887758784100000000000000), (-5154519090723/7057100000000), (-53627063141990309568991858930941044617802431/1201203295428520867943879392050000000000000), (-5154519090723/7057100000000), (-107250264831375785523632375950008589903802431/2402406590857041735887758784100000000000000)]
    bernstein := [(1911168771977751483374481653134881185102711570369/1574441183384070872031401596747776000000000000000000), (377583491590937674329757117163574650007901019641/349875818529793527118089243721728000000000000000000), (16472238394207163412604951877560789948331237635907/18893294200608850464376819160973312000000000000000000), (828316325976500907489950855670182599530160168441/1399503274119174108472356974886912000000000000000000), (6026106292931953135629666248342277811563835768769/25191058934145133952502425547964416000000000000000000)]
    reserve := (59804019/250000000000) }

theorem mixed_003_016_valid : mixed_003_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_016]
  · intro i; fin_cases i <;> norm_num [mixed_003_016]
  · norm_num [mixed_003_016]
  · norm_num [mixed_003_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_016]

def mixed_003_017 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/320), (-1/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(453953/3125000), (14500397/100000000), (8470929/100000000), (3609409/25000000), (3609409/25000000), (16741271/100000000), (8442817/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (144363/100000000), 0, 0]] i.1) i.2
    mu := ![(1404891/25000000), (23851/100000000), (1060839/25000000), (422967/10000000), (1/100000000), (2792987/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1976266649434217936666542001189151403/2549649606382072014934569300000000000000), (-10206522817307/14048910000000), (-113018574433329616131995867948687759151403/1274824803191036007467284650000000000000), (-10206522817307/14048910000000), (-226035172600009798046055069355374329151403/2549649606382072014934569300000000000000)]
    bernstein := [(431494353544917226182530744836840976695954723/685513175810689114136418189312000000000000000000), (45332201131738255259989642425054519256888819/80648608918904601663108022272000000000000000000), (147150743730511226878731212078880858866809512191/320820166279402505415843712598016000000000000000000), (22754937137538018573411460235400435686826201799/71293370284311667870187491688448000000000000000000), (61427818020580505180268371875262141270901030997/427760221705870007221124950130688000000000000000000)]
    reserve := (14360339/100000000000) }

theorem mixed_003_017_valid : mixed_003_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_017]
  · intro i; fin_cases i <;> norm_num [mixed_003_017]
  · norm_num [mixed_003_017]
  · norm_num [mixed_003_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_017]

def mixed_003_018 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/640), (-1/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(2899041/20000000), (3620549/25000000), (4238187/50000000), (2894011/20000000), (2894011/20000000), (1678467/10000000), (3364289/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1471/4000000), 0, 0]] i.1) i.2
    mu := ![(5606479/100000000), (93/781250), (53001/1250000), (4237433/100000000), (1/100000000), (5599629/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-9330006013808069695959618470691659/25733483608712252200420320000000000000), (-406218549166993/560647900000000), (-2273337836970223128149832305376576066659/12866741804356126100210160000000000000), (-406218549166993/560647900000000), (-4546666343934432448229968651134681441659/25733483608712252200420320000000000000)]
    bernstein := [(1460113305022633338280905493168903138714065541/4317362129358249370129269994291200000000000000000), (876482166961516381895054303028337787367033047/2878241419572166246752846662860800000000000000000), (143965312436898173240108101525678914909017053/569322478596692224632431208038400000000000000000), (2109745618836275070019900345211556274372626647/11512965678288664987011386651443200000000000000000), (6607617999285826876677187344432426764307307141/69077794069731989922068319908659200000000000000000)]
    reserve := (95654733/1000000000000) }

theorem mixed_003_018_valid : mixed_003_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_018]
  · intro i; fin_cases i <;> norm_num [mixed_003_018]
  · norm_num [mixed_003_018]
  · norm_num [mixed_003_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_018]

def mixed_003_019 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/1280), (-1/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(14484217/100000000), (14477719/100000000), (8479083/100000000), (7240819/50000000), (7240819/50000000), (4199463/25000000), (4199463/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2801161/50000000), (5949/100000000), (84789/2000000), (265019/6250000), (1/100000000), (2802031/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1834158045712576110074225780350594207/11658132595108215566740754100000000000000), (-921639592793/1273255000000), (-2056668527917305577657913975508135886094207/5829066297554107783370377050000000000000), (-921639592793/1273255000000), (-457037246852951715859968652976721269066023/1295348066123135062971194900000000000000)]
    bernstein := [(147180188761882719213294550072965903980923097273/763281985189350540244964087955456000000000000000000), (1001283314321481543277449222982648252346751301763/5689920253229704027280641382940672000000000000000000), (56387102765717139116162879982571463411925194442979/375534736713160465800522331274084352000000000000000000), (2625446487986599346132720462259348875664564959363/22759681012918816109122565531762688000000000000000000), (35843987517114847283551819720559668787159645695393/500712982284213954400696441698779136000000000000000000)]
    reserve := (8948237/125000000000) }

theorem mixed_003_019_valid : mixed_003_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_019]
  · intro i; fin_cases i <;> norm_num [mixed_003_019]
  · norm_num [mixed_003_019]
  · norm_num [mixed_003_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_019]

def mixed_003_020 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/2560), (-1/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(3620931/25000000), (579219/4000000), (8480439/100000000), (14482437/100000000), (14482437/100000000), (4198811/25000000), (4198811/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(224113/4000000), (119/4000000), (132507/3125000), (4240651/100000000), (1/100000000), (1120739/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-10256187414928891579966225058856271/186615339689734577380910900000000000000), (-202760406646203/280141250000000), (-65811285102863098225475327716189812856271/93307669844867288690455450000000000000), (-202760406646203/280141250000000), (-131622559949538781522059075466154566856271/186615339689734577380910900000000000000)]
    bernstein := [(962968672515542242902288749871475934100604932529/8015067808993407967713936501899264000000000000000000), (1790720547934841834613814307193503408174179946929/16030135617986815935427873003798528000000000000000000), (9501721790776060423783895824832447104218690778387/96180813707920895612567238022791168000000000000000000), (5218546431637205262893710015896042020750903710129/64120542471947263741711492015194112000000000000000000), (448832692290168328502657049335186940121600939937/7543593231993795734318999060611072000000000000000000)]
    reserve := (59498527/1000000000000) }

theorem mixed_003_020_valid : mixed_003_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_020]
  · intro i; fin_cases i <;> norm_num [mixed_003_020]
  · norm_num [mixed_003_020]
  · norm_num [mixed_003_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_020]

def mixed_003_021 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5120), (-1/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(14483479/100000000), (2896371/20000000), (8481117/100000000), (3620709/25000000), (3620709/25000000), (8396969/50000000), (8396969/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1400769/25000000), (93/6250000), (4240611/100000000), (169633/4000000), (1/100000000), (5603511/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1226471659160713443296781188161019/324140623430290803411880050000000000000), (-202760258361131/280153800000000), (-892608737122336564772576919621658033649/633087155137286725413828222656250000), (-202760258361131/280153800000000), (-457015672180164662002845939549507725067269/324140623430290803411880050000000000000)]
    bernstein := [(18663666730084271036559779897560995307201822145531/222747740310104053827774405219975168000000000000000000), (11815269403486563757076003297335486847995381943977/148498493540069369218516270146650112000000000000000000), (195395502360676434837889113913782059053420972561393/2672972883721248645933292862639702016000000000000000000), (38250213397748034289499484239394766034043605790377/593993974160277476874065080586600448000000000000000000), (63496099085629152053016628871867595110832848567977/1187987948320554953748130161173200896000000000000000000)]
    reserve := (53448437/1000000000000) }

theorem mixed_003_021_valid : mixed_003_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_021]
  · intro i; fin_cases i <;> norm_num [mixed_003_021]
  · norm_num [mixed_003_021]
  · norm_num [mixed_003_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_021]

def mixed_003_022 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10240), 0⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(14483317/100000000), (579311/4000000), (8481569/100000000), (7241551/50000000), (7241551/50000000), (4198267/25000000), (4198267/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(175107/3125000), (91/12500000), (4240869/100000000), (4240941/100000000), (1/100000000), (5603389/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(258652918484019820723840509044059579/11895398416759833141508542200000000000000), (-101381396322439/140085600000000), (-17139101550306641456513612078634732923815421/5947699208379916570754271100000000000000), (-101381396322439/140085600000000), (-34278203359266201397047044881109974891690421/11895398416759833141508542200000000000000)]
    bernstein := [(25479725727203701666121283145664882801834486939751137/392373866287669721312226269595923644416000000000000000000), (16698159185347865036108972310386445041343047267/273698288426108901584979261715906560000000000000000), (65485862934434162007460573704834448229678593/1247322929025235879619046114590720000000000000000), (720121736204343256199931320499397516469/18271331968143103705357120819200000000000000), (258652918484019820723840509044059579/11895398416759833141508542200000000000000)]
    reserve := (21743947/1000000000000) }

theorem mixed_003_022_valid : mixed_003_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_022]
  · intro i; fin_cases i <;> norm_num [mixed_003_022]
  · norm_num [mixed_003_022]
  · norm_num [mixed_003_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_022]

def mixed_003_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(3620837/25000000), (14483349/100000000), (530099/6250000), (1448281/10000000), (1448281/10000000), (16793049/100000000), (16793049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2829/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1401127/25000000), (143/20000000), (4240997/100000000), (4240879/100000000), (1/100000000), (5603337/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(3428870128223272342389412019353331957/155324790614605293981039440700000000000000), (261429551635491/550442750000000), (-227872758396876994573443631961878715964468043/77662395307302646990519720350000000000000), (261429551635491/550442750000000), (-455745520222624117370159606313169451282268043/155324790614605293981039440700000000000000)]
    bernstein := [(3428870128223272342389412019353331957/155324790614605293981039440700000000000000), (224990402160989918204642638244583901999/4970393299667369407393262102400000000000000), (86906106719561742844145265173927446197182051/1745034081894646722229954420408320000000000000000), (4649347564078702935337046797229092379872887599/130295878114800288593169930057154560000000000000000), (310528200212406139325343697131265951362310564413557/106738383351644396415524806702821015552000000000000000000)]
    reserve := (581849/200000000000) }

theorem mixed_003_023_valid : mixed_003_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_023]
  · intro i; fin_cases i <;> norm_num [mixed_003_023]
  · norm_num [mixed_003_023]
  · norm_num [mixed_003_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_023]

def mixed_003_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5120), (1/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(7241787/50000000), (14483577/100000000), (4240581/50000000), (14481961/100000000), (14481961/100000000), (16793883/100000000), (16793883/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4243/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5605787/100000000), (143/20000000), (132531/3125000), (3313/78125), (1/100000000), (1400839/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-915955637901361091429210625907121/6519801550405614922651200000000000000), (29532048447398187/18218807750000000), (-735794131527068473736999477775821931317/250761598092523650871200000000000000), (29532048447398187/18218807750000000), (-19130646503748142415800894992960744307121/6519801550405614922651200000000000000)]
    bernstein := [(287524235571462912217760518238243331476211648079/4480373509664353860409035778424832000000000000000000), (65231779436087663697971315808784536614436433093/746728918277392310068172629737472000000000000000000), (308755538724591330926743618361970133352214745837/3360280132248265395306776833818624000000000000000000), (14515598125713206816176908630863750343464938693/186682229569348077517043157434368000000000000000000), (12593222627233232482777682939928095029027161679/280023344354022116275564736151552000000000000000000)]
    reserve := (8994409/200000000000) }

theorem mixed_003_024_valid : mixed_003_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_024]
  · intro i; fin_cases i <;> norm_num [mixed_003_024]
  · norm_num [mixed_003_024]
  · norm_num [mixed_003_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_024]

def mixed_003_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/2560), (1/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(14483911/100000000), (14483921/100000000), (848053/10000000), (14480687/100000000), (14480687/100000000), (4198783/25000000), (4198783/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(16973/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2804123/50000000), (143/10000000), (4240987/100000000), (4240281/100000000), (1/100000000), (1120677/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-22125342646461883667488746083345313751/67343221666067201508556327425000000000000), (59101488266414649/36453599000000000), (-49408250248546724624849599855068286521926251/33671610833033600754278163712500000000000), (59101488266414649/36453599000000000), (-98816478371750802787815532221390489698538751/67343221666067201508556327425000000000000)]
    bernstein := [(233893709764287499953571580860112692039146279394049/2892369346630372634174912904642428928000000000000000000), (8762745384051560444035059148204590495300184721469/68865936824532681766069354872438784000000000000000000), (295682230367379812032023498397222883731470612364547/2169277009972779475631184678481821696000000000000000000), (13021528495977013945419920386365323694093987808683/120515389442932193090621371026767872000000000000000000), (86275497622648262217443776780908914720542827241/2031158249038183029617214118428672000000000000000000)]
    reserve := (42476009/1000000000000) }

theorem mixed_003_025_valid : mixed_003_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_025]
  · intro i; fin_cases i <;> norm_num [mixed_003_025]
  · norm_num [mixed_003_025]
  · norm_num [mixed_003_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_025]

def mixed_003_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(905689/6250000), (1811383/12500000), (2119817/25000000), (14471693/100000000), (14471693/100000000), (16785741/100000000), (16809517/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(33963/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (743/3125000), 0, 0]] i.1) i.2
    mu := ![(5616503/100000000), (2861/100000000), (4242383/100000000), (4238159/100000000), (1/100000000), (700013/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(-14270065645821790879875363896171214610583/20224466677684243957430205086300000000000000), (260753346040179543/160688150830000000), (-7425544212456144796148915465010333109329610583/10112233338842121978715102543150000000000000), (260753346040179543/160688150830000000), (-14851074154846643770506951054656770047444610583/20224466677684243957430205086300000000000000)]
    bernstein := [(6188166367614076381969339126088684278684758688535017/54289639349809750507280216905144598528000000000000000000), (5614345476692690218221916901133053391762489032368617/27144819674904875253640108452572299264000000000000000000), (9160413359679016014975986202064897800173784402449851/40717229512357312880460162678858448896000000000000000000), (1142967824640743509926640127401010414675933532439017/6786204918726218813410027113143074816000000000000000000), (126140381620309669687926252271114941680293996515817/3393102459363109406705013556571537408000000000000000000)]
    reserve := (37175529/1000000000000) }

theorem mixed_003_026_valid : mixed_003_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_026]
  · intro i; fin_cases i <;> norm_num [mixed_003_026]
  · norm_num [mixed_003_026]
  · norm_num [mixed_003_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_026]

def mixed_003_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/640), (1/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(2903579/20000000), (7259027/50000000), (8476717/100000000), (14441003/100000000), (14441003/100000000), (2092943/12500000), (3372357/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(68053/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (118241/100000000), 0, 0]] i.1) i.2
    mu := ![(5639629/100000000), (1433/25000000), (2123973/50000000), (528893/12500000), (1/100000000), (1117393/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-371304702153116298591485013449776834279/253605980784475831944444889725000000000000), (2629458660467765129/1616317671400000000), (-46669908201858942309783891891836169552146779/126802990392237915972222444862500000000000), (2629458660467765129/1616317671400000000), (-93339445099015731503269192298658889327459279/253605980784475831944444889725000000000000)]
    bernstein := [(7626706763847419891001561889456256365076798543921/42548023185130004793116519150125056000000000000000000), (2591516041321430584128095113666201858180355067707/7091337197521667465519419858354176000000000000000000), (12824644711688831323119477064031352538467760937363/31911017388847503594837389362593792000000000000000000), (511582064116487344963935352370627151782699317307/1772834299380416866379854964588544000000000000000000), (67769084380871852745199680291854739734965161521/2659251449070625299569782446882816000000000000000000)]
    reserve := (2548427/100000000000) }

theorem mixed_003_027_valid : mixed_003_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_027]
  · intro i; fin_cases i <;> norm_num [mixed_003_027]
  · norm_num [mixed_003_027]
  · norm_num [mixed_003_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_027]

def mixed_003_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(582139/4000000), (14553919/100000000), (1059157/12500000), (7200107/50000000), (7200107/50000000), (4171873/25000000), (1693143/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(113701/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (121969/50000000), 0, 0]] i.1) i.2
    mu := ![(354223/6250000), (5747/100000000), (2127667/50000000), (844363/20000000), (1/100000000), (1392377/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-4925084098744516743162028514818485037/1075065248689609832542481100000000000000), (647535982898610443/232653666400000000), (-1388091066132752769076895984809840976895259/3762728370413634413898683850000000000000), (647535982898610443/232653666400000000), (-2776147656676814326536589835420078224395259/7525456740827268827797367700000000000000)]
    bernstein := [(3119705125287517021893695197670433125791901657/6070010251899764798751117410304000000000000000000), (8504466822061773137508182696546413396292348171/12140020503799529597502234820608000000000000000000), (697884024832398576498411564746668673100341948807/946921599296363308605174316007424000000000000000000), (393519457930502059751331938389328102578380960007/631281066197575539070116210671616000000000000000000), (454040220555065273858551853199297898438988988821/1262562132395151078140232421343232000000000000000000)]
    reserve := (8990453/25000000000) }

theorem mixed_003_028_valid : mixed_003_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_028]
  · intro i; fin_cases i <;> norm_num [mixed_003_028]
  · norm_num [mixed_003_028]
  · norm_num [mixed_003_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_028]

def mixed_003_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(3647193/25000000), (2917929/20000000), (8469729/100000000), (1794947/12500000), (1794947/12500000), (16631681/100000000), (17001021/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(159569/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (18467/5000000), 0, 0]] i.1) i.2
    mu := ![(711937/12500000), (5761/100000000), (4262691/100000000), (1053129/25000000), (1/100000000), (1388031/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-128744555057339347964268343615606263427/13522040272215007784289661700000000000000), (18494612157119319/4687393208000000), (-2500343548683916593283715236917365653263427/6761020136107503892144830850000000000000), (18494612157119319/4687393208000000), (-5000558352812775847219466205491115700263427/13522040272215007784289661700000000000000)]
    bernstein := [(1924470034701402256867114958071101894338891756813/2268621904076499840387090609078272000000000000000000), (83880828445827374439220926884027270293817340953/81022210859874994299538950324224000000000000000000), (455902937364726788637565198162610142879501949871/425366607014343720072579489202176000000000000000000), (4850270039816692506671529269743875723502601617/5063888178742187143721184395264000000000000000000), (6144404946692057043371389623637685983693554173/8861804312798827501512072691712000000000000000000)]
    reserve := (693358229/1000000000000) }

theorem mixed_003_029_valid : mixed_003_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_029]
  · intro i; fin_cases i <;> norm_num [mixed_003_029]
  · norm_num [mixed_003_029]
  · norm_num [mixed_003_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_029]

def mixed_003_030 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(14641181/100000000), (14642969/100000000), (2116079/25000000), (1787363/12500000), (1787363/12500000), (16548423/100000000), (17105303/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(114391/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (556879/100000000), 0, 0]] i.1) i.2
    mu := ![(358857/6250000), (5781/50000000), (16694/390625), (4198621/100000000), (1/100000000), (5526181/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3982020249143240530940106372163287476263/428563625742405120495566505600000000000000), (3101749148835275699/1106427902400000000), (-39810860219470991534233117208396757471476263/214281812871202560247783252800000000000000), (3101749148835275699/1106427902400000000), (-1941896058992508288486226690498081747694543/10452771359570856597452841600000000000000)]
    bernstein := [(273201450270089341252269024408389354242000178137/280863457766542619767974465110016000000000000000000), (757574851100082779377576780845771462507272547211/561726915533085239535948930220032000000000000000000), (4793372278583595628424239369780318164859949667299/3370361493198511437215693581320192000000000000000000), (297936265070154657068364586578791116190801635211/249656406903593439793755080097792000000000000000000), (2975525269525171068734659936666561757867183581097/4493815324264681916287591441760256000000000000000000)]
    reserve := (662137861/1000000000000) }

theorem mixed_003_030_valid : mixed_003_030.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_030]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_030]
  · intro i; fin_cases i <;> norm_num [mixed_003_030]
  · norm_num [mixed_003_030]
  · norm_num [mixed_003_030, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_030, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_030, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_030, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_030]

def mixed_003_031 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(14710053/100000000), (14713573/100000000), (8456877/100000000), (7109273/50000000), (7109273/50000000), (16438271/100000000), (8622067/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(321821/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (805863/100000000), 0, 0]] i.1) i.2
    mu := ![(5797489/100000000), (5809/50000000), (2144091/50000000), (20901/500000), (1/100000000), (2745923/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2665818173630504595682999874278325133151/138139757382639721520838983100000000000000), (1411990628033696623/354501195800000000), (-12893854383529336664561139778284160646883151/69069878691319860760419491550000000000000), (1411990628033696623/354501195800000000), (-25785042948885042824526596556694042968633151/138139757382639721520838983100000000000000)]
    bernstein := [(2371965063820338317908102177178462612518127031569/1448500342372588286334352575430656000000000000000000), (729707603337313852435405598083486170660557487323/362125085593147071583588143857664000000000000000000), (567303294617576259009416037177347348251740677723/271593814194860303687691107893248000000000000000000), (42067081246292315111744857619630117260379095747/22632817849571691973974258991104000000000000000000), (202575820927167104763612038271849060241677677/152924444929538459283609858048000000000000000000)]
    reserve := (1324679131/1000000000000) }

theorem mixed_003_031_valid : mixed_003_031.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_031]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_031]
  · intro i; fin_cases i <;> norm_num [mixed_003_031]
  · norm_num [mixed_003_031]
  · norm_num [mixed_003_031, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_031, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_031, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_031, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_031]

def mixed_003_032 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/80), (3/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(14811179/100000000), (3704603/25000000), (4222631/50000000), (14099179/100000000), (14099179/100000000), (16274901/100000000), (1090743/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(231481/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1176987/100000000), 0, 0]] i.1) i.2
    mu := ![(5889769/100000000), (11699/50000000), (861943/20000000), (4152797/100000000), (1/100000000), (1088179/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1525495327249329688744640493694150670972437/80517048604683431331645875993700000000000000), (4896000915379731719/1722610188275000000), (-3791911346546914498999599266099670181457972437/40258524302341715665822937996850000000000000), (4896000915379731719/1722610188275000000), (-7582297197766579668310453891705646212244972437/80517048604683431331645875993700000000000000)]
    bernstein := [(6158853778313923664467120652468252341058848313963/3297978310847833347344215080701952000000000000000000), (17347843939318949556451025655316337710785548058689/6595956621695666694688430161403904000000000000000000), (110004363879350568061819001440781191000662878422601/39575739730174000168130580968423424000000000000000000), (61102425325651332497396767795506837998142761680201/26383826486782666778753720645615616000000000000000000), (65366254878391956079912710914544239621822785943003/52767652973565333557507441291231232000000000000000000)]
    reserve := (619378077/500000000000) }

theorem mixed_003_032_valid : mixed_003_032.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_032]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_032]
  · intro i; fin_cases i <;> norm_num [mixed_003_032]
  · norm_num [mixed_003_032]
  · norm_num [mixed_003_032, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_032, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_032, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_032, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_032]

def mixed_003_033 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/160), (1/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(7470941/50000000), (14956189/100000000), (1685793/20000000), (13942253/100000000), (13942253/100000000), (1606059/10000000), (4431967/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(32701/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (833639/50000000), 0, 0]] i.1) i.2
    mu := ![(1500217/25000000), (2361/10000000), (1084493/25000000), (4116699/100000000), (1/100000000), (1074801/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-57319737755915209673160998673681471713/1452673910006160047503938270000000000000), (359173488414909881/88550308425000000), (-69064166905690061349150531468808791501713/726336955003080023751969135000000000000), (359173488414909881/88550308425000000), (-138071014073624207488627901938943901531713/1452673910006160047503938270000000000000)]
    bernstein := [(3028601800823406854461859412954432419082900847/952024373661637048732180984627200000000000000000), (940197428261539059524553490735121038110496549/238006093415409262183045246156800000000000000000), (731962794814518886367911522578133160869125349/178504570061556946637283934617600000000000000000), (54022794629810406970995983864249710187099261/14875380838463078886440327884800000000000000000), (9458769419976579275489495928332929323706687/3718845209615769721610081971200000000000000000)]
    reserve := (1271734757/500000000000) }

theorem mixed_003_033_valid : mixed_003_033.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_033]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_033]
  · intro i; fin_cases i <;> norm_num [mixed_003_033]
  · norm_num [mixed_003_033]
  · norm_num [mixed_003_033, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_033, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_033, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_033, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_033]

def mixed_003_034 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (3/80)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(7564463/50000000), (15158503/100000000), (8402927/100000000), (13711777/100000000), (13711777/100000000), (15746789/100000000), (9069651/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(473241/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2392513/100000000), 0, 0]] i.1) i.2
    mu := ![(309217/5000000), (299/625000), (2189693/50000000), (1015883/25000000), (1/100000000), (5275957/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-772897295028625643280996972900506144647/19728770978548679548858299800000000000000), (2158324390978764159/739647064000000000), (-477223208353693412719066559169332428257147/9864385489274339774429149900000000000000), (2158324390978764159/739647064000000000), (-953673519412358199794852121365764350369647/19728770978548679548858299800000000000000)]
    bernstein := [(180063682709432278621565473868426076657439953/50505653705084619645077247488000000000000000000), (518455122441883488619082892985309188448325059/101011307410169239290154494976000000000000000000), (1099244430304943777185927893340706237006192377/202022614820338478580308989952000000000000000000), (139548968873694914990939425640179110322934887/31080402280052073627739844608000000000000000000), (141524442831966409712403151378106832685661861/62160804560104147255479689216000000000000000000)]
    reserve := (1138373641/500000000000) }

theorem mixed_003_034_valid : mixed_003_034.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_034]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_034]
  · intro i; fin_cases i <;> norm_num [mixed_003_034]
  · norm_num [mixed_003_034]
  · norm_num [mixed_003_034, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_034, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_034, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_034, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_034]

def mixed_003_035 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/80), (1/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(1919257/12500000), (7706473/50000000), (4182789/50000000), (838741/6250000), (838741/6250000), (1919257/12500000), (4668413/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(168257/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (829899/25000000), 0, 0]] i.1) i.2
    mu := ![(3200301/50000000), (24301/50000000), (276951/6250000), (159833/4000000), (1/100000000), (5152687/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1516090390509687892057345766147749906681/18477656543705297999501928459375000000000), (509665571060822899/121516429064062500), (-454820485856455388504958197288493014656681/9238828271852648999750964229687500000000), (509665571060822899/121516429064062500), (-908124881322401089117859048810838279406681/18477656543705297999501928459375000000000)]
    bernstein := [(20987423401376473594243791535684696954862659/3424637158507552063618094976000000000000000000), (1460723583978360902235479128459568786128098013/189211203007542251514899747424000000000000000000), (1139702095570038473806030907468740346350854413/141908402255656688636174810568000000000000000000), (2140864063433914332007420580164745767621363/303223081742856172299518826000000000000000000), (1578284895030911848663093880331207627365391/328491671888094186657812061500000000000000000)]
    reserve := (960928407/200000000000) }

theorem mixed_003_035_valid : mixed_003_035.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_035]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_035]
  · intro i; fin_cases i <;> norm_num [mixed_003_035]
  · norm_num [mixed_003_035]
  · norm_num [mixed_003_035, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_035, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_035, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_035, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_035]

def mixed_003_036 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(3126623/20000000), (15755727/100000000), (2076459/25000000), (13020921/100000000), (13020921/100000000), (74147/500000), (121463/625000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1961803/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (115117/2500000), 0, 0]] i.1) i.2
    mu := ![(1686429/25000000), (24803/25000000), (450047/10000000), (1951253/50000000), (1/100000000), (2493273/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-50591336925691656054033768056387822298761/610551503221756372319254748940000000000000), (2221502570180283223/727452147600000000), (-7748249324593640164779155435261891677923761/305275751610878186159627374470000000000000), (2221502570180283223/727452147600000000), (-15445907312261588673504277102467395533548761/610551503221756372319254748940000000000000)]
    bernstein := [(37924126600423278818713829956313131669098967/5746367089145942327710632931200000000000000000), (1931662123127472375694574932710986178283061717/195376481030962039142161519660800000000000000000), (12353721496378698626920241404548971067803900653/1172258886185772234852969117964800000000000000000), (2226351791697101015922116656091696316262407151/260501974707949385522882026214400000000000000000), (6085050627152557961631600331340861543396073559/1563011848247696313137292157286400000000000000000)]
    reserve := (3893157069/1000000000000) }

theorem mixed_003_036_valid : mixed_003_036.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_036]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_036]
  · intro i; fin_cases i <;> norm_num [mixed_003_036]
  · norm_num [mixed_003_036]
  · norm_num [mixed_003_036, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_036, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_036, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_036, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_036]

def mixed_003_037 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(15976119/100000000), (16222641/100000000), (513819/6250000), (12495457/100000000), (12495457/100000000), (14125097/100000000), (10232063/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2817391/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6339029/100000000), 0, 0]] i.1) i.2
    mu := ![(7162473/100000000), (101803/100000000), (4595447/100000000), (3779429/100000000), (1/100000000), (953049/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-659216874768975397792595438273715375879167/3759998957661613211601955419300000000000000), (107974889460508467223/24305374627300000000), (-49290574616483511215081159604523755968379167/1879999478830806605800977709650000000000000), (107974889460508467223/24305374627300000000), (-97921932358198047032369723770773796560879167/3759998957661613211601955419300000000000000)]
    bernstein := [(110021492752176022788626740466093907989021257873/9625597331613729821701005873408000000000000000000), (35637305086337731098344380300686574042566879691/2406399332903432455425251468352000000000000000000), (27920541690320329062016220629111309397733183391/1804799499677574341568938601264000000000000000000), (2015246378597850104588278838279912735682765599/150399958306464528464078216772000000000000000000), (322356271592455365343481629254751025401617433/37599989576616132116019554193000000000000000000)]
    reserve := (535831717/62500000000) }

theorem mixed_003_037_valid : mixed_003_037.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_037]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_037]
  · intro i; fin_cases i <;> norm_num [mixed_003_037]
  · norm_num [mixed_003_037]
  · norm_num [mixed_003_037, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_037, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_037, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_037, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_037]

def mixed_003_038 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(356381/2000000), (4568969/25000000), (4428573/50000000), (6498629/50000000), (6498629/50000000), (7263353/50000000), (7263353/50000000)]
    cone := fun i => (![![0, 0, 0, (3441557/100000000), 0], ![(4060679/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(792347/12500000), (28539/25000000), (2565843/50000000), (1987107/50000000), (1/100000000), (4925341/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-6138361996553124865399365448322675243651/18027323475495933798478570662000000000000), (8349949417050314963/1292159487600000000), (-12627791959010876699612264626316081720531/429221987511807947582823111000000000000), (8349949417050314963/1292159487600000000), (-524228900281903696518315748856952757018651/18027323475495933798478570662000000000000)]
    bernstein := [(2713123507483006187515619027550269859591149/180273234754959337984785706620000000000000000), (2761358104094767674925694479258960312048669/144218587803967470387828565296000000000000000), (2330525145077367553268050652797998067570921/115374870243173976310262852236800000000000000), (335741609674123304661303950592714075355997/18459979238907836209642056357888000000000000), (5518722514111287359763109356449723922283/421942382603607684791818431037440000000000)]
    reserve := (13079327277/1000000000000) }

theorem mixed_003_038_valid : mixed_003_038.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_038]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_038]
  · intro i; fin_cases i <;> norm_num [mixed_003_038]
  · norm_num [mixed_003_038]
  · norm_num [mixed_003_038, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_038, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_038, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_038, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_038]

def mixed_003_039 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(19807981/100000000), (5142851/25000000), (451057/5000000), (12209531/100000000), (12209531/100000000), (6545103/50000000), (6545103/50000000)]
    cone := fun i => (![![0, 0, 0, (5368287/100000000), 0], ![(1110433/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(6461651/100000000), (25549/20000000), (5675823/100000000), (3835859/100000000), (1/100000000), (2261543/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-16349876161748713378898257239306159360373661/28029524742769975524785142368100000000000000), (36774355207881452221/4127218034975000000), (-465534435491859410983922561874139488570973661/14014762371384987762392571184050000000000000), (36774355207881452221/4127218034975000000), (-914718994821970108588946866508972817781573661/28029524742769975524785142368100000000000000)]
    bernstein := [(95885996194670465441635694524159358038531291/4592357333855432789980797725589504000000000000), (9044885986236176369357451880299956104022407/352174642166827667943312709017600000000000000), (58241826613429071126773680070147576937828624097/2152667500244734120303498933870080000000000000000), (274791209462693234924029445356955349292372651/11005457567713364623228522156800000000000000000), (86914880584197568116008033094865337786736414259/4484723958843196083965622778896000000000000000000)]
    reserve := (19380207429/1000000000000) }

theorem mixed_003_039_valid : mixed_003_039.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_039]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_039]
  · intro i; fin_cases i <;> norm_num [mixed_003_039]
  · norm_num [mixed_003_039]
  · norm_num [mixed_003_039, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_039, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_039, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_039, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_039]

def mixed_003_040 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(21766509/100000000), (22947231/100000000), (9087729/100000000), (2846631/25000000), (2846631/25000000), (11712741/100000000), (11712741/100000000)]
    cone := fun i => (![![0, 0, 0, (718257/10000000), 0], ![(7265983/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(6568437/100000000), (70749/50000000), (6236449/100000000), (920289/25000000), (1/100000000), (2063799/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-693976011083958377354224472008619426683447/755064096738292166847932238300000000000000), (121420529067624738859/10326896651400000000), (-2008680005351991672942512319334431937561921/53933149767020869060566588450000000000000), (121420529067624738859/10326896651400000000), (-27427544063843925043840947998673427699183447/755064096738292166847932238300000000000000)]
    bernstein := [(3366324755948584762988914551003539477563802393/120810255478126746695669158128000000000000000000), (1153332807438023333008599450089183678663859331/34517215850893356198762616608000000000000000000), (50918214434526618041705934586111433835892223219/1449723065737520960348029897536000000000000000000), (31849177536646702321984492011028349230985631437/966482043825013973565353265024000000000000000000), (51905630043836700703288262455257162112731734153/1932964087650027947130706530048000000000000000000)]
    reserve := (6713217071/250000000000) }

theorem mixed_003_040_valid : mixed_003_040.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_040]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_040]
  · intro i; fin_cases i <;> norm_num [mixed_003_040]
  · norm_num [mixed_003_040]
  · norm_num [mixed_003_040, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_040, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_040, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_040, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_040]

def mixed_003_041 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(29670857/100000000), (15916553/50000000), (11484259/100000000), (13505889/100000000), (13505889/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (14835429/100000000), 0], ![(11531993/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (422059/6250000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(165667/3125000), (194687/100000000), (534439/6250000), (223981/5000000), (1/100000000), (2413121/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-9663498055214138363546393786328360010336727/5590010611191051820736856738600000000000000), (183549577780129/9734350000000), (-145261968128439382018771230489868391248336727/2795005305595525910368428369300000000000000), (183549577780129/9734350000000), (-280860438201664625673996067193408422486336727/5590010611191051820736856738600000000000000)]
    bernstein := [(477378380605828243050484861834398711526365604873/14310427164649092661086353250816000000000000000000), (24813560440785721545106430779671975648435865213/596267798527045527545264718784000000000000000000), (7467116442573227790870504145983674492378584039/167700318335731554622105702158000000000000000000), (195791621057237838817065912221305883900955881/4658342175992543183947380615500000000000000000), (29734276258865069281766742161784845189093137/873439157998601846990133865406250000000000000)]
    reserve := (33358779239/1000000000000) }

theorem mixed_003_041_valid : mixed_003_041.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_041]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_041]
  · intro i; fin_cases i <;> norm_num [mixed_003_041]
  · norm_num [mixed_003_041]
  · norm_num [mixed_003_041, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_041, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_041, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_041, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_041]

def mixed_003_042 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(15171341/50000000), (166063/500000), (1116817/10000000), (6319137/50000000), (6319137/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (15171341/100000000), 0], ![(13505497/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (6319137/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(271069/5000000), (201237/100000000), (8853919/100000000), (4261641/100000000), (1/100000000), (2258103/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-59831461573289300253960596525735958567212689/25820897704101524776734118896450000000000000), (2242763348311/100618500000), (-706363941929769952928621149409037489667212689/12910448852050762388367059448225000000000000), (2242763348311/100618500000), (-450965474095416868534427234097446340255737563/8606965901367174925578039632150000000000000)]
    bernstein := [(62890868269924145327863841293114018530351853/1344838422088621082121568692523437500000000000), (3584747498407216080229185060962755735483123987/64552244260253811941835297241125000000000000000), (45458493953097853787241074621066626649679319537/774626931123045743302023566893500000000000000000), (154632264239313065053187949934193547564102728773/2754229088437495976184972682288000000000000000000), (3160509362838312328896588188458482636232304718671/66101498122499903428439344374912000000000000000000)]
    reserve := (46764627807/1000000000000) }

theorem mixed_003_042_valid : mixed_003_042.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_042]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_042]
  · intro i; fin_cases i <;> norm_num [mixed_003_042]
  · norm_num [mixed_003_042]
  · norm_num [mixed_003_042, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_042, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_042, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_042, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_042]

def mixed_003_043 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![(1824171/12500000), (42824877/100000000), (669751/5000000), (1824171/12500000), (1824171/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1824171/25000000), 0], ![(2043859/10000000), 0, (11829143/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1824171/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2607423/100000000), (16049/6250000), (1417247/12500000), (1251329/25000000), (1/100000000), (2607423/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8568269628560976604706500121778770969/2283458716012617534190800000000000000), (8246219434043889/256784000000000), (-81403508993516981686946187144595520969/1141729358006308767095400000000000000), (8246219434043889/256784000000000), (-154238748358472986769185874167412270969/2283458716012617534190800000000000000)]
    bernstein := [(8041458381674657836609489075209565545551/142576934463226850915328000000000000000000), (74393275536815698243725754759975348523/1096745649717129622425600000000000000000), (12618699952116383574534230794304403277669/175369629389769026625853440000000000000000), (30874343200094094620579853599964840851/449665716384023145194496000000000000000), (33793645802950744763178108186220589959/584565431299230088752844800000000000000)]
    reserve := (28200418293/500000000000) }

theorem mixed_003_043_valid : mixed_003_043.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_043]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_043]
  · intro i; fin_cases i <;> norm_num [mixed_003_043]
  · norm_num [mixed_003_043]
  · norm_num [mixed_003_043, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_043, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_043, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_043, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_043]

def mixed_003_044 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, (62809767/100000000), (18090947/100000000), (9549643/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(6717/20000), 0, (54711797/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(238741/25000000), 0, (9549643/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (37231/10000000), (660639/4000000), (3323643/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-36807774432254033047358479489463/5449943744189905800000000000000), (38752885272178701/744620000000000), (-288323697170480851780841553589463/2724971872094952900000000000000), (38752885272178701/744620000000000), (-539839619908707670514324627689463/5449943744189905800000000000000)]
    bernstein := [(98260394814416055009358004265193/1395185598512615884800000000000000), (406223111747073306293563905580353/4650618661708719616000000000000000), (39111159706768286411406579139945843/418555679553784765440000000000000000), (41171662566112174397423369569078089/465061866170871961600000000000000000), (1009901119780614063168161019984818617/13951855985126158848000000000000000000)]
    reserve := (70428188851/1000000000000) }

theorem mixed_003_044_valid : mixed_003_044.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_044]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_044]
  · intro i; fin_cases i <;> norm_num [mixed_003_044]
  · norm_num [mixed_003_044]
  · norm_num [mixed_003_044, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_044, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_044, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_044, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_044]

def mixed_003_045 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, (32515479/50000000), (8630393/50000000), (17708257/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(18646541/50000000), 0, (27550639/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(885413/100000000), 0, (17708257/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (95169/25000000), (17000989/100000000), (6248491/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8477303153785041133256426976697117/1010985300099393923100000000000000), (3743400674107233/63446000000000), (-56059136513685939132448989236197117/505492650049696961550000000000000), (3743400674107233/63446000000000), (-103640969873586837131641551495697117/1010985300099393923100000000000000)]
    bernstein := [(243596674313727508843451522572617287603/2588122368254448443136000000000000000000), (72482424270681756574173171780701666419/647030592063612110784000000000000000000), (57552534261950699946222007924454230661/485272944047709083088000000000000000000), (4595383995724389339194122130458793951/40439412003975756924000000000000000000), (979514373321594851799916391336052923/10109853000993939231000000000000000000)]
    reserve := (18824200687/200000000000) }

theorem mixed_003_045_valid : mixed_003_045.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_045]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_045]
  · intro i; fin_cases i <;> norm_num [mixed_003_045]
  · norm_num [mixed_003_045]
  · norm_num [mixed_003_045, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_045, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_045, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_045, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_045]

def mixed_003_046 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(30524911/50000000), 0, (41103203/50000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (577517/100000000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-34592169114444908552055013/2262317277392400000000000), (569395017/5775170), (-195606453201436508552055013/1131158638696200000000000), (569395017/5775170), (-356620737288428108552055013/2262317277392400000000000)]
    bernstein := [(2474205608706837093034390547/22623172773924000000000000000), (12404529942215295575615572937/90492691095696000000000000000), (159794698189905469363012017581/1085912293148352000000000000000), (201598277502082077551045399317/1447883057531136000000000000000), (653948506597215164632572463307/5791532230124544000000000000000)]
    reserve := (109365986523/1000000000000) }

theorem mixed_003_046_valid : mixed_003_046.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_046]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_046]
  · intro i; fin_cases i <;> norm_num [mixed_003_046]
  · norm_num [mixed_003_046]
  · norm_num [mixed_003_046, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_046, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_046, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_046, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_046]

def mixed_003_047 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2582999/4000000), 0, (19887081/25000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (71153/12500000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-24840276814657694648173271/1393644353658000000000000), (151493897/1423060), (-122220282388524194648173271/696822176829000000000000), (151493897/1423060), (-219600287962390694648173271/1393644353658000000000000)]
    bernstein := [(515774459835714753097844490169/3567729545364480000000000000000), (102854462752865499212300629497/594621590894080000000000000000), (491067540804500739181397027347/2675797159023360000000000000000), (26137213078319186082149792337/148655397723520000000000000000), (33321573439233174233620393129/222983096585280000000000000000)]
    reserve := (144566580307/1000000000000) }

theorem mixed_003_047_valid : mixed_003_047.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_047]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_047]
  · intro i; fin_cases i <;> norm_num [mixed_003_047]
  · norm_num [mixed_003_047]
  · norm_num [mixed_003_047, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_047, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_047, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_047, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_047]

def mixed_003_048 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 0]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(13583621/20000000), 0, (19192791/25000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (560543/100000000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-225687117940091736631685173/10979123676198000000000000), (320397734/2802715), (-977529620943143736631685173/5489561838099000000000000), (320397734/2802715), (-1729372123946195736631685173/10979123676198000000000000)]
    bernstein := [(314235498496942627315637438027/1756659788191680000000000000000), (146182140136763496479577675463/702663915276672000000000000000), (184737751281415488041979179273/843196698332006400000000000000), (23792104293952627085543809151/112426226444267520000000000000), (8326718578362657089749713083/44970490577707008000000000000)]
    reserve := (44720597097/250000000000) }

theorem mixed_003_048_valid : mixed_003_048.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_003_048]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_003_048]
  · intro i; fin_cases i <;> norm_num [mixed_003_048]
  · norm_num [mixed_003_048]
  · norm_num [mixed_003_048, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_003_048, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_003_048, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_003_048, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_003_048]

def mixedTable003 : OwnerTable where
  mode := .mixed
  owners := ![0, 1, 0, 2, 0, 2, 0]
  rows := [mixed_003_000, mixed_003_001, mixed_003_002, mixed_003_003, mixed_003_004, mixed_003_005, mixed_003_006, mixed_003_007, mixed_003_008, mixed_003_009, mixed_003_010, mixed_003_011, mixed_003_012, mixed_003_013, mixed_003_014, mixed_003_015, mixed_003_016, mixed_003_017, mixed_003_018, mixed_003_019, mixed_003_020, mixed_003_021, mixed_003_022, mixed_003_023, mixed_003_024, mixed_003_025, mixed_003_026, mixed_003_027, mixed_003_028, mixed_003_029, mixed_003_030, mixed_003_031, mixed_003_032, mixed_003_033, mixed_003_034, mixed_003_035, mixed_003_036, mixed_003_037, mixed_003_038, mixed_003_039, mixed_003_040, mixed_003_041, mixed_003_042, mixed_003_043, mixed_003_044, mixed_003_045, mixed_003_046, mixed_003_047, mixed_003_048]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_003_000_valid
    · exact mixed_003_001_valid
    · exact mixed_003_002_valid
    · exact mixed_003_003_valid
    · exact mixed_003_004_valid
    · exact mixed_003_005_valid
    · exact mixed_003_006_valid
    · exact mixed_003_007_valid
    · exact mixed_003_008_valid
    · exact mixed_003_009_valid
    · exact mixed_003_010_valid
    · exact mixed_003_011_valid
    · exact mixed_003_012_valid
    · exact mixed_003_013_valid
    · exact mixed_003_014_valid
    · exact mixed_003_015_valid
    · exact mixed_003_016_valid
    · exact mixed_003_017_valid
    · exact mixed_003_018_valid
    · exact mixed_003_019_valid
    · exact mixed_003_020_valid
    · exact mixed_003_021_valid
    · exact mixed_003_022_valid
    · exact mixed_003_023_valid
    · exact mixed_003_024_valid
    · exact mixed_003_025_valid
    · exact mixed_003_026_valid
    · exact mixed_003_027_valid
    · exact mixed_003_028_valid
    · exact mixed_003_029_valid
    · exact mixed_003_030_valid
    · exact mixed_003_031_valid
    · exact mixed_003_032_valid
    · exact mixed_003_033_valid
    · exact mixed_003_034_valid
    · exact mixed_003_035_valid
    · exact mixed_003_036_valid
    · exact mixed_003_037_valid
    · exact mixed_003_038_valid
    · exact mixed_003_039_valid
    · exact mixed_003_040_valid
    · exact mixed_003_041_valid
    · exact mixed_003_042_valid
    · exact mixed_003_043_valid
    · exact mixed_003_044_valid
    · exact mixed_003_045_valid
    · exact mixed_003_046_valid
    · exact mixed_003_047_valid
    · exact mixed_003_048_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
