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

def mixed_007_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-638432322701735789/535495700000000000), (-43020979/5354957), (-2249452497701735789/267747850000000000), (-43020979/5354957), (-3860472672701735789/535495700000000000)]
    bernstein := [(2018189163172449980419/2193390387200000000000), (4922045819891965019943/5483475968000000000000), (35966309939492073677089/41126069760000000000000), (29161993553102634163759/34271724800000000000000), (70833169564657363201811/85679312000000000000000)]
    reserve := (103340537977/125000000000) }

theorem mixed_007_000_valid : mixed_007_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_000]
  · intro i; fin_cases i <;> norm_num [mixed_007_000]
  · norm_num [mixed_007_000]
  · norm_num [mixed_007_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_000]

def mixed_007_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-463584439424451349/469515760000000000), (-84778313/11737894), (-1780883329424451349/234757880000000000), (-84778313/11737894), (-3098182219424451349/469515760000000000)]
    bernstein := [(61743717877011183590251/75122521600000000000000), (120261838135473417770409/150245043200000000000000), (701761794812721635273993/901470259200000000000000), (454336006628787697184529/600980172800000000000000), (881069930649279502042011/1201960345600000000000000)]
    reserve := (366513726461/500000000000) }

theorem mixed_007_001_valid : mixed_007_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_001]
  · intro i; fin_cases i <;> norm_num [mixed_007_001]
  · norm_num [mixed_007_001]
  · norm_num [mixed_007_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_001]

def mixed_007_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2617569561840210799/3189246750000000000), (-27774452/4252329), (-11014526061840210799/1594623375000000000), (-27774452/4252329), (-19411482561840210799/3189246750000000000)]
    bernstein := [(5949827053317156093830561/8164471680000000000000000), (1445667611215448855393791/2041117920000000000000000), (1052207793767594182737863/1530838440000000000000000), (84956007185884073057051/127569870000000000000000), (20542670912776455497081/31892467500000000000000)]
    reserve := (10064421419/15625000000) }

theorem mixed_007_002_valid : mixed_007_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_002]
  · intro i; fin_cases i <;> norm_num [mixed_007_002]
  · norm_num [mixed_007_002]
  · norm_num [mixed_007_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_002]

def mixed_007_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1177095499259553839/1720405125000000000), (-81673514/13763241), (-605533104084394871/95578062500000000), (-81673514/13763241), (-9722500374259553839/1720405125000000000)]
    bernstein := [(11015935038422240838841/17204051250000000000000), (14239923152648945820239/22938735000000000000000), (165387170452975191818429/275264820000000000000000), (213040199480425098684691/367019760000000000000000), (2464933100472708797942401/4404237120000000000000000)]
    reserve := (559673113257/1000000000000) }

theorem mixed_007_003_valid : mixed_007_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_003]
  · intro i; fin_cases i <;> norm_num [mixed_007_003]
  · norm_num [mixed_007_003]
  · norm_num [mixed_007_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_003]

def mixed_007_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1687015189402685609/2950514000000000000), (-11403767/2107510), (-8628847639402685609/1475257000000000000), (-11403767/2107510), (-15570680089402685609/2950514000000000000)]
    bernstein := [(4201724914275460253153831/7553315840000000000000000), (406091888323394249441781/755331584000000000000000), (117514173241897767351949/226599475200000000000000), (3770397213506392934637/7553315840000000000000), (362068925362623858999/755331584000000000000)]
    reserve := (23967548361/50000000000) }

theorem mixed_007_004_valid : mixed_007_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_004]
  · intro i; fin_cases i <;> norm_num [mixed_007_004]
  · norm_num [mixed_007_004]
  · norm_num [mixed_007_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_004]

def mixed_007_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1882761029681522413/3930199000000000000), (-38890387/7860398), (-1524894057811646059/280728500000000000), (-38890387/7860398), (-19465755779681522413/3930199000000000000)]
    bernstein := [(36864946897849232511/77394688000000000000), (4613238310474986107451/10061309440000000000000), (132908491486073210728313/301839283200000000000000), (60622535993222282744749/143732992000000000000000), (4053102460311361544718707/10061309440000000000000000)]
    reserve := (50355056721/125000000000) }

theorem mixed_007_005_valid : mixed_007_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_005]
  · intro i; fin_cases i <;> norm_num [mixed_007_005]
  · norm_num [mixed_007_005]
  · norm_num [mixed_007_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_005]

def mixed_007_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-83878135053007943/208296125000000000), (-37768474/8331845), (-528227222553007943/104148062500000000), (-37768474/8331845), (-972576310053007943/208296125000000000)]
    bernstein := [(213373648154302221980377/533238080000000000000000), (880548723679285254957/2298440000000000000000), (2285278334758713731719/6248883750000000000000), (181193653554727418869/520740312500000000000), (10734942163541657633/32546269531250000000)]
    reserve := (322105793/976562500) }

theorem mixed_007_006_valid : mixed_007_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_006]
  · intro i; fin_cases i <;> norm_num [mixed_007_006]
  · norm_num [mixed_007_006]
  · norm_num [mixed_007_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_006]

def mixed_007_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-747244678874583569/2197127875000000000), (-73096558/17577023), (-5228639991374583569/1098563937500000000), (-73096558/17577023), (-9710035303874583569/2197127875000000000)]
    bernstein := [(112412277082695376839/343301230468750000000), (1708910730242245615821/5492819687500000000000), (19407870805293635341633/65913836250000000000000), (195048777519850520806833/703080920000000000000000), (1462656921638928484591631/5624647360000000000000000)]
    reserve := (52008839951/200000000000) }

theorem mixed_007_007_valid : mixed_007_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_007]
  · intro i; fin_cases i <;> norm_num [mixed_007_007]
  · norm_num [mixed_007_007]
  · norm_num [mixed_007_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_007]

def mixed_007_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-42712259045193777/147652952000000000), (-3708567/971401), (-331290757045193777/73826476000000000), (-3708567/971401), (-619869255045193777/147652952000000000)]
    bernstein := [(97494492454734036387823/377991557120000000000000), (45784843466820354077867/188995778560000000000000), (64137553290789546560629/283493667840000000000000), (9916793359989426814947/47248944640000000000000), (4563787287744939789663/23624472320000000000000)]
    reserve := (38636099261/200000000000) }

theorem mixed_007_008_valid : mixed_007_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_008]
  · intro i; fin_cases i <;> norm_num [mixed_007_008]
  · norm_num [mixed_007_008]
  · norm_num [mixed_007_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_008]

def mixed_007_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-959576870911762121/3859681000000000000), (-13528061/3859681), (-8201273120911762121/1929840500000000000), (-13528061/3859681), (-15442969370911762121/3859681000000000000)]
    bernstein := [(118146270604509520636999/617548960000000000000000), (43533723778425554679293/247019584000000000000000), (972888355526563029133/6049459200000000000000), (1146723036437976065601/7904626688000000000000), (81558357115912201551/632370135040000000000)]
    reserve := (128972499801/1000000000000) }

theorem mixed_007_009_valid : mixed_007_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_009]
  · intro i; fin_cases i <;> norm_num [mixed_007_009]
  · norm_num [mixed_007_009]
  · norm_num [mixed_007_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_009]

def mixed_007_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (32317707/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(20098469/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-21791977844485237/100492345000000000), (-64635414/20098469), (-203078590344485237/50246172500000000), (-64635414/20098469), (-384365202844485237/100492345000000000)]
    bernstein := [(2096548415281994947/16464665804800000000), (11607210975757045439/102904161280000000000), (188939144140619139181/1929453024000000000000), (66496357444266276103/803938760000000000000), (67488978983406097363/1004923450000000000000)]
    reserve := (67158328311/1000000000000) }

theorem mixed_007_010_valid : mixed_007_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_010]
  · intro i; fin_cases i <;> norm_num [mixed_007_010]
  · norm_num [mixed_007_010]
  · norm_num [mixed_007_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_010]

def mixed_007_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(1000061/25000000), (12628013/100000000), (12628013/100000000), (8458343/50000000), (8458343/50000000), (18455179/100000000), (18455179/100000000)]
    cone := fun i => (![![0, 0, (8323579/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4303329/100000000), (441597/12500000), (1/100000000), (333383/6250000), (1/100000000), (790741/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2309648541575680553067563882041009/214088093691930899973350000000000000), (-80838771747625985359/126689145094200000000), (-15522436030023734584759186681367531/18890125913993902938825000000000000), (-80838771747625985359/126689145094200000000), (-520833879396079934222609655520373027/642264281075792699920050000000000000)]
    bernstein := [(1262440858173103299098755448492746423483/27831452179951016996535500000000000000000), (14127231613571474023195864505518237491247/333977426159412203958426000000000000000000), (12075279373908698437500463273288345121171/308286854916380495961624000000000000000000), (192189506423225456460597880847999326754123/5343638818550595263334816000000000000000000), (13700506399657070991382855037740302692819/419108926945144726536064000000000000000000)]
    reserve := (16344803843/500000000000) }

theorem mixed_007_011_valid : mixed_007_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_011]
  · intro i; fin_cases i <;> norm_num [mixed_007_011]
  · norm_num [mixed_007_011]
  · norm_num [mixed_007_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_011]

def mixed_007_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(4897629/100000000), (12957667/100000000), (12957667/100000000), (8490519/50000000), (8490519/50000000), (55039/312500), (55039/312500)]
    cone := fun i => (![![0, 0, (204359/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(870789/20000000), (3668823/100000000), (1/100000000), (674661/12500000), (1/100000000), (3090957/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-11363941744535531037782206410525941/2467484874991602238898970000000000000), (-19482030530978752423/35497452348300000000), (-928861039547677590626574956474025941/1233742437495801119449485000000000000), (-19482030530978752423/35497452348300000000), (-1846358137350819650215367706537525941/2467484874991602238898970000000000000)]
    bernstein := [(205481744878640047726236899815277060337979/6316761279978501731581363200000000000000000), (4946232971498077161339747513714343659347/166230559999434256094246400000000000000000), (127500903607377834660840147130703161152793/4737570959983876298686022400000000000000000), (18950849669966895267587064806248097920177/789595159997312716447670400000000000000000), (8297736313178018828363712728494405161259/394797579998656358223835200000000000000000)]
    reserve := (10508849007/500000000000) }

theorem mixed_007_012_valid : mixed_007_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_012]
  · intro i; fin_cases i <;> norm_num [mixed_007_012]
  · norm_num [mixed_007_012]
  · norm_num [mixed_007_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_012]

def mixed_007_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(3455591/50000000), (3237947/20000000), (3237947/20000000), (10484347/50000000), (10484347/50000000), (469299/5000000), (469299/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (5791357/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1437049/50000000), (921079/20000000), (1/100000000), (1673461/25000000), (1/100000000), (5423523/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(512069420628119064664801041225010877/85809921316554991184197950000000000000), (-10143663827807106561/33090891396775000000), (-21434431497018233298880791686617489123/42904960658277495592098975000000000000), (-10143663827807106561/33090891396775000000), (-43380932414664585662426384414459989123/85809921316554991184197950000000000000)]
    bernstein := [(275699276094838019203671477265676049032477/13729587410648798589471672000000000000000000), (169004296908104736781435616721209494567759/9153058273765865726314448000000000000000000), (2767848583954138199454284643425356980433031/164755048927785583073660064000000000000000000), (552349516091626275839351567328008439558559/36612233095063462905257792000000000000000000), (2926780419294156783683573611070226939937277/219673398570380777431546752000000000000000000)]
    reserve := (1332332653/100000000000) }

theorem mixed_007_013_valid : mixed_007_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_013]
  · intro i; fin_cases i <;> norm_num [mixed_007_013]
  · norm_num [mixed_007_013]
  · norm_num [mixed_007_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_013]

def mixed_007_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(219573/3125000), (3182669/20000000), (3182669/20000000), (4220779/20000000), (4220779/20000000), (1183699/12500000), (1183699/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (5817151/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(297951/10000000), (55949/1250000), (1/100000000), (6678639/100000000), (1/100000000), (2731309/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(400170044186888328524568286092649/63351185101033053016051875000000000), (-101330207940386351/347292927062500000), (-15680221358761717867716479032476101/31675592550516526508025937500000000), (-101330207940386351/347292927062500000), (-31760612761710324063957526351044851/63351185101033053016051875000000000)]
    bernstein := [(2157947053029280687296733632180467271949/162179033858644615721092800000000000000000), (2358459292604779708963671395293662223/202723792323305769651366000000000000000), (3014180533716109042724098405592839099/304085688484958654477049000000000000000), (1031391034827486403647863053722923/126702370202066106032103750000000000), (400170044186888328524568286092649/63351185101033053016051875000000000)]
    reserve := (1263338779/200000000000) }

theorem mixed_007_014_valid : mixed_007_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_014]
  · intro i; fin_cases i <;> norm_num [mixed_007_014]
  · norm_num [mixed_007_014]
  · norm_num [mixed_007_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_014]

def mixed_007_015 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(906487/12500000), (3916531/25000000), (3916531/25000000), (520811/2500000), (520811/2500000), (308609/3125000), (308609/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1369619/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3168817/100000000), (4362061/100000000), (1/100000000), (1646567/25000000), (1/100000000), (5486639/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(1963151767857082395017227494282561089/312186914857123728375477452500000000000), (10019448427849624711/43195540786990625000), (-77774418739719814666581126570751738911/156093457428561864187738726250000000000), (10019448427849624711/43195540786990625000), (-157511989247296711728179480635786038911/312186914857123728375477452500000000000)]
    bernstein := [(1963151767857082395017227494282561089/312186914857123728375477452500000000000), (2415736200803122667261414359445276089/312186914857123728375477452500000000000), (4563388207752087431653434917182535162763/499499063771397965400763924000000000000000), (5236126272405551364405324003927540718489/499499063771397965400763924000000000000000), (9413994007496087273122150896059558013285889/799198502034236744641222278400000000000000000)]
    reserve := (6288385817/1000000000000) }

theorem mixed_007_015_valid : mixed_007_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_015]
  · intro i; fin_cases i <;> norm_num [mixed_007_015]
  · norm_num [mixed_007_015]
  · norm_num [mixed_007_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_015]

def mixed_007_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(3783133/50000000), (385789/2500000), (385789/2500000), (503457/2500000), (503457/2500000), (2661757/25000000), (2661757/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2372813/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3452381/100000000), (2128043/50000000), (1/100000000), (6410723/100000000), (1/100000000), (1100093/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(744336221366981074332596080230256351/129531542980037847802556342500000000000), (23320107078980088633/91835190254787500000), (-33035661202440011498163125948213643649/64765771490018923901278171250000000000), (23320107078980088633/91835190254787500000), (-66815658626247004070658847976657543649/129531542980037847802556342500000000000)]
    bernstein := [(3906155813836893317288312691104343837339551/331600750028896890374544236800000000000000000), (2190249397507420536673172042408824735978751/165800375014448445187272118400000000000000000), (3628360343494281438771262019767301240314253/248700562521672667780908177600000000000000000), (659795364020078326213807120057774037397551/41450093753612111296818029600000000000000000), (356396340703256228610295292064289791697151/20725046876806055648409014800000000000000000)]
    reserve := (1472461919/125000000000) }

theorem mixed_007_016_valid : mixed_007_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_016]
  · intro i; fin_cases i <;> norm_num [mixed_007_016]
  · norm_num [mixed_007_016]
  · norm_num [mixed_007_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_016]

def mixed_007_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(7847857/100000000), (7593359/50000000), (7593359/50000000), (3892923/20000000), (3892923/20000000), (11424739/100000000), (11424739/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2009969/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(467267/12500000), (4140007/100000000), (1/100000000), (6238217/100000000), (1/100000000), (1103811/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(1240810013711113209621705380662033351/266410524405774739982874060000000000000), (427947564570635211131/1547590920695200000000), (-69654912132006137237782632460392166649/133205262202887369991437030000000000000), (427947564570635211131/1547590920695200000000), (-140550634277723387685186970301446366649/266410524405774739982874060000000000000)]
    bernstein := [(733491846951676868857133176687694704974151/42625683904923958397259849600000000000000000), (1587424551367898185094632301896189808297053/85251367809847916794519699200000000000000000), (10221118911270558005409634747492367756865277/511508206859087500767118195200000000000000000), (7261305776944064656422697741909295294717477/341005471239391667178078796800000000000000000), (15383070467299687506030921602040077442370231/682010942478783334356157593600000000000000000)]
    reserve := (537741993/31250000000) }

theorem mixed_007_017_valid : mixed_007_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_017]
  · intro i; fin_cases i <;> norm_num [mixed_007_017]
  · norm_num [mixed_007_017]
  · norm_num [mixed_007_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_017]

def mixed_007_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(323863/4000000), (14933537/100000000), (14933537/100000000), (18813993/100000000), (18813993/100000000), (12204183/100000000), (12204183/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (660981/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1006031/25000000), (4015107/100000000), (1/100000000), (303473/5000000), (1/100000000), (692759/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(1035794969945788139934784337013539/343806250560552648767700000000000000), (484190778113110574113/1615728844126800000000), (-92265382649675420135227092102986461/171903125280276324383850000000000000), (484190778113110574113/1615728844126800000000), (-185566560269296628410388968542986461/343806250560552648767700000000000000)]
    bernstein := [(258339987812981977912657943027395712178167/11441872018655192150989056000000000000000000), (7619702061827146880611265263944542396221/317829778295977559749696000000000000000000), (4178329409813977164113949028073835670253/165027000269065271408496000000000000000000), (47108731299911310095624063783954555821/1770091587044429478804000000000000000000), (12328009697274752691841271559531276707/442522896761107369701000000000000000000)]
    reserve := (2257847207/100000000000) }

theorem mixed_007_018_valid : mixed_007_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_018]
  · intro i; fin_cases i <;> norm_num [mixed_007_018]
  · norm_num [mixed_007_018]
  · norm_num [mixed_007_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_018]

def mixed_007_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(4156569/50000000), (3668643/25000000), (3668643/25000000), (4547367/25000000), (4547367/25000000), (12979391/100000000), (12979391/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2605039/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4308121/100000000), (3882877/100000000), (1/100000000), (1476341/25000000), (1/100000000), (1113799/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(556489690905440271420139098525387499/687662020809366832511067575000000000000), (67603854147970926323/209098799301462500000), (-189609311108769164125462458996971862501/343831010404683416255533787500000000000), (67603854147970926323/209098799301462500000), (-379775111908443768522345057092469112501/687662020809366832511067575000000000000)]
    bernstein := [(191814950662725550036387302464266173377299/6876620208093668325110675750000000000000000), (161033732247007200994543389660528478629319/5501296166474934660088540600000000000000000), (134668865433182571959578151824841923064271/4401036933179947728070832480000000000000000), (22446234846388980819612704180385489536447/704165909308791636491333196800000000000000), (3729615459561677024836566042483295987331/112666545489406661838613311488000000000000)]
    reserve := (13946891413/500000000000) }

theorem mixed_007_019_valid : mixed_007_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_019]
  · intro i; fin_cases i <;> norm_num [mixed_007_019]
  · norm_num [mixed_007_019]
  · norm_num [mixed_007_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_019]

def mixed_007_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(1699847/20000000), (1801643/12500000), (1801643/12500000), (8797373/50000000), (8797373/50000000), (3435623/25000000), (3435623/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1926127/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1146899/25000000), (3745019/100000000), (1/100000000), (5747089/100000000), (1/100000000), (5599079/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-13466231151910607902631058598611789653/6910567632841810473636975550000000000000), (149193110740284154169/429515854608100000000), (-1959180499388667220669733855865609789653/3455283816420905236818487775000000000000), (149193110740284154169/429515854608100000000), (-3904894767625423833436836653132607789653/6910567632841810473636975550000000000000)]
    bernstein := [(2887290399729065827678574546285838734511/87094415458830940615437082624000000000000), (488420781096111512797115196129507832225293/14152842512060027850008525926400000000000000), (19010058344378428215915631985525635774493881/530731594202251044375319722240000000000000000), (16397831182012575225506787030484328192703449/442276328501875870312766435200000000000000000), (3256059896092066515444671234946828805312039/85053140096514590444762776000000000000000000)]
    reserve := (33151269051/1000000000000) }

theorem mixed_007_020_valid : mixed_007_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_020]
  · intro i; fin_cases i <;> norm_num [mixed_007_020]
  · norm_num [mixed_007_020]
  · norm_num [mixed_007_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_020]

def mixed_007_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![(8657691/100000000), (3538379/25000000), (3538379/25000000), (851717/5000000), (851717/5000000), (7241649/50000000), (7241649/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1275521/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4859659/100000000), (1801723/50000000), (1/100000000), (5596111/100000000), (1/100000000), (5631311/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-147793419760535727698571706052851351/28155521510477914625452765000000000000), (166044130061825991/446722417982500000), (-8210637745446086650068276676959951351/14077760755238957312726382500000000000), (166044130061825991/446722417982500000), (-16273482071131637572437981647867051351/28155521510477914625452765000000000000)]
    bernstein := [(172735395200570123380471776654178782953369/4504883441676466340072442400000000000000000), (357521936892982050005997419645581183899061/9009766883352932680144884800000000000000000), (738218911049679782736691447908256133473809/18019533766705865360289769600000000000000000), (89466875938842305915701005496216021560413/2119945149024219454151737600000000000000000), (183950626257321841960090503641018895253497/4239890298048438908303475200000000000000000)]
    reserve := (38344032079/1000000000000) }

theorem mixed_007_021_valid : mixed_007_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_021]
  · intro i; fin_cases i <;> norm_num [mixed_007_021]
  · norm_num [mixed_007_021]
  · norm_num [mixed_007_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_021]

def mixed_007_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, (22960111/100000000), (22960111/100000000), (27039889/100000000), (27039889/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (908341/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2703989/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2770531/50000000), (1/100000000), (8963277/100000000), (1/100000000), (150977/3125000), (1/100000000)]
    alternative := .zero
    polynomial := [(-35098248486488435901245140923197/749843479091392999800000000000000), (20855610185851/34631637500000), (-218552274324140103125923430523197/374921739545696499900000000000000), (20855610185851/34631637500000), (-402006300161791770350601720123197/749843479091392999800000000000000)]
    bernstein := [(4906527495751363605324295155214270259/112917606263174475264000000000000000000), (217436613568473383391424349835442479/4704900260965603136000000000000000000), (1100909400637588252493102072400078829/22495304372741789994000000000000000000), (32260110869585944834785493869492291/624869565909494166500000000000000000), (6359363595501838590447818499179707/117163043608030156218750000000000000)]
    reserve := (8690456091/200000000000) }

theorem mixed_007_022_valid : mixed_007_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_022]
  · intro i; fin_cases i <;> norm_num [mixed_007_022]
  · norm_num [mixed_007_022]
  · norm_num [mixed_007_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_022]

def mixed_007_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, (11668431/50000000), (11668431/50000000), (13331569/50000000), (13331569/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (489511/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (13331569/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2755409/50000000), (1/100000000), (4476667/50000000), (1/100000000), (95279/2000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3404928589575144816186526169653/58763554500722401850000000000000), (5711825327241/8610653125000), (-18093009533186700394201838369653/29381777250361200925000000000000), (5711825327241/8610653125000), (-32781090476798255972217150569653/58763554500722401850000000000000)]
    bernstein := [(38498979740229527331096367594511/706292722364451945312500000000000), (649799426769441120045474503442523/11300683557831231125000000000000000), (106579388942273952140468239595430149/1762906635021672055500000000000000000), (29067182653641090088240785068643443/458642376591004112000000000000000000), (243122168434892760401774340308945587/3669139012728032896000000000000000000)]
    reserve := (54508532399/1000000000000) }

theorem mixed_007_023_valid : mixed_007_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_023]
  · intro i; fin_cases i <;> norm_num [mixed_007_023]
  · norm_num [mixed_007_023]
  · norm_num [mixed_007_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_023]

def mixed_007_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, (11860329/50000000), (11860329/50000000), (13139671/50000000), (13139671/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (8391831/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (13139671/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5466583/100000000), (1/100000000), (8945277/100000000), (1/100000000), (293461/6250000), (1/100000000)]
    alternative := .zero
    polynomial := [(-25499983567674633423086718461323/358756800125478683775000000000000), (99529876572399/136664575000000), (-117131329104490739977511685536323/179378400062739341887500000000000), (99529876572399/136664575000000), (-208762674641306846531936652611323/358756800125478683775000000000000)]
    bernstein := [(61103014275729332072944379441695308197/918417408321225430464000000000000000000), (6407943113162241652603855171850860253/91841740832122543046400000000000000000), (2010704929396713273113732163981430223/27552522249636762913920000000000000000), (69935947705232561139428455545469021/918417408321225430464000000000000000), (46380449955205912521866678268329/584979240968933395200000000000000)]
    reserve := (13306153329/200000000000) }

theorem mixed_007_024_valid : mixed_007_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_024]
  · intro i; fin_cases i <;> norm_num [mixed_007_024]
  · norm_num [mixed_007_024]
  · norm_num [mixed_007_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_024]

def mixed_007_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, (649727/2000000), (649727/2000000), (350273/1000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (12050819/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(350273/20000000), 0, (350273/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7287097/100000000), (1/100000000), (6035661/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3107439164744528898920657/21991223583058500000000000), (7829742476413/7287097000000), (-10842305918531070963583157/10995611791529250000000000), (7829742476413/7287097000000), (-18577172672317613028245657/21991223583058500000000000)]
    bernstein := [(445725436127687093775405127/5629753237262976000000000000), (523794241256098349693552789/6255281374736640000000000000), (149043824041188318819373900477/1688925971178892800000000000000), (57991586312342764985057761757/625528137473664000000000000000), (5467526010975728964346835025463/56297532372629760000000000000000)]
    reserve := (79173174621/1000000000000) }

theorem mixed_007_025_valid : mixed_007_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_025]
  · intro i; fin_cases i <;> norm_num [mixed_007_025]
  · norm_num [mixed_007_025]
  · norm_num [mixed_007_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_025]

def mixed_007_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, (16363753/50000000), (16363753/50000000), (34544989/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6334531/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1727249/100000000), 0, (34544989/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1425263/20000000), (1/100000000), (12024079/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8553040755699536722639333/52461657880950000000000000), (2115442870507/1817937500000), (-27248608118084697112819333/26230828940475000000000000), (2115442870507/1817937500000), (-45944175480469857502999333/52461657880950000000000000)]
    bernstein := [(13108120197950196591267176547947/134301844175232000000000000000000), (3441436427729123619824500043731/33575461043808000000000000000000), (93211485315596664487517939041/868330889064000000000000000000), (235329958371249365900972480399/2098466315238000000000000000000), (61324326842603257352732924627/524616578809500000000000000000)]
    reserve := (48800968737/500000000000) }

theorem mixed_007_026_valid : mixed_007_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_026]
  · intro i; fin_cases i <;> norm_num [mixed_007_026]
  · norm_num [mixed_007_026]
  · norm_num [mixed_007_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_026]

def mixed_007_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, (6593593/20000000), (6593593/20000000), (34064071/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (26521543/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(425801/25000000), 0, (34064071/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (868697/12500000), (1/100000000), (2994583/25000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1172474406728839142329360429/6243324644042400000000000000), (174872260273999/138991520000000), (-3427147551883646939770735429/3121662322021200000000000000), (174872260273999/138991520000000), (-5681820697038454737212110429/6243324644042400000000000000)]
    bernstein := [(7332151729366878512208740993051/62433246440424000000000000000000), (30641029476298173398572478861921/249732985761696000000000000000000), (383298777418544552612344599495173/2996795829140352000000000000000000), (531685997635422050213075337332461/3995727772187136000000000000000000), (2208482106167041572268557895794131/15982911088748544000000000000000000)]
    reserve := (117439860129/1000000000000) }

theorem mixed_007_027_valid : mixed_007_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_027]
  · intro i; fin_cases i <;> norm_num [mixed_007_027]
  · norm_num [mixed_007_027]
  · norm_num [mixed_007_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_027]

def mixed_007_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (41631471/50000000), 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (20350399/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3587082107763798869/4070079800000000000), (83262942/20350399), (-8073476617763798869/2035039900000000000), (83262942/20350399), (-12559871127763798869/4070079800000000000)]
    bernstein := [(1410594187349950607507291/10419404288000000000000000), (782970937210383262458449/5209702144000000000000000), (1289393071544137250690633/7814553216000000000000000), (233793012227942388266729/1302425536000000000000000), (126212035587690384210731/651212768000000000000000)]
    reserve := (1692268277/12500000000) }

theorem mixed_007_028_valid : mixed_007_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_028]
  · intro i; fin_cases i <;> norm_num [mixed_007_028]
  · norm_num [mixed_007_028]
  · norm_num [mixed_007_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_028]

def mixed_007_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 0]
    lambda := ![0, (99999999/100000000), 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (85870743/100000000), 0, 0], ![0, 0, (99999999/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (19590439/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-15187964475643848549/15672351200000000000), (780643110375387/178094900000000), (-32577730361746187949/7836175600000000000), (780643110375387/178094900000000), (-49967496247848527349/15672351200000000000)]
    bernstein := [(491174576026770110554251/2507576192000000000000000), (212375567926557398626119/1003030476800000000000000), (91233188451450767119683/401212190720000000000000), (38974676086665298123263/160484876288000000000000), (16569617120191123222779/64193950515200000000000)]
    reserve := (195876232033/1000000000000) }

theorem mixed_007_029_valid : mixed_007_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_007_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_007_029]
  · intro i; fin_cases i <;> norm_num [mixed_007_029]
  · norm_num [mixed_007_029]
  · norm_num [mixed_007_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_007_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_007_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_007_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_007_029]

def mixedTable007 : OwnerTable where
  mode := .mixed
  owners := ![0, 2, 0, 2, 0, 2, 0]
  rows := [mixed_007_000, mixed_007_001, mixed_007_002, mixed_007_003, mixed_007_004, mixed_007_005, mixed_007_006, mixed_007_007, mixed_007_008, mixed_007_009, mixed_007_010, mixed_007_011, mixed_007_012, mixed_007_013, mixed_007_014, mixed_007_015, mixed_007_016, mixed_007_017, mixed_007_018, mixed_007_019, mixed_007_020, mixed_007_021, mixed_007_022, mixed_007_023, mixed_007_024, mixed_007_025, mixed_007_026, mixed_007_027, mixed_007_028, mixed_007_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_007_000_valid
    · exact mixed_007_001_valid
    · exact mixed_007_002_valid
    · exact mixed_007_003_valid
    · exact mixed_007_004_valid
    · exact mixed_007_005_valid
    · exact mixed_007_006_valid
    · exact mixed_007_007_valid
    · exact mixed_007_008_valid
    · exact mixed_007_009_valid
    · exact mixed_007_010_valid
    · exact mixed_007_011_valid
    · exact mixed_007_012_valid
    · exact mixed_007_013_valid
    · exact mixed_007_014_valid
    · exact mixed_007_015_valid
    · exact mixed_007_016_valid
    · exact mixed_007_017_valid
    · exact mixed_007_018_valid
    · exact mixed_007_019_valid
    · exact mixed_007_020_valid
    · exact mixed_007_021_valid
    · exact mixed_007_022_valid
    · exact mixed_007_023_valid
    · exact mixed_007_024_valid
    · exact mixed_007_025_valid
    · exact mixed_007_026_valid
    · exact mixed_007_027_valid
    · exact mixed_007_028_valid
    · exact mixed_007_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
