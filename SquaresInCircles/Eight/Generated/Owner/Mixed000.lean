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

def mixed_000_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-638432322701735789/535495700000000000), (-43020979/5354957), (-2249452497701735789/267747850000000000), (-43020979/5354957), (-3860472672701735789/535495700000000000)]
    bernstein := [(2018189163172449980419/2193390387200000000000), (4922045819891965019943/5483475968000000000000), (35966309939492073677089/41126069760000000000000), (29161993553102634163759/34271724800000000000000), (70833169564657363201811/85679312000000000000000)]
    reserve := (103340537977/125000000000) }

theorem mixed_000_000_valid : mixed_000_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_000]
  · intro i; fin_cases i <;> norm_num [mixed_000_000]
  · norm_num [mixed_000_000]
  · norm_num [mixed_000_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_000]

def mixed_000_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-463584439424451349/469515760000000000), (-84778313/11737894), (-1780883329424451349/234757880000000000), (-84778313/11737894), (-3098182219424451349/469515760000000000)]
    bernstein := [(61743717877011183590251/75122521600000000000000), (120261838135473417770409/150245043200000000000000), (701761794812721635273993/901470259200000000000000), (454336006628787697184529/600980172800000000000000), (881069930649279502042011/1201960345600000000000000)]
    reserve := (366513726461/500000000000) }

theorem mixed_000_001_valid : mixed_000_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_001]
  · intro i; fin_cases i <;> norm_num [mixed_000_001]
  · norm_num [mixed_000_001]
  · norm_num [mixed_000_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_001]

def mixed_000_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2617569561840210799/3189246750000000000), (-27774452/4252329), (-11014526061840210799/1594623375000000000), (-27774452/4252329), (-19411482561840210799/3189246750000000000)]
    bernstein := [(5949827053317156093830561/8164471680000000000000000), (1445667611215448855393791/2041117920000000000000000), (1052207793767594182737863/1530838440000000000000000), (84956007185884073057051/127569870000000000000000), (20542670912776455497081/31892467500000000000000)]
    reserve := (10064421419/15625000000) }

theorem mixed_000_002_valid : mixed_000_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_002]
  · intro i; fin_cases i <;> norm_num [mixed_000_002]
  · norm_num [mixed_000_002]
  · norm_num [mixed_000_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_002]

def mixed_000_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1177095499259553839/1720405125000000000), (-81673514/13763241), (-605533104084394871/95578062500000000), (-81673514/13763241), (-9722500374259553839/1720405125000000000)]
    bernstein := [(11015935038422240838841/17204051250000000000000), (14239923152648945820239/22938735000000000000000), (165387170452975191818429/275264820000000000000000), (213040199480425098684691/367019760000000000000000), (2464933100472708797942401/4404237120000000000000000)]
    reserve := (559673113257/1000000000000) }

theorem mixed_000_003_valid : mixed_000_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_003]
  · intro i; fin_cases i <;> norm_num [mixed_000_003]
  · norm_num [mixed_000_003]
  · norm_num [mixed_000_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_003]

def mixed_000_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1687015189402685609/2950514000000000000), (-11403767/2107510), (-8628847639402685609/1475257000000000000), (-11403767/2107510), (-15570680089402685609/2950514000000000000)]
    bernstein := [(4201724914275460253153831/7553315840000000000000000), (406091888323394249441781/755331584000000000000000), (117514173241897767351949/226599475200000000000000), (3770397213506392934637/7553315840000000000000), (362068925362623858999/755331584000000000000)]
    reserve := (23967548361/50000000000) }

theorem mixed_000_004_valid : mixed_000_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_004]
  · intro i; fin_cases i <;> norm_num [mixed_000_004]
  · norm_num [mixed_000_004]
  · norm_num [mixed_000_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_004]

def mixed_000_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1882761029681522413/3930199000000000000), (-38890387/7860398), (-1524894057811646059/280728500000000000), (-38890387/7860398), (-19465755779681522413/3930199000000000000)]
    bernstein := [(36864946897849232511/77394688000000000000), (4613238310474986107451/10061309440000000000000), (132908491486073210728313/301839283200000000000000), (60622535993222282744749/143732992000000000000000), (4053102460311361544718707/10061309440000000000000000)]
    reserve := (50355056721/125000000000) }

theorem mixed_000_005_valid : mixed_000_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_005]
  · intro i; fin_cases i <;> norm_num [mixed_000_005]
  · norm_num [mixed_000_005]
  · norm_num [mixed_000_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_005]

def mixed_000_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-83878135053007943/208296125000000000), (-37768474/8331845), (-528227222553007943/104148062500000000), (-37768474/8331845), (-972576310053007943/208296125000000000)]
    bernstein := [(213373648154302221980377/533238080000000000000000), (880548723679285254957/2298440000000000000000), (2285278334758713731719/6248883750000000000000), (181193653554727418869/520740312500000000000), (10734942163541657633/32546269531250000000)]
    reserve := (322105793/976562500) }

theorem mixed_000_006_valid : mixed_000_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_006]
  · intro i; fin_cases i <;> norm_num [mixed_000_006]
  · norm_num [mixed_000_006]
  · norm_num [mixed_000_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_006]

def mixed_000_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-747244678874583569/2197127875000000000), (-73096558/17577023), (-5228639991374583569/1098563937500000000), (-73096558/17577023), (-9710035303874583569/2197127875000000000)]
    bernstein := [(112412277082695376839/343301230468750000000), (1708910730242245615821/5492819687500000000000), (19407870805293635341633/65913836250000000000000), (195048777519850520806833/703080920000000000000000), (1462656921638928484591631/5624647360000000000000000)]
    reserve := (52008839951/200000000000) }

theorem mixed_000_007_valid : mixed_000_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_007]
  · intro i; fin_cases i <;> norm_num [mixed_000_007]
  · norm_num [mixed_000_007]
  · norm_num [mixed_000_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_007]

def mixed_000_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-42712259045193777/147652952000000000), (-3708567/971401), (-331290757045193777/73826476000000000), (-3708567/971401), (-619869255045193777/147652952000000000)]
    bernstein := [(97494492454734036387823/377991557120000000000000), (45784843466820354077867/188995778560000000000000), (64137553290789546560629/283493667840000000000000), (9916793359989426814947/47248944640000000000000), (4563787287744939789663/23624472320000000000000)]
    reserve := (38636099261/200000000000) }

theorem mixed_000_008_valid : mixed_000_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_008]
  · intro i; fin_cases i <;> norm_num [mixed_000_008]
  · norm_num [mixed_000_008]
  · norm_num [mixed_000_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_008]

def mixed_000_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-959576870911762121/3859681000000000000), (-13528061/3859681), (-8201273120911762121/1929840500000000000), (-13528061/3859681), (-15442969370911762121/3859681000000000000)]
    bernstein := [(118146270604509520636999/617548960000000000000000), (43533723778425554679293/247019584000000000000000), (972888355526563029133/6049459200000000000000), (1146723036437976065601/7904626688000000000000), (81558357115912201551/632370135040000000000)]
    reserve := (128972499801/1000000000000) }

theorem mixed_000_009_valid : mixed_000_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_009]
  · intro i; fin_cases i <;> norm_num [mixed_000_009]
  · norm_num [mixed_000_009]
  · norm_num [mixed_000_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_009]

def mixed_000_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (32317707/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(20098469/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-21791977844485237/100492345000000000), (-64635414/20098469), (-203078590344485237/50246172500000000), (-64635414/20098469), (-384365202844485237/100492345000000000)]
    bernstein := [(2096548415281994947/16464665804800000000), (11607210975757045439/102904161280000000000), (188939144140619139181/1929453024000000000000), (66496357444266276103/803938760000000000000), (67488978983406097363/1004923450000000000000)]
    reserve := (67158328311/1000000000000) }

theorem mixed_000_010_valid : mixed_000_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_010]
  · intro i; fin_cases i <;> norm_num [mixed_000_010]
  · norm_num [mixed_000_010]
  · norm_num [mixed_000_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_010]

def mixed_000_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(24134017/100000000), (24134017/100000000), (59571/1250000), (2937053/50000000), (2937053/50000000), (1254863/20000000), (28943759/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5667361/25000000), 0, 0]] i.1) i.2
    mu := ![(4398021/50000000), (1/100000000), (3222817/50000000), (955659/50000000), (1/100000000), (2171757/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-802373214545053767135646184364339391/25143241511876011717542300000000000000), (-3113697148997093011667/2834803369031400000000), (-14147846623357616664306500883612339391/12571620755938005858771150000000000000), (-3113697148997093011667/2834803369031400000000), (-27493320032170179561477355582860339391/25143241511876011717542300000000000000)]
    bernstein := [(221159371353312538330454945551391457341317/3268621396543881523280499000000000000000000), (810939575735004289589229169382312671235651/13074485586175526093121996000000000000000000), (679447757324429257462687894338217083102143/12068755925700485624420304000000000000000000), (3519947792197062119119963364510162656668853/69730589792936139163317312000000000000000000), (37290601887049080723191979546882754522150877/836767077515233669959807744000000000000000000)]
    reserve := (44565092113/1000000000000) }

theorem mixed_000_011_valid : mixed_000_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_011]
  · intro i; fin_cases i <;> norm_num [mixed_000_011]
  · norm_num [mixed_000_011]
  · norm_num [mixed_000_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_011]

def mixed_000_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(206273/1000000), (206273/1000000), (6466347/100000000), (8870583/100000000), (8870583/100000000), (1220737/12500000), (24771991/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7503047/50000000), 0, 0]] i.1) i.2
    mu := ![(7735459/100000000), (1/100000000), (5690017/100000000), (1386871/50000000), (1/100000000), (3333653/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2745452621248944422558618318875115593/203496109955386821724575689000000000000), (-1845758385187546107/2200744660640150000), (-95131243753574977792949953883240105593/101748054977693410862287844500000000000), (-1845758385187546107/2200744660640150000), (-187517034885901011163341289447605095593/203496109955386821724575689000000000000)]
    bernstein := [(23169948528795074478564512445611618628098567/520950041485790263614913763840000000000000000), (10427407119657012299037819521301437536262989/260475020742895131807456881920000000000000000), (13873121947682830791741324113174908161082589/390712531114342697711185322880000000000000000), (118359187033178770290882247803812063751013/3830515010924928408933189440000000000000000), (853221442250796419814764392711558215550007/32559377592861891475932110240000000000000000)]
    reserve := (13102545339/500000000000) }

theorem mixed_000_012_valid : mixed_000_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_012]
  · intro i; fin_cases i <;> norm_num [mixed_000_012]
  · norm_num [mixed_000_012]
  · norm_num [mixed_000_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_012]

def mixed_000_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(8879021/50000000), (8879021/50000000), (7567501/100000000), (2856561/25000000), (2856561/25000000), (12895451/100000000), (10584237/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8273023/100000000), 0, 0]] i.1) i.2
    mu := ![(850971/12500000), (1/100000000), (2524983/50000000), (3462971/100000000), (1/100000000), (4353521/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2167804307995940671254110168776197541/539897686611823713634621050000000000000), (-91853676977386306811/143245820566200000000), (-212331163670577356451029054736394197541/269948843305911856817310525000000000000), (-91853676977386306811/143245820566200000000), (-422494523033158772230803999304012197541/539897686611823713634621050000000000000)]
    bernstein := [(2259381425787769281920607063694784028209659/86383629857891794181539368000000000000000000), (1302175478163118390932970793818828164627753/57589086571927862787692912000000000000000000), (19689926131219081623886653240863225379974177/1036603558294701530178472416000000000000000000), (3525092651139397232094254324734554939991353/230356346287711451150771648000000000000000000), (5313711724708301479744043416738390286903753/460712692575422902301543296000000000000000000)]
    reserve := (2306735547/200000000000) }

theorem mixed_000_013_valid : mixed_000_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_013]
  · intro i; fin_cases i <;> norm_num [mixed_000_013]
  · norm_num [mixed_000_013]
  · norm_num [mixed_000_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_013]

def mixed_000_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(15962309/100000000), (15962309/100000000), (202787/2500000), (2615993/20000000), (2615993/20000000), (14995247/100000000), (9404363/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (95337/2500000), 0, 0]] i.1) i.2
    mu := ![(1231207/20000000), (1/100000000), (4614653/100000000), (972247/25000000), (1/100000000), (2513953/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1163244019005979653460660064027898549/1388685470049375214258486100000000000000), (-373825783286960907573/710199134521375000000), (-484023554849788752684603852365162898549/694342735024687607129243050000000000000), (-373825783286960907573/710199134521375000000), (-966883865680571525715747044666297898549/1388685470049375214258486100000000000000)]
    bernstein := [(42282866006163601558862189525867579117304651/3555034803326400548501724416000000000000000000), (73623864165840604059395523803738245738186251/7110069606652801097003448832000000000000000000), (125119499038483405217032954627571039327735051/14220139213305602194006897664000000000000000000), (205487209584207194071279446415688690000511051/28440278426611204388013795328000000000000000000), (320466530074471851748780673822502507585634251/56880556853222408776027590656000000000000000000)]
    reserve := (1408506473/250000000000) }

theorem mixed_000_014_valid : mixed_000_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_014]
  · intro i; fin_cases i <;> norm_num [mixed_000_014]
  · norm_num [mixed_000_014]
  · norm_num [mixed_000_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_014]

def mixed_000_015 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(3801151/25000000), (3801151/25000000), (1663009/20000000), (13797099/100000000), (13797099/100000000), (3976137/25000000), (17777001/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1872453/100000000), 0, 0]] i.1) i.2
    mu := ![(587417/10000000), (1/100000000), (4424717/100000000), (4070423/100000000), (1/100000000), (5320187/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-236474279515240995643764898517584543/1407143729852375240494147225000000000000), (-310923852071429689897/649788496497250000000), (-464335061041692725933223450766478834543/703571864926187620247073612500000000000), (-310923852071429689897/649788496497250000000), (-928433647803870210870803136634440084543/1407143729852375240494147225000000000000)]
    bernstein := [(329162481073831595290033874293002680772485057/57636607174753289850640270336000000000000000000), (575072481041655213058422925184655063344129857/115273214349506579701280540672000000000000000000), (421146609732846144250318482777395362023201253/98805612299577068315383320576000000000000000000), (1628470074416342388729171186608790003621224257/461092857398026318805122162688000000000000000000), (2579269218009368521174315203753962255882833857/922185714796052637610244325376000000000000000000)]
    reserve := (1398454333/500000000000) }

theorem mixed_000_015_valid : mixed_000_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_015]
  · intro i; fin_cases i <;> norm_num [mixed_000_015]
  · norm_num [mixed_000_015]
  · norm_num [mixed_000_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_015]

def mixed_000_016 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/160), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(7352271/50000000), (7352271/50000000), (4215049/50000000), (14272347/100000000), (14272347/100000000), (4131399/25000000), (17090527/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (564931/100000000), 0, 0]] i.1) i.2
    mu := ![(2848427/50000000), (1/100000000), (4305871/100000000), (1047111/25000000), (1/100000000), (551743/10000000), (1/100000000)]
    alternative := .zero
    polynomial := [(2014154172537798949533986083686083/88573881178049060838046762500000000000), (-548658840921478106103/1226495921491700000000), (-28160112482366173948359412403057438917/44286940589024530419023381250000000000), (-548658840921478106103/1226495921491700000000), (-56322239118904885695668358792198563917/88573881178049060838046762500000000000)]
    bernstein := [(162178269429651696849609784139774880663765683/58047778768846232510822326272000000000000000000), (76450639357985881285076500438299831571003/36279861730528895319263953920000000000000000), (9635928558713835324949591311185603735483/6802474074474167872361991360000000000000000), (1022789136629906714398141755709974203/1417182098848784973408748200000000000000), (2014154172537798949533986083686083/88573881178049060838046762500000000000)]
    reserve := (1136991/50000000000) }

theorem mixed_000_016_valid : mixed_000_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_016]
  · intro i; fin_cases i <;> norm_num [mixed_000_016]
  · norm_num [mixed_000_016]
  · norm_num [mixed_000_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_016]

def mixed_000_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(7211241/50000000), (7211241/50000000), (8550923/100000000), (1811903/12500000), (1811903/12500000), (8394143/50000000), (16825377/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3709/10000000), 0, 0]] i.1) i.2
    mu := ![(1417083/25000000), (1/100000000), (26479/625000), (4252461/100000000), (1/100000000), (224179/4000000), (1/100000000)]
    alternative := .zero
    polynomial := [(14197681522559158957630576572733/2384739116921779595392200000000000000), (19961812486628394963/100061175352000000000), (-745165719092040269099967522421427267/1192369558460889797696100000000000000), (19961812486628394963/100061175352000000000), (-1490345635865603097358892675419427267/2384739116921779595392200000000000000)]
    bernstein := [(14197681522559158957630576572733/2384739116921779595392200000000000000), (12007234238602809564672860979954989/19077912935374236763137600000000000000), (56616963140968309789343258111166046333/45786991044898168231530240000000000000000), (223135622693313985947950831411083884589/122098642786395115284080640000000000000000), (234661994239996040860347242252926649235133/97678914229116092227264512000000000000000000)]
    reserve := (5953557/1000000000000) }

theorem mixed_000_017_valid : mixed_000_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_017]
  · intro i; fin_cases i <;> norm_num [mixed_000_017]
  · norm_num [mixed_000_017]
  · norm_num [mixed_000_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_017]

def mixed_000_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/80), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(7168989/50000000), (7168989/50000000), (8687637/100000000), (14480873/100000000), (14480873/100000000), (16709627/100000000), (8482517/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (127703/50000000), 0, 0]] i.1) i.2
    mu := ![(5749229/100000000), (1/100000000), (2094447/50000000), (4267007/100000000), (1/100000000), (5587071/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1732321734670560617891248386588752699/9568971774258340286411513700000000000000), (85725390695025530479/401381847712100000000), (-2997108704507371731474121751279232752699/4784485887129170143205756850000000000000), (85725390695025530479/401381847712100000000), (-5992485087280072902330352254171876752699/9568971774258340286411513700000000000000)]
    bernstein := [(937212709860408210020599703395613559377660101/391945083873621618131415601152000000000000000000), (196623561274425443138250206803878680943938967/65324180645603603021902600192000000000000000000), (1061963961765686754782721115223238419540322703/293958812905216213598561700864000000000000000000), (68578305645272392715668653925028418747137367/16331045161400900755475650048000000000000000000), (116847026003835675479182799035127590925170501/24496567742101351133213475072000000000000000000)]
    reserve := (478236747/200000000000) }

theorem mixed_000_018_valid : mixed_000_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_018]
  · intro i; fin_cases i <;> norm_num [mixed_000_018]
  · norm_num [mixed_000_018]
  · norm_num [mixed_000_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_018]

def mixed_000_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(14208103/100000000), (14208103/100000000), (4444229/50000000), (7229697/50000000), (7229697/50000000), (2074213/12500000), (4295711/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (29457/5000000), 0, 0]] i.1) i.2
    mu := ![(5903341/100000000), (1/100000000), (413851/10000000), (1072177/25000000), (1/100000000), (5561401/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-38443566225903307942603728721574529/45524228903193183904961271875000000000), (6683180642000103129/28408181118500000000), (-14328930133385956975161526953528730779/22762114451596591952480635937500000000), (6683180642000103129/28408181118500000000), (-28619416700546010642380450178335887029/45524228903193183904961271875000000000)]
    bernstein := [(541560460856129674447141612553287886130171/116542025992174550796700856000000000000000000), (345142023141697111491924296653435748529621/58271012996087275398350428000000000000000000), (207887778180176809096564977675576364931871/29135506498043637699175214000000000000000000), (120680017375039032826077035419545847116921/14567753249021818849587607000000000000000000), (68250061533609518974657253089728382224771/7283876624510909424793803500000000000000000)]
    reserve := (145215979/31250000000) }

theorem mixed_000_019_valid : mixed_000_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_019]
  · intro i; fin_cases i <;> norm_num [mixed_000_019]
  · norm_num [mixed_000_019]
  · norm_num [mixed_000_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_019]

def mixed_000_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(14030547/100000000), (14030547/100000000), (1829499/20000000), (721519/5000000), (721519/5000000), (16442759/100000000), (17487891/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (261283/25000000), 0, 0]] i.1) i.2
    mu := ![(606369/10000000), (1/100000000), (4034407/100000000), (4317151/100000000), (1/100000000), (690983/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(-547244758307988736958590236118255217/243254031218807532003341300000000000000), (214655249474325320157/815446446061000000000), (-77217115770508485050761875805012255217/121627015609403766001670650000000000000), (214655249474325320157/815446446061000000000), (-153886986782708981364565161373906255217/243254031218807532003341300000000000000)]
    bernstein := [(364060598899925645707197511275722216851183/38920644995009205120534608000000000000000000), (826107632804400423000597305564693296860349/77841289990018410241069216000000000000000000), (5515136899609456504838104370006389282257541/467047739940110461446415296000000000000000000), (4029633276449448840058874145671673321245141/311365159960073640964276864000000000000000000), (8726291795075159177488747237819528435557823/622730319920147281928553728000000000000000000)]
    reserve := (9353919981/1000000000000) }

theorem mixed_000_020_valid : mixed_000_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_020]
  · intro i; fin_cases i <;> norm_num [mixed_000_020]
  · norm_num [mixed_000_020]
  · norm_num [mixed_000_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_020]

def mixed_000_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(1731219/12500000), (1731219/12500000), (9395673/100000000), (1800107/12500000), (1800107/12500000), (4074073/25000000), (890341/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11801/781250), 0, 0]] i.1) i.2
    mu := ![(1555791/25000000), (1/100000000), (3924881/100000000), (2172399/50000000), (1/100000000), (5495159/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-876987071893309969925902068847789817/202486048422643284486541975000000000000), (7413765221565640059/25442893899462500000), (-64977128780762245626572892694944789817/101243024211321642243270987500000000000), (7413765221565640059/25442893899462500000), (-129077270489631181283219883321041789817/202486048422643284486541975000000000000)]
    bernstein := [(7265240884423785366201126747971889416775223/518364283961966808285547456000000000000000000), (1977457413323002170273179758833956429332141/129591070990491702071386864000000000000000000), (1597901696943239740506531447815931783850841/97193303242868776553540148000000000000000000), (142224716637039802508466969978095174078649/8099441936905731379461679000000000000000000), (37697741438954208878699234991291562076783/2024860484226432844865419750000000000000000)]
    reserve := (2803140999/200000000000) }

theorem mixed_000_021_valid : mixed_000_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_021]
  · intro i; fin_cases i <;> norm_num [mixed_000_021]
  · norm_num [mixed_000_021]
  · norm_num [mixed_000_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_021]

def mixed_000_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(13965017/100000000), (13965017/100000000), (9833801/100000000), (7327783/50000000), (7327783/50000000), (4115629/25000000), (4115629/25000000)]
    cone := fun i => (![![0, 0, 0, (392943/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(60707/1000000), (1/100000000), (3892729/100000000), (1114891/25000000), (1/100000000), (696161/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(-37741414263289566439663063458518437/4585377020122135543243825000000000000), (2820523132410190103/8688084536875000000), (-1384097554653191108170756200720638437/2292688510061067771621912500000000000), (2820523132410190103/8688084536875000000), (-2730453695043092649901849337982758437/4585377020122135543243825000000000000)]
    bernstein := [(49795947831947567584648319976577975539/2697280600071844437202250000000000000000), (725660218831609339668133356739015206903/36683016160977084345950600000000000000000), (1852858433972404636791043566041992210781/88039238786345002430281440000000000000000), (6146482182394438498613942341073383167/276201533447356870369510400000000000000), (17583718944976635704685225688794592147/751268170976810687405068288000000000000)]
    reserve := (4615384457/250000000000) }

theorem mixed_000_022_valid : mixed_000_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_022]
  · intro i; fin_cases i <;> norm_num [mixed_000_022]
  · norm_num [mixed_000_022]
  · norm_num [mixed_000_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_022]

def mixed_000_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(14673243/100000000), (14673243/100000000), (5196209/50000000), (14462889/100000000), (14462889/100000000), (15667659/100000000), (15667659/100000000)]
    cone := fun i => (![![0, 0, 0, (1907841/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1223957/20000000), (1/100000000), (3981087/100000000), (4500099/100000000), (1/100000000), (269389/5000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-103127876814665213108828897064397711/7292639347240861455202900000000000000), (21438345463983150227/58008086919750000000), (-2137680046916712230537246594358097711/3646319673620430727601450000000000000), (21438345463983150227/58008086919750000000), (-4172232217018759247965664291651797711/7292639347240861455202900000000000000)]
    bernstein := [(84154261933636598761698925465322560523/3584478091955828222461329408000000000000), (1117979304578220926956529993915135151173/44805976149447852780766617600000000000000), (2110161809501983690676942222090484669421/80010671695442594251368960000000000000000), (38846150558916974385551778617098813602289/1400186754670245399398956800000000000000000), (33909961520828460910385158502977299106209/1166822295558537832832464000000000000000000)]
    reserve := (23477410037/1000000000000) }

theorem mixed_000_023_valid : mixed_000_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_023]
  · intro i; fin_cases i <;> norm_num [mixed_000_023]
  · norm_num [mixed_000_023]
  · norm_num [mixed_000_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_023]

def mixed_000_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(15260569/100000000), (15260569/100000000), (10925759/100000000), (14297237/100000000), (14297237/100000000), (2995863/20000000), (2995863/20000000)]
    cone := fun i => (![![0, 0, 0, (1448757/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(6153411/100000000), (1/100000000), (2015187/50000000), (2273359/50000000), (1/100000000), (654039/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(-387998976174510046562340844113763967/18623776490063672531244300000000000000), (340861201486894466417/826684923523800000000), (-5362998030447267081051247091310763967/9311888245031836265622150000000000000), (340861201486894466417/826684923523800000000), (-10337997084720024115540153338507763967/18623776490063672531244300000000000000)]
    bernstein := [(86912136383605465850227069770264365836273/2979804238410187604999088000000000000000000), (183504238235062880920299266430098912785037/5959608476820375209998176000000000000000000), (1157372008096814600539125039788439753171259/35757650860922251259989056000000000000000000), (47529272323925318656653978839762563460021/1402260818075382402352512000000000000000000), (9018909490195543041784859214897259107859/254956512377342254973184000000000000000000)]
    reserve := (14583531237/500000000000) }

theorem mixed_000_024_valid : mixed_000_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_024]
  · intro i; fin_cases i <;> norm_num [mixed_000_024]
  · norm_num [mixed_000_024]
  · norm_num [mixed_000_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_024]

def mixed_000_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(15809511/100000000), (15809511/100000000), (5730001/50000000), (7068273/50000000), (7068273/50000000), (7161971/50000000), (7161971/50000000)]
    cone := fun i => (![![0, 0, 0, (3823783/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(617199/10000000), (1/100000000), (1015087/25000000), (919663/20000000), (1/100000000), (1017039/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2611865969074262336306476665430509/91705195845604886191900000000000000), (284764701796122144853/626510681313000000000), (-78530232047586777736791172517391527/137557793768407329287850000000000000), (284764701796122144853/626510681313000000000), (-149224866187950768464662915038491527/275115587536814658575700000000000000)]
    bernstein := [(1470922774560677317211992941848576781769/41429170829073266232576000000000000000000), (3282441687012739484077623802611764574239/88036988011780690744224000000000000000000), (322051073197366880134530564196355910139/8253467626104439757271000000000000000000), (2545487154876104190094719959198163713/62526269894730604221750000000000000000), (606925809022132749575595512335893979/14328936850875763467484375000000000000)]
    reserve := (35504518799/1000000000000) }

theorem mixed_000_025_valid : mixed_000_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_025]
  · intro i; fin_cases i <;> norm_num [mixed_000_025]
  · norm_num [mixed_000_025]
  · norm_num [mixed_000_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_025]

def mixed_000_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(1392813/6250000), (1392813/6250000), (3295093/20000000), (19477259/100000000), (19477259/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1392813/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (973863/10000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981701/100000000), (1/100000000), (5568341/100000000), (6446087/100000000), (1/100000000), (870009/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-217173488601821490025205525609196529931/3108525140231857594613002575000000000000), (4589448366609/6960426250000), (-909908564784502173533320718488152529931/1554262570115928797306501287500000000000), (4589448366609/6960426250000), (-1602643640967182857041435911367108529931/3108525140231857594613002575000000000000)]
    bernstein := [(20905646544639270638550635253604908441661/485707053161227749158281652343750000000000), (358183985430942589262885326822654524177473/7771312850579643986532506437500000000000000), (654212241475031197420284746891198983892989/13322250600993675405484296750000000000000000), (51816615223247936182065031823607989162871701/994728044874194430276160824000000000000000000), (438036902391552214567688134732017238953647509/7957824358993555442209286592000000000000000000)]
    reserve := (43041677917/1000000000000) }

theorem mixed_000_026_valid : mixed_000_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_026]
  · intro i; fin_cases i <;> norm_num [mixed_000_026]
  · norm_num [mixed_000_026]
  · norm_num [mixed_000_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_026]

def mixed_000_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(22278773/100000000), (22278773/100000000), (2106759/12500000), (19294191/100000000), (19294191/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5569693/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1205887/12500000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3980587/100000000), (1/100000000), (5412003/100000000), (1618343/25000000), (1/100000000), (3447327/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-641324439189643942378275882540165931/8328981019627281070094700000000000000), (15645335175569/22550012500000), (-2496919213765491338056644980571165931/4164490509813640535047350000000000000), (15645335175569/22550012500000), (-4352513988341338733735014078602165931/8328981019627281070094700000000000000)]
    bernstein := [(1179487679811014597134315161817099236651509/21322191410245839539442432000000000000000000), (9591234264862241773123573828791579909857/164016857001891073380326400000000000000000), (39407674521411167716328526285168821879231/639665742307375186183272960000000000000000), (106130183308035259248251566089377329249/1640168570018910733803264000000000000000), (144518441313896272119458567375430045941/2132219141024583953944243200000000000000)]
    reserve := (2765868801/50000000000) }

theorem mixed_000_027_valid : mixed_000_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_027]
  · intro i; fin_cases i <;> norm_num [mixed_000_027]
  · norm_num [mixed_000_027]
  · norm_num [mixed_000_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_027]

def mixed_000_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![(11135539/50000000), (11135539/50000000), (2153153/12500000), (1911631/10000000), (1911631/10000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11135539/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1911631/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3979213/100000000), (1/100000000), (2624867/50000000), (6501991/100000000), (1/100000000), (683109/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-4044473337374822558965613207083066039/47338531913061718809565050000000000000), (23976519204467/32810837500000), (-14587274703787690143184516953322066039/23669265956530859404782525000000000000), (23976519204467/32810837500000), (-25130076070200557727403420699561066039/47338531913061718809565050000000000000)]
    bernstein := [(824990919031717378614768561888339914729/12118664169743800015248652800000000000000), (960960302501476578400589267397595669403/13465182410826444461387392000000000000000), (271320056808398382147827938604210274804179/3635599250923140004574595840000000000000000), (104845348101934312504329455565310577590739/1346518241082644446138739200000000000000000), (9824950524676588907708816886679098361982201/121186641697438000152486528000000000000000000)]
    reserve := (4254753801/62500000000) }

theorem mixed_000_028_valid : mixed_000_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_028]
  · intro i; fin_cases i <;> norm_num [mixed_000_028]
  · norm_num [mixed_000_028]
  · norm_num [mixed_000_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_028]

def mixed_000_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, (1184519/3125000), (29895691/100000000), (321997/1000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(189523/10000000), 0, (1184519/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(321997/20000000), 0, (321997/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (864907/10000000), (5551163/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1018515810429131115772473/4801239736841000000000000), (35412014007629/27028343750000), (-2838406911818943749052473/2400619868420500000000000), (35412014007629/27028343750000), (-4658298013208756382332473/4801239736841000000000000)]
    bernstein := [(988778072833285563086677197207/12291173726312960000000000000000), (264026066567496605999257367711/3072793431578240000000000000000), (210513168145374611890540301809/2304595073683680000000000000000), (18573244187296679175113071819/192049589473640000000000000000), (4898294786111754736237168287/48012397368410000000000000000)]
    reserve := (80446188041/1000000000000) }

theorem mixed_000_029_valid : mixed_000_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_029]
  · intro i; fin_cases i <;> norm_num [mixed_000_029]
  · norm_num [mixed_000_029]
  · norm_num [mixed_000_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_029]

def mixed_000_030 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, (37777193/100000000), (30340181/100000000), (15941313/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(94443/5000000), 0, (37777193/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1594131/100000000), 0, (15941313/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (832621/10000000), (1390109/12500000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-26634315141242891831908489/115743394568900000000000000), (1146166873291933/832621000000000), (-70358920692287762808908489/57871697284450000000000000), (1146166873291933/832621000000000), (-114083526243332633785908489/115743394568900000000000000)]
    bernstein := [(118778107458990216146140242191/1157433945689000000000000000000), (501511674552267532809298642861/4629735782756000000000000000000), (904569245704626292231923132199/7936689913296000000000000000000), (8857233452238854687021804869001/74075772524096000000000000000000), (37071903290338135265532860954471/296303090096384000000000000000000)]
    reserve := (51310965909/500000000000) }

theorem mixed_000_030_valid : mixed_000_030.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_030]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_030]
  · intro i; fin_cases i <;> norm_num [mixed_000_030]
  · norm_num [mixed_000_030]
  · norm_num [mixed_000_030, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_030, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_030, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_030, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_030]

def mixed_000_031 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, (7530779/20000000), (30771539/100000000), (15787283/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(376539/20000000), 0, (7530779/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(197341/12500000), 0, (15787283/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3999883/50000000), (11140411/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3354391425640501264640711449/13368102171573900000000000000), (231733659698881/159995320000000), (-8388002580817657418045711449/6684051085786950000000000000), (231733659698881/159995320000000), (-13421613735994813571450711449/13368102171573900000000000000)]
    bernstein := [(148412574387920174466630078249859/1180080743421696000000000000000000), (751327592637595770539887422175543/5703723593204864000000000000000000), (3532694052237169002845766022889693/25666756169421888000000000000000000), (204619305764955739329768363641503/1425930898301216000000000000000000), (319361567498579774468943071170151/2138896347451824000000000000000000)]
    reserve := (62882381233/500000000000) }

theorem mixed_000_031_valid : mixed_000_031.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_031]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_031]
  · intro i; fin_cases i <;> norm_num [mixed_000_031]
  · norm_num [mixed_000_031]
  · norm_num [mixed_000_031, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_031, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_031, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_031, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_031]

def mixed_000_032 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 0]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (2103217/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (10252217/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-179782200794703179/192229068750000000), (42064340/10252217), (-372011269544703179/96114534375000000), (42064340/10252217), (-564240338294703179/192229068750000000)]
    bernstein := [(4875347786949544410421/30756651000000000000000), (2134528303752767345849/12302660400000000000000), (2780056211318972207479/14763192480000000000000), (399471107887086895873/1968425664000000000000), (171165224627526759109/787370265600000000000)]
    reserve := (2476775159/15625000000) }

theorem mixed_000_032_valid : mixed_000_032.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_000_032]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_000_032]
  · intro i; fin_cases i <;> norm_num [mixed_000_032]
  · norm_num [mixed_000_032]
  · norm_num [mixed_000_032, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_000_032, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_000_032, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_000_032, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_000_032]

def mixedTable000 : OwnerTable where
  mode := .mixed
  owners := ![0, 0, 0, 2, 0, 2, 0]
  rows := [mixed_000_000, mixed_000_001, mixed_000_002, mixed_000_003, mixed_000_004, mixed_000_005, mixed_000_006, mixed_000_007, mixed_000_008, mixed_000_009, mixed_000_010, mixed_000_011, mixed_000_012, mixed_000_013, mixed_000_014, mixed_000_015, mixed_000_016, mixed_000_017, mixed_000_018, mixed_000_019, mixed_000_020, mixed_000_021, mixed_000_022, mixed_000_023, mixed_000_024, mixed_000_025, mixed_000_026, mixed_000_027, mixed_000_028, mixed_000_029, mixed_000_030, mixed_000_031, mixed_000_032]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_000_000_valid
    · exact mixed_000_001_valid
    · exact mixed_000_002_valid
    · exact mixed_000_003_valid
    · exact mixed_000_004_valid
    · exact mixed_000_005_valid
    · exact mixed_000_006_valid
    · exact mixed_000_007_valid
    · exact mixed_000_008_valid
    · exact mixed_000_009_valid
    · exact mixed_000_010_valid
    · exact mixed_000_011_valid
    · exact mixed_000_012_valid
    · exact mixed_000_013_valid
    · exact mixed_000_014_valid
    · exact mixed_000_015_valid
    · exact mixed_000_016_valid
    · exact mixed_000_017_valid
    · exact mixed_000_018_valid
    · exact mixed_000_019_valid
    · exact mixed_000_020_valid
    · exact mixed_000_021_valid
    · exact mixed_000_022_valid
    · exact mixed_000_023_valid
    · exact mixed_000_024_valid
    · exact mixed_000_025_valid
    · exact mixed_000_026_valid
    · exact mixed_000_027_valid
    · exact mixed_000_028_valid
    · exact mixed_000_029_valid
    · exact mixed_000_030_valid
    · exact mixed_000_031_valid
    · exact mixed_000_032_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
