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

def mixed_011_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (43020979/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5354957/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-638432322701735789/535495700000000000), (-43020979/5354957), (-2249452497701735789/267747850000000000), (-43020979/5354957), (-3860472672701735789/535495700000000000)]
    bernstein := [(2018189163172449980419/2193390387200000000000), (4922045819891965019943/5483475968000000000000), (35966309939492073677089/41126069760000000000000), (29161993553102634163759/34271724800000000000000), (70833169564657363201811/85679312000000000000000)]
    reserve := (103340537977/125000000000) }

theorem mixed_011_000_valid : mixed_011_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_000]
  · intro i; fin_cases i <;> norm_num [mixed_011_000]
  · norm_num [mixed_011_000]
  · norm_num [mixed_011_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_000]

def mixed_011_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (84778313/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(5868947/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-463584439424451349/469515760000000000), (-84778313/11737894), (-1780883329424451349/234757880000000000), (-84778313/11737894), (-3098182219424451349/469515760000000000)]
    bernstein := [(61743717877011183590251/75122521600000000000000), (120261838135473417770409/150245043200000000000000), (701761794812721635273993/901470259200000000000000), (454336006628787697184529/600980172800000000000000), (881069930649279502042011/1201960345600000000000000)]
    reserve := (366513726461/500000000000) }

theorem mixed_011_001_valid : mixed_011_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_001]
  · intro i; fin_cases i <;> norm_num [mixed_011_001]
  · norm_num [mixed_011_001]
  · norm_num [mixed_011_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_001]

def mixed_011_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (20830839/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(12756987/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2617569561840210799/3189246750000000000), (-27774452/4252329), (-11014526061840210799/1594623375000000000), (-27774452/4252329), (-19411482561840210799/3189246750000000000)]
    bernstein := [(5949827053317156093830561/8164471680000000000000000), (1445667611215448855393791/2041117920000000000000000), (1052207793767594182737863/1530838440000000000000000), (84956007185884073057051/127569870000000000000000), (20542670912776455497081/31892467500000000000000)]
    reserve := (10064421419/15625000000) }

theorem mixed_011_002_valid : mixed_011_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_002]
  · intro i; fin_cases i <;> norm_num [mixed_011_002]
  · norm_num [mixed_011_002]
  · norm_num [mixed_011_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_002]

def mixed_011_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (40836757/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(13763241/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1177095499259553839/1720405125000000000), (-81673514/13763241), (-605533104084394871/95578062500000000), (-81673514/13763241), (-9722500374259553839/1720405125000000000)]
    bernstein := [(11015935038422240838841/17204051250000000000000), (14239923152648945820239/22938735000000000000000), (165387170452975191818429/275264820000000000000000), (213040199480425098684691/367019760000000000000000), (2464933100472708797942401/4404237120000000000000000)]
    reserve := (559673113257/1000000000000) }

theorem mixed_011_003_valid : mixed_011_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_003]
  · intro i; fin_cases i <;> norm_num [mixed_011_003]
  · norm_num [mixed_011_003]
  · norm_num [mixed_011_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_003]

def mixed_011_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (79826369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1475257/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1687015189402685609/2950514000000000000), (-11403767/2107510), (-8628847639402685609/1475257000000000000), (-11403767/2107510), (-15570680089402685609/2950514000000000000)]
    bernstein := [(4201724914275460253153831/7553315840000000000000000), (406091888323394249441781/755331584000000000000000), (117514173241897767351949/226599475200000000000000), (3770397213506392934637/7553315840000000000000), (362068925362623858999/755331584000000000000)]
    reserve := (23967548361/50000000000) }

theorem mixed_011_004_valid : mixed_011_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_004]
  · intro i; fin_cases i <;> norm_num [mixed_011_004]
  · norm_num [mixed_011_004]
  · norm_num [mixed_011_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_004]

def mixed_011_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (38890387/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3930199/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1882761029681522413/3930199000000000000), (-38890387/7860398), (-1524894057811646059/280728500000000000), (-38890387/7860398), (-19465755779681522413/3930199000000000000)]
    bernstein := [(36864946897849232511/77394688000000000000), (4613238310474986107451/10061309440000000000000), (132908491486073210728313/301839283200000000000000), (60622535993222282744749/143732992000000000000000), (4053102460311361544718707/10061309440000000000000000)]
    reserve := (50355056721/125000000000) }

theorem mixed_011_005_valid : mixed_011_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_005]
  · intro i; fin_cases i <;> norm_num [mixed_011_005]
  · norm_num [mixed_011_005]
  · norm_num [mixed_011_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_005]

def mixed_011_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (18884237/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(1666369/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-83878135053007943/208296125000000000), (-37768474/8331845), (-528227222553007943/104148062500000000), (-37768474/8331845), (-972576310053007943/208296125000000000)]
    bernstein := [(213373648154302221980377/533238080000000000000000), (880548723679285254957/2298440000000000000000), (2285278334758713731719/6248883750000000000000), (181193653554727418869/520740312500000000000), (10734942163541657633/32546269531250000000)]
    reserve := (322105793/976562500) }

theorem mixed_011_006_valid : mixed_011_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_006]
  · intro i; fin_cases i <;> norm_num [mixed_011_006]
  · norm_num [mixed_011_006]
  · norm_num [mixed_011_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_006]

def mixed_011_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (36548279/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(17577023/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-747244678874583569/2197127875000000000), (-73096558/17577023), (-5228639991374583569/1098563937500000000), (-73096558/17577023), (-9710035303874583569/2197127875000000000)]
    bernstein := [(112412277082695376839/343301230468750000000), (1708910730242245615821/5492819687500000000000), (19407870805293635341633/65913836250000000000000), (195048777519850520806833/703080920000000000000000), (1462656921638928484591631/5624647360000000000000000)]
    reserve := (52008839951/200000000000) }

theorem mixed_011_007_valid : mixed_011_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_007]
  · intro i; fin_cases i <;> norm_num [mixed_011_007]
  · norm_num [mixed_011_007]
  · norm_num [mixed_011_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_007]

def mixed_011_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (70462773/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(18456619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-42712259045193777/147652952000000000), (-3708567/971401), (-331290757045193777/73826476000000000), (-3708567/971401), (-619869255045193777/147652952000000000)]
    bernstein := [(97494492454734036387823/377991557120000000000000), (45784843466820354077867/188995778560000000000000), (64137553290789546560629/283493667840000000000000), (9916793359989426814947/47248944640000000000000), (4563787287744939789663/23624472320000000000000)]
    reserve := (38636099261/200000000000) }

theorem mixed_011_008_valid : mixed_011_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_008]
  · intro i; fin_cases i <;> norm_num [mixed_011_008]
  · norm_num [mixed_011_008]
  · norm_num [mixed_011_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_008]

def mixed_011_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (13528061/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(3859681/20000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-959576870911762121/3859681000000000000), (-13528061/3859681), (-8201273120911762121/1929840500000000000), (-13528061/3859681), (-15442969370911762121/3859681000000000000)]
    bernstein := [(118146270604509520636999/617548960000000000000000), (43533723778425554679293/247019584000000000000000), (972888355526563029133/6049459200000000000000), (1146723036437976065601/7904626688000000000000), (81558357115912201551/632370135040000000000)]
    reserve := (128972499801/1000000000000) }

theorem mixed_011_009_valid : mixed_011_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_009]
  · intro i; fin_cases i <;> norm_num [mixed_011_009]
  · norm_num [mixed_011_009]
  · norm_num [mixed_011_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_009]

def mixed_011_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (32317707/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(20098469/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-21791977844485237/100492345000000000), (-64635414/20098469), (-203078590344485237/50246172500000000), (-64635414/20098469), (-384365202844485237/100492345000000000)]
    bernstein := [(2096548415281994947/16464665804800000000), (11607210975757045439/102904161280000000000), (188939144140619139181/1929453024000000000000), (66496357444266276103/803938760000000000000), (67488978983406097363/1004923450000000000000)]
    reserve := (67158328311/1000000000000) }

theorem mixed_011_010_valid : mixed_011_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_010]
  · intro i; fin_cases i <;> norm_num [mixed_011_010]
  · norm_num [mixed_011_010]
  · norm_num [mixed_011_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_010]

def mixed_011_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (61455887/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i.1) i.2
    mu := ![(10426557/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-804772475004034841/4170622800000000000), (-61455887/20853114), (-2682729875001344947/695103800000000000), (-61455887/20853114), (-15291606775004034841/4170622800000000000)]
    bernstein := [(2741434892183840586959/41706228000000000000000), (8620871957510769866777/166824912000000000000000), (24881908677869571013331/667299648000000000000000), (60217446936958700154893/2669198592000000000000000), (79936515032779276797079/10676794368000000000000000)]
    reserve := (1871734911/250000000000) }

theorem mixed_011_011_valid : mixed_011_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_011]
  · intro i; fin_cases i <;> norm_num [mixed_011_011]
  · norm_num [mixed_011_011]
  · norm_num [mixed_011_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_011]

def mixed_011_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![(5742491/100000000), (2776257/25000000), (365571/3125000), (17144787/100000000), (17144787/100000000), (9291159/50000000), (9291159/50000000)]
    cone := fun i => (![![0, 0, (1293123/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2329549/50000000), (394873/12500000), (3649/800000), (1048903/20000000), (1/100000000), (6388589/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-13198825666225041879583000607557734699/669030197017947796752135550000000000000), (-82583433839799/116477450000000), (-46468947610242124295377575578346713665659/13715119038867929833418778775000000000000), (-82583433839799/116477450000000), (-92396743368169021873692248131783560208659/27430238077735859666837557550000000000000)]
    bernstein := [(1023930675419966963339198782384194509125079421/70221409479003800747104147328000000000000000000), (11378697718304608108140698223790209531413127/856358652182973179842733504000000000000000000), (204431909079708473023299233410605293855777669/17555352369750950186776036832000000000000000000), (84754581668108670818869602169877335292176023/8777676184875475093388018416000000000000000000), (32123160931690652547107638147025631901824141/4388838092437737546694009208000000000000000000)]
    reserve := (7319285937/1000000000000) }

theorem mixed_011_012_valid : mixed_011_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_012]
  · intro i; fin_cases i <;> norm_num [mixed_011_012]
  · norm_num [mixed_011_012]
  · norm_num [mixed_011_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_012]

def mixed_011_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![(1267493/20000000), (1216773/10000000), (2510167/20000000), (4282337/25000000), (4282337/25000000), (17342637/100000000), (17342637/100000000)]
    cone := fun i => (![![0, 0, (4689389/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4572879/100000000), (1733287/50000000), (163273/50000000), (670717/12500000), (1/100000000), (769911/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(-86355786759923939553237813134096523842939/7425263867736199796969317854700000000000000), (-50419640027223/76214650000000), (-19067026850779346910685803645454605912592939/3712631933868099898484658927350000000000000), (-50419640027223/76214650000000), (-38047697914798769881818369477775115301342939/7425263867736199796969317854700000000000000)]
    bernstein := [(10286988770195310992383759876909980772434065861/1188042218837791967515090856752000000000000000000), (18340818345437900603343294669088447836696650261/2376084437675583935030181713504000000000000000000), (89052366095651653789836532228544667301229808383/14256506626053503610181090281024000000000000000000), (40324309067726334793131777264615876816703683461/9504337750702335740120726854016000000000000000000), (32451862809570492685325413299362539423837412261/19008675501404671480241453708032000000000000000000)]
    reserve := (213401657/125000000000) }

theorem mixed_011_013_valid : mixed_011_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_013]
  · intro i; fin_cases i <;> norm_num [mixed_011_013]
  · norm_num [mixed_011_013]
  · norm_num [mixed_011_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_013]

def mixed_011_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![(1860271/25000000), (7586433/50000000), (7709317/50000000), (20735021/100000000), (20735021/100000000), (10248687/100000000), (10248687/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (5243167/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(790491/25000000), (427011/10000000), (202917/100000000), (408069/6250000), (1/100000000), (5535913/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-912573913778354347137485431521473579/1695496201137154445259666150000000000000), (-14351121082863/26349700000000), (-9948444159686429475837963611569630973579/847748100568577222629833075000000000000), (-14351121082863/26349700000000), (-19895975745459080597328789737707740473579/1695496201137154445259666150000000000000)]
    bernstein := [(24945758530268482425356877015057883121833621/4340470274911115379864745344000000000000000000), (1546249657737597050123872004548803599602037/263058804540067598779681536000000000000000000), (22849536130787667418411497520598857900865851/4006587946071798812182841856000000000000000000), (5495448630018170398893315119049449791219637/1052235218160270395118726144000000000000000000), (308134286833740880837540925059646286681875221/69447524398577846077835925504000000000000000000)]
    reserve := (2218468473/500000000000) }

theorem mixed_011_014_valid : mixed_011_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_014]
  · intro i; fin_cases i <;> norm_num [mixed_011_014]
  · norm_num [mixed_011_014]
  · norm_num [mixed_011_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_014]

def mixed_011_015 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/80), 0⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![(7202857/100000000), (1557123/10000000), (489301/3125000), (21036153/100000000), (21036153/100000000), (9747987/100000000), (9747987/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (5644083/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1531293/50000000), (541887/12500000), (12627/12500000), (6626199/100000000), (1/100000000), (171883/3125000), (1/100000000)]
    alternative := .zero
    polynomial := [(129343336066611510602948916659801484859/44197819666956232730128244700000000000000), (-55196606133473/102086200000000), (-537550404240070984650727310603628447515141/22098909833478116365064122350000000000000), (-55196606133473/102086200000000), (-1075230151816208580812057570123916696515141/44197819666956232730128244700000000000000)]
    bernstein := [(10653437268409200181761650728612484950974320059/1810342693558527292626052902912000000000000000000), (3448301732078289658389216664196902164918043/565732091737039778945641532160000000000000000), (4813500129932086122560086093808440121777659/848598137605559668418462298240000000000000000), (408043884721411359936845448139596722843/88395639333912465460256489400000000000000), (129343336066611510602948916659801484859/44197819666956232730128244700000000000000)]
    reserve := (2926464179/1000000000000) }

theorem mixed_011_015_valid : mixed_011_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_015]
  · intro i; fin_cases i <;> norm_num [mixed_011_015]
  · norm_num [mixed_011_015]
  · norm_num [mixed_011_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_015]

def mixed_011_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![(55611/800000), (15955763/100000000), (15950777/100000000), (4227777/20000000), (4227777/20000000), (4716079/50000000), (4716079/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24927/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1463341/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3030473/100000000), (4397707/100000000), (20157/20000000), (6691393/100000000), (1/100000000), (2731091/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(84471928488597896326015313700263710858761/32728345815963857027472946947340000000000000), (3073077838783640183/5090437021750000000), (-1248713927274022682527431574702711323511883717/49092518723945785541209420421010000000000000), (3073077838783640183/5090437021750000000), (-2497681270333511158743841195346523438156343717/98185037447891571082418840842020000000000000)]
    bernstein := [(84471928488597896326015313700263710858761/32728345815963857027472946947340000000000000), (207959305158505769330530291484959455710261/32728345815963857027472946947340000000000000), (3524118291055133767097220302780323564577474683/471288179749879541195610436041696000000000000000), (935340015647930314721471156091527301706323583/157096059916626513731870145347232000000000000000), (446265331176857838397659534093321980858329041883/251353695866602421970992232555571200000000000000000)]
    reserve := (88772383/50000000000) }

theorem mixed_011_016_valid : mixed_011_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_016]
  · intro i; fin_cases i <;> norm_num [mixed_011_016]
  · norm_num [mixed_011_016]
  · norm_num [mixed_011_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_016]

def mixed_011_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![(6689047/100000000), (16332161/100000000), (16286291/100000000), (10522153/50000000), (10522153/50000000), (1860389/20000000), (1860389/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(152899/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (5871181/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1514409/50000000), (2229759/50000000), (51533/50000000), (6723881/100000000), (1/100000000), (2711009/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5718888440907404825204728320730170765439/260429527434944268938602488150000000000000), (1032801226078402637/538220958600000000), (-3390496122985760330603026882350210895890439/130214763717472134469301244075000000000000), (1032801226078402637/538220958600000000), (-6775273357530613256380849036379691621015439/260429527434944268938602488150000000000000)]
    bernstein := [(6506798116429481838915204139826732777675739761/666699590233457328482822369664000000000000000000), (504783485893805236166777072098804727132362329/37038866124080962693490131648000000000000000000), (81266722708037606831009107773288119847486713/5494776842583439520462821728000000000000000000), (122608320783624818103694558293394168073747529/9259716531020240673372532912000000000000000000), (373741240549970899545360408237162315031393361/41668724389591083030176398104000000000000000000)]
    reserve := (4484673409/500000000000) }

theorem mixed_011_017_valid : mixed_011_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_017]
  · intro i; fin_cases i <;> norm_num [mixed_011_017]
  · norm_num [mixed_011_017]
  · norm_num [mixed_011_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_017]

def mixed_011_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![(1285109/20000000), (3348823/20000000), (1661381/10000000), (5238597/25000000), (5238597/25000000), (9153877/100000000), (9153877/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(208487/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1180051/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3017681/100000000), (4531737/100000000), (21087/20000000), (6757029/100000000), (1/100000000), (672437/12500000), (1/100000000)]
    alternative := .zero
    polynomial := [(-197870741362390667766129422404741605888409/2426422637093359699712526043050000000000000), (20993711933675428093/6363383924700000000), (-10809930637691019099180942302778981958962803/404403772848893283285421007175000000000000), (20993711933675428093/6363383924700000000), (-64661713084783723927319524394269150147888409/2426422637093359699712526043050000000000000)]
    bernstein := [(6533205623025730608335874690318303917785944391/388227621934937551954004166888000000000000000000), (16160138785364786996538957335073855250361136773/776455243869875103908008333776000000000000000000), (34199149827684499858804751544147441634362759919/1552910487739750207816016667552000000000000000000), (63514242386095349171916757947466098112880084957/3105820975479500415632033335104000000000000000000), (99862832674511507195965346673066421855167819671/6211641950959000831264066670208000000000000000000)]
    reserve := (1607672069/100000000000) }

theorem mixed_011_018_valid : mixed_011_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_018]
  · intro i; fin_cases i <;> norm_num [mixed_011_018]
  · norm_num [mixed_011_018]
  · norm_num [mixed_011_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_018]

def mixed_011_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![(3079469/50000000), (8599279/50000000), (8468603/50000000), (4174851/20000000), (4174851/20000000), (8978393/100000000), (8978393/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2986879/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (5947931/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(374311/12500000), (230799/5000000), (107927/100000000), (6792363/100000000), (1/100000000), (213353/4000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2304398372305608848698852246659526460327/12868471369272926607311511540000000000000), (76831094302819321517/16159305318800000000), (-177120127386144349213502911170104833460327/6434235684636463303655755770000000000000), (76831094302819321517/16159305318800000000), (-351935856399983089578306970093550140460327/12868471369272926607311511540000000000000)]
    bernstein := [(784673620497474908110099516771328423966175913/32943286705338692114717469542400000000000000000), (230116568759445601820943058904567761555919371/8235821676334673028679367385600000000000000000), (180430970230383750958159972923680813592974071/6176866257251004771509525539200000000000000000), (14214474317631701683931751609010627900935119/514738854770917064292460461600000000000000000), (2976382506791759134221954676096081712704273/128684713692729266073115115400000000000000000)]
    reserve := (2891157797/125000000000) }

theorem mixed_011_019_valid : mixed_011_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_019]
  · intro i; fin_cases i <;> norm_num [mixed_011_019]
  · norm_num [mixed_011_019]
  · norm_num [mixed_011_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_019]

def mixed_011_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![(2943491/50000000), (3540791/20000000), (1078839/6250000), (832391/4000000), (832391/4000000), (1752809/20000000), (1752809/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(786721/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1204573/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2956087/100000000), (4714271/100000000), (13823/12500000), (6831729/100000000), (1/100000000), (2642003/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-4423877816229956944452511401671084487380249/13907785762983385146870891311508000000000000), (41177479098669822837/6537918496160000000), (-197811447708055889977911113214450920876180249/6953892881491692573435445655754000000000000), (41177479098669822837/6537918496160000000), (-391199017599881823011369715027230757264980249/13907785762983385146870891311508000000000000)]
    bernstein := [(4278464976872265385954532827834167566833729951/139077857629833851468708913115080000000000000000), (144423503429468441528288711934338584123647053/4120825411254336339813597425632000000000000000), (9717000486236022128884707142866297950642112937/267029486649280994819921113180953600000000000000), (1410759169743686734011423818740982977816753/40574280972350388576626190036992000000000000), (5286214607936257239939042463005436214496763/175280893800553678651025140959805440000000000)]
    reserve := (30158532931/1000000000000) }

theorem mixed_011_020_valid : mixed_011_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_020]
  · intro i; fin_cases i <;> norm_num [mixed_011_020]
  · norm_num [mixed_011_020]
  · norm_num [mixed_011_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_020]

def mixed_011_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![(2803499/50000000), (9135279/50000000), (8796261/50000000), (5191871/25000000), (5191871/25000000), (8497477/100000000), (8497477/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2465587/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1533751/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2898711/100000000), (4829109/100000000), (113457/100000000), (1375457/20000000), (1/100000000), (2614411/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-997522846580968244223684194817328739339773/1983040641089046572385223858528125000000000), (21778652189175046979/2740658782725000000), (-29255934135851429906355111627836207214933523/991520320544523286192611929264062500000000), (21778652189175046979/2740658782725000000), (-57514345425121891568486539060855085690527273/1983040641089046572385223858528125000000000)]
    bernstein := [(1360693690962644487560348657079035997321207/36100153181781043379955008553472000000000000), (19027667961204666650538581920836643203037057/451251914772263042249437606918400000000000000), (6639293372754008178449639996117136868018964621/152297521235638776759185192334960000000000000000), (5324077613141987993066241823659937380637165909/126914601029698980632654326945800000000000000000), (11802108573067464970010272659938203701614745287/317286502574247451581635817364500000000000000000)]
    reserve := (7439401599/200000000000) }

theorem mixed_011_021_valid : mixed_011_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_021]
  · intro i; fin_cases i <;> norm_num [mixed_011_021]
  · norm_num [mixed_011_021]
  · norm_num [mixed_011_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_021]

def mixed_011_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, (12114981/50000000), (11491619/50000000), (131967/500000), (131967/500000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (7177111/100000000), 0, 0], ![(1534429/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (131967/1000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (78731/1250000), (4669/3125000), (353729/4000000), (1/100000000), (943151/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-137429171232637526467004650211489/142704879100409655948800000000000), (18589578180849/1494080000000), (-2796922599157646432715179498219489/71352439550204827974400000000000), (18589578180849/1494080000000), (-5456416027082655338963354346227489/142704879100409655948800000000000)]
    bernstein := [(1003677543335807446820032379302612591/22832780656065544951808000000000000000), (2294537935765625080263698800425096179/45665561312131089903616000000000000000), (70857303078098812040185219960598351/1349721024003874578432000000000000000), (1322219814542503551718785500240313517/26094606464074908516352000000000000000), (16332966250647728906970070987860883711/365324490497048719228928000000000000000)]
    reserve := (549471809/12500000000) }

theorem mixed_011_022_valid : mixed_011_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_022]
  · intro i; fin_cases i <;> norm_num [mixed_011_022]
  · norm_num [mixed_011_022]
  · norm_num [mixed_011_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_022]

def mixed_011_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, (3115391/12500000), (5807559/25000000), (12961659/50000000), (12961659/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (230701/3125000), 0, 0], ![(2257189/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (12961659/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3239333/50000000), (152427/100000000), (8795523/100000000), (1/100000000), (926353/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8088291047042507067469792955964576067/6095533786459911271930650000000000000), (639275117809/43303125000), (-3995256608189536789524106100079115357/98315061071934052773075000000000000), (639275117809/43303125000), (-21783419878246252171184071386267325097/554139435132719206539150000000000000)]
    bernstein := [(16614866608406752723758915701067532118383/305971892026222997179264000000000000000000), (2328654592841885223650645054058504383569/38246486503277874647408000000000000000000), (11573741877916574739098259603843563478419/182866013593797338157919500000000000000000), (312234845022086266579014789812883267901/5079611488716592726608875000000000000000), (52719263611368491492730091719762644677/952427154134361136239164062500000000000)]
    reserve := (27150968833/500000000000) }

theorem mixed_011_023_valid : mixed_011_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_023]
  · intro i; fin_cases i <;> norm_num [mixed_011_023]
  · norm_num [mixed_011_023]
  · norm_num [mixed_011_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_023]

def mixed_011_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, (17205493/50000000), (6287503/20000000), (68303/200000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10192813/100000000), 0, 0], ![(6996403/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(68303/4000000), 0, (68303/200000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2236249/25000000), (104249/50000000), (2932233/25000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5227173626646010439841757245757/2187461975786106345600000000000), (120376562841679/5212450000000), (-61975616579157197887931648685757/1093730987893053172800000000000), (120376562841679/5212450000000), (-118724059531668385336021540125757/2187461975786106345600000000000)]
    bernstein := [(20691729972029707903540686187067/341790933716579116500000000000000), (381064043993711265069014888518231/5468654939465265864000000000000000), (4791054281677297143897762362300381/65623859273583190368000000000000000), (49306229729091165869690519337038947/699987832251554030592000000000000000), (346485855389116109200180648629093923/5599902658012432244736000000000000000)]
    reserve := (7567392787/125000000000) }

theorem mixed_011_024_valid : mixed_011_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_024]
  · intro i; fin_cases i <;> norm_num [mixed_011_024]
  · norm_num [mixed_011_024]
  · norm_num [mixed_011_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_024]

def mixed_011_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, (35128443/100000000), (15688557/50000000), (33494443/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10405329/100000000), 0, 0], ![(1579507/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(837361/50000000), 0, (33494443/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1141437/12500000), (42127/20000000), (5798443/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-680837497937424188277681944896733/223055973485128845600000000000000), (55485621617601/2106350000000), (-6516971056777677820436068890496733/111527986742564422800000000000000), (55485621617601/2106350000000), (-12353104615617931452594455836096733/223055973485128845600000000000000)]
    bernstein := [(42581088254143066137432764315939661187/571023292121929844736000000000000000000), (4802148092181189983505756023035218763/57102329212192984473600000000000000000), (1501295710738556370833377928515678633/17130698763657895342080000000000000000), (48593796184316014153653579844486091/571023292121929844736000000000000000), (4360852491804169771928361582444163/57102329212192984473600000000000000)]
    reserve := (74569792233/1000000000000) }

theorem mixed_011_025_valid : mixed_011_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_025]
  · intro i; fin_cases i <;> norm_num [mixed_011_025]
  · norm_num [mixed_011_025]
  · norm_num [mixed_011_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_025]

def mixed_011_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, (17949483/50000000), (15635283/50000000), (8207617/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2126713/20000000), 0, 0], ![(8816001/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1641523/100000000), 0, (8207617/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (933179/10000000), (106397/50000000), (5728217/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1302572615901372155992822807109243/341244021854795802600000000000000), (158242660077483/5319850000000), (-10303626461304082979442645769109243/170622010927397901300000000000000), (158242660077483/5319850000000), (-19304680306706793802892468731109243/341244021854795802600000000000000)]
    bernstein := [(7757550702793850456277661941428773/87358469594827725465600000000000000), (28757701512463641711828308303143533/291194898649425751552000000000000000), (2687252250113901359654463417806128423/26207540878448317639680000000000000000), (2912995901525714722651776850652589429/29119489864942575155200000000000000000), (79606664601623983972680726271788603637/873584695948277254656000000000000000000)]
    reserve := (11100169707/125000000000) }

theorem mixed_011_026_valid : mixed_011_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_026]
  · intro i; fin_cases i <;> norm_num [mixed_011_026]
  · norm_num [mixed_011_026]
  · norm_num [mixed_011_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_026]

def mixed_011_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, (7344919/20000000), (31117059/100000000), (16079173/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5439061/50000000), 0, 0], ![(780179/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1607917/100000000), 0, (16079173/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (9546409/100000000), (214977/100000000), (11307057/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-151218833152678300452622318104043/32229169918195838612500000000000), (5730351560501/171981600000), (-143975419339764645118255500666649/2302083565585417043750000000000), (5730351560501/171981600000), (-1864437037604026731202954691229043/32229169918195838612500000000000)]
    bernstein := [(25568139385763867237214602475565155511/247520024971744040544000000000000000000), (34667302879850396887185801376693801/304827616960275912000000000000000000), (607312373992507999815549129820113873/5156667186911334178000000000000000000), (445972825902422060839338379743260087/3867500390183500633500000000000000000), (34230139033925980989796546038990117/322291699181958386125000000000000000)]
    reserve := (25824314001/250000000000) }

theorem mixed_011_027_valid : mixed_011_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_027]
  · intro i; fin_cases i <;> norm_num [mixed_011_027]
  · norm_num [mixed_011_027]
  · norm_num [mixed_011_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_027]

def mixed_011_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2962081/10000000), 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (812331/3125000), (577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-229823287470729909864305101/15012318788064000000000000), (56939502/577517), (-1298284279348905909864305101/7506159394032000000000000), (56939502/577517), (-2366745271227081909864305101/15012318788064000000000000)]
    bernstein := [(13138588271588308902191095019/150123187880640000000000000000), (69104768566036171083136612049/600492751522560000000000000000), (900737018833400756137339380437/7205913018270720000000000000000), (1123388895539770296569437309309/9607884024360960000000000000000), (3475613136074926185128324829539/38431536097443840000000000000000)]
    reserve := (87518713511/1000000000000) }

theorem mixed_011_028_valid : mixed_011_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_028]
  · intro i; fin_cases i <;> norm_num [mixed_011_028]
  · norm_num [mixed_011_028]
  · norm_num [mixed_011_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_028]

def mixed_011_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2962081/10000000), 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (812331/3125000), (71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-33001336618930860110602801/1849593204576000000000000), (60597559/569224), (-162240475785418860110602801/924796602288000000000000), (60597559/569224), (-291479614951906860110602801/1849593204576000000000000)]
    bernstein := [(577366111911772817423908059839/4734958603714560000000000000000), (39504985418009181970020858069/263053255761920000000000000000), (570164505889119181559372097557/3551218952785920000000000000000), (10040759707352501223594892749/65763313940480000000000000000), (37320256698406454842364715599/295934912732160000000000000000)]
    reserve := (15242110867/125000000000) }

theorem mixed_011_029_valid : mixed_011_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_029]
  · intro i; fin_cases i <;> norm_num [mixed_011_029]
  · norm_num [mixed_011_029]
  · norm_num [mixed_011_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_029]

def mixed_011_030 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 0]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2962081/10000000), 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (812331/3125000), (560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-59958801475902553849305923/2914217316691200000000000), (64079547/560543), (-259522310030411353849305923/1457108658345600000000000), (64079547/560543), (-459085818584920153849305923/2914217316691200000000000)]
    bernstein := [(72505118810180351826076617277/466274770670592000000000000000), (34406218523311005620756943713/186509908268236800000000000000), (43719098275374436767077075023/223811889921884160000000000000), (5600598990409757589120839401/29841585322917888000000000000), (1921973299653056937048736333/11936634129167155200000000000)]
    reserve := (31099739197/200000000000) }

theorem mixed_011_030_valid : mixed_011_030.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_011_030]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_011_030]
  · intro i; fin_cases i <;> norm_num [mixed_011_030]
  · norm_num [mixed_011_030]
  · norm_num [mixed_011_030, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_011_030, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_011_030, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_011_030, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_011_030]

def mixedTable011 : OwnerTable where
  mode := .mixed
  owners := ![0, 3, 0, 2, 0, 2, 0]
  rows := [mixed_011_000, mixed_011_001, mixed_011_002, mixed_011_003, mixed_011_004, mixed_011_005, mixed_011_006, mixed_011_007, mixed_011_008, mixed_011_009, mixed_011_010, mixed_011_011, mixed_011_012, mixed_011_013, mixed_011_014, mixed_011_015, mixed_011_016, mixed_011_017, mixed_011_018, mixed_011_019, mixed_011_020, mixed_011_021, mixed_011_022, mixed_011_023, mixed_011_024, mixed_011_025, mixed_011_026, mixed_011_027, mixed_011_028, mixed_011_029, mixed_011_030]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_011_000_valid
    · exact mixed_011_001_valid
    · exact mixed_011_002_valid
    · exact mixed_011_003_valid
    · exact mixed_011_004_valid
    · exact mixed_011_005_valid
    · exact mixed_011_006_valid
    · exact mixed_011_007_valid
    · exact mixed_011_008_valid
    · exact mixed_011_009_valid
    · exact mixed_011_010_valid
    · exact mixed_011_011_valid
    · exact mixed_011_012_valid
    · exact mixed_011_013_valid
    · exact mixed_011_014_valid
    · exact mixed_011_015_valid
    · exact mixed_011_016_valid
    · exact mixed_011_017_valid
    · exact mixed_011_018_valid
    · exact mixed_011_019_valid
    · exact mixed_011_020_valid
    · exact mixed_011_021_valid
    · exact mixed_011_022_valid
    · exact mixed_011_023_valid
    · exact mixed_011_024_valid
    · exact mixed_011_025_valid
    · exact mixed_011_026_valid
    · exact mixed_011_027_valid
    · exact mixed_011_028_valid
    · exact mixed_011_029_valid
    · exact mixed_011_030_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
