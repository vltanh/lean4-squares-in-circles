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

def mixed_010_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9323878086264272438164777/457463486508250000000000), (-64079547/560543), (-40650649044724772438164777/228731743254125000000000), (-64079547/560543), (-71977420003185272438164777/457463486508250000000000)]
    bernstein := [(771944384308161177019903367/1873770440737792000000000000), (2045099281096760524528801499/4684426101844480000000000000), (15536936375244992100840585677/35133195763833600000000000000), (12572278001133635972786737987/29277663136528000000000000000), (29171204288533746193542792023/73194157841320000000000000000)]
    reserve := (39854552807/100000000000) }

theorem mixed_010_000_valid : mixed_010_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_000]
  · intro i; fin_cases i <;> norm_num [mixed_010_000]
  · norm_num [mixed_010_000]
  · norm_num [mixed_010_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_000]

def mixed_010_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8195479695018141692827207/464548117886000000000000), (-60597559/569224), (-40655481552973641692827207/232274058943000000000000), (-60597559/569224), (-73115483410929141692827207/464548117886000000000000)]
    bernstein := [(28165181448433940584342241593/74327698861760000000000000000), (59987255907906319759240394787/148655397723520000000000000000), (365240093712578782092801356099/891932386341120000000000000000), (236219105813974844491305697947/594621590894080000000000000000), (436708267205816752992558675273/1189243181788160000000000000000)]
    reserve := (367215279341/1000000000000) }

theorem mixed_010_001_valid : mixed_010_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_001]
  · intro i; fin_cases i <;> norm_num [mixed_010_001]
  · norm_num [mixed_010_001]
  · norm_num [mixed_010_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_001]

def mixed_010_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1423459636141088562438957/94263219891350000000000), (-56939502/577517), (-8132388139765738562438957/47131609945675000000000), (-56939502/577517), (-14841316643390388562438957/94263219891350000000000)]
    bernstein := [(83203201243560805857463083523/241313842921856000000000000000), (22285963806524996156967944413/60328460730464000000000000000), (16997892937923406218361408309/45246345547848000000000000000), (1372467533604261648733468593/3770528795654000000000000000), (315533175520850489662751883/942632198913500000000000000)]
    reserve := (334736258621/1000000000000) }

theorem mixed_010_002_valid : mixed_010_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_002]
  · intro i; fin_cases i <;> norm_num [mixed_010_002]
  · norm_num [mixed_010_002]
  · norm_num [mixed_010_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_002]

def mixed_010_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9752571069990143856572169/764369130194800000000000), (-106220235/1170754), (-65072167873284343856572169/382184565097400000000000), (-106220235/1170754), (-120391764676578543856572169/764369130194800000000000)]
    bernstein := [(2366256876064270440066060111/7643691301948000000000000000), (10218717636968408101363339707/30574765207792000000000000000), (125031836454212323239764602177/366897182493504000000000000000), (161257140290528105389415666383/489196243324672000000000000000), (589205041140438005306430396871/1956784973298688000000000000000)]
    reserve := (150554365753/500000000000) }

theorem mixed_010_003_valid : mixed_010_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_003]
  · intro i; fin_cases i <;> norm_num [mixed_010_003]
  · norm_num [mixed_010_003]
  · norm_num [mixed_010_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_003]

def mixed_010_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8217006815756847909129793/774005730506800000000000), (-49115626/592757), (-65088061666314447909129793/387002865253400000000000), (-49115626/592757), (-121959116516872047909129793/774005730506800000000000)]
    bernstein := [(541462199981933644775104771087/1981454670097408000000000000000), (59039260927319991174284088237/198145467009740800000000000000), (18118853247657556500861091973/59443640102922240000000000000), (582869908921379928159691749/1981454670097408000000000000), (52769526414835754261489823/198145467009740800000000000)]
    reserve := (10652684053/40000000000) }

theorem mixed_010_004_valid : mixed_010_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_004]
  · intro i; fin_cases i <;> norm_num [mixed_010_004]
  · norm_num [mixed_010_004]
  · norm_num [mixed_010_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_004]

def mixed_010_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16975854023440140909521343/1957398529634000000000000), (-44963763/599614), (-162767147713783140909521343/978699264817000000000000), (-44963763/599614), (-308558441404126140909521343/1957398529634000000000000)]
    bernstein := [(118189125096141277148331873/501094023586304000000000000), (1305883121322862166945181561/5010940235863040000000000000), (311992144757981055774654467/1165334938572800000000000000), (129055832776668462154991188473/501094023586304000000000000000), (1154168652199459017370060282977/5010940235863040000000000000000)]
    reserve := (230329758063/1000000000000) }

theorem mixed_010_005_valid : mixed_010_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_005]
  · intro i; fin_cases i <;> norm_num [mixed_010_005]
  · norm_num [mixed_010_005]
  · norm_num [mixed_010_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_005]

def mixed_010_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1713001392265053495332851/247241475078000000000000), (-847162/12623), (-20352687765926803495332851/123620737539000000000000), (-847162/12623), (-12997458046529517831777617/82413825026000000000000)]
    bernstein := [(9607504628175708190365201953/48687552015360000000000000000), (17574063151746684038204791021/79117272024960000000000000000), (130944449994834311994497791/570557250180000000000000000), (45276098750240676060214611/206034562565000000000000000), (573823949222554560672937/2971652344687500000000000)]
    reserve := (48274821771/250000000000) }

theorem mixed_010_006_valid : mixed_010_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_006]
  · intro i; fin_cases i <;> norm_num [mixed_010_006]
  · norm_num [mixed_010_006]
  · norm_num [mixed_010_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_006]

def mixed_010_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2149684459102271992679741/399296712399400000000000), (-72452831/1223174), (-32576645045177971992679741/199648356199700000000000), (-72452831/1223174), (-63003605631253671992679741/399296712399400000000000)]
    bernstein := [(9833958343755183237123771/62390111312406250000000000), (182147981160652667698816969/998241780998500000000000000), (2276921797765271451795085037/11978901371982000000000000000), (23090058397995660877719167837/127774947967808000000000000000), (157993462004359315833255593059/1022199583742464000000000000000)]
    reserve := (154562244513/1000000000000) }

theorem mixed_010_007_valid : mixed_010_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_007]
  · intro i; fin_cases i <;> norm_num [mixed_010_007]
  · norm_num [mixed_010_007]
  · norm_num [mixed_010_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_007]

def mixed_010_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(39545593/50000000), 0, (4742731/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(616623/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16258103025468383514700481/4025846473026000000000000), (-31663876/616623), (-108634821682229461171566827/670974412171000000000000), (-31663876/616623), (-635550827067908383514700481/4025846473026000000000000)]
    bernstein := [(1202427934758944278442937364319/10306166970946560000000000000000), (729497452730180054676562508251/5153083485473280000000000000000), (384886560423589242899146355479/2576541742736640000000000000000), (180807938560314887982240185491/1288270871368320000000000000000), (73843295001210177277388837839/644135435684160000000000000000)]
    reserve := (1791240507/15625000000) }

theorem mixed_010_008_valid : mixed_010_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_008]
  · intro i; fin_cases i <;> norm_num [mixed_010_008]
  · norm_num [mixed_010_008]
  · norm_num [mixed_010_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_008]

def mixed_010_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(37567091/50000000), 0, (96288913/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(31049/5000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1172815546937745451240173/405429272476000000000000), (-53979451/1241960), (-32605666802288045451240173/202714636238000000000000), (-53979451/1241960), (-64038518057638345451240173/405429272476000000000000)]
    bernstein := [(4826313681731068571092620387/64868683596160000000000000000), (2577432852797636702171386609/25947473438464000000000000000), (3341792400699214190779687921/31136968126156800000000000000), (81853068445632448822073413/830319150030848000000000000), (79749310017244897383783/1088943147581440000000000)]
    reserve := (36617756489/500000000000) }

theorem mixed_010_009_valid : mixed_010_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_009]
  · intro i; fin_cases i <;> norm_num [mixed_010_009]
  · norm_num [mixed_010_009]
  · norm_num [mixed_010_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_009]

def mixed_010_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(35484493/50000000), 0, (48750193/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(4997/800000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-63513499788067795265627/32624723414000000000000), (-22218793/624625), (-137356829492157673435033/858545353000000000000), (-22218793/624625), (-5156046020913923795265627/32624723414000000000000)]
    bernstein := [(164189282602699400109037/5345234684149760000000000), (1859880525364616385294769/33407716775936000000000000), (39969091075665330605601251/626394689548800000000000000), (14431766206684286931905513/260997787312000000000000000), (9865545121022244495338973/326247234140000000000000000)]
    reserve := (30239475123/1000000000000) }

theorem mixed_010_010_valid : mixed_010_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_010]
  · intro i; fin_cases i <;> norm_num [mixed_010_010]
  · norm_num [mixed_010_010]
  · norm_num [mixed_010_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_010]

def mixed_010_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(5454841/100000000), (4958679/50000000), (4958679/50000000), (579149/5000000), (579149/5000000), (11583399/100000000), (9990271/25000000)]
    cone := fun i => (![![(23889549/100000000), 0, (33898989/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(250769/100000000), (772469/25000000), (1/100000000), (3853013/100000000), (1/100000000), (2069589/50000000), (10513017/100000000)]
    alternative := .zero
    polynomial := [(-241062774588880485290596841663238962007708047/541309440804920479383333018090300000000000000), (-746717070769388283/67377836056000000), (-17268036059892922906611736463447015236101708047/270654720402460239691666509045150000000000000), (-746717070769388283/67377836056000000), (-34295009345196965327932876085230791510195708047/541309440804920479383333018090300000000000000)]
    bernstein := [(160540402434407316779211535470245251155757212553/5413094408049204793833330180903000000000000000000), (858497234790830521168941791909035406064614112959/21652377632196819175333320723612000000000000000000), (11158291877712116834566914555192366000497447079631/259828531586361830103999848683344000000000000000000), (13719183307101097774929350434225411008272999457931/346438042115149106805333131577792000000000000000000), (41084246900728969051171353953695912981606855574593/1385752168460596427221332526311168000000000000000000)]
    reserve := (2964761509/100000000000) }

theorem mixed_010_011_valid : mixed_010_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_011]
  · intro i; fin_cases i <;> norm_num [mixed_010_011]
  · norm_num [mixed_010_011]
  · norm_num [mixed_010_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_011]

def mixed_010_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(2512079/25000000), (17612549/100000000), (17612549/100000000), (5204159/25000000), (5204159/25000000), (741547/25000000), (5063563/50000000)]
    cone := fun i => (![![(252193/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1115653/12500000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(63769/100000000), (5442697/100000000), (1/100000000), (3445017/50000000), (1/100000000), (4249319/100000000), (1333213/50000000)]
    alternative := .zero
    polynomial := [(-306816467436196144053687953710855028792987/14725707733262413215317684235450000000000000), (-765686170324959569/377255809775000000), (-120394492520529210472792246932766110643292987/7362853866631206607658842117725000000000000), (-765686170324959569/377255809775000000), (-240482168573622224801530805911821366257792987/14725707733262413215317684235450000000000000)]
    bernstein := [(1498407221033807464689553645613537990755194022453/37697811797151777831213271642752000000000000000000), (18564215707537711707938591377887539075595590357/438346648804090439897828740032000000000000000000), (1222542300853236680984931891319524169145668341751/28273358847863833373409953732064000000000000000000), (199928917800903982015703762657487121243294807039/4712226474643972228901658955344000000000000000000), (94051841437101607327474095753578634781469897413/2356113237321986114450829477672000000000000000000)]
    reserve := (7949571339/200000000000) }

theorem mixed_010_012_valid : mixed_010_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_012]
  · intro i; fin_cases i <;> norm_num [mixed_010_012]
  · norm_num [mixed_010_012]
  · norm_num [mixed_010_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_012]

def mixed_010_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(5122123/50000000), (695319/4000000), (695319/4000000), (833629/4000000), (833629/4000000), (3035253/100000000), (10273099/100000000)]
    cone := fun i => (![![(3847/500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (556421/6250000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(6483/10000000), (531613/10000000), (1/100000000), (3428691/50000000), (1/100000000), (4265963/100000000), (2706737/100000000)]
    alternative := .zero
    polynomial := [(178219512288831219128048045877771678849/12128597482842986729085062360800000000000), (-16982643953449019/13785788316000000), (-301120089307895245149577707371806049729053/18192896224264480093627593541200000000000), (-16982643953449019/13785788316000000), (-602774837152656983956539558881245414494653/36385792448528960187255187082400000000000)]
    bernstein := [(203530800855024315785700651454302995181782947/5821726791764633629960829933184000000000000000), (437793107195757618514025529630431996170681747/11643453583529267259921659866368000000000000000), (384319431449728318607256543239791546904240063/9980103071596514794218565599744000000000000000), (1755579818242133110515747339953476414046938147/46573814334117069039686639465472000000000000000), (1091678075499660375004420761181859798292285249/31049209556078046026457759643648000000000000000)]
    reserve := (17480277599/500000000000) }

theorem mixed_010_013_valid : mixed_010_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_013]
  · intro i; fin_cases i <;> norm_num [mixed_010_013]
  · norm_num [mixed_010_013]
  · norm_num [mixed_010_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_013]

def mixed_010_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(10410413/100000000), (17149527/100000000), (17149527/100000000), (20885541/100000000), (20885541/100000000), (388223/12500000), (10413667/100000000)]
    cone := fun i => (![![(260301/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4444939/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(32889/50000000), (1295101/25000000), (1/100000000), (6828497/100000000), (1/100000000), (1071643/25000000), (1372929/50000000)]
    alternative := .zero
    polynomial := [(33078087356353205326398916372026654799781/1097268807579768055615317420900000000000000), (-2331083519969144873/5679276905200000000), (-3065765481517463119534782326017691658650073/182878134596628009269219570150000000000000), (-2331083519969144873/5679276905200000000), (-18427670976461131922535092872478176606700219/1097268807579768055615317420900000000000000)]
    bernstein := [(28024125995985506160356126418566033335393986327/936336049134735407458404199168000000000000000000), (114483637167891634647468927143649996615645637/3511260184255257777969015746880000000000000000), (58866747883037552949531590916680353215999527/1755630092127628888984507873440000000000000000), (3778205695221057387871863139405943834023/115501979745238742696349202200000000000000), (33078087356353205326398916372026654799781/1097268807579768055615317420900000000000000)]
    reserve := (5985912007/200000000000) }

theorem mixed_010_014_valid : mixed_010_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_014]
  · intro i; fin_cases i <;> norm_num [mixed_010_014]
  · norm_num [mixed_010_014]
  · norm_num [mixed_010_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_014]

def mixed_010_015 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(10589163/100000000), (4229633/25000000), (4229633/25000000), (2055167/10000000), (2055167/10000000), (207523/6250000), (11150063/100000000)]
    cone := fun i => (![![0, 0, (69677/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8615651/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(7043/10000000), (201731/4000000), (1/100000000), (6726263/100000000), (1/100000000), (4265259/100000000), (1469833/50000000)]
    alternative := .zero
    polynomial := [(4656916266163572319169111900341568188243/199708394930840927141879978710000000000000), (905281250765209887/887994645625000000), (-1791218663064274431313678304359512406856757/99854197465420463570939989355000000000000), (905281250765209887/887994645625000000), (-3587094242394712434946525720619366381901757/199708394930840927141879978710000000000000)]
    bernstein := [(4656916266163572319169111900341568188243/199708394930840927141879978710000000000000), (5929392024055506176234677365007312685143/199708394930840927141879978710000000000000), (10925915563427812576175829092690387355649881/319533431889345483427007965936000000000000000), (11769003476436615727128680532047236023948943/319533431889345483427007965936000000000000000), (19224514430994583317470819342354439906614715843/511253491022952773483212745497600000000000000000)]
    reserve := (5829645103/250000000000) }

theorem mixed_010_015_valid : mixed_010_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_015]
  · intro i; fin_cases i <;> norm_num [mixed_010_015]
  · norm_num [mixed_010_015]
  · norm_num [mixed_010_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_015]

def mixed_010_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(1069423/10000000), (416119/2500000), (416119/2500000), (2480041/12500000), (2480041/12500000), (3715577/100000000), (6310009/50000000)]
    cone := fun i => (![![0, 0, (236293/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (64499/800000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1991/2500000), (4884151/100000000), (1/100000000), (654381/10000000), (1/100000000), (168351/4000000), (3324163/100000000)]
    alternative := .zero
    polynomial := [(-36087371047218652503729186340106537/3020167495548060759238837500000000000), (10281555486165729567/4862172320500000000), (-30652775164489710445077059957006925287/1510083747774030379619418750000000000), (10281555486165729567/4862172320500000000), (-61269462957932202237650390727673744037/3020167495548060759238837500000000000)]
    bernstein := [(12850260498347285665428451049547690565739/454801693447237384920672000000000000000000), (15095750546015185253059246442324709286907/429534932700168641313968000000000000000000), (33076168281886517403032376361448594497927/828388798778896665391224000000000000000000), (4575266748825559788399802451619154688507/107383733175042160328492000000000000000000), (1227168166376278655128950203821823212139/28425105840452336557542000000000000000000)]
    reserve := (28254645229/1000000000000) }

theorem mixed_010_016_valid : mixed_010_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_016]
  · intro i; fin_cases i <;> norm_num [mixed_010_016]
  · norm_num [mixed_010_016]
  · norm_num [mixed_010_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_016]

def mixed_010_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(10632057/100000000), (8145977/50000000), (8145977/50000000), (19151007/100000000), (19151007/100000000), (208803/5000000), (14305961/100000000)]
    cone := fun i => (![![0, 0, (1781287/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (7487473/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(90083/100000000), (4685913/100000000), (1/100000000), (3176613/50000000), (1/100000000), (260493/6250000), (753139/20000000)]
    alternative := .zero
    polynomial := [(-3459600477901490546696683081385043809311/40597338212745739264437787612500000000000), (49030942419515386801/14070703359300000000), (-467652470774681013200843922180326785371811/20298669106372869632218893806250000000000), (49030942419515386801/14070703359300000000), (-931845341071460535854991161279268526934311/40597338212745739264437787612500000000000)]
    bernstein := [(68655737059198728554493599060732975156118963/2165191371346439427436682006000000000000000000), (15424106843714254767712537961308305624179699/393671158426625350443033092000000000000000000), (3450727230859581370462116914980282079999100803/77946889368471819387720552216000000000000000000), (221911029596076860051363410489655640703507873/4724053901119504205316397104000000000000000000), (289047197668103254375055126136032259119353177/6113481519095828971585925664000000000000000000)]
    reserve := (3963606749/125000000000) }

theorem mixed_010_017_valid : mixed_010_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_017]
  · intro i; fin_cases i <;> norm_num [mixed_010_017]
  · norm_num [mixed_010_017]
  · norm_num [mixed_010_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_017]

def mixed_010_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(11383487/100000000), (8682411/50000000), (8682411/50000000), (10127361/50000000), (10127361/50000000), (3011409/100000000), (5183009/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8621657/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(603719/100000000), (609313/12500000), (1/100000000), (6741353/100000000), (1/100000000), (4157/100000), (1363787/50000000)]
    alternative := .zero
    polynomial := [(8968407809630310357425197633519206334641/702941092678222685994472718450000000000000), (149365308952229/243725200000000), (-800071748620162747460868420651184169165359/351470546339111342997236359225000000000000), (149365308952229/243725200000000), (-1609111905049955805279162038935887544665359/702941092678222685994472718450000000000000)]
    bernstein := [(82964155480812544123922875324078405464995726721/1799529197256250076145850159232000000000000000000), (694269038124062838529523534162431193823748297/14512332235937500614079436768000000000000000000), (16649854985705843617300528497973688418921469607/337411724485546889277346904856000000000000000000), (45913928256187507817856205284474415820321133/907020764746093788379964798000000000000000000), (363161146153650937967990045550310411439922841/7029410926782226859944727184500000000000000000)]
    reserve := (23051628061/500000000000) }

theorem mixed_010_018_valid : mixed_010_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_018]
  · intro i; fin_cases i <;> norm_num [mixed_010_018]
  · norm_num [mixed_010_018]
  · norm_num [mixed_010_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_018]

def mixed_010_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(45518/390625), (17440957/100000000), (17440957/100000000), (10040717/50000000), (10040717/50000000), (1487827/50000000), (5163479/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (855289/10000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(764859/100000000), (149713/3125000), (1/100000000), (672077/10000000), (1/100000000), (82393/2000000), (2715583/100000000)]
    alternative := .zero
    polynomial := [(22828630174899239094082526767834117371347/3443842811201827033753942024200000000000000), (2360794892979/3742825000000), (-3286925826573129708436173375165609092628653/1721921405600913516876971012100000000000000), (2360794892979/3742825000000), (-2198893427773719551988809759033017434209551/1147947603733942344584647341400000000000000)]
    bernstein := [(1758237804922840101219443416861675498325110747/34438428112018270337539420242000000000000000000), (1451401270025142713241007971769141171262989807/27550742489614616270031536193600000000000000000), (3578273532470385601923613656481859345717708389/66121781975075079048075686864640000000000000000), (15017489452784464446522284584107301393479107/271268849128513144812618202521600000000000000), (2448408387826826744057416829376474472227511/43403015860562103170018912403456000000000000)]
    reserve := (51054531269/1000000000000) }

theorem mixed_010_019_valid : mixed_010_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_019]
  · intro i; fin_cases i <;> norm_num [mixed_010_019]
  · norm_num [mixed_010_019]
  · norm_num [mixed_010_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_019]

def mixed_010_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(93157/781250), (8755301/50000000), (8755301/50000000), (4979249/25000000), (4979249/25000000), (2939447/100000000), (514063/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (339551/4000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(18561/2000000), (1175051/25000000), (1/100000000), (3350531/50000000), (1/100000000), (4083801/100000000), (67549/2500000)]
    alternative := .zero
    polynomial := [(-13341290504858353726034180005117515269/335972686831608099363590805150000000000000), (9545191813121/14688137500000), (-93584307130413080152447227585461463638423/55995447805268016560598467525000000000000), (9545191813121/14688137500000), (-561492501491973622560957331332763664315269/335972686831608099363590805150000000000000)]
    bernstein := [(35393704209549391104359787748157445515397/632709942649318057468169166848000000000000), (39563364563302466734533694171118414706504989/688072062631133387496633968947200000000000000), (506531559711888585007814296654317005605403171/8600900782889167343707924611840000000000000000), (1292738583530113861469840988965415877097961577/21502251957222918359269811529600000000000000000), (3288886387614981562315175229374096890237486411/53755629893057295898174528824000000000000000000)]
    reserve := (27969928891/500000000000) }

theorem mixed_010_020_valid : mixed_010_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_020]
  · intro i; fin_cases i <;> norm_num [mixed_010_020]
  · norm_num [mixed_010_020]
  · norm_num [mixed_010_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_020]

def mixed_010_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(12196867/100000000), (17574777/100000000), (17574777/100000000), (19762031/100000000), (19762031/100000000), (1451159/50000000), (1598/15625)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (263433/3125000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092857/100000000), (287689/6250000), (1/100000000), (668247/10000000), (1/100000000), (4049479/100000000), (671563/25000000)]
    alternative := .zero
    polynomial := [(-417283260314665052479600817892815757572747/57135959417260416672647614058700000000000000), (308509311729259/460302400000000), (-43066580354070745197434807364268249056572747/28567979708630208336323807029350000000000000), (308509311729259/460302400000000), (-85715877447826825342390013910643682355572747/57135959417260416672647614058700000000000000)]
    bernstein := [(555955359023889441904768152483781116378509059093/9141753506761666667623618249392000000000000000000), (1139674903759378417839684827303517471008348795117/18283507013523333335247236498784000000000000000000), (6988540066379322242359115758772862328965642894319/109701042081140000011483418992704000000000000000000), (4748558483892996311709872423857438714281761314237/73134028054093333340988945995136000000000000000000), (9654372800149823028374334964634761649057608284853/146268056108186666681977891990272000000000000000000)]
    reserve := (30407479189/500000000000) }

theorem mixed_010_021_valid : mixed_010_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_021]
  · intro i; fin_cases i <;> norm_num [mixed_010_021]
  · norm_num [mixed_010_021]
  · norm_num [mixed_010_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_021]

def mixed_010_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(6235029/50000000), (881723/5000000), (881723/5000000), (392339/2000000), (392339/2000000), (1431927/50000000), (2540817/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2094137/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(157353/12500000), (2249841/50000000), (1/100000000), (6665193/100000000), (1/100000000), (803337/20000000), (2668063/100000000)]
    alternative := .zero
    polynomial := [(-5704412314757899949072549108357409012499/374627509859227109436566957034000000000000), (12973570298343/18748675000000), (-260352673113033192854650198991804083182499/187313754929613554718283478517000000000000), (12973570298343/18748675000000), (-515000933911308485760227848875250757352499/374627509859227109436566957034000000000000)]
    bernstein := [(63029482627272156083469045855405212881988166701/959046425239621400157611410007040000000000000000), (38928544829583361165874115504005653639829149/579134314758225483186963411840000000000000000), (770789771744391192919572894341792879288937143/11238825295776813283097008711020000000000000000), (315866738346501884629168139820373715342513/4524486834048636587398151655000000000000000), (4150566611642521491716068246951984262477669/58535548415504235849463587036562500000000000)]
    reserve := (32860496097/500000000000) }

theorem mixed_010_022_valid : mixed_010_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_022]
  · intro i; fin_cases i <;> norm_num [mixed_010_022]
  · norm_num [mixed_010_022]
  · norm_num [mixed_010_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_022]

def mixed_010_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(12743011/100000000), (3538119/20000000), (3538119/20000000), (19481989/100000000), (19481989/100000000), (2823681/100000000), (10088141/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4164577/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1425483/100000000), (4390621/100000000), (1/100000000), (3324699/50000000), (1/100000000), (3985393/100000000), (1323521/50000000)]
    alternative := .zero
    polynomial := [(-29128863662905564498896068573518910797322441/1219550549412220795710644183946900000000000000), (314017854132667/439062100000000), (-794783792300336494742512612727378989148822441/609775274706110397855322091973450000000000000), (314017854132667/439062100000000), (-1560438720937767424986129156881239067500322441/1219550549412220795710644183946900000000000000)]
    bernstein := [(13470998733050475529956893637384240256480507471/190554773345659499329788153741703125000000000000), (11583415197935933472619543107652464186522640937/160467177554239578382979497887750000000000000000), (384443323770219310097169001345211914633563153679/5226645211766660553045617931201000000000000000000), (37472198314979467422138534851137047821555829109/500970700657138195927350627552000000000000000000), (5780960680158251566676104567653412812188957043839/76147546499885005780957295387904000000000000000000)]
    reserve := (70693578001/1000000000000) }

theorem mixed_010_023_valid : mixed_010_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_023]
  · intro i; fin_cases i <;> norm_num [mixed_010_023]
  · norm_num [mixed_010_023]
  · norm_num [mixed_010_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_023]

def mixed_010_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![(3253813/25000000), (554503/3125000), (554503/3125000), (19357223/100000000), (19357223/100000000), (1390729/50000000), (2500163/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4143941/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(398091/25000000), (427631/10000000), (1/100000000), (331761/5000000), (1/100000000), (3955557/100000000), (2622881/100000000)]
    alternative := .zero
    polynomial := [(-72404979373997684837736038579813372201473/2170197912682360606705479345100000000000000), (19779728578777/26726937500000), (-4033364573251706358508034433678676558604419/3255296869023540910058219017650000000000000), (19779728578777/26726937500000), (-7849514208381419662502860751617913000604419/6510593738047081820116438035300000000000000)]
    bernstein := [(10266741900543100882530786678297849032586279367/135505040401630320808927490816000000000000000000), (1046997841815479528999532659656338001176793583/13550504040163032080892749081600000000000000000), (39326573653814757737619249673610777998619496119/500013599082015883784942441111040000000000000000), (1332022119987087481797433601387982531969104213/16667119969400529459498081370368000000000000000), (135118602763654787237263589204757044502122909/1666711996940052945949808137036800000000000000)]
    reserve := (18941623629/250000000000) }

theorem mixed_010_024_valid : mixed_010_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_024]
  · intro i; fin_cases i <;> norm_num [mixed_010_024]
  · norm_num [mixed_010_024]
  · norm_num [mixed_010_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_024]

def mixed_010_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, (649727/2000000), (649727/2000000), (350273/1000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (12050819/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(350273/20000000), 0, (350273/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7287097/100000000), (1/100000000), (6035661/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3107439164744528898920657/21991223583058500000000000), (7829742476413/7287097000000), (-10842305918531070963583157/10995611791529250000000000), (7829742476413/7287097000000), (-18577172672317613028245657/21991223583058500000000000)]
    bernstein := [(445725436127687093775405127/5629753237262976000000000000), (523794241256098349693552789/6255281374736640000000000000), (149043824041188318819373900477/1688925971178892800000000000000), (57991586312342764985057761757/625528137473664000000000000000), (5467526010975728964346835025463/56297532372629760000000000000000)]
    reserve := (79173174621/1000000000000) }

theorem mixed_010_025_valid : mixed_010_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_025]
  · intro i; fin_cases i <;> norm_num [mixed_010_025]
  · norm_num [mixed_010_025]
  · norm_num [mixed_010_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_025]

def mixed_010_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, (16363753/50000000), (16363753/50000000), (34544989/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6334531/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1727249/100000000), 0, (34544989/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1425263/20000000), (1/100000000), (12024079/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8553040755699536722639333/52461657880950000000000000), (2115442870507/1817937500000), (-27248608118084697112819333/26230828940475000000000000), (2115442870507/1817937500000), (-45944175480469857502999333/52461657880950000000000000)]
    bernstein := [(13108120197950196591267176547947/134301844175232000000000000000000), (3441436427729123619824500043731/33575461043808000000000000000000), (93211485315596664487517939041/868330889064000000000000000000), (235329958371249365900972480399/2098466315238000000000000000000), (61324326842603257352732924627/524616578809500000000000000000)]
    reserve := (48800968737/500000000000) }

theorem mixed_010_026_valid : mixed_010_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_026]
  · intro i; fin_cases i <;> norm_num [mixed_010_026]
  · norm_num [mixed_010_026]
  · norm_num [mixed_010_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_026]

def mixed_010_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, (6593593/20000000), (6593593/20000000), (34064071/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (26521543/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(425801/25000000), 0, (34064071/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (868697/12500000), (1/100000000), (2994583/25000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1172474406728839142329360429/6243324644042400000000000000), (174872260273999/138991520000000), (-3427147551883646939770735429/3121662322021200000000000000), (174872260273999/138991520000000), (-5681820697038454737212110429/6243324644042400000000000000)]
    bernstein := [(7332151729366878512208740993051/62433246440424000000000000000000), (30641029476298173398572478861921/249732985761696000000000000000000), (383298777418544552612344599495173/2996795829140352000000000000000000), (531685997635422050213075337332461/3995727772187136000000000000000000), (2208482106167041572268557895794131/15982911088748544000000000000000000)]
    reserve := (117439860129/1000000000000) }

theorem mixed_010_027_valid : mixed_010_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_027]
  · intro i; fin_cases i <;> norm_num [mixed_010_027]
  · norm_num [mixed_010_027]
  · norm_num [mixed_010_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_027]

def mixed_010_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (41631471/50000000), 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (20350399/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3587082107763798869/4070079800000000000), (83262942/20350399), (-8073476617763798869/2035039900000000000), (83262942/20350399), (-12559871127763798869/4070079800000000000)]
    bernstein := [(1410594187349950607507291/10419404288000000000000000), (782970937210383262458449/5209702144000000000000000), (1289393071544137250690633/7814553216000000000000000), (233793012227942388266729/1302425536000000000000000), (126212035587690384210731/651212768000000000000000)]
    reserve := (1692268277/12500000000) }

theorem mixed_010_028_valid : mixed_010_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_028]
  · intro i; fin_cases i <;> norm_num [mixed_010_028]
  · norm_num [mixed_010_028]
  · norm_num [mixed_010_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_028]

def mixed_010_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (85870743/100000000), 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (19590439/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-15187964623384429949/15672351200000000000), (85870743/19590439), (-32577730683384429949/7836175600000000000), (85870743/19590439), (-49967496743384429949/15672351200000000000)]
    bernstein := [(491174581772955537851651/2507576192000000000000000), (212375570386690762474719/1003030476800000000000000), (24881778954383083676659/109421506560000000000000), (38974676531101527083863/160484876288000000000000), (16569617307944372801779/64193950515200000000000)]
    reserve := (7835049373/40000000000) }

theorem mixed_010_029_valid : mixed_010_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_010_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_010_029]
  · intro i; fin_cases i <;> norm_num [mixed_010_029]
  · norm_num [mixed_010_029]
  · norm_num [mixed_010_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_010_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_010_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_010_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_010_029]

def mixedTable010 : OwnerTable where
  mode := .mixed
  owners := ![0, 2, 0, 2, 0, 2, 3]
  rows := [mixed_010_000, mixed_010_001, mixed_010_002, mixed_010_003, mixed_010_004, mixed_010_005, mixed_010_006, mixed_010_007, mixed_010_008, mixed_010_009, mixed_010_010, mixed_010_011, mixed_010_012, mixed_010_013, mixed_010_014, mixed_010_015, mixed_010_016, mixed_010_017, mixed_010_018, mixed_010_019, mixed_010_020, mixed_010_021, mixed_010_022, mixed_010_023, mixed_010_024, mixed_010_025, mixed_010_026, mixed_010_027, mixed_010_028, mixed_010_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_010_000_valid
    · exact mixed_010_001_valid
    · exact mixed_010_002_valid
    · exact mixed_010_003_valid
    · exact mixed_010_004_valid
    · exact mixed_010_005_valid
    · exact mixed_010_006_valid
    · exact mixed_010_007_valid
    · exact mixed_010_008_valid
    · exact mixed_010_009_valid
    · exact mixed_010_010_valid
    · exact mixed_010_011_valid
    · exact mixed_010_012_valid
    · exact mixed_010_013_valid
    · exact mixed_010_014_valid
    · exact mixed_010_015_valid
    · exact mixed_010_016_valid
    · exact mixed_010_017_valid
    · exact mixed_010_018_valid
    · exact mixed_010_019_valid
    · exact mixed_010_020_valid
    · exact mixed_010_021_valid
    · exact mixed_010_022_valid
    · exact mixed_010_023_valid
    · exact mixed_010_024_valid
    · exact mixed_010_025_valid
    · exact mixed_010_026_valid
    · exact mixed_010_027_valid
    · exact mixed_010_028_valid
    · exact mixed_010_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
