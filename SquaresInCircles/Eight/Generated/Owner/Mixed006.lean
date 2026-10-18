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

def mixed_006_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9323878086264272438164777/457463486508250000000000), (-64079547/560543), (-40650649044724772438164777/228731743254125000000000), (-64079547/560543), (-71977420003185272438164777/457463486508250000000000)]
    bernstein := [(771944384308161177019903367/1873770440737792000000000000), (2045099281096760524528801499/4684426101844480000000000000), (15536936375244992100840585677/35133195763833600000000000000), (12572278001133635972786737987/29277663136528000000000000000), (29171204288533746193542792023/73194157841320000000000000000)]
    reserve := (39854552807/100000000000) }

theorem mixed_006_000_valid : mixed_006_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_000]
  · intro i; fin_cases i <;> norm_num [mixed_006_000]
  · norm_num [mixed_006_000]
  · norm_num [mixed_006_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_000]

def mixed_006_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8195479695018141692827207/464548117886000000000000), (-60597559/569224), (-40655481552973641692827207/232274058943000000000000), (-60597559/569224), (-73115483410929141692827207/464548117886000000000000)]
    bernstein := [(28165181448433940584342241593/74327698861760000000000000000), (59987255907906319759240394787/148655397723520000000000000000), (365240093712578782092801356099/891932386341120000000000000000), (236219105813974844491305697947/594621590894080000000000000000), (436708267205816752992558675273/1189243181788160000000000000000)]
    reserve := (367215279341/1000000000000) }

theorem mixed_006_001_valid : mixed_006_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_001]
  · intro i; fin_cases i <;> norm_num [mixed_006_001]
  · norm_num [mixed_006_001]
  · norm_num [mixed_006_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_001]

def mixed_006_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1423459636141088562438957/94263219891350000000000), (-56939502/577517), (-8132388139765738562438957/47131609945675000000000), (-56939502/577517), (-14841316643390388562438957/94263219891350000000000)]
    bernstein := [(83203201243560805857463083523/241313842921856000000000000000), (22285963806524996156967944413/60328460730464000000000000000), (16997892937923406218361408309/45246345547848000000000000000), (1372467533604261648733468593/3770528795654000000000000000), (315533175520850489662751883/942632198913500000000000000)]
    reserve := (334736258621/1000000000000) }

theorem mixed_006_002_valid : mixed_006_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_002]
  · intro i; fin_cases i <;> norm_num [mixed_006_002]
  · norm_num [mixed_006_002]
  · norm_num [mixed_006_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_002]

def mixed_006_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9752571069990143856572169/764369130194800000000000), (-106220235/1170754), (-65072167873284343856572169/382184565097400000000000), (-106220235/1170754), (-120391764676578543856572169/764369130194800000000000)]
    bernstein := [(2366256876064270440066060111/7643691301948000000000000000), (10218717636968408101363339707/30574765207792000000000000000), (125031836454212323239764602177/366897182493504000000000000000), (161257140290528105389415666383/489196243324672000000000000000), (589205041140438005306430396871/1956784973298688000000000000000)]
    reserve := (150554365753/500000000000) }

theorem mixed_006_003_valid : mixed_006_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_003]
  · intro i; fin_cases i <;> norm_num [mixed_006_003]
  · norm_num [mixed_006_003]
  · norm_num [mixed_006_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_003]

def mixed_006_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8217006815756847909129793/774005730506800000000000), (-49115626/592757), (-65088061666314447909129793/387002865253400000000000), (-49115626/592757), (-121959116516872047909129793/774005730506800000000000)]
    bernstein := [(541462199981933644775104771087/1981454670097408000000000000000), (59039260927319991174284088237/198145467009740800000000000000), (18118853247657556500861091973/59443640102922240000000000000), (582869908921379928159691749/1981454670097408000000000000), (52769526414835754261489823/198145467009740800000000000)]
    reserve := (10652684053/40000000000) }

theorem mixed_006_004_valid : mixed_006_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_004]
  · intro i; fin_cases i <;> norm_num [mixed_006_004]
  · norm_num [mixed_006_004]
  · norm_num [mixed_006_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_004]

def mixed_006_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16975854023440140909521343/1957398529634000000000000), (-44963763/599614), (-162767147713783140909521343/978699264817000000000000), (-44963763/599614), (-308558441404126140909521343/1957398529634000000000000)]
    bernstein := [(118189125096141277148331873/501094023586304000000000000), (1305883121322862166945181561/5010940235863040000000000000), (311992144757981055774654467/1165334938572800000000000000), (129055832776668462154991188473/501094023586304000000000000000), (1154168652199459017370060282977/5010940235863040000000000000000)]
    reserve := (230329758063/1000000000000) }

theorem mixed_006_005_valid : mixed_006_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_005]
  · intro i; fin_cases i <;> norm_num [mixed_006_005]
  · norm_num [mixed_006_005]
  · norm_num [mixed_006_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_005]

def mixed_006_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1713001392265053495332851/247241475078000000000000), (-847162/12623), (-20352687765926803495332851/123620737539000000000000), (-847162/12623), (-12997458046529517831777617/82413825026000000000000)]
    bernstein := [(9607504628175708190365201953/48687552015360000000000000000), (17574063151746684038204791021/79117272024960000000000000000), (130944449994834311994497791/570557250180000000000000000), (45276098750240676060214611/206034562565000000000000000), (573823949222554560672937/2971652344687500000000000)]
    reserve := (48274821771/250000000000) }

theorem mixed_006_006_valid : mixed_006_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_006]
  · intro i; fin_cases i <;> norm_num [mixed_006_006]
  · norm_num [mixed_006_006]
  · norm_num [mixed_006_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_006]

def mixed_006_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2149684459102271992679741/399296712399400000000000), (-72452831/1223174), (-32576645045177971992679741/199648356199700000000000), (-72452831/1223174), (-63003605631253671992679741/399296712399400000000000)]
    bernstein := [(9833958343755183237123771/62390111312406250000000000), (182147981160652667698816969/998241780998500000000000000), (2276921797765271451795085037/11978901371982000000000000000), (23090058397995660877719167837/127774947967808000000000000000), (157993462004359315833255593059/1022199583742464000000000000000)]
    reserve := (154562244513/1000000000000) }

theorem mixed_006_007_valid : mixed_006_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_007]
  · intro i; fin_cases i <;> norm_num [mixed_006_007]
  · norm_num [mixed_006_007]
  · norm_num [mixed_006_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_007]

def mixed_006_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(39545593/50000000), 0, (4742731/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(616623/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16258103025468383514700481/4025846473026000000000000), (-31663876/616623), (-108634821682229461171566827/670974412171000000000000), (-31663876/616623), (-635550827067908383514700481/4025846473026000000000000)]
    bernstein := [(1202427934758944278442937364319/10306166970946560000000000000000), (729497452730180054676562508251/5153083485473280000000000000000), (384886560423589242899146355479/2576541742736640000000000000000), (180807938560314887982240185491/1288270871368320000000000000000), (73843295001210177277388837839/644135435684160000000000000000)]
    reserve := (1791240507/15625000000) }

theorem mixed_006_008_valid : mixed_006_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_008]
  · intro i; fin_cases i <;> norm_num [mixed_006_008]
  · norm_num [mixed_006_008]
  · norm_num [mixed_006_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_008]

def mixed_006_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(37567091/50000000), 0, (96288913/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(31049/5000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1172815546937745451240173/405429272476000000000000), (-53979451/1241960), (-32605666802288045451240173/202714636238000000000000), (-53979451/1241960), (-64038518057638345451240173/405429272476000000000000)]
    bernstein := [(4826313681731068571092620387/64868683596160000000000000000), (2577432852797636702171386609/25947473438464000000000000000), (3341792400699214190779687921/31136968126156800000000000000), (81853068445632448822073413/830319150030848000000000000), (79749310017244897383783/1088943147581440000000000)]
    reserve := (36617756489/500000000000) }

theorem mixed_006_009_valid : mixed_006_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_009]
  · intro i; fin_cases i <;> norm_num [mixed_006_009]
  · norm_num [mixed_006_009]
  · norm_num [mixed_006_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_009]

def mixed_006_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(24087053/100000000), (21288839/100000000), (3241713/50000000), (7015063/100000000), (7015063/100000000), (7149069/100000000), (26961487/100000000)]
    cone := fun i => (![![(443173/6250000), 0, (2200501/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(168409/100000000), (1585777/100000000), (702899/12500000), (2413669/100000000), (1/100000000), (632711/25000000), (881007/12500000)]
    alternative := .zero
    polynomial := [(-702535023831833053674386575319795630403894827269/1485640986377479436644782710416182300000000000000), (-337367447747649/33681800000000), (-34366259920566165459472615115561857418256314327269/742820493188739718322391355208091150000000000000), (-337367447747649/33681800000000), (-68029984817300497865270843655803919206108733827269/1485640986377479436644782710416182300000000000000)]
    bernstein := [(15737626942786370445440653550372309422115063991539/243407419208086230899881199274587308032000000000000), (2196732903168766269788549510443157081905328381093/29829340589226253786750146969924915200000000000000), (2217938341846548358523757245596894713888396611055197/28524306938447605183579828039990700160000000000000000), (305225797637460622004001167976748982410603277787437/3961709297006611831052753894443152800000000000000000), (62518777366917867775883147130282007003208361354643/873906462574987903908695712009519000000000000000000)]
    reserve := (64655494043/1000000000000) }

theorem mixed_006_010_valid : mixed_006_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_010]
  · intro i; fin_cases i <;> norm_num [mixed_006_010]
  · norm_num [mixed_006_010]
  · norm_num [mixed_006_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_010]

def mixed_006_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(1546247/6250000), (5617441/25000000), (682903/10000000), (1839903/25000000), (6706219/100000000), (3386859/50000000), (5024341/20000000)]
    cone := fun i => (![![(872579/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3267/10000000), 0, (40837/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(9853/6250000), (658541/50000000), (2967043/50000000), (1268441/50000000), (1/100000000), (1204257/50000000), (6574457/100000000)]
    alternative := .zero
    polynomial := [(-4898229573338161844033277319299873012185863883/20481062727761820765776759442876806250000000000), (-116687987846119/15764800000000), (-451842051387460769814667838572882181821511207633/10240531363880910382888379721438403125000000000), (-116687987846119/15764800000000), (-898785873201583377785302399826464490630836551383/20481062727761820765776759442876806250000000000)]
    bernstein := [(25726650383782572299669333531815782079006788605909/409621254555236415315535188857536125000000000000000), (15096800843244081178147157076991761706779303413593/211417421705928472420921387797438000000000000000000), (2963825036725671907969782954908459305276498113972661/39323640437302695870291378130323468000000000000000000), (252798112494204268605507417533260702962043812383687/3382678747294855558734742204759008000000000000000000), (3644999082336047080769716073698070183956300664183827/52431520583070261160388504173764624000000000000000000)]
    reserve := (31402972987/500000000000) }

theorem mixed_006_011_valid : mixed_006_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_011]
  · intro i; fin_cases i <;> norm_num [mixed_006_011]
  · norm_num [mixed_006_011]
  · norm_num [mixed_006_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_011]

def mixed_006_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(24486409/100000000), (5714671/25000000), (700929/10000000), (1894847/25000000), (1334227/20000000), (1343327/20000000), (24678459/100000000)]
    cone := fun i => (![![(768201/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(45413/100000000), 0, (454127/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(155397/100000000), (3937/400000), (48331/800000), (1304287/50000000), (1/100000000), (239203/10000000), (3231291/50000000)]
    alternative := .zero
    polynomial := [(-5215551656678847615992202255053946806168831/58449326174413258338606151545900000000000000), (-6911367447011/1294975000000), (-1307860672778554700040262675858101871435652831/29224663087206629169303075772950000000000000), (-6911367447011/1294975000000), (-2610505793900430552464533149461149796065136831/58449326174413258338606151545900000000000000)]
    bernstein := [(9001255673833927573244022090580678807952035023889/149630275006497941346831747957504000000000000000000), (5137038871955544635707528958932102069910923653563/74815137503248970673415873978752000000000000000000), (8133447334105989735468745407031845816646223886763/112222706254873456010123810968128000000000000000000), (1339690477076205240885169174257336020763693007507/18703784375812242668353968494688000000000000000000), (618435086850448681652449710481666420800479638369/9351892187906121334176984247344000000000000000000)]
    reserve := (12031329453/200000000000) }

theorem mixed_006_012_valid : mixed_006_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_012]
  · intro i; fin_cases i <;> norm_num [mixed_006_012]
  · norm_num [mixed_006_012]
  · norm_num [mixed_006_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_012]

def mixed_006_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(12094601/50000000), (23210519/100000000), (3597367/50000000), (1562439/20000000), (6658513/100000000), (3338753/50000000), (2425733/10000000)]
    cone := fun i => (![![(363349/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14421/25000000), 0, (1153681/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(153079/100000000), (647091/100000000), (6140137/100000000), (2683583/100000000), (1/100000000), (2382773/100000000), (794667/12500000)]
    alternative := .zero
    polynomial := [(756458527768114042226677457129806767856126182389/103019790767452212436403630004656394300000000000000), (-12793867266713/3826975000000), (-2420585723832210284424573652453201247964401270817611/51509895383726106218201815002328197150000000000000), (-12793867266713/3826975000000), (-1613975968730729560963791327454510767565552889272537/34339930255817404145467876668218798100000000000000)]
    bernstein := [(941834619885141868346125810311656221613983131540333589/16483166522792353989824580800745023088000000000000000000), (2162773486976863638123525879286662146299477102815529189/32966333045584707979649161601490046176000000000000000000), (1954119774390862390316475884119389176187071527070264281/28256856896215463982556424229848611008000000000000000000), (8942191869922564246616077358696445310710267269767835989/131865332182338831918596646405960184704000000000000000000), (16241383330683394452937893157090094222662973168991667189/263730664364677663837193292811920369408000000000000000000)]
    reserve := (28569590029/500000000000) }

theorem mixed_006_013_valid : mixed_006_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_013]
  · intro i; fin_cases i <;> norm_num [mixed_006_013]
  · norm_num [mixed_006_013]
  · norm_num [mixed_006_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_013]

def mixed_006_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(5876339/25000000), (4636791/20000000), (7297891/100000000), (1994693/25000000), (1994693/25000000), (817819/12500000), (23512703/100000000)]
    cone := fun i => (![![(293863/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (71811/10000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(148519/100000000), (152909/50000000), (3070751/50000000), (1366109/50000000), (1/100000000), (2594551/100000000), (1233381/20000000)]
    alternative := .zero
    polynomial := [(202989823448205688472871155908731254648715211487/3810785444464837860012627157439263237500000000000), (-5176385627167/3712975000000), (-104654013713382382748903818098220368921043605913513/1905392722232418930006313578719631618750000000000), (-5176385627167/3712975000000), (-209511017250212971186280507352349469096735927038513/3810785444464837860012627157439263237500000000000)]
    bernstein := [(524779880144777617985695860872159373626926398296439887/9755610737829984921632325523044513888000000000000000000), (189772652005849045135166210683144911449681967775031/3048628355571870288010101725951410590000000000000000), (1188461929922431742591856056466811038535811019224087/18291770133431221728060610355708463540000000000000000), (118097244593083407813049032444111532800556647931/1905392722232418930006313578719631618750000000000), (202989823448205688472871155908731254648715211487/3810785444464837860012627157439263237500000000000)]
    reserve := (6658398459/125000000000) }

theorem mixed_006_014_valid : mixed_006_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_014]
  · intro i; fin_cases i <;> norm_num [mixed_006_014]
  · norm_num [mixed_006_014]
  · norm_num [mixed_006_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_014]

def mixed_006_015 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(4662869/20000000), (23321631/100000000), (7278999/100000000), (7924599/100000000), (3402223/50000000), (1701673/25000000), (3068661/12500000)]
    cone := fun i => (![![0, 0, (1227273/100000000), 0, 0], ![(11659/2000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7001/12500000), 0, (1120153/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(77533/50000000), (9207/6250000), (6173269/100000000), (1359451/50000000), (1/100000000), (1215963/50000000), (6437137/100000000)]
    alternative := .zero
    polynomial := [(6801409276957431389474536679388208394301659/161807341774115948639609602907955000000000000), (454074707778556003/190359021600000000), (-12245420124867794281716014090658993127967268557/161807341774115948639609602907955000000000000), (454074707778556003/190359021600000000), (-1531527691768093964138186078417297667045196277/20225917721764493579951200363494375000000000)]
    bernstein := [(6801409276957431389474536679388208394301659/161807341774115948639609602907955000000000000), (147419417029905267749174350311163877277044669/2588917468385855178233753646527280000000000000), (99364351252227185678337654160610859019190407843/1553350481031513106940252187916368000000000000000), (261456282632981030166730072547079348660799540069/4142267949417368285174005834443648000000000000000), (2815514747277889654006930896642261827521892878573/51778349367717103564675072930545600000000000000000)]
    reserve := (42033996741/1000000000000) }

theorem mixed_006_015_valid : mixed_006_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_015]
  · intro i; fin_cases i <;> norm_num [mixed_006_015]
  · norm_num [mixed_006_015]
  · norm_num [mixed_006_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_015]

def mixed_006_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(5601539/25000000), (11234631/50000000), (6889783/100000000), (3725061/50000000), (7147447/100000000), (7196233/100000000), (26440997/100000000)]
    cone := fun i => (![![0, 0, (198029/5000000), 0, 0], ![(420707/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7567/50000000), 0, (12107/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(166859/100000000), (28359/20000000), (5938447/100000000), (2564091/100000000), (1/100000000), (102513/4000000), (6924133/100000000)]
    alternative := .zero
    polynomial := [(-12187355055807945076057008393307685661161264419/189420704918900084222308556451279900000000000000), (14190282065949749/2240508703125000), (-7332068237676524518484785234190045287291656464419/94710352459450042111154278225639950000000000000), (14190282065949749/2240508703125000), (-14651949120297241091893513459986782888922151664419/189420704918900084222308556451279900000000000000)]
    bernstein := [(3164534877302806658103239336310360279028960579650683/69273857798912030801301414930753792000000000000000000), (705641376546998790633372579339859189578778167114761/11545642966485338466883569155125632000000000000000000), (181866991429484800003606255998008284945067090609839/2654655134629840596400236703550784000000000000000000), (1370891126160606102931931194830961997525648385650927/20204875191349342317046246021469856000000000000000000), (1791292542147418628506560161963694160988237473760381/30307312787024013475569369032204784000000000000000000)]
    reserve := (45681516489/1000000000000) }

theorem mixed_006_016_valid : mixed_006_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_016]
  · intro i; fin_cases i <;> norm_num [mixed_006_016]
  · norm_num [mixed_006_016]
  · norm_num [mixed_006_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_016]

def mixed_006_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(4899401/20000000), (12344569/50000000), (7537513/100000000), (4068519/50000000), (6131827/100000000), (772931/12500000), (713251/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1537067/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(100261/100000000), 0, (2005211/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(247161/25000000), (19433/12500000), (3261353/50000000), (2802647/100000000), (1/100000000), (2200411/100000000), (239003/4000000)]
    alternative := .zero
    polynomial := [(-10188257309252527908252722643403111191711203251/115441820617749218826324131804562195000000000000), (20748587294547/3886600000000), (-860724066465608752725781328861042142811996390667/19240303436291536471054021967427032500000000000), (20748587294547/3886600000000), (-5154156141484399988446435250522849745680267140751/115441820617749218826324131804562195000000000000)]
    bernstein := [(413865175850222275082282485172771560112791675199483/6156897099613291670737287029576650400000000000000000), (2686983026005405984722050716128463230574863378130747/36941382597679750024423722177459902400000000000000000), (1812756354907670600011797578292100889739001353990547/24627588398453166682949148118306601600000000000000000), (10316509567352940717140750354227575928935748509532723/147765530390719000097694888709839609600000000000000000), (18126393220692080443444194389356609013513838012410369/295531060781438000195389777419679219200000000000000000)]
    reserve := (61334985137/1000000000000) }

theorem mixed_006_017_valid : mixed_006_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_017]
  · intro i; fin_cases i <;> norm_num [mixed_006_017]
  · norm_num [mixed_006_017]
  · norm_num [mixed_006_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_017]

def mixed_006_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(24753491/100000000), (12567727/50000000), (1897851/25000000), (1632379/20000000), (1186451/20000000), (3002753/50000000), (5604999/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4365283/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(55741/50000000), 0, (55741/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1323241/100000000), (78867/50000000), (6634573/100000000), (563303/20000000), (1/100000000), (2132981/100000000), (2932401/50000000)]
    alternative := .zero
    polynomial := [(-19340960466271108375643946680068962994254206832101/81316448439906674179003904587739051100000000000000), (11679616134161/1577340000000), (-597882951443167993149419271907352091067166641777367/13552741406651112363167317431289841850000000000000), (11679616134161/1577340000000), (-3567956748192736850520871684764043583408745643832101/81316448439906674179003904587739051100000000000000)]
    bernstein := [(14798005024980420255251576263809681081716897013306531019/208170108006161085898249995744611970816000000000000000000), (305550318328206036982582536463375945578813891286134221/4003271307810790113427884533550230208000000000000000000), (1001664426987619732827701151508404626234928202919571991/13010631750385067868640624734038248176000000000000000000), (18278083138890303738357517823157186998983732724191769/250204456738174382089242783346889388000000000000000000), (52431909867006559336209293826359475660772416618737699/813164484399066741790039045877390511000000000000000000)]
    reserve := (32239424417/500000000000) }

theorem mixed_006_018_valid : mixed_006_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_018]
  · intro i; fin_cases i <;> norm_num [mixed_006_018]
  · norm_num [mixed_006_018]
  · norm_num [mixed_006_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_018]

def mixed_006_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(24964837/100000000), (1280243/5000000), (3831897/50000000), (1642391/20000000), (2871213/50000000), (5832107/100000000), (21980021/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(5689091/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(30869/25000000), 0, (246953/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1650699/100000000), (31987/20000000), (3376713/50000000), (1419119/50000000), (1/100000000), (258513/12500000), (2873047/50000000)]
    alternative := .zero
    polynomial := [(-926583981023850463709180680924787452638026191003/2088031142825937094357223764135416900000000000000), (15269912789953/1599350000000), (-46123869004885650515627920584474959299466053691003/1044015571412968547178611882067708450000000000000), (15269912789953/1599350000000), (-10146794892083050063060740054225014571810453465667/232003460313993010484135973792824100000000000000)]
    bernstein := [(1553053816488531604394021884931206747088667490578397/20880311428259370943572237641354169000000000000000000), (1328386503633149971655205618400879067256497035404457/16704249142607496754857790113083335200000000000000000), (3210899254633631786662112396058787496632757416723939/40090197942257992211658696271400004480000000000000000), (12508446372097515624200555675869447707777437728757/164472606942596891124753625728820531200000000000000), (1772505851771622042385764250418444102928403716961/26315617110815502579960580116611284992000000000000)]
    reserve := (16838915883/250000000000) }

theorem mixed_006_019_valid : mixed_006_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_019]
  · intro i; fin_cases i <;> norm_num [mixed_006_019]
  · norm_num [mixed_006_019]
  · norm_num [mixed_006_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_019]

def mixed_006_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(5026127/20000000), (26099199/100000000), (387731/5000000), (4143303/50000000), (5560751/100000000), (141559/2500000), (21505829/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3522051/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(136293/100000000), 0, (1362927/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(393759/20000000), (162071/100000000), (1375937/20000000), (286769/10000000), (1/100000000), (401067/20000000), (5619293/100000000)]
    alternative := .zero
    polynomial := [(-12778380722060042549777818808810017358867481683/18015843878180499006920458714190580000000000000), (65527596943/5565625000), (-44672230430486881473443705170875460503500920187/1000880215454472167051136595232810000000000000), (65527596943/5565625000), (-791321767026703823972208874266948271704149081683/18015843878180499006920458714190580000000000000)]
    bernstein := [(1950146268263253742585885541388659965361477569/25228340692317033823024341501991321600000000000), (3042134915981202060601322462395536308033258153723/36896448262513661966173099446662307840000000000000), (5467467967119456698194755100790338346015996770771/65886514754488682082451963297611264000000000000000), (90923811306227913980148884532887505704454918639439/1153014008203551936442909357708197120000000000000000), (201826028660310684713979262480928153260233498986077/2882535020508879841107273394270492800000000000000000)]
    reserve := (35008426129/500000000000) }

theorem mixed_006_020_valid : mixed_006_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_020]
  · intro i; fin_cases i <;> norm_num [mixed_006_020]
  · norm_num [mixed_006_020]
  · norm_num [mixed_006_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_020]

def mixed_006_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(25250769/100000000), (5324099/20000000), (7863759/100000000), (20963/250000), (5385551/100000000), (549523/10000000), (20998997/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(210727/2500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(74991/50000000), 0, (2999649/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2275551/100000000), (41037/25000000), (3506907/50000000), (116189/4000000), (1/100000000), (1944187/100000000), (5484701/100000000)]
    alternative := .zero
    polynomial := [(-2339963784106734141724290979136076296250521361571/2254083122082839128153435228976022150000000000000), (14455010544607/1025925000000), (-51118639111953155231717588966870760479700005174071/1127041561041419564076717614488011075000000000000), (14455010544607/1025925000000), (-99897314439799576321710886954605444663149488986571/2254083122082839128153435228976022150000000000000)]
    bernstein := [(28836372310025490818682407391659601376414187127416549/360653299533254260504549636636163544000000000000000000), (61439537564795746475229681479061513440419135553310481/721306599066508521009099273272327088000000000000000000), (370951648804651237164723378046543170068739083978461367/4327839594399051126054595639633962528000000000000000000), (235178930528752712221603000290774666668576186599569641/2885226396266034084036397093089308352000000000000000000), (418401601591428034987146556130312175424819015147150229/5770452792532068168072794186178616704000000000000000000)]
    reserve := (72507585909/1000000000000) }

theorem mixed_006_021_valid : mixed_006_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_021]
  · intro i; fin_cases i <;> norm_num [mixed_006_021]
  · norm_num [mixed_006_021]
  · norm_num [mixed_006_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_021]

def mixed_006_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(14156009/50000000), (15187621/50000000), (8930799/100000000), (4753243/50000000), 0, 0, (4575091/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(11003861/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(118831/25000000), 0, (4753243/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5974027/100000000), 0, 0]] i.1) i.2
    mu := ![(2872059/100000000), (185771/100000000), (2000021/25000000), (823957/25000000), (1/100000000), (1/100000000), (1493507/25000000)]
    alternative := .zero
    polynomial := [(-63025867596191768317424963046314111299009/39058893225394240899606242550000000000000), (85686033277743/4644275000000), (-1011135945678577713786353991167221147799009/19529446612697120449803121275000000000000), (85686033277743/4644275000000), (-653082007920321219751761006429376061433003/13019631075131413633202080850000000000000)]
    bernstein := [(8132571036100237024468711438863665246670428191/99990766657009256702991980928000000000000000000), (1090653078117132383043327149891912318265870913/12498845832126157087873997616000000000000000000), (102931532646833793310878073894070823511328713/1171766796761827226988187276500000000000000000), (8106309659987865723996280265787047810116781/97647233063485602249015606375000000000000000), (443656486191139776585552503024763610967479/6102952066467850140563475398437500000000000)]
    reserve := (1135865483/15625000000) }

theorem mixed_006_022_valid : mixed_006_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_022]
  · intro i; fin_cases i <;> norm_num [mixed_006_022]
  · norm_num [mixed_006_022]
  · norm_num [mixed_006_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_022]

def mixed_006_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(28241401/100000000), (7728143/25000000), (1132069/12500000), (4813883/50000000), 0, 0, (5540427/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(12570219/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(120347/25000000), 0, (4813883/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5787629/100000000), 0, 0]] i.1) i.2
    mu := ![(1586037/50000000), (187301/100000000), (813931/10000000), (41749/1250000), (1/100000000), (1/100000000), (578763/10000000)]
    alternative := .zero
    polynomial := [(-414580707788226518960454413707512865893263/194745119284861046210619546300000000000000), (99219905008371/4682525000000), (-5145262983599545630176948590709485356893263/97372559642430523105309773150000000000000), (99219905008371/4682525000000), (-9875945259410864741393442767711457847893263/194745119284861046210619546300000000000000)]
    bernstein := [(2549301502265132664682417460343706771038553/30428924888259538470409304109375000000000000), (43749385259862211402678982424357563561504429/486862798212152615526548865750000000000000000), (528691753904195133463013509512291507617701279/5842353578545831386318586389000000000000000000), (5334623882323044484824162632443836884752803473/62318438171155534787398254816000000000000000000), (37437636501413788643785278265039105565205251857/498547505369244278299186038528000000000000000000)]
    reserve := (75093418577/1000000000000) }

theorem mixed_006_023_valid : mixed_006_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_023]
  · intro i; fin_cases i <;> norm_num [mixed_006_023]
  · norm_num [mixed_006_023]
  · norm_num [mixed_006_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_023]

def mixed_006_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![(28121017/100000000), (31483059/100000000), (4600879/50000000), (1954719/20000000), 0, 0, (21420571/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(221187/1562500), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(12217/2500000), 0, (1954719/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2797039/50000000), 0, 0]] i.1) i.2
    mu := ![(862981/25000000), (188777/100000000), (8287963/100000000), (3391899/100000000), (1/100000000), (1/100000000), (2797039/50000000)]
    alternative := .zero
    polynomial := [(-35628884399267209505243850130479529796058839/13071140289481330650194125642950000000000000), (226880299004723/9438850000000), (-353541971828235802335103117750745173882121339/6535570144740665325097062821475000000000000), (226880299004723/9438850000000), (-95922151322457770737851769338715831138311977/1867305755640190092884875091850000000000000)]
    bernstein := [(2881263564410027746305344676388243374221826923521/33462119141072206464496961645952000000000000000000), (309127438580771673425384848465963728976410362329/3346211914107220646449696164595200000000000000000), (93446870259306224885653173162986447488276181539/1003863574232166193934908849378560000000000000000), (2949226228840464512436326530675783434911830553/33462119141072206464496961645952000000000000000), (259069338726219505892955578997077901600870529/3346211914107220646449696164595200000000000000)]
    reserve := (3871083861/50000000000) }

theorem mixed_006_024_valid : mixed_006_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_024]
  · intro i; fin_cases i <;> norm_num [mixed_006_024]
  · norm_num [mixed_006_024]
  · norm_num [mixed_006_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_024]

def mixed_006_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, (62809767/100000000), (18090947/100000000), (9549643/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(6717/20000), 0, (54711797/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(238741/25000000), 0, (9549643/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (37231/10000000), (660639/4000000), (3323643/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-36807774432254033047358479489463/5449943744189905800000000000000), (38752885272178701/744620000000000), (-288323697170480851780841553589463/2724971872094952900000000000000), (38752885272178701/744620000000000), (-539839619908707670514324627689463/5449943744189905800000000000000)]
    bernstein := [(98260394814416055009358004265193/1395185598512615884800000000000000), (406223111747073306293563905580353/4650618661708719616000000000000000), (39111159706768286411406579139945843/418555679553784765440000000000000000), (41171662566112174397423369569078089/465061866170871961600000000000000000), (1009901119780614063168161019984818617/13951855985126158848000000000000000000)]
    reserve := (70428188851/1000000000000) }

theorem mixed_006_025_valid : mixed_006_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_025]
  · intro i; fin_cases i <;> norm_num [mixed_006_025]
  · norm_num [mixed_006_025]
  · norm_num [mixed_006_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_025]

def mixed_006_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, (32515479/50000000), (8630393/50000000), (17708257/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(18646541/50000000), 0, (27550639/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(885413/100000000), 0, (17708257/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (95169/25000000), (17000989/100000000), (6248491/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8477303153785041133256426976697117/1010985300099393923100000000000000), (3743400674107233/63446000000000), (-56059136513685939132448989236197117/505492650049696961550000000000000), (3743400674107233/63446000000000), (-103640969873586837131641551495697117/1010985300099393923100000000000000)]
    bernstein := [(243596674313727508843451522572617287603/2588122368254448443136000000000000000000), (72482424270681756574173171780701666419/647030592063612110784000000000000000000), (57552534261950699946222007924454230661/485272944047709083088000000000000000000), (4595383995724389339194122130458793951/40439412003975756924000000000000000000), (979514373321594851799916391336052923/10109853000993939231000000000000000000)]
    reserve := (18824200687/200000000000) }

theorem mixed_006_026_valid : mixed_006_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_026]
  · intro i; fin_cases i <;> norm_num [mixed_006_026]
  · norm_num [mixed_006_026]
  · norm_num [mixed_006_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_026]

def mixed_006_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(30524911/50000000), 0, (41103203/50000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (577517/100000000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-34592169114444908552055013/2262317277392400000000000), (569395017/5775170), (-195606453201436508552055013/1131158638696200000000000), (569395017/5775170), (-356620737288428108552055013/2262317277392400000000000)]
    bernstein := [(2474205608706837093034390547/22623172773924000000000000000), (12404529942215295575615572937/90492691095696000000000000000), (159794698189905469363012017581/1085912293148352000000000000000), (201598277502082077551045399317/1447883057531136000000000000000), (653948506597215164632572463307/5791532230124544000000000000000)]
    reserve := (109365986523/1000000000000) }

theorem mixed_006_027_valid : mixed_006_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_027]
  · intro i; fin_cases i <;> norm_num [mixed_006_027]
  · norm_num [mixed_006_027]
  · norm_num [mixed_006_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_027]

def mixed_006_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2582999/4000000), 0, (19887081/25000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (71153/12500000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-24840276814657694648173271/1393644353658000000000000), (151493897/1423060), (-122220282388524194648173271/696822176829000000000000), (151493897/1423060), (-219600287962390694648173271/1393644353658000000000000)]
    bernstein := [(515774459835714753097844490169/3567729545364480000000000000000), (102854462752865499212300629497/594621590894080000000000000000), (491067540804500739181397027347/2675797159023360000000000000000), (26137213078319186082149792337/148655397723520000000000000000), (33321573439233174233620393129/222983096585280000000000000000)]
    reserve := (144566580307/1000000000000) }

theorem mixed_006_028_valid : mixed_006_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_028]
  · intro i; fin_cases i <;> norm_num [mixed_006_028]
  · norm_num [mixed_006_028]
  · norm_num [mixed_006_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_028]

def mixed_006_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(13583621/20000000), 0, (19192791/25000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (560543/100000000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-225687117940091736631685173/10979123676198000000000000), (320397734/2802715), (-977529620943143736631685173/5489561838099000000000000), (320397734/2802715), (-1729372123946195736631685173/10979123676198000000000000)]
    bernstein := [(314235498496942627315637438027/1756659788191680000000000000000), (146182140136763496479577675463/702663915276672000000000000000), (184737751281415488041979179273/843196698332006400000000000000), (23792104293952627085543809151/112426226444267520000000000000), (8326718578362657089749713083/44970490577707008000000000000)]
    reserve := (44720597097/250000000000) }

theorem mixed_006_029_valid : mixed_006_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_006_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_006_029]
  · intro i; fin_cases i <;> norm_num [mixed_006_029]
  · norm_num [mixed_006_029]
  · norm_num [mixed_006_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_006_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_006_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_006_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_006_029]

def mixedTable006 : OwnerTable where
  mode := .mixed
  owners := ![0, 1, 0, 2, 0, 2, 3]
  rows := [mixed_006_000, mixed_006_001, mixed_006_002, mixed_006_003, mixed_006_004, mixed_006_005, mixed_006_006, mixed_006_007, mixed_006_008, mixed_006_009, mixed_006_010, mixed_006_011, mixed_006_012, mixed_006_013, mixed_006_014, mixed_006_015, mixed_006_016, mixed_006_017, mixed_006_018, mixed_006_019, mixed_006_020, mixed_006_021, mixed_006_022, mixed_006_023, mixed_006_024, mixed_006_025, mixed_006_026, mixed_006_027, mixed_006_028, mixed_006_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_006_000_valid
    · exact mixed_006_001_valid
    · exact mixed_006_002_valid
    · exact mixed_006_003_valid
    · exact mixed_006_004_valid
    · exact mixed_006_005_valid
    · exact mixed_006_006_valid
    · exact mixed_006_007_valid
    · exact mixed_006_008_valid
    · exact mixed_006_009_valid
    · exact mixed_006_010_valid
    · exact mixed_006_011_valid
    · exact mixed_006_012_valid
    · exact mixed_006_013_valid
    · exact mixed_006_014_valid
    · exact mixed_006_015_valid
    · exact mixed_006_016_valid
    · exact mixed_006_017_valid
    · exact mixed_006_018_valid
    · exact mixed_006_019_valid
    · exact mixed_006_020_valid
    · exact mixed_006_021_valid
    · exact mixed_006_022_valid
    · exact mixed_006_023_valid
    · exact mixed_006_024_valid
    · exact mixed_006_025_valid
    · exact mixed_006_026_valid
    · exact mixed_006_027_valid
    · exact mixed_006_028_valid
    · exact mixed_006_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
