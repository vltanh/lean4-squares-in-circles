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

def mixed_014_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9323878086264272438164777/457463486508250000000000), (-64079547/560543), (-40650649044724772438164777/228731743254125000000000), (-64079547/560543), (-71977420003185272438164777/457463486508250000000000)]
    bernstein := [(771944384308161177019903367/1873770440737792000000000000), (2045099281096760524528801499/4684426101844480000000000000), (15536936375244992100840585677/35133195763833600000000000000), (12572278001133635972786737987/29277663136528000000000000000), (29171204288533746193542792023/73194157841320000000000000000)]
    reserve := (39854552807/100000000000) }

theorem mixed_014_000_valid : mixed_014_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_000]
  · intro i; fin_cases i <;> norm_num [mixed_014_000]
  · norm_num [mixed_014_000]
  · norm_num [mixed_014_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_000]

def mixed_014_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8195479695018141692827207/464548117886000000000000), (-60597559/569224), (-40655481552973641692827207/232274058943000000000000), (-60597559/569224), (-73115483410929141692827207/464548117886000000000000)]
    bernstein := [(28165181448433940584342241593/74327698861760000000000000000), (59987255907906319759240394787/148655397723520000000000000000), (365240093712578782092801356099/891932386341120000000000000000), (236219105813974844491305697947/594621590894080000000000000000), (436708267205816752992558675273/1189243181788160000000000000000)]
    reserve := (367215279341/1000000000000) }

theorem mixed_014_001_valid : mixed_014_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_001]
  · intro i; fin_cases i <;> norm_num [mixed_014_001]
  · norm_num [mixed_014_001]
  · norm_num [mixed_014_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_001]

def mixed_014_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1423459636141088562438957/94263219891350000000000), (-56939502/577517), (-8132388139765738562438957/47131609945675000000000), (-56939502/577517), (-14841316643390388562438957/94263219891350000000000)]
    bernstein := [(83203201243560805857463083523/241313842921856000000000000000), (22285963806524996156967944413/60328460730464000000000000000), (16997892937923406218361408309/45246345547848000000000000000), (1372467533604261648733468593/3770528795654000000000000000), (315533175520850489662751883/942632198913500000000000000)]
    reserve := (334736258621/1000000000000) }

theorem mixed_014_002_valid : mixed_014_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_002]
  · intro i; fin_cases i <;> norm_num [mixed_014_002]
  · norm_num [mixed_014_002]
  · norm_num [mixed_014_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_002]

def mixed_014_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9752571069990143856572169/764369130194800000000000), (-106220235/1170754), (-65072167873284343856572169/382184565097400000000000), (-106220235/1170754), (-120391764676578543856572169/764369130194800000000000)]
    bernstein := [(2366256876064270440066060111/7643691301948000000000000000), (10218717636968408101363339707/30574765207792000000000000000), (125031836454212323239764602177/366897182493504000000000000000), (161257140290528105389415666383/489196243324672000000000000000), (589205041140438005306430396871/1956784973298688000000000000000)]
    reserve := (150554365753/500000000000) }

theorem mixed_014_003_valid : mixed_014_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_003]
  · intro i; fin_cases i <;> norm_num [mixed_014_003]
  · norm_num [mixed_014_003]
  · norm_num [mixed_014_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_003]

def mixed_014_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8217006815756847909129793/774005730506800000000000), (-49115626/592757), (-65088061666314447909129793/387002865253400000000000), (-49115626/592757), (-121959116516872047909129793/774005730506800000000000)]
    bernstein := [(541462199981933644775104771087/1981454670097408000000000000000), (59039260927319991174284088237/198145467009740800000000000000), (18118853247657556500861091973/59443640102922240000000000000), (582869908921379928159691749/1981454670097408000000000000), (52769526414835754261489823/198145467009740800000000000)]
    reserve := (10652684053/40000000000) }

theorem mixed_014_004_valid : mixed_014_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_004]
  · intro i; fin_cases i <;> norm_num [mixed_014_004]
  · norm_num [mixed_014_004]
  · norm_num [mixed_014_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_004]

def mixed_014_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16975854023440140909521343/1957398529634000000000000), (-44963763/599614), (-162767147713783140909521343/978699264817000000000000), (-44963763/599614), (-308558441404126140909521343/1957398529634000000000000)]
    bernstein := [(118189125096141277148331873/501094023586304000000000000), (1305883121322862166945181561/5010940235863040000000000000), (311992144757981055774654467/1165334938572800000000000000), (129055832776668462154991188473/501094023586304000000000000000), (1154168652199459017370060282977/5010940235863040000000000000000)]
    reserve := (230329758063/1000000000000) }

theorem mixed_014_005_valid : mixed_014_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_005]
  · intro i; fin_cases i <;> norm_num [mixed_014_005]
  · norm_num [mixed_014_005]
  · norm_num [mixed_014_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_005]

def mixed_014_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1713001392265053495332851/247241475078000000000000), (-847162/12623), (-20352687765926803495332851/123620737539000000000000), (-847162/12623), (-12997458046529517831777617/82413825026000000000000)]
    bernstein := [(9607504628175708190365201953/48687552015360000000000000000), (17574063151746684038204791021/79117272024960000000000000000), (130944449994834311994497791/570557250180000000000000000), (45276098750240676060214611/206034562565000000000000000), (573823949222554560672937/2971652344687500000000000)]
    reserve := (48274821771/250000000000) }

theorem mixed_014_006_valid : mixed_014_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_006]
  · intro i; fin_cases i <;> norm_num [mixed_014_006]
  · norm_num [mixed_014_006]
  · norm_num [mixed_014_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_006]

def mixed_014_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2149684459102271992679741/399296712399400000000000), (-72452831/1223174), (-32576645045177971992679741/199648356199700000000000), (-72452831/1223174), (-63003605631253671992679741/399296712399400000000000)]
    bernstein := [(9833958343755183237123771/62390111312406250000000000), (182147981160652667698816969/998241780998500000000000000), (2276921797765271451795085037/11978901371982000000000000000), (23090058397995660877719167837/127774947967808000000000000000), (157993462004359315833255593059/1022199583742464000000000000000)]
    reserve := (154562244513/1000000000000) }

theorem mixed_014_007_valid : mixed_014_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_007]
  · intro i; fin_cases i <;> norm_num [mixed_014_007]
  · norm_num [mixed_014_007]
  · norm_num [mixed_014_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_007]

def mixed_014_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(39545593/50000000), 0, (4742731/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(616623/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16258103025468383514700481/4025846473026000000000000), (-31663876/616623), (-108634821682229461171566827/670974412171000000000000), (-31663876/616623), (-635550827067908383514700481/4025846473026000000000000)]
    bernstein := [(1202427934758944278442937364319/10306166970946560000000000000000), (729497452730180054676562508251/5153083485473280000000000000000), (384886560423589242899146355479/2576541742736640000000000000000), (180807938560314887982240185491/1288270871368320000000000000000), (73843295001210177277388837839/644135435684160000000000000000)]
    reserve := (1791240507/15625000000) }

theorem mixed_014_008_valid : mixed_014_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_008]
  · intro i; fin_cases i <;> norm_num [mixed_014_008]
  · norm_num [mixed_014_008]
  · norm_num [mixed_014_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_008]

def mixed_014_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(37567091/50000000), 0, (96288913/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(31049/5000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1172815546937745451240173/405429272476000000000000), (-53979451/1241960), (-32605666802288045451240173/202714636238000000000000), (-53979451/1241960), (-64038518057638345451240173/405429272476000000000000)]
    bernstein := [(4826313681731068571092620387/64868683596160000000000000000), (2577432852797636702171386609/25947473438464000000000000000), (3341792400699214190779687921/31136968126156800000000000000), (81853068445632448822073413/830319150030848000000000000), (79749310017244897383783/1088943147581440000000000)]
    reserve := (36617756489/500000000000) }

theorem mixed_014_009_valid : mixed_014_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_009]
  · intro i; fin_cases i <;> norm_num [mixed_014_009]
  · norm_num [mixed_014_009]
  · norm_num [mixed_014_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_009]

def mixed_014_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(35484493/50000000), 0, (48750193/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(4997/800000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-63513499788067795265627/32624723414000000000000), (-22218793/624625), (-137356829492157673435033/858545353000000000000), (-22218793/624625), (-5156046020913923795265627/32624723414000000000000)]
    bernstein := [(164189282602699400109037/5345234684149760000000000), (1859880525364616385294769/33407716775936000000000000), (39969091075665330605601251/626394689548800000000000000), (14431766206684286931905513/260997787312000000000000000), (9865545121022244495338973/326247234140000000000000000)]
    reserve := (30239475123/1000000000000) }

theorem mixed_014_010_valid : mixed_014_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_010]
  · intro i; fin_cases i <;> norm_num [mixed_014_010]
  · norm_num [mixed_014_010]
  · norm_num [mixed_014_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_010]

def mixed_014_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(5772777/100000000), (3866809/50000000), (8189439/100000000), (2187041/20000000), (2187041/20000000), (11845581/100000000), (1783527/4000000)]
    cone := fun i => (![![(13406279/50000000), 0, (38137829/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(139903/50000000), (243851/10000000), (104107/25000000), (431509/12500000), (1/100000000), (1018383/25000000), (233147/2000000)]
    alternative := .zero
    polynomial := [(-18774677152071602211296571706911699870746088409/36388347282311701772122731071943900000000000000), (-699205513903657/55961200000000), (-1319551592713700079992403703479512731664965338409/18194173641155850886061365535971950000000000000), (-699205513903657/55961200000000), (-2620328508275328557773510835252113763459184588409/36388347282311701772122731071943900000000000000)]
    bernstein := [(48734776859443489091805076551495721493309070691/3602806661615019977437894165539000000000000000000), (28325334632182597295683606424803569694253384321/1108555895881544608442428974012000000000000000000), (523325398419072875593942351306793385156916838157257/17466406695509616850618910914533072000000000000000000), (48048538245788311491754505869526932834249561622489/1791426327744576087242965222003392000000000000000000), (1505914565973862652566835669249862489998113045119671/93154169042717956536634191544176384000000000000000000)]
    reserve := (13526892069/1000000000000) }

theorem mixed_014_011_valid : mixed_014_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_011]
  · intro i; fin_cases i <;> norm_num [mixed_014_011]
  · norm_num [mixed_014_011]
  · norm_num [mixed_014_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_011]

def mixed_014_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(2901651/25000000), (3944833/25000000), (8219749/50000000), (20471263/100000000), (20471263/100000000), (883601/25000000), (2924409/25000000)]
    cone := fun i => (![![(291303/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8468429/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(73659/100000000), (2474783/50000000), (631183/100000000), (829267/12500000), (1/100000000), (857827/20000000), (771933/25000000)]
    alternative := .zero
    polynomial := [(-107300496386818775979405659035469799143879119487/2106059726382967628334515713836714900000000000000), (-1613530160843/613825000000), (-23844723886334897305158469359697451967082475119487/1053029863191483814167257856918357450000000000000), (-1613530160843/613825000000), (-6797449610897567976333933294337062019288724445641/300865675197566804047787959119530700000000000000)]
    bernstein := [(103636924508520384256097304900475603687966681991375953/5391512899540397128536360227421990144000000000000000000), (64652060524700631540260337868649962091082929482569851/2695756449770198564268180113710995072000000000000000000), (106618543226671795937676445838968939534198104096326251/4043634674655297846402270170566492608000000000000000000), (17785764975198271280539854288775967808856414491827539/673939112442549641067045028427748768000000000000000000), (8108006933423668660375926940296449201023885235370913/336969556221274820533522514213874384000000000000000000)]
    reserve := (19222234359/1000000000000) }

theorem mixed_014_012_valid : mixed_014_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_012]
  · intro i; fin_cases i <;> norm_num [mixed_014_012]
  · norm_num [mixed_014_012]
  · norm_num [mixed_014_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_012]

def mixed_014_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(139481/1250000), (16255917/100000000), (133527/800000), (1033371/5000000), (1033371/5000000), (168499/5000000), (2797477/25000000)]
    cone := fun i => (![![(167613/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (108109/1250000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(8827/12500000), (4982133/100000000), (214989/50000000), (6712579/100000000), (1/100000000), (1073701/25000000), (738227/25000000)]
    alternative := .zero
    polynomial := [(-1575971661485981743163328399119708569844939/921328982580820675548132770992395000000000000), (-2918431479441/1765400000000), (-11053883506971376140371221678835160553407907439/460664491290410337774066385496197500000000000), (-2918431479441/1765400000000), (-1700476234021635869153790771482400107557382303/70871460198524667349856366999415000000000000)]
    bernstein := [(3097688043487933097762818087574142646120316338861/147412637212931308087701243358783200000000000000000), (2523346936849143661940383502840725119557560916087/98275091475287538725134162239188800000000000000000), (49226053460117576931661727953424829047993513777383/1768951646555175697052414920305398400000000000000000), (10802537453575076220067774294309193480596147210487/393100365901150154900536648956755200000000000000000), (58108662255529794544105487027516069088561963385261/2358602195406900929403219893740531200000000000000000)]
    reserve := (21013721089/1000000000000) }

theorem mixed_014_013_valid : mixed_014_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_013]
  · intro i; fin_cases i <;> norm_num [mixed_014_013]
  · norm_num [mixed_014_013]
  · norm_num [mixed_014_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_013]

def mixed_014_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(2677171/25000000), (1047743/6250000), (16922531/100000000), (10419299/50000000), (10419299/50000000), (3215671/100000000), (10712031/100000000)]
    cone := fun i => (![![(267759/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8811463/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(67663/100000000), (1256597/25000000), (216473/100000000), (6783031/100000000), (1/100000000), (2148909/50000000), (565209/20000000)]
    alternative := .zero
    polynomial := [(28429419071586009748403340724181377240981874243/1263632109620766527350022934380665275000000000000), (-5136832616017/6766300000000), (-18962933776785062433857019521344604291342228625757/631816054810383263675011467190332637500000000000), (-5136832616017/6766300000000), (-37954296972641710877462442383413389959925439125757/1263632109620766527350022934380665275000000000000)]
    bernstein := [(73495009875359272858560160433456369852925908510531843/3234898200629162310016058712014503104000000000000000000), (110619639872756364341379888775907929564199582666711/4043622750786452887520073390018128880000000000000000), (175057652627649704472658466070501950786046002740643/6065434126179679331280110085027193320000000000000000), (68850374572509919520594066889149409548771089111/2527264219241533054700045868761330550000000000000), (28429419071586009748403340724181377240981874243/1263632109620766527350022934380665275000000000000)]
    reserve := (22498177163/1000000000000) }

theorem mixed_014_014_valid : mixed_014_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_014]
  · intro i; fin_cases i <;> norm_num [mixed_014_014]
  · norm_num [mixed_014_014]
  · norm_num [mixed_014_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_014]

def mixed_014_015 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(10272407/100000000), (8547429/50000000), (17089517/100000000), (20753111/100000000), (20753111/100000000), (3220467/100000000), (10816529/100000000)]
    cone := fun i => (![![0, 0, (270371/50000000), 0, 0], ![0, 0, 0, 0, 0], ![(85461/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4383161/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(68323/100000000), (314963/6250000), (5399/5000000), (339651/5000000), (1/100000000), (4283401/100000000), (285169/10000000)]
    alternative := .zero
    polynomial := [(227290878297894200150027098991918256619351/11586983988726152377906802969728125000000000), (97446342590063801/73775175400000000), (-511389661849832400705909077829298553129576923/11586983988726152377906802969728125000000000), (97446342590063801/73775175400000000), (-255808476364065147453029552464145235693098137/5793491994363076188953401484864062500000000)]
    bernstein := [(227290878297894200150027098991918256619351/11586983988726152377906802969728125000000000), (10334254298419585442691518354258574382659857/370783487639236876093017695031300000000000000), (3507170485542134543468741784403430812920567677/111235046291771062827905308509390000000000000000), (18150661051305212589299858569586467899043381057/593253580222779001748828312050080000000000000000), (21860133632134038449773391167950266299117570939/872431735621733826101218105956000000000000000000)]
    reserve := (9808025907/500000000000) }

theorem mixed_014_015_valid : mixed_014_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_015]
  · intro i; fin_cases i <;> norm_num [mixed_014_015]
  · norm_num [mixed_014_015]
  · norm_num [mixed_014_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_015]

def mixed_014_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(4893769/50000000), (537993/3125000), (686697/4000000), (20440483/100000000), (20440483/100000000), (849561/25000000), (11550051/100000000)]
    cone := fun i => (![![0, 0, (69203/4000000), 0, 0], ![0, 0, 0, 0, 0], ![(128937/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8521119/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(9111/12500000), (100079/2000000), (54321/50000000), (6744871/100000000), (1/100000000), (4259307/100000000), (760541/25000000)]
    alternative := .zero
    polynomial := [(-128862422806396720119159506732571749813368211/3435590789091987465129040890694200000000000000), (320702377283455353/87985534400000000), (-78211651944825270568791015769181149106731243211/1717795394545993732564520445347100000000000000), (320702377283455353/87985534400000000), (-156294441466844144417462872031629726463649118211/3435590789091987465129040890694200000000000000)]
    bernstein := [(11664310710312586359751134405582868480330107234031/462900653688183574248965509483008000000000000000000), (2605817880038482705303255786373221520987579938077/77150108948030595708160918247168000000000000000000), (35452055187799015561463961137060922688563966296881/942333473579516561863965501447552000000000000000000), (13460777696347850946746428967472723785169069877863/366463017503145329613764361674048000000000000000000), (17087145230799434255266936200628293470890585052989/549694526254717994420646542511072000000000000000000)]
    reserve := (6299575631/250000000000) }

theorem mixed_014_016_valid : mixed_014_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_016]
  · intro i; fin_cases i <;> norm_num [mixed_014_016]
  · norm_num [mixed_014_016]
  · norm_num [mixed_014_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_016]

def mixed_014_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(2298113/25000000), (866439/5000000), (687757/4000000), (10077871/50000000), (10077871/50000000), (3604457/100000000), (6184451/50000000)]
    cone := fun i => (![![0, 0, (1540097/50000000), 0, 0], ![0, 0, 0, 0, 0], ![(2157669/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4137821/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(15577/20000000), (4956573/100000000), (109117/100000000), (167357/2500000), (1/100000000), (1061319/25000000), (203461/6250000)]
    alternative := .zero
    polynomial := [(-1614301967730077469736939674139360361905465099/10148631543437705781008337438479700000000000000), (2600470963705128339/424928877250000000), (-239070435033461244652716233875726898452436665099/5074315771718852890504168719239850000000000000), (2600470963705128339/424928877250000000), (-476526568099192411835695528077314436542967865099/10148631543437705781008337438479700000000000000)]
    bernstein := [(48080043422139902934631407274056643958977180215701/1623781046950032924961333990156752000000000000000000), (125201768332677447235554981092750384568095448526703/3247562093900065849922667980313504000000000000000000), (830266166778047086762219544235057844725033894097127/19485372563400395099536007881881024000000000000000000), (542585471301197942804283251112362855219233253734327/12990248375600263399690671921254016000000000000000000), (935253801508547520508330838073468772352471378635781/25980496751200526799381343842508032000000000000000000)]
    reserve := (462655159/15625000000) }

theorem mixed_014_017_valid : mixed_014_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_017]
  · intro i; fin_cases i <;> norm_num [mixed_014_017]
  · norm_num [mixed_014_017]
  · norm_num [mixed_014_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_017]

def mixed_014_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(365273/4000000), (9390791/50000000), (9248087/50000000), (21436149/100000000), (21436149/100000000), (1202619/50000000), (1662577/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(815451/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1903091/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(121133/25000000), (5276949/100000000), (117861/100000000), (7154089/100000000), (1/100000000), (2129891/50000000), (2186657/100000000)]
    alternative := .zero
    polynomial := [(-905329995563385268750833990973083422043562474009/4921955664029132825351128742439374100000000000000), (10536894861983/1964350000000), (-45311816193461696836043729070197794778103430023557/1442642177387849276396020493473609650000000000000), (10536894861983/1964350000000), (-870898243098733622307257369408309892985086126436051/27891082096165086010323062873823119900000000000000)]
    bernstein := [(9203781819137531272702887320764793268973029668409553207/214203510498547860559281122870961560832000000000000000000), (2532068350836556334074348003372243382366440016577274669/53550877624636965139820280717740390208000000000000000000), (1941629566102146422497068050837641471512177978848222969/40163158218477723854865210538305292656000000000000000000), (51467108683406474044505596517158668633264563600916147/1115643283846603440412922514952924796000000000000000000), (1999377861467270316611645096382400354128801668384191/49219556640291328253511287424393741000000000000000000)]
    reserve := (40621614617/1000000000000) }

theorem mixed_014_018_valid : mixed_014_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_018]
  · intro i; fin_cases i <;> norm_num [mixed_014_018]
  · norm_num [mixed_014_018]
  · norm_num [mixed_014_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_018]

def mixed_014_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(438211/5000000), (19351723/100000000), (3773601/20000000), (860619/4000000), (860619/4000000), (2222873/100000000), (776223/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4299719/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9646301/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(57567/10000000), (2683947/50000000), (30219/25000000), (1807719/25000000), (1/100000000), (1060343/25000000), (10201/500000)]
    alternative := .zero
    polynomial := [(-6229669971844891227863171188994490580213/18401641002919686166483118706400000000000), (85083505692797/12087600000000), (-2065214369929014368222752695577100856266491/64405743510218901582690915472400000000000), (85083505692797/12087600000000), (-4086821050055114497850463192831240278471491/128811487020437803165381830944800000000000)]
    bernstein := [(18396005302858071628423963143682443765527/378820175533098136943579544000000000000000), (540742948438699220237034376039747170266229/10202890061024776488347075718400000000000000), (133844024669439955608218073787308207778698683/2473180550792405820775331154140160000000000000), (6845338413291415034149731686495398867743777/131902962708928310441350994887475200000000000), (2931431643342142047713849947113659922720463/63313422100285589011848477545988096000000000)]
    reserve := (46300319049/1000000000000) }

theorem mixed_014_019_valid : mixed_014_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_019]
  · intro i; fin_cases i <;> norm_num [mixed_014_019]
  · norm_num [mixed_014_019]
  · norm_num [mixed_014_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_019]

def mixed_014_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(8401489/100000000), (4989699/25000000), (4804527/25000000), (5391827/25000000), (5391827/25000000), (256357/12500000), (904517/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(673353/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4879113/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(163623/25000000), (5471783/100000000), (6197/5000000), (91241/1250000), (1/100000000), (4219899/100000000), (475111/25000000)]
    alternative := .zero
    polynomial := [(-99734477215519761499664472022469629960142683/183866586717772544085290973071662500000000000), (3415881709237/387312500000), (-1010095556703532461786685304379364415312622561/30644431119628757347548495511943750000000000), (3415881709237/387312500000), (-5960838863005675009220447354253716861915592683/183866586717772544085290973071662500000000000)]
    bernstein := [(41931078173556551339680811070263181140271707/772428245329227015972668539181056000000000000), (1706226263596096956652750301120631911328752671/28966059199846013098975070219289600000000000000), (40425127267541232006711943130339152337127377771/672426374282139589797635558662080000000000000000), (681309987342365213371612828385348845121372002439/11767461549937442821458622276586400000000000000000), (1535691186498595796629340392111035619727404395077/29418653874843607053646555691466000000000000000000)]
    reserve := (10440254629/200000000000) }

theorem mixed_014_020_valid : mixed_014_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_020]
  · intro i; fin_cases i <;> norm_num [mixed_014_020]
  · norm_num [mixed_014_020]
  · norm_num [mixed_014_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_020]

def mixed_014_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(4020951/50000000), (4121221/20000000), (19545843/100000000), (21593057/100000000), (21593057/100000000), (377643/20000000), (3365911/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(6524691/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9852421/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3607/500000), (5589221/100000000), (63531/50000000), (1471891/20000000), (1/100000000), (52443/1250000), (441661/25000000)]
    alternative := .zero
    polynomial := [(-35303645873688367410937617117859713986292293/44106251538719898952082850519900000000000000), (3491261163397/325800000000), (-750897599924212222275881776890495126853812293/22053125769359949476041425259950000000000000), (3491261163397/325800000000), (-1466491553974736077140825936663130539721332293/44106251538719898952082850519900000000000000)]
    bernstein := [(424778661090237036420619494789563445062246694667/7057000246195183832333256083184000000000000000000), (917973499784403636536731288746550210996915165823/14114000492390367664666512166368000000000000000000), (5620921443856077089175756420819627599410335764761/84684002954342205987999072998208000000000000000000), (3622353909440009325865135851875053557042516600103/56456001969561470658666048665472000000000000000000), (6588686648774606943883383945763336161423063542107/112912003939122941317332097330944000000000000000000)]
    reserve := (29176201019/500000000000) }

theorem mixed_014_021_valid : mixed_014_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_021]
  · intro i; fin_cases i <;> norm_num [mixed_014_021]
  · norm_num [mixed_014_021]
  · norm_num [mixed_014_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_021]

def mixed_014_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(1536749/20000000), (5324267/25000000), (794019/4000000), (21593887/100000000), (21593887/100000000), (1734091/100000000), (6246847/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1928791/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4964949/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(388363/50000000), (5720873/100000000), (521/400000), (1482297/20000000), (1/100000000), (4168051/100000000), (819071/50000000)]
    alternative := .zero
    polynomial := [(-654871601296923404275857823804635692583366246001/585770748857394624908895065135562300000000000000), (41484418995663/3256250000000), (-10342146965467611140852069368904764643215544796001/292885374428697312454447532567781150000000000000), (41484418995663/3256250000000), (-20029422329638298877428280914004893593847723346001/585770748857394624908895065135562300000000000000)]
    bernstein := [(99459076760297494237989080652286736379942634961614799/1499573117074930239766771366747039488000000000000000000), (4463749931492790985855798845205827120914687307400219/62482213211455426656948806947793312000000000000000000), (1281427055411466753365545841070068415347144552777357/17573122465721838747266851954066869000000000000000000), (34521103106987403633871588696180903074249020932103/488142290714495520757412554279635250000000000000000), (5929293814005800795602099089194004556451871155831/91526679508967910142014853927431609375000000000000)]
    reserve := (64782136157/1000000000000) }

theorem mixed_014_022_valid : mixed_014_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_022]
  · intro i; fin_cases i <;> norm_num [mixed_014_022]
  · norm_num [mixed_014_022]
  · norm_num [mixed_014_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_022]

def mixed_014_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(4549831/50000000), (27559223/100000000), (3147227/12500000), (27127361/100000000), (1923473/100000000), (970261/50000000), (3585971/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11206621/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(630097/50000000), 0, (1575243/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1019993/100000000), (1466689/20000000), (166983/100000000), (4675973/50000000), (1/100000000), (345197/50000000), (187737/10000000)]
    alternative := .zero
    polynomial := [(-1594310982863135672836163022394931507258874753533/841112054485275113494799587351910300000000000000), (62248190399491/3339660000000), (-58017533457503175019524684141991022388140382260599/1261668081727912670242199381027865450000000000000), (62248190399491/3339660000000), (-111252133966416943020540879216797250254504140260599/2523336163455825340484398762055730900000000000000)]
    bernstein := [(2168933622608336532508139858591292365467539112213/30328559656920977650052869736246765625000000000000), (1150034022244351072089293587065970513153224182873/14704756197295019466692300478180250000000000000000), (867032790465801628397745109956060674051865518261081/10814297843382108602075994694524561000000000000000000), (5677869803771243058705116212143549376842641635478539/73406142936896737177727963987075808000000000000000000), (149969756986967027689947143148881638091814108689836387/2153246859482304290546686943620890368000000000000000000)]
    reserve := (69648194923/1000000000000) }

theorem mixed_014_023_valid : mixed_014_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_023]
  · intro i; fin_cases i <;> norm_num [mixed_014_023]
  · norm_num [mixed_014_023]
  · norm_num [mixed_014_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_023]

def mixed_014_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![(8602713/100000000), (571913/2000000), (25541951/100000000), (5452839/20000000), (17/1000), (432607/25000000), (820633/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(160721/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(127821/10000000), 0, (6391049/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1055247/100000000), (7545441/100000000), (21433/12500000), (9439983/100000000), (1/100000000), (122589/20000000), (857759/50000000)]
    alternative := .zero
    polynomial := [(-14758912181807988674507395579610693879211652421/5975257870578493189224735594354180000000000000), (11560158167481/535825000000), (-143622544449406062772620540734787526861003927421/2987628935289246594612367797177090000000000000), (11560158167481/535825000000), (-272486176717004136870733685889964359842796202421/5975257870578493189224735594354180000000000000)]
    bernstein := [(1215563667890551965694790290563094178104497994632619/15296660148680942564415323121546700800000000000000000), (132462724852178140943053822765911531220155788020531/1529666014868094256441532312154670080000000000000000), (40746754141663814176803282513714452321779827522721/458899804460428276932459693646401024000000000000000), (1315194093100555202367912642968497818063324444467/15296660148680942564415323121546700800000000000000), (119409838408931464200148595551857791423922300331/1529666014868094256441532312154670080000000000000)]
    reserve := (15612537279/200000000000) }

theorem mixed_014_024_valid : mixed_014_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_024]
  · intro i; fin_cases i <;> norm_num [mixed_014_024]
  · norm_num [mixed_014_024]
  · norm_num [mixed_014_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_024]

def mixed_014_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, (17949483/50000000), (15635283/50000000), (8207617/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2126713/20000000), 0, 0], ![(8816001/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1641523/100000000), 0, (8207617/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (933179/10000000), (106397/50000000), (5728217/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1302572615901372155992822807109243/341244021854795802600000000000000), (158242660077483/5319850000000), (-10303626461304082979442645769109243/170622010927397901300000000000000), (158242660077483/5319850000000), (-19304680306706793802892468731109243/341244021854795802600000000000000)]
    bernstein := [(7757550702793850456277661941428773/87358469594827725465600000000000000), (28757701512463641711828308303143533/291194898649425751552000000000000000), (2687252250113901359654463417806128423/26207540878448317639680000000000000000), (2912995901525714722651776850652589429/29119489864942575155200000000000000000), (79606664601623983972680726271788603637/873584695948277254656000000000000000000)]
    reserve := (11100169707/125000000000) }

theorem mixed_014_025_valid : mixed_014_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_025]
  · intro i; fin_cases i <;> norm_num [mixed_014_025]
  · norm_num [mixed_014_025]
  · norm_num [mixed_014_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_025]

def mixed_014_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, (7344919/20000000), (31117059/100000000), (16079173/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5439061/50000000), 0, 0], ![(780179/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1607917/100000000), 0, (16079173/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (9546409/100000000), (214977/100000000), (11307057/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-151218833152678300452622318104043/32229169918195838612500000000000), (5730351560501/171981600000), (-143975419339764645118255500666649/2302083565585417043750000000000), (5730351560501/171981600000), (-1864437037604026731202954691229043/32229169918195838612500000000000)]
    bernstein := [(25568139385763867237214602475565155511/247520024971744040544000000000000000000), (34667302879850396887185801376693801/304827616960275912000000000000000000), (607312373992507999815549129820113873/5156667186911334178000000000000000000), (445972825902422060839338379743260087/3867500390183500633500000000000000000), (34230139033925980989796546038990117/322291699181958386125000000000000000)]
    reserve := (25824314001/250000000000) }

theorem mixed_014_026_valid : mixed_014_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_026]
  · intro i; fin_cases i <;> norm_num [mixed_014_026]
  · norm_num [mixed_014_026]
  · norm_num [mixed_014_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_026]

def mixed_014_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2962081/10000000), 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (812331/3125000), (577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-229823287470729909864305101/15012318788064000000000000), (56939502/577517), (-1298284279348905909864305101/7506159394032000000000000), (56939502/577517), (-2366745271227081909864305101/15012318788064000000000000)]
    bernstein := [(13138588271588308902191095019/150123187880640000000000000000), (69104768566036171083136612049/600492751522560000000000000000), (900737018833400756137339380437/7205913018270720000000000000000), (1123388895539770296569437309309/9607884024360960000000000000000), (3475613136074926185128324829539/38431536097443840000000000000000)]
    reserve := (87518713511/1000000000000) }

theorem mixed_014_027_valid : mixed_014_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_027]
  · intro i; fin_cases i <;> norm_num [mixed_014_027]
  · norm_num [mixed_014_027]
  · norm_num [mixed_014_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_027]

def mixed_014_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2962081/10000000), 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (812331/3125000), (71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-33001336618930860110602801/1849593204576000000000000), (60597559/569224), (-162240475785418860110602801/924796602288000000000000), (60597559/569224), (-291479614951906860110602801/1849593204576000000000000)]
    bernstein := [(577366111911772817423908059839/4734958603714560000000000000000), (39504985418009181970020858069/263053255761920000000000000000), (570164505889119181559372097557/3551218952785920000000000000000), (10040759707352501223594892749/65763313940480000000000000000), (37320256698406454842364715599/295934912732160000000000000000)]
    reserve := (15242110867/125000000000) }

theorem mixed_014_028_valid : mixed_014_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_028]
  · intro i; fin_cases i <;> norm_num [mixed_014_028]
  · norm_num [mixed_014_028]
  · norm_num [mixed_014_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_028]

def mixed_014_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2962081/10000000), 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (812331/3125000), (560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-59958801475902553849305923/2914217316691200000000000), (64079547/560543), (-259522310030411353849305923/1457108658345600000000000), (64079547/560543), (-459085818584920153849305923/2914217316691200000000000)]
    bernstein := [(72505118810180351826076617277/466274770670592000000000000000), (34406218523311005620756943713/186509908268236800000000000000), (43719098275374436767077075023/223811889921884160000000000000), (5600598990409757589120839401/29841585322917888000000000000), (1921973299653056937048736333/11936634129167155200000000000)]
    reserve := (31099739197/200000000000) }

theorem mixed_014_029_valid : mixed_014_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_014_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_014_029]
  · intro i; fin_cases i <;> norm_num [mixed_014_029]
  · norm_num [mixed_014_029]
  · norm_num [mixed_014_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_014_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_014_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_014_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_014_029]

def mixedTable014 : OwnerTable where
  mode := .mixed
  owners := ![0, 3, 0, 2, 0, 2, 3]
  rows := [mixed_014_000, mixed_014_001, mixed_014_002, mixed_014_003, mixed_014_004, mixed_014_005, mixed_014_006, mixed_014_007, mixed_014_008, mixed_014_009, mixed_014_010, mixed_014_011, mixed_014_012, mixed_014_013, mixed_014_014, mixed_014_015, mixed_014_016, mixed_014_017, mixed_014_018, mixed_014_019, mixed_014_020, mixed_014_021, mixed_014_022, mixed_014_023, mixed_014_024, mixed_014_025, mixed_014_026, mixed_014_027, mixed_014_028, mixed_014_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_014_000_valid
    · exact mixed_014_001_valid
    · exact mixed_014_002_valid
    · exact mixed_014_003_valid
    · exact mixed_014_004_valid
    · exact mixed_014_005_valid
    · exact mixed_014_006_valid
    · exact mixed_014_007_valid
    · exact mixed_014_008_valid
    · exact mixed_014_009_valid
    · exact mixed_014_010_valid
    · exact mixed_014_011_valid
    · exact mixed_014_012_valid
    · exact mixed_014_013_valid
    · exact mixed_014_014_valid
    · exact mixed_014_015_valid
    · exact mixed_014_016_valid
    · exact mixed_014_017_valid
    · exact mixed_014_018_valid
    · exact mixed_014_019_valid
    · exact mixed_014_020_valid
    · exact mixed_014_021_valid
    · exact mixed_014_022_valid
    · exact mixed_014_023_valid
    · exact mixed_014_024_valid
    · exact mixed_014_025_valid
    · exact mixed_014_026_valid
    · exact mixed_014_027_valid
    · exact mixed_014_028_valid
    · exact mixed_014_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
