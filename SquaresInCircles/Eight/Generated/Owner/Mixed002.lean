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

def mixed_002_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9323878086264272438164777/457463486508250000000000), (-64079547/560543), (-40650649044724772438164777/228731743254125000000000), (-64079547/560543), (-71977420003185272438164777/457463486508250000000000)]
    bernstein := [(771944384308161177019903367/1873770440737792000000000000), (2045099281096760524528801499/4684426101844480000000000000), (15536936375244992100840585677/35133195763833600000000000000), (12572278001133635972786737987/29277663136528000000000000000), (29171204288533746193542792023/73194157841320000000000000000)]
    reserve := (39854552807/100000000000) }

theorem mixed_002_000_valid : mixed_002_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_000]
  · intro i; fin_cases i <;> norm_num [mixed_002_000]
  · norm_num [mixed_002_000]
  · norm_num [mixed_002_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_000]

def mixed_002_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8195479695018141692827207/464548117886000000000000), (-60597559/569224), (-40655481552973641692827207/232274058943000000000000), (-60597559/569224), (-73115483410929141692827207/464548117886000000000000)]
    bernstein := [(28165181448433940584342241593/74327698861760000000000000000), (59987255907906319759240394787/148655397723520000000000000000), (365240093712578782092801356099/891932386341120000000000000000), (236219105813974844491305697947/594621590894080000000000000000), (436708267205816752992558675273/1189243181788160000000000000000)]
    reserve := (367215279341/1000000000000) }

theorem mixed_002_001_valid : mixed_002_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_001]
  · intro i; fin_cases i <;> norm_num [mixed_002_001]
  · norm_num [mixed_002_001]
  · norm_num [mixed_002_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_001]

def mixed_002_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1423459636141088562438957/94263219891350000000000), (-56939502/577517), (-8132388139765738562438957/47131609945675000000000), (-56939502/577517), (-14841316643390388562438957/94263219891350000000000)]
    bernstein := [(83203201243560805857463083523/241313842921856000000000000000), (22285963806524996156967944413/60328460730464000000000000000), (16997892937923406218361408309/45246345547848000000000000000), (1372467533604261648733468593/3770528795654000000000000000), (315533175520850489662751883/942632198913500000000000000)]
    reserve := (334736258621/1000000000000) }

theorem mixed_002_002_valid : mixed_002_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_002]
  · intro i; fin_cases i <;> norm_num [mixed_002_002]
  · norm_num [mixed_002_002]
  · norm_num [mixed_002_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_002]

def mixed_002_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(15722243/50000000), (15722243/50000000), 0, 0, 0, 0, (9277757/25000000)]
    cone := fun i => (![![(1970971/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9691711/100000000), 0, 0]] i.1) i.2
    mu := ![(5431/2500000), (1/100000000), (7945393/100000000), (1/100000000), (1/100000000), (1/100000000), (9691711/100000000)]
    alternative := .zero
    polynomial := [(-97427442093932945207046865603009/20910559140847215650000000000000), (-18627739998979/543100000000), (-665623663029850184233480588253009/10455279570423607825000000000000), (-18627739998979/543100000000), (-1233819883965767423259914310903009/20910559140847215650000000000000)]
    bernstein := [(72938516328398226337487202226350071/209105591408472156500000000000000000), (297040296848047980163714956951934227/836422365633888626000000000000000000), (3560317263217994524153347064894435897/10037068387606663512000000000000000000), (4653308285179613358664312147407764263/13382757850142218016000000000000000000), (17891602133044360177812933577340920431/53531031400568872064000000000000000000)]
    reserve := (334228608433/1000000000000) }

theorem mixed_002_003_valid : mixed_002_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_003]
  · intro i; fin_cases i <;> norm_num [mixed_002_003]
  · norm_num [mixed_002_003]
  · norm_num [mixed_002_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_003]

def mixed_002_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(15883043/50000000), (15883043/50000000), 0, 0, 0, 0, (36467829/100000000)]
    cone := fun i => (![![(17911403/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9523737/100000000), 0, 0]] i.1) i.2
    mu := ![(108083/50000000), (1/100000000), (1605331/20000000), (1/100000000), (1/100000000), (1/100000000), (9523737/100000000)]
    alternative := .zero
    polynomial := [(-1935508050436792556005076650539/510016664321098025000000000000), (-666923477246639/21616600000000), (-15763494741822963667187576775539/255008332160549012500000000000), (-666923477246639/21616600000000), (-29591481433209134778370076900539/510016664321098025000000000000)]
    bernstein := [(423567913941451451508303397145667701/1305642660662010944000000000000000000), (43150919601403928959912770780102151/130564266066201094400000000000000000), (12927733840993080171451287267858679/39169279819860328320000000000000000), (421981864034003895916378933008127/1305642660662010944000000000000000), (1395930919209213955616163249801/4502216071248313600000000000000)]
    reserve := (310054181567/1000000000000) }

theorem mixed_002_004_valid : mixed_002_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_004]
  · intro i; fin_cases i <;> norm_num [mixed_002_004]
  · norm_num [mixed_002_004]
  · norm_num [mixed_002_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_004]

def mixed_002_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(16027921/50000000), (16027921/50000000), 0, 0, 0, 0, (35888317/100000000)]
    cone := fun i => (![![(8068369/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4686197/50000000), 0, 0]] i.1) i.2
    mu := ![(26899/12500000), (1/100000000), (809987/10000000), (1/100000000), (1/100000000), (1/100000000), (1874479/20000000)]
    alternative := .zero
    polynomial := [(-3099065681464512134221816735371/1021021228051798175000000000000), (-296458345096637/10759600000000), (-30718587144192753511002161516621/510510614025899087500000000000), (-296458345096637/10759600000000), (-58338108606920994887782506297871/1021021228051798175000000000000)]
    bernstein := [(2115941874337152992541680950413/7064363091385414400000000000000), (798223883779000208125284628529117/2613814343812603328000000000000000), (23908759168619162424258391084378171/78414430314378099840000000000000000), (1900987363423940918490966039489341/6375156936128300800000000000000000), (18190393799855559164374021166932809/63751569361283008000000000000000000)]
    reserve := (8916640201/31250000000) }

theorem mixed_002_005_valid : mixed_002_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_005]
  · intro i; fin_cases i <;> norm_num [mixed_002_005]
  · norm_num [mixed_002_005]
  · norm_num [mixed_002_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_005]

def mixed_002_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(16157263/50000000), (16157263/50000000), 0, 0, 0, 0, (8842737/25000000)]
    cone := fun i => (![![(14383163/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9237281/100000000), 0, 0]] i.1) i.2
    mu := ![(107157/50000000), (1/100000000), (4082617/50000000), (1/100000000), (1/100000000), (1/100000000), (4618641/50000000)]
    alternative := .zero
    polynomial := [(-13317981786141283540765596505489/5612687879248744525000000000000), (-43549751766571/1785950000000), (-164801724598247959535910409505489/2806343939624372262500000000000), (-43549751766571/1785950000000), (-316285467410354635531055222505489/5612687879248744525000000000000)]
    bernstein := [(3938457215748743902502336744086897871/14368480970876785984000000000000000000), (45679340400644548719253501789061829/163278192850872568000000000000000000), (6716900772707989361549090362118491/24054376625351762250000000000000000), (347769484199210679801547534894217/1275610881647441937500000000000000), (228032460357966882897091717822359/876982481132616332031250000000000)]
    reserve := (32502425257/125000000000) }

theorem mixed_002_006_valid : mixed_002_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_006]
  · intro i; fin_cases i <;> norm_num [mixed_002_006]
  · norm_num [mixed_002_006]
  · norm_num [mixed_002_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_006]

def mixed_002_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(32542819/100000000), (32542819/100000000), 0, 0, 0, 0, (34914361/100000000)]
    cone := fun i => (![![(12648221/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4559021/50000000), 0, 0]] i.1) i.2
    mu := ![(53383/25000000), (1/100000000), (205573/2500000), (1/100000000), (1/100000000), (1/100000000), (4559021/50000000)]
    alternative := .zero
    polynomial := [(-9012107220213874164078179170541/5003116812575363900000000000000), (-455502420455197/21353200000000), (-143749117620066820191583613545541/2501558406287681950000000000000), (-455502420455197/21353200000000), (-278486128019919766219089047920541/5003116812575363900000000000000)]
    bernstein := [(193952820795209801228431768928571/781737001964900609375000000000000), (3171655202871375044912593929261669/12507792031438409750000000000000000), (37973597084104445031565210375988137/150093504377260917000000000000000000), (394599964979335760952108968289710937/1600997380024116448000000000000000000), (2997815381201683375175238815846992259/12807979040192931584000000000000000000)]
    reserve := (14628651463/62500000000) }

theorem mixed_002_007_valid : mixed_002_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_007]
  · intro i; fin_cases i <;> norm_num [mixed_002_007]
  · norm_num [mixed_002_007]
  · norm_num [mixed_002_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_007]

def mixed_002_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(32741317/100000000), (32741317/100000000), 0, 0, 0, 0, (17258683/50000000)]
    cone := fun i => (![![(85387/781250), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1802873/20000000), 0, 0]] i.1) i.2
    mu := ![(106421/50000000), (1/100000000), (2068269/25000000), (1/100000000), (1/100000000), (1/100000000), (1802873/20000000)]
    alternative := .zero
    polynomial := [(-11278754110570617067941568267/8576300574725100000000000000), (-97799062277001/5321050000000), (-241778059433308279986029068267/4288150287362550000000000000), (-97799062277001/5321050000000), (-472277364756045942904116568267/8576300574725100000000000000)]
    bernstein := [(4862318776998450662836998091805333/21955329471296256000000000000000000), (2489218894370896192597912249655657/10977664735648128000000000000000000), (531914467867974744691829825560337/2352356729067456000000000000000000), (86113217110495468553993998313191/392059454844576000000000000000000), (284569408296772630334723823727973/1372208091956016000000000000000000)]
    reserve := (5184516291/25000000000) }

theorem mixed_002_008_valid : mixed_002_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_008]
  · intro i; fin_cases i <;> norm_num [mixed_002_008]
  · norm_num [mixed_002_008]
  · norm_num [mixed_002_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_008]

def mixed_002_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(3291053/10000000), (3291053/10000000), 0, 0, 0, 0, (1708947/5000000)]
    cone := fun i => (![![(4612401/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8925983/100000000), 0, 0]] i.1) i.2
    mu := ![(42449/20000000), (1/100000000), (8315833/100000000), (1/100000000), (1/100000000), (1/100000000), (278937/3125000)]
    alternative := .zero
    polynomial := [(-210703740241141618128641693849/231680999730957480000000000000), (-16463207247479/1061225000000), (-109245684969532300944727944795433/1969288497713138580000000000000), (-16463207247479/1061225000000), (-214909406354965194381268980795433/3938576995426277160000000000000)]
    bernstein := [(122320849708381678004618759335172327/630172319268204345600000000000000000), (50217808534127415402045530672468189/252068927707281738240000000000000000), (60048662087887104223345797456894941/302482713248738085888000000000000000), (1549232983429458233050774293837473/8066205686633015623680000000000000), (116091735058546878185197789891823/645296454930641249894400000000000)]
    reserve := (179904498423/1000000000000) }

theorem mixed_002_009_valid : mixed_002_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_009]
  · intro i; fin_cases i <;> norm_num [mixed_002_009]
  · norm_num [mixed_002_009]
  · norm_num [mixed_002_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_009]

def mixed_002_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(8262723/25000000), (8262723/25000000), 0, 0, 0, 0, (4237277/12500000)]
    cone := fun i => (![![(301271/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1072127/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8852671/100000000), 0, 0]] i.1) i.2
    mu := ![(211737/100000000), (1/100000000), (4211039/50000000), (1/100000000), (1/100000000), (1/100000000), (8852671/100000000)]
    alternative := .zero
    polynomial := [(-32437747313177186515151639883359/56380939422072703950000000000000), (-80737370781967606997/6368805462450000000), (-1542717520630811051234523929883359/28190469711036351975000000000000), (-80737370781967606997/6368805462450000000), (-3052997293948444915953896219883359/56380939422072703950000000000000)]
    bernstein := [(510395535442338698784935960437443/3079151038304130605056000000000000), (3290164989325598699124689810640991/19244693989400816281600000000000000), (184500379830747406201320408085311367/1082514036903795915840000000000000000), (24692029134367690375804445553580007/150349171792193877200000000000000000), (85914820195267156661381295839854841/563809394220727039500000000000000000)]
    reserve := (76191369881/500000000000) }

theorem mixed_002_010_valid : mixed_002_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_010]
  · intro i; fin_cases i <;> norm_num [mixed_002_010]
  · norm_num [mixed_002_010]
  · norm_num [mixed_002_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_010]

def mixed_002_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(33162759/100000000), (33162759/100000000), 0, 0, 0, 0, (16837241/50000000)]
    cone := fun i => (![![(5848259/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2769607/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4397121/50000000), 0, 0]] i.1) i.2
    mu := ![(211319/100000000), (1/100000000), (8545721/100000000), (1/100000000), (1/100000000), (1/100000000), (4397121/50000000)]
    alternative := .zero
    polynomial := [(-248482714149656545419435454186811/794064304140673887900000000000000), (-1783335735675945017233/180587321599900000000), (-21493421486467319936468262094186811/397032152070336943950000000000000), (-1783335735675945017233/180587321599900000000), (-42738360258784983327517088734186811/794064304140673887900000000000000)]
    bernstein := [(1093708644476244075606268005490340989/7940643041406738879000000000000000000), (4547717760862272919143364375416731867/31762572165626955516000000000000000000), (54487277241612614692162312063738955803/381150865987523466192000000000000000000), (69679144194266286604321126209586203703/508201154650031288256000000000000000000), (255457030811221514482113186926154551509/2032804618600125153024000000000000000000)]
    reserve := (6283364089/50000000000) }

theorem mixed_002_011_valid : mixed_002_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_011]
  · intro i; fin_cases i <;> norm_num [mixed_002_011]
  · norm_num [mixed_002_011]
  · norm_num [mixed_002_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_011]

def mixed_002_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(6649283/20000000), (6649283/20000000), 0, 0, 0, 0, (33507171/100000000)]
    cone := fun i => (![![(4172099/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4475251/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2187637/25000000), 0, 0]] i.1) i.2
    mu := ![(210989/100000000), (1/100000000), (8642019/100000000), (1/100000000), (1/100000000), (1/100000000), (2187637/25000000)]
    alternative := .zero
    polynomial := [(-9793419608797323361402199460311/79777474958500457340000000000000), (-324490486945973288749/45584273669775000000), (-2142387824797085865632722299960311/39888737479250228670000000000000), (-324490486945973288749/45584273669775000000), (-4274982229985374407904042400460311/79777474958500457340000000000000)]
    bernstein := [(22530760248373738799023395306741598009/204230335893761170790400000000000000000), (11845006154599866717583629042277759603/102115167946880585395200000000000000000), (17776692243782137444006143300657848803/153172751920320878092800000000000000000), (940609929309579840309586433916825689/8509597328906715449600000000000000000), (423125609784536972602268421663176963/4254798664453357724800000000000000000)]
    reserve := (49723341003/500000000000) }

theorem mixed_002_012_valid : mixed_002_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_012]
  · intro i; fin_cases i <;> norm_num [mixed_002_012]
  · norm_num [mixed_002_012]
  · norm_num [mixed_002_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_012]

def mixed_002_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(29193997/100000000), (29193997/100000000), (6022007/100000000), (6313779/100000000), 0, 0, (29276221/100000000)]
    cone := fun i => (![![(2192633/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(315689/100000000), 0, (6313779/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (477851/6250000), 0, 0]] i.1) i.2
    mu := ![(184751/100000000), (1/100000000), (7679259/100000000), (2204673/100000000), (1/100000000), (1/100000000), (7645617/100000000)]
    alternative := .zero
    polynomial := [(77816543777244849436048371009893/6276398404211327386771875000000000), (-19403737538429008643/5066967069675000000), (-73466504318940920934126921010799741/1569099601052831846692968750000000), (-19403737538429008643/5066967069675000000), (-293943833819540928585943732414208857/6276398404211327386771875000000000)]
    bernstein := [(262117897690276744897798202673639756629/3012671234021437145650500000000000000000), (185381476299747292363251909762154047743/2008447489347624763767000000000000000000), (159596020857154864265536906709984768147/1721526419440821226086000000000000000000), (708921404724285638577210326235310699343/8033789957390499055068000000000000000000), (3803835739610691654964501765561325586229/48202739744342994330408000000000000000000)]
    reserve := (78913268411/1000000000000) }

theorem mixed_002_013_valid : mixed_002_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_013]
  · intro i; fin_cases i <;> norm_num [mixed_002_013]
  · norm_num [mixed_002_013]
  · norm_num [mixed_002_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_013]

def mixed_002_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(1212391/5000000), (1212391/5000000), (170033/2500000), (3672453/50000000), (6525021/100000000), (1315543/20000000), (12127699/50000000)]
    cone := fun i => (![![(60629/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(20497/50000000), 0, (163977/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(15321/10000000), (1/100000000), (128911/2000000), (2529397/100000000), (1/100000000), (585277/25000000), (6350219/100000000)]
    alternative := .zero
    polynomial := [(23194710328647572726567604167603363758831/371342148232804326672293018820000000000000), (-117410587527708797/98752271550000000), (-7194364339103618856206243525922768875841169/185671074116402163336146509410000000000000), (-117410587527708797/98752271550000000), (-4803974462845295095046351552004380371813723/123780716077601442224097672940000000000000)]
    bernstein := [(64615981812279482239253868748940130932672178031/950635899475979076281070128179200000000000000000), (43165044567529280842628516279768238920205931/594147437172486922675668830112000000000000000), (130630471202922355731992135695454445174547631/1782442311517460768027006490336000000000000000), (25954108866618158716221133252695141676331/371342148232804326672293018820000000000000), (23194710328647572726567604167603363758831/371342148232804326672293018820000000000000)]
    reserve := (31230915261/500000000000) }

theorem mixed_002_014_valid : mixed_002_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_014]
  · intro i; fin_cases i <;> norm_num [mixed_002_014]
  · norm_num [mixed_002_014]
  · norm_num [mixed_002_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_014]

def mixed_002_015 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(22530597/100000000), (22530597/100000000), (1540207/20000000), (1689707/20000000), (1689707/20000000), (1654169/25000000), (11862013/50000000)]
    cone := fun i => (![![0, 0, (37063/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (915929/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(149853/100000000), (1/100000000), (1203281/20000000), (2888561/100000000), (1/100000000), (168233/6250000), (622337/10000000)]
    alternative := .zero
    polynomial := [(10061865443856985335882237075596456059099/209738186136603103735899622050000000000000), (30684178040632130371/18031526769300000000), (-1324905542322518558735072685537487409646967/34956364356100517289316603675000000000000), (30684178040632130371/18031526769300000000), (-7959495119378968337746318350300520913940901/209738186136603103735899622050000000000000)]
    bernstein := [(10061865443856985335882237075596456059099/209738186136603103735899622050000000000000), (323488341411592262236792995782836863973/5519425950963239571997358475000000000000), (21912292063155923991847376280701145554911433/335581097818564965977439395280000000000000000), (11416909058847151700795890814516236857694687/167790548909282482988719697640000000000000000), (35887880525632191101837207418217086928308615899/536929756509703945563903032448000000000000000000)]
    reserve := (9594691009/200000000000) }

theorem mixed_002_015_valid : mixed_002_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_015]
  · intro i; fin_cases i <;> norm_num [mixed_002_015]
  · norm_num [mixed_002_015]
  · norm_num [mixed_002_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_015]

def mixed_002_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(21025857/100000000), (21025857/100000000), (8211689/100000000), (900351/10000000), (900351/10000000), (21617/312500), (24812137/100000000)]
    cone := fun i => (![![0, 0, (1858297/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (208607/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(7829/5000000), (1/100000000), (2803107/50000000), (1539561/50000000), (1/100000000), (177789/6250000), (6508623/100000000)]
    alternative := .zero
    polynomial := [(-3114203378847041625792731158870577567041/144801516306637008142083246300000000000000), (54848182508607538111/14630349802000000000), (-2872222162429666526252630136835445105792041/72400758153318504071041623150000000000000), (54848182508607538111/14630349802000000000), (-5741330121480486010879467542512019634017041/144801516306637008142083246300000000000000)]
    bernstein := [(17594965024452051347468417251194671271192491759/370691881744990740843733110528000000000000000000), (3615928289242693561920805791289780837371784853/61781980290831790140622185088000000000000000000), (18202078737255102170820899241966024319679115677/278018911308743055632799832896000000000000000000), (1054844081123517187344281041016537902226221253/15445495072707947535155546272000000000000000000), (1551873404816746641943989267129812553898790159/23168242609061921302733319408000000000000000000)]
    reserve := (47465201939/1000000000000) }

theorem mixed_002_016_valid : mixed_002_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_016]
  · intro i; fin_cases i <;> norm_num [mixed_002_016]
  · norm_num [mixed_002_016]
  · norm_num [mixed_002_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_016]

def mixed_002_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(1946337/10000000), (1946337/10000000), (8599643/100000000), (296211/3125000), (296211/3125000), (7327181/100000000), (6547233/25000000)]
    cone := fun i => (![![0, 0, (6521757/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (537893/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(41227/25000000), (1/100000000), (5174603/100000000), (646783/20000000), (1/100000000), (1501373/50000000), (3435769/50000000)]
    alternative := .zero
    polynomial := [(-2162422522679090211105799687110004737393439/14235080243411631750169938417020000000000000), (257101647110759497251/42666671576200000000), (-298651230628556536199657439489405922149693439/7117540121705815875084969208510000000000000), (257101647110759497251/42666671576200000000), (-595140038734433982188209079291701839561993439/14235080243411631750169938417020000000000000)]
    bernstein := [(102435986503908858186917966965558765788775015361/2277612838945861080027190146723200000000000000000), (257659049579056934013418983010123506527992161683/4555225677891722160054380293446400000000000000000), (1744004185112732575617167233182837578943405399947/27331354067350332960326281760678400000000000000000), (1215421417365748638274059304169654531430103489147/18220902711566888640217521173785600000000000000000), (2376856520452674224711668343690255874329371648241/36441805423133777280435042347571200000000000000000)]
    reserve := (22487576631/500000000000) }

theorem mixed_002_017_valid : mixed_002_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_017]
  · intro i; fin_cases i <;> norm_num [mixed_002_017]
  · norm_num [mixed_002_017]
  · norm_num [mixed_002_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_017]

def mixed_002_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(21091779/100000000), (21091779/100000000), (10359283/100000000), (573281/5000000), (573281/5000000), (1343339/25000000), (4788141/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (761533/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(140399/12500000), (1/100000000), (2788069/50000000), (3904501/100000000), (1/100000000), (60173/2000000), (5026323/100000000)]
    alternative := .zero
    polynomial := [(1342867130951132372327084392418367328589879/46225873714298155416187538124900000000000000), (432090387470121/557613800000000), (-91533830893728730210491894351558099564660121/23112936857149077708093769062450000000000000), (432090387470121/557613800000000), (-184410528918408592793310873095534566457910121/46225873714298155416187538124900000000000000)]
    bernstein := [(7702764041774062036016096368914629416700928035399/118338236708603277865440097599744000000000000000000), (1960303706527584214773654691771393630338557720333/29584559177150819466360024399936000000000000000000), (1487125701694331041595422158375086761419466963433/22188419382863114599770018299952000000000000000000), (124577121242066750687500522140180586342875594937/1849034948571926216647501524996000000000000000000), (31115747796440866549672695267336042470713855679/462258737142981554161875381249000000000000000000)]
    reserve := (65091083457/1000000000000) }

theorem mixed_002_018_valid : mixed_002_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_018]
  · intro i; fin_cases i <;> norm_num [mixed_002_018]
  · norm_num [mixed_002_018]
  · norm_num [mixed_002_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_018]

def mixed_002_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(10300547/50000000), (10300547/50000000), (5523043/50000000), (2443857/20000000), (2443857/20000000), (5106243/100000000), (9103457/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (3556521/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(271271/20000000), (1/100000000), (539753/10000000), (2081073/50000000), (1/100000000), (3095583/100000000), (1194507/25000000)]
    alternative := .zero
    polynomial := [(115825342570128930377420501590628338117673/6259568478733277394224882894550000000000000), (106026546265731/134938250000000), (-9828725781019992042321368341916387910682327/3129784239366638697112441447275000000000000), (106026546265731/134938250000000), (-19773276904610113015020157185423404159482327/6259568478733277394224882894550000000000000)]
    bernstein := [(318486155874023750094946100215380721384214021/4815052675948674918634525303500000000000000000), (41543512380253590383984434814765975230584973/618228985553903940170358804400000000000000000), (8163966507088450528262862764620219152462428351/120183714791678925969117751575360000000000000000), (5407679495299896127217845003674145975389749/79133310150899704341805926963200000000000000), (5397350641630483894245783636681091770249749/78889823042743089866908062572544000000000000)]
    reserve := (66143857047/1000000000000) }

theorem mixed_002_019_valid : mixed_002_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_019]
  · intro i; fin_cases i <;> norm_num [mixed_002_019]
  · norm_num [mixed_002_019]
  · norm_num [mixed_002_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_019]

def mixed_002_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(20161923/100000000), (20161923/100000000), (2335443/20000000), (3224907/25000000), (3224907/25000000), (2429433/50000000), (1083801/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4020381/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(393141/25000000), (1/100000000), (5221093/100000000), (549577/12500000), (1/100000000), (3172941/100000000), (4550433/100000000)]
    alternative := .zero
    polynomial := [(22078632687374037518066981882447400958293/2872565750489698926291131885900000000000000), (416511135748221/522109300000000), (-3750337436227187853845198186900411810041707/1436282875244849463145565942950000000000000), (416511135748221/522109300000000), (-7522753505141749745208463355683271021041707/2872565750489698926291131885900000000000000)]
    bernstein := [(31779605044369042783876231086622075663151517/470641172560232272083539048185856000000000000), (403197810212854694123299664540974553271222867/5883014657002903401044238102323200000000000000), (5094791059856317498919944315296224796593997613/73537683212536292513052976279040000000000000000), (12824679012924212499942471436437346994299519431/183844208031340731282632440697600000000000000000), (4593742907558799428638534322904355285534601619/65658645725478832600940157392000000000000000000)]
    reserve := (67524064823/1000000000000) }

theorem mixed_002_020_valid : mixed_002_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_020]
  · intro i; fin_cases i <;> norm_num [mixed_002_020]
  · norm_num [mixed_002_020]
  · norm_num [mixed_002_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_020]

def mixed_002_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(1977053/10000000), (1977053/10000000), (3064727/25000000), (6756779/50000000), (6756779/50000000), (925803/20000000), (165439/1000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4442271/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(13859/781250), (1/100000000), (630859/12500000), (922053/20000000), (1/100000000), (648313/20000000), (2170433/50000000)]
    alternative := .zero
    polynomial := [(-1568103866214470092289527997101230590599/453744306512680882770416543880000000000000), (10233874993571/12617180000000), (-509583147773179863862736815559091139903099/226872153256340441385208271940000000000000), (10233874993571/12617180000000), (-1017598191680145257633184103121081049215599/453744306512680882770416543880000000000000)]
    bernstein := [(5029255578264371012097644622613231697655383681/72599089042028941243266647020800000000000000000), (10205290728072050524845203270780927186208227389/145198178084057882486533294041600000000000000000), (61914236527924700460332143748803441535084063723/871189068504347294919199764249600000000000000000), (41597816324997899071022474047265525024694821429/580792712336231529946133176166400000000000000000), (83568834824469589341749199906771509632013983601/1161585424672463059892266352332800000000000000000)]
    reserve := (34637181021/500000000000) }

theorem mixed_002_021_valid : mixed_002_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_021]
  · intro i; fin_cases i <;> norm_num [mixed_002_021]
  · norm_num [mixed_002_021]
  · norm_num [mixed_002_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_021]

def mixed_002_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(4855859/25000000), (4855859/25000000), (12796611/100000000), (14067429/100000000), (14067429/100000000), (220733/5000000), (15806999/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (301649/6250000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1962357/100000000), (1/100000000), (243743/5000000), (4805213/100000000), (1/100000000), (3302227/100000000), (4146959/100000000)]
    alternative := .zero
    polynomial := [(-1966021368367427332484668321785775554371051/131143943344741117592248211474412500000000000), (100666992266419/121871500000000), (-390093611521800351816865976052319593020363153/196715915017111676388372317211618750000000000), (100666992266419/121871500000000), (-774289158938498421636277947139281859377613153/393431830034223352776744634423237500000000000)]
    bernstein := [(71924213131295562521439783775239231814919257749247/1007185484887611783108466264123488000000000000000000), (9120869409572749069989684333194796321300805796771/125898185610951472888558283015436000000000000000000), (432475806421560155142075451881127238518628531873/5901477450513350291651169516348562500000000000000), (72703896434352134311257050208110398914605317777/983579575085558381941861586058093750000000000000), (4570481427325574492995122896435120416015314643/61473723442847398871366349128630859375000000000)]
    reserve := (2231596557/31250000000) }

theorem mixed_002_022_valid : mixed_002_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_022]
  · intro i; fin_cases i <;> norm_num [mixed_002_022]
  · norm_num [mixed_002_022]
  · norm_num [mixed_002_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_022]

def mixed_002_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(19117443/100000000), (19117443/100000000), (332377/2500000), (7283519/50000000), (7283519/50000000), (4213949/100000000), (15122007/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1035309/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1069677/50000000), (1/100000000), (4705021/100000000), (2491679/50000000), (1/100000000), (209727/6250000), (3966613/100000000)]
    alternative := .zero
    polynomial := [(-31939817409136730350629930148443971631007/1182801607982420512013956258650000000000000), (198233327537367/235251050000000), (-1057229995442920465060531452753625284756007/591400803991210256006978129325000000000000), (198233327537367/235251050000000), (-2082520173476704199770432975358806597881007/1182801607982420512013956258650000000000000)]
    bernstein := [(13665592769220859354011437193346111531234817/184812751247253205002180665414062500000000000), (11675515790248966316214619704776511520203499/155631790524002698949204770875000000000000000), (2693940591497601949051896994974154681995699881/35484048239472615360418687759500000000000000000), (1526728055109564040524435775972324462403549563/19920869187072345465498210672000000000000000000), (233689261069090256957049096860175258373527778673/3027972116434996510755728022144000000000000000000)]
    reserve := (3697145537/50000000000) }

theorem mixed_002_023_valid : mixed_002_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_023]
  · intro i; fin_cases i <;> norm_num [mixed_002_023]
  · norm_num [mixed_002_023]
  · norm_num [mixed_002_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_023]

def mixed_002_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(3769929/20000000), (3769929/20000000), (13758483/100000000), (7508819/50000000), (7508819/50000000), (2012599/50000000), (1810219/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (274811/5000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1153147/50000000), (1/100000000), (4537303/100000000), (6433/125000), (1/100000000), (3402417/100000000), (3797969/100000000)]
    alternative := .zero
    polynomial := [(-32798881264186785213370489677830079488787/828467848910722460490961827560000000000000), (390758713878247/453730300000000), (-679254658709939011155731873948521989488787/414233924455361230245480913780000000000000), (390758713878247/453730300000000), (-1325710436155691237098093258219213899488787/828467848910722460490961827560000000000000)]
    bernstein := [(163048344087447597139043148613740628614169758093/2120877693211449498856862278553600000000000000000), (16545021415015491990044260962849054851329589957/212087769321144949885686227855360000000000000000), (1675108603192653880090098596505984545906947629/21208776932114494988568622785536000000000000000), (169225486078800473788610411668187389897114949/2120877693211449498856862278553600000000000000), (17058796920234549387187268057612217826940557/212087769321144949885686227855360000000000000)]
    reserve := (9609721049/125000000000) }

theorem mixed_002_024_valid : mixed_002_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_024]
  · intro i; fin_cases i <;> norm_num [mixed_002_024]
  · norm_num [mixed_002_024]
  · norm_num [mixed_002_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_024]

def mixed_002_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![(842159/4000000), (842159/4000000), (8026687/50000000), (8731873/50000000), (4337859/100000000), (2171239/50000000), (61307/390625)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(328147/50000000), 0, (6562943/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(348369/12500000), (1/100000000), (2472119/50000000), (2996931/50000000), (1/100000000), (387733/25000000), (4114709/100000000)]
    alternative := .zero
    polynomial := [(-54275697255605958715357991832453272304913/784328880672236708746122242148000000000000), (246591465591721/247211900000000), (-684375879488413398860331232192397439304913/392164440336118354373061121074000000000000), (246591465591721/247211900000000), (-62594098177200992333585927264397219347853/37348994317725557559339154388000000000000)]
    bernstein := [(1237802037214335059559113486423249104280011/15445245650160969033769791845376000000000000), (8606032782073646917059556201852710385068311/105677996553732946020530154731520000000000000), (4973250146746358234869270497440622889825958293/60236458035627779231702188196966400000000000000), (882579419884086514104359018375129247770282543/10567799655373294602053015473152000000000000000), (169253241886305990478461267278284703707406975167/2007881934520925974390072939898880000000000000000)]
    reserve := (40070649093/500000000000) }

theorem mixed_002_025_valid : mixed_002_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_025]
  · intro i; fin_cases i <;> norm_num [mixed_002_025]
  · norm_num [mixed_002_025]
  · norm_num [mixed_002_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_025]

def mixed_002_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![0, (1184519/3125000), (29895691/100000000), (321997/1000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(189523/10000000), 0, (1184519/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(321997/20000000), 0, (321997/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (864907/10000000), (5551163/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1018515810429131115772473/4801239736841000000000000), (35412014007629/27028343750000), (-2838406911818943749052473/2400619868420500000000000), (35412014007629/27028343750000), (-4658298013208756382332473/4801239736841000000000000)]
    bernstein := [(988778072833285563086677197207/12291173726312960000000000000000), (264026066567496605999257367711/3072793431578240000000000000000), (210513168145374611890540301809/2304595073683680000000000000000), (18573244187296679175113071819/192049589473640000000000000000), (4898294786111754736237168287/48012397368410000000000000000)]
    reserve := (80446188041/1000000000000) }

theorem mixed_002_026_valid : mixed_002_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_026]
  · intro i; fin_cases i <;> norm_num [mixed_002_026]
  · norm_num [mixed_002_026]
  · norm_num [mixed_002_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_026]

def mixed_002_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![0, (37777193/100000000), (30340181/100000000), (15941313/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(94443/5000000), 0, (37777193/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1594131/100000000), 0, (15941313/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (832621/10000000), (1390109/12500000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-26634315141242891831908489/115743394568900000000000000), (1146166873291933/832621000000000), (-70358920692287762808908489/57871697284450000000000000), (1146166873291933/832621000000000), (-114083526243332633785908489/115743394568900000000000000)]
    bernstein := [(118778107458990216146140242191/1157433945689000000000000000000), (501511674552267532809298642861/4629735782756000000000000000000), (904569245704626292231923132199/7936689913296000000000000000000), (8857233452238854687021804869001/74075772524096000000000000000000), (37071903290338135265532860954471/296303090096384000000000000000000)]
    reserve := (51310965909/500000000000) }

theorem mixed_002_027_valid : mixed_002_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_027]
  · intro i; fin_cases i <;> norm_num [mixed_002_027]
  · norm_num [mixed_002_027]
  · norm_num [mixed_002_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_027]

def mixed_002_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![0, (7530779/20000000), (30771539/100000000), (15787283/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(376539/20000000), 0, (7530779/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(197341/12500000), 0, (15787283/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3999883/50000000), (11140411/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3354391425640501264640711449/13368102171573900000000000000), (231733659698881/159995320000000), (-8388002580817657418045711449/6684051085786950000000000000), (231733659698881/159995320000000), (-13421613735994813571450711449/13368102171573900000000000000)]
    bernstein := [(148412574387920174466630078249859/1180080743421696000000000000000000), (751327592637595770539887422175543/5703723593204864000000000000000000), (3532694052237169002845766022889693/25666756169421888000000000000000000), (204619305764955739329768363641503/1425930898301216000000000000000000), (319361567498579774468943071170151/2138896347451824000000000000000000)]
    reserve := (62882381233/500000000000) }

theorem mixed_002_028_valid : mixed_002_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_028]
  · intro i; fin_cases i <;> norm_num [mixed_002_028]
  · norm_num [mixed_002_028]
  · norm_num [mixed_002_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_028]

def mixed_002_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (2103217/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (10252217/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-179782200794703179/192229068750000000), (42064340/10252217), (-372011269544703179/96114534375000000), (42064340/10252217), (-564240338294703179/192229068750000000)]
    bernstein := [(4875347786949544410421/30756651000000000000000), (2134528303752767345849/12302660400000000000000), (2780056211318972207479/14763192480000000000000), (399471107887086895873/1968425664000000000000), (171165224627526759109/787370265600000000000)]
    reserve := (2476775159/15625000000) }

theorem mixed_002_029_valid : mixed_002_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_002_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_002_029]
  · intro i; fin_cases i <;> norm_num [mixed_002_029]
  · norm_num [mixed_002_029]
  · norm_num [mixed_002_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_002_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_002_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_002_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_002_029]

def mixedTable002 : OwnerTable where
  mode := .mixed
  owners := ![0, 0, 0, 2, 0, 2, 3]
  rows := [mixed_002_000, mixed_002_001, mixed_002_002, mixed_002_003, mixed_002_004, mixed_002_005, mixed_002_006, mixed_002_007, mixed_002_008, mixed_002_009, mixed_002_010, mixed_002_011, mixed_002_012, mixed_002_013, mixed_002_014, mixed_002_015, mixed_002_016, mixed_002_017, mixed_002_018, mixed_002_019, mixed_002_020, mixed_002_021, mixed_002_022, mixed_002_023, mixed_002_024, mixed_002_025, mixed_002_026, mixed_002_027, mixed_002_028, mixed_002_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_002_000_valid
    · exact mixed_002_001_valid
    · exact mixed_002_002_valid
    · exact mixed_002_003_valid
    · exact mixed_002_004_valid
    · exact mixed_002_005_valid
    · exact mixed_002_006_valid
    · exact mixed_002_007_valid
    · exact mixed_002_008_valid
    · exact mixed_002_009_valid
    · exact mixed_002_010_valid
    · exact mixed_002_011_valid
    · exact mixed_002_012_valid
    · exact mixed_002_013_valid
    · exact mixed_002_014_valid
    · exact mixed_002_015_valid
    · exact mixed_002_016_valid
    · exact mixed_002_017_valid
    · exact mixed_002_018_valid
    · exact mixed_002_019_valid
    · exact mixed_002_020_valid
    · exact mixed_002_021_valid
    · exact mixed_002_022_valid
    · exact mixed_002_023_valid
    · exact mixed_002_024_valid
    · exact mixed_002_025_valid
    · exact mixed_002_026_valid
    · exact mixed_002_027_valid
    · exact mixed_002_028_valid
    · exact mixed_002_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
