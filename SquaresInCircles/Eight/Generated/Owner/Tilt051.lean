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

def tilt_051_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-27816856624615310046613720486725634069/436841181155419663589505000000000000000), (44854701730859/71506050000000), (-125237918010685583989654747879425634069/218420590577709831794752500000000000000), (44854701730859/71506050000000), (-222658979396755857932695775272125634069/436841181155419663589505000000000000000)]
    bernstein := [(35139344020559802466031164848004451713941131/1118313423757874338789132800000000000000000000), (533993170954295543813100694436477201665037/15532130885526032483182400000000000000000000), (69837609583222087270295286335910061660019/1872176490666084272526450000000000000000000), (696723045258162819872136872081919344767/17334967506167446967837500000000000000000), (2938260631824240476190843004945017842339/68256434555534322435860156250000000000000)]
    reserve := (15710865699/500000000000) }

theorem tilt_051_000_valid : tilt_051_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_000]
  · intro i; fin_cases i <;> norm_num [tilt_051_000]
  · norm_num [tilt_051_000]
  · norm_num [tilt_051_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_000]

def tilt_051_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![(22301/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-27711318413946498171062837891189395519/436841181155419663589505000000000000000), (44854701730859/71506050000000), (-125132379800016772114103865283889395519/218420590577709831794752500000000000000), (44854701730859/71506050000000), (-222553441186087046057144892676589395519/436841181155419663589505000000000000000)]
    bernstein := [(35426323628548646386841000352669187115339681/1118313423757874338789132800000000000000000000), (537995918670331571817119018637380121150887/15532130885526032483182400000000000000000000), (70322225969726033001128431945670249618969/1872176490666084272526450000000000000000000), (701231034542444927127810285805538677117/17334967506167446967837500000000000000000), (2956096589427269683158942163590642157289/68256434555534322435860156250000000000000)]
    reserve := (253426797/8000000000) }

theorem tilt_051_001_valid : tilt_051_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_001]
  · intro i; fin_cases i <;> norm_num [tilt_051_001]
  · norm_num [tilt_051_001]
  · norm_num [tilt_051_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_001]

def tilt_051_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, (3303/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (2899/50000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-808937791706250943208292308516256165253567/12664025841695616047459749950000000000000000), (44854701730859/71506050000000), (-3633174361288428184817051692630629165253567/6332012920847808023729874975000000000000000), (44854701730859/71506050000000), (-6457410930870605426425811076745002165253567/12664025841695616047459749950000000000000000)]
    bernstein := [(1011817840931900991838171380055844621760335360033/32419906154740777081496959872000000000000000000000), (15384616015561791503439146290949676642177964391/450276474371399681687457776000000000000000000000), (2012988136249953059589919920838856898982799417/54274396464409783060541785500000000000000000000), (1545389002690128600599137698036988599881137/38656977538753406738277625000000000000000000), (6519468672905565897465092730148349351703629/152211849058841539031968148437500000000000000)]
    reserve := (15604885407/500000000000) }

theorem tilt_051_002_valid : tilt_051_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_002]
  · intro i; fin_cases i <;> norm_num [tilt_051_002]
  · norm_num [tilt_051_002]
  · norm_num [tilt_051_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_002]

def tilt_051_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5580889/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3980653/100000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-154856026035814246075835738982789280441/2443864081611238612066818000000000000000), (44854701730859/71506050000000), (-699868362290703861498931470880509280441/1221932040805619306033409000000000000000), (44854701730859/71506050000000), (-1244880698545593476922027202778229280441/2443864081611238612066818000000000000000)]
    bernstein := [(198657143443275201213999761411641815195552359/6256292048924770846891054080000000000000000000), (3016293590886177962861557372261923130714193/86892945123955150651264640000000000000000000), (2759408102370930504965660683913585613784937/73315922448337158362004540000000000000000000), (27512241520909108946637916352569845148141/678851133780899614463005000000000000000000), (16566680228523100595891950563352551605471/381853762751756033135440312500000000000000)]
    reserve := (1984573509/62500000000) }

theorem tilt_051_003_valid : tilt_051_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_003]
  · intro i; fin_cases i <;> norm_num [tilt_051_003]
  · norm_num [tilt_051_003]
  · norm_num [tilt_051_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_003]

def tilt_051_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2784869/25000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1994311/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-11090067634285634779992939525118353113/173917367428550342276728125000000000000), (44854701730859/71506050000000), (-49875821494639915128995461570805853113/86958683714275171138364062500000000000), (44854701730859/71506050000000), (-88661575354994195477997983616493353113/173917367428550342276728125000000000000)]
    bernstein := [(13947746726881133515660068398640810221777287/445228460617088876228424000000000000000000000), (212008759708080518300046244740843862108249/6183728619681789947617000000000000000000000), (194130975369181747000587967298154736826341/5217521022856510268301843750000000000000000), (1937050200920812337190515043647862419213/48310379841263983965757812500000000000000), (1167178138744779803127922326728404573903/27174588660710990980738769531250000000000)]
    reserve := (31327167871/1000000000000) }

theorem tilt_051_004_valid : tilt_051_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_004]
  · intro i; fin_cases i <;> norm_num [tilt_051_004]
  · norm_num [tilt_051_004]
  · norm_num [tilt_051_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_004]

def tilt_051_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (6414999/100000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-57699316657978613086675704701185468729/909639694786823135327981250000000000000), (44854701730859/71506050000000), (-260560375477212799026932536336060468729/454819847393411567663990625000000000000), (44854701730859/71506050000000), (-463421434296446984967189367970935468729/909639694786823135327981250000000000000)]
    bernstein := [(73780351143855853678690895597408547496634471/2328677618654267226439632000000000000000000000), (48714715063538410133477401059913505815879/1406206291457890837222000000000000000000000), (146452561074231043087592492631358334002679/3898455834800670579977062500000000000000000), (63494151570215105093728341564869843789/1569426664573538880828125000000000000000), (6156242192781626664718896678364718284799/142131202310441114894997070312500000000000)]
    reserve := (15841684257/500000000000) }

theorem tilt_051_005_valid : tilt_051_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_005]
  · intro i; fin_cases i <;> norm_num [tilt_051_005]
  · norm_num [tilt_051_005]
  · norm_num [tilt_051_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_005]

def tilt_051_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (6421291/100000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-348348223395893325110014885137239330089/5463191360164552777769737500000000000000), (44854701730859/71506050000000), (-1566708405132245058044499580145489330089/2731595680082276388884868750000000000000), (44854701730859/71506050000000), (-2785068586868596790978984275153739330089/5463191360164552777769737500000000000000)]
    bernstein := [(1516218088834377821087536569450536643192599/48393667411838252979552000000000000000000000), (391792450533807900451645245607864742071441/11426282583350698620172000000000000000000000), (871253273918967245949871335451464463457039/23413677257848083333298875000000000000000000), (8693356127509201210018467201569205757627/216793307943037808641656250000000000000000), (36667325032819651249918983954657428214959/853623650025711371526521484375000000000000)]
    reserve := (3133091931/100000000000) }

theorem tilt_051_006_valid : tilt_051_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_006]
  · intro i; fin_cases i <;> norm_num [tilt_051_006]
  · norm_num [tilt_051_006]
  · norm_num [tilt_051_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_006]

def tilt_051_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (2858359/50000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-415383831816800563133098087776442612333/6548303893829040659136712500000000000000), (44854701730859/71458975000000), (-1877792896609829048160141648525801862333/3274151946914520329568356250000000000000), (44854701730859/71458975000000), (-477171708771836790455312172753594444619/935471984832720094162387500000000000000)]
    bernstein := [(531995740448972701238124597885157338582994067/16763657968202344087389984000000000000000000000), (8078149801822431570720205577412974617546309/232828582891699223435972000000000000000000000), (7390642056787743679190862484289843974092881/196449116814871219774101375000000000000000000), (10527304563399468623978213368414901683919/259853329120200026156218750000000000000000), (44375562571698456055076283725640778265723/1023172483410787602990111328125000000000000)]
    reserve := (31735062923/1000000000000) }

theorem tilt_051_007_valid : tilt_051_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_007]
  · intro i; fin_cases i <;> norm_num [tilt_051_007]
  · norm_num [tilt_051_007]
  · norm_num [tilt_051_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_007]

def tilt_051_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1431063/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-1245843500298262939693406689270059317/19539606991210489774675000000000000000), (44854701730859/71553150000000), (-1460894377340991396843809329902622731737/2549918712352968915595087500000000000000), (44854701730859/71553150000000), (-2596623601104136166427639513905759981737/5099837424705937831190175000000000000000)]
    bernstein := [(408369220427852062235177811471716052700767863/13055583807247200847846848000000000000000000000), (55870904979685050281361543921718935928947209/1631947975905900105980856000000000000000000000), (5684841254494491730872150652952020052340109/152995122741178134935705250000000000000000000), (510547514823188196501216767915438123520733/12749593561764844577975437500000000000000000), (11394471043153229355767169463174973112149/265616532536767595374488281250000000000000)]
    reserve := (3909909607/125000000000) }

theorem tilt_051_008_valid : tilt_051_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_008]
  · intro i; fin_cases i <;> norm_num [tilt_051_008]
  · norm_num [tilt_051_008]
  · norm_num [tilt_051_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_008]

def tilt_051_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283/20000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-1384784899206262700648380526184338467/21831356078056955256750000000000000000), (44854701730859/71506050000000), (-6253451069818182557122550171184338467/10915678039028477628375000000000000000), (44854701730859/71506050000000), (-11122117240430102413596719816184338467/21831356078056955256750000000000000000)]
    bernstein := [(1770725757096493325888988116151530656195133/55888271559825805457280000000000000000000000), (26890485811159279343034706160970344962091/776225993886469520240000000000000000000000), (3514857038195828974812470619914633379317/93562954620244093957500000000000000000000), (35048730847335738252827436801554685481/866323653891149018125000000000000000000), (147749652539036879500751548552346799077/3411149387196399258867187500000000000000)]
    reserve := (6336663159/200000000000) }

theorem tilt_051_009_valid : tilt_051_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_009]
  · intro i; fin_cases i <;> norm_num [tilt_051_009]
  · norm_num [tilt_051_009]
  · norm_num [tilt_051_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_009]

def tilt_051_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1605323/25000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-348153892589621773847448102515525005571/5463192210957852779989350000000000000000), (44854701730859/71506050000000), (-1566514264063548355258934218964525005571/2731596105478926389994675000000000000000), (44854701730859/71506050000000), (-2784874635537474936670420335413525005571/5463192210957852779989350000000000000000)]
    bernstein := [(438715667949357377522156848296620151326331229/13985772060052103116772736000000000000000000000), (6667845138311766880394820074739165863708683/194246834167390321066288000000000000000000000), (872145998005148603455691870332591981561621/23413680904105083342811500000000000000000000), (8701660500129122530787629280612289047753/216793341704676697618625000000000000000000), (36700181817423288732672189949911774058501/853623782962164496873335937500000000000000)]
    reserve := (6273742573/200000000000) }

theorem tilt_051_010_valid : tilt_051_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_010]
  · intro i; fin_cases i <;> norm_num [tilt_051_010]
  · norm_num [tilt_051_010]
  · norm_num [tilt_051_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_010]

def tilt_051_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(9827/50000000), 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-27723845388470098963565666645948330869/436841181155419663589505000000000000000), (44854701730859/71506050000000), (-125144906774540372906606694038648330869/218420590577709831794752500000000000000), (44854701730859/71506050000000), (-222565968160610646849647721431348330869/436841181155419663589505000000000000000)]
    bernstein := [(35392260266897096588266515899899935352684331/1118313423757874338789132800000000000000000000), (537520808107574964559864232455637980131437/15532130885526032483182400000000000000000000), (70264703892281447247782942707925041196819/1872176490666084272526450000000000000000000), (700695953773508264705189457566549867167/17334967506167446967837500000000000000000), (2953979530732781149225964104036382083139/68256434555534322435860156250000000000000)]
    reserve := (31647890041/1000000000000) }

theorem tilt_051_011_valid : tilt_051_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_011]
  · intro i; fin_cases i <;> norm_num [tilt_051_011]
  · norm_num [tilt_051_011]
  · norm_num [tilt_051_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_011]

def tilt_051_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2911/50000000), 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (5109/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-237514660109872543406724795198646876683613/3719702657538398435464635075000000000000000), (44854701730859/71506050000000), (-1067054997812260926031719143447487376683613/1859851328769199217732317537500000000000000), (44854701730859/71506050000000), (-1896595335514649308656713491696327876683613/3719702657538398435464635075000000000000000)]
    bernstein := [(297432814394238740129084470552631555614042846787/9522438803298299994789465792000000000000000000000), (4522142815721888719916077787931390475395609749/132256094490254166594298136000000000000000000000), (591663592679454105675230138840981781974446763/15941582818021707580562721750000000000000000000), (454204323661341918119734479664214833753843/11354403716539677763933562500000000000000000), (1916057076478326193227485619934671353113031/44707964633874981195488402343750000000000000)]
    reserve := (1561747051/50000000000) }

theorem tilt_051_012_valid : tilt_051_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_012]
  · intro i; fin_cases i <;> norm_num [tilt_051_012]
  · norm_num [tilt_051_012]
  · norm_num [tilt_051_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_012]

def tilt_051_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9836583/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (701609/20000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-581049596417576550676670367280298860837/9164489982157102290776925000000000000000), (44854701730859/71506050000000), (-2624845785142986611582650984919798860837/4582244991078551145388462500000000000000), (44854701730859/71506050000000), (-4668641973868396672488631602559298860837/9164489982157102290776925000000000000000)]
    bernstein := [(248013680115664205095860810461964319437722921/7820364784774060621462976000000000000000000000), (33894670852029288190296596327331953190105303/977545598096757577682872000000000000000000000), (10336866849123710895362689879490792653616309/274934699464713068723307750000000000000000000), (309208157353870306001222709368353921829211/7637074985130918575647437500000000000000000), (8866809985516039379024359669934248931221/204564508530292461847699218750000000000000)]
    reserve := (15856912493/500000000000) }

theorem tilt_051_013_valid : tilt_051_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_013]
  · intro i; fin_cases i <;> norm_num [tilt_051_013]
  · norm_num [tilt_051_013]
  · norm_num [tilt_051_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_013]

def tilt_051_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9816929/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3515069/100000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-2927293386704713652587832608775775146113/45914198131852617899911425000000000000000), (44854701730859/71506050000000), (-13166735334152420876096545273045275146113/22957099065926308949955712500000000000000), (44854701730859/71506050000000), (-23406177281600128099605257937314775146113/45914198131852617899911425000000000000000)]
    bernstein := [(1227841944542539799156139190832736095971461429/39180115739180900607924416000000000000000000000), (167966204315593804389851821948633143475116747/4897514467397612575990552000000000000000000000), (51266191346469568807332851592013487165989841/1377425943955578536997342750000000000000000000), (1534579517390973482954484139799991693936639/38261831776543848249926187500000000000000000), (44031019067382526097059315918527035758129/1024870494014567363837308593750000000000000)]
    reserve := (15669197517/500000000000) }

theorem tilt_051_014_valid : tilt_051_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_014]
  · intro i; fin_cases i <;> norm_num [tilt_051_014]
  · norm_num [tilt_051_014]
  · norm_num [tilt_051_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_014]

def tilt_051_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(9827/50000000), 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-27723845388470098963565666645948330869/436841181155419663589505000000000000000), (44854701730859/71506050000000), (-125144906774540372906606694038648330869/218420590577709831794752500000000000000), (44854701730859/71506050000000), (-222565968160610646849647721431348330869/436841181155419663589505000000000000000)]
    bernstein := [(35392260266897096588266515899899935352684331/1118313423757874338789132800000000000000000000), (537520808107574964559864232455637980131437/15532130885526032483182400000000000000000000), (70264703892281447247782942707925041196819/1872176490666084272526450000000000000000000), (700695953773508264705189457566549867167/17334967506167446967837500000000000000000), (2953979530732781149225964104036382083139/68256434555534322435860156250000000000000)]
    reserve := (31647890041/1000000000000) }

theorem tilt_051_015_valid : tilt_051_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_015]
  · intro i; fin_cases i <;> norm_num [tilt_051_015]
  · norm_num [tilt_051_015]
  · norm_num [tilt_051_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_015]

def tilt_051_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2911/50000000), 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (5109/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-237514660109872543406724795198646876683613/3719702657538398435464635075000000000000000), (44854701730859/71506050000000), (-1067054997812260926031719143447487376683613/1859851328769199217732317537500000000000000), (44854701730859/71506050000000), (-1896595335514649308656713491696327876683613/3719702657538398435464635075000000000000000)]
    bernstein := [(297432814394238740129084470552631555614042846787/9522438803298299994789465792000000000000000000000), (4522142815721888719916077787931390475395609749/132256094490254166594298136000000000000000000000), (591663592679454105675230138840981781974446763/15941582818021707580562721750000000000000000000), (454204323661341918119734479664214833753843/11354403716539677763933562500000000000000000), (1916057076478326193227485619934671353113031/44707964633874981195488402343750000000000000)]
    reserve := (1561747051/50000000000) }

theorem tilt_051_016_valid : tilt_051_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_016]
  · intro i; fin_cases i <;> norm_num [tilt_051_016]
  · norm_num [tilt_051_016]
  · norm_num [tilt_051_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_016]

def tilt_051_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-27816856624615310046613720486725634069/436841181155419663589505000000000000000), (44854701730859/71506050000000), (-125237918010685583989654747879425634069/218420590577709831794752500000000000000), (44854701730859/71506050000000), (-222658979396755857932695775272125634069/436841181155419663589505000000000000000)]
    bernstein := [(35139344020559802466031164848004451713941131/1118313423757874338789132800000000000000000000), (533993170954295543813100694436477201665037/15532130885526032483182400000000000000000000), (69837609583222087270295286335910061660019/1872176490666084272526450000000000000000000), (696723045258162819872136872081919344767/17334967506167446967837500000000000000000), (2938260631824240476190843004945017842339/68256434555534322435860156250000000000000)]
    reserve := (15710865699/500000000000) }

theorem tilt_051_017_valid : tilt_051_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_017]
  · intro i; fin_cases i <;> norm_num [tilt_051_017]
  · norm_num [tilt_051_017]
  · norm_num [tilt_051_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_017]

def tilt_051_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-27816856624615310046613720486725634069/436841181155419663589505000000000000000), (44854701730859/71506050000000), (-125237918010685583989654747879425634069/218420590577709831794752500000000000000), (44854701730859/71506050000000), (-222658979396755857932695775272125634069/436841181155419663589505000000000000000)]
    bernstein := [(35139344020559802466031164848004451713941131/1118313423757874338789132800000000000000000000), (533993170954295543813100694436477201665037/15532130885526032483182400000000000000000000), (69837609583222087270295286335910061660019/1872176490666084272526450000000000000000000), (696723045258162819872136872081919344767/17334967506167446967837500000000000000000), (2938260631824240476190843004945017842339/68256434555534322435860156250000000000000)]
    reserve := (15710865699/500000000000) }

theorem tilt_051_018_valid : tilt_051_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_018]
  · intro i; fin_cases i <;> norm_num [tilt_051_018]
  · norm_num [tilt_051_018]
  · norm_num [tilt_051_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_018]

def tilt_051_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-27816856624615310046613720486725634069/436841181155419663589505000000000000000), (44854701730859/71506050000000), (-125237918010685583989654747879425634069/218420590577709831794752500000000000000), (44854701730859/71506050000000), (-222658979396755857932695775272125634069/436841181155419663589505000000000000000)]
    bernstein := [(35139344020559802466031164848004451713941131/1118313423757874338789132800000000000000000000), (533993170954295543813100694436477201665037/15532130885526032483182400000000000000000000), (69837609583222087270295286335910061660019/1872176490666084272526450000000000000000000), (696723045258162819872136872081919344767/17334967506167446967837500000000000000000), (2938260631824240476190843004945017842339/68256434555534322435860156250000000000000)]
    reserve := (15710865699/500000000000) }

theorem tilt_051_019_valid : tilt_051_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_019]
  · intro i; fin_cases i <;> norm_num [tilt_051_019]
  · norm_num [tilt_051_019]
  · norm_num [tilt_051_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_019]

def tilt_051_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11150627/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2456689/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1992319/50000000), (1/100000000), (1430121/25000000), (1283629/20000000), (1/100000000), (3511557/100000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-27816856624615310046613720486725634069/436841181155419663589505000000000000000), (44854701730859/71506050000000), (-125237918010685583989654747879425634069/218420590577709831794752500000000000000), (44854701730859/71506050000000), (-222658979396755857932695775272125634069/436841181155419663589505000000000000000)]
    bernstein := [(35139344020559802466031164848004451713941131/1118313423757874338789132800000000000000000000), (533993170954295543813100694436477201665037/15532130885526032483182400000000000000000000), (69837609583222087270295286335910061660019/1872176490666084272526450000000000000000000), (696723045258162819872136872081919344767/17334967506167446967837500000000000000000), (2938260631824240476190843004945017842339/68256434555534322435860156250000000000000)]
    reserve := (15710865699/500000000000) }

theorem tilt_051_020_valid : tilt_051_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_051_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_051_020]
  · intro i; fin_cases i <;> norm_num [tilt_051_020]
  · norm_num [tilt_051_020]
  · norm_num [tilt_051_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_051_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_051_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_051_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_051_020]

def tiltBundle051_row : Alternative → Row
  | .zero => tilt_051_000
  | (.spike 0 false false) => tilt_051_001
  | (.spike 0 false true) => tilt_051_002
  | (.spike 0 true false) => tilt_051_003
  | (.spike 0 true true) => tilt_051_004
  | (.spike 1 false false) => tilt_051_005
  | (.spike 1 false true) => tilt_051_006
  | (.spike 1 true false) => tilt_051_007
  | (.spike 1 true true) => tilt_051_008
  | (.spike 2 false false) => tilt_051_009
  | (.spike 2 false true) => tilt_051_010
  | (.spike 2 true false) => tilt_051_011
  | (.spike 2 true true) => tilt_051_012
  | (.spike 3 false false) => tilt_051_013
  | (.spike 3 false true) => tilt_051_014
  | (.spike 3 true false) => tilt_051_015
  | (.spike 3 true true) => tilt_051_016
  | (.spike 4 false false) => tilt_051_017
  | (.spike 4 false true) => tilt_051_018
  | (.spike 4 true false) => tilt_051_019
  | (.spike 4 true true) => tilt_051_020

def tiltBundle051 : TiltBundle where
  interval := ⟨(7/40), (1/5)⟩
  lambda := ![(11150627/50000000), (11150627/50000000), (4022617/25000000), (2456689/12500000), (2456689/12500000), 0, 0]
  row := tiltBundle051_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_051_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_051_001_valid | exact tilt_051_002_valid | exact tilt_051_003_valid | exact tilt_051_004_valid | exact tilt_051_005_valid | exact tilt_051_006_valid | exact tilt_051_007_valid | exact tilt_051_008_valid | exact tilt_051_009_valid | exact tilt_051_010_valid | exact tilt_051_011_valid | exact tilt_051_012_valid | exact tilt_051_013_valid | exact tilt_051_014_valid | exact tilt_051_015_valid | exact tilt_051_016_valid | exact tilt_051_017_valid | exact tilt_051_018_valid | exact tilt_051_019_valid | exact tilt_051_020_valid
  same_interval := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_lambda := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_mode := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_owners := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_alternative := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_sign := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl

end SquaresInCircles.Eight.Generated.Owner
