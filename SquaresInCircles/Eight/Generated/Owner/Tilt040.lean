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

def tilt_040_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (65229/10000000)]
    alternative := .zero
    polynomial := [(-46156217531145575663571928992764884895140057/1699446406424844030491297147150000000000000000), (19592738637959/29876350000000), (-10137200923091543899497667770460443930785420171/2549169609637266045736945720725000000000000000), (19592738637959/29876350000000), (-20135933193589651072004619753942593206885420171/5098339219274532091473891441450000000000000000)]
    bernstein := [(3198184156288116509457819215124987830616360317/117149338678183182248940520253906250000000000000000), (96319557944108267631580315714360747396217245079/2276044294318987540836558679218750000000000000000000), (81371371374210900750129847128844118565740264438497/1529501765782359627442167432435000000000000000000000000), (11642634259793955444229769012818041876091959349513/194222446448553603484719673960000000000000000000000000), (2721166062351429798682787329254278089164678945102503/43505828004476007180577206967040000000000000000000000000)]
    reserve := (27300061/1000000000000) }

theorem tilt_040_000_valid : tilt_040_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_000]
  · intro i; fin_cases i <;> norm_num [tilt_040_000]
  · norm_num [tilt_040_000]
  · norm_num [tilt_040_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_000]

def tilt_040_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14933/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (328041/50000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-24714972007397452562834630125739620324946159/915710308424406312386902200787500000000000000), (228282579446832848461/350023847512500000000), (-201236846955364818584812444581359240314827351/50872794912467017354827900043750000000000000), (228282579446832848461/350023847512500000000), (-3597548273189169281963789372338726705341946159/915710308424406312386902200787500000000000000)]
    bernstein := [(15016465311323119815798183827398565187554707081/357699339228283715776133672182617187500000000000000), (188876083671231765974562958638441578982303017/3323571096197758102449557929687500000000000000000), (6186833775862337935338676103646444959656226368271/91571030842440631238690220078750000000000000000000000), (2587717512492259702878096188124680196928398094477/34884202225691669043310560030000000000000000000000000), (43841295501188051759926603976988556238843472703721/571760582821092721880602349760000000000000000000000000)]
    reserve := (4198069/100000000000) }

theorem tilt_040_001_valid : tilt_040_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_001]
  · intro i; fin_cases i <;> norm_num [tilt_040_001]
  · norm_num [tilt_040_001]
  · norm_num [tilt_040_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_001]

def tilt_040_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4423/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1941/50000000), (4182689/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (324249/50000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-179076481453555075019946747217462959788493915443/6558898720515871150653982942686060000000000000000), (1597058815410739088273/2421844152787500000000), (-13110717575027595931300626707765193867492752315443/3279449360257935575326991471343030000000000000000), (1597058815410739088273/2421844152787500000000), (-8680786222867212262527102222770974925065670238481/2186299573505290383551327647562020000000000000000)]
    bernstein := [(35116997536625851032216346406351570081924497138679/854023270900504056074737362328914062500000000000000000), (164897190403003811075081893911399322817526285187807/2928079785944585335113385242270562500000000000000000000), (132529944376691593495716320459170331307231753919159001/1967669616154761345196194882805818000000000000000000000000), (18547550768865343612772431462313713594760625112283329/249862808400604615263008874007088000000000000000000000000), (12919634197683746009104745177858545780415024755994481997/167907807245206301456741963332763136000000000000000000000000)]
    reserve := (8223897/200000000000) }

theorem tilt_040_002_valid : tilt_040_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_002]
  · intro i; fin_cases i <;> norm_num [tilt_040_002]
  · norm_num [tilt_040_002]
  · norm_num [tilt_040_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_002]

def tilt_040_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(268313/5000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (328041/50000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-3945334341749979199002193863213751240455373/146440432679149087421023849320000000000000000), (228282579446832848461/350023847512500000000), (-96543054480852422928803790449527560838551791/24406738779858181236837308220000000000000000), (228282579446832848461/350023847512500000000), (-575312992543364558373820548833951613790855373/146440432679149087421023849320000000000000000)]
    bernstein := [(5204576182304890418693731748544606046509370907/57203294015292612273837441140625000000000000000000), (18751901768928646203536143690644577796142833/177168545149957761591443875000000000000000000000), (1707289901684232594225125170443737792431346765837/14644043267914908742102384932000000000000000000000000), (687365723147933259061369426528804299658013573119/5578683149681869996991384736000000000000000000000000), (11495372196912323480901684774098752003515939076987/91435977477712600926297818112000000000000000000000000)]
    reserve := (45491927/500000000000) }

theorem tilt_040_003_valid : tilt_040_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_003]
  · intro i; fin_cases i <;> norm_num [tilt_040_003]
  · norm_num [tilt_040_003]
  · norm_num [tilt_040_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_003]

def tilt_040_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1342907/25000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (324249/50000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-690452618058537625675320623788551554979301139/25356177803366363067508577740200000000000000000), (1597058815410739088273/2421844152787500000000), (-16894380892091664090090554021594749873102433713/4226029633894393844584762956700000000000000000), (1597058815410739088273/2421844152787500000000), (-100675832734491446914868003505779947683635301139/25356177803366363067508577740200000000000000000)]
    bernstein := [(1136339952644695195244084188421970146399022064901/9904756954439985573245538179765625000000000000000000), (1470858007677263033419855425687560638859274586111/11319722233645697797994900776875000000000000000000000), (357497689573389242541292785394193493837402203687891/2535617780336636306750857774020000000000000000000000000), (428541100049559442916187111106995821844815545313251/2897848891813298636286694598880000000000000000000000000), (97764625016303791056227475068471217643335917519215981/649118151766178894528219590149120000000000000000000000000)]
    reserve := (114726687/1000000000000) }

theorem tilt_040_004_valid : tilt_040_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_004]
  · intro i; fin_cases i <;> norm_num [tilt_040_004]
  · norm_num [tilt_040_004]
  · norm_num [tilt_040_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_004]

def tilt_040_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (1121187/25000000), (1/100000000), (2715017/50000000), (328041/50000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-1440994224671612625364884711097324999074489437/53391707610615850340815877779650000000000000000), (228282579446832848461/350023847512500000000), (-11733377036550568726298517054369685142183165493/2966205978367547241156437654425000000000000000), (228282579446832848461/350023847512500000000), (-209759792433238624448008422267557007560222489437/53391707610615850340815877779650000000000000000)]
    bernstein := [(893396050828284851399638123918159671324956655883/20856135785396816539381202257675781250000000000000000), (11178474892328132315582588891020364675378594531/193785233778367633350812564531250000000000000000000), (365300710793361083413872115862995157551336143873053/5339170761061585034081587777965000000000000000000000000), (152621288728516406461896461541772954094502892751311/2033969813737746679650128677320000000000000000000000000), (2584765935995157599567434912819631230905056597527403/33337261337360140700606987101440000000000000000000000000)]
    reserve := (342689/8000000000) }

theorem tilt_040_005_valid : tilt_040_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_005]
  · intro i; fin_cases i <;> norm_num [tilt_040_005]
  · norm_num [tilt_040_005]
  · norm_num [tilt_040_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_005]

def tilt_040_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (2244451/50000000), (1/100000000), (2715017/50000000), (324249/50000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-30209186468352705069248295451595535014051944087/1109291546115338887039276303983525000000000000000), (1597058815410739088273/2421844152787500000000), (-739102693743615655475314661168360331866777648029/184881924352556481173212717330587500000000000000), (1597058815410739088273/2421844152787500000000), (-4404406975993341227782639671558566456186613944087/1109291546115338887039276303983525000000000000000)]
    bernstein := [(48523252163507374009363365945418346385372697475233/433317010201304252749717306243564453125000000000000000), (62987635319157274771750269019734916441448653960163/495219440230062003142534064278359375000000000000000000), (15335239014096763409302417062787189809169838484698903/110929154611533888703927630398352500000000000000000000000), (18399672979425451704459895589868435340792496368145783/126776176698895872804488720455260000000000000000000000000), (4199007444684999932133678213513102404860689995776640873/28397863580552675508205473381978240000000000000000000000000)]
    reserve := (111980953/1000000000000) }

theorem tilt_040_006_valid : tilt_040_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_006]
  · intro i; fin_cases i <;> norm_num [tilt_040_006]
  · norm_num [tilt_040_006]
  · norm_num [tilt_040_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_006]

def tilt_040_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4180461/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (328041/50000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-46110073149611000136802882574135966074623349/1708415399545661607296858133030000000000000000), (3727705798658182350187/5714010862087500000000), (-1126426774832122973015221631843698258448707783/284735899924276934549476355505000000000000000), (3727705798658182350187/5714010862087500000000), (-958921510834732405422075272641150512088231907/244059342792237372470979733290000000000000000)]
    bernstein := [(36604537637257559485742402819663130736035578291/667349765447524065350335208214843750000000000000000), (3028936875931429161683001646639907202920036909/43404862793334898559371395656250000000000000000000), (4590008770679490780051211009338771306766056549127/56947179984855386909895271101000000000000000000000000), (13257555777335184039564365602648951939276073242443/151859146626281031759720722936000000000000000000000000), (95879102094322998591005715273781706663598516117331/1066717908008998466995111419648000000000000000000000000)]
    reserve := (54850603/1000000000000) }

theorem tilt_040_007_valid : tilt_040_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_007]
  · intro i; fin_cases i <;> norm_num [tilt_040_007]
  · norm_num [tilt_040_007]
  · norm_num [tilt_040_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_007]

def tilt_040_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4184917/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (324249/50000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-4833654165573089299804779860929429472084106157/177499023265345359793480831438950000000000000000), (11182174607415898173883/16961939404162500000000), (-118254174411340798280198338853095748498906868719/29583170544224226632246805239825000000000000000), (11182174607415898173883/16961939404162500000000), (-704691392302471700381385253257645061521357106157/177499023265345359793480831438950000000000000000)]
    bernstein := [(6931914767982285252592063137877908445969487938363/69335555963025531169328449780839843750000000000000000), (9120820715494617046761669284265846396540858390593/79240635386314892764946799749531250000000000000000000), (2237755285339283334042633314309937288535856325390733/17749902326534535979348083143895000000000000000000000000), (2695545301618048389310868897853925472907834629244413/20285602658896612547826380735880000000000000000000000000), (615823173480046086665484584255596466027182563317824403/4543974995592841210713109284837120000000000000000000000000)]
    reserve := (49988167/500000000000) }

theorem tilt_040_008_valid : tilt_040_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_008]
  · intro i; fin_cases i <;> norm_num [tilt_040_008]
  · norm_num [tilt_040_008]
  · norm_num [tilt_040_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_008]

def tilt_040_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (4484749/100000000), (1/100000000), (2715017/50000000), (328041/50000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-17291977139415343381477124905782412603050562499/640700634189484423740527673946650000000000000000), (228282579446832848461/350023847512500000000), (-422401681697944148227646642014499506088581520833/106783439031580737290087945657775000000000000000), (228282579446832848461/350023847512500000000), (-2517118113048249545984402727181214623928438562499/640700634189484423740527673946650000000000000000)]
    bernstein := [(10703905585375289483241558616398367829491594333141/250273685230267353023643622635410156250000000000000000), (44661713601443619566046308923074729832822652479/775141107952821844440243507968750000000000000000000), (4379294333263516017873682267629209208643724272553731/64070063418948442374052767394665000000000000000000000000), (1829811663973650057667265206920223635034532537628497/24407643207218454237734387578920000000000000000000000000), (30990243637430456639900459088537707247003659196856181/400047225250019542628231913488640000000000000000000000000)]
    reserve := (42768801/1000000000000) }

theorem tilt_040_009_valid : tilt_040_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_009]
  · intro i; fin_cases i <;> norm_num [tilt_040_009]
  · norm_num [tilt_040_009]
  · norm_num [tilt_040_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_009]

def tilt_040_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (4488903/100000000), (1/100000000), (2715017/50000000), (324249/50000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-40207449619383776246911409519919618704212342003/1479055724312027923100799414134550000000000000000), (1597058815410739088273/2421844152787500000000), (-2956339958934147097666969245249118739701474342003/739527862156013961550399707067275000000000000000), (1597058815410739088273/2421844152787500000000), (-5872472468248910419087027080978317860698736342003/1479055724312027923100799414134550000000000000000)]
    bernstein := [(92975983888727190831225638977426119886560213591077/577756142309385907461249771146308593750000000000000000), (116308012032046183377899451519799784814635430301247/660292734067869608527142595595781250000000000000000000), (83067381442734432886650525503047128878855130287072921/443716717293608376930239824240365000000000000000000000000), (32811309907047172225115193068817014232379281351109027/169034939921374619782948504472520000000000000000000000000), (7453420993292768607001585960853831036676354987750020237/37863826542387914831380465001844480000000000000000000000000)]
    reserve := (80462999/500000000000) }

theorem tilt_040_010_valid : tilt_040_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_010]
  · intro i; fin_cases i <;> norm_num [tilt_040_010]
  · norm_num [tilt_040_010]
  · norm_num [tilt_040_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_010]

def tilt_040_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(737/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (328041/50000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-98867546131751285604032836335023957330777261/3662841233697625249547608803150000000000000000), (228282579446832848461/350023847512500000000), (-2414844716165098314801980773586999375788259087/610473538949604208257934800525000000000000000), (228282579446832848461/350023847512500000000), (-14390200750858838603207851805186972297398777261/3662841233697625249547608803150000000000000000)]
    bernstein := [(57036002048024209247860925195377258372265680699/1430797356913134863104534688730468750000000000000000), (727346738257045846570145904737151677779247443/13294284384791032409798231718750000000000000000000), (2663486804257522590262793691201732317483853311301/40698235929973613883862320035000000000000000000000000), (3351736205797941790300176209891002290529583410261/46512269634255558724414080040000000000000000000000000), (170518226085747977798410243279655629782406555087259/2287042331284370887522409399040000000000000000000000000)]
    reserve := (2491443/62500000000) }

theorem tilt_040_011_valid : tilt_040_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_011]
  · intro i; fin_cases i <;> norm_num [tilt_040_011]
  · norm_num [tilt_040_011]
  · norm_num [tilt_040_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_011]

def tilt_040_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2183/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (479/12500000), (2715017/50000000), (324249/50000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-132569118156652943309309124295393344573180731221/4855815281494748502570723075033420000000000000000), (1597058815410739088273/2421844152787500000000), (-3235460228371622887418634056940485625311276510407/809302546915791417095120512505570000000000000000), (1597058815410739088273/2421844152787500000000), (-19280192252073084381202495217347520407294478331221/4855815281494748502570723075033420000000000000000)]
    bernstein := [(81306937091613217462043942258196941639074277392339/1896802844333886133816688701184929687500000000000000000), (125865177360929149700105613466814334422457461971529/2167774679238727010076215658497062500000000000000000000), (33553793016336297196651766480053944921658903058476949/485581528149474850257072307503342000000000000000000000000), (42163881782759573930741507630672199562968628010097989/554950317885114114579511208575248000000000000000000000000), (9782112217172294496821809715955024066458639258745980459/124308871206265561665810510720855552000000000000000000000000)]
    reserve := (21432627/500000000000) }

theorem tilt_040_012_valid : tilt_040_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_012]
  · intro i; fin_cases i <;> norm_num [tilt_040_012]
  · norm_num [tilt_040_012]
  · norm_num [tilt_040_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_012]

def tilt_040_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (1356831/25000000), (328041/50000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-195686408920342042634931300338906365406369/7263915074025849101451929287500000000000000), (228282579446832848461/350023847512500000000), (-14366520478753389108234955588039702133906369/3631957537012924550725964643750000000000000), (228282579446832848461/350023847512500000000), (-28537354548586436173834979875740497902406369/7263915074025849101451929287500000000000000)]
    bernstein := [(264029657296169744775434467921765315516762471/2837466825791347305254659877929687500000000000000), (8534934525614771957071271620748371256288741/79093151938434768090722226562500000000000000000), (258568041519340553225205510031003328335365849283/2179174522207754730435578786250000000000000000000000), (104003887016981833643659189388806622771710595321/830161722745811325880220490000000000000000000000000), (579591321049780535190408424446542854978606520711/4535517704757603341394375360000000000000000000000000)]
    reserve := (93051187/1000000000000) }

theorem tilt_040_013_valid : tilt_040_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_013]
  · intro i; fin_cases i <;> norm_num [tilt_040_013]
  · norm_num [tilt_040_013]
  · norm_num [tilt_040_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_013]

def tilt_040_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (679093/12500000), (324249/50000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-11906073917268127391419483508496455401660243/437175032635918041455981064900000000000000000), (1597058815410739088273/2421844152787500000000), (-291282708389941131845925045422533578879220081/72862505439319673575996844150000000000000000), (1597058815410739088273/2421844152787500000000), (-1735790176422378663684130789026705017873660243/437175032635918041455981064900000000000000000)]
    bernstein := [(18907352568181556605601412114098337880587799237/170771497123405484943742603476562500000000000000000), (24576930189421053298407458769338539639106443007/195167425283891982792848689687500000000000000000000), (5988394872100767293254861065481306484378002670867/43717503263591804145598106490000000000000000000000000), (7188189058402605733438395027970462355850962953187/49962860872676347594969264560000000000000000000000000), (1640686818212076780013486782717706681050310290321197/11191680835479501861273115261440000000000000000000000000)]
    reserve := (110717261/1000000000000) }

theorem tilt_040_014_valid : tilt_040_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_014]
  · intro i; fin_cases i <;> norm_num [tilt_040_014]
  · norm_num [tilt_040_014]
  · norm_num [tilt_040_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_014]

def tilt_040_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(737/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (328041/50000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-98867546131751285604032836335023957330777261/3662841233697625249547608803150000000000000000), (228282579446832848461/350023847512500000000), (-2414844716165098314801980773586999375788259087/610473538949604208257934800525000000000000000), (228282579446832848461/350023847512500000000), (-14390200750858838603207851805186972297398777261/3662841233697625249547608803150000000000000000)]
    bernstein := [(57036002048024209247860925195377258372265680699/1430797356913134863104534688730468750000000000000000), (727346738257045846570145904737151677779247443/13294284384791032409798231718750000000000000000000), (2663486804257522590262793691201732317483853311301/40698235929973613883862320035000000000000000000000000), (3351736205797941790300176209891002290529583410261/46512269634255558724414080040000000000000000000000000), (170518226085747977798410243279655629782406555087259/2287042331284370887522409399040000000000000000000000000)]
    reserve := (2491443/62500000000) }

theorem tilt_040_015_valid : tilt_040_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_015]
  · intro i; fin_cases i <;> norm_num [tilt_040_015]
  · norm_num [tilt_040_015]
  · norm_num [tilt_040_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_015]

def tilt_040_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2183/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (479/12500000), (2715017/50000000), (324249/50000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-132569118156652943309309124295393344573180731221/4855815281494748502570723075033420000000000000000), (1597058815410739088273/2421844152787500000000), (-3235460228371622887418634056940485625311276510407/809302546915791417095120512505570000000000000000), (1597058815410739088273/2421844152787500000000), (-19280192252073084381202495217347520407294478331221/4855815281494748502570723075033420000000000000000)]
    bernstein := [(81306937091613217462043942258196941639074277392339/1896802844333886133816688701184929687500000000000000000), (125865177360929149700105613466814334422457461971529/2167774679238727010076215658497062500000000000000000000), (33553793016336297196651766480053944921658903058476949/485581528149474850257072307503342000000000000000000000000), (42163881782759573930741507630672199562968628010097989/554950317885114114579511208575248000000000000000000000000), (9782112217172294496821809715955024066458639258745980459/124308871206265561665810510720855552000000000000000000000000)]
    reserve := (21432627/500000000000) }

theorem tilt_040_016_valid : tilt_040_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_016]
  · intro i; fin_cases i <;> norm_num [tilt_040_016]
  · norm_num [tilt_040_016]
  · norm_num [tilt_040_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_016]

def tilt_040_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (1356831/25000000), (328041/50000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-782746000490441151128766129562016934429851/29055660296103396405807717150000000000000000), (228282579446832848461/350023847512500000000), (-57466082279822629413528863280365200008429851/14527830148051698202903858575000000000000000), (228282579446832848461/350023847512500000000), (-114149418559154817675928960431168383082429851/29055660296103396405807717150000000000000000)]
    bernstein := [(1055974295758235865872995995182132570271320509/11349867303165389221018639511718750000000000000000), (34135714071530684306959505452048363872681839/316372607753739072362888906250000000000000000000), (1034161273716208396732735765079331121286528090257/8716698088831018921742315145000000000000000000000000), (415973294789950785466974631274700793988971995659/3320646890983245303520881960000000000000000000000000), (2318134389721834433607246362381184682922030053469/18142070819030413365577501440000000000000000000000000)]
    reserve := (9303847/100000000000) }

theorem tilt_040_017_valid : tilt_040_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_017]
  · intro i; fin_cases i <;> norm_num [tilt_040_017]
  · norm_num [tilt_040_017]
  · norm_num [tilt_040_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_017]

def tilt_040_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (1086549/20000000), (324249/50000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-9204336228517254756990460581145379140772551/338082087468878814554920762755000000000000000), (1597058815410739088273/2421844152787500000000), (-675772978558457521834437463577367495318972551/169041043734439407277460381377500000000000000), (1597058815410739088273/2421844152787500000000), (-447447206962799262970628155524529870499057517/112694029156292938184973587585000000000000000)]
    bernstein := [(5273400742930885084406087660399515260494916603/44021105139176928978505307650390625000000000000000), (20376164821732566092023912005213794069225387699/150929503334320899354875340515625000000000000000000), (14813904839618020294513560986071203667888339299157/101424626240663644366476228826500000000000000000000000), (1969909769524056480108093608806743610529026276653/12879317617862050078282695724000000000000000000000000), (1347407249138190164590988241091695305640839378665529/8654901439203297652605971526528000000000000000000000000)]
    reserve := (29948139/250000000000) }

theorem tilt_040_018_valid : tilt_040_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_018]
  · intro i; fin_cases i <;> norm_num [tilt_040_018]
  · norm_num [tilt_040_018]
  · norm_num [tilt_040_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_018]

def tilt_040_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (65229/10000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-45899337171823206838026631746857426102333657/1699446406424844030491297147150000000000000000), (19592738637959/29876350000000), (-10137210165821671421276814659326102376152500571/2549169609637266045736945720725000000000000000), (19592738637959/29876350000000), (-20136722320127873222039549423411632473998000171/5098339219274532091473891441450000000000000000)]
    bernstein := [(20902468356620575576493224568537130048898520317/117149338678183182248940520253906250000000000000000), (440287231948784245260824401977951984005288415079/2276044294318987540836558679218750000000000000000000), (312516775470730040737707260811387146766880259748497/1529501765782359627442167432435000000000000000000000000), (40994318795635070721446804230056394829958527089513/194222446448553603484719673960000000000000000000000000), (9295917678228013819312836271001540665603987019042503/43505828004476007180577206967040000000000000000000000000)]
    reserve := (178425833/1000000000000) }

theorem tilt_040_019_valid : tilt_040_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_019]
  · intro i; fin_cases i <;> norm_num [tilt_040_019]
  · norm_num [tilt_040_019]
  · norm_num [tilt_040_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_019]

def tilt_040_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(2/25), (33/400)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5368943/100000000), (1/100000000), (4182689/100000000), (179473/4000000), (1/100000000), (2715017/50000000), (65229/10000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-46147351457329029525104799207481404004333657/1699446406424844030491297147150000000000000000), (19592738637959/29876350000000), (-10136412915881327329114748400777324839614500571/2549169609637266045736945720725000000000000000), (19592738637959/29876350000000), (-20134383777390667569654182403932205467216000171/5098339219274532091473891441450000000000000000)]
    bernstein := [(4042581624760563213479675870703860101384520317/117149338678183182248940520253906250000000000000000), (112796237641741702238108724373034691934070415079/2276044294318987540836558679218750000000000000000000), (92492086636954745852112197725116217742323685748497/1529501765782359627442167432435000000000000000000000000), (13060997872138065910986406707062313063900181089513/194222446448553603484719673960000000000000000000000000), (3040284964663139330484868152423058870428039093042503/43505828004476007180577206967040000000000000000000000000)]
    reserve := (34507933/1000000000000) }

theorem tilt_040_020_valid : tilt_040_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_040_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_040_020]
  · intro i; fin_cases i <;> norm_num [tilt_040_020]
  · norm_num [tilt_040_020]
  · norm_num [tilt_040_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_040_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_040_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_040_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_040_020]

def tiltBundle040_row : Alternative → Row
  | .zero => tilt_040_000
  | (.spike 0 false false) => tilt_040_001
  | (.spike 0 false true) => tilt_040_002
  | (.spike 0 true false) => tilt_040_003
  | (.spike 0 true true) => tilt_040_004
  | (.spike 1 false false) => tilt_040_005
  | (.spike 1 false true) => tilt_040_006
  | (.spike 1 true false) => tilt_040_007
  | (.spike 1 true true) => tilt_040_008
  | (.spike 2 false false) => tilt_040_009
  | (.spike 2 false true) => tilt_040_010
  | (.spike 2 true false) => tilt_040_011
  | (.spike 2 true true) => tilt_040_012
  | (.spike 3 false false) => tilt_040_013
  | (.spike 3 false true) => tilt_040_014
  | (.spike 3 true false) => tilt_040_015
  | (.spike 3 true true) => tilt_040_016
  | (.spike 4 false false) => tilt_040_017
  | (.spike 4 false true) => tilt_040_018
  | (.spike 4 true false) => tilt_040_019
  | (.spike 4 true true) => tilt_040_020

def tiltBundle040 : TiltBundle where
  interval := ⟨(2/25), (33/400)⟩
  lambda := ![(14932757/100000000), (14932757/100000000), (4950537/50000000), (7370083/50000000), (7370083/50000000), (3909361/25000000), (3778909/25000000)]
  row := tiltBundle040_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_040_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_040_001_valid | exact tilt_040_002_valid | exact tilt_040_003_valid | exact tilt_040_004_valid | exact tilt_040_005_valid | exact tilt_040_006_valid | exact tilt_040_007_valid | exact tilt_040_008_valid | exact tilt_040_009_valid | exact tilt_040_010_valid | exact tilt_040_011_valid | exact tilt_040_012_valid | exact tilt_040_013_valid | exact tilt_040_014_valid | exact tilt_040_015_valid | exact tilt_040_016_valid | exact tilt_040_017_valid | exact tilt_040_018_valid | exact tilt_040_019_valid | exact tilt_040_020_valid
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
