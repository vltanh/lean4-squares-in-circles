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

def tilt_013_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1653801/100000000), 0, (8988487/100000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := .zero
    polynomial := [(-62463422280069055091762878336120703408559739/1535891925717651421554494252100000000000000000), (-962715966816050403/356319837031250000), (-27122292466624482115098497591652162648248559739/767945962858825710777247126050000000000000000), (-962715966816050403/356319837031250000), (-54182121510968895175105232304968204593088559739/1535891925717651421554494252100000000000000000)]
    bernstein := [(1534593577875940338391184800261253965473705409061/245742708114824227448719080336000000000000000000000), (1870199917000076540131991850555567653451174424487/163828472076549484965812720224000000000000000000000), (38025102336922852440050107757004084343411924797983/2948912497377890729384628964032000000000000000000000), (7011063268197475868797845649816774025991834048887/655313888306197939863250880896000000000000000000000), (18996212405837934873984589156419364955648988435461/3931883329837187639179505285376000000000000000000000)]
    reserve := (4831326571/1000000000000) }

theorem tilt_013_000_valid : tilt_013_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_000]
  · intro i; fin_cases i <;> norm_num [tilt_013_000]
  · norm_num [tilt_013_000]
  · norm_num [tilt_013_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_000]

def tilt_013_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(17191/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1631781/100000000), 0, (8990141/100000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-62522799942288147276344019106510287626205329/1535891925717651421554494252100000000000000000), (-7701733706073275626153/2850558696250000000000), (-27122378882651766441606433382569717605274425329/767945962858825710777247126050000000000000000), (-7701733706073275626153/2850558696250000000000), (-54182234965361244735936522746032924922922645329/1535891925717651421554494252100000000000000000)]
    bernstein := [(1525049709924183510032091553779373444312538851471/245742708114824227448719080336000000000000000000000), (1863846737239076831327927630070157640813586559957/163828472076549484965812720224000000000000000000000), (37910879470698590434745480015556669865075253473213/2948912497377890729384628964032000000000000000000000), (6985702565764258258994102161653480494294033548357/655313888306197939863250880896000000000000000000000), (18844134993952553140126262858749298426635542861871/3931883329837187639179505285376000000000000000000000)]
    reserve := (4792648563/1000000000000) }

theorem tilt_013_001_valid : tilt_013_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_001]
  · intro i; fin_cases i <;> norm_num [tilt_013_001]
  · norm_num [tilt_013_001]
  · norm_num [tilt_013_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_001]

def tilt_013_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1273/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(83791/5000000), 0, (4493417/50000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (4469/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-92887140925372649491907169982202940936329456039/2287967005344061400975678270878300000000000000000), (-3080692873530483624281/1140223478500000000000), (-40403053841615498255935561345219854996478876256039/1143983502672030700487839135439150000000000000000), (-3080692873530483624281/1140223478500000000000), (-80713220542305623862379215520457507052021423056039/2287967005344061400975678270878300000000000000000)]
    bernstein := [(2312164497062063846260446279333764482302263561872761/366074720855049824156108523340528000000000000000000000), (8410130879991294730097086104933298579880836032217161/732149441710099648312217046681056000000000000000000000), (56957686506624374102877230018436051920034469706549083/4392896650260597889873302280086336000000000000000000000), (31540923132100907893402223845214601368829167805530361/2928597766840398593248868186724224000000000000000000000), (28714735989998374523277186287233260922656099409779161/5857195533680797186497736373448448000000000000000000000)]
    reserve := (490247181/100000000000) }

theorem tilt_013_002_valid : tilt_013_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_002]
  · intro i; fin_cases i <;> norm_num [tilt_013_002]
  · norm_num [tilt_013_002]
  · norm_num [tilt_013_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_002]

def tilt_013_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1631781/100000000), 0, (8990141/100000000), 0, 0]] i.1) i.2
    mu := ![(1766929/25000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-31183200302436186196450870748958578059611673/767573781046816365794288412600000000000000000), (-7701733706073275626153/2850558696250000000000), (-13554554018391046690360309661016580500728931673/383786890523408182897144206300000000000000000), (-7701733706073275626153/2850558696250000000000), (-27077924836479657194524168451284202423398251673/767573781046816365794288412600000000000000000)]
    bernstein := [(772293636514620538535983745469494432288315129927/122811804967490618527086146016000000000000000000000), (938222178994484517144621078606726432300112126909/81874536644993745684724097344000000000000000000000), (19067635110135900579388943156452349835331737185381/1473741659609887422325033752192000000000000000000000), (3518109837453725164998969113867450574665938497709/327498146579974982738896389376000000000000000000000), (9579108292202304696977072931482557491102950314727/1964988879479849896433378336256000000000000000000000)]
    reserve := (4874891859/1000000000000) }

theorem tilt_013_003_valid : tilt_013_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_003]
  · intro i; fin_cases i <;> norm_num [tilt_013_003]
  · norm_num [tilt_013_003]
  · norm_num [tilt_013_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_003]

def tilt_013_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(83791/5000000), 0, (4493417/50000000), 0, 0]] i.1) i.2
    mu := ![(7074571/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-20765514659686982300433158631066665730801827/512212168849093229342516947900000000000000000), (-3080692873530483624281/1140223478500000000000), (-9045090543911611898004666988968050482719201827/256106084424546614671258473950000000000000000), (-3080692873530483624281/1140223478500000000000), (-18069415573163536813708900819305034299707601827/512212168849093229342516947900000000000000000)]
    bernstein := [(522345990439969686180533313139789754342666616573/81953947015854916694802711664000000000000000000000), (1892215952398662267182556089519026630228800565773/163907894031709833389605423328000000000000000000000), (1829673203436882410551868232632684323338435122017/140492480598608428619661791424000000000000000000000), (7098751200952327355879824620246370191579818453373/655631576126839333558421693312000000000000000000000), (6503615429297717890273528888093550489225425431773/1311263152253678667116843386624000000000000000000000)]
    reserve := (1239952373/250000000000) }

theorem tilt_013_004_valid : tilt_013_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_004]
  · intro i; fin_cases i <;> norm_num [tilt_013_004]
  · norm_num [tilt_013_004]
  · norm_num [tilt_013_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_004]

def tilt_013_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1631781/100000000), 0, (8990141/100000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (138729/4000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-3338094548910781263169697088652571090226303/81876770638825797693874455100000000000000000), (-7701733706073275626153/2850558696250000000000), (-1445870341059942969479368525653000260233046303/40938385319412898846937227550000000000000000), (-7701733706073275626153/2850558696250000000000), (-2888402587570975157695567354217347949375866303/81876770638825797693874455100000000000000000)]
    bernstein := [(80483465758392963460552274578648797928425011297/13100283302212127631019912816000000000000000000000), (296450479621279067132090942454890780701389610097/26200566604424255262039825632000000000000000000000), (2011227343124375711777329007664766150553058665491/157203399626545531572238953792000000000000000000000), (1110698972622045203981063952275298246529746366497/104802266417697021048159302528000000000000000000000), (991564529140427695330257754828163635453793084097/209604532835394042096318605056000000000000000000000)]
    reserve := (4730644493/1000000000000) }

theorem tilt_013_005_valid : tilt_013_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_005]
  · intro i; fin_cases i <;> norm_num [tilt_013_005]
  · norm_num [tilt_013_005]
  · norm_num [tilt_013_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_005]

def tilt_013_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(83791/5000000), 0, (4493417/50000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (17357/500000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-466667246033453703411711414655587533425547/11524461334510893842629524337500000000000000), (-3080692873530483624281/1140223478500000000000), (-203508475298651358783121109067409421003575547/5762230667255446921314762168750000000000000), (-3080692873530483624281/1140223478500000000000), (-406550283351269263862830506720163254473725547/11524461334510893842629524337500000000000000)]
    bernstein := [(11839968612409390967177988218672449608753816853/1843913813521743014820723894000000000000000000000), (14249497119535668116462722857288433135959984351/1229275875681162009880482596000000000000000000000), (289213346916902025515363825845519917560625488959/22126965762260916177848686728000000000000000000000), (53471803630379631044581088541900335331733975551/4917103502724648039521930384000000000000000000000), (147722187187417555388746270535658931534235204053/29502621016347888237131582304000000000000000000000)]
    reserve := (5007086899/1000000000000) }

theorem tilt_013_006_valid : tilt_013_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_006]
  · intro i; fin_cases i <;> norm_num [tilt_013_006]
  · norm_num [tilt_013_006]
  · norm_num [tilt_013_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_006]

def tilt_013_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1631781/100000000), 0, (8990141/100000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2453899/50000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-12515810912044752649963254446074865334723929/307074020728659215132656129260000000000000000), (-7698862674176932471159/2849590213750000000000), (-5422688637729915409974269269113748543677555929/153537010364329607566328064630000000000000000), (-7698862674176932471159/2849590213750000000000), (-10832861464547786067298575283781422222020387929/307074020728659215132656129260000000000000000)]
    bernstein := [(17774225079127719877216511515029885664435933463/2890108430387380848307351804800000000000000000000), (52976989522380672170943208779486486294862572251/4679223173008140421069045779200000000000000000000), (7547574463902243108846461151804196331637127205413/589582119799025693054699768179200000000000000000000), (1389642287914048278943962370727628988461743794157/131018248844227931789933281817600000000000000000000), (3725934074771737930087054275472533537183887679271/786109493065367590739599690905600000000000000000000)]
    reserve := (4739713879/1000000000000) }

theorem tilt_013_007_valid : tilt_013_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_007]
  · intro i; fin_cases i <;> norm_num [tilt_013_007]
  · norm_num [tilt_013_007]
  · norm_num [tilt_013_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_007]

def tilt_013_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(83791/5000000), 0, (4493417/50000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (982227/20000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-8297674092459941944100916119146310487643493/204855208084663600595150433300000000000000000), (-410912263277184001813/152081480500000000000), (-3617478244053610399601020395030512088058243493/102427604042331800297575216650000000000000000), (-410912263277184001813/152081480500000000000), (-7226658814014760857257939873941877865628843493/204855208084663600595150433300000000000000000)]
    bernstein := [(210254920697867744175118672242146120768373482107/32776833293546176095224069328000000000000000000000), (253139920991946411720239671687242190843068734969/21851222195697450730149379552000000000000000000000), (5137911915676963819249570787724141588271542745921/393321999522554113142688831936000000000000000000000), (949761728768893711952098645754935792514979577769/87404888782789802920597518208000000000000000000000), (2621113190284695390337652982552296824962161898907/524429332696738817523585109248000000000000000000000)]
    reserve := (4998029337/1000000000000) }

theorem tilt_013_008_valid : tilt_013_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_008]
  · intro i; fin_cases i <;> norm_num [tilt_013_008]
  · norm_num [tilt_013_008]
  · norm_num [tilt_013_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_008]

def tilt_013_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1631781/100000000), 0, (8990141/100000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (1734113/50000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-23471015624960445401369481404102710541425193/575696209545793906035715052643750000000000000), (-7701733706073275626153/2850558696250000000000), (-10166278798400132745820448582017465804398291443/287848104772896953017857526321875000000000000), (-7701733706073275626153/2850558696250000000000), (-20309086581175305046239527682630828898255157693/575696209545793906035715052643750000000000000)]
    bernstein := [(565894456820694724675640298117860590897347507907/92111393527327024965714408423000000000000000000000), (694802632859084184759203602537587467170968908569/61407595684884683310476272282000000000000000000000), (14141385573404475219152997558368497399294008613321/1105336722327924299588572901076000000000000000000000), (2603187976596808725508884142653978596594425021369/245630382739538733241905089128000000000000000000000), (6971859209847398496016300502787503689071331544707/1473782296437232399451430534768000000000000000000000)]
    reserve := (4730589603/1000000000000) }

theorem tilt_013_009_valid : tilt_013_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_009]
  · intro i; fin_cases i <;> norm_num [tilt_013_009]
  · norm_num [tilt_013_009]
  · norm_num [tilt_013_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_009]

def tilt_013_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(83791/5000000), 0, (4493417/50000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (3471401/100000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-745930852997776255360012014747085956330190501/18439143446947030660228368227100000000000000000), (-3080692873530483624281/1140223478500000000000), (-325612917321012224978806820897004301033641790501/9219571723473515330114184113550000000000000000), (-3080692873530483624281/1140223478500000000000), (-650479903789026673702253629779261516110953390501/18439143446947030660228368227100000000000000000)]
    bernstein := [(19062458458070160534461842419803296642930106048699/2950262951511524905636538916336000000000000000000000), (22878105599939299792581761661750791893191184229433/1966841967674349937091025944224000000000000000000000), (464160277783015035139373360721015228086406041303297/35403155418138298867638466996032000000000000000000000), (85869934716532188507700012692193317303134069709033/7867367870697399748364103776896000000000000000000000), (238244533293913427932570806025961804527330378446299/47204207224184398490184622661376000000000000000000000)]
    reserve := (315443987/62500000000) }

theorem tilt_013_010_valid : tilt_013_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_010]
  · intro i; fin_cases i <;> norm_num [tilt_013_010]
  · norm_num [tilt_013_010]
  · norm_num [tilt_013_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_010]

def tilt_013_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11503/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1631781/100000000), 0, (8990141/100000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-62617442056330472459877024855797932156377329/1535891925717651421554494252100000000000000000), (-7701733706073275626153/2850558696250000000000), (-27122473524765808766789966388319005249804597329/767945962858825710777247126050000000000000000), (-7701733706073275626153/2850558696250000000000), (-54182329607475287061120055751782212567452817329/1535891925717651421554494252100000000000000000)]
    bernstein := [(1509831163344063578194800696288170916216351079471/245742708114824227448719080336000000000000000000000), (1853713690014907200902599303511177403901661035957/163828472076549484965812720224000000000000000000000), (37728674188817963864432186748010848752654528557213/2948912497377890729384628964032000000000000000000000), (6945246185200927639764798793022738949914999224357/655313888306197939863250880896000000000000000000000), (18601548232597151187369278989169458679254142289871/3931883329837187639179505285376000000000000000000000)]
    reserve := (4730951219/1000000000000) }

theorem tilt_013_011_valid : tilt_013_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_011]
  · intro i; fin_cases i <;> norm_num [tilt_013_011]
  · norm_num [tilt_013_011]
  · norm_num [tilt_013_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_011]

def tilt_013_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3407/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(83791/5000000), 0, (4493417/50000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (2991/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-62089295497050042428448727194184552069719739453/1531284249940498467289830769343700000000000000000), (-3080692873530483624281/1140223478500000000000), (-27040766539122954201943545983434018362346684939453/765642124970249233644915384671850000000000000000), (-3080692873530483624281/1140223478500000000000), (-54019443782748858361458643239673852172623650139453/1531284249940498467289830769343700000000000000000)]
    bernstein := [(1560014179832270217933133886572602240740528169818147/245005479990479754766372923094992000000000000000000000), (1884582716552547711069941465253141381035335734185649/163336986660319836510915282063328000000000000000000000), (38270560898392488333043533778424654197929000192666041/2940065759885757057196475077139904000000000000000000000), (7069863505139976467266065848336935692727598947444449/653347946641279346043661128253312000000000000000000000), (19417931404165036467460089968589485917401529311930947/3920087679847676076261966769519872000000000000000000000)]
    reserve := (2476721567/500000000000) }

theorem tilt_013_012_valid : tilt_013_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_012]
  · intro i; fin_cases i <;> norm_num [tilt_013_012]
  · norm_num [tilt_013_012]
  · norm_num [tilt_013_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_012]

def tilt_013_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1631781/100000000), 0, (8990141/100000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (87797/2000000), (2787/2000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-250063140138472066439758861784021674709011/6140521116998008294037284455000000000000000), (-7701733706073275626153/2850558696250000000000), (-108435811705204271547103309087054862974790011/3070260558499004147018642227500000000000000), (-7701733706073275626153/2850558696250000000000), (-216621560270270071027766859312325704274871011/6140521116998008294037284455000000000000000)]
    bernstein := [(6081743261906933090964074936346772765862480189/982483378719681327045965512800000000000000000000), (7441415661618052017717851838578760485327165263/654988919146454218030643675200000000000000000000), (151383575200037109897753267080129944285932249767/11789800544636175924551586153600000000000000000000), (27887933640918752141945626754936186182240160863/2619955676585816872122574700800000000000000000000), (75093195546304966399129716140129230719639173789/15719734059514901232735448204800000000000000000000)]
    reserve := (95540033/20000000000) }

theorem tilt_013_013_valid : tilt_013_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_013]
  · intro i; fin_cases i <;> norm_num [tilt_013_013]
  · norm_num [tilt_013_013]
  · norm_num [tilt_013_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_013]

def tilt_013_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(83791/5000000), 0, (4493417/50000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (137319/3125000), (2787/2000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-41489611031148211916567366485258924570002281/1024436181057119796413886110400000000000000000), (-3080692873530483624281/1140223478500000000000), (-18090348329787433440444722733644612397408402281/512218090528559898206943055200000000000000000), (-3080692873530483624281/1140223478500000000000), (-36139207048543718668972878100803965870246802281/1024436181057119796413886110400000000000000000)]
    bernstein := [(1051441367676356340312461595059330763993194412919/163909788969139167426221777664000000000000000000000), (1265977824517288568268408750280622023480900180173/109273192646092778284147851776000000000000000000000), (3670911995297811359319578771549794361958423458851/280988209661381429873523047424000000000000000000000), (4750465708355501022798424295655704227035497347773/437092770584371113136591407104000000000000000000000), (13114775327644045815364653516838035243585282538519/2622556623506226678819548442624000000000000000000000)]
    reserve := (1250189911/250000000000) }

theorem tilt_013_014_valid : tilt_013_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_014]
  · intro i; fin_cases i <;> norm_num [tilt_013_014]
  · norm_num [tilt_013_014]
  · norm_num [tilt_013_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_014]

def tilt_013_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11503/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1631781/100000000), 0, (8990141/100000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-62617442056330472459877024855797932156377329/1535891925717651421554494252100000000000000000), (-7701733706073275626153/2850558696250000000000), (-27122473524765808766789966388319005249804597329/767945962858825710777247126050000000000000000), (-7701733706073275626153/2850558696250000000000), (-54182329607475287061120055751782212567452817329/1535891925717651421554494252100000000000000000)]
    bernstein := [(1509831163344063578194800696288170916216351079471/245742708114824227448719080336000000000000000000000), (1853713690014907200902599303511177403901661035957/163828472076549484965812720224000000000000000000000), (37728674188817963864432186748010848752654528557213/2948912497377890729384628964032000000000000000000000), (6945246185200927639764798793022738949914999224357/655313888306197939863250880896000000000000000000000), (18601548232597151187369278989169458679254142289871/3931883329837187639179505285376000000000000000000000)]
    reserve := (4730951219/1000000000000) }

theorem tilt_013_015_valid : tilt_013_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_015]
  · intro i; fin_cases i <;> norm_num [tilt_013_015]
  · norm_num [tilt_013_015]
  · norm_num [tilt_013_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_015]

def tilt_013_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3407/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(83791/5000000), 0, (4493417/50000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (2991/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-62089295497050042428448727194184552069719739453/1531284249940498467289830769343700000000000000000), (-3080692873530483624281/1140223478500000000000), (-27040766539122954201943545983434018362346684939453/765642124970249233644915384671850000000000000000), (-3080692873530483624281/1140223478500000000000), (-54019443782748858361458643239673852172623650139453/1531284249940498467289830769343700000000000000000)]
    bernstein := [(1560014179832270217933133886572602240740528169818147/245005479990479754766372923094992000000000000000000000), (1884582716552547711069941465253141381035335734185649/163336986660319836510915282063328000000000000000000000), (38270560898392488333043533778424654197929000192666041/2940065759885757057196475077139904000000000000000000000), (7069863505139976467266065848336935692727598947444449/653347946641279346043661128253312000000000000000000000), (19417931404165036467460089968589485917401529311930947/3920087679847676076261966769519872000000000000000000000)]
    reserve := (2476721567/500000000000) }

theorem tilt_013_016_valid : tilt_013_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_016]
  · intro i; fin_cases i <;> norm_num [tilt_013_016]
  · norm_num [tilt_013_016]
  · norm_num [tilt_013_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_016]

def tilt_013_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1631781/100000000), 0, (8990141/100000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (87797/2000000), (2787/2000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-50012654256707963910529367461478391136931/1228104223399601658807456891000000000000000), (-7701733706073275626153/2850558696250000000000), (-21687162367269867860043239412515646651153131/614052111699800829403728445500000000000000), (-7701733706073275626153/2850558696250000000000), (-43324312080283027756175949457569814911169331/1228104223399601658807456891000000000000000)]
    bernstein := [(1216344434729778664531715116842661642939589869/196496675743936265409193102560000000000000000000), (1488280324061816579036054992643614922421577823/130997783829290843606128735040000000000000000000), (30276664543831847280312399587722181848155898807/2357960108927235184910317230720000000000000000000), (5577575516146014984407748504377532456884909423/523991135317163374424514940160000000000000000000), (15018571879027231310484428878130200630517499469/3143946811902980246547089640960000000000000000000)]
    reserve := (2388490133/500000000000) }

theorem tilt_013_017_valid : tilt_013_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_017]
  · intro i; fin_cases i <;> norm_num [tilt_013_017]
  · norm_num [tilt_013_017]
  · norm_num [tilt_013_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_017]

def tilt_013_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(83791/5000000), 0, (4493417/50000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (137319/3125000), (2787/2000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-41473973418662035832267900860903563623276281/1024436181057119796413886110400000000000000000), (-3080692873530483624281/1140223478500000000000), (-18090332692174947264360423268020257036461676281/512218090528559898206943055200000000000000000), (-3080692873530483624281/1140223478500000000000), (-36139191410931232492888578635179610509300076281/1024436181057119796413886110400000000000000000)]
    bernstein := [(1053955911401745940843899966921297159587681938919/163909788969139167426221777664000000000000000000000), (1267652096773345983086099636283477453964012822173/109273192646092778284147851776000000000000000000000), (3675212792222271881608376502750624927775528512851/280988209661381429873523047424000000000000000000000), (4757150271652129255025663967702017304849620389773/437092770584371113136591407104000000000000000000000), (13154857671606224840817128104651320777594312464519/2622556623506226678819548442624000000000000000000000)]
    reserve := (2508021667/500000000000) }

theorem tilt_013_018_valid : tilt_013_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_018]
  · intro i; fin_cases i <;> norm_num [tilt_013_018]
  · norm_num [tilt_013_018]
  · norm_num [tilt_013_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_018]

def tilt_013_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(411203/25000000), 0, (8990141/100000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-10432820155482503844028588536437203970857519/255981987619608570259082375350000000000000000), (-15403465776973144437193/5701117392500000000000), (-4520408833977105456411108325803195984202178149/127990993809804285129541187675000000000000000), (-15403465776973144437193/5701117392500000000000), (-9030384847798728408978188063069954764433498779/255981987619608570259082375350000000000000000)]
    bernstein := [(252187907895974203275509858231619304003158142021/40957118019137371241453180056000000000000000000000), (927954382811966413235941611577523946083158142421/81914236038274742482906360112000000000000000000000), (6294691626511543430705840360875157466991314048863/491485416229648454897438160672000000000000000000000), (3477006204686103044031432234196920297773514723621/327656944153098969931625440448000000000000000000000), (3109019964196016149337730637285890102103702184421/655313888306197939863250880896000000000000000000000)]
    reserve := (4744321797/1000000000000) }

theorem tilt_013_019_valid : tilt_013_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_019]
  · intro i; fin_cases i <;> norm_num [tilt_013_019]
  · norm_num [tilt_013_019]
  · norm_num [tilt_013_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_019]

def tilt_013_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662789/100000000), 0, (4493417/50000000), 0, 0]] i.1) i.2
    mu := ![(7071143/100000000), (1/100000000), (2454733/50000000), (867453/25000000), (1/100000000), (1098007/25000000), (2787/2000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-31064921839326378532560035605305543658122557/767945962858825710777247126050000000000000000), (-7701733001412912468259/2850558696250000000000), (-13560993328983510331553758204711006214633774447/383972981429412855388623563025000000000000000), (-7701733001412912468259/2850558696250000000000), (-27090921736127694284574956373816706885609426337/767945962858825710777247126050000000000000000)]
    bernstein := [(794116919181844420858795078314205777251063496063/122871354057412113724359540168000000000000000000000), (952958658711956477846463682541552950705363332421/81914236038274742482906360112000000000000000000000), (19333684434520815932747768801026214146387972356589/1474456248688945364692314482016000000000000000000000), (3576836374207677074945046575575404449952438913621/327656944153098969931625440448000000000000000000000), (9925667112519905781934184720187967752567009623263/1965941664918593819589752642688000000000000000000000)]
    reserve := (5048810597/1000000000000) }

theorem tilt_013_020_valid : tilt_013_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_013_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_013_020]
  · intro i; fin_cases i <;> norm_num [tilt_013_020]
  · norm_num [tilt_013_020]
  · norm_num [tilt_013_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_013_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_013_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_013_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_013_020]

def tiltBundle013_row : Alternative → Row
  | .zero => tilt_013_000
  | (.spike 0 false false) => tilt_013_001
  | (.spike 0 false true) => tilt_013_002
  | (.spike 0 true false) => tilt_013_003
  | (.spike 0 true true) => tilt_013_004
  | (.spike 1 false false) => tilt_013_005
  | (.spike 1 false true) => tilt_013_006
  | (.spike 1 true false) => tilt_013_007
  | (.spike 1 true true) => tilt_013_008
  | (.spike 2 false false) => tilt_013_009
  | (.spike 2 false true) => tilt_013_010
  | (.spike 2 true false) => tilt_013_011
  | (.spike 2 true true) => tilt_013_012
  | (.spike 3 false false) => tilt_013_013
  | (.spike 3 false true) => tilt_013_014
  | (.spike 3 true false) => tilt_013_015
  | (.spike 3 true true) => tilt_013_016
  | (.spike 4 false false) => tilt_013_017
  | (.spike 4 false true) => tilt_013_018
  | (.spike 4 true false) => tilt_013_019
  | (.spike 4 true true) => tilt_013_020

def tiltBundle013 : TiltBundle where
  interval := ⟨(-1/20), (-1/40)⟩
  lambda := ![(17190771/100000000), (17190771/100000000), (3750209/50000000), (11502587/100000000), (11502587/100000000), (13031181/100000000), (11040843/50000000)]
  row := tiltBundle013_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_013_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_013_001_valid | exact tilt_013_002_valid | exact tilt_013_003_valid | exact tilt_013_004_valid | exact tilt_013_005_valid | exact tilt_013_006_valid | exact tilt_013_007_valid | exact tilt_013_008_valid | exact tilt_013_009_valid | exact tilt_013_010_valid | exact tilt_013_011_valid | exact tilt_013_012_valid | exact tilt_013_013_valid | exact tilt_013_014_valid | exact tilt_013_015_valid | exact tilt_013_016_valid | exact tilt_013_017_valid | exact tilt_013_018_valid | exact tilt_013_019_valid | exact tilt_013_020_valid
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
