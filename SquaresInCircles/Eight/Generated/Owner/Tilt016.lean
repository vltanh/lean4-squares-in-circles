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

def tilt_016_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(162937/100000000), 0, (99283/10000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := .zero
    polynomial := [(-19024534351066282808615809251176774726669623/6063799990375815016106745530550000000000000000), (-6135740493059649369/2961429222800000000), (-668230208287200950113877298565253622874789169623/3031899995187907508053372765275000000000000000), (-6135740493059649369/2961429222800000000), (-1336441392040050833944945981321256068974851669623/6063799990375815016106745530550000000000000000)]
    bernstein := [(4779446382022236781498526769966253044627355534352777/3973971961692694128955716750901248000000000000000000000), (1533377264214315558010557597222583493735942629191553/883104880376154250879048166866944000000000000000000000), (91143700533505504720981437826767902058469620243096731/47687663540312329547468601010814976000000000000000000000), (469393687945376710211721158557992046517028381709381/271724578577278231039707128266752000000000000000000000), (5795620091446431934042285886984616561386647472389229/4891042414391008158714728308801536000000000000000000000)]
    reserve := (148118223/125000000000) }

theorem tilt_016_000_valid : tilt_016_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_000]
  · intro i; fin_cases i <;> norm_num [tilt_016_000]
  · norm_num [tilt_016_000]
  · norm_num [tilt_016_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_000]

def tilt_016_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(591/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(145557/100000000), 0, (992993/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-76658730170738391171837291391392247869350617/24255199961503260064426982122200000000000000000), (-766966286493369254583/370178652850000000000), (-2672924072745361571211514015570694279360221100617/12127599980751630032213491061100000000000000000), (-766966286493369254583/370178652850000000000), (-5345771486760552404031856193849997166472572850617/24255199961503260064426982122200000000000000000)]
    bernstein := [(18749887341603345983236855154334853944874352478438983/15895887846770776515822867003604992000000000000000000000), (6051772627162837732790960660283623349586160153947087/3532419521504617003516192667467776000000000000000000000), (360161962993371494637641931233675608793769853630670549/190750654161249318189874404043259904000000000000000000000), (1852435184628281404754510839520372658704125859789899/1086898314309112924158828513067008000000000000000000000), (22730046326988954500668434750599688443273922140528291/19564169657564032634858913235206144000000000000000000000)]
    reserve := (1161820139/1000000000000) }

theorem tilt_016_001_valid : tilt_016_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_001]
  · intro i; fin_cases i <;> norm_num [tilt_016_001]
  · norm_num [tilt_016_001]
  · norm_num [tilt_016_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_001]

def tilt_016_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (547/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(180317/100000000), 0, (992667/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (3841/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-287544097491417302271233943451570929665317823737/93164223052134021907464038331370200000000000000000), (-3067881460252971391737/1480714611400000000000), (-10266694386999348730301880322679606526873689956073737/46582111526067010953732019165685100000000000000000), (-3067881460252971391737/1480714611400000000000), (-20533101229901206043301489411415761482817714594323737/93164223052134021907464038331370200000000000000000)]
    bernstein := [(76546229546037225188890779011601790576136685280710021863/61056105219446552597275632160846774272000000000000000000000), (24250924739097179831902574212901997537264909692953559407/13568023382099233910505696035743727616000000000000000000000), (1437702467959808101790070437044673972503309160913033515189/732673262633358631167307585930161291264000000000000000000000), (7424681303560197284025433824999481208476854980373650539/4174776425261302741694060318690377728000000000000000000000), (92876005805849394683606782421758296681575937206933786051/75145975654703449350493085736426799104000000000000000000000)]
    reserve := (1235941179/1000000000000) }

theorem tilt_016_002_valid : tilt_016_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_002]
  · intro i; fin_cases i <;> norm_num [tilt_016_002]
  · norm_num [tilt_016_002]
  · norm_num [tilt_016_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_002]

def tilt_016_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(145557/100000000), 0, (992993/100000000), 0, 0]] i.1) i.2
    mu := ![(1152253/20000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-15020417289690534744947479364054478490997561/4848646498746296421357781997400000000000000000), (-766966286493369254583/370178652850000000000), (-534320747692961556332171355610935055232270747561/2424323249373148210678890998700000000000000000), (-766966286493369254583/370178652850000000000), (-1068626474968633422129597763742506055986050497561/4848646498746296421357781997400000000000000000)]
    bernstein := [(3947217624698555005052700639700697710555144017419239/3177608969418372822701036009816064000000000000000000000), (1253998783238228235270650787449558758020479531433071/706135326537416182822452446625792000000000000000000000), (74385851069966230580965595561911654412947574776686517/38131307633020473872412432117792768000000000000000000000), (4990915704604043696009817612539682905473544207605871/2824541306149664731289809786503168000000000000000000000), (62254221122719184508664190560061950325474399457649639/50841743510693965163216576157057024000000000000000000000)]
    reserve := (612235309/500000000000) }

theorem tilt_016_003_valid : tilt_016_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_003]
  · intro i; fin_cases i <;> norm_num [tilt_016_003]
  · norm_num [tilt_016_003]
  · norm_num [tilt_016_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_003]

def tilt_016_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(180317/100000000), 0, (992667/100000000), 0, 0]] i.1) i.2
    mu := ![(2883477/50000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-12251976434973941254346109827977565999955437/4044528606207570318372635512200000000000000000), (-3067881460252971391737/1480714611400000000000), (-445706691309073079297198764979296458451170705437/2022264303103785159186317756100000000000000000), (-3067881460252971391737/1480714611400000000000), (-891401130641711184653143183848764939336341455437/4044528606207570318372635512200000000000000000)]
    bernstein := [(3474588553173335352210127260845541258540776507850163/2650622267364193283848690409275392000000000000000000000), (1086467773586750276081203189049767420333930144038107/589027170525376285299708979838976000000000000000000000), (64232702567196521261438553734023332406070486618360089/31807467208370319406184284911304704000000000000000000000), (4324905580045116884723789285627838736155353116095707/2356108682101505141198835919355904000000000000000000000), (54839991766756317773444227822638237909201652427926963/42409956277827092541579046548406272000000000000000000000)]
    reserve := (1293092391/1000000000000) }

theorem tilt_016_004_valid : tilt_016_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_004]
  · intro i; fin_cases i <;> norm_num [tilt_016_004]
  · norm_num [tilt_016_004]
  · norm_num [tilt_016_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_004]

def tilt_016_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(145557/100000000), 0, (992993/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (1038513/25000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-128408830120603078886648318182274779087121/40407610172365885201345145826000000000000000), (-766966286493369254583/370178652850000000000), (-4452921068843646642550972049353558033209539621/20203805086182942600672572913000000000000000), (-766966286493369254583/370178652850000000000), (-8905713728857172682023057450388933791639992121/40407610172365885201345145826000000000000000)]
    bernstein := [(30777131424875802648740805495682950872733413652679/26481531402561706525553554768527360000000000000000000), (9979872072312269145254074021351939451014121777231/5884784756124823672345234393006080000000000000000000), (84928457564915048813907871745619032692718569290691/45396910975820068329520379603189760000000000000000000), (3054656670262324121163983383812114709916406941387/1810703001884561129952379813232640000000000000000000), (37301936003421881393175848973419576668004448482083/32592654033922100339142836638187520000000000000000000)]
    reserve := (57224453/50000000000) }

theorem tilt_016_005_valid : tilt_016_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_005]
  · intro i; fin_cases i <;> norm_num [tilt_016_005]
  · norm_num [tilt_016_005]
  · norm_num [tilt_016_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_005]

def tilt_016_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(180317/100000000), 0, (992667/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (4157697/100000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-9748814392569761165197686147246095128865443/3235445287460342312594586851880000000000000000), (-3067881460252971391737/1480714611400000000000), (-356545729589220375521702172777214616966623415443/1617722643730171156297293425940000000000000000), (-3067881460252971391737/1480714611400000000000), (-713081710364048181282239147868281987838117965443/3235445287460342312594586851880000000000000000)]
    bernstein := [(2813749588551261279868461386531078458859427150872957/2120381423590009937981988439248076800000000000000000000), (876733322259049980416142713299031261550895600783573/471195871908891097329330764277350400000000000000000000), (51794102657485393537219304855229797796263368980913271/25444577083080119255783861270976921600000000000000000000), (268473915908753270785111352187345626341838699026921/144983345202735722255178696700723200000000000000000000), (3416711872521981768529401831691769506828717764279089/2609700213649243000593216540613017600000000000000000000)]
    reserve := (327308847/250000000000) }

theorem tilt_016_006_valid : tilt_016_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_006]
  · intro i; fin_cases i <;> norm_num [tilt_016_006]
  · norm_num [tilt_016_006]
  · norm_num [tilt_016_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_006]

def tilt_016_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(145557/100000000), 0, (992993/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (4313861/100000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-154017098183842446040341046329281077785394727/48489796153819253619366454398600000000000000000), (-1533190795558059710979/740042854550000000000), (-5343585337129325949049004084960996603176841644727/24244898076909626809683227199300000000000000000), (-1533190795558059710979/740042854550000000000), (-10687016657160468055651967828875663925275897894727/48489796153819253619366454398600000000000000000)]
    bernstein := [(36958032831126408593239983310127886141738906485362873/31778272807366986051987999554666496000000000000000000000), (11982251881134476087483751957873713636322291868181297/7061838401637108011552888789925888000000000000000000000), (713783073715229567800851103464268437505010422460530219/381339273688403832623855994655997952000000000000000000000), (3667981842442905420275338933544496387456020446310069/2172873354349879388170119627669504000000000000000000000), (44808903404367103554333353309327353226755695110345821/39111720378297828987062153298051072000000000000000000000)]
    reserve := (572832171/500000000000) }

theorem tilt_016_007_valid : tilt_016_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_007]
  · intro i; fin_cases i <;> norm_num [tilt_016_007]
  · norm_num [tilt_016_007]
  · norm_num [tilt_016_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_007]

def tilt_016_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(180317/100000000), 0, (992667/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (4317527/100000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-29261149724571481830218315413580705838952921/9706200738438757327668294818040000000000000000), (-6138730044078950206017/2962687027400000000000), (-1069620920611617472079972179453901653015102402921/4853100369219378663834147409020000000000000000), (-6138730044078950206017/2962687027400000000000), (-2139212580073510372678114140592389725324365852921/9706200738438757327668294818040000000000000000)]
    bernstein := [(8436142536599050941169600584269750833097799610031879/6361055715943224002260693691950694400000000000000000000), (2628916216717654631728660994743110187750040412966031/1413567936876272000502376375989043200000000000000000000), (155305354493858705077781965549692415416680303835612437/76332668591318688027128324303408332800000000000000000000), (804942159248662253347722295537678052766341391358987/434943980577314461693038884919705600000000000000000000), (10240805824799836452306186403791266339121125571920483/7828991650391660310474699928554700800000000000000000000)]
    reserve := (327015479/250000000000) }

theorem tilt_016_008_valid : tilt_016_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_008]
  · intro i; fin_cases i <;> norm_num [tilt_016_008]
  · norm_num [tilt_016_008]
  · norm_num [tilt_016_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_008]

def tilt_016_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(145557/100000000), 0, (992993/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (4154053/100000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-154094423211179415845026725070067612709707009/48489143879570218914439224271800000000000000000), (-766966286493369254583/370178652850000000000), (-5343506572738023189909830593519286156030080457009/24244571939785109457219612135900000000000000000), (-766966286493369254583/370178652850000000000), (-10686859051052835200403816160313502244447451207009/48489143879570218914439224271800000000000000000)]
    bernstein := [(36930082610212893249236184511208955401539557171692191/31777845332915138667766890018766848000000000000000000000), (11975297382627068931991747228418350000902996823780199/7061743407314475259503753337503744000000000000000000000), (713369408463855054787285272879712895784177237014903773/381334143994981664013202680225202176000000000000000000000), (3665419049524946298007132035596641684481650517318723/2172844125327530849078077950001152000000000000000000000), (44759276939895984940541326774594973133430208549346907/39111194255895555283405403100020736000000000000000000000)]
    reserve := (1144410897/1000000000000) }

theorem tilt_016_009_valid : tilt_016_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_009]
  · intro i; fin_cases i <;> norm_num [tilt_016_009]
  · norm_num [tilt_016_009]
  · norm_num [tilt_016_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_009]

def tilt_016_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(180317/100000000), 0, (992667/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2078849/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-71719479379627336492485033931359636591747787/24265845492318145680871926029400000000000000000), (-3067881460252971391737/1480714611400000000000), (-2674092218439873895596612919968548935913201997787/12132922746159072840435963014700000000000000000), (-3067881460252971391737/1480714611400000000000), (-5348112717400368163856733354903166512189812247787/24265845492318145680871926029400000000000000000)]
    bernstein := [(22018504520595545942293366913663064243969098532737813/15902864501845619953416225442627584000000000000000000000), (6778914754693272339192629392310838392999895420118957/3533969889299026656314716765028352000000000000000000000), (399440000422953031518850263057591586613429084879903039/190834374022147439440994705311531008000000000000000000000), (2076141714253058927126940897615947136824533550265889/1087375350553546663481451312316416000000000000000000000), (26751897697435015529433393333950104098021756820604201/19572756309963839942666123621695488000000000000000000000)]
    reserve := (1366792559/1000000000000) }

theorem tilt_016_010_valid : tilt_016_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_010]
  · intro i; fin_cases i <;> norm_num [tilt_016_010]
  · norm_num [tilt_016_010]
  · norm_num [tilt_016_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_010]

def tilt_016_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14149/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(145557/100000000), 0, (992993/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-76823221784180538967359530585057493646718617/24255199961503260064426982122200000000000000000), (-766966286493369254583/370178652850000000000), (-2672924237236975013359309537809887944605998468617/12127599980751630032213491061100000000000000000), (-766966286493369254583/370178652850000000000), (-5345771651252165846179651716089190831718350218617/24255199961503260064426982122200000000000000000)]
    bernstein := [(18642077695682800152554121942205443617969412979470983/15895887846770776515822867003604992000000000000000000000), (6027815395974915962908765853682154057380300976195087/3532419521504617003516192667467776000000000000000000000), (358868293564643714499247681910379773747108698468166549/190750654161249318189874404043259904000000000000000000000), (1845063944830333676878175989647329667621529369685899/1086898314309112924158828513067008000000000000000000000), (22597365306326334482692592781563043104928173646392291/19564169657564032634858913235206144000000000000000000000)]
    reserve := (577519151/500000000000) }

theorem tilt_016_011_valid : tilt_016_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_011]
  · intro i; fin_cases i <;> norm_num [tilt_016_011]
  · norm_num [tilt_016_011]
  · norm_num [tilt_016_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_011]

def tilt_016_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4191/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(180317/100000000), 0, (992667/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1839/50000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-45806962121757259237836722927816692819166001607/14868437576401498419493740040908600000000000000000), (-3067881460252971391737/1480714611400000000000), (-1638501259890744129784299115399122294170998573251607/7434218788200749209746870020454300000000000000000), (-3067881460252971391737/1480714611400000000000), (-3276956712819366502309360394075316771649177980501607/14868437576401498419493740040908600000000000000000)]
    bernstein := [(12270909634851724660024413589503228509205313484453699993/9744179250070486004199417473209860096000000000000000000000), (3882432062976018856950494641701749493372277636285448977/2165373166682330223155426105157746688000000000000000000000), (230103677452789168233606064852027664549352194263321445579/116930151000845832050393009678518321152000000000000000000000), (1188666785534513054065964909974986474605089576640209429/666268666671486222509361878510075904000000000000000000000), (14889638050826453047057243610617242035592737226894928061/11992836000086752005168513813181366272000000000000000000000)]
    reserve := (310386093/250000000000) }

theorem tilt_016_012_valid : tilt_016_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_012]
  · intro i; fin_cases i <;> norm_num [tilt_016_012]
  · norm_num [tilt_016_012]
  · norm_num [tilt_016_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_012]

def tilt_016_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(145557/100000000), 0, (992993/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (2733909/50000000), (3431/25000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-150729544058715021783441098576005940202568489/48486404206656193241800972825800000000000000000), (-766966286493369254583/370178652850000000000), (-5343201304445370804733868692366930318472195818489/24243202103328096620900486412900000000000000000), (-766966286493369254583/370178652850000000000), (-10686251879346682894445953943635284631004189068489/48486404206656193241800972825800000000000000000)]
    bernstein := [(39127669214450712012839277235843869420718597593254711/31776049860874202802946685551116288000000000000000000000), (37390282455325680011568195569112948333430673282965437/21184033240582801868631123700744192000000000000000000000), (739724235608502683007101875048864028297382034507175333/381312598330490433635360226613395456000000000000000000000), (11446828832551150815835708132157223932053655989812849/6518164074025477498040345754075136000000000000000000000), (47463879455085548669703833057656856493453881711364947/39108984444152864988242074524450816000000000000000000000)]
    reserve := (121363109/100000000000) }

theorem tilt_016_013_valid : tilt_016_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_013]
  · intro i; fin_cases i <;> norm_num [tilt_016_013]
  · norm_num [tilt_016_013]
  · norm_num [tilt_016_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_013]

def tilt_016_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(180317/100000000), 0, (992667/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (547323/10000000), (3431/25000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-29360317809183084978805619897614117939561139/9706879127871369403181391132600000000000000000), (-3067881460252971391737/1480714611400000000000), (-1069697168805126838309968837983073209200686811139/4853439563935684701590695566300000000000000000), (-3067881460252971391737/1480714611400000000000), (-2139364977292444493534958870346248804283434061139/9706879127871369403181391132600000000000000000)]
    bernstein := [(8368159376642483896813089144637706744381697060582061/6361500305241780652068956492660736000000000000000000000), (7842001264973701261207134051626669662350631320127887/4241000203494520434712637661773824000000000000000000000), (22072613455622307431045597040367263785771868292896769/10905429094700195403546782558846976000000000000000000000), (2401311609061117503124972028404617861837335824991499/1304923139536775518373119280545792000000000000000000000), (10160176966033671624524595868058510332059486409540897/7829538837220653110238715683274752000000000000000000000)]
    reserve := (259534493/200000000000) }

theorem tilt_016_014_valid : tilt_016_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_014]
  · intro i; fin_cases i <;> norm_num [tilt_016_014]
  · norm_num [tilt_016_014]
  · norm_num [tilt_016_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_014]

def tilt_016_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14149/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(145557/100000000), 0, (992993/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-76823221784180538967359530585057493646718617/24255199961503260064426982122200000000000000000), (-766966286493369254583/370178652850000000000), (-2672924237236975013359309537809887944605998468617/12127599980751630032213491061100000000000000000), (-766966286493369254583/370178652850000000000), (-5345771651252165846179651716089190831718350218617/24255199961503260064426982122200000000000000000)]
    bernstein := [(18642077695682800152554121942205443617969412979470983/15895887846770776515822867003604992000000000000000000000), (6027815395974915962908765853682154057380300976195087/3532419521504617003516192667467776000000000000000000000), (358868293564643714499247681910379773747108698468166549/190750654161249318189874404043259904000000000000000000000), (1845063944830333676878175989647329667621529369685899/1086898314309112924158828513067008000000000000000000000), (22597365306326334482692592781563043104928173646392291/19564169657564032634858913235206144000000000000000000000)]
    reserve := (577519151/500000000000) }

theorem tilt_016_015_valid : tilt_016_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_015]
  · intro i; fin_cases i <;> norm_num [tilt_016_015]
  · norm_num [tilt_016_015]
  · norm_num [tilt_016_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_015]

def tilt_016_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4191/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(180317/100000000), 0, (992667/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1839/50000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-45806962121757259237836722927816692819166001607/14868437576401498419493740040908600000000000000000), (-3067881460252971391737/1480714611400000000000), (-1638501259890744129784299115399122294170998573251607/7434218788200749209746870020454300000000000000000), (-3067881460252971391737/1480714611400000000000), (-3276956712819366502309360394075316771649177980501607/14868437576401498419493740040908600000000000000000)]
    bernstein := [(12270909634851724660024413589503228509205313484453699993/9744179250070486004199417473209860096000000000000000000000), (3882432062976018856950494641701749493372277636285448977/2165373166682330223155426105157746688000000000000000000000), (230103677452789168233606064852027664549352194263321445579/116930151000845832050393009678518321152000000000000000000000), (1188666785534513054065964909974986474605089576640209429/666268666671486222509361878510075904000000000000000000000), (14889638050826453047057243610617242035592737226894928061/11992836000086752005168513813181366272000000000000000000000)]
    reserve := (310386093/250000000000) }

theorem tilt_016_016_valid : tilt_016_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_016]
  · intro i; fin_cases i <;> norm_num [tilt_016_016]
  · norm_num [tilt_016_016]
  · norm_num [tilt_016_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_016]

def tilt_016_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(145557/100000000), 0, (992993/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (5467819/100000000), (3431/25000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-301462173099720263970716890730237021366803913/96972826148505550065927927167800000000000000000), (-766966286493369254583/370178652850000000000), (-10686404566338716560128591033991585389403677553913/48486413074252775032963963583900000000000000000), (-766966286493369254583/370178652850000000000), (-21372507670504333399993211351092440541785988303913/96972826148505550065927927167800000000000000000)]
    bernstein := [(78253366943951108847888305715150361869099577067670487/63552111344684597291206526348689408000000000000000000000), (224337764245120918963798508484306229626136057823817687/127104222689369194582413052697378816000000000000000000000), (211346416154403782217664245282334856704364521298383123/108946476590887881070639759454896128000000000000000000000), (68679763587036107442527223494752460350107444327786099/39108991596728982948434785445347328000000000000000000000), (94925332356778810059659453422118951281306142205494899/78217983193457965896869570890694656000000000000000000000)]
    reserve := (242719969/200000000000) }

theorem tilt_016_017_valid : tilt_016_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_017]
  · intro i; fin_cases i <;> norm_num [tilt_016_017]
  · norm_num [tilt_016_017]
  · norm_num [tilt_016_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_017]

def tilt_016_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(180317/100000000), 0, (992667/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (5473231/100000000), (3431/25000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-291433968414131011703427724598761947673631669/97068809013906857614139892842200000000000000000), (-3067881460252971391737/1480714611400000000000), (-10696971473204569193789491716945289150347831881669/48534404506953428807069946421100000000000000000), (-3067881460252971391737/1480714611400000000000), (-21393651512440724256567280006165979538747990131669/97068809013906857614139892842200000000000000000)]
    bernstein := [(85103368534305623399643217202181520492239481232575531/63615014675353998206002720173064192000000000000000000000), (238103544354924006589501456705642290017523200506009131/127230029350707996412005440346128384000000000000000000000), (1562143727051223581622765667558166950954347055380081793/763380176104247978472032642076770304000000000000000000000), (72914247624916946098451916332898114010984085269137687/39147701338679383511386289337270272000000000000000000000), (103351543518364579769413271555516233554841568725432087/78295402677358767022772578674540544000000000000000000000)]
    reserve := (330005147/250000000000) }

theorem tilt_016_018_valid : tilt_016_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_018]
  · intro i; fin_cases i <;> norm_num [tilt_016_018]
  · norm_num [tilt_016_018]
  · norm_num [tilt_016_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_018]

def tilt_016_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(20243/12500000), 0, (992993/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-2385413935257753434659140067583496905899781/757974998796976877013343191318750000000000000), (-6135740230531013827359/2961429222800000000000), (-1336461873610209371208293769936900793819798210871/6063799990375815016106745530550000000000000000), (-6135740230531013827359/2961429222800000000000), (-1336442790298727309180816496816360125844551012623/6063799990375815016106745530550000000000000000)]
    bernstein := [(4740886698040406861678165775915618850178768581409777/3973971961692694128955716750901248000000000000000000000), (1524810579104351200976463392341891362099635828664553/883104880376154250879048166866944000000000000000000000), (90681196095029189147387826099337202708213256476667731/47687663540312329547468601010814976000000000000000000000), (466758778923912101630842172870866512510629998930381/271724578577278231039707128266752000000000000000000000), (5748197806397273178032868367365494489688661845178229/4891042414391008158714728308801536000000000000000000000)]
    reserve := (587625021/500000000000) }

theorem tilt_016_019_valid : tilt_016_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_019]
  · intro i; fin_cases i <;> norm_num [tilt_016_019]
  · norm_num [tilt_016_019]
  · norm_num [tilt_016_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_019]

def tilt_016_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(16393/10000000), 0, (992667/100000000), 0, 0]] i.1) i.2
    mu := ![(5764109/100000000), (1/100000000), (2157847/50000000), (2077937/50000000), (1/100000000), (1367631/25000000), (3431/25000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-2246519635201764067234570325707442318899781/757974998796976877013343191318750000000000000), (-6135752981921882992779/2961429222800000000000), (-1336459641625478941941377067678275318282709460871/6063799990375815016106745530550000000000000000), (-6135752981921882992779/2961429222800000000000), (-1336441669468397327828839191115669658744158262623/6063799990375815016106745530550000000000000000)]
    bernstein := [(5469256935156421496333042514125513568136274174159777/3973971961692694128955716750901248000000000000000000000), (1686664486247767024283646582510232723575897483414553/883104880376154250879048166866944000000000000000000000), (99421003800159279202539189764795482920808165054917731/47687663540312329547468601010814976000000000000000000000), (516556687757537502447130090337656058099385464680381/271724578577278231039707128266752000000000000000000000), (6644534921151196871171842548879222972659909136928229/4891042414391008158714728308801536000000000000000000000)]
    reserve := (1358510999/1000000000000) }

theorem tilt_016_020_valid : tilt_016_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_016_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_016_020]
  · intro i; fin_cases i <;> norm_num [tilt_016_020]
  · norm_num [tilt_016_020]
  · norm_num [tilt_016_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_016_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_016_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_016_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_016_020]

def tiltBundle016_row : Alternative → Row
  | .zero => tilt_016_000
  | (.spike 0 false false) => tilt_016_001
  | (.spike 0 false true) => tilt_016_002
  | (.spike 0 true false) => tilt_016_003
  | (.spike 0 true true) => tilt_016_004
  | (.spike 1 false false) => tilt_016_005
  | (.spike 1 false true) => tilt_016_006
  | (.spike 1 true false) => tilt_016_007
  | (.spike 1 true true) => tilt_016_008
  | (.spike 2 false false) => tilt_016_009
  | (.spike 2 false true) => tilt_016_010
  | (.spike 2 true false) => tilt_016_011
  | (.spike 2 true true) => tilt_016_012
  | (.spike 3 false false) => tilt_016_013
  | (.spike 3 false true) => tilt_016_014
  | (.spike 3 true false) => tilt_016_015
  | (.spike 3 true true) => tilt_016_016
  | (.spike 4 false false) => tilt_016_017
  | (.spike 4 false true) => tilt_016_018
  | (.spike 4 true false) => tilt_016_019
  | (.spike 4 true true) => tilt_016_020

def tiltBundle016 : TiltBundle where
  interval := ⟨(-1/160), (-1/320)⟩
  lambda := ![(14774907/100000000), (14774907/100000000), (8385431/100000000), (2829769/20000000), (2829769/20000000), (3277347/20000000), (17380329/100000000)]
  row := tiltBundle016_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_016_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_016_001_valid | exact tilt_016_002_valid | exact tilt_016_003_valid | exact tilt_016_004_valid | exact tilt_016_005_valid | exact tilt_016_006_valid | exact tilt_016_007_valid | exact tilt_016_008_valid | exact tilt_016_009_valid | exact tilt_016_010_valid | exact tilt_016_011_valid | exact tilt_016_012_valid | exact tilt_016_013_valid | exact tilt_016_014_valid | exact tilt_016_015_valid | exact tilt_016_016_valid | exact tilt_016_017_valid | exact tilt_016_018_valid | exact tilt_016_019_valid | exact tilt_016_020_valid
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
