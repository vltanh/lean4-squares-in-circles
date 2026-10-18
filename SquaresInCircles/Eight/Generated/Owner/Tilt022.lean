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

def tilt_022_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1118947/20000000), (54107/100000000)]
    alternative := .zero
    polynomial := [(-87662152278129770808072343014126242659317951/61029052050626206909945098311900000000000000000), (132909561354747/211987750000000), (-1583965637392042945941402070026282444662659317951/30514526025313103454972549155950000000000000000), (132909561354747/211987750000000), (-3167843612631807762111996067709550763082659317951/61029052050626206909945098311900000000000000000)]
    bernstein := [(3706334142633783083046070537841547499483194535161953169/10238975885285988085888414625199816704000000000000000000000), (1066914650696728307188117058091258676856730259365544923/2559743971321497021472103656299954176000000000000000000000), (288295448545515016153978283674134244736003576392768841/639935992830374255368025914074988544000000000000000000000), (74086507547658494342964933444070992512352696775786947/159983998207593563842006478518747136000000000000000000000), (18179999892583555473332609408546133629608099894230849/39995999551898390960501619629686784000000000000000000000)]
    reserve := (72396579/200000000000) }

theorem tilt_022_000_valid : tilt_022_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_000]
  · intro i; fin_cases i <;> norm_num [tilt_022_000]
  · norm_num [tilt_022_000]
  · norm_num [tilt_022_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_000]

def tilt_022_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7253/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3777/100000000), 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1118947/20000000), (29221/50000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-15862065823173850480821873027047468701710733/12359745018930187351790242374637500000000000000), (2870134053843398631693/4955595234200000000000), (-297194687435203091624455701095022595985867835733/6179872509465093675895121187318750000000000000), (2870134053843398631693/4955595234200000000000), (-594373512804583009398430580317018144503033960733/12359745018930187351790242374637500000000000000)]
    bernstein := [(777299099353366182696232031465635767810641900803638227/2073621118875158421214528830116462592000000000000000000000), (220313485557775023453477648452655142071899916361997009/518405279718789605303632207529115648000000000000000000000), (177118748715977228772505714496961482917935819973989809/388803959789092203977724155646836736000000000000000000000), (15116197099045464598277862445104392820873176341744201/32400329982424350331477012970569728000000000000000000000), (3709619428288628923497464325743059754262496727629667/8100082495606087582869253242642432000000000000000000000)]
    reserve := (732131/1953125000) }

theorem tilt_022_001_valid : tilt_022_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_001]
  · intro i; fin_cases i <;> norm_num [tilt_022_001]
  · norm_num [tilt_022_001]
  · norm_num [tilt_022_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_001]

def tilt_022_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4297/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (3771/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1118947/20000000), (9999/20000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-7534464617422524479415104098501170751675814891/4725565211882281305043242000677700000000000000000), (80409392805822192569/117759195125000000000), (-132679339521551083417482998077819866592194802814891/2362782605941140652521621000338850000000000000000), (80409392805822192569/117759195125000000000), (-265351144578484744310486581051541232013637929814891/4725565211882281305043242000677700000000000000000)]
    bernstein := [(295364397029269471645224955978051723834403065810214069029/792818282818348000274723603856419192832000000000000000000000), (85950820135794062043166926944420574132746425400304751543/198204570704587000068680900964104798208000000000000000000000), (70148947704424496128469969405382131200399783690126217143/148653428028440250051510675723078598656000000000000000000000), (6036522482774526512087011250858769895249787457247048127/12387785669036687504292556310256549888000000000000000000000), (1486062065785100990406005562084817599685391554406005909/3096946417259171876073139077564137472000000000000000000000)]
    reserve := (372549931/1000000000000) }

theorem tilt_022_002_valid : tilt_022_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_002]
  · intro i; fin_cases i <;> norm_num [tilt_022_002]
  · norm_num [tilt_022_002]
  · norm_num [tilt_022_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_002]

def tilt_022_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3777/100000000), 0, 0]] i.1) i.2
    mu := ![(698051/12500000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1118947/20000000), (29221/50000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-10079872544786945145565682631035932580792211/8235750782258781713120830416100000000000000000), (2870134053843398631693/4955595234200000000000), (-198031215402285841230827678240947126452719792211/4117875391129390856560415208050000000000000000), (2870134053843398631693/4955595234200000000000), (-396052350932026895516509790799263216972858792211/8235750782258781713120830416100000000000000000)]
    bernstein := [(600088197988664030435381499180827719221399588098810109/1381729697961245486978782059902795776000000000000000000000), (167339429696376941205436508640632848282318832080635903/345432424490311371744695514975698944000000000000000000000), (44474399517199209055642794637605198354108148214204501/86358106122577842936173878743924736000000000000000000000), (11356028023205259135786845650854669945944165435572167/21589526530644460734043469685981184000000000000000000000), (2792746489806399868142309859250794992968003419044589/5397381632661115183510867421495296000000000000000000000)]
    reserve := (108575541/250000000000) }

theorem tilt_022_003_valid : tilt_022_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_003]
  · intro i; fin_cases i <;> norm_num [tilt_022_003]
  · norm_num [tilt_022_003]
  · norm_num [tilt_022_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_003]

def tilt_022_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5589941/100000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1118947/20000000), (9999/20000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-3852123023291366068226546276868136426249129/2507507561665521397228800654100000000000000000), (80409392805822192569/117759195125000000000), (-70402955613029770156767297056141043437517249129/1253753780832760698614400327050000000000000000), (80409392805822192569/117759195125000000000), (-140802059103036248947466367566005218738608249129/2507507561665521397228800654100000000000000000)]
    bernstein := [(181200249973154067801171857487190813188131926240889351/420689959836957722339293899947769856000000000000000000000), (7389405647032935881527775205302951601850068616873131/15024641422748490083546210712420352000000000000000000000), (13937155784169075857083225333783795867805077247959439/26293122489809857646205868746735616000000000000000000000), (512217644661036896874421933285607800909224547082259/939040088921780630221638169526272000000000000000000000), (884141037675087831299470665800535063023046846906071/1643320155613116102887866796670976000000000000000000000)]
    reserve := (430721593/1000000000000) }

theorem tilt_022_004_valid : tilt_022_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_004]
  · intro i; fin_cases i <;> norm_num [tilt_022_004]
  · norm_num [tilt_022_004]
  · norm_num [tilt_022_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_004]

def tilt_022_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3777/100000000), 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4253539/100000000), (1/100000000), (1118947/20000000), (29221/50000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-41649105072911616550329315868992638012193/32172737142979423610938036058691406250000000), (2870134053843398631693/4955595234200000000000), (-12377693540755618269880742711710605290630991963/257381897143835388887504288469531250000000000), (2870134053843398631693/4955595234200000000000), (-12377360347915034976948340077183653349526894419/257381897143835388887504288469531250000000000)]
    bernstein := [(15703787228582430737805403372802495766102634426608861/43181516828719093878096591485796352000000000000000000000), (4467140232391368738009850648503264427081985087879337/10795379207179773469524147871449088000000000000000000000), (1199273903782045828557495472536584929927941226205329/2698844801794943367381036967862272000000000000000000000), (307238102190925087614333667225356469346911536540693/674711200448735841845259241965568000000000000000000000), (75363685586404468918230794926127971731573332387781/168677800112183960461314810491392000000000000000000000)]
    reserve := (363669189/1000000000000) }

theorem tilt_022_005_valid : tilt_022_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_005]
  · intro i; fin_cases i <;> norm_num [tilt_022_005]
  · norm_num [tilt_022_005]
  · norm_num [tilt_022_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_005]

def tilt_022_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4257267/100000000), (1/100000000), (1118947/20000000), (9999/20000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-382350736756522950415973340870674388089993/250736417803204045986746332860000000000000000), (80409392805822192569/117759195125000000000), (-7039890145447777732285921493142533054646689993/125368208901602022993373166430000000000000000), (80409392805822192569/117759195125000000000), (-14079397940158798941621427012944195434905289993/250736417803204045986746332860000000000000000)]
    bernstein := [(18595405300054356776799231345811047690141296081840167/42066590405505997715935763636001177600000000000000000000), (755913308175009083840325875114179372275531406500427/1502378228768071346997705844142899200000000000000000000), (4270237113187208017398828050778532629082601240011789/7887485701032374571737955681750220800000000000000000000), (52282291026273374779495660363584623928210785409203/93898639298004459187356615258931200000000000000000000), (90270113411093560557078323406955589879817477788407/164322618771507803577874076703129600000000000000000000)]
    reserve := (221023443/500000000000) }

theorem tilt_022_006_valid : tilt_022_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_006]
  · intro i; fin_cases i <;> norm_num [tilt_022_006]
  · norm_num [tilt_022_006]
  · norm_num [tilt_022_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_006]

def tilt_022_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3777/100000000), 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (4237883/100000000), (4255403/100000000), (1/100000000), (1118947/20000000), (29221/50000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-13327475393091862801596617871733582132594543/10295239799638367304432859863631250000000000000), (14347541733297489631569/24767035828600000000000), (-247554512904699901141078590525101431707844032043/5147619899819183652216429931815625000000000000), (14347541733297489631569/24767035828600000000000), (-495095698334006710419355584432331129833555469543/10295239799638367304432859863631250000000000000)]
    bernstein := [(629218956084264123493446066317864385024407925657456617/1727254618903296101538078474298720256000000000000000000000), (178973784564013432754180500846646438590104129172585139/431813654725824025384519618574680064000000000000000000000), (144144965101545447271245030115284649692186912169823939/323860241044368019038389713931010048000000000000000000000), (12310194560918445107763663899830592190798111238315771/26988353420364001586532476160917504000000000000000000000), (3020046977304375396384330166173503948361185918448857/6747088355091000396633119040229376000000000000000000000)]
    reserve := (364288477/1000000000000) }

theorem tilt_022_007_valid : tilt_022_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_007]
  · intro i; fin_cases i <;> norm_num [tilt_022_007]
  · norm_num [tilt_022_007]
  · norm_num [tilt_022_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_007]

def tilt_022_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (4241627/100000000), (4255403/100000000), (1/100000000), (1118947/20000000), (9999/20000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-9558918922394449016952455937468329276427241/6268432397332970582986222139900000000000000000), (402148255580788574413/589055949625000000000), (-175996951534460651370211947185623873702101427241/3134216198666485291493111069950000000000000000), (402148255580788574413/589055949625000000000), (-351984344149998908291406941915310279074926427241/6268432397332970582986222139900000000000000000)]
    bernstein := [(464235961491912173595587002593506885904944106690388679/1051668443114530713924057738650845184000000000000000000000), (132109583662672459208875013210170807365719477814778093/262917110778632678481014434662711296000000000000000000000), (106614787083533724225573502286681049078748580266003693/197187833083974508860760825997033472000000000000000000000), (9136830931817917215956930143015181928352053548091077/16432319423664542405063402166419456000000000000000000000), (173339109675123394174917956971267163393767909621043/316006142762779661635834657046528000000000000000000000)]
    reserve := (22071403/50000000000) }

theorem tilt_022_008_valid : tilt_022_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_008]
  · intro i; fin_cases i <;> norm_num [tilt_022_008]
  · norm_num [tilt_022_008]
  · norm_num [tilt_022_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_008]

def tilt_022_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3777/100000000), 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (212677/5000000), (1/100000000), (1118947/20000000), (29221/50000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-853026826064537519939335680133321660234283/658897811593970414970757474520000000000000000), (2870134053843398631693/4955595234200000000000), (-15843451509889248045774433464872935293675034283/329448905796985207485378737260000000000000000), (2870134053843398631693/4955595234200000000000), (-31686049992952431554028927594065737265689834283/658897811593970414970757474520000000000000000)]
    bernstein := [(40192820219773776481752378819788072900607340824440677/110544709070393459495740318336365363200000000000000000000), (11433660533023101162141849251580416426752664331991159/27636177267598364873935079584091340800000000000000000000), (9208759870003695680223274696252627556249276008163959/20727132950698773655451309688068505600000000000000000000), (786390902244730330099417440679874375098331375463551/1727261079224897804620942474005708800000000000000000000), (192896374051088093353092694181776383151929775996117/431815269806224451155235618501427200000000000000000000)]
    reserve := (363588819/1000000000000) }

theorem tilt_022_009_valid : tilt_022_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_009]
  · intro i; fin_cases i <;> norm_num [tilt_022_009]
  · norm_num [tilt_022_009]
  · norm_num [tilt_022_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_009]

def tilt_022_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (1064317/25000000), (1/100000000), (1118947/20000000), (9999/20000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-918769513751435413214019073968078882921223/626841191748257087498801218600000000000000000), (80409392805822192569/117759195125000000000), (-17599692390109899058891697347271954955368921223/313420595874128543749400609300000000000000000), (80409392805822192569/117759195125000000000), (-35198466010706046682370180675469941831854921223/626841191748257087498801218600000000000000000)]
    bernstein := [(52714412022957854769974964046909963530719873062766537/105166500716579267804982877855154176000000000000000000000), (14784969363279415113052636203759159225662235061267779/26291625179144816951245719463788544000000000000000000000), (3947655770859214917741067651492510008701706230048193/6572906294786204237811429865947136000000000000000000000), (1012222180523494838201351449203684464395335634954731/1643226573696551059452857466486784000000000000000000000), (249996042197565714098531286312180354139750705181177/410806643424137764863214366621696000000000000000000000)]
    reserve := (501247181/1000000000000) }

theorem tilt_022_010_valid : tilt_022_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_010]
  · intro i; fin_cases i <;> norm_num [tilt_022_010]
  · norm_num [tilt_022_010]
  · norm_num [tilt_022_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_010]

def tilt_022_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14497/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3777/100000000), 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1118947/20000000), (29221/50000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-63453113200898380093429189642723689452227807/49438980075720749407160969498550000000000000000), (2870134053843398631693/4955595234200000000000), (-1188778754590720569475992946077624917758116727807/24719490037860374703580484749275000000000000000), (2870134053843398631693/4955595234200000000000), (-2377494056068240240571892462965607111826781227807/49438980075720749407160969498550000000000000000)]
    bernstein := [(3108382682080653323265513971938070283940856613251978033/8294484475500633684858115320465850368000000000000000000000), (881050511907972705098793085151563304316209606867396411/2073621118875158421214528830116462592000000000000000000000), (708322420879954136710903067570527684678548268576167611/1555215839156368815910896622587346944000000000000000000000), (60452073783704143600478174292865967156309081741222179/129601319929697401325908051882278912000000000000000000000), (14835299028994462019720504981684692585206896879533793/32400329982424350331477012970569728000000000000000000000)]
    reserve := (46844121/125000000000) }

theorem tilt_022_011_valid : tilt_022_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_011]
  · intro i; fin_cases i <;> norm_num [tilt_022_011]
  · norm_num [tilt_022_011]
  · norm_num [tilt_022_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_011]

def tilt_022_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2147/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (3769/100000000), (1118947/20000000), (9999/20000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-7530105986511443089024338070299704917851166171/4723058945527530691781484778720300000000000000000), (80409392805822192569/117759195125000000000), (-132608970906724503462641001062534851885617704166171/2361529472763765345890742389360150000000000000000), (80409392805822192569/117759195125000000000), (-265210411707462495482192977786999404066317557166171/4723058945527530691781484778720300000000000000000)]
    bernstein := [(295268588049319332717457704615268754430649037208612631349/792397801098476163626473949333026766848000000000000000000000), (85920445450694733456862988334357705842928774233162554983/198099450274619040906618487333256691712000000000000000000000), (23374383742166398093464415850957798193982842552308422861/49524862568654760226654621833314172928000000000000000000000), (6034271603756079230720452766990555920140204508836418287/12381215642163690056663655458328543232000000000000000000000), (1485511583066276411022291457809025160118542005644318629/3095303910540922514165913864582135808000000000000000000000)]
    reserve := (372626713/1000000000000) }

theorem tilt_022_012_valid : tilt_022_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_012]
  · intro i; fin_cases i <;> norm_num [tilt_022_012]
  · norm_num [tilt_022_012]
  · norm_num [tilt_022_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_012]

def tilt_022_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3777/100000000), 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (5591967/100000000), (29221/50000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-4031326576009460653643884147980493269643951/3294301339826198880436859596554000000000000000), (2870134053843398631693/4955595234200000000000), (-79212510229894233262366312833955720875606103951/1647150669913099440218429798277000000000000000), (2870134053843398631693/4955595234200000000000), (-158420989133212457064078981783763461257942563951/3294301339826198880436859596554000000000000000)]
    bernstein := [(240139997909775809316628940256409535706914101603027169/552692051473535410760473678130593136640000000000000000000), (66961953908051489038859194535853703942766306297502923/138173012868383852690118419532648284160000000000000000000), (53388917089815846581779136652132996751044726640264523/103629759651287889517588814649486213120000000000000000000), (4544047725955217073256756172423977793017425188048947/8635813304273990793132401220790517760000000000000000000), (1117507723314403758708821544963087353878574753384849/2158953326068497698283100305197629440000000000000000000)]
    reserve := (217245749/500000000000) }

theorem tilt_022_013_valid : tilt_022_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_013]
  · intro i; fin_cases i <;> norm_num [tilt_022_013]
  · norm_num [tilt_022_013]
  · norm_num [tilt_022_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_013]

def tilt_022_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1119501/20000000), (9999/20000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-1926405533202050271051425815609496086443793/1253753614071831059536542722100000000000000000), (80409392805822192569/117759195125000000000), (-35201473468668229669070980130772895151857443793/626876807035915529768271361050000000000000000), (80409392805822192569/117759195125000000000), (-70401020531803257287870908835730180807628443793/1253753614071831059536542722100000000000000000)]
    bernstein := [(90542350177436444196460393309338449940628725912142367/210344951940637492013534371418996736000000000000000000000), (25848475529221586401498757032558171866608124628830389/52586237985159373003383592854749184000000000000000000000), (20894900210920539271067752259599826031957603496619189/39439678488869529752537694641061888000000000000000000000), (1791858952723993644405440937107221638560489409043021/3286639874072460812711474553421824000000000000000000000), (441844816550677823116747027081788166577197020874607/821659968518115203177868638355456000000000000000000000)]
    reserve := (53805873/125000000000) }

theorem tilt_022_014_valid : tilt_022_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_014]
  · intro i; fin_cases i <;> norm_num [tilt_022_014]
  · norm_num [tilt_022_014]
  · norm_num [tilt_022_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_014]

def tilt_022_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14497/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3777/100000000), 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1118947/20000000), (29221/50000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-63453113200898380093429189642723689452227807/49438980075720749407160969498550000000000000000), (2870134053843398631693/4955595234200000000000), (-1188778754590720569475992946077624917758116727807/24719490037860374703580484749275000000000000000), (2870134053843398631693/4955595234200000000000), (-2377494056068240240571892462965607111826781227807/49438980075720749407160969498550000000000000000)]
    bernstein := [(3108382682080653323265513971938070283940856613251978033/8294484475500633684858115320465850368000000000000000000000), (881050511907972705098793085151563304316209606867396411/2073621118875158421214528830116462592000000000000000000000), (708322420879954136710903067570527684678548268576167611/1555215839156368815910896622587346944000000000000000000000), (60452073783704143600478174292865967156309081741222179/129601319929697401325908051882278912000000000000000000000), (14835299028994462019720504981684692585206896879533793/32400329982424350331477012970569728000000000000000000000)]
    reserve := (46844121/125000000000) }

theorem tilt_022_015_valid : tilt_022_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_015]
  · intro i; fin_cases i <;> norm_num [tilt_022_015]
  · norm_num [tilt_022_015]
  · norm_num [tilt_022_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_015]

def tilt_022_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2147/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (3769/100000000), (1118947/20000000), (9999/20000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-7530105986511443089024338070299704917851166171/4723058945527530691781484778720300000000000000000), (80409392805822192569/117759195125000000000), (-132608970906724503462641001062534851885617704166171/2361529472763765345890742389360150000000000000000), (80409392805822192569/117759195125000000000), (-265210411707462495482192977786999404066317557166171/4723058945527530691781484778720300000000000000000)]
    bernstein := [(295268588049319332717457704615268754430649037208612631349/792397801098476163626473949333026766848000000000000000000000), (85920445450694733456862988334357705842928774233162554983/198099450274619040906618487333256691712000000000000000000000), (23374383742166398093464415850957798193982842552308422861/49524862568654760226654621833314172928000000000000000000000), (6034271603756079230720452766990555920140204508836418287/12381215642163690056663655458328543232000000000000000000000), (1485511583066276411022291457809025160118542005644318629/3095303910540922514165913864582135808000000000000000000000)]
    reserve := (372626713/1000000000000) }

theorem tilt_022_016_valid : tilt_022_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_016]
  · intro i; fin_cases i <;> norm_num [tilt_022_016]
  · norm_num [tilt_022_016]
  · norm_num [tilt_022_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_016]

def tilt_022_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3777/100000000), 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (174749/3125000), (29221/50000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-6299109726507318588583039042978522427439997/5147346763967745411922681031900000000000000000), (2870134053843398631693/4955595234200000000000), (-123769569528489317355964404340473698911808439997/2573673381983872705961340515950000000000000000), (2870134053843398631693/4955595234200000000000), (-247532839947252127393340225641904419301189439997/5147346763967745411922681031900000000000000000)]
    bernstein := [(375191830679407984959806475896858536578776883441958643/863581484859878818088357949712891904000000000000000000000), (104621325853790143596871912038695919675576036644691281/215895371214969704522089487428222976000000000000000000000), (83415138451054867234455294718748918466464200430566481/161921528411227278391567115571167232000000000000000000000), (7099654219419100268023133766387539457878592268537609/13493460700935606532630592964263936000000000000000000000), (1746000723382532353317849752255059557094084408793603/3373365175233901633157648241065984000000000000000000000)]
    reserve := (434460253/1000000000000) }

theorem tilt_022_017_valid : tilt_022_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_017]
  · intro i; fin_cases i <;> norm_num [tilt_022_017]
  · norm_num [tilt_022_017]
  · norm_num [tilt_022_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_017]

def tilt_022_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1119501/20000000), (9999/20000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1898390412891871849002117514988369840731343/1253753614071831059536542722100000000000000000), (80409392805822192569/117759195125000000000), (-35201445453547919490648930822472274025611731343/626876807035915529768271361050000000000000000), (80409392805822192569/117759195125000000000), (-70400992516682947109448859527429559681382731343/1253753614071831059536542722100000000000000000)]
    bernstein := [(95242713976683195677659010736706933606392815958210817/210344951940637492013534371418996736000000000000000000000), (27023575085467335620703369285743074622224432163546539/52586237985159373003383592854749184000000000000000000000), (21776232050164752653240960421246293136181338693415339/39439678488869529752537694641061888000000000000000000000), (1865303930103512712006146190882863031807544745220371/3286639874072460812711474553421824000000000000000000000), (460206240199331355236369061611149565252214976027057/821659968518115203177868638355456000000000000000000000)]
    reserve := (226396481/500000000000) }

theorem tilt_022_018_valid : tilt_022_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_018]
  · intro i; fin_cases i <;> norm_num [tilt_022_018]
  · norm_num [tilt_022_018]
  · norm_num [tilt_022_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_018]

def tilt_022_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1118947/20000000), (54107/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-77477600414465798093438802761180947551171201/61029052050626206909945098311900000000000000000), (132909561354747/211987750000000), (-1583967212423345513777364542354157250183735785201/30514526025313103454972549155950000000000000000), (132909561354747/211987750000000), (-3167856947246276561756635645905553319419920399201/61029052050626206909945098311900000000000000000)]
    bernstein := [(5415006793961821955447447862740336779261552483753571919/10238975885285988085888414625199816704000000000000000000000), (1494082329589113228784856116499680033527989779261951173/2559743971321497021472103656299954176000000000000000000000), (395087233835937211543028383531876659493601505657437591/639935992830374255368025914074988544000000000000000000000), (100784416899528515413410472244862153763606998381343197/159983998207593563842006478518747136000000000000000000000), (24854467147017070689593923125950976186447701589949599/39995999551898390960501619629686784000000000000000000000)]
    reserve := (528862149/1000000000000) }

theorem tilt_022_019_valid : tilt_022_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_019]
  · intro i; fin_cases i <;> norm_num [tilt_022_019]
  · norm_num [tilt_022_019]
  · norm_num [tilt_022_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_019]

def tilt_022_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793587/50000000), (1/100000000), (847951/20000000), (4255403/100000000), (1/100000000), (1118947/20000000), (54107/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-87633433980981136072605522781146530409171201/61029052050626206909945098311900000000000000000), (132909561354747/211987750000000), (-1583956999140691141102911763026418439676931785201/30514526025313103454972549155950000000000000000), (132909561354747/211987750000000), (-3167826364847401301069750920530055732823454399201/61029052050626206909945098311900000000000000000)]
    bernstein := [(3711215962874568497302933333965775934924998048699571919/10238975885285988085888414625199816704000000000000000000000), (1068137759544162479942329014587417469640250885443951173/2559743971321497021472103656299954176000000000000000000000), (288601962926963094936619790713743491887817232251437591/639935992830374255368025914074988544000000000000000000000), (74163338866921408030347664425430497571910544579343197/159983998207593563842006478518747136000000000000000000000), (18199263011519881547759890679971934400163782855949599/39995999551898390960501619629686784000000000000000000000)]
    reserve := (362459683/1000000000000) }

theorem tilt_022_020_valid : tilt_022_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_022_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_022_020]
  · intro i; fin_cases i <;> norm_num [tilt_022_020]
  · norm_num [tilt_022_020]
  · norm_num [tilt_022_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_022_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_022_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_022_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_022_020]

def tiltBundle022_row : Alternative → Row
  | .zero => tilt_022_000
  | (.spike 0 false false) => tilt_022_001
  | (.spike 0 false true) => tilt_022_002
  | (.spike 0 true false) => tilt_022_003
  | (.spike 0 true true) => tilt_022_004
  | (.spike 1 false false) => tilt_022_005
  | (.spike 1 false true) => tilt_022_006
  | (.spike 1 true false) => tilt_022_007
  | (.spike 1 true true) => tilt_022_008
  | (.spike 2 false false) => tilt_022_009
  | (.spike 2 false true) => tilt_022_010
  | (.spike 2 true false) => tilt_022_011
  | (.spike 2 true true) => tilt_022_012
  | (.spike 3 false false) => tilt_022_013
  | (.spike 3 false true) => tilt_022_014
  | (.spike 3 true false) => tilt_022_015
  | (.spike 3 true true) => tilt_022_016
  | (.spike 4 false false) => tilt_022_017
  | (.spike 4 false true) => tilt_022_018
  | (.spike 4 true false) => tilt_022_019
  | (.spike 4 true true) => tilt_022_020

def tiltBundle022 : TiltBundle where
  interval := ⟨(3/640), (1/160)⟩
  lambda := ![(7253037/50000000), (7253037/50000000), (267803/3125000), (2899499/20000000), (2899499/20000000), (4183779/25000000), (16688049/100000000)]
  row := tiltBundle022_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_022_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_022_001_valid | exact tilt_022_002_valid | exact tilt_022_003_valid | exact tilt_022_004_valid | exact tilt_022_005_valid | exact tilt_022_006_valid | exact tilt_022_007_valid | exact tilt_022_008_valid | exact tilt_022_009_valid | exact tilt_022_010_valid | exact tilt_022_011_valid | exact tilt_022_012_valid | exact tilt_022_013_valid | exact tilt_022_014_valid | exact tilt_022_015_valid | exact tilt_022_016_valid | exact tilt_022_017_valid | exact tilt_022_018_valid | exact tilt_022_019_valid | exact tilt_022_020_valid
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
