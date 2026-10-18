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

def tilt_024_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (5583709/100000000), (21499/20000000)]
    alternative := .zero
    polynomial := [(-15730890437678974516629298173913553520192961/4570564502938107684231056097300000000000000000), (289633563743/460942500000), (-59353988870128470714806653243130867262720192961/2285282251469053842115528048650000000000000000), (289633563743/460942500000), (-118692246849819262455096677188087820971920192961/4570564502938107684231056097300000000000000000)]
    bernstein := [(7984574530835943743069907756677105012136072063294959/47925842442328292031002638782824448000000000000000000000), (1106731408691998361762283359179236437698915578372151/3993820203527357669250219898568704000000000000000000000), (3103376265232231867007206569151686304055507240530853/8986095457936554755812994771779584000000000000000000000), (278064652161068312488649960924560875851604864528317/748841288161379562984416230981632000000000000000000000), (66464550234121859590316477230791712491505927346239/187210322040344890746104057745408000000000000000000000)]
    reserve := (33320539/200000000000) }

theorem tilt_024_000_valid : tilt_024_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_000]
  · intro i; fin_cases i <;> norm_num [tilt_024_000]
  · norm_num [tilt_024_000]
  · norm_num [tilt_024_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_000]

def tilt_024_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1817/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2373/100000000), 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (5583709/100000000), (111731/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-207838655813387880399730073829011633936221/63342325066626690812511605663200000000000000), (62177423598767760047/103003132935000000000), (-791855623404370581654584502064146445956832221/31671162533313345406255802831600000000000000), (62177423598767760047/103003132935000000000), (-1583503408152927775428769274054463880279728221/63342325066626690812511605663200000000000000)]
    bernstein := [(120092493033123388841729462832999125362864816906899/664192418490631489454201694198956032000000000000000000), (142579770033820333672942116117089646751698385265299/498144313867973617090651270649217024000000000000000000), (43705435691805344351892014036983330351918486806833/124536078466993404272662817662304256000000000000000000), (11674626204540043159707329618775290221376881223611/31134019616748351068165704415576064000000000000000000), (2788970987814330877195321163760505435293928648937/7783504904187087767041426103894016000000000000000000)]
    reserve := (180809791/1000000000000) }

theorem tilt_024_001_valid : tilt_024_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_001]
  · intro i; fin_cases i <;> norm_num [tilt_024_001]
  · norm_num [tilt_024_001]
  · norm_num [tilt_024_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_001]

def tilt_024_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2153/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (3779/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (5583709/100000000), (103401/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-99455648173267670489582686880657696218235447789/27690574025086718256220691748491100000000000000000), (208137032163475996637/317746102950000000000), (-41518625214345187812597612706214038888985819716421/1538365223615928792012260652693950000000000000000), (208137032163475996637/317746102950000000000), (-747235798210040112956267446024972042305526519447789/27690574025086718256220691748491100000000000000000)]
    bernstein := [(51569893965663952413579650643000414199941256157615404291/290356713489293306822348680708658036736000000000000000000000), (21347174245042634420623288939780910740239744314247383297/72589178372323326705587170177164509184000000000000000000000), (2217811660019129876059355294578005552622232204810085433/6049098197693610558798930848097042432000000000000000000000), (1793248303743089352985260021328140187943231022990949433/4536823648270207919099198136072781824000000000000000000000), (430960759343521321622704127920259459492643024391413011/1134205912067551979774799534018195456000000000000000000000)]
    reserve := (177608753/1000000000000) }

theorem tilt_024_002_valid : tilt_024_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_002]
  · intro i; fin_cases i <;> norm_num [tilt_024_002]
  · norm_num [tilt_024_002]
  · norm_num [tilt_024_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_002]

def tilt_024_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2373/100000000), 0, 0]] i.1) i.2
    mu := ![(2783177/50000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (5583709/100000000), (111731/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-11954272935325546995811517349544932738702001/3709624326782878515359380761018750000000000000), (62177423598767760047/103003132935000000000), (-46374570066688332467547839542821045437920827001/1854812163391439257679690380509375000000000000), (62177423598767760047/103003132935000000000), (-92737185860441339388099867568292545943102952001/3709624326782878515359380761018750000000000000)]
    bernstein := [(9316707572476989476067140523967929244541758726884719/38898230380806836221214780408659968000000000000000000000), (1118092971055533058484335185508247811809521249372791/3241519198400569685101231700721664000000000000000000000), (2987783494454188784779637300419568781396440169348773/7293418196401281791477771326623744000000000000000000000), (7124069872534652327097686205839375242378520882681/16426617559462346377202187672576000000000000000000000), (46286580964426938627540775682651452705249562071/110990659185556394440555322112000000000000000000000)]
    reserve := (119757473/500000000000) }

theorem tilt_024_003_valid : tilt_024_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_003]
  · intro i; fin_cases i <;> norm_num [tilt_024_003]
  · norm_num [tilt_024_003]
  · norm_num [tilt_024_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_003]

def tilt_024_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1392969/25000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (5583709/100000000), (103401/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-21581058741984579735115726654976698724033579/6109266600568356006295035721800000000000000000), (208137032163475996637/317746102950000000000), (-27480171190847328548743731859447404696440011193/1018211100094726001049172620300000000000000000), (208137032163475996637/317746102950000000000), (-164859446086341986712727275430029451479916033579/6109266600568356006295035721800000000000000000)]
    bernstein := [(15168568986275684787161240978767444370962890293427301/64060303349575644676568233770221568000000000000000000000), (5657498654730364953711578178790146256904858481262967/16015075837393911169142058442555392000000000000000000000), (1704867991443365703737887315691353339724369512888189/4003768959348477792285514610638848000000000000000000000), (454876160727113959674560208633490545042739644200063/1000942239837119448071378652659712000000000000000000000), (109891463271648961906591907259387205576036098315221/250235559959279862017844663164928000000000000000000000)]
    reserve := (236785781/1000000000000) }

theorem tilt_024_004_valid : tilt_024_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_004]
  · intro i; fin_cases i <;> norm_num [tilt_024_004]
  · norm_num [tilt_024_004]
  · norm_num [tilt_024_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_004]

def tilt_024_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2373/100000000), 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4270343/100000000), (1/100000000), (5583709/100000000), (111731/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-15629736920992421434227589137501474064294829/4748583836541195697024240910340000000000000000), (62177423598767760047/103003132935000000000), (-59363086132569837984971644557577259711849494829/2374291918270597848512120455170000000000000000), (62177423598767760047/103003132935000000000), (-118710542528218683548509061526017017949634694829/4748583836541195697024240910340000000000000000)]
    bernstein := [(8492256331137890312484418904278058469628085705866051/49792510449850208192028904368006758400000000000000000000), (1145080888800671874980960031444767864007832836469739/4149375870820850682669075364000563200000000000000000000), (3180699843930006533518250257783570553188570638810817/9336095709346914036005419569001267200000000000000000000), (283756484728698630443259495984241773334101024216313/778007975778909503000451630750105600000000000000000000), (67698330881009655425033346948831676786037275653971/194501993944727375750112907687526400000000000000000000)]
    reserve := (34110577/200000000000) }

theorem tilt_024_005_valid : tilt_024_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_005]
  · intro i; fin_cases i <;> norm_num [tilt_024_005]
  · norm_num [tilt_024_005]
  · norm_num [tilt_024_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_005]

def tilt_024_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4274103/100000000), (1/100000000), (5583709/100000000), (103401/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-344271344888918581097048564259423741721783/97742821966239110450332265532000000000000000), (208137032163475996637/317746102950000000000), (-439657917478073147426305046394791112363587261/16290470327706518408388710922000000000000000), (208137032163475996637/317746102950000000000), (-2637603233523549965976733229804487250439801783/97742821966239110450332265532000000000000000)]
    bernstein := [(253237947352312733710604531268094137681442640349977/1024907772860711414795676056624824320000000000000000000), (93153604544324877939317306983066716677390747291059/256226943215177853698919014156206080000000000000000000), (27936057008474092278916191852653079475793883364753/64056735803794463424729753539051520000000000000000000), (7442541226085874822828461795806292082658741196251/16014183950948615856182438384762880000000000000000000), (1799399096945792522018117990622885422476499295817/4003545987737153964045609596190720000000000000000000)]
    reserve := (61770911/250000000000) }

theorem tilt_024_006_valid : tilt_024_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_006]
  · intro i; fin_cases i <;> norm_num [tilt_024_006]
  · norm_num [tilt_024_006]
  · norm_num [tilt_024_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_006]

def tilt_024_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2373/100000000), 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (529847/12500000), (4272223/100000000), (1/100000000), (5583709/100000000), (111731/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-1953684429520480405533747541931040180241907/593568934779017617381839514180000000000000000), (44679878925778261023/74000418946250000000), (-7420423370718987091145563758328752259219991907/296784467389508808690919757090000000000000000), (44679878925778261023/74000418946250000000), (-14838893057008453701885593769115573478259741907/593568934779017617381839514180000000000000000)]
    bernstein := [(1069314045954188566955784367553642950723643373603133/6224021393548431771637797504208076800000000000000000000), (431504402371405432364798346549022512235541851685311/1556005348387107942909449376052019200000000000000000000), (133092241440938265383088964314385629638755524486037/389001337096776985727362344013004800000000000000000000), (35619890011358888209878783697397475147631700460679/97250334274194246431840586003251200000000000000000000), (8502258662785325185077013062459692663846613128493/24312583568548561607960146500812800000000000000000000)]
    reserve := (34360873/200000000000) }

theorem tilt_024_007_valid : tilt_024_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_007]
  · intro i; fin_cases i <;> norm_num [tilt_024_007]
  · norm_num [tilt_024_007]
  · norm_num [tilt_024_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_007]

def tilt_024_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (530321/12500000), (4272223/100000000), (1/100000000), (5583709/100000000), (103401/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-9682788578891344946467507639315703177010367/2749036879897119726411805337700000000000000000), (1795620827115556426153/2741786086050000000000), (-1124121177453882712437176968933306875729598799/41652073937835147369875838450000000000000000), (1795620827115556426153/2741786086050000000000), (-74182314923377367675907212441958938094976510367/2749036879897119726411805337700000000000000000)]
    bernstein := [(7086321440065526855446984304448657791751154400285873/28825740953750022142419851937841152000000000000000000000), (237294156969466769475985287714185457060195472040081/655130476221591412327723907678208000000000000000000000), (783096925966227125147383266607505164316171426465897/1801608809609376383901240746115072000000000000000000000), (208626041391954999961058601469357998739013396747299/450402202402344095975310186528768000000000000000000000), (1362789031654178333070202576844456566167665364109/3043258124340162810643987746816000000000000000000000)]
    reserve := (122916553/500000000000) }

theorem tilt_024_008_valid : tilt_024_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_008]
  · intro i; fin_cases i <;> norm_num [tilt_024_008]
  · norm_num [tilt_024_008]
  · norm_num [tilt_024_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_008]

def tilt_024_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2373/100000000), 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (533793/12500000), (1/100000000), (5583709/100000000), (111731/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-13025098197711779842812530822586721707138313/3957154123776996328244453475600000000000000000), (62177423598767760047/103003132935000000000), (-49469250342559556905472187682239953537475138313/1978577061888498164122226737800000000000000000), (62177423598767760047/103003132935000000000), (-98925475586921402031101562833657320353243138313/3957154123776996328244453475600000000000000000)]
    bernstein := [(7073584838733554987029669183024015108963836244395047/41493768424935877018852560476307456000000000000000000000), (2861878594615733613439343387453975132279192847476749/10373442106233969254713140119076864000000000000000000000), (2649965580532552491019548218247347199527157792391949/7780081579675476941034855089307648000000000000000000000), (78804090172095427234198151180037238626180024080887/216113377213207692806523752480768000000000000000000000), (18800802636419536861766186246133127903932428658429/54028344303301923201630938120192000000000000000000000)]
    reserve := (6818937/40000000000) }

theorem tilt_024_009_valid : tilt_024_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_009]
  · intro i; fin_cases i <;> norm_num [tilt_024_009]
  · norm_num [tilt_024_009]
  · norm_num [tilt_024_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_009]

def tilt_024_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (534263/12500000), (1/100000000), (5583709/100000000), (103401/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-12695915213290964962649887625854685482068083/3665356681307081687071593771600000000000000000), (208137032163475996637/317746102950000000000), (-5495701447268443632836331655433341589648229787/203630926739282315948421876200000000000000000), (208137032163475996637/317746102950000000000), (-98909930135618694426091319910174293928186068083/3665356681307081687071593771600000000000000000)]
    bernstein := [(11743533112691809195909972489645329456921473279819677/38434050474582544871027835106492416000000000000000000000), (4055054410865806202062900798425805977505427675220959/9608512618645636217756958776623104000000000000000000000), (396018436713292225303630553664200879484104140349351/800709384887136351479746564718592000000000000000000000), (314209850253464382809912225931963440247952232957351/600532038665352263609809923538944000000000000000000000), (76256447041756545040210721004454857112989142789517/150133009666338065902452480884736000000000000000000000)]
    reserve := (305550233/1000000000000) }

theorem tilt_024_010_valid : tilt_024_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_010]
  · intro i; fin_cases i <;> norm_num [tilt_024_010]
  · norm_num [tilt_024_010]
  · norm_num [tilt_024_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_010]

def tilt_024_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7259/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2373/100000000), 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (5583709/100000000), (111731/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-207851029018287679668233624157296331835533/63342325066626690812511605663200000000000000), (62177423598767760047/103003132935000000000), (-791855635777575481453853005614474730654731533/31671162533313345406255802831600000000000000), (62177423598767760047/103003132935000000000), (-1583503420526132675228037777604792164977627533/63342325066626690812511605663200000000000000)]
    bernstein := [(119962727768819768757130228449931900571946478064227/664192418490631489454201694198956032000000000000000000), (142482443234555652296520291924596697216348497187427/498144313867973617090651270649217024000000000000000000), (14560367733340180429186576233080039343831249333003/41512026155664468090887605887434752000000000000000000), (11668542863797596446132584267720721091947098357003/31134019616748351068165704415576064000000000000000000), (2787450093228055776090296557577624640173042810201/7783504904187087767041426103894016000000000000000000)]
    reserve := (90307209/500000000000) }

theorem tilt_024_011_valid : tilt_024_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_011]
  · intro i; fin_cases i <;> norm_num [tilt_024_011]
  · norm_num [tilt_024_011]
  · norm_num [tilt_024_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_011]

def tilt_024_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (43/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (151/4000000), (5583709/100000000), (103401/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-3973842689827719380225216627703733731712856473/1106450563055859872106198585345900000000000000000), (208137032163475996637/317746102950000000000), (-1658987122252971267255126276077210077556523428497/61469475725325548450344365852550000000000000000), (208137032163475996637/317746102950000000000), (-29857794357863655091212047752762077662285708856473/1106450563055859872106198585345900000000000000000)]
    bernstein := [(2062419974045477350843493946800651932629088155967112087/11601975056068613212536292878276624384000000000000000000000), (853435071263591297157727198402435848813798352639870429/2900493764017153303134073219569156096000000000000000000000), (88656227547984619125362457085766414701696430417872181/241707813668096108594506101630763008000000000000000000000), (71682254595833078974015095055233879969722127207120181/181280860251072081445879576223072256000000000000000000000), (17227245902700482223705182457147323142477796114209127/45320215062768020361469894055768064000000000000000000000)]
    reserve := (88882279/500000000000) }

theorem tilt_024_012_valid : tilt_024_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_012]
  · intro i; fin_cases i <;> norm_num [tilt_024_012]
  · norm_num [tilt_024_012]
  · norm_num [tilt_024_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_012]

def tilt_024_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2373/100000000), 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (348809/6250000), (111731/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-101360612321809310240531402226092614025381867/31457632527073252867438080538440000000000000000), (62177423598767760047/103003132935000000000), (-393256570454983365511553663633634738711528581867/15728816263536626433719040269220000000000000000), (62177423598767760047/103003132935000000000), (-786411780297644921712866795865043384809031781867/31457632527073252867438080538440000000000000000)]
    bernstein := [(79128231028008604658874796353330488193430342534494373/329857184847083631987267527386752614400000000000000000000), (9491642941141829818227625424739368114487395567236797/27488098737256969332272293948896051200000000000000000000), (25359389831105965135794097288249251898086528182267191/61848222158828180997612661385016115200000000000000000000), (2237163786735068481084533716135385093508756627732799/5154018513235681749801055115418009600000000000000000000), (537825384936740530403746208101741560383018088000533/1288504628308920437450263778854502400000000000000000000)]
    reserve := (119943167/500000000000) }

theorem tilt_024_013_valid : tilt_024_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_013]
  · intro i; fin_cases i <;> norm_num [tilt_024_013]
  · norm_num [tilt_024_013]
  · norm_num [tilt_024_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_013]

def tilt_024_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (223459/4000000), (103401/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-54910707039751688084903162065148548363605491/15541968013175219956583617352700000000000000000), (208137032163475996637/317746102950000000000), (-23303176791918358246563304047919127659295289499/863442667398623330921312075150000000000000000), (208137032163475996637/317746102950000000000), (-419402271547490696750054569700479149318951605491/15541968013175219956583617352700000000000000000)]
    bernstein := [(38499516165413447689751019542504987845858047250784029/162969346513832194411946231492247552000000000000000000000), (14370343190901991067442352285406147630978598667650143/40742336628458048602986557873061888000000000000000000000), (1443866782056284611124673565567533001485155857330727/3395194719038170716915546489421824000000000000000000000), (1155808917737239078165741516341215243494198493746727/2546396039278628037686659867066368000000000000000000000), (279214864044023819942006672927051842490000546749709/636599009819657009421664966766592000000000000000000000)]
    reserve := (236237777/1000000000000) }

theorem tilt_024_014_valid : tilt_024_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_014]
  · intro i; fin_cases i <;> norm_num [tilt_024_014]
  · norm_num [tilt_024_014]
  · norm_num [tilt_024_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_014]

def tilt_024_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7259/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2373/100000000), 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (5583709/100000000), (111731/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-207851029146714243740819239779663612317671/63342325066626690812511605663200000000000000), (62177423598767760047/103003132935000000000), (-791855635777703908017925591230097097935213671/31671162533313345406255802831600000000000000), (62177423598767760047/103003132935000000000), (-1583503420526261101792110363220414532258109671/63342325066626690812511605663200000000000000)]
    bernstein := [(119962726421932914021924603895387952800428727369449/664192418490631489454201694198956032000000000000000000), (142482442224360919164115827312990626613349669807849/498144313867973617090651270649217024000000000000000000), (43681102947463637837478659576985863423814041067683/124536078466993404272662817662304256000000000000000000), (11668542800656109987124870317004568625564304910561/31134019616748351068165704415576064000000000000000000), (2787450077442067617510896604504387443855569824587/7783504904187087767041426103894016000000000000000000)]
    reserve := (11288401/62500000000) }

theorem tilt_024_015_valid : tilt_024_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_015]
  · intro i; fin_cases i <;> norm_num [tilt_024_015]
  · norm_num [tilt_024_015]
  · norm_num [tilt_024_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_015]

def tilt_024_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (43/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (151/4000000), (5583709/100000000), (103401/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-3973842699724817814688184664142539175907850463/1106450563055859872106198585345900000000000000000), (208137032163475996637/317746102950000000000), (-1658987122254070944858955494747925500383656205607/61469475725325548450344365852550000000000000000), (208137032163475996637/317746102950000000000), (-29857794357873552189646510720798516467729903850463/1106450563055859872106198585345900000000000000000)]
    bernstein := [(2062419870248635337189706894846908400369006782667830897/11601975056068613212536292878276624384000000000000000000000), (853435045313620629779099246843767219528727085460408699/2900493764017153303134073219569156096000000000000000000000), (29552075128472225573669299537908515957077747979432737/80569271222698702864835367210254336000000000000000000000), (71682252973849051770443167608163428192498043569786211/181280860251072081445879576223072256000000000000000000000), (17227245497188637591042451230779398999759702165743137/45320215062768020361469894055768064000000000000000000000)]
    reserve := (177764549/1000000000000) }

theorem tilt_024_016_valid : tilt_024_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_016]
  · intro i; fin_cases i <;> norm_num [tilt_024_016]
  · norm_num [tilt_024_016]
  · norm_num [tilt_024_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_016]

def tilt_024_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2373/100000000), 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (348809/6250000), (111731/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-405446211318109435275042719760049082540028893/125830530108293011469752322153760000000000000000), (62177423598767760047/103003132935000000000), (-1573026285581964334240527571645394633472552828893/62915265054146505734876161076880000000000000000), (62177423598767760047/103003132935000000000), (-3145647124952610559045780100571029217862565628893/125830530108293011469752322153760000000000000000)]
    bernstein := [(316473469424715970267680152922266072655720480584802067/1319428739388334527949070109547010457600000000000000000000), (37963283777640993677955401109268077650002439683074363/109952394949027877329089175795584204800000000000000000000), (101430161113044258425704074518910607566542249359770289/247392888635312723990450645540064460800000000000000000000), (8948038607251904441187993796629487248850628859586921/20616074052942726999204220461672038400000000000000000000), (2151147398804679847598500319822306160514014727260707/5154018513235681749801055115418009600000000000000000000)]
    reserve := (239856431/1000000000000) }

theorem tilt_024_017_valid : tilt_024_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_017]
  · intro i; fin_cases i <;> norm_num [tilt_024_017]
  · norm_num [tilt_024_017]
  · norm_num [tilt_024_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_017]

def tilt_024_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (223459/4000000), (103401/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-54578459519975026106080149610351147493963981/15541968013175219956583617352700000000000000000), (208137032163475996637/317746102950000000000), (-23303139875527271950787879268757483503643107109/863442667398623330921312075150000000000000000), (208137032163475996637/317746102950000000000), (-419401939299970920088075746688024351918081963981/15541968013175219956583617352700000000000000000)]
    bernstein := [(41983996343927280246083197481742073396582600820578339/162969346513832194411946231492247552000000000000000000000), (15241488754382638812657838734627281528928981398146913/40742336628458048602986557873061888000000000000000000000), (1516464608577887085988087772986232060040811410063257/3395194719038170716915546489421824000000000000000000000), (1210259237063075930562741084362233689927426040719257/2546396039278628037686659867066368000000000000000000000), (292827975554576555644588176457987243639049077319219/636599009819657009421664966766592000000000000000000000)]
    reserve := (257618977/1000000000000) }

theorem tilt_024_018_valid : tilt_024_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_018]
  · intro i; fin_cases i <;> norm_num [tilt_024_018]
  · norm_num [tilt_024_018]
  · norm_num [tilt_024_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_018]

def tilt_024_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (5583709/100000000), (21499/20000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-14973691497337747069169920429047270768827311/4570564502938107684231056097300000000000000000), (289633563743/460942500000), (-59354047544906241839773190957899032400884099511/2285282251469053842115528048650000000000000000), (289633563743/460942500000), (-118693121398315145932477211995369017530999371711/4570564502938107684231056097300000000000000000)]
    bernstein := [(15924272671319556958441562399506106275510952240856209/47925842442328292031002638782824448000000000000000000000), (1768371416356921073172953774380271799417568324003401/3993820203527357669250219898568704000000000000000000000), (4592062521389328268469884270998904151003212114544603/8986095457936554755812994771779584000000000000000000000), (402121495292885383431461379417417000055932709552067/748841288161379562984416230981632000000000000000000000), (97478666918794569555203526376674859022385868327489/187210322040344890746104057745408000000000000000000000)]
    reserve := (332269019/1000000000000) }

theorem tilt_024_019_valid : tilt_024_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_019]
  · intro i; fin_cases i <;> norm_num [tilt_024_019]
  · norm_num [tilt_024_019]
  · norm_num [tilt_024_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_019]

def tilt_024_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1113823/20000000), (1/100000000), (4240671/100000000), (4272223/100000000), (1/100000000), (5583709/100000000), (21499/20000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-15726674585346044115956710000753715055827311/4570564502938107684231056097300000000000000000), (289633563743/460942500000), (-59353286128304024011388867378867236340583099511/2285282251469053842115528048650000000000000000), (289633563743/460942500000), (-118690845582022701978661778047733718966110371711/4570564502938107684231056097300000000000000000)]
    bernstein := [(8030076353828003706364760051110705986188391449856209/47925842442328292031002638782824448000000000000000000000), (1110541220618228403238755013696917933872831525003401/3993820203527357669250219898568704000000000000000000000), (3111993327001571676131222022698539439652131317544603/8986095457936554755812994771779584000000000000000000000), (278786864444834231329392918631500537471032176552067/748841288161379562984416230981632000000000000000000000), (66646228042299403166089782765133525897283557327489/187210322040344890746104057745408000000000000000000000)]
    reserve := (41888029/250000000000) }

theorem tilt_024_020_valid : tilt_024_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_024_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_024_020]
  · intro i; fin_cases i <;> norm_num [tilt_024_020]
  · norm_num [tilt_024_020]
  · norm_num [tilt_024_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_024_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_024_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_024_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_024_020]

def tiltBundle024_row : Alternative → Row
  | .zero => tilt_024_000
  | (.spike 0 false false) => tilt_024_001
  | (.spike 0 false true) => tilt_024_002
  | (.spike 0 true false) => tilt_024_003
  | (.spike 0 true true) => tilt_024_004
  | (.spike 1 false false) => tilt_024_005
  | (.spike 1 false true) => tilt_024_006
  | (.spike 1 true false) => tilt_024_007
  | (.spike 1 true true) => tilt_024_008
  | (.spike 2 false false) => tilt_024_009
  | (.spike 2 false true) => tilt_024_010
  | (.spike 2 true false) => tilt_024_011
  | (.spike 2 true true) => tilt_024_012
  | (.spike 3 false false) => tilt_024_013
  | (.spike 3 false true) => tilt_024_014
  | (.spike 3 true false) => tilt_024_015
  | (.spike 3 true true) => tilt_024_016
  | (.spike 4 false false) => tilt_024_017
  | (.spike 4 false true) => tilt_024_018
  | (.spike 4 true false) => tilt_024_019
  | (.spike 4 true true) => tilt_024_020

def tiltBundle024 : TiltBundle where
  interval := ⟨(3/320), (1/80)⟩
  lambda := ![(14536169/100000000), (14536169/100000000), (2166209/25000000), (2903681/20000000), (7259203/50000000), (16659137/100000000), (8283439/50000000)]
  row := tiltBundle024_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_024_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_024_001_valid | exact tilt_024_002_valid | exact tilt_024_003_valid | exact tilt_024_004_valid | exact tilt_024_005_valid | exact tilt_024_006_valid | exact tilt_024_007_valid | exact tilt_024_008_valid | exact tilt_024_009_valid | exact tilt_024_010_valid | exact tilt_024_011_valid | exact tilt_024_012_valid | exact tilt_024_013_valid | exact tilt_024_014_valid | exact tilt_024_015_valid | exact tilt_024_016_valid | exact tilt_024_017_valid | exact tilt_024_018_valid | exact tilt_024_019_valid | exact tilt_024_020_valid
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
