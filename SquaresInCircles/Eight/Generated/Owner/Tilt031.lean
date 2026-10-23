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

def tilt_031_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1384541/25000000), (288911/100000000)]
    alternative := .zero
    polynomial := [(-382629308540525167830071675287281429487787047/36053002191755820361711358915100000000000000000), (268742715962283/422918300000000), (-169853694523415624762898855336645803796487787047/18026501095877910180855679457550000000000000000), (268742715962283/422918300000000), (-48474965676898674908281091285429189451926826721/5150428884536545765958765559300000000000000000)]
    bernstein := [(3242342390187954790746508949918074247749973993/60486900521956081746562959817215836160000000000000), (152098690374487955852470750886363007513272692147/1680191681165446715182304439367106560000000000000000), (1271544635738743287857539807286905559742815262999731/11341293847866765327480554965727969280000000000000000000), (2134045162026543137116470554268675023099010094379/18027807737826681493372365229260800000000000000000000), (5902660445234640757736460789682156242594833729261039/54006161180317930130859785551085568000000000000000000000)]
    reserve := (26802021/500000000000) }

theorem tilt_031_000_valid : tilt_031_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_000]
  · intro i; fin_cases i <;> norm_num [tilt_031_000]
  · norm_num [tilt_031_000]
  · norm_num [tilt_031_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_000]

def tilt_031_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7329/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1384541/25000000), (146453/50000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-668064458559079682328345116848080704713742051/63965187047091502428145684190550000000000000000), (19400869459660919537781/30968826894950000000000), (-297380600384063130796430051179623043317249242051/31982593523545751214072842095275000000000000000), (19400869459660919537781/30968826894950000000000), (-594093136309567181910531757242398005929784742051/63965187047091502428145684190550000000000000000)]
    bernstein := [(6740702579264407874188086973982736299651492269/107315775956945630800152462313264250880000000000000), (42062494436341782194609150614289977068549817193/425856253797403296826001834576445440000000000000000), (2406647428409573017866268546002894600087820378214623/20121707991927305775028586683737047040000000000000000000), (4007921438798176847857278637641655838917276926007/31984911765899389246588120622694400000000000000000000), (77718694339890839470195017675680683011853204760450509/670723599730910192500952889457901568000000000000000000000)]
    reserve := (62811851/1000000000000) }

theorem tilt_031_001_valid : tilt_031_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_001]
  · intro i; fin_cases i <;> norm_num [tilt_031_001]
  · norm_num [tilt_031_001]
  · norm_num [tilt_031_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_001]

def tilt_031_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2171/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (3811/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1384541/25000000), (284919/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-3401593961487947032902823293867970299757204121041/316165518201916770872193199542536100000000000000000), (6473565167688541360323/10041454926475000000000), (-1509694613642090439750985883511724457747244583121041/158082759100958385436096599771268050000000000000000), (6473565167688541360323/10041454926475000000000), (-3015987633322692932469068943729580945194731962121041/316165518201916770872193199542536100000000000000000)]
    bernstein := [(38112318734648539916454827036844042214341446050079/530437719062548927894529370245622933749760000000000000), (231047673624577629209583776754537984991777806363763/2104911583581543364660830834308027514880000000000000000), (355209563138093419511881724701444792626818720595877889/2688028981735889837303358295163629731840000000000000000000), (21972497095741920324383234974105873728038770205187437/158094217650974287045341371675495628800000000000000000000), (431897624924593339270943642341679534897054459948376865919/3315235744140930799340808564035143335936000000000000000000000)]
    reserve := (35925347/500000000000) }

theorem tilt_031_002_valid : tilt_031_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_002]
  · intro i; fin_cases i <;> norm_num [tilt_031_002]
  · norm_num [tilt_031_002]
  · norm_num [tilt_031_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_002]

def tilt_031_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2748923/50000000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1384541/25000000), (146453/50000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-5313417885576755915209104641600085457650208343/511466779158145867069490857326100000000000000000), (19400869459660919537781/30968826894950000000000), (-2377832159587023359259813398688054901309171208343/255733389579072933534745428663050000000000000000), (19400869459660919537781/30968826894950000000000), (-4750350901288469962604417692734509717160692208343/511466779158145867069490857326100000000000000000)]
    bernstein := [(101702162542405212897644490683589430164515535417/858098863076051137133213512338516213760000000000000), (4734422401510436593572282132981672168110114141741/30646387967001826326186196869232721920000000000000000), (9402836170510808713336269340993525985714906355874913/53631178942253196070825844521157263360000000000000000000), (416693448927943244368547119349136416758622846876659/2301767336577390389305830236959539200000000000000000000), (920333656518317555933454369634879657400561761535755737/5363117894225319607082584452115726336000000000000000000000)]
    reserve := (29630083/250000000000) }

theorem tilt_031_003_valid : tilt_031_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_003]
  · intro i; fin_cases i <;> norm_num [tilt_031_003]
  · norm_num [tilt_031_003]
  · norm_num [tilt_031_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_003]

def tilt_031_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5503323/100000000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1384541/25000000), (284919/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-1014592511589247565855694271569142667259515569/94860127274696134877098346304300000000000000000), (6473565167688541360323/10041454926475000000000), (-452952388804208678416843396167224645908836515569/47430063637348067438549173152150000000000000000), (6473565167688541360323/10041454926475000000000), (-904890185096828109267831098062880149150413515569/94860127274696134877098346304300000000000000000)]
    bernstein := [(21518170992457671802495655869282130152182088511/159148884507506838919821240919004282880000000000000), (2296110779311650982041798889379131846778607889807/13262407042292236576651770076583690240000000000000000), (5834238959755218627781798478723640486127757307829637/29840415845157532297466482672313303040000000000000000000), (28795905982230645260981509600246212183919305200999/142300504745624855972658477216563200000000000000000000), (192629499512574864959515862477784173139127475188839071/994680528171917743248882755743776768000000000000000000000)]
    reserve := (67603901/500000000000) }

theorem tilt_031_004_valid : tilt_031_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_004]
  · intro i; fin_cases i <;> norm_num [tilt_031_004]
  · norm_num [tilt_031_004]
  · norm_num [tilt_031_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_004]

def tilt_031_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (4337403/100000000), (1/100000000), (1384541/25000000), (146453/50000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-7954643340005539848230653150685834543492453/761149354549477051727178130631250000000000000), (19400869459660919537781/30968826894950000000000), (-3538665106832740575799495467901787100891054953/380574677274738525863589065315625000000000000), (19400869459660919537781/30968826894950000000000), (-7069375570325475611750760282652888367238617453/761149354549477051727178130631250000000000000)]
    bernstein := [(71711136389472293981873004480578861357821507/1276996712953715918387004056807669760000000000000), (3267521125190869634373912019769606800400082353/35472130915380997732972334911324160000000000000000), (27043783905922733649861692326018077997031937078769/239436883678821734697563260651438080000000000000000000), (45158020334218782239110589559218331725810412121/380602263040568645203565825228800000000000000000000), (871665305311735232318460576052363649739912413288227/7981229455960724489918775355047936000000000000000000000)]
    reserve := (11231217/200000000000) }

theorem tilt_031_005_valid : tilt_031_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_005]
  · intro i; fin_cases i <;> norm_num [tilt_031_005]
  · norm_num [tilt_031_005]
  · norm_num [tilt_031_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_005]

def tilt_031_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (4341289/100000000), (1/100000000), (1384541/25000000), (284919/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-354883686538372721961831968083012372575045521/33199379220791018887353599512860000000000000000), (6473565167688541360323/10041454926475000000000), (-158525178355008564701975270497235019375170445521/16599689610395509443676799756430000000000000000), (6473565167688541360323/10041454926475000000000), (-316695473023478756681988709026387026377765845521/33199379220791018887353599512860000000000000000)]
    bernstein := [(7877067622794446379950032551284731673800431199/55699315625312261473321100740474699776000000000000), (39640082786626312692644665643377049571390388403/221029030259175640767147225160613888000000000000000), (2106785124194707653904383565642552071489144146920933/10443621679746049026247706388839006208000000000000000000), (3462534057655776093633991367307926411206476650797/16600892830624779885944534078586880000000000000000000), (69580864135032424563359490880315266025650806263970239/348120722658201634208256879627966873600000000000000000000)]
    reserve := (8838829/62500000000) }

theorem tilt_031_006_valid : tilt_031_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_006]
  · intro i; fin_cases i <;> norm_num [tilt_031_006]
  · norm_num [tilt_031_006]
  · norm_num [tilt_031_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_006]

def tilt_031_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (845437/20000000), (2169673/50000000), (1/100000000), (1384541/25000000), (146453/50000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-133634864937340953072253453568997528278194891/12786993573352559711496098136450000000000000000), (3879258278118195837159/6190839248050000000000), (-59450112431042417968647707094018173195731144891/6393496786676279855748049068225000000000000000), (3879258278118195837159/6190839248050000000000), (-118766589997147494984223160734467348863184094891/12786993573352559711496098136450000000000000000)]
    bernstein := [(1297331915673510712799133567956511585337192229/21453015317074773843266772159241912320000000000000), (57525679935980976411609147727737927015213293191/595917092140965940090743671090053120000000000000000), (472498329669189734945304807454087576164915318487943/4022440371951520095612519779857858560000000000000000000), (183641964628451474603086961797256578977113051279671/1489792730352414850226859177725132800000000000000000000), (15276110035238023536009008688270055636763284019648069/134081345731717336520417325995261952000000000000000000000)]
    reserve := (60473173/1000000000000) }

theorem tilt_031_007_valid : tilt_031_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_007]
  · intro i; fin_cases i <;> norm_num [tilt_031_007]
  · norm_num [tilt_031_007]
  · norm_num [tilt_031_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_007]

def tilt_031_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4231181/100000000), (2169673/50000000), (1/100000000), (1384541/25000000), (284919/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-35489205960974042711474580805718952572193541/3320019782803645812822934586628000000000000000), (6475136010530172134661/10046198827825000000000), (-15852388419387973641021932430620343805954533541/1660009891401822906411467293314000000000000000), (6475136010530172134661/10046198827825000000000), (-31669287632814973239332390280434968659336873541/3320019782803645812822934586628000000000000000)]
    bernstein := [(763698301995633511482898223157809522248889579/5570068902036985138922594331372866764800000000000), (27065723423370882214711731968618945238237612841/154724136167694031636738731427024076800000000000000), (205968694843323683358286786166334234067529427044393/1044387919131934713547986437132412518400000000000000000), (78894167310155412399096932270395344757836596755321/386810340419235079091846828567560192000000000000000000), (6794166287264663523516743928705938064704921774313419/34812930637731157118266214571080417280000000000000000000)]
    reserve := (68553757/500000000000) }

theorem tilt_031_008_valid : tilt_031_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_008]
  · intro i; fin_cases i <;> norm_num [tilt_031_008]
  · norm_num [tilt_031_008]
  · norm_num [tilt_031_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_008]

def tilt_031_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (1084351/25000000), (1/100000000), (1384541/25000000), (146453/50000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-1336390060317411712222883331803831023942823279/127873121045799468859062542231400000000000000000), (19400869459660919537781/30968826894950000000000), (-594495884681592126067109170935283421697496823279/63936560522899734429531271115700000000000000000), (19400869459660919537781/30968826894950000000000), (-1187655379302866840421995458538763012371050823279/127873121045799468859062542231400000000000000000)]
    bernstein := [(12031216587984345370781255241672521180440308001/214535497237952358173376582852531978240000000000000), (78356006477169344803816911937538146915646881997/851331338245842691164192789097349120000000000000000), (4540307932156694634291722294540541739764354635021467/40225405732116067157508109284849745920000000000000000000), (7581702354288283160311243265355484884676754750803/63941194932627669937224780297011200000000000000000000), (146338156522247675458385904140488253601626322017088961/1340846857737202238583603642828324864000000000000000000000)]
    reserve := (56080307/1000000000000) }

theorem tilt_031_009_valid : tilt_031_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_009]
  · intro i; fin_cases i <;> norm_num [tilt_031_009]
  · norm_num [tilt_031_009]
  · norm_num [tilt_031_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_009]

def tilt_031_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (434129/10000000), (1/100000000), (1384541/25000000), (284919/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-11032619473789370398671904579089611238724319/1037480839629570865829533204518750000000000000), (6473565167688541360323/10041454926475000000000), (-4953855466424336199210003491178587453932286819/518740419814785432914766602259375000000000000), (6473565167688541360323/10041454926475000000000), (-9896678313374883028021335077778085296625849319/1037480839629570865829533204518750000000000000)]
    bernstein := [(342813037170704754130425051501971751852254761/1740604014232667040332909775138324480000000000000), (95431785907178840901294665855462373890240101/406303458037503977668746446110720000000000000000), (83963386227308431740783733640699597825944387318387/326363252668625070062420582838435840000000000000000000), (8060019756663467212962668753404085043540282299/30516354144447723644648338227200000000000000000000), (2778741418413787131169974527361788559980649418405321/10878775088954169002080686094614528000000000000000000000)]
    reserve := (98475309/500000000000) }

theorem tilt_031_010_valid : tilt_031_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_010]
  · intro i; fin_cases i <;> norm_num [tilt_031_010]
  · norm_num [tilt_031_010]
  · norm_num [tilt_031_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_010]

def tilt_031_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14597/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1384541/25000000), (146453/50000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-668106694575926969902984480663704960027722051/63965187047091502428145684190550000000000000000), (19400869459660919537781/30968826894950000000000), (-297380642620079978084004690543438667572563222051/31982593523545751214072842095275000000000000000), (19400869459660919537781/30968826894950000000000), (-594093178545584029198106396606213630185098722051/63965187047091502428145684190550000000000000000)]
    bernstein := [(6669703834944117461219316399918363116851112269/107315775956945630800152462313264250880000000000000), (41780725900520141844882914782027534367470957193/425856253797403296826001834576445440000000000000000), (2393332522958093155084444587864525090500731900754623/20121707991927305775028586683737047040000000000000000000), (3986754230127937893386433461642949127193091786007/31984911765899389246588120622694400000000000000000000), (77274770343210413386477558710592645509927552395270509/670723599730910192500952889457901568000000000000000000000)]
    reserve := (7768783/125000000000) }

theorem tilt_031_011_valid : tilt_031_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_011]
  · intro i; fin_cases i <;> norm_num [tilt_031_011]
  · norm_num [tilt_031_011]
  · norm_num [tilt_031_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_011]

def tilt_031_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (759/20000000), (1384541/25000000), (284919/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-892527472705619348438660949873713905912812523/82961301023856407995852322105100000000000000000), (6473565167688541360323/10041454926475000000000), (-396141286244839571780368091602683078232201812523/41480650511928203997926161052550000000000000000), (6473565167688541360323/10041454926475000000000), (-791390045016973524212297522255492442558490812523/82961301023856407995852322105100000000000000000)]
    bernstein := [(10076371647633854866870398530957119937576468837/139185966691826010993054151205883740160000000000000), (60927198561610255130457655657033514647240375489/552325264650103218226405361928110080000000000000000), (3462844956350236124735871917875655896044684072311879/26097368754717377061197653351103201280000000000000000000), (5788134002596179426438176680338051919299355718111/41483657216209469180094823320780800000000000000000000), (113802925618108302772878903894931502957212020031412357/869912291823912568706588445036773376000000000000000000000)]
    reserve := (2895801/40000000000) }

theorem tilt_031_012_valid : tilt_031_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_012]
  · intro i; fin_cases i <;> norm_num [tilt_031_012]
  · norm_num [tilt_031_012]
  · norm_num [tilt_031_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_012]

def tilt_031_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (5535413/100000000), (146453/50000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-1328224798760390067625461182367840869656940503/127866826597371227984685605613075000000000000000), (19400869459660919537781/30968826894950000000000), (-594458521635402337142382751526988673376582690503/63933413298685613992342802806537500000000000000), (19400869459660919537781/30968826894950000000000), (-1187588818472044284217140041871609505883508440503/127866826597371227984685605613075000000000000000)]
    bernstein := [(25645848331080261774151018322002026986249434457/214524936905864212408431509746137169920000000000000), (132386087103775513006186052084242381213674398629/851289432166127827017585356135464960000000000000000), (7093445369706368296154440624486102422696442597356419/40223425669849539826580908077400719360000000000000000000), (11640503572159105651716708128531647977300982830971/63938047480288570698745681254809600000000000000000000), (231460974787147746641353399402186609169301782888573177/1340780855661651327552696935913357312000000000000000000000)]
    reserve := (59773583/500000000000) }

theorem tilt_031_013_valid : tilt_031_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_013]
  · intro i; fin_cases i <;> norm_num [tilt_031_013]
  · norm_num [tilt_031_013]
  · norm_num [tilt_031_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_013]

def tilt_031_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1385229/25000000), (284919/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-591935141988209321644658865171148358943518767/55335017191485885065489340894600000000000000000), (6473565167688541360323/10041454926475000000000), (-264222044502016475148046897726887997931637518767/27667508595742942532744670447300000000000000000), (6473565167688541360323/10041454926475000000000), (-527852153862044740974449136588604847504331518767/55335017191485885065489340894600000000000000000)]
    bernstein := [(12400761014157826514817892386200922782395672673/92836753578527205469488881788633743360000000000000), (63179570030048969407404784583680471728439219981/368399815787806370910670165827911680000000000000000), (3374892080421735258070145372735171455915726952243291/17406891295973851025529165335368826880000000000000000000), (5554032968769060205190802674096504358084493254419/27669514061315929145651192712396800000000000000000000), (111419876334669947901672794770475110267328531074538753/580229709865795034184305511178960896000000000000000000000)]
    reserve := (133575987/1000000000000) }

theorem tilt_031_014_valid : tilt_031_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_014]
  · intro i; fin_cases i <;> norm_num [tilt_031_014]
  · norm_num [tilt_031_014]
  · norm_num [tilt_031_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_014]

def tilt_031_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14597/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1384541/25000000), (146453/50000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-668106694575926969902984480663704960027722051/63965187047091502428145684190550000000000000000), (19400869459660919537781/30968826894950000000000), (-297380642620079978084004690543438667572563222051/31982593523545751214072842095275000000000000000), (19400869459660919537781/30968826894950000000000), (-594093178545584029198106396606213630185098722051/63965187047091502428145684190550000000000000000)]
    bernstein := [(6669703834944117461219316399918363116851112269/107315775956945630800152462313264250880000000000000), (41780725900520141844882914782027534367470957193/425856253797403296826001834576445440000000000000000), (2393332522958093155084444587864525090500731900754623/20121707991927305775028586683737047040000000000000000000), (3986754230127937893386433461642949127193091786007/31984911765899389246588120622694400000000000000000000), (77274770343210413386477558710592645509927552395270509/670723599730910192500952889457901568000000000000000000000)]
    reserve := (7768783/125000000000) }

theorem tilt_031_015_valid : tilt_031_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_015]
  · intro i; fin_cases i <;> norm_num [tilt_031_015]
  · norm_num [tilt_031_015]
  · norm_num [tilt_031_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_015]

def tilt_031_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (759/20000000), (1384541/25000000), (284919/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-892527472705619348438660949873713905912812523/82961301023856407995852322105100000000000000000), (6473565167688541360323/10041454926475000000000), (-396141286244839571780368091602683078232201812523/41480650511928203997926161052550000000000000000), (6473565167688541360323/10041454926475000000000), (-791390045016973524212297522255492442558490812523/82961301023856407995852322105100000000000000000)]
    bernstein := [(10076371647633854866870398530957119937576468837/139185966691826010993054151205883740160000000000000), (60927198561610255130457655657033514647240375489/552325264650103218226405361928110080000000000000000), (3462844956350236124735871917875655896044684072311879/26097368754717377061197653351103201280000000000000000000), (5788134002596179426438176680338051919299355718111/41483657216209469180094823320780800000000000000000000), (113802925618108302772878903894931502957212020031412357/869912291823912568706588445036773376000000000000000000000)]
    reserve := (2895801/40000000000) }

theorem tilt_031_016_valid : tilt_031_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_016]
  · intro i; fin_cases i <;> norm_num [tilt_031_016]
  · norm_num [tilt_031_016]
  · norm_num [tilt_031_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_016]

def tilt_031_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (5535413/100000000), (146453/50000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-2656455862743959014330465272673672702498830131/255733653194742455969371211226150000000000000000), (19400869459660919537781/30968826894950000000000), (-1188917049536027853163845045961915337716350330131/127866826597371227984685605613075000000000000000), (19400869459660919537781/30968826894950000000000), (-2375177643209311747313359626651157002730201830131/255733653194742455969371211226150000000000000000)]
    bernstein := [(51281164821996827815590408400241244858599389789/429049873811728424816863019492274339840000000000000), (264730377113660958278718638769021906745357484633/1702578864332255654035170712270929920000000000000000), (14184915627636433936653244373862039375581667544836463/80446851339699079653161816154801438720000000000000000000), (23277867234442891986061574062618794751669481674567/127876094960577141397491362509619200000000000000000000), (462856098598723646456936015983760209626205850700207229/2681561711323302655105393871826714624000000000000000000000)]
    reserve := (119522619/1000000000000) }

theorem tilt_031_017_valid : tilt_031_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_017]
  · intro i; fin_cases i <;> norm_num [tilt_031_017]
  · norm_num [tilt_031_017]
  · norm_num [tilt_031_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_017]

def tilt_031_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1385229/25000000), (284919/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-295483274626489721581262271034840058145795071/27667508595742942532744670447300000000000000000), (6473565167688541360323/10041454926475000000000), (-132110537954640622634782381701893264844492795071/13833754297871471266372335223650000000000000000), (6473565167688541360323/10041454926475000000000), (-263925592634654755547983501132751689630839795071/27667508595742942532744670447300000000000000000)]
    bernstein := [(7014482701039626121642844759884519340143845649/46418376789263602734744440894316871680000000000000), (34820664453774491506358874757230626121534957053/184199907893903185455335082913955840000000000000000), (1840120483177479150384854874049879345789388792783083/8703445647986925512764582667684413440000000000000000000), (3019728819418616372029716910359255779690376730147/13834757030657964572825596356198400000000000000000000), (60800161989026709783919262868732071580632604855968689/290114854932897517092152755589480448000000000000000000000)]
    reserve := (151114347/1000000000000) }

theorem tilt_031_018_valid : tilt_031_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_018]
  · intro i; fin_cases i <;> norm_num [tilt_031_018]
  · norm_num [tilt_031_018]
  · norm_num [tilt_031_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_018]

def tilt_031_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1384541/25000000), (288911/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-53832388620295509134297299858065546294652471/5150428884536545765958765559300000000000000000), (268742715962283/422918300000000), (-169853858730299917216931334752154642213915793297/18026501095877910180855679457550000000000000000), (268742715962283/422918300000000), (-339330890740257765869922588405302825603769019297/36053002191755820361711358915100000000000000000)]
    bernstein := [(1853846009131727002833566586415826544655113209/8640985788850868820937565688173690880000000000000), (422502906738873984374078054654434555252549606837/1680191681165446715182304439367106560000000000000000), (3096767681291949088347687567825035089778570526092981/11341293847866765327480554965727969280000000000000000000), (5035360441420359544284691044472539237442981077629/18027807737826681493372365229260800000000000000000000), (102159011402532730209998212356059856376810987063455023/378043128262225510916018498857598976000000000000000000000)]
    reserve := (26817629/125000000000) }

theorem tilt_031_019_valid : tilt_031_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_019]
  · intro i; fin_cases i <;> norm_num [tilt_031_019]
  · norm_num [tilt_031_019]
  · norm_num [tilt_031_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_019]

def tilt_031_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/32), (11/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(687573/12500000), (1/100000000), (4229183/100000000), (2169673/50000000), (1/100000000), (1384541/25000000), (288911/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-54648199559190779013024140658732320604652471/5150428884536545765958765559300000000000000000), (268742715962283/422918300000000), (-169847964189906012767612449803727552388463793297/18026501095877910180855679457550000000000000000), (268742715962283/422918300000000), (-339313390982897690082133730622843978532695019297/36053002191755820361711358915100000000000000000)]
    bernstein := [(487905693941498621005391614155573753207993209/8640985788850868820937565688173690880000000000000), (156930305492421657827001041359260062819315926837/1680191681165446715182304439367106560000000000000000), (1304340316660652869495093444192297947226736916092981/11341293847866765327480554965727969280000000000000000000), (2186475403921588940078338849105864611782923077629/18027807737826681493372365229260800000000000000000000), (42424555068660250872377345794837416181560303097455023/378043128262225510916018498857598976000000000000000000000)]
    reserve := (14116031/250000000000) }

theorem tilt_031_020_valid : tilt_031_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_031_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_031_020]
  · intro i; fin_cases i <;> norm_num [tilt_031_020]
  · norm_num [tilt_031_020]
  · norm_num [tilt_031_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_031_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_031_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_031_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_031_020]

def tiltBundle031_row : Alternative → Row
  | .zero => tilt_031_000
  | (.spike 0 false false) => tilt_031_001
  | (.spike 0 false true) => tilt_031_002
  | (.spike 0 true false) => tilt_031_003
  | (.spike 0 true true) => tilt_031_004
  | (.spike 1 false false) => tilt_031_005
  | (.spike 1 false true) => tilt_031_006
  | (.spike 1 true false) => tilt_031_007
  | (.spike 1 true true) => tilt_031_008
  | (.spike 2 false false) => tilt_031_009
  | (.spike 2 false true) => tilt_031_010
  | (.spike 2 true false) => tilt_031_011
  | (.spike 2 true true) => tilt_031_012
  | (.spike 3 false false) => tilt_031_013
  | (.spike 3 false true) => tilt_031_014
  | (.spike 3 true false) => tilt_031_015
  | (.spike 3 true true) => tilt_031_016
  | (.spike 4 false false) => tilt_031_017
  | (.spike 4 false true) => tilt_031_018
  | (.spike 4 true false) => tilt_031_019
  | (.spike 4 true true) => tilt_031_020

def tiltBundle031 : TiltBundle where
  interval := ⟨(1/32), (11/320)⟩
  lambda := ![(14657491/100000000), (14657491/100000000), (9047127/100000000), (14596789/100000000), (14596789/100000000), (4087413/25000000), (16094661/100000000)]
  row := tiltBundle031_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_031_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_031_001_valid | exact tilt_031_002_valid | exact tilt_031_003_valid | exact tilt_031_004_valid | exact tilt_031_005_valid | exact tilt_031_006_valid | exact tilt_031_007_valid | exact tilt_031_008_valid | exact tilt_031_009_valid | exact tilt_031_010_valid | exact tilt_031_011_valid | exact tilt_031_012_valid | exact tilt_031_013_valid | exact tilt_031_014_valid | exact tilt_031_015_valid | exact tilt_031_016_valid | exact tilt_031_017_valid | exact tilt_031_018_valid | exact tilt_031_019_valid | exact tilt_031_020_valid
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
