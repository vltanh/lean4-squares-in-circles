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

def tilt_043_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (1352673/25000000), (70427/10000000)]
    alternative := .zero
    polynomial := [(-204713354559699518315466825346417009956165383/6855701576148569327493696898050000000000000000), (164294940911/249125000000), (-12533758705948355227694341936384393138956165383/3427850788074284663746848449025000000000000000), (164294940911/249125000000), (-24862804057337010937073217047422369267956165383/6855701576148569327493696898050000000000000000)]
    bernstein := [(22304888992118172008363294964485279326468231017817/280809536559045399654141824944128000000000000000000000), (3034021479106551658465537453260186247533363209189/31910174608982431778879752834560000000000000000000000), (140748040149193774816275496163378233720037818439419/1316294702620525310878789804425600000000000000000000000), (337199184519115225133355842362909541963549136773/2932920460384414685558800812000000000000000000000000), (4807320024036448087983337555833453913760786968361/40327656330285701926433511165000000000000000000000000)]
    reserve := (79430667/1000000000000) }

theorem tilt_043_000_valid : tilt_043_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_000]
  · intro i; fin_cases i <;> norm_num [tilt_043_000]
  · norm_num [tilt_043_000]
  · norm_num [tilt_043_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_000]

def tilt_043_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![(2997/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (1352673/25000000), (708029/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1023179742271055741356544712406834428519177589/34461467414904052368949655111175000000000000000), (2314942309516836939/3527754492500000000), (-62700980089508333194191670183517303374774677589/17230733707452026184474827555587500000000000000), (2314942309516836939/3527754492500000000), (-17768397205249372949575256522089681760147168227/4923066773557721766992807873025000000000000000)]
    bernstein := [(134634771015524006270181156561080233825756314348011/1411541705314469985032177873353728000000000000000000000), (17785747611825625466104245401749291027292256019087/160402466513007952844565667426560000000000000000000000), (811187796831457335439182492966095514134950787276177/6616601743661578054838333781345600000000000000000000000), (1924380400325217314309918616466814642145087566959/14742873760386760371743167962000000000000000000000000), (27299872783400498067944773581257799464027377097563/202714514205317955111468559477500000000000000000000000)]
    reserve := (47690681/500000000000) }

theorem tilt_043_001_valid : tilt_043_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_001]
  · intro i; fin_cases i <;> norm_num [tilt_043_001]
  · norm_num [tilt_043_001]
  · norm_num [tilt_043_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_001]

def tilt_043_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, (4439/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (487/12500000), (835067/20000000), (4509307/100000000), (1/100000000), (1352673/25000000), (21891/3125000)]
    alternative := (.spike 0 false true)
    polynomial := [(-581227150498062690067129995482670617992074471497/19371981706282099796350560422295600000000000000000), (2313380897797580081/3490301040000000000), (-35587518175610657233538125330837105161598518471497/9685990853141049898175280211147800000000000000000), (2313380897797580081/3490301040000000000), (-70593809200723251777009120666191539705204962471497/19371981706282099796350560422295600000000000000000)]
    bernstein := [(73121408710814026148547273451761865034974626865897303/793476370689314807658518954897227776000000000000000000000), (9734458125002999952613437975240424908949440949515851/90167769396513046324831699420139520000000000000000000000), (446126693665821099936034408471342011205659152582358421/3719420487606163160899307601080755200000000000000000000000), (1061694720001051158533226652612565522341396451870507/8287478804826566757797031196704000000000000000000000000), (15092605918840247529661630820562405933271642129374599/113952833566365292919709178954680000000000000000000000000)]
    reserve := (92153227/1000000000000) }

theorem tilt_043_002_valid : tilt_043_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_002]
  · intro i; fin_cases i <;> norm_num [tilt_043_002]
  · norm_num [tilt_043_002]
  · norm_num [tilt_043_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_002]

def tilt_043_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (8969/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5348469/100000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (1352673/25000000), (708029/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-194483328589261882539485771565313899055464031/6560805236436829190454096158550000000000000000), (2314942309516836939/3527754492500000000), (-1705251223793855804624284224431692098196923433/468628945459773513603864011325000000000000000), (2314942309516836939/3527754492500000000), (-23679033804524719382200493370478375475701464031/6560805236436829190454096158550000000000000000)]
    bernstein := [(38547673980600537072034394892150587414959034858369/268730582484452523640999778654208000000000000000000000), (4854088114667231619440007916031858925540954171373/30537566191415059504659065756160000000000000000000000), (215003819057811346731841013722791623616634700426483/1259674605395871204567186462441600000000000000000000000), (501353137172313904319316773257253027791431109261/2806761598475648851531164132000000000000000000000000), (7053871845837760612439831574732581477027874368977/38592971979040171708553506815000000000000000000000000)]
    reserve := (143443569/1000000000000) }

theorem tilt_043_003_valid : tilt_043_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_003]
  · intro i; fin_cases i <;> norm_num [tilt_043_003]
  · norm_num [tilt_043_003]
  · norm_num [tilt_043_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_003]

def tilt_043_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (369/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(167307/3125000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (1352673/25000000), (21891/3125000)]
    alternative := (.spike 0 true true)
    polynomial := [(-3545021072511685593019917399038765720977157/118446737088424822615938985200000000000000000), (2313380897797580081/3490301040000000000), (-217585123544205413832882020357895015668977157/59223368544212411307969492600000000000000000), (2313380897797580081/3490301040000000000), (-431625226015899142072744123316751265616977157/118446737088424822615938985200000000000000000)]
    bernstein := [(812868156964361919218474116198560585760014255643/4851578351141880734348860833792000000000000000000000), (101094595206329426219900545388992542367817533631/551315721720668265266916003840000000000000000000000), (4443106620371745725429140190300182692031945360801/22741773520977565942260285158400000000000000000000000), (10314458040534850970988734625523376474231143967/50672400893443774381150368000000000000000000000000), (144857868818088352366653256184453467023695207819/696745512284851897740817560000000000000000000000000)]
    reserve := (41886789/250000000000) }

theorem tilt_043_004_valid : tilt_043_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_004]
  · intro i; fin_cases i <;> norm_num [tilt_043_004]
  · norm_num [tilt_043_004]
  · norm_num [tilt_043_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_004]

def tilt_043_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (450721/10000000), (1/100000000), (1352673/25000000), (708029/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-12031057614496790185719179630964971492873263/405240488425982591319669388650000000000000000), (2314942309516836939/3527754492500000000), (-737314796604235983860941417378606399841873263/202620244212991295659834694325000000000000000), (2314942309516836939/3527754492500000000), (-208942647941996453933737665018035404027267609/57891498346568941617095626950000000000000000)]
    bernstein := [(1614529808333467517088753756235787597350750261937/16598650405928246940453658159104000000000000000000000), (2339783011882155571655177889247827976101789899519/20748313007410308675567072698880000000000000000000000), (9685861487099043968215981297022123800057079440259/77806173777788657533376522620800000000000000000000000), (252523273621205420380044556820811593386706095583/1907014063181094547386679476000000000000000000000000), (325528647811478199460407091794070498543334968321/2383767578976368184233349345000000000000000000000000)]
    reserve := (97268739/1000000000000) }

theorem tilt_043_005_valid : tilt_043_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_005]
  · intro i; fin_cases i <;> norm_num [tilt_043_005]
  · norm_num [tilt_043_005]
  · norm_num [tilt_043_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_005]

def tilt_043_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (1127851/25000000), (1/100000000), (1352673/25000000), (21891/3125000)]
    alternative := (.spike 1 false true)
    polynomial := [(-297811487771093273059425985905195352336378667/9949173725739217887604493528400000000000000000), (2313380897797580081/3490301040000000000), (-18276543668262809695299469227439391763652378667/4974586862869608943802246764200000000000000000), (2313380897797580081/3490301040000000000), (-36255275848754526117539512468973588174968378667/9949173725739217887604493528400000000000000000)]
    bernstein := [(66604175305660004962993085496228616497363222558133/407518155806278364676280054923264000000000000000000000), (91314728960886075359149696153521536927965573656571/509397694757847955845350068654080000000000000000000000), (365355885447348811450336621276163897489594060737231/1910241355341929834420062757452800000000000000000000000), (9337731765238649999619247131426720589098220131547/46819641062302201824021146016000000000000000000000000), (11926963914102199837625945976861682352617872177989/58524551327877752280026432520000000000000000000000000)]
    reserve := (163438547/1000000000000) }

theorem tilt_043_006_valid : tilt_043_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_006]
  · intro i; fin_cases i <;> norm_num [tilt_043_006]
  · norm_num [tilt_043_006]
  · norm_num [tilt_043_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_006]

def tilt_043_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (417307/10000000), (4509307/100000000), (1/100000000), (1352673/25000000), (708029/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-92963449362612234951930872250031919319074363/3131161186633443866709720455850000000000000000), (484861739098870658901/738663644757500000000), (-5697558764969178408352158440448604809707474363/1565580593316721933354860227925000000000000000), (484861739098870658901/738663644757500000000), (-1614593440082249225964626572663882528585124909/447308740947634838101388636550000000000000000)]
    bernstein := [(14188223428434391259908739839503161390299176700837/128252362204505860780430149871616000000000000000000000), (1839447517727621370906835304500654375061848798529/14574132068693847815957971576320000000000000000000000), (82972164441220242609340263529458726355383464502559/601182947833621222408266327523200000000000000000000000), (195612154612637367102396688248724842349686509153/1339534197490243365437313564000000000000000000000000), (2767506484417918462527640859969372453069894132021/18418595215490846274763061505000000000000000000000000)]
    reserve := (13828423/125000000000) }

theorem tilt_043_007_valid : tilt_043_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_007]
  · intro i; fin_cases i <;> norm_num [tilt_043_007]
  · norm_num [tilt_043_007]
  · norm_num [tilt_043_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_007]

def tilt_043_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (2611/62500), (4509307/100000000), (1/100000000), (1352673/25000000), (21891/3125000)]
    alternative := (.spike 1 true true)
    polynomial := [(-1063656486543205993916283217607438171910503/35535513444449747315895554400000000000000000), (605966660736232387/914518416000000000), (-65271987395463572930357867864404245106890503/17767756722224873657947777200000000000000000), (605966660736232387/914518416000000000), (-129480318304383939866799452511201052041870503/35535513444449747315895554400000000000000000)]
    bernstein := [(218462622907565796115206871188005909003542560697/1455534630684661650059081908224000000000000000000000), (27428223961209774792683494640329591609219470149/165401662577802460233986580480000000000000000000000), (1212722706463318192039918824314104243830734647579/6822818581334351484651946444800000000000000000000000), (2825206372674390863882181533136864924060331493/15202358692812726124447296000000000000000000000000), (39739175216396085025274961653412546928551339401/209032432026174984211150320000000000000000000000000)]
    reserve := (75045491/500000000000) }

theorem tilt_043_008_valid : tilt_043_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_008]
  · intro i; fin_cases i <;> norm_num [tilt_043_008]
  · norm_num [tilt_043_008]
  · norm_num [tilt_043_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_008]

def tilt_043_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4507211/100000000), (1/100000000), (1352673/25000000), (708029/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-8181138877746676289717274179755338734766193/275563593268051359167882681686200000000000000), (2314942309516836939/3527754492500000000), (-501374190813880856633562496888733526025578193/137781796634025679583941340843100000000000000), (2314942309516836939/3527754492500000000), (-142081034678573576711058245656815959045198599/39366227609721622738268954526600000000000000)]
    bernstein := [(1097136692776737476632930829361672811707653617007/11287084780259383671516474641866752000000000000000000), (1590122823647015392930374665271298406848594400609/14108855975324229589395593302333440000000000000000000), (6582899092918375155330347117765156947911153462749/52908209907465860960233474883750400000000000000000000), (171630350651589862890915220472699336360335587713/1296769850673182866672389090288000000000000000000000), (221252613875280883545994505527951220023017369631/1620962313341478583340486362860000000000000000000000)]
    reserve := (97202839/1000000000000) }

theorem tilt_043_009_valid : tilt_043_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_009]
  · intro i; fin_cases i <;> norm_num [tilt_043_009]
  · norm_num [tilt_043_009]
  · norm_num [tilt_043_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_009]

def tilt_043_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (902281/20000000), (1/100000000), (1352673/25000000), (21891/3125000)]
    alternative := (.spike 2 false true)
    polynomial := [(-237874106739606366339762182677334722665061529/7959340744862315372195148140400000000000000000), (2313380897797580081/3490301040000000000), (-14620863039272579591681734177218028725861061529/3979670372431157686097574070200000000000000000), (2313380897797580081/3490301040000000000), (-29003851971805552817023706171758722729057061529/7959340744862315372195148140400000000000000000)]
    bernstein := [(68885120581377342501077898804614232057152376440071/326014596909560437645113267830784000000000000000000000), (92558243713309324603116134871146859214830913399177/407518246136950547056391584788480000000000000000000000), (365449969320425291235736363130390153330564662066597/1528193423013564551461468442956800000000000000000000000), (9263848333453847430225210042798206429168369762089/37455721152293248810330108896000000000000000000000000), (11784150353635414850785212774053423913021796607543/46819651440366561012912636120000000000000000000000000)]
    reserve := (211294589/1000000000000) }

theorem tilt_043_010_valid : tilt_043_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_010]
  · intro i; fin_cases i <;> norm_num [tilt_043_010]
  · norm_num [tilt_043_010]
  · norm_num [tilt_043_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_010]

def tilt_043_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3689/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (1352673/25000000), (708029/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1023265234667225015305381872036481016976933589/34461467414904052368949655111175000000000000000), (2314942309516836939/3527754492500000000), (-62701065581904502468140507343146949963232433589/17230733707452026184474827555587500000000000000), (2314942309516836939/3527754492500000000), (-17768409418448825702996518973465345558498276227/4923066773557721766992807873025000000000000000)]
    bernstein := [(131079176370309974278349273590770848856478918992011/1411541705314469985032177873353728000000000000000000000), (17381615052523115704898977884733198736630086567087/160402466513007952844565667426560000000000000000000000), (794513675606021197586675934430337186185395040184177/6616601743661578054838333781345600000000000000000000000), (1887219505974715176242819277407961683800744802959/14742873760386760371743167962000000000000000000000000), (26788796417851504815755921688962715326142903149563/202714514205317955111468559477500000000000000000000000)]
    reserve := (46431209/500000000000) }

theorem tilt_043_011_valid : tilt_043_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_011]
  · intro i; fin_cases i <;> norm_num [tilt_043_011]
  · norm_num [tilt_043_011]
  · norm_num [tilt_043_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_011]

def tilt_043_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4371/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (959/25000000), (1352673/25000000), (21891/3125000)]
    alternative := (.spike 2 true true)
    polynomial := [(-163496261209223449008229381375932127301747558467/5449612923533157437577057038715600000000000000000), (2313380897797580081/3490301040000000000), (-10011261908930836287725942648200485582073991558467/2724806461766578718788528519357800000000000000000), (2313380897797580081/3490301040000000000), (-19859027556652449126443655915025039036846235558467/5449612923533157437577057038715600000000000000000)]
    bernstein := [(21034697016886963474159484781875505395132787745298333/223216145347918128643156256305790976000000000000000000000), (2791248900650046316845925882716514417595713641150361/25365471062263423709449574580203520000000000000000000000), (127680563406569668742410494028875784029100543963738631/1046325681318366228014794951433395200000000000000000000000), (303525572748985650153216103280983396653616261707577/2331385207928623502706762369504000000000000000000000000), (4312546113892596593188643438803026169539941210844589/32056546609018573162217982580680000000000000000000000000)]
    reserve := (94234657/1000000000000) }

theorem tilt_043_012_valid : tilt_043_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_012]
  · intro i; fin_cases i <;> norm_num [tilt_043_012]
  · norm_num [tilt_043_012]
  · norm_num [tilt_043_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_012]

def tilt_043_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (5407991/100000000), (708029/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-11434910532643945381462208154522539011962792743/385775760848678333203563285453430000000000000000), (2314942309516836939/3527754492500000000), (-701881433600256738512114474066965008838714592743/192887880424339166601781642726715000000000000000), (2314942309516836939/3527754492500000000), (-1392327956667869531642766739979407478665466392743/385775760848678333203563285453430000000000000000)]
    bernstein := [(2296609619504832939106601670001927473903220029334457/15801375164361864528017952172172492800000000000000000000), (288830968108590412590190453042149625546114035888069/1795610814132030060002040019565056000000000000000000000), (12782943029988261328393679872879013436592949873679899/74068946082946239975084150807058560000000000000000000000), (506484043706542430400622125266013567276020477479861/2805641897081296968753187530570400000000000000000000000), (7124374239328203826167374632232841364802836053553177/38577576084867833320356328545343000000000000000000000000)]
    reserve := (145342389/1000000000000) }

theorem tilt_043_013_valid : tilt_043_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_013]
  · intro i; fin_cases i <;> norm_num [tilt_043_013]
  · norm_num [tilt_043_013]
  · norm_num [tilt_043_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_013]

def tilt_043_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (1082679/20000000), (21891/3125000)]
    alternative := (.spike 3 false true)
    polynomial := [(-953036327244925081030603763816800820216929909/31838454698507203702921206212400000000000000000), (2313380897797580081/3490301040000000000), (-58486964856837370517628211773341778670692929909/15919227349253601851460603106200000000000000000), (2313380897797580081/3490301040000000000), (-38673631128809938651408606594288918840389643303/10612818232835734567640402070800000000000000000)]
    bernstein := [(70954349367854447372242311441500801630455695907897/434701034816951687890550868819968000000000000000000000), (26533641483382675589756785448271557519039480357647/148193534596688075417233250734080000000000000000000000), (1167877043687643279846190279894998296648883956793937/6112983302113383110960871592780800000000000000000000000), (904540929111102155352041581546275871530060128293/4540243094261276820380920672000000000000000000000000), (38127690021779411663630695460498993567142929311003/187285027638277668840712977720000000000000000000000000)]
    reserve := (163225627/1000000000000) }

theorem tilt_043_014_valid : tilt_043_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_014]
  · intro i; fin_cases i <;> norm_num [tilt_043_014]
  · norm_num [tilt_043_014]
  · norm_num [tilt_043_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_014]

def tilt_043_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3689/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (1352673/25000000), (708029/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1023265234667225015305381872036481016976933589/34461467414904052368949655111175000000000000000), (2314942309516836939/3527754492500000000), (-62701065581904502468140507343146949963232433589/17230733707452026184474827555587500000000000000), (2314942309516836939/3527754492500000000), (-17768409418448825702996518973465345558498276227/4923066773557721766992807873025000000000000000)]
    bernstein := [(131079176370309974278349273590770848856478918992011/1411541705314469985032177873353728000000000000000000000), (17381615052523115704898977884733198736630086567087/160402466513007952844565667426560000000000000000000000), (794513675606021197586675934430337186185395040184177/6616601743661578054838333781345600000000000000000000000), (1887219505974715176242819277407961683800744802959/14742873760386760371743167962000000000000000000000000), (26788796417851504815755921688962715326142903149563/202714514205317955111468559477500000000000000000000000)]
    reserve := (46431209/500000000000) }

theorem tilt_043_015_valid : tilt_043_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_015]
  · intro i; fin_cases i <;> norm_num [tilt_043_015]
  · norm_num [tilt_043_015]
  · norm_num [tilt_043_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_015]

def tilt_043_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4371/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (959/25000000), (1352673/25000000), (21891/3125000)]
    alternative := (.spike 3 true true)
    polynomial := [(-163496261209223449008229381375932127301747558467/5449612923533157437577057038715600000000000000000), (2313380897797580081/3490301040000000000), (-10011261908930836287725942648200485582073991558467/2724806461766578718788528519357800000000000000000), (2313380897797580081/3490301040000000000), (-19859027556652449126443655915025039036846235558467/5449612923533157437577057038715600000000000000000)]
    bernstein := [(21034697016886963474159484781875505395132787745298333/223216145347918128643156256305790976000000000000000000000), (2791248900650046316845925882716514417595713641150361/25365471062263423709449574580203520000000000000000000000), (127680563406569668742410494028875784029100543963738631/1046325681318366228014794951433395200000000000000000000000), (303525572748985650153216103280983396653616261707577/2331385207928623502706762369504000000000000000000000000), (4312546113892596593188643438803026169539941210844589/32056546609018573162217982580680000000000000000000000000)]
    reserve := (94234657/1000000000000) }

theorem tilt_043_016_valid : tilt_043_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_016]
  · intro i; fin_cases i <;> norm_num [tilt_043_016]
  · norm_num [tilt_043_016]
  · norm_num [tilt_043_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_016]

def tilt_043_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (5407991/100000000), (708029/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-11434914640635742113778397310899362204940683943/385775760848678333203563285453430000000000000000), (2314942309516836939/3527754492500000000), (-701881437708248535244430663223341832031692483943/192887880424339166601781642726715000000000000000), (2314942309516836939/3527754492500000000), (-1392327960775861328375082929135784301858444283943/385775760848678333203563285453430000000000000000)]
    bernstein := [(2296438769765095568972488815763245230406723199923257/15801375164361864528017952172172492800000000000000000000), (288811549150732218713883316717610304026043920217669/1795610814132030060002040019565056000000000000000000000), (12782141822439040362776590499697917486236717577881499/74068946082946239975084150807058560000000000000000000000), (506453688222875435135146510242338439311401647262261/2805641897081296968753187530570400000000000000000000000), (7123956758249285709835506044165080157420404365389977/38577576084867833320356328545343000000000000000000000000)]
    reserve := (18166447/125000000000) }

theorem tilt_043_017_valid : tilt_043_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_017]
  · intro i; fin_cases i <;> norm_num [tilt_043_017]
  · norm_num [tilt_043_017]
  · norm_num [tilt_043_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_017]

def tilt_043_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (1082679/20000000), (21891/3125000)]
    alternative := (.spike 4 false true)
    polynomial := [(-952794403320683133824037757047264026869422709/31838454698507203702921206212400000000000000000), (2313380897797580081/3490301040000000000), (-58486722932913128570421645766572241877345422709/15919227349253601851460603106200000000000000000), (2313380897797580081/3490301040000000000), (-38673550487501858002339751258699073242607140903/10612818232835734567640402070800000000000000000)]
    bernstein := [(74308189195046717966957245344278865011215293450297/434701034816951687890550868819968000000000000000000000), (27677244178373496343017467670664015477527673100047/148193534596688075417233250734080000000000000000000000), (1215060992446740437503790391962454571768855900704337/6112983302113383110960871592780800000000000000000000000), (939593205853209805462321447048872014052595833893/4540243094261276820380920672000000000000000000000000), (39573919224387272048740100607013338912721438648603/187285027638277668840712977720000000000000000000000000)]
    reserve := (170940907/1000000000000) }

theorem tilt_043_018_valid : tilt_043_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_018]
  · intro i; fin_cases i <;> norm_num [tilt_043_018]
  · norm_num [tilt_043_018]
  · norm_num [tilt_043_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_018]

def tilt_043_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (1352673/25000000), (704271/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-594090018711101895359830240467535329258271763/19995824655997287665421401981606250000000000000), (164294940911/249125000000), (-36556835065251138968033924816145193457052245513/9997912327998643832710700990803125000000000000), (164294940911/249125000000), (-72519580111791176040708019391822851584846219263/19995824655997287665421401981606250000000000000)]
    bernstein := [(187586745917395684819406924168942064909912429315937/819028977909648902775660625166592000000000000000000000), (22773178354613262430476494392011238073412552145229/93071474762460102588143252859840000000000000000000000), (984877652906115757031231682397789039131716741718259/3839198333951479231760909180468400000000000000000000000), (2263270638786431102215086199477003341850126671053/8554363489196700605527872505500000000000000000000000), (31618215270810409390715807697431834518244995550321/117622497976454633326008246950625000000000000000000000)]
    reserve := (114517771/500000000000) }

theorem tilt_043_019_valid : tilt_043_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_019]
  · intro i; fin_cases i <;> norm_num [tilt_043_019]
  · norm_num [tilt_043_019]
  · norm_num [tilt_043_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_019]

def tilt_043_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/80), (9/100)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
    cone := fun i => (![![0, 0, 0, (2089/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2675573/50000000), (1/100000000), (835067/20000000), (4509307/100000000), (1/100000000), (1352673/25000000), (704271/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-596971711382570040792491899496121959127271763/19995824655997287665421401981606250000000000000), (164294940911/249125000000), (-36553732317138432800106338910283988011560995513/9997912327998643832710700990803125000000000000), (164294940911/249125000000), (-72510492922894295559420185921071854063994719263/19995824655997287665421401981606250000000000000)]
    bernstein := [(71520476050891166457339338677454905935348880815937/819028977909648902775660625166592000000000000000000000), (9587059506629586851337850028502460828749877645229/93071474762460102588143252859840000000000000000000000), (441084812534495524131078195732017981108232052218259/3839198333951479231760909180468400000000000000000000000), (1051913795447006658870347587738674519212280171053/8554363489196700605527872505500000000000000000000000), (14966262673288167132730674758495783314135095050321/117622497976454633326008246950625000000000000000000000)]
    reserve := (43661749/500000000000) }

theorem tilt_043_020_valid : tilt_043_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_043_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_043_020]
  · intro i; fin_cases i <;> norm_num [tilt_043_020]
  · norm_num [tilt_043_020]
  · norm_num [tilt_043_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_043_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_043_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_043_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_043_020]

def tiltBundle043_row : Alternative → Row
  | .zero => tilt_043_000
  | (.spike 0 false false) => tilt_043_001
  | (.spike 0 false true) => tilt_043_002
  | (.spike 0 true false) => tilt_043_003
  | (.spike 0 true true) => tilt_043_004
  | (.spike 1 false false) => tilt_043_005
  | (.spike 1 false true) => tilt_043_006
  | (.spike 1 true false) => tilt_043_007
  | (.spike 1 true true) => tilt_043_008
  | (.spike 2 false false) => tilt_043_009
  | (.spike 2 false true) => tilt_043_010
  | (.spike 2 true false) => tilt_043_011
  | (.spike 2 true true) => tilt_043_012
  | (.spike 3 false false) => tilt_043_013
  | (.spike 3 false true) => tilt_043_014
  | (.spike 3 true false) => tilt_043_015
  | (.spike 3 true true) => tilt_043_016
  | (.spike 4 false false) => tilt_043_017
  | (.spike 4 false true) => tilt_043_018
  | (.spike 4 true false) => tilt_043_019
  | (.spike 4 true true) => tilt_043_020

def tiltBundle043 : TiltBundle where
  interval := ⟨(7/80), (9/100)⟩
  lambda := ![(3746279/25000000), (3746279/25000000), (5018213/50000000), (3689017/25000000), (3689017/25000000), (775849/5000000), (7482113/50000000)]
  row := tiltBundle043_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_043_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_043_001_valid | exact tilt_043_002_valid | exact tilt_043_003_valid | exact tilt_043_004_valid | exact tilt_043_005_valid | exact tilt_043_006_valid | exact tilt_043_007_valid | exact tilt_043_008_valid | exact tilt_043_009_valid | exact tilt_043_010_valid | exact tilt_043_011_valid | exact tilt_043_012_valid | exact tilt_043_013_valid | exact tilt_043_014_valid | exact tilt_043_015_valid | exact tilt_043_016_valid | exact tilt_043_017_valid | exact tilt_043_018_valid | exact tilt_043_019_valid | exact tilt_043_020_valid
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
