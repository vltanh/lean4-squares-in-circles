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

def tilt_038_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2751297/50000000), (206087/50000000)]
    alternative := .zero
    polynomial := [(-27061151472600971103839127231118281727758463/1702001997685501312494177025237500000000000000), (27045132128059/42136980000000), (-5518579724711770831521962986681742505634008463/851000998842750656247088512618750000000000000), (27045132128059/42136980000000), (-11010098297950940691940086846132366729540258463/1702001997685501312494177025237500000000000000)]
    bernstein := [(3476334007821748289090777241135279540354631867006177/285548551476011555879983066946469888000000000000000000000), (7696011138343593596797336839587857052867875249027/424923439696445767678546230575104000000000000000000000), (17911789694120148714307950112575547751513498995571/836568021902377605117137891444736000000000000000000000), (9159170491962342546791503574993543627358721907/414964296578560319998580303296000000000000000000000), (1824033838132769326976542632181784644799630379/90773439876560069999689441346000000000000000000000)]
    reserve := (1217423/100000000000) }

theorem tilt_038_000_valid : tilt_038_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_000]
  · intro i; fin_cases i <;> norm_num [tilt_038_000]
  · norm_num [tilt_038_000]
  · norm_num [tilt_038_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_000]

def tilt_038_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(59/400000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2751297/50000000), (416097/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-25225488829601211997296487547619798155738221/1603654597853207068656838145602500000000000000), (1238494145387699825267/1948118996340000000000), (-5153125501942146327952320703507586634486113221/801827298926603534328419072801250000000000000), (1238494145387699825267/1948118996340000000000), (-10281025515054691443907344919467553470816488221/1603654597853207068656838145602500000000000000)]
    bernstein := [(5974133336340844378834853577855541800319024166178659/269048595775763912835826034458125926400000000000000000000), (11190586604467357828932116726908823556784133914609/400369934190124870291407789372211200000000000000000000), (24500024651729825859942744436884836384245837943657/788228307936808338386209085326540800000000000000000000), (12354940351353828256735746417437867849526359569/390986263857543818643952919308800000000000000000000), (7569526925167888233265604508347560928405074979/256584735656513130985094103296400000000000000000000)]
    reserve := (11102331/500000000000) }

theorem tilt_038_001_valid : tilt_038_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_001]
  · intro i; fin_cases i <;> norm_num [tilt_038_001]
  · norm_num [tilt_038_001]
  · norm_num [tilt_038_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_001]

def tilt_038_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4369/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (767/20000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2751297/50000000), (408253/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-116177268394449833425150495130439699449912115037/7240894974183796853936599831740045000000000000000), (11148207361276138222597/17202548495940000000000), (-23691949707955086459875467260621192996935635365037/3620447487091898426968299915870022500000000000000), (11148207361276138222597/17202548495940000000000), (-47267722147515723086325784026111946294421358615037/7240894974183796853936599831740045000000000000000)]
    bernstein := [(36439680549203779228375068307239747973785823475736200323/1214820590151959835186147856826663908147200000000000000000000), (5024383752056364552244325900589547099019921673079421/139059133488090640474604837090964275200000000000000000000), (140955283716563571642666936020881447684270476228003929/3559044697710819829646917549296866918400000000000000000000), (5488483269889816569436510130693497984443138647661/135799935046963516088481286221644800000000000000000000), (14892713474156680314570249084959867699640996145121/386181065289802498876618657692802400000000000000000000)]
    reserve := (5999187/200000000000) }

theorem tilt_038_002_valid : tilt_038_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_002]
  · intro i; fin_cases i <;> norm_num [tilt_038_002]
  · norm_num [tilt_038_002]
  · norm_num [tilt_038_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_002]

def tilt_038_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(21801/400000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2751297/50000000), (416097/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-670069678136952598247952137407031809234999/42742791405781641079739088255000000000000000), (1238494145387699825267/1948118996340000000000), (-137345860651822358377649492866151473827484999/21371395702890820539869544127500000000000000), (1238494145387699825267/1948118996340000000000), (-274021651625507764157051033594895915845734999/42742791405781641079739088255000000000000000)]
    bernstein := [(542618562224855075355296083120591731774565255399721/7171050438577422412292559072971980800000000000000000000), (66832879648101281031102277554275353191473301367/820862000752910074667188538572800000000000000000000), (1776385097181647398479947501108468917050405399083/21008936831769792223513356659097600000000000000000000), (68198028113727068320785036918695816388723847/801623047610263744792176307200000000000000000000), (567492686291270403873437776969738616571425801/6838846624925062572758254120800000000000000000000)]
    reserve := (18916983/250000000000) }

theorem tilt_038_003_valid : tilt_038_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_003]
  · intro i; fin_cases i <;> norm_num [tilt_038_003]
  · norm_num [tilt_038_003]
  · norm_num [tilt_038_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_003]

def tilt_038_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5455691/100000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2751297/50000000), (408253/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-887755690961046101021750717451335127449726869/55560304764505620041910044404650000000000000000), (11148207361276138222597/17202548495940000000000), (-181787645341448924269375224445317933028852226869/27780152382252810020955022202325000000000000000), (11148207361276138222597/17202548495940000000000), (-362687534991936802437728698173184530930254726869/55560304764505620041910044404650000000000000000)]
    bernstein := [(901124042771921892972685965662470232792428277727681451/9321472340599399206570538675464044544000000000000000000000), (1426132979678034781320402811366279793316424450696001/13871238602082439295491873028964352000000000000000000000), (2902697013202646635887912786428673589751059526093873/27309000997849802362999625025773568000000000000000000000), (1450887356615803927948563477966072011273677599441/13546131447346132124503782254848000000000000000000000), (311909491414820352651871148051839501235438245977/2963216254106966402235202368248000000000000000000000)]
    reserve := (96671857/1000000000000) }

theorem tilt_038_004_valid : tilt_038_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_004]
  · intro i; fin_cases i <;> norm_num [tilt_038_004]
  · norm_num [tilt_038_004]
  · norm_num [tilt_038_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_004]

def tilt_038_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (1096877/25000000), (1/100000000), (2751297/50000000), (416097/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-504410051323984357192446464071364702849395721/32058558770254217462221419076200000000000000000), (1238494145387699825267/1948118996340000000000), (-103015938505410621603389887253838767091479395721/16029279385127108731110709538100000000000000000), (1238494145387699825267/1948118996340000000000), (-205527466959497258849587328043606169480109395721/32058558770254217462221419076200000000000000000)]
    bernstein := [(97704170144445308456683823020387865105400681594871159/5378533651372493812746605876679278592000000000000000000000), (1339659759366816370503640938151617392458846711249763/56026392201796810549443811215409152000000000000000000000), (426123223835832728051982643544917819278785635371157/15757422806755352967031071904333824000000000000000000000), (1507865704758279294413557438471190773371165014483/54713273634567197802191221890048000000000000000000000), (130597620459929792691341777218247630359258667479/5129369403240674793955427052192000000000000000000000)]
    reserve := (18165577/1000000000000) }

theorem tilt_038_005_valid : tilt_038_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_005]
  · intro i; fin_cases i <;> norm_num [tilt_038_005]
  · norm_num [tilt_038_005]
  · norm_num [tilt_038_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_005]

def tilt_038_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (2195743/50000000), (1/100000000), (2751297/50000000), (408253/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-12070539312917816597775866098594593589122433/755585504025956569227470983130400000000000000), (11148207361276138222597/17202548495940000000000), (-2472196250990519062148033265293844264777162433/377792752012978284613735491565200000000000000), (11148207361276138222597/17202548495940000000000), (-4932321962668120307698290664489093935965202433/755585504025956569227470983130400000000000000)]
    bernstein := [(12656671714615880646945251378077922849343426129223807/126766212075123429685482338177110769664000000000000000000), (139948895041546990354325901673124329261706341457099/1320481375782535725890441022678237184000000000000000000), (40652626225143377954345926481581288952873534566061/371385386938838172906686537628254208000000000000000000), (142207892263177233113761677656582533889877817659/1289532593537632544814883811209216000000000000000000), (4369589202906310344237022900022962242321990389/40297893548051017025465119100288000000000000000000)]
    reserve := (99842627/1000000000000) }

theorem tilt_038_006_valid : tilt_038_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_006]
  · intro i; fin_cases i <;> norm_num [tilt_038_006]
  · norm_num [tilt_038_006]
  · norm_num [tilt_038_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_006]

def tilt_038_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (4211621/100000000), (4389497/100000000), (1/100000000), (2751297/50000000), (416097/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-378296851062608530627218430695363441652342343/24042961957875677638870588237293750000000000000), (7429184768361268770229/11682952421580000000000), (-77262812943086656798314562820015564798988592343/12021480978937838819435294118646875000000000000), (7429184768361268770229/11682952421580000000000), (-154147329035110705066001907209335766156324842343/24042961957875677638870588237293750000000000000)]
    bernstein := [(100997480275645132346155012899831031102711181766108697/4033739660470631448937018549041364992000000000000000000000), (185088467473641121891127032463355433845553056255047/6002588780462249179965801412263936000000000000000000000), (402000002982290344500854241705217260298977532888531/11817596661535053073057671530394624000000000000000000000), (202730888092086715783813949368368053742435511727/5861903105920165214810352941664000000000000000000000), (125163423807686169513966749907781319607507653257/3846873913260108422219294117967000000000000000000000)]
    reserve := (1001527/40000000000) }

theorem tilt_038_007_valid : tilt_038_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_007]
  · intro i; fin_cases i <;> norm_num [tilt_038_007]
  · norm_num [tilt_038_007]
  · norm_num [tilt_038_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_007]

def tilt_038_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (168631/4000000), (4389497/100000000), (1/100000000), (2751297/50000000), (408253/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-90531623390422577546465556439604881838417227/5667116658624700301463727954237500000000000000), (892074529848498944043/1376882232860000000000), (-18541282792063091473625283570082552332174167227/2833558329312350150731863977118750000000000000), (892074529848498944043/1376882232860000000000), (-36992033960735760369704101583725499782509917227/5667116658624700301463727954237500000000000000)]
    bernstein := [(88399614708593582489083336043720846663125644875861333/950784402789448598929220800534806528000000000000000000000), (140163123540186440733786766874289433070665654538983/1414857742246203272216102381748224000000000000000000000), (285495099746468636890491030807989512452847748912159/2785501180047212692175451564066816000000000000000000000), (142672846490727837384424580824409373633304670503/1381697013912307883023537482176000000000000000000000), (91909010061752416849638714151059854545637481173/906738665379952048234196472678000000000000000000000)]
    reserve := (92975457/1000000000000) }

theorem tilt_038_008_valid : tilt_038_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_008]
  · intro i; fin_cases i <;> norm_num [tilt_038_008]
  · norm_num [tilt_038_008]
  · norm_num [tilt_038_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_008]

def tilt_038_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4387509/100000000), (1/100000000), (2751297/50000000), (416097/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-56045832760111705983547291408166835813196969/3562062897448324029734054962650000000000000000), (1238494145387699825267/1948118996340000000000), (-11446218257037330059581648669787966583610696969/1781031448724162014867027481325000000000000000), (1238494145387699825267/1948118996340000000000), (-22836390681314548413179750048167766331408196969/3562062897448324029734054962650000000000000000)]
    bernstein := [(10812410101393789788340558647487430261998011062339351/597614986360763810848386626642509824000000000000000000000), (21199542836369984566895220985973765119262475048901/889308015417803289952956289646592000000000000000000000), (47219248847662241573454004920168711205931267675573/1750825155353800227094882695241728000000000000000000000), (23870990515747747967068576835419044975439928341/868464858806448525344683876608000000000000000000000), (14469246304366723940680926007239749893669187831/569930063591731844757448794024000000000000000000000)]
    reserve := (9046301/500000000000) }

theorem tilt_038_009_valid : tilt_038_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_009]
  · intro i; fin_cases i <;> norm_num [tilt_038_009]
  · norm_num [tilt_038_009]
  · norm_num [tilt_038_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_009]

def tilt_038_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4391487/100000000), (1/100000000), (2751297/50000000), (408253/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-501268349408648094314727652900251053647510891/31482736503452703104816900866950000000000000000), (11148207361276138222597/17202548495940000000000), (-103006529677786768668779377500542459491905010891/15741368251726351552408450433475000000000000000), (11148207361276138222597/17202548495940000000000), (-205511791006164889243244027348184667930162510891/31482736503452703104816900866950000000000000000)]
    bernstein := [(809009436715686526724362173165851080301189709632053589/5281926705895107457733837862954074112000000000000000000000), (8765260094406705829400995936137572443215706112297273/55020069853074036018060811072438272000000000000000000000), (2519125702586541899251779487960880188063711428132047/15474394646177072630079603114123264000000000000000000000), (8791057764889425681866210123329273874065871096393/53730536965892613298887510812928000000000000000000000), (814881673055858712056913672998533745021036216309/5037237840552432496770704138712000000000000000000000)]
    reserve := (153165593/1000000000000) }

theorem tilt_038_010_valid : tilt_038_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_010]
  · intro i; fin_cases i <;> norm_num [tilt_038_010]
  · norm_num [tilt_038_010]
  · norm_num [tilt_038_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_010]

def tilt_038_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(293/2000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2751297/50000000), (416097/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-100908902059193076455004722574497889071566009/6414618391412828274627352582410000000000000000), (1238494145387699825267/1948118996340000000000), (-20612508954509373540275101586414365234393066009/3207309195706414137313676291205000000000000000), (1238494145387699825267/1948118996340000000000), (-41124109006959554004095198450254232579714566009/6414618391412828274627352582410000000000000000)]
    bernstein := [(22725588392879563940306833935919542700953770430901511/1076194383103055651343304137832503705600000000000000000000), (43019737241723596484010630558269174284675022439061/1601479736760499481165631157488844800000000000000000000), (94569074968070625835053359233061221229361226885253/3152913231747233353544836341306163200000000000000000000), (47717733498150668388219745088946635826955068901/1563945055430175274575811677235200000000000000000000), (29161064835183627400937999910799836080181186791/1026338942626052523940376413185600000000000000000000)]
    reserve := (1055831/50000000000) }

theorem tilt_038_011_valid : tilt_038_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_011]
  · intro i; fin_cases i <;> norm_num [tilt_038_011]
  · norm_num [tilt_038_011]
  · norm_num [tilt_038_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_011]

def tilt_038_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4339/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (3809/100000000), (2751297/50000000), (408253/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-5769160806644159422460208417659904862973814139123/359590208039974996305665042491497150000000000000000), (11148207361276138222597/17202548495940000000000), (-1176565995517028317312281024059827822856756341639123/179795104019987498152832521245748575000000000000000), (11148207361276138222597/17202548495940000000000), (-2347362830227412475202101839701995740850538869139123/359590208039974996305665042491497150000000000000000)]
    bernstein := [(1863653191449302312833066730546628187504719062678803610317/60329225917715971476193444415290258489344000000000000000000000), (255700264574245484471790032208786054038182485721033859/6905817985086535196450714791127547904000000000000000000000), (7158273163690017182176210288851701641202148953380260791/176745779055808510184160481685420679168000000000000000000000), (278603901775009966594423530880471430661757772448819/6743962876061069527783901163210496000000000000000000000), (756765570547141237659314157196157246534130903294159/19178144428798666469635468932879848000000000000000000000)]
    reserve := (15445691/500000000000) }

theorem tilt_038_012_valid : tilt_038_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_012]
  · intro i; fin_cases i <;> norm_num [tilt_038_012]
  · norm_num [tilt_038_012]
  · norm_num [tilt_038_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_012]

def tilt_038_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (343741/6250000), (416097/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-3015041076932507347223884067471186012994006967/192342797493630415381430428255200000000000000000), (1238494145387699825267/1948118996340000000000), (-618056855636039210794854634167356135502474006967/96171398746815207690715214127600000000000000000), (1238494145387699825267/1948118996340000000000), (-1233098670195145914242485384267241084991954006967/192342797493630415381430428255200000000000000000)]
    bernstein := [(2488339021341034701754068025493588341795712883713998793/32269766595948961030239806838099935232000000000000000000000), (3979008034072301237968652379756261484111116374744443/48020486005876430104523522080505856000000000000000000000), (8130147716828460188282863807837348066326655188253739/94540331824069221768280684095995904000000000000000000000), (4057255954384450484678485765898214807397799008363/46895005865113701273948752031744000000000000000000000), (2598129767033202111854361021822926002842925699433/30774847598980866461028868520832000000000000000000000)]
    reserve := (9638817/125000000000) }

theorem tilt_038_013_valid : tilt_038_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_013]
  · intro i; fin_cases i <;> norm_num [tilt_038_013]
  · norm_num [tilt_038_013]
  · norm_num [tilt_038_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_013]

def tilt_038_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2752667/50000000), (408253/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-9056473865022291934094212027667361357324221033/566714515453756780979089576679100000000000000000), (11148207361276138222597/17202548495940000000000), (-1854233417070123652516699702432095139040859221033/283357257726878390489544788339550000000000000000), (11148207361276138222597/17202548495940000000000), (-3699410360275225013099305192836522916724394221033/566714515453756780979089576679100000000000000000)]
    bernstein := [(2986545165005682461352811533513302668069800763553871069/31692972787010051753169591037646077952000000000000000000000), (14201544701917773536858344450285531922471677410467557/141486485656294873898078531418062848000000000000000000000), (28928214919259560839377186777615502017311785646822261/278551518635830532986842108729311232000000000000000000000), (14462073238628744724931563922134033911668885483637/138170396148725462791092315837952000000000000000000000), (9323271697891683968599445854575018678371963672567/90674322472601084956654332268656000000000000000000000)]
    reserve := (9423367/100000000000) }

theorem tilt_038_014_valid : tilt_038_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_014]
  · intro i; fin_cases i <;> norm_num [tilt_038_014]
  · norm_num [tilt_038_014]
  · norm_num [tilt_038_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_014]

def tilt_038_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(293/2000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2751297/50000000), (416097/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-100908902059193076455004722574497889071566009/6414618391412828274627352582410000000000000000), (1238494145387699825267/1948118996340000000000), (-20612508954509373540275101586414365234393066009/3207309195706414137313676291205000000000000000), (1238494145387699825267/1948118996340000000000), (-41124109006959554004095198450254232579714566009/6414618391412828274627352582410000000000000000)]
    bernstein := [(22725588392879563940306833935919542700953770430901511/1076194383103055651343304137832503705600000000000000000000), (43019737241723596484010630558269174284675022439061/1601479736760499481165631157488844800000000000000000000), (94569074968070625835053359233061221229361226885253/3152913231747233353544836341306163200000000000000000000), (47717733498150668388219745088946635826955068901/1563945055430175274575811677235200000000000000000000), (29161064835183627400937999910799836080181186791/1026338942626052523940376413185600000000000000000000)]
    reserve := (1055831/50000000000) }

theorem tilt_038_015_valid : tilt_038_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_015]
  · intro i; fin_cases i <;> norm_num [tilt_038_015]
  · norm_num [tilt_038_015]
  · norm_num [tilt_038_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_015]

def tilt_038_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4339/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (3809/100000000), (2751297/50000000), (408253/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-5769160806644159422460208417659904862973814139123/359590208039974996305665042491497150000000000000000), (11148207361276138222597/17202548495940000000000), (-1176565995517028317312281024059827822856756341639123/179795104019987498152832521245748575000000000000000), (11148207361276138222597/17202548495940000000000), (-2347362830227412475202101839701995740850538869139123/359590208039974996305665042491497150000000000000000)]
    bernstein := [(1863653191449302312833066730546628187504719062678803610317/60329225917715971476193444415290258489344000000000000000000000), (255700264574245484471790032208786054038182485721033859/6905817985086535196450714791127547904000000000000000000000), (7158273163690017182176210288851701641202148953380260791/176745779055808510184160481685420679168000000000000000000000), (278603901775009966594423530880471430661757772448819/6743962876061069527783901163210496000000000000000000000), (756765570547141237659314157196157246534130903294159/19178144428798666469635468932879848000000000000000000000)]
    reserve := (15445691/500000000000) }

theorem tilt_038_016_valid : tilt_038_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_016]
  · intro i; fin_cases i <;> norm_num [tilt_038_016]
  · norm_num [tilt_038_016]
  · norm_num [tilt_038_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_016]

def tilt_038_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (343741/6250000), (416097/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-3015045009581082311821642225353267499364439967/192342797493630415381430428255200000000000000000), (1238494145387699825267/1948118996340000000000), (-618056859568687785759452392325238216988844439967/96171398746815207690715214127600000000000000000), (1238494145387699825267/1948118996340000000000), (-1233098674127794489207083142425123166478324439967/192342797493630415381430428255200000000000000000)]
    bernstein := [(2487676132780898605495227806681568550998327006009805793/32269766595948961030239806838099935232000000000000000000000), (3978021518279902167394118087180629380289265854901443/48020486005876430104523522080505856000000000000000000000), (8128205365640281041869656983318669409260946010314739/94540331824069221768280684095995904000000000000000000000), (4056292412224449833617161745051547750291639245363/46895005865113701273948752031744000000000000000000000), (2597497393209699229570251476226340912990928866433/30774847598980866461028868520832000000000000000000000)]
    reserve := (38544997/500000000000) }

theorem tilt_038_017_valid : tilt_038_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_017]
  · intro i; fin_cases i <;> norm_num [tilt_038_017]
  · norm_num [tilt_038_017]
  · norm_num [tilt_038_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_017]

def tilt_038_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2752667/50000000), (408253/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-9048199020255601611060780670845787596758372033/566714515453756780979089576679100000000000000000), (11148207361276138222597/17202548495940000000000), (-1854225142225356962193666271075273565280293372033/283357257726878390489544788339550000000000000000), (11148207361276138222597/17202548495940000000000), (-3699402085430458322776271761479701342963828372033/566714515453756780979089576679100000000000000000)]
    bernstein := [(3451482032884894461975080059853855919726540030734914069/31692972787010051753169591037646077952000000000000000000000), (16277312441236889568679725947267062341305427028046557/141486485656294873898078531418062848000000000000000000000), (33015194535719093782177879412020684846448997108289261/278551518635830532986842108729311232000000000000000000000), (16489501229760307461675614088344642561668114822637/138170396148725462791092315837952000000000000000000000), (10653875011220254602698241462840900951121048721567/90674322472601084956654332268656000000000000000000000)]
    reserve := (108903701/1000000000000) }

theorem tilt_038_018_valid : tilt_038_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_018]
  · intro i; fin_cases i <;> norm_num [tilt_038_018]
  · norm_num [tilt_038_018]
  · norm_num [tilt_038_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_018]

def tilt_038_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2751297/50000000), (206087/50000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-3827576353113574726835397299155704241955209/243143142526500187499168146462500000000000000), (27045132128059/42136980000000), (-3153477123727359409265968935983587951136835211/486286285053000374998336292925000000000000000), (27045132128059/42136980000000), (-3145821971021132259812298141385276542652924793/486286285053000374998336292925000000000000000)]
    bernstein := [(13844148128613246088922689892568529643850711848362247/81585300421717587394280876270419968000000000000000000000), (149255443657975061944118544477743140707199991440179/849846879392891535357092461150208000000000000000000000), (42766677978300815471280225747388149457029460245181/239019434829250744319182254698496000000000000000000000), (149043894685564224032672316957477161067015170939/829928593157120639997160606592000000000000000000000), (4606319008937186720700564965784423917315370269/25935268536160019999911268956000000000000000000000)]
    reserve := (84844623/500000000000) }

theorem tilt_038_019_valid : tilt_038_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_019]
  · intro i; fin_cases i <;> norm_num [tilt_038_019]
  · norm_num [tilt_038_019]
  · norm_num [tilt_038_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_019]

def tilt_038_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(31/640), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(545297/10000000), (1/100000000), (2106849/50000000), (4389497/100000000), (1/100000000), (2751297/50000000), (206087/50000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-3865005854671301245734054868464089319830209/243143142526500187499168146462500000000000000), (27045132128059/42136980000000), (-3153320420782735807501467889603576642993335211/486286285053000374998336292925000000000000000), (27045132128059/42136980000000), (-3145590409073393205009999779866648464353674793/486286285053000374998336292925000000000000000)]
    bernstein := [(1346787623407730497448343353221412486405867107612247/81585300421717587394280876270419968000000000000000000000), (19085040209134393460678262961058766590296043690179/849846879392891535357092461150208000000000000000000000), (6159218885957530288953860810772950728177297995181/239019434829250744319182254698496000000000000000000000), (21945074542736803835782624916596079598807420939/829928593157120639997160606592000000000000000000000), (634809756045417958377996544064399389215120269/25935268536160019999911268956000000000000000000000)]
    reserve := (4126931/250000000000) }

theorem tilt_038_020_valid : tilt_038_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_038_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_038_020]
  · intro i; fin_cases i <;> norm_num [tilt_038_020]
  · norm_num [tilt_038_020]
  · norm_num [tilt_038_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_038_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_038_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_038_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_038_020]

def tiltBundle038_row : Alternative → Row
  | .zero => tilt_038_000
  | (.spike 0 false false) => tilt_038_001
  | (.spike 0 false true) => tilt_038_002
  | (.spike 0 true false) => tilt_038_003
  | (.spike 0 true true) => tilt_038_004
  | (.spike 1 false false) => tilt_038_005
  | (.spike 1 false true) => tilt_038_006
  | (.spike 1 true false) => tilt_038_007
  | (.spike 1 true true) => tilt_038_008
  | (.spike 2 false false) => tilt_038_009
  | (.spike 2 false true) => tilt_038_010
  | (.spike 2 true false) => tilt_038_011
  | (.spike 2 true true) => tilt_038_012
  | (.spike 3 false false) => tilt_038_013
  | (.spike 3 false true) => tilt_038_014
  | (.spike 3 true false) => tilt_038_015
  | (.spike 3 true true) => tilt_038_016
  | (.spike 4 false false) => tilt_038_017
  | (.spike 4 false true) => tilt_038_018
  | (.spike 4 true false) => tilt_038_019
  | (.spike 4 true true) => tilt_038_020

def tiltBundle038 : TiltBundle where
  interval := ⟨(31/640), (1/20)⟩
  lambda := ![(1474961/10000000), (1474961/10000000), (1867081/20000000), (586001/4000000), (586001/4000000), (16112211/100000000), (3150623/20000000)]
  row := tiltBundle038_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_038_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_038_001_valid | exact tilt_038_002_valid | exact tilt_038_003_valid | exact tilt_038_004_valid | exact tilt_038_005_valid | exact tilt_038_006_valid | exact tilt_038_007_valid | exact tilt_038_008_valid | exact tilt_038_009_valid | exact tilt_038_010_valid | exact tilt_038_011_valid | exact tilt_038_012_valid | exact tilt_038_013_valid | exact tilt_038_014_valid | exact tilt_038_015_valid | exact tilt_038_016_valid | exact tilt_038_017_valid | exact tilt_038_018_valid | exact tilt_038_019_valid | exact tilt_038_020_valid
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
