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

def tilt_021_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5597859/100000000), (8113/20000000)]
    alternative := .zero
    polynomial := [(-299708324507838182176771777003537181023369/321241009529328799435390437180000000000000000), (265664988658393/424027700000000), (-11142454882399864111009986414283742955461023369/160620504764664399717695218590000000000000000), (265664988658393/424027700000000), (-3183515722353602911976828008112926053391574767/45891572789904114205055776740000000000000000)]
    bernstein := [(1170492140607611562760016080713663005363190947565431/3368456128082254751967639630564556800000000000000000000), (406970929391089060224268343276828924390383908731699/962416036594929929133611323018444800000000000000000000), (2714099250799926176429981162203669033346086135231691/5774496219569579574801667938110668800000000000000000000), (215996104654145314393895453147575791589977170480017/441764738109148164192477328598630400000000000000000000), (25850132675699155554997503817406534615680602275103911/53895298049316076031482234089032908800000000000000000000)]
    reserve := (69497247/200000000000) }

theorem tilt_021_000_valid : tilt_021_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_000]
  · intro i; fin_cases i <;> norm_num [tilt_021_000]
  · norm_num [tilt_021_000]
  · norm_num [tilt_021_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_000]

def tilt_021_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14497/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (63/1562500), 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5597859/100000000), (44919/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-44147168858373204157729405493391870699059137/56322501588789696884614765994100000000000000000), (167889143508145609147/297607816504687500000), (-196160258220509252565930463337998868606929228793/3129027866043872049145264777450000000000000000), (167889143508145609147/297607816504687500000), (-3530840500800308172982590610678486243054027059137/56322501588789696884614765994100000000000000000)]
    bernstein := [(216669873625921268822909615481887906847306416992563263/590584234259667452004818128670294016000000000000000000000), (56983128730595798054343848331709565915700991126937621/131240940946592767112181806371176448000000000000000000000), (1124454261335254151112133578949597819482001476447232567/2362336937038669808019272514681176064000000000000000000000), (258433962791745992961186661785474541855850187485286589/524963763786371068448727225484705792000000000000000000000), (4564762614515960604690535242995357141731917782857016303/9449347748154679232077090058724704256000000000000000000000)]
    reserve := (73374757/200000000000) }

theorem tilt_021_001_valid : tilt_021_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_001]
  · intro i; fin_cases i <;> norm_num [tilt_021_001]
  · norm_num [tilt_021_001]
  · norm_num [tilt_021_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_001]

def tilt_021_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2147/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (3769/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5597859/100000000), (911/2500000)]
    alternative := (.spike 0 false true)
    polynomial := [(-14149852981395035719577828509778471796865927417/12915690391551670529983369485870300000000000000000), (1358630839955526616067/1931446173500000000000), (-498488075283148144511083057217195478181934653927417/6457845195775835264991684742935150000000000000000), (1358630839955526616067/1931446173500000000000), (-996962000713314893986446536605881177892072441927417/12915690391551670529983369485870300000000000000000)]
    bernstein := [(47244789590202242739603390651496003818122328830853150983/135430829680116844776478416420159356928000000000000000000000), (117871883640174918487409036777848636013750837157480873749/270861659360233689552956832840318713856000000000000000000000), (796481319720683768646178631340776391366971876706407390141/1625169956161402137317740997041912283136000000000000000000000), (556458082338220438981236583816666481837533373025155575741/1083446637440934758211827331361274855424000000000000000000000), (1095796747020654157129004559827804409233383606223281101623/2166893274881869516423654662722549710848000000000000000000000)]
    reserve := (174424057/500000000000) }

theorem tilt_021_002_valid : tilt_021_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_002]
  · intro i; fin_cases i <;> norm_num [tilt_021_002]
  · norm_num [tilt_021_002]
  · norm_num [tilt_021_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_002]

def tilt_021_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (63/1562500), 0, 0]] i.1) i.2
    mu := ![(1117927/20000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5597859/100000000), (44919/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-8153266789675907381443054340285225017691137/11258924872483420717199159556900000000000000000), (167889143508145609147/297607816504687500000), (-117637676443485163358930545128981722388131230379/1876487478747236786199859926150000000000000000), (167889143508145609147/297607816504687500000), (-705817905394121304246201827719550049103769691137/11258924872483420717199159556900000000000000000)]
    bernstein := [(50356963760820841953634531930476516488581540856331263/118058384070891753619578259315359744000000000000000000000), (38869269309083265502806694856122031894782648310180863/78705589380594502413052172876906496000000000000000000000), (252957589017420801519525700266701884396488883176344567/472233536283567014478313037261438976000000000000000000000), (173769117121633407199568769296964026097789895764171767/314822357522378009652208691507625984000000000000000000000), (1025214402182057159211019605824554479363004782414224303/1888934145134268057913252149045755904000000000000000000000)]
    reserve := (85308577/200000000000) }

theorem tilt_021_003_valid : tilt_021_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_003]
  · intro i; fin_cases i <;> norm_num [tilt_021_003]
  · norm_num [tilt_021_003]
  · norm_num [tilt_021_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_003]

def tilt_021_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5595171/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5597859/100000000), (911/2500000)]
    alternative := (.spike 0 true true)
    polynomial := [(-1185889725347435690997896250313834993537567/1142839223950062253320998505300000000000000000), (1358630839955526616067/1931446173500000000000), (-44108433495365192235226857227794253137381537567/571419611975031126660499252650000000000000000), (1358630839955526616067/1931446173500000000000), (-88215681101005037034762716559338192439769537567/1142839223950062253320998505300000000000000000)]
    bernstein := [(4874121374794984307304200443815369260743152902820833/11983537820926604773383193286934528000000000000000000000), (11817222522762822621540828719765578173087679773243299/23967075641853209546766386573869056000000000000000000000), (78800631412393910196395936053703046397993325657596091/143802453851119257280598319443214336000000000000000000000), (54787539646604147241957618126454940964304642817301691/95868302567412838187065546295476224000000000000000000000), (108060356389691370331895733750751190559213403806759473/191736605134825676374131092590952448000000000000000000000)]
    reserve := (406734759/1000000000000) }

theorem tilt_021_004_valid : tilt_021_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_004]
  · intro i; fin_cases i <;> norm_num [tilt_021_004]
  · norm_num [tilt_021_004]
  · norm_num [tilt_021_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_004]

def tilt_021_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (63/1562500), 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (132773/3125000), (1/100000000), (5597859/100000000), (44919/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-2166388277018742743372825664948874869390503/2724090431252504895038610371520000000000000000), (167889143508145609147/297607816504687500000), (-9487477693558518599595689010014958285490021167/151338357291805827502145020640000000000000000), (167889143508145609147/297607816504687500000), (-170772432095776316049979029354604300263950990503/2724090431252504895038610371520000000000000000)]
    bernstein := [(10152601888424944815037863878841760618357770920715097/28564158480410265728200059089269555200000000000000000000), (2683411023490159125016348528812433339713610838992499/6347590773424503495155568686504345600000000000000000000), (53077911250115807067380659779855876826337580579376673/114256633921641062912800236357078220800000000000000000000), (12208871581972964989448098396615313893484239170644491/25390363093698013980622274746017382400000000000000000000), (215549457677208724810913754097244833838258609328770857/457026535686564251651200945428312883200000000000000000000)]
    reserve := (177715753/500000000000) }

theorem tilt_021_005_valid : tilt_021_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_005]
  · intro i; fin_cases i <;> norm_num [tilt_021_005]
  · norm_num [tilt_021_005]
  · norm_num [tilt_021_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_005]

def tilt_021_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850491/20000000), (1/100000000), (5597859/100000000), (911/2500000)]
    alternative := (.spike 1 false true)
    polynomial := [(-703526272277707772175860341358210482749941/685664214073920639246917704860000000000000000), (1358630839955526616067/1931446173500000000000), (-26463534544580375472001707749959510430408349941/342832107036960319623458852430000000000000000), (1358630839955526616067/1931446173500000000000), (-52926365562888473236231239639577662650333949941/685664214073920639246917704860000000000000000)]
    bernstein := [(3007844306958007851163551165772916428939075832373259/7189710389367754082189759792912793600000000000000000000), (7257006108722782875619770719403711014909382197638177/14379420778735508164379519585825587200000000000000000000), (48280148415688416195913474696431477568122964868970793/86276524672413048986277117514953523200000000000000000000), (33538963641164076974590127791658234000773475444919593/57517683114942032657518078343302348800000000000000000000), (66169155445240649742155832899126501497616451280089979/115035366229884065315036156686604697600000000000000000000)]
    reserve := (104588507/250000000000) }

theorem tilt_021_006_valid : tilt_021_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_006]
  · intro i; fin_cases i <;> norm_num [tilt_021_006]
  · norm_num [tilt_021_006]
  · norm_num [tilt_021_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_006]

def tilt_021_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (63/1562500), 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (1059603/25000000), (850119/20000000), (1/100000000), (5597859/100000000), (44919/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-7461854165045386337993939926847326732942217/9382954879439295937195999206600000000000000000), (447609418143140327477/793271785950000000000), (-98037483240505412114771421508295351197211230739/1563825813239882656199333201100000000000000000), (447609418143140327477/793271785950000000000), (-588217437588867427302290535109845259856534442217/9382954879439295937195999206600000000000000000)]
    bernstein := [(35010597864705112895072154787819368909044023889596183/98387412956629391766412320640598016000000000000000000000), (27758832231116923513651018051582189657761059533909783/65591608637752927844274880427065344000000000000000000000), (20336090657498311048012548964068675279340994360712983/43727739091835285229516586951376896000000000000000000000), (126305184478995540117558516581905464788197065106692047/262366434551011711377099521708261376000000000000000000000), (743406585610763038572609775783142489334172257133962823/1574198607306070268262597130249568256000000000000000000000)]
    reserve := (355844277/1000000000000) }

theorem tilt_021_007_valid : tilt_021_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_007]
  · intro i; fin_cases i <;> norm_num [tilt_021_007]
  · norm_num [tilt_021_007]
  · norm_num [tilt_021_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_007]

def tilt_021_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (2121071/50000000), (850119/20000000), (1/100000000), (5597859/100000000), (911/2500000)]
    alternative := (.spike 1 true true)
    polynomial := [(-445276886516713799814732001774648726739/433965665825148863997852438000000000000000), (679490145558247145741/966147840500000000000), (-16749046724292587756559249821780077643941739/216982832912574431998926219000000000000000), (679490145558247145741/966147840500000000000), (-33497648171698658799318684911558380639156739/433965665825148863997852438000000000000000)]
    bernstein := [(1901826306475876668632766133914765915251607576061/4550459820082712952154121180282880000000000000000000), (4588848348612439795458265451717491351044406561783/9100919640165425904308242360565760000000000000000000), (30529208127640438443992357690525560186614741564847/54605517840992555425849454163394560000000000000000000), (21206837442676067160277931548857418188159276720047/36403678560661703617232969442263040000000000000000000), (41834927274620904788166027860293421043370930844941/72807357121323407234465938884526080000000000000000000)]
    reserve := (208970783/500000000000) }

theorem tilt_021_008_valid : tilt_021_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_008]
  · intro i; fin_cases i <;> norm_num [tilt_021_008]
  · norm_num [tilt_021_008]
  · norm_num [tilt_021_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_008]

def tilt_021_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (63/1562500), 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (4248737/100000000), (1/100000000), (5597859/100000000), (44919/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-671648611458817155669611114620689218614943137/844468232445750196287040356792900000000000000000), (167889143508145609147/297607816504687500000), (-2941118784802083584131344496888462800441270104793/46914901802541677571502242044050000000000000000), (167889143508145609147/297607816504687500000), (-52939466477826045697208531332877709718724246943137/844468232445750196287040356792900000000000000000)]
    bernstein := [(3146593362867212698294981510697028445210733482849479263/8854891213050349578218796291644719104000000000000000000000), (831698953783853573517649449557372047749461966248309621/1967753602900077684048621398143270912000000000000000000000), (16451300476809710381403195640503289487633097083341876567/35419564852201398312875185166578876416000000000000000000000), (3784116436309117258260720226274354394731464205433634589/7871014411600310736194485592573083648000000000000000000000), (66808923915231341615412801012513930468234684620691212303/141678259408805593251500740666315505664000000000000000000000)]
    reserve := (355350877/1000000000000) }

theorem tilt_021_009_valid : tilt_021_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_009]
  · intro i; fin_cases i <;> norm_num [tilt_021_009]
  · norm_num [tilt_021_009]
  · norm_num [tilt_021_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_009]

def tilt_021_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (531557/12500000), (1/100000000), (5597859/100000000), (911/2500000)]
    alternative := (.spike 2 false true)
    polynomial := [(-1911900968429734143225491299576542197987447/1977878005712126831547932996400000000000000000), (1358630839955526616067/1931446173500000000000), (-76337019327685453863610650503528744831141987447/988939002856063415773966498200000000000000000), (1358630839955526616067/1931446173500000000000), (-152672126754402477993078075515757913120085987447/1977878005712126831547932996400000000000000000)]
    bernstein := [(9908600117313159639121710385175345343739009686146953/20739554077175991045172053896331264000000000000000000000), (23397936651719487284390301833267775342958318363733659/41479108154351982090344107792662528000000000000000000000), (154055337437611668651029732537117147527711334342505331/248874648926111892542064646755975168000000000000000000000), (106604194624346511031683923912647550978843127387394931/165916432617407928361376431170650112000000000000000000000), (210587075799765023517297830427930997325983256934255193/331832865234815856722752862341300224000000000000000000000)]
    reserve := (477763411/1000000000000) }

theorem tilt_021_010_valid : tilt_021_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_010]
  · intro i; fin_cases i <;> norm_num [tilt_021_010]
  · norm_num [tilt_021_010]
  · norm_num [tilt_021_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_010]

def tilt_021_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14491/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (63/1562500), 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5597859/100000000), (44919/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-44150821308393585358352118312505754850785137/56322501588789696884614765994100000000000000000), (167889143508145609147/297607816504687500000), (-196160258626337032608286088083867659038501642793/3129027866043872049145264777450000000000000000), (167889143508145609147/297607816504687500000), (-3530840504452758193363791233391305356938178785137/56322501588789696884614765994100000000000000000)]
    bernstein := [(216631574163570139820577729579528237621915837596037263/590584234259667452004818128670294016000000000000000000000), (56974617697405043327486170912694596078852971161695621/131240940946592767112181806371176448000000000000000000000), (1124301061865117550475552706351943977017342145552098567/2362336937038669808019272514681176064000000000000000000000), (258399918243409239873683157035273833074671482102108589/524963763786371068448727225484705792000000000000000000000), (4564149808157669847920502539885419010413780572954410303/9449347748154679232077090058724704256000000000000000000000)]
    reserve := (73361787/200000000000) }

theorem tilt_021_011_valid : tilt_021_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_011]
  · intro i; fin_cases i <;> norm_num [tilt_021_011]
  · norm_num [tilt_021_011]
  · norm_num [tilt_021_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_011]

def tilt_021_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4293/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (471/12500000), (5597859/100000000), (911/2500000)]
    alternative := (.spike 2 true true)
    polynomial := [(-2357566302183084908873965466850710617686937261/2152043928334955981116889370423600000000000000000), (1358630839955526616067/1931446173500000000000), (-83059302424393114013677317864669456021831942937261/1076021964167477990558444685211800000000000000000), (1358630839955526616067/1931446173500000000000), (-166116247282484044942445761763872061333046198937261/2152043928334955981116889370423600000000000000000)]
    bernstein := [(7873267343277408748721435573720849451639444922090649939/22565816141977548028556233884812967936000000000000000000000), (19642551467085696123965840522863806658433094820214836217/45131632283955096057112467769625935872000000000000000000000), (132726365195193015084871558575777545377640891267333897153/270789793703730576342674806617755615232000000000000000000000), (92728206519745209006058586999976026396628318120152021953/180526529135820384228449871078503743488000000000000000000000), (182603933934474004872815212499934306123465997269770421059/361053058271640768456899742157007486976000000000000000000000)]
    reserve := (348902397/1000000000000) }

theorem tilt_021_012_valid : tilt_021_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_012]
  · intro i; fin_cases i <;> norm_num [tilt_021_012]
  · norm_num [tilt_021_012]
  · norm_num [tilt_021_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_012]

def tilt_021_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (63/1562500), 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (559509/10000000), (44919/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-407586910077587660163357428136105713704721/562946414717522083250291282910000000000000000), (167889143508145609147/297607816504687500000), (-5881885584307131370284799631445871026240034907/93824402452920347208381880485000000000000000), (167889143508145609147/297607816504687500000), (-35290905918932710634048634431247090051726504721/562946414717522083250291282910000000000000000)]
    bernstein := [(2518651688541666272287484902435928064480066945674479/5902920997588404359662574322686361600000000000000000000), (1943999215576710609385159213904010241967380528471279/3935280665058936239775049548457574400000000000000000000), (1405677141100166548455877677877101227683018061552879/2623520443372624159850033032305049600000000000000000000), (8690599160672708624390090304338028424875235928593511/15741122660235744959100198193830297600000000000000000000), (51273579766300671730557480929834519967571168866768799/94446735961414469754601189162981785600000000000000000000)]
    reserve := (213339437/500000000000) }

theorem tilt_021_013_valid : tilt_021_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_013]
  · intro i; fin_cases i <;> norm_num [tilt_021_013]
  · norm_num [tilt_021_013]
  · norm_num [tilt_021_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_013]

def tilt_021_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5600629/100000000), (911/2500000)]
    alternative := (.spike 3 false true)
    polynomial := [(-2135005001800053062042876007682865893286533/2057110345821559200045303773820000000000000000), (1358630839955526616067/1931446173500000000000), (-79395170765244160660280025825446665803380486533/1028555172910779600022651886910000000000000000), (1358630839955526616067/1931446173500000000000), (-158788206525486521267498008774885648740867686533/2057110345821559200045303773820000000000000000)]
    bernstein := [(8769183531081459504303204173271570706314659233075067/21570365379801872597467044499370803200000000000000000000), (21262530146736791935570156184132545304947964427084401/43140730759603745194934088998741606400000000000000000000), (141790312109543926941897620567162001053824983843273209/258844384557622471169604533992449638400000000000000000000), (98583687680801587251169511742127644064049211881647609/172562923038414980779736355994966425600000000000000000000), (194440873980128746857047593021612687653445397376808427/345125846076829961559472711989932851200000000000000000000)]
    reserve := (203269239/500000000000) }

theorem tilt_021_014_valid : tilt_021_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_014]
  · intro i; fin_cases i <;> norm_num [tilt_021_014]
  · norm_num [tilt_021_014]
  · norm_num [tilt_021_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_014]

def tilt_021_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14491/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (63/1562500), 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5597859/100000000), (44919/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-44150821308393585358352118312505754850785137/56322501588789696884614765994100000000000000000), (167889143508145609147/297607816504687500000), (-196160258626337032608286088083867659038501642793/3129027866043872049145264777450000000000000000), (167889143508145609147/297607816504687500000), (-3530840504452758193363791233391305356938178785137/56322501588789696884614765994100000000000000000)]
    bernstein := [(216631574163570139820577729579528237621915837596037263/590584234259667452004818128670294016000000000000000000000), (56974617697405043327486170912694596078852971161695621/131240940946592767112181806371176448000000000000000000000), (1124301061865117550475552706351943977017342145552098567/2362336937038669808019272514681176064000000000000000000000), (258399918243409239873683157035273833074671482102108589/524963763786371068448727225484705792000000000000000000000), (4564149808157669847920502539885419010413780572954410303/9449347748154679232077090058724704256000000000000000000000)]
    reserve := (73361787/200000000000) }

theorem tilt_021_015_valid : tilt_021_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_015]
  · intro i; fin_cases i <;> norm_num [tilt_021_015]
  · norm_num [tilt_021_015]
  · norm_num [tilt_021_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_015]

def tilt_021_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4293/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (471/12500000), (5597859/100000000), (911/2500000)]
    alternative := (.spike 3 true true)
    polynomial := [(-2357566302183084908873965466850710617686937261/2152043928334955981116889370423600000000000000000), (1358630839955526616067/1931446173500000000000), (-83059302424393114013677317864669456021831942937261/1076021964167477990558444685211800000000000000000), (1358630839955526616067/1931446173500000000000), (-166116247282484044942445761763872061333046198937261/2152043928334955981116889370423600000000000000000)]
    bernstein := [(7873267343277408748721435573720849451639444922090649939/22565816141977548028556233884812967936000000000000000000000), (19642551467085696123965840522863806658433094820214836217/45131632283955096057112467769625935872000000000000000000000), (132726365195193015084871558575777545377640891267333897153/270789793703730576342674806617755615232000000000000000000000), (92728206519745209006058586999976026396628318120152021953/180526529135820384228449871078503743488000000000000000000000), (182603933934474004872815212499934306123465997269770421059/361053058271640768456899742157007486976000000000000000000000)]
    reserve := (348902397/1000000000000) }

theorem tilt_021_016_valid : tilt_021_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_016]
  · intro i; fin_cases i <;> norm_num [tilt_021_016]
  · norm_num [tilt_021_016]
  · norm_num [tilt_021_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_016]

def tilt_021_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (63/1562500), 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (559509/10000000), (44919/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-407604715340063570696749417491857731858061/562946414717522083250291282910000000000000000), (167889143508145609147/297607816504687500000), (-5881885590242218862254977428775656276912752687/93824402452920347208381880485000000000000000), (167889143508145609147/297607816504687500000), (-35290905936737973109959167823236445803744658061/562946414717522083250291282910000000000000000)]
    bernstein := [(2518464983186071308323911366916145735239430685089139/5902920997588404359662574322686361600000000000000000000), (1943874744731888405810872013599788016352819381357939/3935280665058936239775049548457574400000000000000000000), (12650347440578241584625524722342411659710335512131851/23611683990353617438650297290745446400000000000000000000), (8690101271215801192003099885988479478949368242653451/15741122660235744959100198193830297600000000000000000000), (51270592407679639863749825403259122231330751436796259/94446735961414469754601189162981785600000000000000000000)]
    reserve := (85329449/200000000000) }

theorem tilt_021_017_valid : tilt_021_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_017]
  · intro i; fin_cases i <;> norm_num [tilt_021_017]
  · norm_num [tilt_021_017]
  · norm_num [tilt_021_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_017]

def tilt_021_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5600629/100000000), (911/2500000)]
    alternative := (.spike 4 false true)
    polynomial := [(-2088470445080322773279593247636074745569333/2057110345821559200045303773820000000000000000), (1358630839955526616067/1931446173500000000000), (-79395124230687440929991262542686619012232769333/1028555172910779600022651886910000000000000000), (1358630839955526616067/1931446173500000000000), (-158788159990929801537209245492125601949719969333/2057110345821559200045303773820000000000000000)]
    bernstein := [(9257143254874689334488553016332351794275609935352267/21570365379801872597467044499370803200000000000000000000), (22238454359508394253042153519172019032330183220636001/43140730759603745194934088998741606400000000000000000000), (147645890742562608559878162697350789798434100622997609/258844384557622471169604533992449638400000000000000000000), (102487432183972095875669149015281068288415216684412009/172562923038414980779736355994966425600000000000000000000), (202248420169389494342058417686383716120403082866061627/345125846076829961559472711989932851200000000000000000000)]
    reserve := (429160243/1000000000000) }

theorem tilt_021_018_valid : tilt_021_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_018]
  · intro i; fin_cases i <;> norm_num [tilt_021_018]
  · norm_num [tilt_021_018]
  · norm_num [tilt_021_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_018]

def tilt_021_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5597859/100000000), (8113/20000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-245987521510952311933479729866167928470039/321241009529328799435390437180000000000000000), (265664988658393/424027700000000), (-11142465978005787076179404824377303439623934519/160620504764664399717695218590000000000000000), (265664988658393/424027700000000), (-3183526566927151885720982309860677244474199857/45891572789904114205055776740000000000000000)]
    bernstein := [(1733793315384232507412804997437530597601894746469801/3368456128082254751967639630564556800000000000000000000), (567913959860700969199898797444549261053353611256429/962416036594929929133611323018444800000000000000000000), (3679756297329949956709651744627694729984902504994261/5774496219569579574801667938110668800000000000000000000), (289871407770702496563435209353455791211374989782607/441764738109148164192477328598630400000000000000000000), (34862906019588949239325135087037897121576636392757881/53895298049316076031482234089032908800000000000000000000)]
    reserve := (51471453/100000000000) }

theorem tilt_021_019_valid : tilt_021_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_019]
  · intro i; fin_cases i <;> norm_num [tilt_021_019]
  · norm_num [tilt_021_019]
  · norm_num [tilt_021_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_019]

def tilt_021_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592403/100000000), (1/100000000), (4240277/100000000), (850119/20000000), (1/100000000), (5597859/100000000), (8113/20000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-299599725920620666960459526132435962270039/321241009529328799435390437180000000000000000), (265664988658393/424027700000000), (-11142412148558932303520483938403900124243334519/160620504764664399717695218590000000000000000), (265664988658393/424027700000000), (-3183503528198849140910572488183095401789199857/45891572789904114205055776740000000000000000)]
    bernstein := [(1171639631305495412564861999256652641566052421469801/3368456128082254751967639630564556800000000000000000000), (407299409023437374506127536763216736838523266256429/962416036594929929133611323018444800000000000000000000), (2716074504649074871992000972951771182427478039994261/5774496219569579574801667938110668800000000000000000000), (216147599579378973736637582815598913556095754782607/441764738109148164192477328598630400000000000000000000), (25868667570226094248317875801559773104540518467757881/53895298049316076031482234089032908800000000000000000000)]
    reserve := (347826893/1000000000000) }

theorem tilt_021_020_valid : tilt_021_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_021_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_021_020]
  · intro i; fin_cases i <;> norm_num [tilt_021_020]
  · norm_num [tilt_021_020]
  · norm_num [tilt_021_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_021_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_021_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_021_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_021_020]

def tiltBundle021_row : Alternative → Row
  | .zero => tilt_021_000
  | (.spike 0 false false) => tilt_021_001
  | (.spike 0 false true) => tilt_021_002
  | (.spike 0 true false) => tilt_021_003
  | (.spike 0 true true) => tilt_021_004
  | (.spike 1 false false) => tilt_021_005
  | (.spike 1 false true) => tilt_021_006
  | (.spike 1 true false) => tilt_021_007
  | (.spike 1 true true) => tilt_021_008
  | (.spike 2 false false) => tilt_021_009
  | (.spike 2 false true) => tilt_021_010
  | (.spike 2 true false) => tilt_021_011
  | (.spike 2 true true) => tilt_021_012
  | (.spike 3 false false) => tilt_021_013
  | (.spike 3 false true) => tilt_021_014
  | (.spike 3 true false) => tilt_021_015
  | (.spike 3 true true) => tilt_021_016
  | (.spike 4 false false) => tilt_021_017
  | (.spike 4 false true) => tilt_021_018
  | (.spike 4 true false) => tilt_021_019
  | (.spike 4 true true) => tilt_021_020

def tiltBundle021 : TiltBundle where
  interval := ⟨(1/320), (3/640)⟩
  lambda := ![(14497491/100000000), (14497491/100000000), (8542547/100000000), (579657/4000000), (579657/4000000), (16756717/100000000), (2090363/12500000)]
  row := tiltBundle021_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_021_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_021_001_valid | exact tilt_021_002_valid | exact tilt_021_003_valid | exact tilt_021_004_valid | exact tilt_021_005_valid | exact tilt_021_006_valid | exact tilt_021_007_valid | exact tilt_021_008_valid | exact tilt_021_009_valid | exact tilt_021_010_valid | exact tilt_021_011_valid | exact tilt_021_012_valid | exact tilt_021_013_valid | exact tilt_021_014_valid | exact tilt_021_015_valid | exact tilt_021_016_valid | exact tilt_021_017_valid | exact tilt_021_018_valid | exact tilt_021_019_valid | exact tilt_021_020_valid
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
