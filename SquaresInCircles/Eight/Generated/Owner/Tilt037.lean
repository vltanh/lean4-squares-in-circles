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

def tilt_037_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5506031/100000000), (200043/50000000)]
    alternative := .zero
    polynomial := [(-5928660382269097209174013663928710988903227/385739426513839393232905045140000000000000000), (13513764640637/21075050000000), (-1290595425687522265388336438206237270388903227/192869713256919696616452522570000000000000000), (13513764640637/21075050000000), (-2575262190992775433567498862748545829788903227/385739426513839393232905045140000000000000000)]
    bernstein := [(4751581286806409197212704931328195213079969693/258865347133552419583095449992141209600000000000000), (315266043107741612502650019114130691010329836549/12943267356677620979154772499607060480000000000000000), (53658377474118583714145197815975285956958730262279/1941490103501643146873215874941059072000000000000000000), (182470473970694951384726227363333707818540023414609/6471633678338810489577386249803530240000000000000000000), (1684566429195120270534400113289993389740629402955333/64716336783388104895773862498035302400000000000000000000)]
    reserve := (2294427/125000000000) }

theorem tilt_037_000_valid : tilt_037_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_000]
  · intro i; fin_cases i <;> norm_num [tilt_037_000]
  · norm_num [tilt_037_000]
  · norm_num [tilt_037_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_000]

def tilt_037_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14741/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5506031/100000000), (80803/20000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-106574736729256510295093905909709980337642011/7011495676564035742879926747300000000000000000), (270304335071917278101/425731816287500000000), (-23241734445928705641009854986424600819153642011/3505747838282017871439963373650000000000000000), (270304335071917278101/425731816287500000000), (-46376894155128154771724616066939491657969642011/7011495676564035742879926747300000000000000000)]
    bernstein := [(132599018648429197494500320753295123322570863549/4705335097951238619600679724145180672000000000000000), (7994806033652638708047933281658362879191977304357/235266754897561930980033986207259033600000000000000000), (1308780944372103339266623147942366445348944480678247/35290013234634289647005097931088855040000000000000000000), (4410507956246575613856158207462118151387479378045937/117633377448780965490016993103629516800000000000000000000), (41410449009493676360100512430238846799415451216436069/1176333774487809654900169931036295168000000000000000000000)]
    reserve := (3522571/125000000000) }

theorem tilt_037_001_valid : tilt_037_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_001]
  · intro i; fin_cases i <;> norm_num [tilt_037_001]
  · norm_num [tilt_037_001]
  · norm_num [tilt_037_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_001]

def tilt_037_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2183/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (479/12500000), (421501/10000000), (548091/12500000), (1/100000000), (5506031/100000000), (396159/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-340620750573878108803649844253006614993606921151/21954672449217567819324356822326800000000000000000), (90121273435312087933/139151178882500000000), (-74147720481095123066366885242788593210694150921151/10977336224608783909662178411163400000000000000000), (90121273435312087933/139151178882500000000), (-147954820211616368023930120641324179806394694921151/21954672449217567819324356822326800000000000000000)]
    bernstein := [(535550418236321993033448306298651392403256102058809/14733531275590886651978148338770013847552000000000000000), (377737437868347396594103564555044464360474748898139/8875621250355955814444667673957839667200000000000000000), (5085425279238241213751584279471261348676436656146688027/110501484566931649889836112540775103856640000000000000000000), (17214485872349747641189071135519622814747844361754036317/368338281889772166299453708469250346188800000000000000000000), (164650773393897631368727806183122964268020694502337416129/3683382818897721662994537084692503461888000000000000000000000)]
    reserve := (36349087/1000000000000) }

theorem tilt_037_002_valid : tilt_037_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_002]
  · intro i; fin_cases i <;> norm_num [tilt_037_002]
  · norm_num [tilt_037_002]
  · norm_num [tilt_037_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_002]

def tilt_037_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2727323/50000000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5506031/100000000), (80803/20000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-106147037719692913321118786610490919510411201/7007998516168840237410601761225000000000000000), (270304335071917278101/425731816287500000000), (-23229767502226748036423821164164327724062411201/3503999258084420118705300880612500000000000000), (270304335071917278101/425731816287500000000), (-46353387966733803159526523541718164528614411201/7007998516168840237410601761225000000000000000)]
    bernstein := [(384989660577944558044142056607257642029134866759/4702988193337765005301157857522089984000000000000000), (20614579871571759936323998352431435297145861349887/235149409666888250265057892876104499200000000000000000), (3201832293067944376343255174159201696829044886891877/35272411450033237539758683931415674880000000000000000000), (10721126769556252228275050397478360302123322125829667/117574704833444125132528946438052249600000000000000000000), (104522748102222306343992274437584826436592889348390079/1175747048334441251325289464380522496000000000000000000000)]
    reserve := (81860647/1000000000000) }

theorem tilt_037_003_valid : tilt_037_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_003]
  · intro i; fin_cases i <;> norm_num [tilt_037_003]
  · norm_num [tilt_037_003]
  · norm_num [tilt_037_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_003]

def tilt_037_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5460091/100000000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5506031/100000000), (396159/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-1416866765802599952745606971122235336157981499/91714517407275320832108680418300000000000000000), (90121273435312087933/139151178882500000000), (-309742237990215472235056717795328005291021981499/45857258703637660416054340209150000000000000000), (90121273435312087933/139151178882500000000), (-618067609214628344517367828619533775245885981499/91714517407275320832108680418300000000000000000)]
    bernstein := [(6321207360062638181262180558365267961505282032541/61548570755104721162783482674111578112000000000000000), (4038383240421051826037262802996835666936045392711/37077452262111277808905712454284083200000000000000000), (51878402341390810390218779479103831747290431836726023/461614280663285408720876120055836835840000000000000000000), (174034590162871746863788096069116146501977212450321233/1538714268877618029069587066852789452800000000000000000000), (1709116859252385067785734542959481107824741728546673221/15387142688776180290695870668527894528000000000000000000000)]
    reserve := (25675687/250000000000) }

theorem tilt_037_004_valid : tilt_037_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_004]
  · intro i; fin_cases i <;> norm_num [tilt_037_004]
  · norm_num [tilt_037_004]
  · norm_num [tilt_037_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_004]

def tilt_037_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (547843/12500000), (1/100000000), (5506031/100000000), (80803/20000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-21311280242771186502584875337330326948063217/1401664623551881360389631542580000000000000000), (270304335071917278101/425731816287500000000), (-4646249584490406637593066877279533115101663217/700832311775940680194815771290000000000000000), (270304335071917278101/425731816287500000000), (-9271187888738042088683548879221735903255263217/1401664623551881360389631542580000000000000000)]
    bernstein := [(22478740221322832059885805789368063863077310103/940641205955544031585227702011114291200000000000000), (1396769794969393945006709211846388835685839241679/47032060297777201579261385100555714560000000000000000), (231415329349947433661652622004263340368141856487509/7054809044666580236889207765083357184000000000000000000), (780953532064239068884716999672818699474344589941939/23516030148888600789630692550277857280000000000000000000), (7270776985449358170178799692096961431556966352742543/235160301488886007896306925502778572800000000000000000000)]
    reserve := (5974313/250000000000) }

theorem tilt_037_005_valid : tilt_037_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_005]
  · intro i; fin_cases i <;> norm_num [tilt_037_005]
  · norm_num [tilt_037_005]
  · norm_num [tilt_037_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_005]

def tilt_037_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (2193357/50000000), (1/100000000), (5506031/100000000), (396159/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-708242828127152760975157276065388608217624037/45855149279588239843827243272100000000000000000), (90121273435312087933/139151178882500000000), (-154863836989912287229340535068736593471785624037/22927574639794119921913621636050000000000000000), (90121273435312087933/139151178882500000000), (-309019431151697421697705912861407798335353624037/45855149279588239843827243272100000000000000000)]
    bernstein := [(3266934521331355334199586604561325940773231676483/30772869767035851636787837082422738944000000000000000), (2083245731711878912316694858304724195761117935193/18537873353636055202884239206278758400000000000000000), (26736697059048827130296932893573217686114459668778649/230796523252768887275908778118170542080000000000000000000), (89675788136814218525542354814604375055092163447460879/769321744175896290919695927060568473600000000000000000000), (881146088952252324160702729809129283343144122088711323/7693217441758962909196959270605684736000000000000000000000)]
    reserve := (829397/7812500000) }

theorem tilt_037_006_valid : tilt_037_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_006]
  · intro i; fin_cases i <;> norm_num [tilt_037_006]
  · norm_num [tilt_037_006]
  · norm_num [tilt_037_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_006]

def tilt_037_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (210647/5000000), (548091/12500000), (1/100000000), (5506031/100000000), (80803/20000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-53276712863210696520414042959045461216752407/3504026158374913552115956853100000000000000000), (8444988951927288217/13297585578906250000), (-11615746295965258811065455353136537176661252407/1752013079187456776057978426550000000000000000), (8444988951927288217/13297585578906250000), (-23178215879067306925610496663314028892105752407/3504026158374913552115956853100000000000000000)]
    bernstein := [(71791957937888348006595087874075729839009033313/2351512149148245345807066606845558784000000000000000), (4277637822276560405815579690120774242606124287209/117575607457412267290353330342277939200000000000000000), (697288647363960079301487415727325767027073999141139/17636341118611840093552999551341690880000000000000000000), (2351194759239451853923571223914167288199741732165669/58787803728706133645176665171138969600000000000000000000), (1305576745860547079058897766735378070642129692269209/34581061016885960967750979512434688000000000000000000000)]
    reserve := (7632531/250000000000) }

theorem tilt_037_007_valid : tilt_037_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_007]
  · intro i; fin_cases i <;> norm_num [tilt_037_007]
  · norm_num [tilt_037_007]
  · norm_num [tilt_037_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_007]

def tilt_037_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (4217079/100000000), (548091/12500000), (1/100000000), (5506031/100000000), (396159/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-590218698986661241152026465360797691364378389/38214073112224592478807821403900000000000000000), (300477588454488571319/464064944322500000000), (-129051867491162530948850708279225360367426378389/19107036556112296239403910701950000000000000000), (300477588454488571319/464064944322500000000), (-257513516283338400656549390093089923043488378389/38214073112224592478807821403900000000000000000)]
    bernstein := [(2552582513440064421904701474839657771916003100051/25645030353743369141157369687306141696000000000000000), (1632929615778527616709048546684978604720381038921/15448813466110463338046608245365145600000000000000000), (20987155322412065812058337539500143140147750066652553/192337727653075268558680272654796062720000000000000000000), (70386002247063989438493093506819750679474754917000863/641125758843584228528934242182653542400000000000000000000), (690526301718969870050500794610521346916348889457255531/6411257588435842285289342421826535424000000000000000000000)]
    reserve := (24883793/250000000000) }

theorem tilt_037_008_valid : tilt_037_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_008]
  · intro i; fin_cases i <;> norm_num [tilt_037_008]
  · norm_num [tilt_037_008]
  · norm_num [tilt_037_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_008]

def tilt_037_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (876549/20000000), (1/100000000), (5506031/100000000), (80803/20000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-170491098567956289328398253632982865112554341/11213319546930215906456513444700000000000000000), (270304335071917278101/425731816287500000000), (-37170005974636105439887143261969640554936554341/5606659773465107953228256722350000000000000000), (270304335071917278101/425731816287500000000), (-74169520850704254590445888270306298244760554341/11213319546930215906456513444700000000000000000)]
    bernstein := [(179278782325622347778683861909409931292413838019/7525131364634814767570268826745438208000000000000000), (11146599871462088847092324141848408179325680159067/376256568231740738378513441337271910400000000000000000), (1847188596050173568024470665472937325140274897029657/56438485234761110756777016200590786560000000000000000000), (6233847115308208603809135772306271416596579472508047/188128284115870369189256720668635955200000000000000000000), (58028393080608969840392224711390802092920098410426139/1881282841158703691892567206686359552000000000000000000000)]
    reserve := (23824007/1000000000000) }

theorem tilt_037_009_valid : tilt_037_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_009]
  · intro i; fin_cases i <;> norm_num [tilt_037_009]
  · norm_num [tilt_037_009]
  · norm_num [tilt_037_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_009]

def tilt_037_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (2193357/50000000), (1/100000000), (5506031/100000000), (396159/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-235266253507584613449897531773393551155324679/15285049759862746614609081090700000000000000000), (90121273435312087933/139151178882500000000), (-51620464307435962769571690129330461839011324679/7642524879931373307304540545350000000000000000), (90121273435312087933/139151178882500000000), (-103005662361364340925693482726887530126867324679/15285049759862746614609081090700000000000000000)]
    bernstein := [(1638112097822669397169475159580680323176716442161/10257623255678617212262612360807579648000000000000000), (1025242988262763964374410186574310469391855361731/6179291117878685067628079735426252800000000000000000), (13031342116172448953104373031136642350651592427242883/76932174417589629091969592706056847360000000000000000000), (43623320941411507983736085239105529574147783468970293/256440581391965430306565309020189491200000000000000000000), (431039647476828998933379997461595284344363516376120441/2564405813919654303065653090201894912000000000000000000000)]
    reserve := (79848521/500000000000) }

theorem tilt_037_010_valid : tilt_037_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_010]
  · intro i; fin_cases i <;> norm_num [tilt_037_010]
  · norm_num [tilt_037_010]
  · norm_num [tilt_037_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_010]

def tilt_037_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2929/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5506031/100000000), (80803/20000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-106582028367823003572380675365997283542813761/7011495676564035742879926747300000000000000000), (270304335071917278101/425731816287500000000), (-23241741737567272134287141755880888122358813761/3505747838282017871439963373650000000000000000), (270304335071917278101/425731816287500000000), (-46376901446766721265001902836395778961174813761/7011495676564035742879926747300000000000000000)]
    bernstein := [(127684155297431502378848949667944983605399321799/4705335097951238619600679724145180672000000000000000), (7749044906796964679323407414220020265539062196607/235266754897561930980033986207259033600000000000000000), (1271914051384458034364868417500521436580741588352997/35290013234634289647005097931088855040000000000000000000), (4287609132856816314334635595207120122393624957153187/117633377448780965490016993103629516800000000000000000000), (40181367972061016925446386173691840593249132923104319/1176333774487809654900169931036295168000000000000000000000)]
    reserve := (13568019/500000000000) }

theorem tilt_037_011_valid : tilt_037_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_011]
  · intro i; fin_cases i <;> norm_num [tilt_037_011]
  · norm_num [tilt_037_011]
  · norm_num [tilt_037_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_011]

def tilt_037_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2169/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (3807/100000000), (5506031/100000000), (396159/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-8355058522522827438936446929655668116527509717/538554073649909022707852176748100000000000000000), (90121273435312087933/139151178882500000000), (-1818863246066624347796698484367637176466175509717/269277036824954511353926088374050000000000000000), (90121273435312087933/139151178882500000000), (-3629371433610725868154460521805618684815823509717/538554073649909022707852176748100000000000000000)]
    bernstein := [(13447884914331646573308348935905200051775690043603/361417520852177282172741634614922051584000000000000000), (9453176876116880680203795086465117126461354536713/217721398103721254320928695551157862400000000000000000), (127077363316274095071055606820164574365005346834568009/2710631406391329616295562259611915386880000000000000000000), (430044927543682276978110571820166065393048786384457439/9035438021304432054318540865373051289600000000000000000000), (4116623194892148739998645963869000354084123292684016043/90354380213044320543185408653730512896000000000000000000000)]
    reserve := (9302181/250000000000) }

theorem tilt_037_012_valid : tilt_037_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_012]
  · intro i; fin_cases i <;> norm_num [tilt_037_012]
  · norm_num [tilt_037_012]
  · norm_num [tilt_037_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_012]

def tilt_037_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5503291/100000000), (80803/20000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-106137349973443989684762782398112124476256461/7008006502937191749822951405300000000000000000), (270304335071917278101/425731816287500000000), (-23229784167653901220314297600045864946652256461/3504003251468595874911475702650000000000000000), (270304335071917278101/425731816287500000000), (-46353430985334358450943832417693617768828256461/7008006502937191749822951405300000000000000000)]
    bernstein := [(391601577613997914586109609113974886463164371099/4702993553167276016807904699368865792000000000000000), (20945201438000196485363123263119354145940789291507/235149677658363800840395234968443289600000000000000000), (3251429317263412437214088781127340937520002702820897/35272451648754570126059285245266493440000000000000000000), (10886462587721691075566787908334909011054242811654087/117574838829181900420197617484221644800000000000000000000), (106176228059258621306230372147989116547576096129117619/1175748388291819004201976174842216448000000000000000000000)]
    reserve := (1665329/20000000000) }

theorem tilt_037_013_valid : tilt_037_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_013]
  · intro i; fin_cases i <;> norm_num [tilt_037_013]
  · norm_num [tilt_037_013]
  · norm_num [tilt_037_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_013]

def tilt_037_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5508771/100000000), (396159/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-59045022156682864564329463067135688434948369/3821433174602660139556186988100000000000000000), (90121273435312087933/139151178882500000000), (-12905918510422856020553906670004886777282948369/1910716587301330069778093494050000000000000000), (90121273435312087933/139151178882500000000), (-25752791998689029176543483876942637866130948369/3821433174602660139556186988100000000000000000)]
    bernstein := [(257327072953050943235001624915655619292713610871/2564520391994981733436971729429725184000000000000000), (164617154668671118172552421170550630239227753141/1544891802406615502070464897246822400000000000000000), (2116168922542012693327106653041471355579786799553013/19233902939962363000777287970722938880000000000000000000), (7099992633845441376083635477595763927350504848405523/64113009799874543335924293235743129600000000000000000000), (69698603604354438046581524866252550409364635390979951/641130097998745433359242932357431296000000000000000000000)]
    reserve := (100341207/1000000000000) }

theorem tilt_037_014_valid : tilt_037_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_014]
  · intro i; fin_cases i <;> norm_num [tilt_037_014]
  · norm_num [tilt_037_014]
  · norm_num [tilt_037_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_014]

def tilt_037_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2929/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5506031/100000000), (80803/20000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-106582028367823003572380675365997283542813761/7011495676564035742879926747300000000000000000), (270304335071917278101/425731816287500000000), (-23241741737567272134287141755880888122358813761/3505747838282017871439963373650000000000000000), (270304335071917278101/425731816287500000000), (-46376901446766721265001902836395778961174813761/7011495676564035742879926747300000000000000000)]
    bernstein := [(127684155297431502378848949667944983605399321799/4705335097951238619600679724145180672000000000000000), (7749044906796964679323407414220020265539062196607/235266754897561930980033986207259033600000000000000000), (1271914051384458034364868417500521436580741588352997/35290013234634289647005097931088855040000000000000000000), (4287609132856816314334635595207120122393624957153187/117633377448780965490016993103629516800000000000000000000), (40181367972061016925446386173691840593249132923104319/1176333774487809654900169931036295168000000000000000000000)]
    reserve := (13568019/500000000000) }

theorem tilt_037_015_valid : tilt_037_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_015]
  · intro i; fin_cases i <;> norm_num [tilt_037_015]
  · norm_num [tilt_037_015]
  · norm_num [tilt_037_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_015]

def tilt_037_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2169/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (3807/100000000), (5506031/100000000), (396159/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-8355058522522827438936446929655668116527509717/538554073649909022707852176748100000000000000000), (90121273435312087933/139151178882500000000), (-1818863246066624347796698484367637176466175509717/269277036824954511353926088374050000000000000000), (90121273435312087933/139151178882500000000), (-3629371433610725868154460521805618684815823509717/538554073649909022707852176748100000000000000000)]
    bernstein := [(13447884914331646573308348935905200051775690043603/361417520852177282172741634614922051584000000000000000), (9453176876116880680203795086465117126461354536713/217721398103721254320928695551157862400000000000000000), (127077363316274095071055606820164574365005346834568009/2710631406391329616295562259611915386880000000000000000000), (430044927543682276978110571820166065393048786384457439/9035438021304432054318540865373051289600000000000000000000), (4116623194892148739998645963869000354084123292684016043/90354380213044320543185408653730512896000000000000000000000)]
    reserve := (9302181/250000000000) }

theorem tilt_037_016_valid : tilt_037_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_016]
  · intro i; fin_cases i <;> norm_num [tilt_037_016]
  · norm_num [tilt_037_016]
  · norm_num [tilt_037_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_016]

def tilt_037_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5503291/100000000), (80803/20000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-106137495963763273159956633034007351609950211/7008006502937191749822951405300000000000000000), (270304335071917278101/425731816287500000000), (-23229784313644220503789491450681760173785950211/3504003251468595874911475702650000000000000000), (270304335071917278101/425731816287500000000), (-46353431131324677734419026268329512995961950211/7008006502937191749822951405300000000000000000)]
    bernstein := [(391503174153197761682971332644520094041095427349/4702993553167276016807904699368865792000000000000000), (20940280905386032445006806985530404580407054397757/235149677658363800840395234968443289600000000000000000), (3250691182833246285474962747125395215003927093489647/35272451648754570126059285245266493440000000000000000000), (10884001955820833825173694647380954415956684064135337/117574838829181900420197617484221644800000000000000000000), (106151619882174173066670808600610933405836179023423869/1175748388291819004201976174842216448000000000000000000000)]
    reserve := (41622763/500000000000) }

theorem tilt_037_017_valid : tilt_037_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_017]
  · intro i; fin_cases i <;> norm_num [tilt_037_017]
  · norm_num [tilt_037_017]
  · norm_num [tilt_037_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_017]

def tilt_037_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (1377193/25000000), (396159/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-88482268443470913386097843234719079177336131/5732150802453644915255112793800000000000000000), (90121273435312087933/139151178882500000000), (-19358795998956962006644561993246642503081336131/2866075401226822457627556396900000000000000000), (90121273435312087933/139151178882500000000), (-38629109729470453099903026143258565926985336131/5732150802453644915255112793800000000000000000)]
    bernstein := [(443473481788287487630631163356773945835922524629/3846781286293525229221468897837842432000000000000000), (281556501662023037114485531029448938161912117359/2317338124273207969410523432432435200000000000000000), (3605438342855841547148108361850625581256278390653487/28850859647201439219161016733783818240000000000000000000), (12087379527862215435625229150848746206258714975055977/96169532157338130730536722445946060800000000000000000000), (118922896226096948227322584430490339630320477544895549/961695321573381307305367224459460608000000000000000000000)]
    reserve := (57642149/500000000000) }

theorem tilt_037_018_valid : tilt_037_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_018]
  · intro i; fin_cases i <;> norm_num [tilt_037_018]
  · norm_num [tilt_037_018]
  · norm_num [tilt_037_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_018]

def tilt_037_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5506031/100000000), (400087/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-528102000087619853135355930955153191132769531/34716635158960377315961056551700000000000000000), (13513764640637/21075050000000), (-116153714258575762232545234425791241621291949531/17358317579480188657980528275850000000000000000), (13513764640637/21075050000000), (-231779326517063904611955112920627330051451129531/34716635158960377315961056551700000000000000000)]
    bernstein := [(4104850411327457936893542254648262834269620147229/23297939474202903426855155734243442688000000000000000), (212234742288793507956607314462818928565704876094597/1164896973710145171342757786712172134400000000000000000), (32408432124493026924672860193487384311014614718385287/174734546056521775701413668006825820160000000000000000000), (108353128933515237659771309676666624506445710369293777/582448486855072585671378893356086067200000000000000000000), (1070920743606683279301136462008388060174267904728254149/5824484868550725856713788933560860672000000000000000000000)]
    reserve := (88094709/500000000000) }

theorem tilt_037_019_valid : tilt_037_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_019]
  · intro i; fin_cases i <;> norm_num [tilt_037_019]
  · norm_num [tilt_037_019]
  · norm_num [tilt_037_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_019]

def tilt_037_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/64), (31/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(682171/12500000), (1/100000000), (421501/10000000), (548091/12500000), (1/100000000), (5506031/100000000), (400087/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-533460644300452639833904547526312417075769531/34716635158960377315961056551700000000000000000), (13513764640637/21075050000000), (-116148112727757032217717285243518571998706949531/17358317579480188657980528275850000000000000000), (13513764640637/21075050000000), (-231762764811213611795600665939510831580338129531/34716635158960377315961056551700000000000000000)]
    bernstein := [(525298400788720574008851086670347565133313947229/23297939474202903426855155734243442688000000000000000), (33270997517208342278022237987974507065098472294597/1164896973710145171342757786712172134400000000000000000), (5565972163094298918779297860787501379587818289385287/174734546056521775701413668006825820160000000000000000000), (18885346263122389597474470925827489064175110118293777/582448486855072585671378893356086067200000000000000000000), (176314536290257690987739457366836597157250125601254149/5824484868550725856713788933560860672000000000000000000000)]
    reserve := (22546989/1000000000000) }

theorem tilt_037_020_valid : tilt_037_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_037_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_037_020]
  · intro i; fin_cases i <;> norm_num [tilt_037_020]
  · norm_num [tilt_037_020]
  · norm_num [tilt_037_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_037_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_037_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_037_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_037_020]

def tiltBundle037_row : Alternative → Row
  | .zero => tilt_037_000
  | (.spike 0 false false) => tilt_037_001
  | (.spike 0 false true) => tilt_037_002
  | (.spike 0 true false) => tilt_037_003
  | (.spike 0 true true) => tilt_037_004
  | (.spike 1 false false) => tilt_037_005
  | (.spike 1 false true) => tilt_037_006
  | (.spike 1 true false) => tilt_037_007
  | (.spike 1 true true) => tilt_037_008
  | (.spike 2 false false) => tilt_037_009
  | (.spike 2 false true) => tilt_037_010
  | (.spike 2 true false) => tilt_037_011
  | (.spike 2 true true) => tilt_037_012
  | (.spike 3 false false) => tilt_037_013
  | (.spike 3 false true) => tilt_037_014
  | (.spike 3 true false) => tilt_037_015
  | (.spike 3 true true) => tilt_037_016
  | (.spike 4 false false) => tilt_037_017
  | (.spike 4 false true) => tilt_037_018
  | (.spike 4 true false) => tilt_037_019
  | (.spike 4 true true) => tilt_037_020

def tiltBundle037 : TiltBundle where
  interval := ⟨(3/64), (31/640)⟩
  lambda := ![(14740791/100000000), (14740791/100000000), (93079/1000000), (366129/2500000), (366129/2500000), (3227001/20000000), (1973149/12500000)]
  row := tiltBundle037_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_037_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_037_001_valid | exact tilt_037_002_valid | exact tilt_037_003_valid | exact tilt_037_004_valid | exact tilt_037_005_valid | exact tilt_037_006_valid | exact tilt_037_007_valid | exact tilt_037_008_valid | exact tilt_037_009_valid | exact tilt_037_010_valid | exact tilt_037_011_valid | exact tilt_037_012_valid | exact tilt_037_013_valid | exact tilt_037_014_valid | exact tilt_037_015_valid | exact tilt_037_016_valid | exact tilt_037_017_valid | exact tilt_037_018_valid | exact tilt_037_019_valid | exact tilt_037_020_valid
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
