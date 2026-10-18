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

def tilt_023_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1397507/25000000), (80749/100000000)]
    alternative := .zero
    polynomial := [(-12142211256026929417059256190016617308363757/4993156748515753290669759072900000000000000000), (133074814803289/212093050000000), (-86646499902833913328835445181735697540308363757/2496578374257876645334879536450000000000000000), (133074814803289/212093050000000), (-173280857594411799728253831107281378463308363757/4993156748515753290669759072900000000000000000)]
    bernstein := [(438809881162068279921824571421342330219196679757843/3272315206707284076573333306015744000000000000000000000), (1867747596306229349581787343571780680065075938972729/6544630413414568153146666612031488000000000000000000000), (60442648722086566517728466983248826872232174385863/158978876439220279023805666689024000000000000000000000), (10956128396926760244114074590603676297886573008642561/26178521653658272612586666448125952000000000000000000000), (1612395769455359908457647658742625052366048257331791/4027464869793580401936410222788608000000000000000000000)]
    reserve := (134097681/1000000000000) }

theorem tilt_023_000_valid : tilt_023_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_000]
  · intro i; fin_cases i <;> norm_num [tilt_023_000]
  · norm_num [tilt_023_000]
  · norm_num [tilt_023_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_000]

def tilt_023_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14519/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3271/100000000), 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1397507/25000000), (10631/12500000)]
    alternative := (.spike 0 false false)
    polynomial := [(-149513686478350992373830450475836544122097/65737345841398621943442282510000000000000000), (1341037588237199925083/2254761214550000000000), (-1083782673010602759541132429618737122690322097/32868672920699310971721141255000000000000000), (1341037588237199925083/2254761214550000000000), (-2167415832334727168089891028786998408836522097/65737345841398621943442282510000000000000000)]
    bernstein := [(6673803093688216710991478380241949301504798191503/43081626970619000876854334265753600000000000000000000), (25641463402729802881525614397504348289860426177709/86163253941238001753708668531507200000000000000000000), (809190155907349653428984943303618387447076131923/2093034508694040528430170085785600000000000000000000), (145432197432010620705759411149537275530036548047381/344653015764952007014834674126028800000000000000000000), (21403203335051687736629919844122110776762921369211/53023540886915693386897642173235200000000000000000000)]
    reserve := (30982131/200000000000) }

theorem tilt_023_001_valid : tilt_023_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_001]
  · intro i; fin_cases i <;> norm_num [tilt_023_001]
  · norm_num [tilt_023_001]
  · norm_num [tilt_023_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_001]

def tilt_023_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4301/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (151/4000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1397507/25000000), (38317/50000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-184848247607787624565416672067636411375605301/71554423849371746881391885764140000000000000000), (86299088704658086869/130028310349600000000), (-1307793891814828882460458605407982369035648805301/35777211924685873440695942882070000000000000000), (86299088704658086869/130028310349600000000), (-2615402935382049977296351794143897101659922005301/71554423849371746881391885764140000000000000000)]
    bernstein := [(6423997303743381577833335406716266308193467183223499/46893907213924268036188986254386790400000000000000000000), (28001606676884666623216546142470286810669642028736097/93787814427848536072377972508773580800000000000000000000), (912774657113077306459475499966867313210160578803359/2278246504320207353984890020456038400000000000000000000), (166282663129672600433706988345357457678198558127808873/375151257711394144289511890035094323200000000000000000000), (24606417229186145427180856348317278741195582413308263/57715578109445252967617213851552972800000000000000000000)]
    reserve := (6849501/50000000000) }

theorem tilt_023_002_valid : tilt_023_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_002]
  · intro i; fin_cases i <;> norm_num [tilt_023_002]
  · norm_num [tilt_023_002]
  · norm_num [tilt_023_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_002]

def tilt_023_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3271/100000000), 0, 0]] i.1) i.2
    mu := ![(348539/6250000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1397507/25000000), (10631/12500000)]
    alternative := (.spike 0 true false)
    polynomial := [(-13827710355497423317396130826526782826478703/6241954090478589430630931770600000000000000000), (1341037588237199925083/2254761214550000000000), (-102907979350438588219545795295962570919998478703/3120977045239294715315465885300000000000000000), (1341037588237199925083/2254761214550000000000), (-205802130990521679015774194461098615057170478703/6241954090478589430630931770600000000000000000)]
    bernstein := [(875578920887550984342647714481160103657786881847697/4090727032736048369258287445180416000000000000000000000), (2918505145598687333658107091789370036118054258419891/8181454065472096738516574890360832000000000000000000000), (88586817844097192621179513585452750555186985395277/198739774869767532109714369806336000000000000000000000), (15744400330889610805544768386407427289660475808531019/32725816261888386954066299561443328000000000000000000000), (2330026670000540171600421229059353970682493255121189/5034740963367444146779430701760512000000000000000000000)]
    reserve := (26754991/125000000000) }

theorem tilt_023_003_valid : tilt_023_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_003]
  · intro i; fin_cases i <;> norm_num [tilt_023_003]
  · norm_num [tilt_023_003]
  · norm_num [tilt_023_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_003]

def tilt_023_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5582153/100000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1397507/25000000), (38317/50000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-454854954150961779605655341575145404521954561/180159973901640408604211859951700000000000000000), (86299088704658086869/130028310349600000000), (-3292757391811037802653226876036717303790667954561/90079986950820204302105929975850000000000000000), (86299088704658086869/130028310349600000000), (-6585059928667924643526848096731859462176813954561/180159973901640408604211859951700000000000000000)]
    bernstein := [(23093275008146248053212164704613235043462062815562239/118069640496179058182856284537946112000000000000000000000), (84340636742581738003145389482492175271582784180408317/236139280992358116365712569075892224000000000000000000000), (2634342888631327805943966394380835770737331563965699/5736176866211128332770345807511552000000000000000000000), (474022143926279839964764214264427467838499353144698853/944557123969432465462850276303568896000000000000000000000), (70470538003621688807496186164363798143601658974729643/145316480610681917763515427123625984000000000000000000000)]
    reserve := (12224393/62500000000) }

theorem tilt_023_004_valid : tilt_023_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_004]
  · intro i; fin_cases i <;> norm_num [tilt_023_004]
  · norm_num [tilt_023_004]
  · norm_num [tilt_023_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_004]

def tilt_023_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3271/100000000), 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (2130371/50000000), (1/100000000), (1397507/25000000), (10631/12500000)]
    alternative := (.spike 1 false false)
    polynomial := [(-2252351048079924812580669606923113165651897/985627373614397250899434775100000000000000000), (1341037588237199925083/2254761214550000000000), (-16249615111372516417389509931085888933627651897/492813686807198625449717387550000000000000000), (1341037588237199925083/2254761214550000000000), (-32496977871696952909966439192564854754089651897/985627373614397250899434775100000000000000000)]
    bernstein := [(93095988432290698310905195230368722398159075301703/645940755571931382349453574209536000000000000000000000), (370518620323448481192866104006177289406855292388309/1291881511143862764698907148419072000000000000000000000), (11794026863506868089521342820311344808362326670123/31381737112806382948151590649856000000000000000000000), (2124784685567640707222172054706863379250289419142781/5167526044575451058795628593676288000000000000000000000), (312331380054414064702117327907097756190186762686611/795004006857761701353173629796352000000000000000000000)]
    reserve := (72062327/500000000000) }

theorem tilt_023_005_valid : tilt_023_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_005]
  · intro i; fin_cases i <;> norm_num [tilt_023_005]
  · norm_num [tilt_023_005]
  · norm_num [tilt_023_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_005]

def tilt_023_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (1066121/25000000), (1/100000000), (1397507/25000000), (38317/50000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-525776134288110254407138154039007722755937/209152214906257894213331134200000000000000000), (86299088704658086869/130028310349600000000), (-3822642047648911235226025006348756705718755937/104576107453128947106665567100000000000000000), (86299088704658086869/130028310349600000000), (-7644758319163534360197642874543474403714755937/209152214906257894213331134200000000000000000)]
    bernstein := [(28301502793992746512170350278177287472545108949663/137069995560965173551648692109312000000000000000000000), (100897096405415652375352199653032887779096351156189/274139991121930347103297384218624000000000000000000000), (3130760598420022378303705884435320967265682632483/6659271039399117743399936458752000000000000000000000), (562240508876032747492090247998599140340318163413701/1096559964487721388413189536874496000000000000000000000), (83647424926261194514675672549841550561654938813131/168701532998110982832798390288384000000000000000000000)]
    reserve := (10323741/50000000000) }

theorem tilt_023_006_valid : tilt_023_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_006]
  · intro i; fin_cases i <;> norm_num [tilt_023_006]
  · norm_num [tilt_023_006]
  · norm_num [tilt_023_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_006]

def tilt_023_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3271/100000000), 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (211999/5000000), (4262613/100000000), (1/100000000), (1397507/25000000), (10631/12500000)]
    alternative := (.spike 1 true false)
    polynomial := [(-150154335838109537491208821566118780416031/65708195440777839978197401800000000000000000), (67036879659854924347/112688068450000000000), (-1083312477090237688495148111461599451390116031/32854097720388919989098700900000000000000000), (67036879659854924347/112688068450000000000), (-2166474799844637267452805014101632783999816031/65708195440777839978197401800000000000000000)]
    bernstein := [(6242195748785049948838779858376801147146863236769/43062522964068165208111449243648000000000000000000000), (24781329381649440309265107792264619410274916263907/86125045928136330416222898487296000000000000000000000), (10249457164975235640281991620324919128854630867577/27197382924674630657754599522304000000000000000000000), (142040382767757294169230516735168284041674603879163/344500183712545321664891593949184000000000000000000000), (271530814823243982108776926405383465889156448002289/689000367425090643329783187898368000000000000000000000)]
    reserve := (36239143/250000000000) }

theorem tilt_023_007_valid : tilt_023_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_007]
  · intro i; fin_cases i <;> norm_num [tilt_023_007]
  · norm_num [tilt_023_007]
  · norm_num [tilt_023_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_007]

def tilt_023_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4243743/100000000), (4262613/100000000), (1/100000000), (1397507/25000000), (38317/50000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-662098422182584215581339818320255581549471/263378111217203393908198209900000000000000000), (9591152784954861111/14454000047200000000), (-4813681415929390789144107685257091586192549471/131689055608601696954099104950000000000000000), (9591152784954861111/14454000047200000000), (-9626700733436598994072634030695862916803549471/263378111217203393908198209900000000000000000)]
    bernstein := [(35495610885659263802066915686128293837183348975329/172607478967306416231676778840064000000000000000000000), (126734969290422483648035326284454836456985627943587/345214957934612832463353557680128000000000000000000000), (51139743204073073128475479028784882335288298448057/109015249874088262883164281372672000000000000000000000), (706452861382618059804599632037307793613032793956283/1380859831738451329853414230720512000000000000000000000), (1365961540464075182213589961413631603306130694585649/2761719663476902659706828461441024000000000000000000000)]
    reserve := (205643527/1000000000000) }

theorem tilt_023_008_valid : tilt_023_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_008]
  · intro i; fin_cases i <;> norm_num [tilt_023_008]
  · norm_num [tilt_023_008]
  · norm_num [tilt_023_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_008]

def tilt_023_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3271/100000000), 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4260743/100000000), (1/100000000), (1397507/25000000), (10631/12500000)]
    alternative := (.spike 2 false false)
    polynomial := [(-14077690007728621850816181433861780792229/6160172530887706569050957588437500000000000), (1341037588237199925083/2254761214550000000000), (-101560118774977524543974978053271081194060979/3080086265443853284525478794218750000000000), (1341037588237199925083/2254761214550000000000), (-203106159859947320466099139925108300607329729/6160172530887706569050957588437500000000000)]
    bernstein := [(581527173772199634812550446867165600497252105471/4037130669842567377093235565158400000000000000000000), (2315096126935088252255034152055000374361470068813/8074261339685134754186471130316800000000000000000000), (73696997546148282480362558900489206960164781411/196135902988302868522748286566400000000000000000000), (13277324101104424121689782634937452081037815455317/32297045358740539016745884521267200000000000000000000), (1951674141004165904627820331452183150640562827627/4968776209037006002576289926348800000000000000000000)]
    reserve := (72022337/500000000000) }

theorem tilt_023_009_valid : tilt_023_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_009]
  · intro i; fin_cases i <;> norm_num [tilt_023_009]
  · norm_num [tilt_023_009]
  · norm_num [tilt_023_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_009]

def tilt_023_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (852897/20000000), (1/100000000), (1397507/25000000), (38317/50000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-1163845380726583872555646904081679480371617/474078464956501945904005773300000000000000000), (86299088704658086869/130028310349600000000), (-8664629425685733837602292609813606393834371617/237039232478250972952002886650000000000000000), (86299088704658086869/130028310349600000000), (-17328095005990741091332029572723131108188371617/474078464956501945904005773300000000000000000)]
    bernstein := [(82445325741216199975711411446816473098649067717983/310692062793893115267649223589888000000000000000000000), (265291328841694409453246057139279160495845033669149/621384125587786230535298447179776000000000000000000000), (7985267425183825049720814463767554891248976165603/15094351228853106814622634344448000000000000000000000), (1420784025508073442190482637498277969059543175150341/2485536502351144922141193788719104000000000000000000000), (212120288837008088571302433296910163886608946424971/382390231130945372637106736726016000000000000000000000)]
    reserve := (265360257/1000000000000) }

theorem tilt_023_010_valid : tilt_023_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_010]
  · intro i; fin_cases i <;> norm_num [tilt_023_010]
  · norm_num [tilt_023_010]
  · norm_num [tilt_023_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_010]

def tilt_023_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14507/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3271/100000000), 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1397507/25000000), (10631/12500000)]
    alternative := (.spike 2 true false)
    polynomial := [(-18690283725388059212260889508761007212909/8217168230174827742930285313750000000000000), (1341037588237199925083/2254761214550000000000), (-135472835199240939127807085785541421775487909/4108584115087413871465142656875000000000000), (1341037588237199925083/2254761214550000000000), (-270926980114756490196401910681574082543762909/8217168230174827742930285313750000000000000)]
    bernstein := [(833522185812870560916168343857273261149885056291/5385203371327375109606791783219200000000000000000000), (3203776496077200177540746105480117929031224879273/10770406742654750219213583566438400000000000000000000), (101114604436352788402392089555277749157017547031/261629313586755066053771260723200000000000000000000), (18173398687262741012304949920580192974793069369457/43081626970619000876854334265753600000000000000000000), (2674534854334860012728293528857648572353567191967/6627942610864461673362205271654400000000000000000000)]
    reserve := (6191203/40000000000) }

theorem tilt_023_011_valid : tilt_023_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_011]
  · intro i; fin_cases i <;> norm_num [tilt_023_011]
  · norm_num [tilt_023_011]
  · norm_num [tilt_023_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_011]

def tilt_023_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4297/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (3771/100000000), (1397507/25000000), (38317/50000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-2564505871617540336624757870654092994286843359/992758397115455693486860931628300000000000000000), (86299088704658086869/130028310349600000000), (-18144557527549287697165738866491457833708540843359/496379198557727846743430465814150000000000000000), (86299088704658086869/130028310349600000000), (-36286550549226957853994852975112261574422794843359/992758397115455693486860931628300000000000000000)]
    bernstein := [(89200096400159197302607436320113187702700042270935841/650614143133585043283549180151922688000000000000000000000), (388644018712395719045869887285756942054994081157037923/1301228286267170086567098360303845376000000000000000000000), (12667512828361199887901574295755835623168844869063581/31608784281793605341710891343413248000000000000000000000), (2307613952848289727088201940216408716549312661805597307/5204913145068680346268393441215381504000000000000000000000), (341482849522165651067720625422090351635992256236195317/800755868472104668656675914033135616000000000000000000000)]
    reserve := (137101379/1000000000000) }

theorem tilt_023_012_valid : tilt_023_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_012]
  · intro i; fin_cases i <;> norm_num [tilt_023_012]
  · norm_num [tilt_023_012]
  · norm_num [tilt_023_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_012]

def tilt_023_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3271/100000000), 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (5587261/100000000), (10631/12500000)]
    alternative := (.spike 3 false false)
    polynomial := [(-55304166916798823564623694940814701668228119/24967826510350271629868208694350000000000000000), (1341037588237199925083/2254761214550000000000), (-411632078016961437861574325511825151295315228119/12483913255175135814934104347175000000000000000), (1341037588237199925083/2254761214550000000000), (-823208851867006076899584027328709487888962228119/24967826510350271629868208694350000000000000000)]
    bernstein := [(3506706387313861828450324067318841044555468250239081/16362914781823154015350429249929216000000000000000000000), (11682804059294797310004170642621675497770797418403643/32725829563646308030700858499858432000000000000000000000), (354560668811013355296379034487119377010702691220421/794959422598695741636458101211136000000000000000000000), (63012743563485205219061298963011796364440642721728787/130903318254585232122803433999433728000000000000000000000), (9325513186836854565053599650793177880666673872703197/20138972039166958788123605230682112000000000000000000000)]
    reserve := (214308173/1000000000000) }

theorem tilt_023_013_valid : tilt_023_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_013]
  · intro i; fin_cases i <;> norm_num [tilt_023_013]
  · norm_num [tilt_023_013]
  · norm_num [tilt_023_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_013]

def tilt_023_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1398199/25000000), (38317/50000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-227462686184973263574330705503348416024916639/90079950342396456488433175846200000000000000000), (86299088704658086869/130028310349600000000), (-1646378062120268741645441260915099693224580916639/45039975171198228244216587923100000000000000000), (86299088704658086869/130028310349600000000), (-3292528661554352510027308191124696038033136916639/90079950342396456488433175846200000000000000000)]
    bernstein := [(11523495789548138496056948959000130261027935396126561/59034796256392941724259566122565632000000000000000000000), (42124026285593423746566941312421906870394976189378083/118069592512785883448519132245131264000000000000000000000), (1316046795606797469692552331962106395823198132155101/2868087267517065994700869609193472000000000000000000000), (236825866813460267827195436596957408932537083044178747/472278370051143533794076528980525056000000000000000000000), (35206775566631394777369307397218834176447030292315957/72658210777099005199088696766234624000000000000000000000)]
    reserve := (97599183/500000000000) }

theorem tilt_023_014_valid : tilt_023_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_014]
  · intro i; fin_cases i <;> norm_num [tilt_023_014]
  · norm_num [tilt_023_014]
  · norm_num [tilt_023_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_014]

def tilt_023_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14507/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3271/100000000), 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1397507/25000000), (10631/12500000)]
    alternative := (.spike 3 true false)
    polynomial := [(-18690283725388059212260889508761007212909/8217168230174827742930285313750000000000000), (1341037588237199925083/2254761214550000000000), (-135472835199240939127807085785541421775487909/4108584115087413871465142656875000000000000), (1341037588237199925083/2254761214550000000000), (-270926980114756490196401910681574082543762909/8217168230174827742930285313750000000000000)]
    bernstein := [(833522185812870560916168343857273261149885056291/5385203371327375109606791783219200000000000000000000), (3203776496077200177540746105480117929031224879273/10770406742654750219213583566438400000000000000000000), (101114604436352788402392089555277749157017547031/261629313586755066053771260723200000000000000000000), (18173398687262741012304949920580192974793069369457/43081626970619000876854334265753600000000000000000000), (2674534854334860012728293528857648572353567191967/6627942610864461673362205271654400000000000000000000)]
    reserve := (6191203/40000000000) }

theorem tilt_023_015_valid : tilt_023_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_015]
  · intro i; fin_cases i <;> norm_num [tilt_023_015]
  · norm_num [tilt_023_015]
  · norm_num [tilt_023_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_015]

def tilt_023_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4297/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (3771/100000000), (1397507/25000000), (38317/50000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-2564505871617540336624757870654092994286843359/992758397115455693486860931628300000000000000000), (86299088704658086869/130028310349600000000), (-18144557527549287697165738866491457833708540843359/496379198557727846743430465814150000000000000000), (86299088704658086869/130028310349600000000), (-36286550549226957853994852975112261574422794843359/992758397115455693486860931628300000000000000000)]
    bernstein := [(89200096400159197302607436320113187702700042270935841/650614143133585043283549180151922688000000000000000000000), (388644018712395719045869887285756942054994081157037923/1301228286267170086567098360303845376000000000000000000000), (12667512828361199887901574295755835623168844869063581/31608784281793605341710891343413248000000000000000000000), (2307613952848289727088201940216408716549312661805597307/5204913145068680346268393441215381504000000000000000000000), (341482849522165651067720625422090351635992256236195317/800755868472104668656675914033135616000000000000000000000)]
    reserve := (137101379/1000000000000) }

theorem tilt_023_016_valid : tilt_023_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_016]
  · intro i; fin_cases i <;> norm_num [tilt_023_016]
  · norm_num [tilt_023_016]
  · norm_num [tilt_023_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_016]

def tilt_023_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3271/100000000), 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (5587261/100000000), (10631/12500000)]
    alternative := (.spike 4 false false)
    polynomial := [(-55304932613146050866074257356484824066594119/24967826510350271629868208694350000000000000000), (1341037588237199925083/2254761214550000000000), (-411632078782657785088875776074240821417713594119/12483913255175135814934104347175000000000000000), (1341037588237199925083/2254761214550000000000), (-823208852632702424126885477891125158011360594119/24967826510350271629868208694350000000000000000)]
    bernstein := [(3506204541351324269786621912339024903625407752673081/16362914781823154015350429249929216000000000000000000000), (11681800347767130007310621896813639645107155855305643/32725829563646308030700858499858432000000000000000000000), (354536286598925579966748434775831259832780674414421/794959422598695741636458101211136000000000000000000000), (63008728521344785672889523114042805167400258797846787/130903318254585232122803433999433728000000000000000000000), (9324895469950436814134700077725696228453223823561197/20138972039166958788123605230682112000000000000000000000)]
    reserve := (1674043/7812500000) }

theorem tilt_023_017_valid : tilt_023_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_017]
  · intro i; fin_cases i <;> norm_num [tilt_023_017]
  · norm_num [tilt_023_017]
  · norm_num [tilt_023_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_017]

def tilt_023_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1398199/25000000), (38317/50000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-225487196569084802237204614608536248950878639/90079950342396456488433175846200000000000000000), (86299088704658086869/130028310349600000000), (-1646376086630652853184104134824204881057506878639/45039975171198228244216587923100000000000000000), (86299088704658086869/130028310349600000000), (-3292526686064736621565971065033801225866062878639/90079950342396456488433175846200000000000000000)]
    bernstein := [(12818253811260623623064826080804137352435836895764561/59034796256392941724259566122565632000000000000000000000), (44713592903528050361081387321082919139500041635492083/118069592512785883448519132245131264000000000000000000000), (1378952681166013394560384077231698468731212561113101/2868087267517065994700869609193472000000000000000000000), (247184639040172785969682444967761893345910804667204747/472278370051143533794076528980525056000000000000000000000), (36800479518721645304237402626383165659862499424521957/72658210777099005199088696766234624000000000000000000000)]
    reserve := (108565241/500000000000) }

theorem tilt_023_018_valid : tilt_023_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_018]
  · intro i; fin_cases i <;> norm_num [tilt_023_018]
  · norm_num [tilt_023_018]
  · norm_num [tilt_023_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_018]

def tilt_023_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1397507/25000000), (80749/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-11311552283729219134956870019762666025851007/4993156748515753290669759072900000000000000000), (133074814803289/212093050000000), (-86646585812924059795283407498524363045101476007/2496578374257876645334879536450000000000000000), (133074814803289/212093050000000), (-173281860073564390371431858127028963424177101007/4993156748515753290669759072900000000000000000)]
    bernstein := [(983186145648001038727665523312372421296384303820593/3272315206707284076573333306015744000000000000000000000), (2956497924977307965061758234017031277711786644760979/6544630413414568153146666612031488000000000000000000000), (86889962762232336043139648737337073832380719733613/158978876439220279023805666689024000000000000000000000), (15311107703590809921763632128881484105471966064736811/26178521653658272612586666448125952000000000000000000000), (2282390553661626773139104216135594620620232762953541/4027464869793580401936410222788608000000000000000000000)]
    reserve := (300455819/1000000000000) }

theorem tilt_023_019_valid : tilt_023_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_019]
  · intro i; fin_cases i <;> norm_num [tilt_023_019]
  · norm_num [tilt_023_019]
  · norm_num [tilt_023_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_019]

def tilt_023_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394847/25000000), (1/100000000), (4241861/100000000), (4262613/100000000), (1/100000000), (1397507/25000000), (80749/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-12138883354929472359790281503131094996851007/4993156748515753290669759072900000000000000000), (133074814803289/212093050000000), (-86645751824676693015945341768678013081476476007/2496578374257876645334879536450000000000000000), (133074814803289/212093050000000), (-173279364765998456559530893255852895067956101007/4993156748515753290669759072900000000000000000)]
    bernstein := [(441029157519775830336761839905043105067780524820593/3272315206707284076573333306015744000000000000000000000), (1872205301315297703764817250851310380391735307760979/6544630413414568153146666612031488000000000000000000000), (60551475843931261761682331281782341501111480733613/158978876439220279023805666689024000000000000000000000), (10974150747363708261093591537532333747905104031736811/26178521653658272612586666448125952000000000000000000000), (1615186119516141544945680672717288447353886139953541/4027464869793580401936410222788608000000000000000000000)]
    reserve := (67387939/500000000000) }

theorem tilt_023_020_valid : tilt_023_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_023_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_023_020]
  · intro i; fin_cases i <;> norm_num [tilt_023_020]
  · norm_num [tilt_023_020]
  · norm_num [tilt_023_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_023_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_023_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_023_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_023_020]

def tiltBundle023_row : Alternative → Row
  | .zero => tilt_023_000
  | (.spike 0 false false) => tilt_023_001
  | (.spike 0 false true) => tilt_023_002
  | (.spike 0 true false) => tilt_023_003
  | (.spike 0 true true) => tilt_023_004
  | (.spike 1 false false) => tilt_023_005
  | (.spike 1 false true) => tilt_023_006
  | (.spike 1 true false) => tilt_023_007
  | (.spike 1 true true) => tilt_023_008
  | (.spike 2 false false) => tilt_023_009
  | (.spike 2 false true) => tilt_023_010
  | (.spike 2 true false) => tilt_023_011
  | (.spike 2 true true) => tilt_023_012
  | (.spike 3 false false) => tilt_023_013
  | (.spike 3 false true) => tilt_023_014
  | (.spike 3 true false) => tilt_023_015
  | (.spike 3 true true) => tilt_023_016
  | (.spike 4 false false) => tilt_023_017
  | (.spike 4 false true) => tilt_023_018
  | (.spike 4 true false) => tilt_023_019
  | (.spike 4 true true) => tilt_023_020

def tiltBundle023 : TiltBundle where
  interval := ⟨(1/160), (3/320)⟩
  lambda := ![(7259481/50000000), (7259481/50000000), (8610447/100000000), (14506521/100000000), (14506521/100000000), (133621/800000), (8317981/50000000)]
  row := tiltBundle023_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_023_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_023_001_valid | exact tilt_023_002_valid | exact tilt_023_003_valid | exact tilt_023_004_valid | exact tilt_023_005_valid | exact tilt_023_006_valid | exact tilt_023_007_valid | exact tilt_023_008_valid | exact tilt_023_009_valid | exact tilt_023_010_valid | exact tilt_023_011_valid | exact tilt_023_012_valid | exact tilt_023_013_valid | exact tilt_023_014_valid | exact tilt_023_015_valid | exact tilt_023_016_valid | exact tilt_023_017_valid | exact tilt_023_018_valid | exact tilt_023_019_valid | exact tilt_023_020_valid
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
