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

def tilt_017_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26559/50000000), 0, (327011/100000000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (21723/390625), (6711/50000000)]
    alternative := .zero
    polynomial := [(151716777458480380218567853415885726329/2196266315591180881497064200000000000000000), (-20161754063079643/29835323390625000), (-236706772768280834943635443547402490114273671/1098133157795590440748532100000000000000000), (-20161754063079643/29835323390625000), (-473413697253339128367651105662658396114273671/2196266315591180881497064200000000000000000)]
    bernstein := [(134344712026863659767416950942174422324324072733/1771501652413336987689742761984000000000000000000000), (10386930386692267002466860138494346096293533/17299820824348994020407644160000000000000000000), (522300441824195624871559412985138661013995129/674693012149610766795898122240000000000000000000), (437073897910005226029914768392958575443/732088771863726960499021400000000000000000), (151716777458480380218567853415885726329/2196266315591180881497064200000000000000000)]
    reserve := (4317463/62500000000) }

theorem tilt_017_000_valid : tilt_017_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_000]
  · intro i; fin_cases i <;> norm_num [tilt_017_000]
  · norm_num [tilt_017_000]
  · norm_num [tilt_017_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_000]

def tilt_017_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7287/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(903/2500000), 0, (40883/12500000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(207636178774158498370387213522781385069/4392859894826467139373430600000000000000000), (-774208905117689872379/1145761776300000000000), (-473414158529187215817434872263516743458614931/2196429947413233569686715300000000000000000), (-774208905117689872379/1145761776300000000000), (-946828524694553205793368114914247009698614931/4392859894826467139373430600000000000000000)]
    bernstein := [(574158636660656582885643654531837629210101759139/10629801824025132939543771611136000000000000000000000), (120114309465191788858261872362749637201502953/207613316875490877725464289280000000000000000000), (1015166806246509526040364105197998417074581869/1349486559690690705215517880320000000000000000000), (15159832020460138989816229779840953144789/26357159368958802836240583600000000000000000), (207636178774158498370387213522781385069/4392859894826467139373430600000000000000000)]
    reserve := (23633371/500000000000) }

theorem tilt_017_001_valid : tilt_017_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_001]
  · intro i; fin_cases i <;> norm_num [tilt_017_001]
  · norm_num [tilt_017_001]
  · norm_num [tilt_017_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_001]

def tilt_017_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4317/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(17529/25000000), 0, (163479/50000000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (3789/100000000), (853581/20000000), (421139/10000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(394066605374853403048425019250344201173109/3328909228299496798217185708680000000000000000), (-774215869454886248219/1145761776300000000000), (-358753017587765560310240276989363911636409226891/1664454614149748399108592854340000000000000000), (-774215869454886248219/1145761776300000000000), (-717506429242136495473883602403747073617019626891/3328909228299496798217185708680000000000000000)]
    bernstein := [(336024676129654041760105294335458176334081125302793/2685087940748748580528756708972953600000000000000000000), (34070906367316744100536539052074244653610194811/52443123842748995713452279472128000000000000000000), (842023706041476366337547081796441707800001857909/1022640914933605416412319449706496000000000000000000), (4302845002605458633021691161131221868609343/6657818456598993596434371417360000000000000000), (394066605374853403048425019250344201173109/3328909228299496798217185708680000000000000000)]
    reserve := (23675419/200000000000) }

theorem tilt_017_002_valid : tilt_017_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_002]
  · intro i; fin_cases i <;> norm_num [tilt_017_002]
  · norm_num [tilt_017_002]
  · norm_num [tilt_017_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_002]

def tilt_017_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(903/2500000), 0, (40883/12500000), 0, 0]] i.1) i.2
    mu := ![(2827463/50000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(2139358089917428888259192028202731450433/19758103899300008840246446200000000000000000), (-774208905117689872379/1145761776300000000000), (-2129310075933052569632226844678356313748549567/9879051949650004420123223100000000000000000), (-774208905117689872379/1145761776300000000000), (-4258622291224195056693341948548740830228549567/19758103899300008840246446200000000000000000)]
    bernstein := [(611049762397901589420847021560323011036458313047/5312275270336514376838527582208000000000000000000000), (66357741455815356564838996675864933161468619/103755376373760046422627491840000000000000000000), (4936311400405576154773864978503589689904468033/6069689517864962715723708272640000000000000000000), (25139427999873902600518605515123128597741/39516207798600017680492892400000000000000000), (2139358089917428888259192028202731450433/19758103899300008840246446200000000000000000)]
    reserve := (108277499/1000000000000) }

theorem tilt_017_003_valid : tilt_017_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_003]
  · intro i; fin_cases i <;> norm_num [tilt_017_003]
  · norm_num [tilt_017_003]
  · norm_num [tilt_017_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_003]

def tilt_017_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(17529/25000000), 0, (163479/50000000), 0, 0]] i.1) i.2
    mu := ![(2830259/50000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(3471875247863455491903236409580170058333/19777642142064792260831376600000000000000000), (-774215869454886248219/1145761776300000000000), (-2131414390957103348024664510532142214377941667/9888821071032396130415688300000000000000000), (-774215869454886248219/1145761776300000000000), (-4262832253789454559504820924300694008925941667/19777642142064792260831376600000000000000000)]
    bernstein := [(969461130907643477850590610077483647651718429147/5317528432501982464023979884544000000000000000000000), (73411221154602479462959670408754013434183319/103857977197304345000468357120000000000000000000), (5349951159839580086619252819882574455381955933/6075691666042304182527398891520000000000000000000), (27825278733529742714051404802857242551041/39555284284129584521662753200000000000000000), (3471875247863455491903236409580170058333/19777642142064792260831376600000000000000000)]
    reserve := (175545457/1000000000000) }

theorem tilt_017_004_valid : tilt_017_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_004]
  · intro i; fin_cases i <;> norm_num [tilt_017_004]
  · norm_num [tilt_017_004]
  · norm_num [tilt_017_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_004]

def tilt_017_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(903/2500000), 0, (40883/12500000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (84191/2000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(29373455467332505759821899493930717671/878188121749197046416951400000000000000000), (-774208905117689872379/1145761776300000000000), (-94641475929611520199078338615926572629282329/439094060874598523208475700000000000000000), (-774208905117689872379/1145761776300000000000), (-189282981232678507730662437053752639189282329/878188121749197046416951400000000000000000)]
    bernstein := [(85415281166158620886754775157802960979729545801/2125031510656813943408541302784000000000000000000000), (23438811598020472862364431117716686379226177/41504521692515897332198072320000000000000000000), (66405524721723466524469101020915124533082957/89926463667117777553095823360000000000000000000), (2957827886858852202557645793000072877901/5269128730495182278501708400000000000000000), (29373455467332505759821899493930717671/878188121749197046416951400000000000000000)]
    reserve := (16723897/500000000000) }

theorem tilt_017_005_valid : tilt_017_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_005]
  · intro i; fin_cases i <;> norm_num [tilt_017_005]
  · norm_num [tilt_017_005]
  · norm_num [tilt_017_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_005]

def tilt_017_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(17529/25000000), 0, (163479/50000000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421323/10000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(831257154998132685641855350546736677843/4394779180906949046662104200000000000000000), (-774215869454886248219/1145761776300000000000), (-473620381125185686665574040813062724139322157/2197389590453474523331052100000000000000000), (-774215869454886248219/1145761776300000000000), (-947241593507526371463833723481475995015322157/4394779180906949046662104200000000000000000)]
    bernstein := [(231494823891197239115372691479125284595321605237/1181605121640688462449426300928000000000000000000000), (16626559072783238814593861335601068356684749/23078225032044696532215357440000000000000000000), (1207172277562426620172501607458673221374047443/1350076164374614747134598410240000000000000000000), (6302587424163537330297049518097960458811/8789558361813898093324208400000000000000000), (831257154998132685641855350546736677843/4394779180906949046662104200000000000000000)]
    reserve := (11821657/62500000000) }

theorem tilt_017_006_valid : tilt_017_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_006]
  · intro i; fin_cases i <;> norm_num [tilt_017_006]
  · norm_num [tilt_017_006]
  · norm_num [tilt_017_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_006]

def tilt_017_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(903/2500000), 0, (40883/12500000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (266629/6250000), (421139/10000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(1678009905138031489874789504338717890883/49398356186837218551659354400000000000000000), (-483582748383189533247/715792213400000000000), (-483965426110231393293149790358569185424032647/2245379826674419025075425200000000000000000), (-483582748383189533247/715792213400000000000), (-10647241052434995790480785262678026418046609117/49398356186837218551659354400000000000000000)]
    bernstein := [(1606700661532095366460714054215738626096244023791/39844562105360787138480583999488000000000000000000000), (54957201671138173884810222293370873638934629/97276762952540984224806113280000000000000000000), (11210944729855076497508121669046684129374898483/15175175020596393539069753671680000000000000000000), (6937682722951670368417278930144775107877/12349589046709304637914838600000000000000000), (1678009905138031489874789504338717890883/49398356186837218551659354400000000000000000)]
    reserve := (16984471/500000000000) }

theorem tilt_017_007_valid : tilt_017_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_007]
  · intro i; fin_cases i <;> norm_num [tilt_017_007]
  · norm_num [tilt_017_007]
  · norm_num [tilt_017_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_007]

def tilt_017_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(17529/25000000), 0, (163479/50000000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (4269747/100000000), (421139/10000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(4144823656400640085692028901438806598691/21973779122726048950173782200000000000000000), (-3873463194980725239253/5731281398100000000000), (-7104258492561511394153613803681066840565203927/32960668684089073425260673300000000000000000), (-3873463194980725239253/5731281398100000000000), (-14208529419593991990227484683448837997550203927/65921337368178146850521346600000000000000000)]
    bernstein := [(10410353354026106692664608403037152930621666617421/53171947886288283470717131948032000000000000000000000), (249318273021176380443162504904604784333937389/346171535718022678845814661120000000000000000000), (18100891354090812329648844763441210948628421673/20251034839504326712480157675520000000000000000000), (94482484792939953212162214852500917807771/131842674736356293701042693200000000000000000), (4144823656400640085692028901438806598691/21973779122726048950173782200000000000000000)]
    reserve := (18862589/100000000000) }

theorem tilt_017_008_valid : tilt_017_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_008]
  · intro i; fin_cases i <;> norm_num [tilt_017_008]
  · norm_num [tilt_017_008]
  · norm_num [tilt_017_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_008]

def tilt_017_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(903/2500000), 0, (40883/12500000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (4209551/100000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(1465149654595651575402112910087817718449/43909416518362463635561095400000000000000000), (-774208905117689872379/1145761776300000000000), (-4732074924132227558385879589074380196342281551/21954708259181231817780547700000000000000000), (-774208905117689872379/1145761776300000000000), (-9464151313414109712423334580261670480502281551/43909416518362463635561095400000000000000000)]
    bernstein := [(4262238851800966920071667753743587073726060533919/106251600773442550774897179623424000000000000000000000), (1171774332172840266611844139838286555386746013/2075226577606299819822210539520000000000000000000), (9959748661714882851280757825560857126125251249/13488972754440948828844368506880000000000000000000), (147870288669325142320607094732560692632569/263456499110174781813366572400000000000000000), (1465149654595651575402112910087817718449/43909416518362463635561095400000000000000000)]
    reserve := (667351/20000000000) }

theorem tilt_017_009_valid : tilt_017_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_009]
  · intro i; fin_cases i <;> norm_num [tilt_017_009]
  · norm_num [tilt_017_009]
  · norm_num [tilt_017_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_009]

def tilt_017_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(17529/25000000), 0, (163479/50000000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (4213231/100000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(10911852929417590260907655877803998870609/43947802239972101781334567400000000000000000), (-774215869454886248219/1145761776300000000000), (-4736202336099025794333266744688574109773129391/21973901119986050890667283700000000000000000), (-774215869454886248219/1145761776300000000000), (-9472415584050981006256794397033026023545129391/43947802239972101781334567400000000000000000)]
    bernstein := [(27124374256199240145269016553699607258999482330879/106344486188263815224918481567744000000000000000000000), (1619237815023594448352789273463649181588131933/2077040745864527641111689093120000000000000000000), (12870226873764808205334590797100292341037955409/13500764848119429667225979105280000000000000000000), (204673344040829274685729388939943895545529/263686813439832610688007404400000000000000000), (10911852929417590260907655877803998870609/43947802239972101781334567400000000000000000)]
    reserve := (31036401/125000000000) }

theorem tilt_017_010_valid : tilt_017_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_010]
  · intro i; fin_cases i <;> norm_num [tilt_017_010]
  · norm_num [tilt_017_010]
  · norm_num [tilt_017_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_010]

def tilt_017_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(449/3125000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(903/2500000), 0, (40883/12500000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(593502420502115436405286189738609508707/13178579684479401418120291800000000000000000), (-774208905117689872379/1145761776300000000000), (-1420242504993677467812363322666001060110491293/6589289842239700709060145900000000000000000), (-774208905117689872379/1145761776300000000000), (-2840485603489775437740163050618191858830491293/13178579684479401418120291800000000000000000)]
    bernstein := [(183479763619541301609673433836494498265696026213/3543267274675044313181257203712000000000000000000000), (39883681838852612164469836836792665860180651/69204438958496959241821429760000000000000000000), (3036466830553398147726588671223649938084299107/4048459679072072115646553640960000000000000000000), (15101019788819418872404478878181483851789/26357159368958802836240583600000000000000000), (593502420502115436405286189738609508707/13178579684479401418120291800000000000000000)]
    reserve := (9007077/200000000000) }

theorem tilt_017_011_valid : tilt_017_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_011]
  · intro i; fin_cases i <;> norm_num [tilt_017_011]
  · norm_num [tilt_017_011]
  · norm_num [tilt_017_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_011]

def tilt_017_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (133/3125000), 0, 0], ![0, 0, 0, 0, 0], ![(17529/25000000), 0, (163479/50000000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (467/12500000), (21723/390625), (13423/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(246631571425231392190861149381781012145863/2051465570883960154087392090200000000000000000), (-774215869454886248219/1145761776300000000000), (-221084265433077857853091093605090967446943854137/1025732785441980077043696045100000000000000000), (-774215869454886248219/1145761776300000000000), (-442168777497727140937574378071331316674899854137/2051465570883960154087392090200000000000000000)]
    bernstein := [(630392442547670422787651245676810518142913654715753/4964117451819737082766941342400512000000000000000000000), (63168252072700429272379036873046177682140942731/96955418980854239897791823093760000000000000000000), (520066264694246246275318499612823571928745259463/630210223375552559335646850109440000000000000000000), (7977692860050343630951583381914039710028303/12308793425303760924524352541200000000000000000), (246631571425231392190861149381781012145863/2051465570883960154087392090200000000000000000)]
    reserve := (24044427/200000000000) }

theorem tilt_017_012_valid : tilt_017_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_012]
  · intro i; fin_cases i <;> norm_num [tilt_017_012]
  · norm_num [tilt_017_012]
  · norm_num [tilt_017_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_012]

def tilt_017_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(903/2500000), 0, (40883/12500000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (2779169/50000000), (13423/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(33100600064988330003030154704803346259093/316129506655977537285906239137500000000000000), (-774208905117689872379/1145761776300000000000), (-34068945560878857976266334165442952200933740907/158064753327988768642953119568750000000000000), (-774208905117689872379/1145761776300000000000), (-68137924222357780940862671361040609205213740907/316129506655977537285906239137500000000000000)]
    bernstein := [(123151676617102719722818797140122001443849528061831/1104952711904327673790354735366144000000000000000000000), (219605150771833275331669012516364499066707830917/345297722470102398059485854801920000000000000000000), (78634079006027705015959824564660747013239628693/97114984444716299454230396663040000000000000000000), (6399558797232863435893594909136421207550351/10116144212991281193148999652400000000000000000), (33100600064988330003030154704803346259093/316129506655977537285906239137500000000000000)]
    reserve := (52352911/500000000000) }

theorem tilt_017_013_valid : tilt_017_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_013]
  · intro i; fin_cases i <;> norm_num [tilt_017_013]
  · norm_num [tilt_017_013]
  · norm_num [tilt_017_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_013]

def tilt_017_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(17529/25000000), 0, (163479/50000000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (2781919/50000000), (13423/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(7003500818739389372866222532644448392621/39555289774879216347983470907812500000000000), (-774215869454886248219/1145761776300000000000), (-4262829313896799141862785822900366990715951129/19777644887439608173991735453906250000000000), (-774215869454886248219/1145761776300000000000), (-8525665631294417023114944512023266625880294879/39555289774879216347983470907812500000000000)]
    bernstein := [(25414836128088745090104005951982752111736056815307/138255758436612497204343719968768000000000000000000000), (244834680881365592809679515542095686683689164667/345639396091531243010859299921920000000000000000000), (10718258867830445874468152653043207428394720071/12151385018842895262100522262880000000000000000000), (7138568180518327263198100849154978735551601/10126154182369079385083768552400000000000000000), (7003500818739389372866222532644448392621/39555289774879216347983470907812500000000000)]
    reserve := (35411197/200000000000) }

theorem tilt_017_014_valid : tilt_017_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_014]
  · intro i; fin_cases i <;> norm_num [tilt_017_014]
  · norm_num [tilt_017_014]
  · norm_num [tilt_017_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_014]

def tilt_017_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(449/3125000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(903/2500000), 0, (40883/12500000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (21723/390625), (13423/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(593502420502115436405286189738609508707/13178579684479401418120291800000000000000000), (-774208905117689872379/1145761776300000000000), (-1420242504993677467812363322666001060110491293/6589289842239700709060145900000000000000000), (-774208905117689872379/1145761776300000000000), (-2840485603489775437740163050618191858830491293/13178579684479401418120291800000000000000000)]
    bernstein := [(183479763619541301609673433836494498265696026213/3543267274675044313181257203712000000000000000000000), (39883681838852612164469836836792665860180651/69204438958496959241821429760000000000000000000), (3036466830553398147726588671223649938084299107/4048459679072072115646553640960000000000000000000), (15101019788819418872404478878181483851789/26357159368958802836240583600000000000000000), (593502420502115436405286189738609508707/13178579684479401418120291800000000000000000)]
    reserve := (9007077/200000000000) }

theorem tilt_017_015_valid : tilt_017_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_015]
  · intro i; fin_cases i <;> norm_num [tilt_017_015]
  · norm_num [tilt_017_015]
  · norm_num [tilt_017_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_015]

def tilt_017_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (133/3125000), 0, 0], ![0, 0, 0, 0, 0], ![(17529/25000000), 0, (163479/50000000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (467/12500000), (21723/390625), (13423/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(246631571425231392190861149381781012145863/2051465570883960154087392090200000000000000000), (-774215869454886248219/1145761776300000000000), (-221084265433077857853091093605090967446943854137/1025732785441980077043696045100000000000000000), (-774215869454886248219/1145761776300000000000), (-442168777497727140937574378071331316674899854137/2051465570883960154087392090200000000000000000)]
    bernstein := [(630392442547670422787651245676810518142913654715753/4964117451819737082766941342400512000000000000000000000), (63168252072700429272379036873046177682140942731/96955418980854239897791823093760000000000000000000), (520066264694246246275318499612823571928745259463/630210223375552559335646850109440000000000000000000), (7977692860050343630951583381914039710028303/12308793425303760924524352541200000000000000000), (246631571425231392190861149381781012145863/2051465570883960154087392090200000000000000000)]
    reserve := (24044427/200000000000) }

theorem tilt_017_016_valid : tilt_017_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_016]
  · intro i; fin_cases i <;> norm_num [tilt_017_016]
  · norm_num [tilt_017_016]
  · norm_num [tilt_017_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_016]

def tilt_017_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(903/2500000), 0, (40883/12500000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (2779169/50000000), (13423/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(264723508913008913411171408679226100528369/2529036053247820298287249913100000000000000000), (-774208905117689872379/1145761776300000000000), (-272551564568322470707857286393372576808139471631/1264518026623910149143624956550000000000000000), (-774208905117689872379/1145761776300000000000), (-545103393860153854424627983958153832842379471631/2529036053247820298287249913100000000000000000)]
    bernstein := [(984929272627306327758693319447219782904813238646523/8839621695234621390322837882929152000000000000000000000), (219594051649382696527795727776029688717356438417/345297722470102398059485854801920000000000000000000), (629047659185291051614416931991190571221215485169/776919875557730395633843173304320000000000000000000), (6399233630805272529441315593299618529372851/10116144212991281193148999652400000000000000000), (264723508913008913411171408679226100528369/2529036053247820298287249913100000000000000000)]
    reserve := (104673679/1000000000000) }

theorem tilt_017_017_valid : tilt_017_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_017]
  · intro i; fin_cases i <;> norm_num [tilt_017_017]
  · norm_num [tilt_017_017]
  · norm_num [tilt_017_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_017]

def tilt_017_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(17529/25000000), 0, (163479/50000000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (5563839/100000000), (13423/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(1758436912091906360828953200016719485221/8790065974273881694468538795312500000000000), (-774215869454886248219/1145761776300000000000), (-947295371244403610384361244899452086747108529/4395032987136940847234269397656250000000000), (-774215869454886248219/1145761776300000000000), (-1894592500925719312675083318752104190213702279/8790065974273881694468538795312500000000000)]
    bernstein := [(57187419907942310237016365836269445613360892555563/276511566571206293149771276075008000000000000000000000), (505563640845408131677035066574426488817756643803/691278916428015732874428190187520000000000000000000), (814640670576230685889808196051502618063427557/900102755765645485513578372640000000000000000000), (4914261502959661627625550320123870208496603/6750770668242341141351837794800000000000000000), (1758436912091906360828953200016719485221/8790065974273881694468538795312500000000000)]
    reserve := (50012051/250000000000) }

theorem tilt_017_018_valid : tilt_017_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_018]
  · intro i; fin_cases i <;> norm_num [tilt_017_018]
  · norm_num [tilt_017_018]
  · norm_num [tilt_017_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_018]

def tilt_017_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(52791/100000000), 0, (40883/12500000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (21723/390625), (6711/50000000)]
    alternative := (.spike 4 true false)
    polynomial := [(144693431797707744352457032783114427329/2196266315591180881497064200000000000000000), (-4032355648961203861/5967064678125000000), (-236707014537284830836711601852535900671061171/1098133157795590440748532100000000000000000), (-4032355648961203861/5967064678125000000), (-473414173768001459381167556162104584456549671/2196266315591180881497064200000000000000000)]
    bernstein := [(42893460386895663453787218840608302259553606911/590500550804445662563247587328000000000000000000000), (3443874099613412445294386156685820314002011/5766606941449664673469214720000000000000000000), (520143482710602343499714048302473653964407629/674693012149610766795898122240000000000000000000), (1304199738763253569989421306357393077329/2196266315591180881497064200000000000000000), (144693431797707744352457032783114427329/2196266315591180881497064200000000000000000)]
    reserve := (65881551/1000000000000) }

theorem tilt_017_019_valid : tilt_017_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_019]
  · intro i; fin_cases i <;> norm_num [tilt_017_019]
  · norm_num [tilt_017_019]
  · norm_num [tilt_017_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_019]

def tilt_017_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/320), 0⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(10689/20000000), 0, (163479/50000000), 0, 0]] i.1) i.2
    mu := ![(5657721/100000000), (1/100000000), (853581/20000000), (421139/10000000), (1/100000000), (21723/390625), (6711/50000000)]
    alternative := (.spike 4 true true)
    polynomial := [(524871869746836663071130275281229427329/2196266315591180881497064200000000000000000), (-129035327566960495681/190946069700000000000), (-236706637640884746553320142438768043770061171/1098133157795590440748532100000000000000000), (-129035327566960495681/190946069700000000000), (-157804600051213079981101118669270456256516557/732088771863726960499021400000000000000000)]
    bernstein := [(435335534634149427979385265492757202693319820733/1771501652413336987689742761984000000000000000000000), (26652552610699755096689007089767076319477691/34599641648697988040815288320000000000000000000), (636934382030399808149347539845118275985407629/674693012149610766795898122240000000000000000000), (3368755397322632739577209970215755207783/4392532631182361762994128400000000000000000), (524871869746836663071130275281229427329/2196266315591180881497064200000000000000000)]
    reserve := (59745927/250000000000) }

theorem tilt_017_020_valid : tilt_017_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_017_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_017_020]
  · intro i; fin_cases i <;> norm_num [tilt_017_020]
  · norm_num [tilt_017_020]
  · norm_num [tilt_017_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_017_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_017_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_017_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_017_020]

def tiltBundle017_row : Alternative → Row
  | .zero => tilt_017_000
  | (.spike 0 false false) => tilt_017_001
  | (.spike 0 false true) => tilt_017_002
  | (.spike 0 true false) => tilt_017_003
  | (.spike 0 true true) => tilt_017_004
  | (.spike 1 false false) => tilt_017_005
  | (.spike 1 false true) => tilt_017_006
  | (.spike 1 true false) => tilt_017_007
  | (.spike 1 true true) => tilt_017_008
  | (.spike 2 false false) => tilt_017_009
  | (.spike 2 false true) => tilt_017_010
  | (.spike 2 true false) => tilt_017_011
  | (.spike 2 true true) => tilt_017_012
  | (.spike 3 false false) => tilt_017_013
  | (.spike 3 false true) => tilt_017_014
  | (.spike 3 true false) => tilt_017_015
  | (.spike 3 true true) => tilt_017_016
  | (.spike 4 false false) => tilt_017_017
  | (.spike 4 false true) => tilt_017_018
  | (.spike 4 true false) => tilt_017_019
  | (.spike 4 true true) => tilt_017_020

def tiltBundle017 : TiltBundle where
  interval := ⟨(-1/320), 0⟩
  lambda := ![(14574473/100000000), (14574473/100000000), (8445829/100000000), (3592079/25000000), (3592079/25000000), (16670749/100000000), (16997843/100000000)]
  row := tiltBundle017_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_017_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_017_001_valid | exact tilt_017_002_valid | exact tilt_017_003_valid | exact tilt_017_004_valid | exact tilt_017_005_valid | exact tilt_017_006_valid | exact tilt_017_007_valid | exact tilt_017_008_valid | exact tilt_017_009_valid | exact tilt_017_010_valid | exact tilt_017_011_valid | exact tilt_017_012_valid | exact tilt_017_013_valid | exact tilt_017_014_valid | exact tilt_017_015_valid | exact tilt_017_016_valid | exact tilt_017_017_valid | exact tilt_017_018_valid | exact tilt_017_019_valid | exact tilt_017_020_valid
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
