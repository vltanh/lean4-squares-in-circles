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

def tilt_010_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8451437/100000000), 0, (8479401/25000000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := .zero
    polynomial := [(-27581271869610982124532130371422332018569091/37350223108789109407513056022500000000000000), (-359917191613526982499/25837834841900000000), (-1145743195326232709136539931976984970668569091/18675111554394554703756528011250000000000000), (-359917191613526982499/25837834841900000000), (-2263905118782854436148547733582547609318569091/37350223108789109407513056022500000000000000)]
    bernstein := [(26631569532523640786794180741801959858601817/470727734934154437332841469132800000000000000), (21004205973430779718182485535358736745378181/326894260370940581481139909120000000000000000), (46967179291968774911824812039067484188005305483/717124283688750900624250675632000000000000000000), (2003935844281997864462860674121461729908196281/33200198318923652806678272020000000000000000000), (18260613340058438867859753515948703618526702709/373502231087891094075130560225000000000000000000)]
    reserve := (24445119493/500000000000) }

theorem tilt_010_000_valid : tilt_010_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_000]
  · intro i; fin_cases i <;> norm_num [tilt_010_000]
  · norm_num [tilt_010_000]
  · norm_num [tilt_010_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_000]

def tilt_010_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(12523/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8414351/100000000), 0, (4240757/12500000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-55168512654625701039617934488076459958427507/74700446217578218815026112045000000000000000), (-179958781990436536071771/12918917420950000000000), (-2291494610814670555827914086041108513532652507/37350223108789109407513056022500000000000000), (-179958781990436536071771/12918917420950000000000), (-4527820708974715410616210237594140567106877507/74700446217578218815026112045000000000000000)]
    bernstein := [(53186365163776883222189743329111358739712409/941455469868308874665682938265600000000000000), (41955264388333127182696883076623139964232437/653788520741881162962279818240000000000000000), (93818099874493462807469070390916035989902119691/1434248567377501801248501351264000000000000000000), (4002503230830297550647537339615096800586396137/66400396637847305613356544040000000000000000000), (36460970348901805552038356309839145407868551093/747004462175782188150261120450000000000000000000)]
    reserve := (12202393759/250000000000) }

theorem tilt_010_001_valid : tilt_010_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_001]
  · intro i; fin_cases i <;> norm_num [tilt_010_001]
  · norm_num [tilt_010_001]
  · norm_num [tilt_010_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_001]

def tilt_010_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (7419/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2122131/25000000), 0, (33909153/100000000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (6511/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-359102301735499277083583538232832591995538326283/486374605322651782704635015524995000000000000000), (-359917559803012379513671/25837834841900000000000), (-14919821478189358586031491666269617801873595426283/243187302661325891352317507762497500000000000000), (-359917559803012379513671/25837834841900000000000), (-29480540654643217894979399794306403011751652526283/486374605322651782704635015524995000000000000000)]
    bernstein := [(347594811280513043860691507120301974466850198321/6129816564312559082948261611047321600000000000000), (274069613127830671571273141984828449321639898453/4256817058550388252047403896560640000000000000000), (612815919567270981392469607557414722784511422316579/9338392422194914227928992298079904000000000000000000), (443238757793883940712182086036610074824850002267/7327677669644471302518041665160000000000000000000), (238416226644856571076452611445605461597940994887117/4863746053226517827046350155249950000000000000000000)]
    reserve := (24509526611/500000000000) }

theorem tilt_010_002_valid : tilt_010_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_002]
  · intro i; fin_cases i <;> norm_num [tilt_010_002]
  · norm_num [tilt_010_002]
  · norm_num [tilt_010_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_002]

def tilt_010_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8414351/100000000), 0, (4240757/12500000), 0, 0]] i.1) i.2
    mu := ![(2875621/25000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-330795195425975614769586779944392341428472011/447996838002511510616003925720000000000000000), (-179958781990436536071771/12918917420950000000000), (-13742589521260120555366517359885817832881072011/223998419001255755308001962860000000000000000), (-179958781990436536071771/12918917420950000000000), (-27154383847094265495963447939827243324333672011/447996838002511510616003925720000000000000000)]
    bernstein := [(4157423928720349878668347095885487859810390141/73399801938331485899326083189964800000000000000), (9835438686768862211326993684581831871904244139/152916254038190595623596006645760000000000000000), (563907332329245717137485187419924088168032719443/8601539289648221003827275373824000000000000000000), (72186122841606965546723677593087682952212826003/1194658234673364028309343801920000000000000000000), (219316809302099528162311311475866457446627815789/4479968380025115106160039257200000000000000000000)]
    reserve := (48954990459/1000000000000) }

theorem tilt_010_003_valid : tilt_010_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_003]
  · intro i; fin_cases i <;> norm_num [tilt_010_003]
  · norm_num [tilt_010_003]
  · norm_num [tilt_010_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_003]

def tilt_010_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2122131/25000000), 0, (33909153/100000000), 0, 0]] i.1) i.2
    mu := ![(2302611/20000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-386217837901171305109342057590439945798867129/523143314815638026809194134925000000000000000), (-359917559803012379513671/25837834841900000000000), (-16047691139979713634188571196996028527455367129/261571657407819013404597067462500000000000000), (-359917559803012379513671/25837834841900000000000), (-31709164442058255963267800336401617109111867129/523143314815638026809194134925000000000000000)]
    bernstein := [(4865695451661982607823931921740221955997255199/85711800699394134312418367066112000000000000000), (11507883249788463104449555483107962354846112721/178566251457071113150871598054400000000000000000), (659767433910067689912585493976604819108280581377/10044351644460250114736527390560000000000000000000), (1431704882397092271210591117210918215294609563/23644895584887594432053972200000000000000000000), (256763312206345428381553081053645611470075917071/5231433148156380268091941349250000000000000000000)]
    reserve := (9816174839/200000000000) }

theorem tilt_010_004_valid : tilt_010_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_004]
  · intro i; fin_cases i <;> norm_num [tilt_010_004]
  · norm_num [tilt_010_004]
  · norm_num [tilt_010_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_004]

def tilt_010_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8414351/100000000), 0, (4240757/12500000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (203049/20000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-1167375889071215519065464309442043114962663/1580178929939674008650630925000000000000000), (-179958781990436536071771/12918917420950000000000), (-48473591041975443516447219734707773779587663/790089464969837004325315462500000000000000), (-179958781990436536071771/12918917420950000000000), (-95779806194879671513828975159973504444212663/1580178929939674008650630925000000000000000)]
    bernstein := [(1120315299483812595365781402216071346035381/19915116606255091505947643904000000000000000), (2652611386361739339588651988070980217608099/41489826263031440637390924800000000000000000), (1977369495629061620394106078144124807999303519/30339435454841740966092113760000000000000000000), (253001869979113179645381934844123321311817999/4213810479839130689735015800000000000000000000), (767539843296013058036593227865298932176624737/15801789299396740086506309250000000000000000000)]
    reserve := (48572970361/1000000000000) }

theorem tilt_010_005_valid : tilt_010_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_005]
  · intro i; fin_cases i <;> norm_num [tilt_010_005]
  · norm_num [tilt_010_005]
  · norm_num [tilt_010_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_005]

def tilt_010_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2122131/25000000), 0, (33909153/100000000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (1016251/100000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-551647058581258644204216897683746512693705571/747374379955068407213099128837500000000000000), (-359917559803012379513671/25837834841900000000000), (-22925982287253319445053738860834180050119455571/373687189977534203606549564418750000000000000), (-359917559803012379513671/25837834841900000000000), (-45300317515925380245903260823984613587545205571/747374379955068407213099128837500000000000000)]
    bernstein := [(536173290853174812734555056924227962304127577/9419216800910646756753397020672000000000000000), (422561668049886375705416836018427326708287361/6541122778410171358856525708800000000000000000), (944773200450186665012643886421296792819098548723/14349588095137313418491503273680000000000000000000), (683521713240235948105384803479590448089198279/11259877664106492010743489700000000000000000000), (367965348794039990455227082167862438648711720229/7473743799550684072130991288375000000000000000000)]
    reserve := (9846881527/200000000000) }

theorem tilt_010_006_valid : tilt_010_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_006]
  · intro i; fin_cases i <;> norm_num [tilt_010_006]
  · norm_num [tilt_010_006]
  · norm_num [tilt_010_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_006]

def tilt_010_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8414351/100000000), 0, (4240757/12500000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (6524271/100000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-1572068474192949105009813889806553876519381/2128013333148816638350669025000000000000000), (-27683286663837976921393/1987334768850000000000), (-195837144497600859623262552748584230767433143/3192019999723224957526003537500000000000000), (-27683286663837976921393/1987334768850000000000), (-386958083572622871931495663827748799905308143/6384039999446449915052007075000000000000000)]
    bernstein := [(1508987994212136996829362330282083599398047/26819515731007855232874893312000000000000000), (32155378680044188078253651060177899793990417/502865919956397285616404249600000000000000000), (7989993762800881388632299878034679725974588759/122573567989371838368998535840000000000000000000), (3066978580136764845881037017888372030814832117/51072319995571599320416056600000000000000000000), (3101602670638690377656398252394636522261633257/63840399994464499150520070750000000000000000000)]
    reserve := (3036481083/62500000000) }

theorem tilt_010_007_valid : tilt_010_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_007]
  · intro i; fin_cases i <;> norm_num [tilt_010_007]
  · norm_num [tilt_010_007]
  · norm_num [tilt_010_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_007]

def tilt_010_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2122131/25000000), 0, (33909153/100000000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262763/50000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-236329886475055342332930142214352563625612859/320175582386383658352847870350000000000000000), (-1079857358146658792387031/77520964945900000000000), (-9821490791065692826439271630240887683316112859/160087791193191829176423935175000000000000000), (-1079857358146658792387031/77520964945900000000000), (-19406651695656330310545613118267422803006612859/320175582386383658352847870350000000000000000)]
    bernstein := [(229656502521606874531772175873182997281232833/4035197493706546044963891929088000000000000000), (180997048133241199526586637321992414076034269/2802220481740656975669369395200000000000000000), (404677514668012073007465808378365042628655144867/6147371181818566240374679110720000000000000000000), (292770164811599692655278133164166179726816291/4823737587742126679515598800000000000000000000), (157602251852474888376939029983207014285957225341/3201755823863836583528478703500000000000000000000)]
    reserve := (4922369491/100000000000) }

theorem tilt_010_008_valid : tilt_010_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_008]
  · intro i; fin_cases i <;> norm_num [tilt_010_008]
  · norm_num [tilt_010_008]
  · norm_num [tilt_010_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_008]

def tilt_010_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8414351/100000000), 0, (4240757/12500000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (203049/20000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-7004255386185260144779464063826094174583953/9481073579638044051903785550000000000000000), (-179958781990436536071771/12918917420950000000000), (-290841546303610628129069996615420478162333953/4740536789819022025951892775000000000000000), (-179958781990436536071771/12918917420950000000000), (-574678837221035996113360529167014862150083953/9481073579638044051903785550000000000000000)]
    bernstein := [(6721891124049304177167871720036566773708611/119490699637530549035685863424000000000000000), (5305222306901775405697200111577441071944423/82979652526062881274781849600000000000000000), (11864215954815272795142102604233449658581217289/182036612729050445796552682560000000000000000000), (506003692910234328669273379367230186933186723/8427620959678261379470031600000000000000000000), (4605238531793056671245054975811497812533595447/94810735796380440519037855500000000000000000000)]
    reserve := (6071620599/125000000000) }

theorem tilt_010_009_valid : tilt_010_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_009]
  · intro i; fin_cases i <;> norm_num [tilt_010_009]
  · norm_num [tilt_010_009]
  · norm_num [tilt_010_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_009]

def tilt_010_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2122131/25000000), 0, (33909153/100000000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (1016251/100000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-2206576565011833941119286141150529342027834409/2989497519820273628852396515350000000000000000), (-359917559803012379513671/25837834841900000000000), (-91703917479700077144517373993752263491730834409/1494748759910136814426198257675000000000000000), (-359917559803012379513671/25837834841900000000000), (-181201258394388320347915461846353997641433834409/2989497519820273628852396515350000000000000000)]
    bernstein := [(2144844864484307515006779072294849062927352683/37676867203642587027013588082688000000000000000), (1690351696018351224099900390333819685556040319/26164491113640685435426102835200000000000000000), (3779322535569727575028861543654386396378344490017/57398352380549253673966013094720000000000000000000), (2734266639498221383084277140567025322034962241/45039510656425968042973958800000000000000000000), (1471980433840119646571936695882492640522870193791/29894975198202736288523965153500000000000000000000)]
    reserve := (49238389531/1000000000000) }

theorem tilt_010_010_valid : tilt_010_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_010]
  · intro i; fin_cases i <;> norm_num [tilt_010_010]
  · norm_num [tilt_010_010]
  · norm_num [tilt_010_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_010]

def tilt_010_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3031/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8414351/100000000), 0, (4240757/12500000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-55186328363260745959878566330761120869718007/74700446217578218815026112045000000000000000), (-179958781990436536071771/12918917420950000000000), (-2291512426523305600748174717883793174443943007/37350223108789109407513056022500000000000000), (-179958781990436536071771/12918917420950000000000), (-4527838524683350455536470869436825228018168007/74700446217578218815026112045000000000000000)]
    bernstein := [(52954760951521299258801529374210766892935909/941455469868308874665682938265600000000000000), (41794923010617722900351196492461191762617937/653788520741881162962279818240000000000000000), (93467362018595333462298011303983116629326046191/1434248567377501801248501351264000000000000000000), (3986308751681041718130622994614740032223331637/66400396637847305613356544040000000000000000000), (36279232305115712320459650882612919451794160593/747004462175782188150261120450000000000000000000)]
    reserve := (9713257187/200000000000) }

theorem tilt_010_011_valid : tilt_010_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_011]
  · intro i; fin_cases i <;> norm_num [tilt_010_011]
  · norm_num [tilt_010_011]
  · norm_num [tilt_010_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_011]

def tilt_010_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (449/50000000), 0, 0], ![0, 0, 0, 0, 0], ![(2122131/25000000), 0, (33909153/100000000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (197/25000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-434491018911959422986184940268824513550760288261/588639516194516364262405762914600000000000000000), (-359917559803012379513671/25837834841900000000000), (-18056740613514387829453627122564918424446028288261/294319758097258182131202881457300000000000000000), (-359917559803012379513671/25837834841900000000000), (-35678990208116816235921069304861012335341296288261/588639516194516364262405762914600000000000000000)]
    bernstein := [(422187619245892687796789254109236212923471452607/7418669102562273932365581553532928000000000000000), (332739145032560926920891656504390713472139205651/5151853543446023564142764967731200000000000000000), (743949526409371191195380759472860970185299803005693/11301878710934714193838190647960320000000000000000000), (538220746328539370242112592568936457516717304589/8868391957732826580224568932800000000000000000000), (289728579201761334696636637261170403502773303449539/5886395161945163642624057629146000000000000000000000)]
    reserve := (49220035561/1000000000000) }

theorem tilt_010_012_valid : tilt_010_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_012]
  · intro i; fin_cases i <;> norm_num [tilt_010_012]
  · norm_num [tilt_010_012]
  · norm_num [tilt_010_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_012]

def tilt_010_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8414351/100000000), 0, (4240757/12500000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (1107519/100000000), (237593/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-1470880078620963679889354509731498816617357279/1991017755631908668360874373650000000000000000), (-179958781990436536071771/12918917420950000000000), (-61076480771430690064222477639440579260065607279/995508877815954334180437186825000000000000000), (-179958781990436536071771/12918917420950000000000), (-120682081464240416448555600769149659703513857279/1991017755631908668360874373650000000000000000)]
    bernstein := [(1411693949359418417527944152588226725406255373/25092949929440916632634281336832000000000000000), (1114163180118935118042326387843815231381384489/17425659673222858772662695372800000000000000000), (2491630595582081545121589959456157302239503748327/38227540908132646432528787974080000000000000000000), (106267515782679391017027645810816223561912233389/1769793560561696594098554998800000000000000000000), (967176603690856758014047556084719418359361896921/19910177556319086683608743736500000000000000000000)]
    reserve := (24288497703/500000000000) }

theorem tilt_010_013_valid : tilt_010_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_013]
  · intro i; fin_cases i <;> norm_num [tilt_010_013]
  · norm_num [tilt_010_013]
  · norm_num [tilt_010_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_013]

def tilt_010_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2122131/25000000), 0, (33909153/100000000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (554313/50000000), (237593/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-10297461396660460026568521193660969449636554339/13951054882567488824653752209700000000000000000), (-359917559803012379513671/25837834841900000000000), (-427953708530704693433596485699022712624862554339/6975527441283744412326876104850000000000000000), (-359917559803012379513671/25837834841900000000000), (-845609955664748926840624450204384455800088554339/13951054882567488824653752209700000000000000000)]
    bernstein := [(10008608182350642261058961908118164647151193593/175826217843065951463943904772096000000000000000), (7887850123108213255720517228761094205791110949/122101540168795799627738822758400000000000000000), (17635838923336529727985345089844178686409565728107/267860253745295785433352042426240000000000000000000), (12759123763935965446894897874100525709504162811/210185384294802091520207189600000000000000000000), (6868713274389624076350824260965140654200587187861/139510548825674888246537522097000000000000000000000)]
    reserve := (49234364943/1000000000000) }

theorem tilt_010_014_valid : tilt_010_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_014]
  · intro i; fin_cases i <;> norm_num [tilt_010_014]
  · norm_num [tilt_010_014]
  · norm_num [tilt_010_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_014]

def tilt_010_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3031/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8414351/100000000), 0, (4240757/12500000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-55186328363260745959878566330761120869718007/74700446217578218815026112045000000000000000), (-179958781990436536071771/12918917420950000000000), (-2291512426523305600748174717883793174443943007/37350223108789109407513056022500000000000000), (-179958781990436536071771/12918917420950000000000), (-4527838524683350455536470869436825228018168007/74700446217578218815026112045000000000000000)]
    bernstein := [(52954760951521299258801529374210766892935909/941455469868308874665682938265600000000000000), (41794923010617722900351196492461191762617937/653788520741881162962279818240000000000000000), (93467362018595333462298011303983116629326046191/1434248567377501801248501351264000000000000000000), (3986308751681041718130622994614740032223331637/66400396637847305613356544040000000000000000000), (36279232305115712320459650882612919451794160593/747004462175782188150261120450000000000000000000)]
    reserve := (9713257187/200000000000) }

theorem tilt_010_015_valid : tilt_010_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_015]
  · intro i; fin_cases i <;> norm_num [tilt_010_015]
  · norm_num [tilt_010_015]
  · norm_num [tilt_010_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_015]

def tilt_010_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (449/50000000), 0, 0], ![0, 0, 0, 0, 0], ![(2122131/25000000), 0, (33909153/100000000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (197/25000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-434491018911959422986184940268824513550760288261/588639516194516364262405762914600000000000000000), (-359917559803012379513671/25837834841900000000000), (-18056740613514387829453627122564918424446028288261/294319758097258182131202881457300000000000000000), (-359917559803012379513671/25837834841900000000000), (-35678990208116816235921069304861012335341296288261/588639516194516364262405762914600000000000000000)]
    bernstein := [(422187619245892687796789254109236212923471452607/7418669102562273932365581553532928000000000000000), (332739145032560926920891656504390713472139205651/5151853543446023564142764967731200000000000000000), (743949526409371191195380759472860970185299803005693/11301878710934714193838190647960320000000000000000000), (538220746328539370242112592568936457516717304589/8868391957732826580224568932800000000000000000000), (289728579201761334696636637261170403502773303449539/5886395161945163642624057629146000000000000000000000)]
    reserve := (49220035561/1000000000000) }

theorem tilt_010_016_valid : tilt_010_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_016]
  · intro i; fin_cases i <;> norm_num [tilt_010_016]
  · norm_num [tilt_010_016]
  · norm_num [tilt_010_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_016]

def tilt_010_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8414351/100000000), 0, (4240757/12500000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (1107519/100000000), (237593/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-91930005153726000020714540070653874423823619/124438609726994291772554648353125000000000000), (-179958781990436536071771/12918917420950000000000), (-954320012113583474760383683919367850534834811/15554826215874286471569331044140625000000000), (-179958781990436536071771/12918917420950000000000), (-7542630091754941798062354931284288929854854869/124438609726994291772554648353125000000000000)]
    bernstein := [(88230868716058640736308027775106591329786703/1568309370590057289539642583552000000000000000), (69635196598191514628976450328321666494187429/1089103729576428673291418460800000000000000000), (155726907500658332036149861662798080779772943997/2389221306758290402033049248380000000000000000000), (6641719518334026983448664023072418640437455329/110612097535106037131159687425000000000000000000), (60448535283297777324025533605243504919639231331/1244386097269942917725546483531250000000000000000)]
    reserve := (48576993439/1000000000000) }

theorem tilt_010_017_valid : tilt_010_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_017]
  · intro i; fin_cases i <;> norm_num [tilt_010_017]
  · norm_num [tilt_010_017]
  · norm_num [tilt_010_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_017]

def tilt_010_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2122131/25000000), 0, (33909153/100000000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (554313/50000000), (237593/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-5148721102488175845583743967592140076177149357/6975527441283744412326876104850000000000000000), (-359917559803012379513671/25837834841900000000000), (-213976844669510292549097726220273011663790149357/3487763720641872206163438052425000000000000000), (-359917559803012379513671/25837834841900000000000), (-422804968236532409252611708472953883251403149357/6975527441283744412326876104850000000000000000)]
    bernstein := [(5004428837122025310636197134157562755910258359/87913108921532975731971952386048000000000000000), (3944011424132594137164908277525648940665705787/61050770084397899813869411379200000000000000000), (8818108375010785263512743424737380441002666108741/133930126872647892716676021213120000000000000000000), (6379709722992173205477442428196962610934881093/105092692147401045760103594800000000000000000000), (3434454524379606602888382265342924087888438409243/69755274412837444123268761048500000000000000000000)]
    reserve := (24617884119/500000000000) }

theorem tilt_010_018_valid : tilt_010_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_018]
  · intro i; fin_cases i <;> norm_num [tilt_010_018]
  · norm_num [tilt_010_018]
  · norm_num [tilt_010_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_018]

def tilt_010_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(105219/1250000), 0, (4240757/12500000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-110372551184024050399688896445590537397860189/149400892435156437630052224090000000000000000), (-44989695776822596149147/3229729355237500000000), (-4583024747497655828701844095185025493016871489/74700446217578218815026112045000000000000000), (-44989695776822596149147/3229729355237500000000), (-9055676943811287607003999293924460448635882789/149400892435156437630052224090000000000000000)]
    bernstein := [(105910914623472588986998944515470245041973023/1882910939736617749331365876531200000000000000), (83590809516656213236901991221079845541666419/1307577041483762325924559636480000000000000000), (186936830102493578842548069766570770645554122157/2868497134755003602497002702528000000000000000000), (7972714675087724916817712623982286497992770799/132800793275694611226713088080000000000000000000), (72559554295573502067522495076890332967123929411/1494008924351564376300522240900000000000000000000)]
    reserve := (9713403061/200000000000) }

theorem tilt_010_019_valid : tilt_010_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_019]
  · intro i; fin_cases i <;> norm_num [tilt_010_019]
  · norm_num [tilt_010_019]
  · norm_num [tilt_010_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_019]

def tilt_010_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1697071/20000000), 0, (33909153/100000000), 0, 0]] i.1) i.2
    mu := ![(11507769/100000000), (1/100000000), (3262449/50000000), (253937/25000000), (1/100000000), (138509/12500000), (237593/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-110273138008525879779423300235579571374585189/149400892435156437630052224090000000000000000), (-359917557569304682464037/25837834841900000000000), (-4582925319373242670958651724370497097737346489/74700446217578218815026112045000000000000000), (-359917557569304682464037/25837834841900000000000), (-9055577500737959462137880148505414624100107789/149400892435156437630052224090000000000000000)]
    bernstein := [(107203211901840054797114990243409721554408023/1882910939736617749331365876531200000000000000), (84485479146083722540681110632848490067431419/1307577041483762325924559636480000000000000000), (188893875287175862588211159244363957213579247157/2868497134755003602497002702528000000000000000000), (8063076779949943893666303030716201448045295799/132800793275694611226713088080000000000000000000), (73573620629447733855225244865043371813085704411/1494008924351564376300522240900000000000000000000)]
    reserve := (4924577051/100000000000) }

theorem tilt_010_020_valid : tilt_010_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_010_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_010_020]
  · intro i; fin_cases i <;> norm_num [tilt_010_020]
  · norm_num [tilt_010_020]
  · norm_num [tilt_010_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_010_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_010_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_010_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_010_020]

def tiltBundle010_row : Alternative → Row
  | .zero => tilt_010_000
  | (.spike 0 false false) => tilt_010_001
  | (.spike 0 false true) => tilt_010_002
  | (.spike 0 true false) => tilt_010_003
  | (.spike 0 true true) => tilt_010_004
  | (.spike 1 false false) => tilt_010_005
  | (.spike 1 false true) => tilt_010_006
  | (.spike 1 true false) => tilt_010_007
  | (.spike 1 true true) => tilt_010_008
  | (.spike 2 false false) => tilt_010_009
  | (.spike 2 false true) => tilt_010_010
  | (.spike 2 true false) => tilt_010_011
  | (.spike 2 true true) => tilt_010_012
  | (.spike 3 false false) => tilt_010_013
  | (.spike 3 false true) => tilt_010_014
  | (.spike 3 true false) => tilt_010_015
  | (.spike 3 true true) => tilt_010_016
  | (.spike 4 false false) => tilt_010_017
  | (.spike 4 false true) => tilt_010_018
  | (.spike 4 true false) => tilt_010_019
  | (.spike 4 true true) => tilt_010_020

def tiltBundle010 : TiltBundle where
  interval := ⟨(-1/8), (-1/10)⟩
  lambda := ![(25045519/100000000), (25045519/100000000), (26403/1000000), (3031189/100000000), (3031189/100000000), (1584473/50000000), (38037337/100000000)]
  row := tiltBundle010_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_010_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_010_001_valid | exact tilt_010_002_valid | exact tilt_010_003_valid | exact tilt_010_004_valid | exact tilt_010_005_valid | exact tilt_010_006_valid | exact tilt_010_007_valid | exact tilt_010_008_valid | exact tilt_010_009_valid | exact tilt_010_010_valid | exact tilt_010_011_valid | exact tilt_010_012_valid | exact tilt_010_013_valid | exact tilt_010_014_valid | exact tilt_010_015_valid | exact tilt_010_016_valid | exact tilt_010_017_valid | exact tilt_010_018_valid | exact tilt_010_019_valid | exact tilt_010_020_valid
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
