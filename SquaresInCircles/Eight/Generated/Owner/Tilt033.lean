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

def tilt_033_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (22099/400000), (33887/10000000)]
    alternative := .zero
    polynomial := [(-243439327301832175570304408739108754571/19175146236476409122323668750000000000000), (134711115176519/211244200000000), (-76497073784698880097634733188505846254571/9587573118238204561161834375000000000000), (134711115176519/211244200000000), (-152750708242095928019699161968272583754571/19175146236476409122323668750000000000000)]
    bernstein := [(12591883140017774586620473134667872461140549/785413989846073717650377472000000000000000000000), (149293415685296038728368417553238388870425579/3141655959384294870601509888000000000000000000000), (355618306223327188286817132109159478602119961/5385695930373076921031159808000000000000000000000), (3596895451261009809460294327618863625465662539/50266495350148717929624158208000000000000000000000), (12887266207033860299477125721442178728768942469/201065981400594871718496632832000000000000000000000)]
    reserve := (100201/6250000000) }

theorem tilt_033_000_valid : tilt_033_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_000]
  · intro i; fin_cases i <;> norm_num [tilt_033_000]
  · norm_num [tilt_033_000]
  · norm_num [tilt_033_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_000]

def tilt_033_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3673/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (22099/400000), (171419/50000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-68042790031101261502444720657998869352173/5431909758662341789447801650000000000000000), (2852236676326130652433/4526408689975000000000), (-21429164526120280333075776493313375885352173/2715954879331170894723900825000000000000000), (2852236676326130652433/4526408689975000000000), (-1475527112489981358781003733309267341425937/187307233057322130670613850000000000000000)]
    bernstein := [(196888898237152260501563428431442658377036703/7672104266027914472268343296000000000000000000000), (50213383590337088141413318011992689996518027277/889964094859238078783127822336000000000000000000000), (113426012160650164860373282674999586812132449743/1525652734044408135056790552576000000000000000000000), (1131051808875771598792104878073528283608359347757/14239425517747809260530045157376000000000000000000000), (4082282446354122624728860599263377466380673969347/56957702070991237042120180629504000000000000000000000)]
    reserve := (25662959/1000000000000) }

theorem tilt_033_001_valid : tilt_033_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_001]
  · intro i; fin_cases i <;> norm_num [tilt_033_001]
  · norm_num [tilt_033_001]
  · norm_num [tilt_033_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_001]

def tilt_033_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (17/390625), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (191/5000000), (1056221/25000000), (544809/12500000), (1/100000000), (22099/400000), (41863/12500000)]
    alternative := (.spike 0 false true)
    polynomial := [(-13014099633044955464111824785471100917346129/1013484929939724029129694706200000000000000000), (713493653136660150923/1105414493075000000000), (-4089133311611131001073150613401003294069346129/506742464969862014564847353100000000000000000), (713493653136660150923/1105414493075000000000), (-8165252523589217046682189402016535487221346129/1013484929939724029129694706200000000000000000)]
    bernstein := [(1411674599759947127177350264455924824384633062751/41512342730331096233152295165952000000000000000000000), (11000268536903459021241810716279711327098030228721/166049370921324384932609180663808000000000000000000000), (24298663678131024761156031935703562814670403843739/284656064436556088455901452566528000000000000000000000), (242685454991266273569301803624842150206609668623761/2656789934741190158921746890620928000000000000000000000), (894738498615126286273332897877363660978726690124831/10627159738964760635686987562483712000000000000000000000)]
    reserve := (34006141/1000000000000) }

theorem tilt_033_002_valid : tilt_033_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_002]
  · intro i; fin_cases i <;> norm_num [tilt_033_002]
  · norm_num [tilt_033_002]
  · norm_num [tilt_033_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_002]

def tilt_033_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5479339/100000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (22099/400000), (171419/50000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-931038258622992661246962043466285248979249/74651551520755556108541665943750000000000000), (2852236676326130652433/4526408689975000000000), (-294500142067793755259455993841753052217979249/37325775760377778054270832971875000000000000), (2852236676326130652433/4526408689975000000000), (-20278249857826362684747069849656545489206181/2574191431750191589949712618750000000000000)]
    bernstein := [(8490438565398871126485070695784787662268488139/105438881044487847524340228864000000000000000000000), (1361178119652499809416131713819124621947189603601/12230910201160590312823466548224000000000000000000000), (2709405734180772265817127164056018337942461337659/20967274630561011964840228368384000000000000000000000), (26284241390579484125799213365524903083639654529841/195694563218569445005175464771584000000000000000000000), (99068972445051613472737625327014341213103228440511/782778252874277780020701859086336000000000000000000000)]
    reserve := (4026237/50000000000) }

theorem tilt_033_003_valid : tilt_033_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_003]
  · intro i; fin_cases i <;> norm_num [tilt_033_003]
  · norm_num [tilt_033_003]
  · norm_num [tilt_033_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_003]

def tilt_033_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2742401/50000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (22099/400000), (41863/12500000)]
    alternative := (.spike 0 true true)
    polynomial := [(-1865286988118322438713383156148249835056873/145993324906820796908355999300000000000000000), (713493653136660150923/1105414493075000000000), (-589033560431161236556763019890122161963056873/72996662453410398454177999650000000000000000), (713493653136660150923/1105414493075000000000), (-1176201833874204150674812656624096074091056873/145993324906820796908355999300000000000000000)]
    bernstein := [(589649588890296033706711165284152739544474543687/5979886588183379841366261731328000000000000000000000), (3129965291700177217804851545427970306759627677577/23919546352733519365465046925312000000000000000000000), (6149762568956005215864712516530445902452883377443/41004936604686033197940080443392000000000000000000000), (59690947650686742485894910296309524580378143670057/382712741643736309847440750804992000000000000000000000), (227827990682338420345596223542293184247609533392647/1530850966574945239389763003219968000000000000000000000)]
    reserve := (2465137/25000000000) }

theorem tilt_033_004_valid : tilt_033_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_004]
  · intro i; fin_cases i <;> norm_num [tilt_033_004]
  · norm_num [tilt_033_004]
  · norm_num [tilt_033_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_004]

def tilt_033_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (136141/3125000), (1/100000000), (22099/400000), (171419/50000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-136085451982088333648741913661470768942301/10858934069797670355037646800000000000000000), (2852236676326130652433/4526408689975000000000), (-42839116778893603055073167146887437040942301/5429467034898835177518823400000000000000000), (2852236676326130652433/4526408689975000000000), (-2949729245027762681948192840693565631480769/374446002406816219139229200000000000000000)]
    bernstein := [(307102612801259286691656044078917323527228911/15337308258583192335942828032000000000000000000000), (90346651333553456874767947367366893270576932349/1779127757995650310969368051712000000000000000000000), (209545161906783553424601939775756395155586223391/3049933299421114818804630945792000000000000000000000), (19270531592783288273914264593211955195796326001/261156368146150504362476044288000000000000000000000), (68976314059629073330455105486274125693722135871/1044625472584602017449904177152000000000000000000000)]
    reserve := (500581/25000000000) }

theorem tilt_033_005_valid : tilt_033_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_005]
  · intro i; fin_cases i <;> norm_num [tilt_033_005]
  · norm_num [tilt_033_005]
  · norm_num [tilt_033_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_005]

def tilt_033_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (4360433/100000000), (1/100000000), (22099/400000), (41863/12500000)]
    alternative := (.spike 1 false true)
    polynomial := [(-1761002296590748060518423125476655601299/137885486573080652929496050000000000000000), (713493653136660150923/1105414493075000000000), (-556320487366494142218939651378083663601299/68942743286540326464748025000000000000000), (713493653136660150923/1105414493075000000000), (-1110879972436397536377360879630690671601299/137885486573080652929496050000000000000000)]
    bernstein := [(585438543773643161368515887855025118243609981/5647789530033383543992158208000000000000000000000), (3070296082428838165820973855231877766376264051/22591158120133534175968632832000000000000000000000), (6003950074272303097534474188360918384753644209/38727699634514630015946227712000000000000000000000), (58202904258033342500557200958756760375457598291/361458529922136546815498125312000000000000000000000), (222484070507295070903485859434857095053793110461/1445834119688546187261992501248000000000000000000000)]
    reserve := (20731599/200000000000) }

theorem tilt_033_006_valid : tilt_033_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_006]
  · intro i; fin_cases i <;> norm_num [tilt_033_006]
  · norm_num [tilt_033_006]
  · norm_num [tilt_033_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_006]

def tilt_033_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (527857/12500000), (544809/12500000), (1/100000000), (22099/400000), (171419/50000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-6185543548442488613551274336158194995723/493572942762792626638235100000000000000000), (2851559445002549376697/4524235954150000000000), (-1947252177834938040124552008184108670120723/246786471381396313319117550000000000000000), (2851559445002549376697/4524235954150000000000), (-134079959038670123849501818690760660180887/17019756646992849194421900000000000000000)]
    bernstein := [(17608754494259468051881045968205416875645753/697129232260827103003521024000000000000000000000), (4538125665346628460481627073042811012055391227/80866990942255943948408438784000000000000000000000), (934392522138973085187169138822776657859951163/12602647939052874381570146304000000000000000000000), (102639270102544858438037570060150186238328959707/1293871855076095103174535020544000000000000000000000), (370914035734830526739956372781341866988584527797/5175487420304380412698140082176000000000000000000000)]
    reserve := (3157369/125000000000) }

theorem tilt_033_007_valid : tilt_033_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_007]
  · intro i; fin_cases i <;> norm_num [tilt_033_007]
  · norm_num [tilt_033_007]
  · norm_num [tilt_033_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_007]

def tilt_033_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (4226911/100000000), (544809/12500000), (1/100000000), (22099/400000), (41863/12500000)]
    alternative := (.spike 1 true true)
    polynomial := [(-3568437990769597554331747344232997807377/279407874394653555538437450000000000000000), (1427334173713082855759/2211889689912500000000), (-7180064578786529815560325949303681855461/889833994887431705536425000000000000000), (1427334173713082855759/2211889689912500000000), (-2250971839748200764531610600737123104807377/279407874394653555538437450000000000000000)]
    bernstein := [(86649623748432410368990198224738829493757851/880349733477308433450338304000000000000000000000), (5977452453947725998387499446495960900663970673/45778186140820038539417591808000000000000000000000), (11739871044523218763486894461636952625844769307/78476890527120066067573014528000000000000000000000), (8760616272523167551572578272400152518479619861/56342382942547739740821651456000000000000000000000), (209721245830812599413069950870588490847985593/1414680788513994430962204672000000000000000000000)]
    reserve := (24606591/250000000000) }

theorem tilt_033_008_valid : tilt_033_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_008]
  · intro i; fin_cases i <;> norm_num [tilt_033_008]
  · norm_num [tilt_033_008]
  · norm_num [tilt_033_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_008]

def tilt_033_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (4356513/100000000), (1/100000000), (22099/400000), (171419/50000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-15552719112594863741601550554940965321031/1241021321414050198781203830000000000000000), (2852236676326130652433/4526408689975000000000), (-4895900276715617353386709171280012608521031/620510660707025099390601915000000000000000), (2852236676326130652433/4526408689975000000000), (-337111994286849649759717820413968422473139/42793838669450006854524270000000000000000)]
    bernstein := [(34966491670716525796279780828163914636622941/1752835631900672280761314099200000000000000000000), (10310141062922803545259007190259921763023998119/203328933300477984568312435507200000000000000000000), (23921975917196646561986853260168139391807107821/348563885657962259259964175155200000000000000000000), (239812674612912516137874060192112270912352124679/3253262932807647753092998968115200000000000000000000), (858275290051555329755811548817592174820444926409/13013051731230591012371995872460800000000000000000000)]
    reserve := (1246783/62500000000) }

theorem tilt_033_009_valid : tilt_033_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_009]
  · intro i; fin_cases i <;> norm_num [tilt_033_009]
  · norm_num [tilt_033_009]
  · norm_num [tilt_033_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_009]

def tilt_033_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (2180217/50000000), (1/100000000), (22099/400000), (41863/12500000)]
    alternative := (.spike 2 false true)
    polynomial := [(-16877276529316025756674393489694934246251/1327148112627373703791286662500000000000000), (713493653136660150923/1105414493075000000000), (-5354513544433788859030662345763327230246251/663574056313686851895643331250000000000000), (713493653136660150923/1105414493075000000000), (-10692149812338261692304650298036959526246251/1327148112627373703791286662500000000000000)]
    bernstein := [(662126820094170074485196888007711596554229113/4181537437939786685176238592000000000000000000000), (3188015665763589014231237091743401792368711223/16726149751759146740704954368000000000000000000000), (78177793958851654503641875509546149207479182841/372754194467775270221424697344000000000000000000000), (750531025528156674926487381370410619807211199659/3479039148365902522066630508544000000000000000000000), (2902817947905750083221147481170311429151112453989/13916156593463610088266522034176000000000000000000000)]
    reserve := (19793163/125000000000) }

theorem tilt_033_010_valid : tilt_033_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_010]
  · intro i; fin_cases i <;> norm_num [tilt_033_010]
  · norm_num [tilt_033_010]
  · norm_num [tilt_033_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_010]

def tilt_033_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7309/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (22099/400000), (171419/50000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-2835297648547135659200118706653279576127/226329573277597574560325068750000000000000), (2852236676326130652433/4526408689975000000000), (-892882036652262930308088942567293988576127/113164786638798787280162534375000000000000), (2852236676326130652433/4526408689975000000000), (-61480302608826852584723371256135679226763/7804468044055088777942243750000000000000)]
    bernstein := [(7946775021914276579858851722643128667054597/319671011084496436344514304000000000000000000000), (2062417056268249050866663824038642230877139423/37081837285801586615963659264000000000000000000000), (4674979534528649260670591639400845918874225557/63568863918517005627366273024000000000000000000000), (46650126272121289518920045709346442690521226943/593309396572825385855418548224000000000000000000000), (168186730332727709626777070910976993166149894353/2373237586291301543421674192896000000000000000000000)]
    reserve := (24859229/1000000000000) }

theorem tilt_033_011_valid : tilt_033_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_011]
  · intro i; fin_cases i <;> norm_num [tilt_033_011]
  · norm_num [tilt_033_011]
  · norm_num [tilt_033_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_011]

def tilt_033_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (433/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (19/500000), (22099/400000), (41863/12500000)]
    alternative := (.spike 2 true true)
    polynomial := [(-17033273426830860978439982895008530584191/1326550955418486949122637050000000000000000), (713493653136660150923/1105414493075000000000), (-5352267844078775946854145203595966898584191/663275477709243474561318525000000000000000), (713493653136660150923/1105414493075000000000), (-10687502414730721032729850424296925266584191/1326550955418486949122637050000000000000000)]
    bernstein := [(1884232759684182027197693871763193129164517329/54335527133941225436063213568000000000000000000000), (14544238876302802285125964011331313769923828959/217342108535764901744252854272000000000000000000000), (32054817929074603104974724905971024886665495381/372586471775596974418719178752000000000000000000000), (319987394603231034815524658574798723086659437119/3477473736572238427908045668352000000000000000000000), (1180469975890937516842660584138284581882597221649/13909894946288953711632182673408000000000000000000000)]
    reserve := (3467773/100000000000) }

theorem tilt_033_012_valid : tilt_033_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_012]
  · intro i; fin_cases i <;> norm_num [tilt_033_012]
  · norm_num [tilt_033_012]
  · norm_num [tilt_033_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_012]

def tilt_033_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (1380501/25000000), (171419/50000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-7757920997416579522825424220878267983167989/622096968122044259388956331975000000000000000), (2852236676326130652433/4526408689975000000000), (-2454169893603426849763911875646340407187167989/311048484061022129694478165987500000000000000), (2852236676326130652433/4526408689975000000000), (-168985581593428866207068907830062156772109241/21451619590415319289274356275000000000000000)]
    bernstein := [(71801800464140781328225075230260732023883228279/878658338423411478088677633024000000000000000000000), (11464753687399736927033692819691493029184487555861/101924367257115731458286605430784000000000000000000000), (159508100461366245492109399369343744988469290910993/1223092407085388777499439265169408000000000000000000000), (220981504834974610943141580507690371589489719144501/1630789876113851703332585686892544000000000000000000000), (833360339342559202645526906637285574924191533549371/6523159504455406813330342747570176000000000000000000000)]
    reserve := (40858771/500000000000) }

theorem tilt_033_013_valid : tilt_033_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_013]
  · intro i; fin_cases i <;> norm_num [tilt_033_013]
  · norm_num [tilt_033_013]
  · norm_num [tilt_033_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_013]

def tilt_033_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (5527497/100000000), (41863/12500000)]
    alternative := (.spike 3 false true)
    polynomial := [(-5182131128543530031264184641004120726194101/405536553643206700725320995850000000000000000), (713493653136660150923/1105414493075000000000), (-1636203262900841218563021442553115468342194101/202768276821603350362660497925000000000000000), (713493653136660150923/1105414493075000000000), (-3267224394673138907094778700465226815958194101/405536553643206700725320995850000000000000000)]
    bernstein := [(1605699934014123707200953971377458708177688882619/16610777237225746461709147990016000000000000000000000), (8565468160417637577552440948195750025956117550549/66443108948902985846836591960064000000000000000000000), (118031954871728728727158366314298873403593081360337/797317307386835830162039103520768000000000000000000000), (163745576990344038105858317933687197949991576920309/1063089743182447773549385471361024000000000000000000000), (624604074685090168095738936168213330409348407990139/4252358972729791094197541885444096000000000000000000000)]
    reserve := (96666153/1000000000000) }

theorem tilt_033_014_valid : tilt_033_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_014]
  · intro i; fin_cases i <;> norm_num [tilt_033_014]
  · norm_num [tilt_033_014]
  · norm_num [tilt_033_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_014]

def tilt_033_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7309/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (22099/400000), (171419/50000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-2835297648547135659200118706653279576127/226329573277597574560325068750000000000000), (2852236676326130652433/4526408689975000000000), (-892882036652262930308088942567293988576127/113164786638798787280162534375000000000000), (2852236676326130652433/4526408689975000000000), (-61480302608826852584723371256135679226763/7804468044055088777942243750000000000000)]
    bernstein := [(7946775021914276579858851722643128667054597/319671011084496436344514304000000000000000000000), (2062417056268249050866663824038642230877139423/37081837285801586615963659264000000000000000000000), (4674979534528649260670591639400845918874225557/63568863918517005627366273024000000000000000000000), (46650126272121289518920045709346442690521226943/593309396572825385855418548224000000000000000000000), (168186730332727709626777070910976993166149894353/2373237586291301543421674192896000000000000000000000)]
    reserve := (24859229/1000000000000) }

theorem tilt_033_015_valid : tilt_033_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_015]
  · intro i; fin_cases i <;> norm_num [tilt_033_015]
  · norm_num [tilt_033_015]
  · norm_num [tilt_033_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_015]

def tilt_033_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (433/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (19/500000), (22099/400000), (41863/12500000)]
    alternative := (.spike 3 true true)
    polynomial := [(-17033273426830860978439982895008530584191/1326550955418486949122637050000000000000000), (713493653136660150923/1105414493075000000000), (-5352267844078775946854145203595966898584191/663275477709243474561318525000000000000000), (713493653136660150923/1105414493075000000000), (-10687502414730721032729850424296925266584191/1326550955418486949122637050000000000000000)]
    bernstein := [(1884232759684182027197693871763193129164517329/54335527133941225436063213568000000000000000000000), (14544238876302802285125964011331313769923828959/217342108535764901744252854272000000000000000000000), (32054817929074603104974724905971024886665495381/372586471775596974418719178752000000000000000000000), (319987394603231034815524658574798723086659437119/3477473736572238427908045668352000000000000000000000), (1180469975890937516842660584138284581882597221649/13909894946288953711632182673408000000000000000000000)]
    reserve := (3467773/100000000000) }

theorem tilt_033_016_valid : tilt_033_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_016]
  · intro i; fin_cases i <;> norm_num [tilt_033_016]
  · norm_num [tilt_033_016]
  · norm_num [tilt_033_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_016]

def tilt_033_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (1380501/25000000), (171419/50000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-7757935277587184089077647407800525100754989/622096968122044259388956331975000000000000000), (2852236676326130652433/4526408689975000000000), (-2454169907883597454330164098833262664304754989/311048484061022129694478165987500000000000000), (2852236676326130652433/4526408689975000000000), (-168985582085848542226594846560645682879612241/21451619590415319289274356275000000000000000)]
    bernstein := [(71781574187578350338804927728631895501949885279/878658338423411478088677633024000000000000000000000), (11462407164753654718265624214287593755040374518861/101924367257115731458286605430784000000000000000000000), (159479938803056519943401295123495153501047059829993/1223092407085388777499439265169408000000000000000000000), (220943951319404942340998964063990489447238583227501/1630789876113851703332585686892544000000000000000000000), (833210106239143884620129425221713469481367836842371/6523159504455406813330342747570176000000000000000000000)]
    reserve := (81694523/1000000000000) }

theorem tilt_033_017_valid : tilt_033_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_017]
  · intro i; fin_cases i <;> norm_num [tilt_033_017]
  · norm_num [tilt_033_017]
  · norm_num [tilt_033_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_017]

def tilt_033_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (2763749/50000000), (41863/12500000)]
    alternative := (.spike 4 false true)
    polynomial := [(-11644834865540782671626703315773861480439811/912457410773242381072856900025000000000000000), (713493653136660150923/1105414493075000000000), (-3681443045269906780467518795900904022904439811/456228705386621190536428450012500000000000000), (713493653136660150923/1105414493075000000000), (-7351241255674272778263410888486034184328439811/912457410773242381072856900025000000000000000)]
    bernstein := [(4227405487832702136596885993178784656065431588109/37374255545272007928744218625024000000000000000000000), (21730914458146244188353398747573725174464154106339/149497022181088031714976874500096000000000000000000000), (295078786154378230598170791350158926814178059657607/1793964266173056380579722494001152000000000000000000000), (407774927100600708686382882262802886256275497845699/2391952354897408507439629992001536000000000000000000000), (1562768621828519050817549794713976808722598692714829/9567809419589634029758519968006144000000000000000000000)]
    reserve := (28277523/250000000000) }

theorem tilt_033_018_valid : tilt_033_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_018]
  · intro i; fin_cases i <;> norm_num [tilt_033_018]
  · norm_num [tilt_033_018]
  · norm_num [tilt_033_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_018]

def tilt_033_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (22099/400000), (33887/10000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-240378352843679627802146748026788504571/19175146236476409122323668750000000000000), (134711115176519/211244200000000), (-76497147233460475747726793353481496408371/9587573118238204561161834375000000000000), (134711115176519/211244200000000), (-152753916114077271867651439958936204312171/19175146236476409122323668750000000000000)]
    bernstein := [(137960675810979823428068790388866661478214949/785413989846073717650377472000000000000000000000), (650767089540378101328499419896753144230707979/3141655959384294870601509888000000000000000000000), (1215284815884923395368122979463619503900381561/5385695930373076921031159808000000000000000000000), (11620424098059719784751718388489786582754520939/50266495350148717929624158208000000000000000000000), (44981275971542521058806320318564797098820768869/201065981400594871718496632832000000000000000000000)]
    reserve := (21956681/125000000000) }

theorem tilt_033_019_valid : tilt_033_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_019]
  · intro i; fin_cases i <;> norm_num [tilt_033_019]
  · norm_num [tilt_033_019]
  · norm_num [tilt_033_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_019]

def tilt_033_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(548207/10000000), (1/100000000), (1056221/25000000), (544809/12500000), (1/100000000), (22099/400000), (33887/10000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-243382504596407999801988439779129004571/19175146236476409122323668750000000000000), (134711115176519/211244200000000), (-76494029411440857543573674527020805908371/9587573118238204561161834375000000000000), (134711115176519/211244200000000), (-152744676318285307087345360614262482812171/19175146236476409122323668750000000000000)]
    bernstein := [(15270541539344872580197177448189898519714949/785413989846073717650377472000000000000000000000), (160066664111101350505821113744397540477207979/3141655959384294870601509888000000000000000000000), (374190021352244475440866736338991609843881561/5385695930373076921031159808000000000000000000000), (3771221706084744587907659966347995721161020939/50266495350148717929624158208000000000000000000000), (13588637148146490971421050868102353012182268869/201065981400594871718496632832000000000000000000000)]
    reserve := (3888533/200000000000) }

theorem tilt_033_020_valid : tilt_033_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_033_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_033_020]
  · intro i; fin_cases i <;> norm_num [tilt_033_020]
  · norm_num [tilt_033_020]
  · norm_num [tilt_033_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_033_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_033_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_033_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_033_020]

def tiltBundle033_row : Alternative → Row
  | .zero => tilt_033_000
  | (.spike 0 false false) => tilt_033_001
  | (.spike 0 false true) => tilt_033_002
  | (.spike 0 true false) => tilt_033_003
  | (.spike 0 true true) => tilt_033_004
  | (.spike 1 false false) => tilt_033_005
  | (.spike 1 false true) => tilt_033_006
  | (.spike 1 true false) => tilt_033_007
  | (.spike 1 true true) => tilt_033_008
  | (.spike 2 false false) => tilt_033_009
  | (.spike 2 false true) => tilt_033_010
  | (.spike 2 true false) => tilt_033_011
  | (.spike 2 true true) => tilt_033_012
  | (.spike 3 false false) => tilt_033_013
  | (.spike 3 false true) => tilt_033_014
  | (.spike 3 true false) => tilt_033_015
  | (.spike 3 true true) => tilt_033_016
  | (.spike 4 false false) => tilt_033_017
  | (.spike 4 false true) => tilt_033_018
  | (.spike 4 true false) => tilt_033_019
  | (.spike 4 true true) => tilt_033_020

def tiltBundle033 : TiltBundle where
  interval := ⟨(3/80), (13/320)⟩
  lambda := ![(14692461/100000000), (14692461/100000000), (4578403/50000000), (456801/3125000), (456801/3125000), (2032463/12500000), (1995413/12500000)]
  row := tiltBundle033_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_033_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_033_001_valid | exact tilt_033_002_valid | exact tilt_033_003_valid | exact tilt_033_004_valid | exact tilt_033_005_valid | exact tilt_033_006_valid | exact tilt_033_007_valid | exact tilt_033_008_valid | exact tilt_033_009_valid | exact tilt_033_010_valid | exact tilt_033_011_valid | exact tilt_033_012_valid | exact tilt_033_013_valid | exact tilt_033_014_valid | exact tilt_033_015_valid | exact tilt_033_016_valid | exact tilt_033_017_valid | exact tilt_033_018_valid | exact tilt_033_019_valid | exact tilt_033_020_valid
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
