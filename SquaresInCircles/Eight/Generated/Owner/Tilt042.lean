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

def tilt_042_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (42331/781250), (687291/100000000)]
    alternative := .zero
    polynomial := [(-235647559407101033736932373055564982400508657/8139862075023250606010689412700000000000000000), (11454986203101/17402012500000), (-15294634399983376162232575985375575241400508657/4069931037511625303005344706350000000000000000), (11454986203101/17402012500000), (-30353621240559651290728219597695585500400508657/8139862075023250606010689412700000000000000000)]
    bernstein := [(785502061564604792349411299223791779013037766618703/13023779320037200969617103060320000000000000000000000000), (131335496095688298463181240649004236233190796496371/1736503909338293462615613741376000000000000000000000000), (838433835823599225607489221908896329391594612181/9632379158116882073060415206400000000000000000000000), (26268152165400900880012096314235625563243992320611/277840625494126954018498198620160000000000000000000000), (32717951029719982690030899095446240586944758324143/333408750592952344822197838344192000000000000000000000)]
    reserve := (3769557/62500000000) }

theorem tilt_042_000_valid : tilt_042_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_000]
  · intro i; fin_cases i <;> norm_num [tilt_042_000]
  · norm_num [tilt_042_000]
  · norm_num [tilt_042_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_000]

def tilt_042_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7481/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (42331/781250), (345531/50000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-39258655059364552795044359984599083143581541/1364087255929370434137058646900000000000000000), (2100114929076682249581/3206898549940000000000), (-2550408365559247153388402968844073050073581541/682043627964685217068529323450000000000000000), (2100114929076682249581/3206898549940000000000), (-5061558076059129753981761577703547017003581541/1364087255929370434137058646900000000000000000)]
    bernstein := [(165269734444426158140919069633383730113854038194139/2182539609486992694619293835040000000000000000000000000), (79346014800312586106768532838582510129385756479469/873015843794797077847717534016000000000000000000000000), (35675669694657777745204178618145588023844067514699/349206337517918831139087013606400000000000000000000000), (15301648484171516568941532305839696137098737864829/139682535007167532455634805442560000000000000000000000), (6315661156412750575228050069167724093000538844859/55873014002867012982253922177024000000000000000000000)]
    reserve := (75723589/1000000000000) }

theorem tilt_042_001_valid : tilt_042_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_001]
  · intro i; fin_cases i <;> norm_num [tilt_042_001]
  · norm_num [tilt_042_001]
  · norm_num [tilt_042_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_001]

def tilt_042_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (277/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (389/10000000), (4176483/100000000), (2250969/50000000), (1/100000000), (42331/781250), (534/78125)]
    alternative := (.spike 0 false true)
    polynomial := [(-91614699625181898528768090225580540101101777/3149033039028938378200421481216000000000000000), (2098769829598245425619/3171899622400000000000), (-5946488256044410686144059423737304679070901777/1574516519514469189100210740608000000000000000), (2098769829598245425619/3171899622400000000000), (-11801361812463639473759350757249028818040701777/3149033039028938378200421481216000000000000000)]
    bernstein := [(370375020925082975250571915522400856286369608643183/5038452862446301405120674369945600000000000000000000000), (59784188854394900798671437501492472247729859639731/671793714992840187349423249326080000000000000000000000), (243167559740589500150715186894425621568669945716509/2418457373974224674457923697573888000000000000000000000), (11627007251910034024171044199441875590870941302371/107486994398854429975907719892172800000000000000000000), (14428653314493782972934017299916349101085496979023/128984393278625315971089263870607360000000000000000000)]
    reserve := (9188709/125000000000) }

theorem tilt_042_002_valid : tilt_042_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_002]
  · intro i; fin_cases i <;> norm_num [tilt_042_002]
  · norm_num [tilt_042_002]
  · norm_num [tilt_042_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_002]

def tilt_042_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(267709/5000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (42331/781250), (345531/50000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-470089442701259601996862666668831397174609/16360863858519863526824022588000000000000000), (2100114929076682249581/3206898549940000000000), (-30588821483679597476426124289171914340774609/8180431929259931763412011294000000000000000), (2100114929076682249581/3206898549940000000000), (-60707553524657935350855385911674997284374609/16360863858519863526824022588000000000000000)]
    bernstein := [(3246564758655502847870686931150574305560508201711/26177382173631781642918436140800000000000000000000000), (485836878665808916150938380384198467191327988627/3490317623150904219055791485440000000000000000000000), (1890812708464538917570478304920106868070320895453/12565143443343255188600849347584000000000000000000000), (88165384052127119231799748306853989450673461507/558450819704144675048926637670400000000000000000000), (108144344603232453935820263627457213481325158991/670140983644973610058711965204480000000000000000000)]
    reserve := (496087/4000000000) }

theorem tilt_042_003_valid : tilt_042_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_003]
  · intro i; fin_cases i <;> norm_num [tilt_042_003]
  · norm_num [tilt_042_003]
  · norm_num [tilt_042_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_003]

def tilt_042_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5359537/100000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (42331/781250), (534/78125)]
    alternative := (.spike 0 true true)
    polynomial := [(-2350343757419010924699637373868749110976437/80992490776638457834035644160000000000000000), (2098769829598245425619/3171899622400000000000), (-152936503584721818024437256693265957783976437/40496245388319228917017822080000000000000000), (2098769829598245425619/3171899622400000000000), (-303522663412024625124174876012663166456976437/80992490776638457834035644160000000000000000)]
    bernstein := [(19212805716952075915823809445343164185841657565323/129587985242621532534457030656000000000000000000000000), (2829487742259507879061256216938933276713304015711/17278398032349537671260937420800000000000000000000000), (10905872948913529486065879193334598971251636439729/62202232916458335616539374714880000000000000000000000), (505828851276368419450066657651931094970533689551/2764543685175926027401749987328000000000000000000000), (619297416539306426253793668990711718155242768363/3317452422211111232882099984793600000000000000000000)]
    reserve := (74130351/500000000000) }

theorem tilt_042_004_valid : tilt_042_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_004]
  · intro i; fin_cases i <;> norm_num [tilt_042_004]
  · norm_num [tilt_042_004]
  · norm_num [tilt_042_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_004]

def tilt_042_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (562481/12500000), (1/100000000), (42331/781250), (345531/50000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-44143072747244420122772767877476633664697013/1533885734148643073377425891450000000000000000), (2100114929076682249581/3206898549940000000000), (-2867874986159903631684366129009720566729697013/766942867074321536688712945725000000000000000), (2100114929076682249581/3206898549940000000000), (-5691606899572562843245959490141964499794697013/1533885734148643073377425891450000000000000000)]
    bernstein := [(189754668366426434973399311787752937705491870217227/2454217174637828917403881426320000000000000000000000000), (30262723245362735665881116775348158664561053344639/327228956618377188987184190176000000000000000000000000), (122228300074113681421474659080471400278517761063921/1178024243826157880353863084633600000000000000000000000), (5818975024692105958977219172052364260027104074799/52356633058940350237949470428160000000000000000000000), (7202066930492755488195887228266226780983513438187/62827959670728420285539364513792000000000000000000000)]
    reserve := (38658899/500000000000) }

theorem tilt_042_005_valid : tilt_042_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_005]
  · intro i; fin_cases i <;> norm_num [tilt_042_005]
  · norm_num [tilt_042_005]
  · norm_num [tilt_042_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_005]

def tilt_042_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (1126007/25000000), (1/100000000), (42331/781250), (534/78125)]
    alternative := (.spike 1 false true)
    polynomial := [(-8814571401407476466102069722405268748141937/303710953759175548518982982400000000000000000), (2098769829598245425619/3171899622400000000000), (-573492429626673059299767818185271713593141937/151855476879587774259491491200000000000000000), (2098769829598245425619/3171899622400000000000), (-1138170287851938642133433566648138158438141937/303710953759175548518982982400000000000000000)]
    bernstein := [(70262781767613490688503775595606273519092813839823/485937526014680877630372771840000000000000000000000000), (10372460937184766317957686609189292887558557112211/64791670135290783684049702912000000000000000000000000), (40039519348607121856796482408523219037775449703229/233250012487046821262578930483200000000000000000000000), (1858735871721186968962009145837885721302816746051/10366667221646525389447952465920000000000000000000000), (2276606958141953064306748776410571068700518802863/12440000665975830467337542959104000000000000000000000)]
    reserve := (144592211/1000000000000) }

theorem tilt_042_006_valid : tilt_042_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_006]
  · intro i; fin_cases i <;> norm_num [tilt_042_006]
  · norm_num [tilt_042_006]
  · norm_num [tilt_042_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_006]

def tilt_042_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4174231/100000000), (2250969/50000000), (1/100000000), (42331/781250), (345531/50000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-353130735555247362629171051922079981052578961/12270165542071596338336661749700000000000000000), (6298804041314884697451/9615508077740000000000), (-22943488532502068706204478914655201592516578961/6135082771035798169168330874850000000000000000), (6298804041314884697451/9615508077740000000000), (-45533846329448890049779786777388323203980578961/12270165542071596338336661749700000000000000000)]
    bernstein := [(1770762833362976284301775007041155418583347886278319/19632264867314554141338658799520000000000000000000000000), (276016651366297598675896267346458564919576482976083/2617635315641940552178487839936000000000000000000000000), (1100704742132356384130670207353943949994223739198237/9423487136310985987842556223769600000000000000000000000), (52047920910280936030876150117572492786560615185603/418821650502710488348558054389760000000000000000000000), (64253689748064685813129867705253656698523263015439/502585980603252586018269665267712000000000000000000000)]
    reserve := (90196563/1000000000000) }

theorem tilt_042_007_valid : tilt_042_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_007]
  · intro i; fin_cases i <;> norm_num [tilt_042_007]
  · norm_num [tilt_042_007]
  · norm_num [tilt_042_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_007]

def tilt_042_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (835747/20000000), (2250969/50000000), (1/100000000), (42331/781250), (534/78125)]
    alternative := (.spike 1 true true)
    polynomial := [(-3525968126880296335607558169140427660431743/121493484373245837498873427200000000000000000), (114506696719613092683/173105996800000000000), (-229392308486134003904177940953226762025031743/60746742186622918749436713600000000000000000), (114506696719613092683/173105996800000000000), (-455258648845387711472748323737313096389631743/121493484373245837498873427200000000000000000)]
    bernstein := [(25605787170303940793643349646888466895290819032897/194389574997193339998197483520000000000000000000000000), (3813584066812010313447132783479790727459770304829/25918609999625778666426331136000000000000000000000000), (14800606017424914190443537074122456716850962841331/93306995998652803199134792089600000000000000000000000), (689140653613348324205498024879146928002203208589/4146977599940124586628212981760000000000000000000000), (845004895106104299034248526055535651486971695457/4976373119928149503953855578112000000000000000000000)]
    reserve := (32931019/250000000000) }

theorem tilt_042_008_valid : tilt_042_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_008]
  · intro i; fin_cases i <;> norm_num [tilt_042_008]
  · norm_num [tilt_042_008]
  · norm_num [tilt_042_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_008]

def tilt_042_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (4499849/100000000), (1/100000000), (42331/781250), (345531/50000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-706290927748936423709642363007907579279655237/24542177200378456819321315814100000000000000000), (2100114929076682249581/3206898549940000000000), (-45886011582626314114640444734990487364049655237/12271088600189228409660657907050000000000000000), (2100114929076682249581/3206898549940000000000), (-91065732237503691805571247106973067148819655237/24542177200378456819321315814100000000000000000)]
    bernstein := [(3033467149026722798829231121564384188053234295510523/39267483520605530910914105302560000000000000000000000000), (483855843555152081842346510621774612328192320912111/5235664469414070788121880707008000000000000000000000000), (1954400759523007914723510675945451608432548594699329/18848392089890654837238770545228800000000000000000000000), (93047943500927518428634809502384474828903212401951/837706315106251326099500913121280000000000000000000000), (115166268887190670944910583840380260377301335609563/1005247578127501591319401095745536000000000000000000000)]
    reserve := (4828211/62500000000) }

theorem tilt_042_009_valid : tilt_042_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_009]
  · intro i; fin_cases i <;> norm_num [tilt_042_009]
  · norm_num [tilt_042_009]
  · norm_num [tilt_042_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_009]

def tilt_042_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (4504029/100000000), (1/100000000), (42331/781250), (534/78125)]
    alternative := (.spike 2 false true)
    polynomial := [(-11733503433379952183099846184126409663249801/404948028253520533655772537600000000000000000), (2098769829598245425619/3171899622400000000000), (-764637481562729863798431043765034252068249801/202474014126760266827886268800000000000000000), (2098769829598245425619/3171899622400000000000), (-1517541459692079775413762241345942094473249801/404948028253520533655772537600000000000000000)]
    bernstein := [(124948325159250547505053963900521565376269554250679/647916845205632853849236060160000000000000000000000000), (17999443174244407796047349184086934346778380336603/86388912694084380513231474688000000000000000000000000), (68399407125021813475090830653167067887360919398517/311000085698703769847633308876800000000000000000000000), (3145719427135212627887424544941926031458602694923/13822226031053500882117035950080000000000000000000000), (3836535775918595965737914042213610578231743080599/16586671237264201058540443140096000000000000000000000)]
    reserve := (48211559/250000000000) }

theorem tilt_042_010_valid : tilt_042_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_010]
  · intro i; fin_cases i <;> norm_num [tilt_042_010]
  · norm_num [tilt_042_010]
  · norm_num [tilt_042_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_010]

def tilt_042_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14753/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (42331/781250), (345531/50000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-117785231999610431677527343937614176739323373/4092261767788111302411175940700000000000000000), (2100114929076682249581/3206898549940000000000), (-7651234363499258233457603170516036077529323373/2046130883894055651205587970350000000000000000), (2100114929076682249581/3206898549940000000000), (-15184683494998906035237678997094457978319323373/4092261767788111302411175940700000000000000000)]
    bernstein := [(480767266018773505649625390165027763655481608803667/6547618828460978083857881505120000000000000000000000000), (77340000027276889087283381505369519695661649215719/873015843794797077847717534016000000000000000000000000), (313857835648737569138682179901586940046368890596041/3142857037661269480251783122457600000000000000000000000), (14980548698341458486619813202662884220518858301079/139682535007167532455634805442560000000000000000000000), (18561580059817435687550376431886708469207526955827/167619042008601038946761766531072000000000000000000000)]
    reserve := (2937051/40000000000) }

theorem tilt_042_011_valid : tilt_042_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_011]
  · intro i; fin_cases i <;> norm_num [tilt_042_011]
  · norm_num [tilt_042_011]
  · norm_num [tilt_042_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_011]

def tilt_042_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (437/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (767/20000000), (42331/781250), (534/78125)]
    alternative := (.spike 2 true true)
    polynomial := [(-69471972087709370144120601071358901098107563/2388084181268732189123712948480000000000000000), (2098769829598245425619/3171899622400000000000), (-4509543178112574389029752846279478749417107563/1194042090634366094561856474240000000000000000), (2098769829598245425619/3171899622400000000000), (-8949614384137439407915385091487598597736107563/2388084181268732189123712948480000000000000000)]
    bernstein := [(288133119614187076960978958730962969122113533670677/3820934690029971502597940717568000000000000000000000000), (46305489567751270847722548960907940188312248036289/509457958670662867013058762342400000000000000000000000), (187892333907044789636910035227700305177759969588271/1834048651214386321247011544432640000000000000000000000), (8972321049398597148017594198978955575942829242449/81513273387306058722089401974784000000000000000000000), (11127987993385705847620044476083388782582333747637/97815928064767270466507282369740800000000000000000000)]
    reserve := (37704533/500000000000) }

theorem tilt_042_012_valid : tilt_042_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_012]
  · intro i; fin_cases i <;> norm_num [tilt_042_012]
  · norm_num [tilt_042_012]
  · norm_num [tilt_042_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_012]

def tilt_042_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (5415663/100000000), (345531/50000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-5013922267262238090468725823424340954414930263/174516002001091920187333288673700000000000000000), (2100114929076682249581/3206898549940000000000), (-326280619832047518484913228994427278805304930263/87258001000545960093666644336850000000000000000), (2100114929076682249581/3206898549940000000000), (-647547317396832798879357732165430216656194930263/174516002001091920187333288673700000000000000000)]
    bernstein := [(35228350655778065092170938055285605056165747748943977/279225603201747072299733261877920000000000000000000000000), (5262054135717913233261858932670735888543776598444389/37230080426899609639964434917056000000000000000000000000), (20455989877099356039306819660585627470703410880704171/134028289536838594703871965701401600000000000000000000000), (953203361782416342478245515936427923226482955314549/5956812868303937542394309586728960000000000000000000000), (1168870139251535573170449624210895449137457339004937/7148175441964725050873171504074752000000000000000000000)]
    reserve := (126164471/1000000000000) }

theorem tilt_042_013_valid : tilt_042_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_013]
  · intro i; fin_cases i <;> norm_num [tilt_042_013]
  · norm_num [tilt_042_013]
  · norm_num [tilt_042_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_013]

def tilt_042_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (5421073/100000000), (534/78125)]
    alternative := (.spike 3 false true)
    polynomial := [(-107459723821727102266233822415888693799836297/3702510612004056184758573638400000000000000000), (2098769829598245425619/3171899622400000000000), (-6991392412336435921184392831473903890444836297/1851255306002028092379286819200000000000000000), (2098769829598245425619/3171899622400000000000), (-13875325100851144740102551840531919087089836297/3702510612004056184758573638400000000000000000)]
    bernstein := [(853087092445127210082622395749001093060511045998263/5924016979206489895613717821440000000000000000000000000), (125985611448560304576901274300497475895734358787291/789868930560865319415162376192000000000000000000000000), (486446945847783893044885324439261113387810558591349/2843528150019115149894584554291200000000000000000000000), (22585388223471392272994946737280421517424484536331/126379028889738451106425980190720000000000000000000000), (27664738626750733111125901685907155654042512452503/151654834667686141327711176228864000000000000000000000)]
    reserve := (28800967/200000000000) }

theorem tilt_042_014_valid : tilt_042_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_014]
  · intro i; fin_cases i <;> norm_num [tilt_042_014]
  · norm_num [tilt_042_014]
  · norm_num [tilt_042_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_014]

def tilt_042_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14753/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (42331/781250), (345531/50000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-117785231999610431677527343937614176739323373/4092261767788111302411175940700000000000000000), (2100114929076682249581/3206898549940000000000), (-7651234363499258233457603170516036077529323373/2046130883894055651205587970350000000000000000), (2100114929076682249581/3206898549940000000000), (-15184683494998906035237678997094457978319323373/4092261767788111302411175940700000000000000000)]
    bernstein := [(480767266018773505649625390165027763655481608803667/6547618828460978083857881505120000000000000000000000000), (77340000027276889087283381505369519695661649215719/873015843794797077847717534016000000000000000000000000), (313857835648737569138682179901586940046368890596041/3142857037661269480251783122457600000000000000000000000), (14980548698341458486619813202662884220518858301079/139682535007167532455634805442560000000000000000000000), (18561580059817435687550376431886708469207526955827/167619042008601038946761766531072000000000000000000000)]
    reserve := (2937051/40000000000) }

theorem tilt_042_015_valid : tilt_042_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_015]
  · intro i; fin_cases i <;> norm_num [tilt_042_015]
  · norm_num [tilt_042_015]
  · norm_num [tilt_042_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_015]

def tilt_042_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (437/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (767/20000000), (42331/781250), (534/78125)]
    alternative := (.spike 3 true true)
    polynomial := [(-69471972087709370144120601071358901098107563/2388084181268732189123712948480000000000000000), (2098769829598245425619/3171899622400000000000), (-4509543178112574389029752846279478749417107563/1194042090634366094561856474240000000000000000), (2098769829598245425619/3171899622400000000000), (-8949614384137439407915385091487598597736107563/2388084181268732189123712948480000000000000000)]
    bernstein := [(288133119614187076960978958730962969122113533670677/3820934690029971502597940717568000000000000000000000000), (46305489567751270847722548960907940188312248036289/509457958670662867013058762342400000000000000000000000), (187892333907044789636910035227700305177759969588271/1834048651214386321247011544432640000000000000000000000), (8972321049398597148017594198978955575942829242449/81513273387306058722089401974784000000000000000000000), (11127987993385705847620044476083388782582333747637/97815928064767270466507282369740800000000000000000000)]
    reserve := (37704533/500000000000) }

theorem tilt_042_016_valid : tilt_042_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_016]
  · intro i; fin_cases i <;> norm_num [tilt_042_016]
  · norm_num [tilt_042_016]
  · norm_num [tilt_042_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_016]

def tilt_042_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (5415663/100000000), (345531/50000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1671308081470799427342501061918903627260387421/58172000667030640062444429557900000000000000000), (2100114929076682249581/3206898549940000000000), (-108760207269732559558824002118919882910890387421/29086000333515320031222214778950000000000000000), (2100114929076682249581/3206898549940000000000), (-215849106457994319690305503175920862194520387421/58172000667030640062444429557900000000000000000)]
    bernstein := [(11741713779558832146643015020763322226927902948690659/93075201067249024099911087292640000000000000000000000000), (5261626136492647568477533408300174072888692207540389/37230080426899609639964434917056000000000000000000000000), (6818149583884729460691282406525610446565771635816057/44676096512279531567957321900467200000000000000000000000), (953134852586265078555236374317977399531190462650549/5956812868303937542394309586728960000000000000000000000), (389595970121752040052443692325066928525629195190979/2382725147321575016957723834691584000000000000000000000)]
    reserve := (126152977/1000000000000) }

theorem tilt_042_017_valid : tilt_042_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_017]
  · intro i; fin_cases i <;> norm_num [tilt_042_017]
  · norm_num [tilt_042_017]
  · norm_num [tilt_042_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_017]

def tilt_042_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (2710537/50000000), (534/78125)]
    alternative := (.spike 4 false true)
    polynomial := [(-376004337136491632585894578649481326062558087/12958789532461095630342673747200000000000000000), (2098769829598245425619/3171899622400000000000), (-24469773191402086854293440254855206163097558087/6479394766230547815171336873600000000000000000), (2098769829598245425619/3171899622400000000000), (-48563542045667682076000985931060931000132558087/12958789532461095630342673747200000000000000000)]
    bernstein := [(3155861295373421711313386746122630883485508394575673/20734063251937753008548277995520000000000000000000000000), (463628627903892489285437623183189818022856819640661/2764541766925033734473103732736000000000000000000000000), (1784226080448226493608067757445192347745980034962779/9952350360930121444103173437849600000000000000000000000), (82679052022611495292826922709417043294110587742501/442326682708005397515696597237760000000000000000000000), (101183763332065262344289618925113196459852632346713/530792019249606477018835916685312000000000000000000000)]
    reserve := (152206601/1000000000000) }

theorem tilt_042_018_valid : tilt_042_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_018]
  · intro i; fin_cases i <;> norm_num [tilt_042_018]
  · norm_num [tilt_042_018]
  · norm_num [tilt_042_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_018]

def tilt_042_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (42331/781250), (687291/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-78141667995042114264073510703989712285985969/2713287358341083535336896470900000000000000000), (11454986203101/17402012500000), (-5098216083274074258841860749590159581101300969/1356643679170541767668448235450000000000000000), (11454986203101/17402012500000), (-10118290498553106403419647988476329449916615969/2713287358341083535336896470900000000000000000)]
    bernstein := [(913722035297932405708975456456504714569085514373151/4341259773345733656539034353440000000000000000000000000), (392089664646665930686323336139953312226209207114121/1736503909338293462615613741376000000000000000000000000), (761610049419596032083388917997563168904874977477/3210793052705627357686805068800000000000000000000000), (67988478386001188229491555691835045230162208998361/277840625494126954018498198620160000000000000000000000), (27594044210794808208687035512306899124908947061631/111136250197650781607399279448064000000000000000000000)]
    reserve := (13154621/62500000000) }

theorem tilt_042_019_valid : tilt_042_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_019]
  · intro i; fin_cases i <;> norm_num [tilt_042_019]
  · norm_num [tilt_042_019]
  · norm_num [tilt_042_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_019]

def tilt_042_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/200), (7/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2678429/50000000), (1/100000000), (4176483/100000000), (2250969/50000000), (1/100000000), (42331/781250), (687291/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-78534464338215355159581266577851057506985969/2713287358341083535336896470900000000000000000), (11454986203101/17402012500000), (-5097793836855647836658838776335265157862300969/1356643679170541767668448235450000000000000000), (11454986203101/17402012500000), (-10117053209373080318158096286092679258217615969/2713287358341083535336896470900000000000000000)]
    bernstein := [(295113563044370812435164139666296273915657693373151/4341259773345733656539034353440000000000000000000000000), (144704917018495580425067798489297752203705516114121/1736503909338293462615613741376000000000000000000000000), (304305566950503535511040454928184437819307977477/3210793052705627357686805068800000000000000000000000), (28425971542589930758736224047797179425757477998361/277840625494126954018498198620160000000000000000000000), (11772909679377155752593722181839125238519046061631/111136250197650781607399279448064000000000000000000000)]
    reserve := (2124337/31250000000) }

theorem tilt_042_020_valid : tilt_042_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_042_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_042_020]
  · intro i; fin_cases i <;> norm_num [tilt_042_020]
  · norm_num [tilt_042_020]
  · norm_num [tilt_042_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_042_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_042_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_042_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_042_020]

def tiltBundle042_row : Alternative → Row
  | .zero => tilt_042_000
  | (.spike 0 false false) => tilt_042_001
  | (.spike 0 false true) => tilt_042_002
  | (.spike 0 true false) => tilt_042_003
  | (.spike 0 true true) => tilt_042_004
  | (.spike 1 false false) => tilt_042_005
  | (.spike 1 false true) => tilt_042_006
  | (.spike 1 true false) => tilt_042_007
  | (.spike 1 true true) => tilt_042_008
  | (.spike 2 false false) => tilt_042_009
  | (.spike 2 false true) => tilt_042_010
  | (.spike 2 true false) => tilt_042_011
  | (.spike 2 true true) => tilt_042_012
  | (.spike 3 false false) => tilt_042_013
  | (.spike 3 false true) => tilt_042_014
  | (.spike 3 true false) => tilt_042_015
  | (.spike 3 true true) => tilt_042_016
  | (.spike 4 false false) => tilt_042_017
  | (.spike 4 false true) => tilt_042_018
  | (.spike 4 true false) => tilt_042_019
  | (.spike 4 true true) => tilt_042_020

def tiltBundle042 : TiltBundle where
  interval := ⟨(17/200), (7/80)⟩
  lambda := ![(7480891/50000000), (7480891/50000000), (4994811/50000000), (14752587/100000000), (14752587/100000000), (15562171/100000000), (1501947/10000000)]
  row := tiltBundle042_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_042_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_042_001_valid | exact tilt_042_002_valid | exact tilt_042_003_valid | exact tilt_042_004_valid | exact tilt_042_005_valid | exact tilt_042_006_valid | exact tilt_042_007_valid | exact tilt_042_008_valid | exact tilt_042_009_valid | exact tilt_042_010_valid | exact tilt_042_011_valid | exact tilt_042_012_valid | exact tilt_042_013_valid | exact tilt_042_014_valid | exact tilt_042_015_valid | exact tilt_042_016_valid | exact tilt_042_017_valid | exact tilt_042_018_valid | exact tilt_042_019_valid | exact tilt_042_020_valid
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
