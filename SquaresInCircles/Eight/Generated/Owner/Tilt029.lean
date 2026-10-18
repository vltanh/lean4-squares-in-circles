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

def tilt_029_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (1387851/25000000), (238121/100000000)]
    alternative := .zero
    polynomial := [(-5279215466871515567277492744476363933227799/617741084709387445498023936175000000000000000), (44679289070799/70550500000000), (-3555851790177711640179170007189327049183227799/308870542354693722749011968087500000000000000), (44679289070799/70550500000000), (-7106424364888551764791062521634177734433227799/617741084709387445498023936175000000000000000)]
    bernstein := [(152620225436469094170530999533039189122072375401/1581417176856031860474941276608000000000000000000000), (1795627756819175630251993722990033786728481297009/12651337414848254883799530212864000000000000000000000), (51199839651898473990536042363171096135191742017643/303632097956358117211188725108736000000000000000000000), (142976549029306544262579848251186850098358650092929/809685594550288312563169933623296000000000000000000000), (1073976189648334138095765101085817940241120638119561/6477484756402306500505359468986368000000000000000000000)]
    reserve := (24127129/250000000000) }

theorem tilt_029_000_valid : tilt_029_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_000]
  · intro i; fin_cases i <;> norm_num [tilt_029_000]
  · norm_num [tilt_029_000]
  · norm_num [tilt_029_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_000]

def tilt_029_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14623/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (1387851/25000000), (242143/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-2870549871854467325890484445880451439257221/342640955590840266194447383650000000000000000), (26576433845012827159/42708274303750000000), (-1940434317723741349537989713846065131609257221/171320477795420133097223691825000000000000000), (26576433845012827159/42708274303750000000), (-3877998085575628231750088943246249811779257221/342640955590840266194447383650000000000000000)]
    bernstein := [(92608019808296612175624732860245511018511875579/877160846312551081457785302144000000000000000000000), (1050176489532386578974512496364411496900304193811/7017286770500408651662282417152000000000000000000000), (29524195874357658931380325535405722483207771866497/168414882492009807639894778011648000000000000000000000), (81973241328840465714004269488125319803729670759491/449106353312026153706386074697728000000000000000000000), (615481774034573774271665891757883642138941232688219/3592850826496209229651088597581824000000000000000000000)]
    reserve := (10557701/100000000000) }

theorem tilt_029_001_valid : tilt_029_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_001]
  · intro i; fin_cases i <;> norm_num [tilt_029_001]
  · norm_num [tilt_029_001]
  · norm_num [tilt_029_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_001]

def tilt_029_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4331/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1901/50000000), (423303/10000000), (864039/20000000), (1/100000000), (1387851/25000000), (117051/50000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-1824665598363902545342621288723246514140046483/209910102165341436095800750238700000000000000000), (53238572427587694457/82580065755000000000), (-409490213944463252049462850446254807217226682161/34985017027556906015966791706450000000000000000), (53238572427587694457/82580065755000000000), (-2455116618068415609751434481388805596789220046483/209910102165341436095800750238700000000000000000)]
    bernstein := [(61637233209856264383963634018751393351242834727917/537369861543274076405249920611072000000000000000000000), (231460615465349789631263562203477236856216927801351/1432986297448730870413999788296192000000000000000000000), (6510393698368880038170923911476329785364722800374077/34391671138769540889935994919108608000000000000000000000), (18161765269945343791713469992800268351252346918682231/91711123036718775706495986450956288000000000000000000000), (413163744816022849509016867104792171412481112995754637/2201066952881250616955903674822950912000000000000000000000)]
    reserve := (114701693/1000000000000) }

theorem tilt_029_002_valid : tilt_029_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_002]
  · intro i; fin_cases i <;> norm_num [tilt_029_002]
  · norm_num [tilt_029_002]
  · norm_num [tilt_029_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_002]

def tilt_029_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5516823/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (1387851/25000000), (242143/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-55877940471911398516368740366468485041617/6715110096340521659588869350000000000000000), (26576433845012827159/42708274303750000000), (-38028437284319383439263298697355155715041617/3357555048170260829794434675000000000000000), (26576433845012827159/42708274303750000000), (-76000996628166855480010228654343842945041617/6715110096340521659588869350000000000000000)]
    bernstein := [(2787340919519288501720285691193844531982263983/17190681846631735448547505536000000000000000000000), (28361267263797271329928387114131761866046483047/137525454773053883588380044288000000000000000000000), (765348589521769551536848469037227928271134789469/3300610914553293206121121062912000000000000000000000), (2104509737997661101990484031525428002672527688407/8801629105475448549656322834432000000000000000000000), (16046543106047830480770451580431728021636531941263/70413032843803588397250582675456000000000000000000000)]
    reserve := (32428509/200000000000) }

theorem tilt_029_003_valid : tilt_029_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_003]
  · intro i; fin_cases i <;> norm_num [tilt_029_003]
  · norm_num [tilt_029_003]
  · norm_num [tilt_029_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_003]

def tilt_029_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5522313/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (1387851/25000000), (117051/50000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-26485184297322245681251636231382230334197/3068772766197599590099604425000000000000000), (53238572427587694457/82580065755000000000), (-53878168337151342014646837018779476196002591/4603159149296399385149406637500000000000000), (53238572427587694457/82580065755000000000), (-107676881121410717292249919128864805701002591/9206318298592798770298813275000000000000000)]
    bernstein := [(1389252304159853927844976024233785421285915403/7856058281465854950654987328000000000000000000000), (42170960541655813027876177531502740069106821481/188545398755180518815719695872000000000000000000000), (1137824792300805328290228251831536058960833005587/4525089570124332451577272700928000000000000000000000), (3139617128963642171549889120118644369813469376761/12066905520331553204206060535808000000000000000000000), (8040353970415722024487096519391243942336045419883/32178414720884141877882828095488000000000000000000000)]
    reserve := (176838339/1000000000000) }

theorem tilt_029_004_valid : tilt_029_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_004]
  · intro i; fin_cases i <;> norm_num [tilt_029_004]
  · norm_num [tilt_029_004]
  · norm_num [tilt_029_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_004]

def tilt_029_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (431827/10000000), (1/100000000), (1387851/25000000), (242143/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-4307842138425451566747965482292056293329459/513732421557102560057878048350000000000000000), (26576433845012827159/42708274303750000000), (-2909358479367219834754326907870981281723329459/256866210778551280028939024175000000000000000), (26576433845012827159/42708274303750000000), (-5814409116596014217941905850259670507153329459/513732421557102560057878048350000000000000000)]
    bernstein := [(128761559620425365696602075699417908688377361741/1315154999186182553748167803776000000000000000000000), (1493847936252961175403026647059599793087738430069/10521239993489460429985342430208000000000000000000000), (42329245772053283779799770463099099928574604066263/252509759843747050319648218324992000000000000000000000), (117738463377960608675536508106379831632161509838789/673359359583325467519061915533312000000000000000000000), (881474780103604747120696169334864183957206472120301/5386874876666603740152495324266496000000000000000000000)]
    reserve := (19581199/200000000000) }

theorem tilt_029_005_valid : tilt_029_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_005]
  · intro i; fin_cases i <;> norm_num [tilt_029_005]
  · norm_num [tilt_029_005]
  · norm_num [tilt_029_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_005]

def tilt_029_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (4322121/100000000), (1/100000000), (1387851/25000000), (117051/50000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-26196595529043851497168187442890329042935991/3037928079273246216025308006150000000000000000), (53238572427587694457/82580065755000000000), (-1616259508704190852276577494859752832942994181/138087639966965737092059454825000000000000000), (53238572427587694457/82580065755000000000), (-11843837531987718299529178899823890665234311997/1012642693091082072008436002050000000000000000)]
    bernstein := [(1432659010204402714703790979558379871959164932809/7777095882939510313024788495744000000000000000000000), (14374696120751003990379312321085385114459218940881/62216767063516082504198307965952000000000000000000000), (35134512120262057032417750451633417545794148697217/135745673593125998190978126471168000000000000000000000), (1065400878340436713724423077784322509458417891368161/3981873092065029280268691709820928000000000000000000000), (8194605859553225227252551046973513685386956281302249/31854984736520234242149533678567424000000000000000000000)]
    reserve := (92107583/500000000000) }

theorem tilt_029_006_valid : tilt_029_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_006]
  · intro i; fin_cases i <;> norm_num [tilt_029_006]
  · norm_num [tilt_029_006]
  · norm_num [tilt_029_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_006]

def tilt_029_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (4231061/100000000), (864039/20000000), (1/100000000), (1387851/25000000), (242143/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-86154984396245669800992727633662794364812423/10274447269708479794791991137650000000000000000), (1594212313245701989263/2561304509307500000000), (-58187617025397727864699744562599929814175312423/5137223634854239897395995568825000000000000000), (1594212313245701989263/2561304509307500000000), (-116289079066399210059598496397566196833985812423/10274447269708479794791991137650000000000000000)]
    bernstein := [(2665077000335587954088656232569506853079611553977/26302585010453708274667497312384000000000000000000000), (30616665680162920558653998005059836723498206742593/210420680083629666197339978499072000000000000000000000), (864839816635796956308946719569760266516677647966811/5050096322007111988736159483977728000000000000000000000), (2404785808009557072975384398627381091447231218980433/13466923525352298636629758623940608000000000000000000000), (18040308957443842572633313038408328785490064565550297/107735388202818389093038068991524864000000000000000000000)]
    reserve := (101323767/1000000000000) }

theorem tilt_029_007_valid : tilt_029_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_007]
  · intro i; fin_cases i <;> norm_num [tilt_029_007]
  · norm_num [tilt_029_007]
  · norm_num [tilt_029_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_007]

def tilt_029_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (4234999/100000000), (864039/20000000), (1/100000000), (1387851/25000000), (117051/50000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-1190779739353831165716540260369833257344341/138090309147574340993106723387500000000000000), (1597544306885325688433/2478554339745000000000), (-2424372210699066166174895860759509594974658023/207135463721361511489660085081250000000000000), (1597544306885325688433/2478554339745000000000), (-4845172082180070838852642100737909690177283023/414270927442723022979320170162500000000000000)]
    bernstein := [(63914829274218284024123967048888348232826054459/353511191417790312942353211872000000000000000000000), (1930397816616650603442486965810052820292270187193/8484268594026967510616477084928000000000000000000000), (51966643502708291954163730990074860077919326931011/203622446256647220254795450038272000000000000000000000), (143267769994457164073437270055872077831007406873033/542993190017725920679454533435392000000000000000000000), (366967577537730620635991407099490605194158593887899/1447981840047269121811878755827712000000000000000000000)]
    reserve := (11300001/62500000000) }

theorem tilt_029_008_valid : tilt_029_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_008]
  · intro i; fin_cases i <;> norm_num [tilt_029_008]
  · norm_num [tilt_029_008]
  · norm_num [tilt_029_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_008]

def tilt_029_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (4318271/100000000), (1/100000000), (1387851/25000000), (242143/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-59233385210301849387941980448199891641743237/7063822432208939899647493115006250000000000000), (26576433845012827159/42708274303750000000), (-3636698990655467845773072669651095020504817567/321082837827679086347613323409375000000000000), (26576433845012827159/42708274303750000000), (-79948144409209990757619656751875890559464243237/7063822432208939899647493115006250000000000000)]
    bernstein := [(1769082368747160975355427460663358576970870678363/18083385426454886143097582374416000000000000000000000), (1866299738544294044316310596232096027851332909497/13151553037421735376798241726848000000000000000000000), (581760440303083476178047564677244837376537324059809/3472010001879338139474735815887872000000000000000000000), (147108423264537135991249685614274780359619132790857/841699394394991064115087470518272000000000000000000000), (12114587809715462583441057670920174210660739285056443/74069546706759213642127697405607936000000000000000000000)]
    reserve := (97829157/1000000000000) }

theorem tilt_029_009_valid : tilt_029_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_009]
  · intro i; fin_cases i <;> norm_num [tilt_029_009]
  · norm_num [tilt_029_009]
  · norm_num [tilt_029_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_009]

def tilt_029_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (2161061/50000000), (1/100000000), (1387851/25000000), (117051/50000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-406649496239155046622605440735967507406989/47467637221128821509522380223437500000000000), (53238572427587694457/82580065755000000000), (-75761453162093687817273427329686620338923497/6472859621063021114934870030468750000000000), (53238572427587694457/82580065755000000000), (-1665532021077343666840147584930897744934095967/142402911663386464528567140670312500000000000)]
    bernstein := [(29235209809180248238368594088853885248940263211/121517151286089783064377293372000000000000000000000), (838224654405558942097627036235276666965231798897/2916411630866154793545055040928000000000000000000000), (286524840736845883200980120167470680196272534447/909011417412827468117939233536000000000000000000000), (60464703040755232404139052517639968700768570402257/186650344375433906786883522619392000000000000000000000), (156107278519057052607596554030771038506067996356971/497734251667823751431689393651712000000000000000000000)]
    reserve := (240585049/1000000000000) }

theorem tilt_029_010_valid : tilt_029_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_010]
  · intro i; fin_cases i <;> norm_num [tilt_029_010]
  · norm_num [tilt_029_010]
  · norm_num [tilt_029_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_010]

def tilt_029_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(583/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (1387851/25000000), (242143/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-717682000783114394083796653607345165949649/85660238897710066548611845912500000000000000), (26576433845012827159/42708274303750000000), (-485108623963754834947108604003653515208449649/42830119448855033274305922956250000000000000), (26576433845012827159/42708274303750000000), (-969499565926726555500133411353699685250949649/85660238897710066548611845912500000000000000)]
    bernstein := [(23037858384605181061378422433365393436208733551/219290211578137770364446325536000000000000000000000), (261630878546300853285665545794573290755599480359/1754321692625102162915570604288000000000000000000000), (7359129333991149708915341981309593620016825928093/42103720623002451909973694502912000000000000000000000), (20434853029500141722440191053226427862528027824279/112276588328006538426596518674432000000000000000000000), (153402744013052771552003859462427802491814683781711/898212706624052307412772149395456000000000000000000000)]
    reserve := (52528241/500000000000) }

theorem tilt_029_011_valid : tilt_029_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_011]
  · intro i; fin_cases i <;> norm_num [tilt_029_011]
  · norm_num [tilt_029_011]
  · norm_num [tilt_029_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_011]

def tilt_029_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4317/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (3789/100000000), (1387851/25000000), (117051/50000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-40407507635391120295742331899307529686890593/4648719253635388984551926136270000000000000000), (53238572427587694457/82580065755000000000), (-9068667415660085386002181277932196578506963531/774786542272564830758654356045000000000000000), (53238572427587694457/82580065755000000000), (-54371596986325121195717345335693871941354890593/4648719253635388984551926136270000000000000000)]
    bernstein := [(1370088738573145187094367797223693406558997131807/11900721289306595800452930908851200000000000000000000), (5139465391486260507974926747404596498185512405021/31735256771484255467874482423603200000000000000000000), (144504359750520716178380914038677587578783842465167/761646162515622131228987578166476800000000000000000000), (403077866971275709704305437848070040087942010155501/2031056433374992349943966875110604800000000000000000000), (9170738605541508668653274763842787215903632077980927/48745354400999816398655205002654515200000000000000000000)]
    reserve := (115126529/1000000000000) }

theorem tilt_029_012_valid : tilt_029_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_012]
  · intro i; fin_cases i <;> norm_num [tilt_029_012]
  · norm_num [tilt_029_012]
  · norm_num [tilt_029_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_012]

def tilt_029_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (5548649/100000000), (242143/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-34193834683893126378760450278630591465946517/4109650954457272975657086274050000000000000000), (26576433845012827159/42708274303750000000), (-23273420371814185132723711407792308915955946517/2054825477228636487828543137025000000000000000), (26576433845012827159/42708274303750000000), (-46512646908944477139068662365305987240445946517/4109650954457272975657086274050000000000000000)]
    bernstein := [(1714811585035336975517798012518841314242241679083/10520706443410618817682140861568000000000000000000000), (17428775926707043884698498971179926002351573058947/84165651547284950541457126892544000000000000000000000), (470113850424844785777245331411206503285641452178769/2019975637134838812994971045421056000000000000000000000), (1292548417829742932052975986476679547360838083856307/5386601699026236834653256121122816000000000000000000000), (9857194849116017925872315311656262218677272065772363/43092813592209894677226048968982528000000000000000000000)]
    reserve := (81496979/500000000000) }

theorem tilt_029_013_valid : tilt_029_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_013]
  · intro i; fin_cases i <;> norm_num [tilt_029_013]
  · norm_num [tilt_029_013]
  · norm_num [tilt_029_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_013]

def tilt_029_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (69427/1250000), (117051/50000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-95361166499609301386057967670561090190977/11047570344183608593155399800000000000000000), (53238572427587694457/82580065755000000000), (-193961245915341681999292242330236090750572931/16571355516275412889733099700000000000000000), (53238572427587694457/82580065755000000000), (-387636408331184536094426310757460498230572931/33142711032550825779466199400000000000000000)]
    bernstein := [(4963871932424377294664176233768751439877562623/28281780081110037998477823488000000000000000000000), (150916881695230743506369839158526195152714240421/678762721946640911963467763712000000000000000000000), (4074601192786091964183150281425394226734799060967/16290305326719381887123226329088000000000000000000000), (11245101576463444940712125798245433731622563942901/43440814204585018365661936877568000000000000000000000), (28791875180001316669006909377067963636304270222303/115842171212226715641765165006848000000000000000000000)]
    reserve := (175514833/1000000000000) }

theorem tilt_029_014_valid : tilt_029_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_014]
  · intro i; fin_cases i <;> norm_num [tilt_029_014]
  · norm_num [tilt_029_014]
  · norm_num [tilt_029_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_014]

def tilt_029_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(583/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (1387851/25000000), (242143/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-717682000783114394083796653607345165949649/85660238897710066548611845912500000000000000), (26576433845012827159/42708274303750000000), (-485108623963754834947108604003653515208449649/42830119448855033274305922956250000000000000), (26576433845012827159/42708274303750000000), (-969499565926726555500133411353699685250949649/85660238897710066548611845912500000000000000)]
    bernstein := [(23037858384605181061378422433365393436208733551/219290211578137770364446325536000000000000000000000), (261630878546300853285665545794573290755599480359/1754321692625102162915570604288000000000000000000000), (7359129333991149708915341981309593620016825928093/42103720623002451909973694502912000000000000000000000), (20434853029500141722440191053226427862528027824279/112276588328006538426596518674432000000000000000000000), (153402744013052771552003859462427802491814683781711/898212706624052307412772149395456000000000000000000000)]
    reserve := (52528241/500000000000) }

theorem tilt_029_015_valid : tilt_029_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_015]
  · intro i; fin_cases i <;> norm_num [tilt_029_015]
  · norm_num [tilt_029_015]
  · norm_num [tilt_029_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_015]

def tilt_029_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4317/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (3789/100000000), (1387851/25000000), (117051/50000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-40407507635391120295742331899307529686890593/4648719253635388984551926136270000000000000000), (53238572427587694457/82580065755000000000), (-9068667415660085386002181277932196578506963531/774786542272564830758654356045000000000000000), (53238572427587694457/82580065755000000000), (-54371596986325121195717345335693871941354890593/4648719253635388984551926136270000000000000000)]
    bernstein := [(1370088738573145187094367797223693406558997131807/11900721289306595800452930908851200000000000000000000), (5139465391486260507974926747404596498185512405021/31735256771484255467874482423603200000000000000000000), (144504359750520716178380914038677587578783842465167/761646162515622131228987578166476800000000000000000000), (403077866971275709704305437848070040087942010155501/2031056433374992349943966875110604800000000000000000000), (9170738605541508668653274763842787215903632077980927/48745354400999816398655205002654515200000000000000000000)]
    reserve := (115126529/1000000000000) }

theorem tilt_029_016_valid : tilt_029_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_016]
  · intro i; fin_cases i <;> norm_num [tilt_029_016]
  · norm_num [tilt_029_016]
  · norm_num [tilt_029_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_016]

def tilt_029_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (5548649/100000000), (242143/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-34193941710662777991174497196396227433646517/4109650954457272975657086274050000000000000000), (26576433845012827159/42708274303750000000), (-23273420478840954784336125454710074551923646517/2054825477228636487828543137025000000000000000), (26576433845012827159/42708274303750000000), (-46512647015971246790681076412223752876413646517/4109650954457272975657086274050000000000000000)]
    bernstein := [(1714537253912339192926500538855045436197633979083/10520706443410618817682140861568000000000000000000000), (17426581106373203411736644292754216194810423758947/84165651547284950541457126892544000000000000000000000), (470061170452872105581070722073012062793774741078769/2019975637134838812994971045421056000000000000000000000), (1292407926022976969835859291098949899149329950556307/5386601699026236834653256121122816000000000000000000000), (9856070815947996802133355513154809171728754226072363/43092813592209894677226048968982528000000000000000000000)]
    reserve := (81483941/500000000000) }

theorem tilt_029_017_valid : tilt_029_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_017]
  · intro i; fin_cases i <;> norm_num [tilt_029_017]
  · norm_num [tilt_029_017]
  · norm_num [tilt_029_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_017]

def tilt_029_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (5554161/100000000), (117051/50000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-237888945928382438420948287607469688228799/27618930833114807498959603481250000000000000), (53238572427587694457/82580065755000000000), (-161633886684371303651812342100206365871978799/13809465416557403749479801740625000000000000), (53238572427587694457/82580065755000000000), (-323029884422814224865203735912805262055728799/27618930833114807498959603481250000000000000)]
    bernstein := [(13727201326265518794717832872311776636836674401/70704462932773907197336584912000000000000000000000), (136305067744990336164744305668825830393684088009/565635703462191257578692679296000000000000000000000), (3648505628278141596131449572708428451395286474643/13575256883092590181888624303104000000000000000000000), (10045654124935485633645862148583371393032005963929/36200685021580240485036331474944000000000000000000000), (77378050657805636639849272809019393534947460258561/289605480172641923880290651799552000000000000000000000)]
    reserve := (194149007/1000000000000) }

theorem tilt_029_018_valid : tilt_029_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_018]
  · intro i; fin_cases i <;> norm_num [tilt_029_018]
  · norm_num [tilt_029_018]
  · norm_num [tilt_029_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_018]

def tilt_029_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (1387851/25000000), (238121/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-5178971327904503068067210443990008150933549/617741084709387445498023936175000000000000000), (44679289070799/70550500000000), (-3555855250709836392537056965529305239111278549/308870542354693722749011968087500000000000000), (44679289070799/70550500000000), (-7106531530091768282006046720614620470071623549/617741084709387445498023936175000000000000000)]
    bernstein := [(409234040324018668086400437891199341289951579651/1581417176856031860474941276608000000000000000000000), (3848532631902969401289115112312369457450995335259/12651337414848254883799530212864000000000000000000000), (100469415339164047555146672799935552681547812250393/303632097956358117211188725108736000000000000000000000), (274361691626602907368745522450593071157703030791179/809685594550288312563169933623296000000000000000000000), (2125054063076865726331012150393887066123903722003811/6477484756402306500505359468986368000000000000000000000)]
    reserve := (258776777/1000000000000) }

theorem tilt_029_019_valid : tilt_029_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_019]
  · intro i; fin_cases i <;> norm_num [tilt_029_019]
  · norm_num [tilt_029_019]
  · norm_num [tilt_029_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_019]

def tilt_029_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/40), (9/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5519567/100000000), (1/100000000), (423303/10000000), (864039/20000000), (1/100000000), (1387851/25000000), (238121/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-5277910061997479839427307323379019565433549/617741084709387445498023936175000000000000000), (44679289070799/70550500000000), (-3555753700586501202077960765943370356395778549/308870542354693722749011968087500000000000000), (44679289070799/70550500000000), (-7106229491111004924316494224563361693226123549/617741084709387445498023936175000000000000000)]
    bernstein := [(156276143479651506231349817826373003636397079651/1581417176856031860474941276608000000000000000000000), (1825032239384349174540953623627305827344204835259/12651337414848254883799530212864000000000000000000000), (17303158692901016780737420990774934951526556250131/101210699318786039070396241702912000000000000000000000), (144879810024213007094489021736544271902618600291179/809685594550288312563169933623296000000000000000000000), (1089292819037829212151818885989515627642153447503811/6477484756402306500505359468986368000000000000000000000)]
    reserve := (49410157/500000000000) }

theorem tilt_029_020_valid : tilt_029_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_029_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_029_020]
  · intro i; fin_cases i <;> norm_num [tilt_029_020]
  · norm_num [tilt_029_020]
  · norm_num [tilt_029_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_029_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_029_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_029_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_029_020]

def tiltBundle029_row : Alternative → Row
  | .zero => tilt_029_000
  | (.spike 0 false false) => tilt_029_001
  | (.spike 0 false true) => tilt_029_002
  | (.spike 0 true false) => tilt_029_003
  | (.spike 0 true true) => tilt_029_004
  | (.spike 1 false false) => tilt_029_005
  | (.spike 1 false true) => tilt_029_006
  | (.spike 1 true false) => tilt_029_007
  | (.spike 1 true true) => tilt_029_008
  | (.spike 2 false false) => tilt_029_009
  | (.spike 2 false true) => tilt_029_010
  | (.spike 2 true false) => tilt_029_011
  | (.spike 2 true true) => tilt_029_012
  | (.spike 3 false false) => tilt_029_013
  | (.spike 3 false true) => tilt_029_014
  | (.spike 3 true false) => tilt_029_015
  | (.spike 3 true true) => tilt_029_016
  | (.spike 4 false false) => tilt_029_017
  | (.spike 4 false true) => tilt_029_018
  | (.spike 4 true false) => tilt_029_019
  | (.spike 4 true true) => tilt_029_020

def tiltBundle029 : TiltBundle where
  interval := ⟨(1/40), (9/320)⟩
  lambda := ![(14622663/100000000), (14622663/100000000), (4468819/50000000), (7287627/50000000), (7287627/50000000), (8219473/50000000), (811379/5000000)]
  row := tiltBundle029_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_029_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_029_001_valid | exact tilt_029_002_valid | exact tilt_029_003_valid | exact tilt_029_004_valid | exact tilt_029_005_valid | exact tilt_029_006_valid | exact tilt_029_007_valid | exact tilt_029_008_valid | exact tilt_029_009_valid | exact tilt_029_010_valid | exact tilt_029_011_valid | exact tilt_029_012_valid | exact tilt_029_013_valid | exact tilt_029_014_valid | exact tilt_029_015_valid | exact tilt_029_016_valid | exact tilt_029_017_valid | exact tilt_029_018_valid | exact tilt_029_019_valid | exact tilt_029_020_valid
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
