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

def tilt_015_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(336983/100000000), 0, (2021537/100000000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (2665419/50000000), (887/3125000)]
    alternative := .zero
    polynomial := [(-58765812143462069434023544224849750887153/8161203396259275855780343387500000000000000), (-838539805827958041/389812373600000000), (-465660873926289300856982515074766941305574653/4080601698129637927890171693750000000000000), (-838539805827958041/389812373600000000), (-931262982040435139644531006605309032860262153/8161203396259275855780343387500000000000000)]
    bernstein := [(621569897923681869777747779585780999584247299447/334282891110779939052762865152000000000000000000000), (658698804722076996365888420722508649769115046749/222855260740519959368508576768000000000000000000000), (13273401516791666944253597218700627679722290523941/4011394693329359268633154381824000000000000000000000), (2602261797544716340714601068738042833682238507549/891421042962079837474034307072000000000000000000000), (9556106630298297922663327285089735646049627424247/5348526257772479024844205842432000000000000000000000)]
    reserve := (446670081/250000000000) }

theorem tilt_015_000_valid : tilt_015_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_000]
  · intro i; fin_cases i <;> norm_num [tilt_015_000]
  · norm_num [tilt_015_000]
  · norm_num [tilt_015_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_000]

def tilt_015_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3017/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(319013/100000000), 0, (1010937/50000000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (2665419/50000000), (5677/20000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-754830129710642669333841796625799024968453/104467083834416931303866988525000000000000000), (-104817877392068281559/48728263390625000000), (-5960468318448752219941758857381340601764668453/52233541917208465651933494262500000000000000), (-104817877392068281559/48728263390625000000), (-11920181806767793797214183872966055404504368453/104467083834416931303866988525000000000000000)]
    bernstein := [(7848786749446892558390527228019574722258880553147/4278971753857717506206391849984000000000000000000000), (8359788800232774197202821781292297685413370524649/2852647835905145004137594566656000000000000000000000), (168611163945488367011870227019130927467976245045041/51347661046292610074476702199808000000000000000000000), (33022550313661616828327107925050534838309518665449/11410591343620580016550378266624000000000000000000000), (120599112613361141988314015220039832563755464757947/68463548061723480099302269599744000000000000000000000)]
    reserve := (352301673/200000000000) }

theorem tilt_015_001_valid : tilt_015_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_001]
  · intro i; fin_cases i <;> norm_num [tilt_015_001]
  · norm_num [tilt_015_001]
  · norm_num [tilt_015_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_001]

def tilt_015_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1117/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(177477/50000000), 0, (5053/250000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1961/50000000), (549341/12500000), (1017409/25000000), (1/100000000), (2665419/50000000), (887/3125000)]
    alternative := (.spike 0 false true)
    polynomial := [(-457527752353655992351425270407220349050098551/64016479440257759812741013531550000000000000000), (-209635240267702090029/97453093400000000000), (-3652644102906732860573477366127807810596713036051/32008239720128879906370506765775000000000000000), (-209635240267702090029/97453093400000000000), (-7304830678061112065154603306985208400844375973551/64016479440257759812741013531550000000000000000)]
    bernstein := [(135573889654515875064601178727278136167429460908477/70867972915485347079185727412224000000000000000000000), (142177987271540267288959866460386882623581283413759/47245315276990231386123818274816000000000000000000000), (105803960297042074459037239519007718197932015215116147/31465379974475494103158462971027456000000000000000000000), (20787087849569493195528383489685873606477801747662683/6992306660994554245146325104672768000000000000000000000), (77207589295690811280459680857837786231452753674855249/41953839965967325470877950628036608000000000000000000000)]
    reserve := (115018657/62500000000) }

theorem tilt_015_002_valid : tilt_015_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_002]
  · intro i; fin_cases i <;> norm_num [tilt_015_002]
  · norm_num [tilt_015_002]
  · norm_num [tilt_015_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_002]

def tilt_015_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(319013/100000000), 0, (1010937/50000000), 0, 0]] i.1) i.2
    mu := ![(5926317/100000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (2665419/50000000), (5677/20000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-1196244152927345285969168153400790393240243/167065046456124936183734727330000000000000000), (-104817877392068281559/48728263390625000000), (-9532043418650130701157487455119198144555680243/83532523228062468091867363665000000000000000), (-104817877392068281559/48728263390625000000), (-19062890593147334057029005742084995498718120243/167065046456124936183734727330000000000000000)]
    bernstein := [(12998048985681723669929742439742362543192176689357/6842984302842877386085774431436800000000000000000000), (13666502322024044700364997300526777431169032884719/4561989535228584924057182954291200000000000000000000), (274998353435105082696017508075564632910630568461671/82115811634114528633029293177241600000000000000000000), (53999630227710473401262609437309970156820471969519/18247958140914339696228731817164800000000000000000000), (200000674237018265244269394699872968184300391358157/109487748845486038177372390902988800000000000000000000)]
    reserve := (1826694551/1000000000000) }

theorem tilt_015_003_valid : tilt_015_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_003]
  · intro i; fin_cases i <;> norm_num [tilt_015_003]
  · norm_num [tilt_015_003]
  · norm_num [tilt_015_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_003]

def tilt_015_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(177477/50000000), 0, (5053/250000), 0, 0]] i.1) i.2
    mu := ![(1483039/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (2665419/50000000), (887/3125000)]
    alternative := (.spike 0 true true)
    polynomial := [(-926249668792254437721227771770269392275853/130643561347437925084506668200000000000000000), (-209635240267702090029/97453093400000000000), (-7454236163856556684805031241211145949261525853/65321780673718962542253334100000000000000000), (-209635240267702090029/97453093400000000000), (-14907546078044321115172341254650521629130775853/130643561347437925084506668200000000000000000)]
    bernstein := [(10542847242621094877566815194720258743457759425747/5351160272791057411461393129472000000000000000000000), (32818681146810518088793763331216242809330395086547/10702320545582114822922786258944000000000000000000000), (219591896673086664199311470983736442181334510142841/64213923273492688937536717553664000000000000000000000), (129711684419872301106299840839678037948158145428947/42809282182328459291691145035776000000000000000000000), (162455635244206111735123169989673745616208443470547/85618564364656918583382290071552000000000000000000000)]
    reserve := (948717351/500000000000) }

theorem tilt_015_004_valid : tilt_015_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_004]
  · intro i; fin_cases i <;> norm_num [tilt_015_004]
  · norm_num [tilt_015_004]
  · norm_num [tilt_015_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_004]

def tilt_015_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(319013/100000000), 0, (1010937/50000000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (4067841/100000000), (1/100000000), (2665419/50000000), (5677/20000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-1009172270535804464656673439930719702622629/139228008523638118741513522575000000000000000), (-104817877392068281559/48728263390625000000), (-7943788944560479641778669899789459063397722629/69614004261819059370756761287500000000000000), (-104817877392068281559/48728263390625000000), (-15886568716850423479092683126138987407092822629/139228008523638118741513522575000000000000000)]
    bernstein := [(10330303158203884750650586377456518988778181686171/5702779229128217343652393884672000000000000000000000), (11054722153741863955028373668140163474790075006857/3801852819418811562434929256448000000000000000000000), (223154389378350088600704047084262866142829528719313/68433350749538608123828726616064000000000000000000000), (43663701091367710849395119885601259147855650501257/15207411277675246249739717025792000000000000000000000), (158646300825264284828685897999352541177888583132571/91244467666051477498438302154752000000000000000000000)]
    reserve := (434673753/250000000000) }

theorem tilt_015_005_valid : tilt_015_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_005]
  · intro i; fin_cases i <;> norm_num [tilt_015_005]
  · norm_num [tilt_015_005]
  · norm_num [tilt_015_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_005]

def tilt_015_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(177477/50000000), 0, (5053/250000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (508929/12500000), (1/100000000), (2665419/50000000), (887/3125000)]
    alternative := (.spike 1 false true)
    polynomial := [(-4527346632352162025449283316750725982367/640376868624290241307730100000000000000000), (-209635240267702090029/97453093400000000000), (-36538492086315566173957763243872189175607367/320188434312145120653865050000000000000000), (-209635240267702090029/97453093400000000000), (-73072456825998780185890077204427627625232367/640376868624290241307730100000000000000000)]
    bernstein := [(52204922367234052128555732035101105294328150033/26229836538850928283964624896000000000000000000000), (3174930628160271720911268476014264598442327083/1028621040739252089567240192000000000000000000000), (1082698214134466763280244480585520372411223528499/314758038466211139407575498752000000000000000000000), (12549485969108454835128895714286096366159280683/4114484162957008358268960768000000000000000000000), (804739517145508082180746156961022050424200457233/419677384621614852543433998336000000000000000000000)]
    reserve := (1917519377/1000000000000) }

theorem tilt_015_006_valid : tilt_015_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_006]
  · intro i; fin_cases i <;> norm_num [tilt_015_006]
  · norm_num [tilt_015_006]
  · norm_num [tilt_015_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_006]

def tilt_015_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(319013/100000000), 0, (1010937/50000000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (274557/6250000), (1017409/25000000), (1/100000000), (2665419/50000000), (5677/20000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-252192393160785776571939804199930416269003/34807971898846083347132665950000000000000000), (-419075343968686844819/194832511125000000000), (-1986007412729251295918651646534496834011494003/17403985949423041673566332975000000000000000), (-419075343968686844819/194832511125000000000), (-3971762633065341806060731353264793737606719003/34807971898846083347132665950000000000000000)]
    bernstein := [(2584901012036732658180787212571936373744875162597/1425734528976735573898553997312000000000000000000000), (921814932998784921422767186158861198428060295933/316829895328163460866345332736000000000000000000000), (55823822322513099276818977329380765435644780233391/17108814347720826886782647967744000000000000000000000), (3641479370519529590791881877893186976653607169533/1267319581312653843465381330944000000000000000000000), (39716248845730605819521970054511117207527230247397/22811752463627769182376863956992000000000000000000000)]
    reserve := (870521651/500000000000) }

theorem tilt_015_007_valid : tilt_015_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_007]
  · intro i; fin_cases i <;> norm_num [tilt_015_007]
  · norm_num [tilt_015_007]
  · norm_num [tilt_015_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_007]

def tilt_015_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(177477/50000000), 0, (5053/250000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (17174/390625), (1017409/25000000), (1/100000000), (2665419/50000000), (887/3125000)]
    alternative := (.spike 1 true true)
    polynomial := [(-7218409659516205742123794057671320677919/1020571973527239390813149700000000000000000), (-422849440425948577/196559200000000000), (-116462888964452968668366863428965515412902713/1020571973527239390813149700000000000000000), (-422849440425948577/196559200000000000), (-58227835277396726231312369817453922046112397/510285986763619695406574850000000000000000)]
    bernstein := [(41566657961243674494409612429877160649539086003/20901314017837862723853305856000000000000000000000), (42984488587517651986387005704339862415092458401/13934209345225241815902203904000000000000000000000), (862258118549517207986182799855483287099059292409/250815768214054352686239670272000000000000000000000), (169881394781055091800355709707101457992328377601/55736837380900967263608815616000000000000000000000), (640474675535702941375442070495343462557611241203/334421024285405803581652893696000000000000000000000)]
    reserve := (119698417/62500000000) }

theorem tilt_015_008_valid : tilt_015_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_008]
  · intro i; fin_cases i <;> norm_num [tilt_015_008]
  · norm_num [tilt_015_008]
  · norm_num [tilt_015_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_008]

def tilt_015_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(319013/100000000), 0, (1010937/50000000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (2033921/50000000), (1/100000000), (2665419/50000000), (5677/20000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-1211019550277207086267634927700299155334243/167073651300180060789312812580000000000000000), (-104817877392068281559/48728263390625000000), (-9532549089392673619060219475434775598314774243/83536825650090030394656406290000000000000000), (-104817877392068281559/48728263390625000000), (-19063887159235070031034171315941850897474214243/167073651300180060789312812580000000000000000)]
    bernstein := [(12395853532799557462754337366473593125704537395357/6843336757255375289930252803276800000000000000000000), (13265327669360594747176999999734871593324152586719/4562224504836916859953501868851200000000000000000000), (267779174312510372888514904483095914895812719379671/82120041087064503479163033639321600000000000000000000), (52395085645714206110503766245888488405801870071519/18248898019347667439814007475404800000000000000000000), (190367396843722904798862721976210643669691702464157/109493388116086004638884044852428800000000000000000000)]
    reserve := (1738620021/1000000000000) }

theorem tilt_015_009_valid : tilt_015_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_009]
  · intro i; fin_cases i <;> norm_num [tilt_015_009]
  · norm_num [tilt_015_009]
  · norm_num [tilt_015_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_009]

def tilt_015_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(177477/50000000), 0, (5053/250000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (4071433/100000000), (1/100000000), (2665419/50000000), (887/3125000)]
    alternative := (.spike 2 false true)
    polynomial := [(-366550291462806338342232658454640053147837/52254765314231884758758502540000000000000000), (-209635240267702090029/97453093400000000000), (-2981538805266563459194211895457655169831122837/26127382657115942379379251270000000000000000), (-209635240267702090029/97453093400000000000), (-5962711060241664112050081558256855699609097837/52254765314231884758758502540000000000000000)]
    bernstein := [(4377977006864611019112067559484954970055007068563/2140355187270937999718748264038400000000000000000000), (4482961565033135565635604874438221665675638463921/1426903458180625333145832176025600000000000000000000), (89764644649378947000618928819877800394354274428089/25684262247251255996624979168460800000000000000000000), (17723401192433596151884831437498892273246777267121/5707613832722501332583328704102400000000000000000000), (67555186845661727971397460853702754931370029327763/34245682996335007995499972224614400000000000000000000)]
    reserve := (246582857/125000000000) }

theorem tilt_015_010_valid : tilt_015_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_010]
  · intro i; fin_cases i <;> norm_num [tilt_015_010]
  · norm_num [tilt_015_010]
  · norm_num [tilt_015_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_010]

def tilt_015_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1381/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(319013/100000000), 0, (1010937/50000000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (2665419/50000000), (5677/20000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-756273127570398300107358656635335125649953/104467083834416931303866988525000000000000000), (-104817877392068281559/48728263390625000000), (-5960469761446611975572532374241350137865349953/52233541917208465651933494262500000000000000), (-104817877392068281559/48728263390625000000), (-11920183249765653552844957389826064940605049953/104467083834416931303866988525000000000000000)]
    bernstein := [(7789663085295699190077744852703993966719816671647/4278971753857717506206391849984000000000000000000000), (8320376103008412050258493958222217528580815364149/2852647835905145004137594566656000000000000000000000), (167901781575710354126323971063940369828820362200541/51347661046292610074476702199808000000000000000000000), (32864917996579770972379328422095196282604121904949/11410591343620580016550378266624000000000000000000000), (119653355653058274456530771007440905363236631276447/68463548061723480099302269599744000000000000000000000)]
    reserve := (1747694343/1000000000000) }

theorem tilt_015_011_valid : tilt_015_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_011]
  · intro i; fin_cases i <;> norm_num [tilt_015_011]
  · norm_num [tilt_015_011]
  · norm_num [tilt_015_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_011]

def tilt_015_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4091/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(177477/50000000), 0, (5053/250000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (359/10000000), (2665419/50000000), (887/3125000)]
    alternative := (.spike 2 true true)
    polynomial := [(-41812893645858272013886343265048449331447341/5859744038514160064450286552225000000000000000), (-209635240267702090029/97453093400000000000), (-334344459625013052164064934983705337051807478591/2929872019257080032225143276112500000000000000), (-209635240267702090029/97453093400000000000), (-668647106356380246056115983624145625654283509841/5859744038514160064450286552225000000000000000)]
    bernstein := [(461900791686057273453397662812931810527744333165359/240015115817539996239883737179136000000000000000000000), (483353968490727231905473328194801032635874580107653/160010077211693330826589158119424000000000000000000000), (9717635498038257031111222877130188765990820317379277/2880181389810479954878604846149632000000000000000000000), (1910050336139276280580484511038255222788099447405253/640040308846773323306356632477696000000000000000000000), (7111023744063115992466866033586981237962220274870959/3840241853080639939838139794866176000000000000000000000)]
    reserve := (925856237/500000000000) }

theorem tilt_015_012_valid : tilt_015_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_012]
  · intro i; fin_cases i <;> norm_num [tilt_015_012]
  · norm_num [tilt_015_012]
  · norm_num [tilt_015_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_012]

def tilt_015_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(319013/100000000), 0, (1010937/50000000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (26641/500000), (5677/20000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-359977798398231693254663637947428357334809/50119386055539361882534558800000000000000000), (-104817877392068281559/48728263390625000000), (-2859606834683099721284761436992993887795734809/25059693027769680941267279400000000000000000), (-104817877392068281559/48728263390625000000), (-5718853691567801210876268210348040347234134809/50119386055539361882534558800000000000000000)]
    bernstein := [(3854110617883194584716432370412927585574255669991/2052890052834892262708615528448000000000000000000000), (4069746508599837115339625602515349461791114750797/1368593368556594841805743685632000000000000000000000), (81955843825407604307753785207101994539094465806773/24634680634018707152503386341376000000000000000000000), (16079086977467268714520041653783350729303370693197/5474373474226379367222974742528000000000000000000000), (59275512941715296602380981680640820112936861404391/32846240845358276203337848455168000000000000000000000)]
    reserve := (1804636129/1000000000000) }

theorem tilt_015_013_valid : tilt_015_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_013]
  · intro i; fin_cases i <;> norm_num [tilt_015_013]
  · norm_num [tilt_015_013]
  · norm_num [tilt_015_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_013]

def tilt_015_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(177477/50000000), 0, (5053/250000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (1333369/25000000), (887/3125000)]
    alternative := (.spike 3 false true)
    polynomial := [(-1387553968338076768864382704361487559603213/195965808505457509926284412600000000000000000), (-209635240267702090029/97453093400000000000), (-11181379038517617519561843409805376805637353213/97982904252728754963142206300000000000000000), (-209635240267702090029/97453093400000000000), (-22361370523066896962354822436906392123715103213/195965808505457509926284412600000000000000000)]
    bernstein := [(429433417066775997089036334401639620365649710551/216939446388744313691367825408000000000000000000000), (444843090769700495893285008996480843492144092317/144626297592496209127578550272000000000000000000000), (330285235754521847674767195587239495615266973608761/96321114196602475278967314481152000000000000000000000), (65055232142863172136747147533922906447644141892529/21404692043689438950881625440256000000000000000000000), (244879399532463054123070463283526184256831088711187/128428152262136633705289752641536000000000000000000000)]
    reserve := (190674237/100000000000) }

theorem tilt_015_014_valid : tilt_015_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_014]
  · intro i; fin_cases i <;> norm_num [tilt_015_014]
  · norm_num [tilt_015_014]
  · norm_num [tilt_015_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_014]

def tilt_015_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1381/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(319013/100000000), 0, (1010937/50000000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (2665419/50000000), (5677/20000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-756273127570398300107358656635335125649953/104467083834416931303866988525000000000000000), (-104817877392068281559/48728263390625000000), (-5960469761446611975572532374241350137865349953/52233541917208465651933494262500000000000000), (-104817877392068281559/48728263390625000000), (-11920183249765653552844957389826064940605049953/104467083834416931303866988525000000000000000)]
    bernstein := [(7789663085295699190077744852703993966719816671647/4278971753857717506206391849984000000000000000000000), (8320376103008412050258493958222217528580815364149/2852647835905145004137594566656000000000000000000000), (167901781575710354126323971063940369828820362200541/51347661046292610074476702199808000000000000000000000), (32864917996579770972379328422095196282604121904949/11410591343620580016550378266624000000000000000000000), (119653355653058274456530771007440905363236631276447/68463548061723480099302269599744000000000000000000000)]
    reserve := (1747694343/1000000000000) }

theorem tilt_015_015_valid : tilt_015_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_015]
  · intro i; fin_cases i <;> norm_num [tilt_015_015]
  · norm_num [tilt_015_015]
  · norm_num [tilt_015_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_015]

def tilt_015_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4091/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(177477/50000000), 0, (5053/250000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (359/10000000), (2665419/50000000), (887/3125000)]
    alternative := (.spike 3 true true)
    polynomial := [(-41812893645858272013886343265048449331447341/5859744038514160064450286552225000000000000000), (-209635240267702090029/97453093400000000000), (-334344459625013052164064934983705337051807478591/2929872019257080032225143276112500000000000000), (-209635240267702090029/97453093400000000000), (-668647106356380246056115983624145625654283509841/5859744038514160064450286552225000000000000000)]
    bernstein := [(461900791686057273453397662812931810527744333165359/240015115817539996239883737179136000000000000000000000), (483353968490727231905473328194801032635874580107653/160010077211693330826589158119424000000000000000000000), (9717635498038257031111222877130188765990820317379277/2880181389810479954878604846149632000000000000000000000), (1910050336139276280580484511038255222788099447405253/640040308846773323306356632477696000000000000000000000), (7111023744063115992466866033586981237962220274870959/3840241853080639939838139794866176000000000000000000000)]
    reserve := (925856237/500000000000) }

theorem tilt_015_016_valid : tilt_015_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_016]
  · intro i; fin_cases i <;> norm_num [tilt_015_016]
  · norm_num [tilt_015_016]
  · norm_num [tilt_015_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_016]

def tilt_015_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(319013/100000000), 0, (1010937/50000000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (26641/500000), (5677/20000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-44997411983620796055965500134178345933373/6264923256942420235316819850000000000000000), (-104817877392068281559/48728263390625000000), (-357450854522571306994994312169514985775733373/3132461628471210117658409925000000000000000), (-104817877392068281559/48728263390625000000), (-714856711633158993193932658838895793205533373/6264923256942420235316819850000000000000000)]
    bernstein := [(481756157789097426778941691382957100114033212227/256611256604361532838576941056000000000000000000000), (508713201010166299071041246176328180494692515009/171074171069574355225717960704000000000000000000000), (10244388457999754902460083415252260443151197806281/3079335079252338394062923292672000000000000000000000), (2009865424320295587251500685884103820452146767809/684296684278297420902871842816000000000000000000000), (7409316435327827597719047777341760975514684489027/4105780105669784525417231056896000000000000000000000)]
    reserve := (225575781/125000000000) }

theorem tilt_015_017_valid : tilt_015_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_017]
  · intro i; fin_cases i <;> norm_num [tilt_015_017]
  · norm_num [tilt_015_017]
  · norm_num [tilt_015_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_017]

def tilt_015_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(177477/50000000), 0, (5053/250000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (1333369/25000000), (887/3125000)]
    alternative := (.spike 4 false true)
    polynomial := [(-691683252011576859353331467391507665863169/97982904252728754963142206300000000000000000), (-209635240267702090029/97453093400000000000), (-5590687425526651298255842845017899166704738169/48991452126364377481571103150000000000000000), (-209635240267702090029/97453093400000000000), (-11180683167801291019652332358568406825743613169/97982904252728754963142206300000000000000000)]
    bernstein := [(217035250993792639955670474399530573383174204963/108469723194372156845683912704000000000000000000000), (223967119619898928606131161710691417930401162721/72313148796248104563789275136000000000000000000000), (166171903312093109915415944744219201343042306619693/48160557098301237639483657240576000000000000000000000), (32756334256353443140995360549019013647608254259077/10702346021844719475440812720128000000000000000000000), (123811955274125706324762408442197965437379706294031/64214076131068316852644876320768000000000000000000000)]
    reserve := (1928112381/1000000000000) }

theorem tilt_015_018_valid : tilt_015_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_018]
  · intro i; fin_cases i <;> norm_num [tilt_015_018]
  · norm_num [tilt_015_018]
  · norm_num [tilt_015_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_018]

def tilt_015_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(167481/50000000), 0, (1010937/50000000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (2665419/50000000), (887/3125000)]
    alternative := (.spike 4 true false)
    polynomial := [(-117854060526017104900355084634026923140181/16322406792518551711560686775000000000000000), (-419270981634332844119/194906186800000000000), (-1862645999763307138421335845991828632970845737/16322406792518551711560686775000000000000000), (-419270981634332844119/194906186800000000000), (-465632036425695280329108872726798651511926389/4080601698129637927890171693750000000000000)]
    bernstein := [(307490759825268651103108612460860693201115204411/167141445555389969526381432576000000000000000000000), (327152980150325460364958285054435285549114537437/111427630370259979684254288384000000000000000000000), (6597157826276416253181451019111802615201679151033/2005697346664679634316577190912000000000000000000000), (1292341506221683263006627699935954434066436692837/445710521481039918737017153536000000000000000000000), (4725301844299588368813385102547775018826687816811/2674263128886239512422102921216000000000000000000000)]
    reserve := (883477357/500000000000) }

theorem tilt_015_019_valid : tilt_015_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_019]
  · intro i; fin_cases i <;> norm_num [tilt_015_019]
  · norm_num [tilt_015_019]
  · norm_num [tilt_015_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_019]

def tilt_015_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(67801/20000000), 0, (5053/250000), 0, 0]] i.1) i.2
    mu := ![(1482309/25000000), (1/100000000), (549341/12500000), (1017409/25000000), (1/100000000), (2665419/50000000), (887/3125000)]
    alternative := (.spike 4 true true)
    polynomial := [(-28651748969808695534111050806364598124889/4080601698129637927890171693750000000000000), (-4192708903010305753/1949061868000000000), (-1862639502223105987941565110460581973230720737/16322406792518551711560686775000000000000000), (-4192708903010305753/1949061868000000000), (-1862524895227226753159428666257356514838221181/16322406792518551711560686775000000000000000)]
    bernstein := [(1363000477993793432081088566327678914021235302019/668565782221559878105525730304000000000000000000000), (1397296941100994675241359590140395276433246727873/445710521481039918737017153536000000000000000000000), (27984863579744207218379429793229996116250987557257/8022789386658718537266308763648000000000000000000000), (5524067130797530218471925545587786565597062849473/1782842085924159674948068614144000000000000000000000), (21029338674086634179410718911835735201058690751619/10697052515544958049688411684864000000000000000000000)]
    reserve := (491475073/250000000000) }

theorem tilt_015_020_valid : tilt_015_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_015_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_015_020]
  · intro i; fin_cases i <;> norm_num [tilt_015_020]
  · norm_num [tilt_015_020]
  · norm_num [tilt_015_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_015_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_015_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_015_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_015_020]

def tiltBundle015_row : Alternative → Row
  | .zero => tilt_015_000
  | (.spike 0 false false) => tilt_015_001
  | (.spike 0 false true) => tilt_015_002
  | (.spike 0 true false) => tilt_015_003
  | (.spike 0 true true) => tilt_015_004
  | (.spike 1 false false) => tilt_015_005
  | (.spike 1 false true) => tilt_015_006
  | (.spike 1 true false) => tilt_015_007
  | (.spike 1 true true) => tilt_015_008
  | (.spike 2 false false) => tilt_015_009
  | (.spike 2 false true) => tilt_015_010
  | (.spike 2 true false) => tilt_015_011
  | (.spike 2 true true) => tilt_015_012
  | (.spike 3 false false) => tilt_015_013
  | (.spike 3 false true) => tilt_015_014
  | (.spike 3 true false) => tilt_015_015
  | (.spike 3 true true) => tilt_015_016
  | (.spike 4 false false) => tilt_015_017
  | (.spike 4 false true) => tilt_015_018
  | (.spike 4 true false) => tilt_015_019
  | (.spike 4 true true) => tilt_015_020

def tiltBundle015 : TiltBundle where
  interval := ⟨(-1/80), (-1/160)⟩
  lambda := ![(3016951/20000000), (3016951/20000000), (1036013/12500000), (13809513/100000000), (13809513/100000000), (3987333/25000000), (4493507/25000000)]
  row := tiltBundle015_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_015_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_015_001_valid | exact tilt_015_002_valid | exact tilt_015_003_valid | exact tilt_015_004_valid | exact tilt_015_005_valid | exact tilt_015_006_valid | exact tilt_015_007_valid | exact tilt_015_008_valid | exact tilt_015_009_valid | exact tilt_015_010_valid | exact tilt_015_011_valid | exact tilt_015_012_valid | exact tilt_015_013_valid | exact tilt_015_014_valid | exact tilt_015_015_valid | exact tilt_015_016_valid | exact tilt_015_017_valid | exact tilt_015_018_valid | exact tilt_015_019_valid | exact tilt_015_020_valid
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
