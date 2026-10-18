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

def tilt_041_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (334927/50000000)]
    alternative := .zero
    polynomial := [(-16044128306414382742946053828838511669874005593/571927481210057245115982526331100000000000000000), (68651998460801/104490550000000), (-1104969776059775965138023776099066232102874005593/285963740605028622557991263165550000000000000000), (68651998460801/104490550000000), (-2193895423813137547533101498369293952535874005593/571927481210057245115982526331100000000000000000)]
    bernstein := [(15301809735453462368928562927300396616064797891817167/357105939487255255487052504245760000000000000000000000000), (32665599984150761811183392867082667404172063842094931/563128596883748672114198179772160000000000000000000000000), (759297135096949028300503937977462155666949219350536341/10981007639233099106226864505557120000000000000000000000000), (10736645373062912407203515255877695757215953148471731/140782149220937168028549544943040000000000000000000000000), (72619587482577674568255317980075435571720509068707047/915083969936091592185572042129760000000000000000000000000)]
    reserve := (5356187/125000000000) }

theorem tilt_041_000_valid : tilt_041_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_000]
  · intro i; fin_cases i <;> norm_num [tilt_041_000]
  · norm_num [tilt_041_000]
  · norm_num [tilt_041_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_000]

def tilt_041_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14947/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (168409/25000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-8018580250853955390790642720904617933511596523/287578293727004781915872716373700000000000000000), (23000426423647369481547/35194298069900000000000), (-552766066182004924905389309934582693429239596523/143789146863502390957936358186850000000000000000), (23000426423647369481547/35194298069900000000000), (-1097513552113155894419987977148260768924967596523/287578293727004781915872716373700000000000000000)]
    bernstein := [(10394285528125783992743897414563968814446511722653837/179561080961251766269422964369920000000000000000000000000), (20637030041820238527915580377423679586391474198889241/283154012285050862194090059198720000000000000000000000000), (463143158785622479012362562169115348914365434089694751/5521503239558491812784756154375040000000000000000000000000), (6433005525061126906091579078336066096105195785034041/70788503071262715548522514799680000000000000000000000000), (43191834270190281930001409031365219499779711559042517/460125269963207651065396346197920000000000000000000000000)]
    reserve := (11577437/200000000000) }

theorem tilt_041_001_valid : tilt_041_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_001]
  · intro i; fin_cases i <;> norm_num [tilt_041_001]
  · norm_num [tilt_041_001]
  · norm_num [tilt_041_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_001]

def tilt_041_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1107/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1943/50000000), (2089811/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (666073/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-12462414497216396076281772879059378645031292430441/441993040604136071839526704179714540000000000000000), (22986423679313253972953/34799167055075000000000), (-858333804604379566917975542661956711065679334830441/220996520302068035919763352089857270000000000000000), (22986423679313253972953/34799167055075000000000), (-1704205194711542737759669312444854043486327377230441/441993040604136071839526704179714540000000000000000)]
    bernstein := [(15553385364708155273204245240511146944458877116329231679/275976142425997157051021551878065664000000000000000000000000), (31197182000440453253654995913174885805421421611459986947/435193147671764747657380139500026624000000000000000000000000), (704143420421056438799199073093880637423139527050165014117/8486266379599412579318912720250519168000000000000000000000000), (9815915792988312949407698436841262943334349823759528547/108798286917941186914345034875006656000000000000000000000000), (66068126900141546074751107838427433701808981861100417239/707188864966617714943242726687543264000000000000000000000000)]
    reserve := (56357717/1000000000000) }

theorem tilt_041_002_valid : tilt_041_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_002]
  · intro i; fin_cases i <;> norm_num [tilt_041_002]
  · norm_num [tilt_041_002]
  · norm_num [tilt_041_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_002]

def tilt_041_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2680093/50000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (168409/25000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-307722097374396012420047885788566305174353871/11055174147159165581499268037100000000000000000), (23000426423647369481547/35194298069900000000000), (-21249074259762912271745363212728258399398353871/5527587073579582790749634018550000000000000000), (23000426423647369481547/35194298069900000000000), (-42190426422151428531070678539667950493622353871/11055174147159165581499268037100000000000000000)]
    bernstein := [(735442965638646131953381688227560860717232251435849/6902742882128649728936128335360000000000000000000000000), (1323073122166477907472262509882410384183198439958757/10885094544895178418706971605760000000000000000000000000), (28136321604882567448893199703899001386737054064375027/212259343625455979164785946312320000000000000000000000000), (379789179646270007936382019863470259805028721268357/2721273636223794604676742901440000000000000000000000000), (2521757926093160782874215210735860123918196084820209/17688278635454664930398828859360000000000000000000000000)]
    reserve := (106543583/1000000000000) }

theorem tilt_041_003_valid : tilt_041_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_003]
  · intro i; fin_cases i <;> norm_num [tilt_041_003]
  · norm_num [tilt_041_003]
  · norm_num [tilt_041_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_003]

def tilt_041_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5365549/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (666073/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-653118306754792391447058980673309557295042167/23223821978102499578691830936700000000000000000), (22986423679313253972953/34799167055075000000000), (-45098086384460361818152853147584101061347042167/11611910989051249789345915468350000000000000000), (22986423679313253972953/34799167055075000000000), (-89543054462165931244858647314494892565399042167/23223821978102499578691830936700000000000000000)]
    bernstein := [(1892847802157939111562057376673322346065543398978273/14500727869254243639378313950720000000000000000000000000), (3335723640453039822130199630002486447048763343768989/22866532409208614969788879691520000000000000000000000000), (10012432745812983506503975233826451951107108019148397/63699625997081141701554736283520000000000000000000000000), (940067422438261696444516225685212128636851458768189/5716633102302153742447219922880000000000000000000000000), (6230013946523497819891331313048249753776481298129993/37158115164963999325906929498720000000000000000000000000)]
    reserve := (5221387/40000000000) }

theorem tilt_041_004_valid : tilt_041_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_004]
  · intro i; fin_cases i <;> norm_num [tilt_041_004]
  · norm_num [tilt_041_004]
  · norm_num [tilt_041_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_004]

def tilt_041_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (4492301/100000000), (1/100000000), (5424211/100000000), (168409/25000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-5129289484587202036251944915769123951399736763/183964806779392921841011455311452000000000000000), (23000426423647369481547/35194298069900000000000), (-353606097988141209918287994502655973990386616763/91982403389696460920505727655726000000000000000), (23000426423647369481547/35194298069900000000000), (-702082906491695217800324044089542824029373496763/183964806779392921841011455311452000000000000000)]
    bernstein := [(6790661315913847335364975328241867515049483172270397/114865830574450214612924225755443200000000000000000000000), (13424603206066925468746307748670184904553380209741321/181134578982786876889611279075891200000000000000000000000), (300624138043654613445330959070192450668518326480595631/3532124290164344099347419941979878400000000000000000000000), (4170994903038735679200377653512428167835227531310121/45283644745696719222402819768972800000000000000000000000), (27992605794403946955571478023710567805312921472297477/294343690847028674945618328498323200000000000000000000000)]
    reserve := (59118201/1000000000000) }

theorem tilt_041_005_valid : tilt_041_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_005]
  · intro i; fin_cases i <;> norm_num [tilt_041_005]
  · norm_num [tilt_041_005]
  · norm_num [tilt_041_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_005]

def tilt_041_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (1124117/25000000), (1/100000000), (5424211/100000000), (666073/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-128020929811665541995618968764256244227093665249/4551703430437023490000447556868700000000000000000), (22986423679313253972953/34799167055075000000000), (-8838917605462353252956809214417662604073065665249/2275851715218511745000223778434350000000000000000), (22986423679313253972953/34799167055075000000000), (-17549814281113040963917999460071068963919037665249/4551703430437023490000447556868700000000000000000)]
    bernstein := [(361870008748488138699018857536214630505062455683383431/2842039215102141496195401401361920000000000000000000000000), (639401979283408947567515249508389979381804407135690283/4481677223814915436308132979070720000000000000000000000000), (13456166607569471559946909707716695554897066518004828413/87392705864390851008008593091879040000000000000000000000000), (180650999246019236154757216848175093588213017740492683/1120419305953728859077033244767680000000000000000000000000), (1197662547672529094257785838687223276715701061003858271/7282725488699237584000716090989920000000000000000000000000)]
    reserve := (127327591/1000000000000) }

theorem tilt_041_006_valid : tilt_041_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_006]
  · intro i; fin_cases i <;> norm_num [tilt_041_006]
  · norm_num [tilt_041_006]
  · norm_num [tilt_041_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_006]

def tilt_041_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2088691/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (168409/25000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-8014205367035715479807907032575239997752804223/287424170847483980582285240069700000000000000000), (2090437113896801963937/3197766932900000000000), (-552520883919654610236890814744018377741559804223/143712085423741990291142620034850000000000000000), (2090437113896801963937/3197766932900000000000), (-1097027562472273504993973722455461515485366804223/287424170847483980582285240069700000000000000000)]
    bernstein := [(526564745282047541544349920136518515995648916538015617/7358058773695589902906502145784320000000000000000000000000), (24520166829496636602664062403567555320220869157585141/283002260526753457804096236376320000000000000000000000000), (539296191516312203020853517997406551254903827186039651/5518544080271692427179876609338240000000000000000000000000), (7414991213136610638769980963283301984569292865249941/70750565131688364451024059094080000000000000000000000000), (49612395030773287151293219537961624836712575308730817/459878673355974368931656384111520000000000000000000000000)]
    reserve := (71562997/1000000000000) }

theorem tilt_041_007_valid : tilt_041_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_007]
  · intro i; fin_cases i <;> norm_num [tilt_041_007]
  · norm_num [tilt_041_007]
  · norm_num [tilt_041_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_007]

def tilt_041_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2090931/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (666073/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-2133764855424170226114934501825506219017007463/75867201842482018899115723790460000000000000000), (7664036554372543951571/11605939033025000000000), (-147312375211096988809665105679012151407522407463/37933600921241009449557861895230000000000000000), (7664036554372543951571/11605939033025000000000), (-292490985566769807393215276856198796596027807463/75867201842482018899115723790460000000000000000)]
    bernstein := [(223145299223613818400701417105807892576506757359431577/1942200367167539683817362529035776000000000000000000000000), (9722321907774051200592161532421382958778413304538221/74700014121828449377590866501376000000000000000000000000), (205928184323340554008789624000986116643424429927151531/1456650275375654762863021896776832000000000000000000000000), (2774156590716501002406206216971538162483351848427021/18675003530457112344397716625344000000000000000000000000), (18412472115327620288858798956438126336458159988322777/121387522947971230238585158064736000000000000000000000000)]
    reserve := (114893037/1000000000000) }

theorem tilt_041_008_valid : tilt_041_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_008]
  · intro i; fin_cases i <;> norm_num [tilt_041_008]
  · norm_num [tilt_041_008]
  · norm_num [tilt_041_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_008]

def tilt_041_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (2246151/50000000), (1/100000000), (5424211/100000000), (168409/25000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-64116284537681608111801304042156217302434742819/2299560596631549125860609748541300000000000000000), (23000426423647369481547/35194298069900000000000), (-4420077360482205018042720641457633748204306742819/1149780298315774562930304874270650000000000000000), (23000426423647369481547/35194298069900000000000), (-8776038436426728427973639978873111279106178742819/2299560596631549125860609748541300000000000000000)]
    bernstein := [(84787266582341777763549936954630314659144333960298261/1435823201799211161512966086894080000000000000000000000000), (167656132210857942610898625531043409281784655042585473/2264182741298756062385831137025280000000000000000000000000), (3754848769220126557359946508554171025385277061730704503/44151563455325743216523707171992960000000000000000000000000), (52099570841832788080760807031311850109849078663219873/566045685324689015596457784256320000000000000000000000000), (349661397528512756201025332690065889611525472245734301/3679296954610478601376975597666080000000000000000000000000)]
    reserve := (59051327/1000000000000) }

theorem tilt_041_009_valid : tilt_041_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_009]
  · intro i; fin_cases i <;> norm_num [tilt_041_009]
  · norm_num [tilt_041_009]
  · norm_num [tilt_041_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_009]

def tilt_041_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (4496469/100000000), (1/100000000), (5424211/100000000), (666073/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-102242181492471458542485652893199101873108600677/3641363554176964243945927768299180000000000000000), (22986423679313253972953/34799167055075000000000), (-7070961071833311801855139432292127583774949400677/1820681777088482121972963884149590000000000000000), (22986423679313253972953/34799167055075000000000), (-14039679962174152145167793211691056065676790200677/3641363554176964243945927768299180000000000000000)]
    bernstein := [(399994264124702073556279970059755197328141237947852963/2273631877730006942561359777279488000000000000000000000000), (685804542804163348599384149054568767663524625195603159/3585342576420395563269836571863808000000000000000000000000), (14164154358345336040273196850649385513404561668948561649/69914180240197713483761813151344256000000000000000000000000), (188109664835211050165968034200506255829132493356178359/896335644105098890817459142965952000000000000000000000000), (1241517455470334350702090936477968460823708029517016283/5826181686683142790313484429278688000000000000000000000000)]
    reserve := (43981863/250000000000) }

theorem tilt_041_010_valid : tilt_041_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_010]
  · intro i; fin_cases i <;> norm_num [tilt_041_010]
  · norm_num [tilt_041_010]
  · norm_num [tilt_041_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_010]

def tilt_041_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7373/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (168409/25000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-8019206540377571669746014309202985792660995523/287578293727004781915872716373700000000000000000), (23000426423647369481547/35194298069900000000000), (-552766692471528541184344681522881061288388995523/143789146863502390957936358186850000000000000000), (23000426423647369481547/35194298069900000000000), (-1097514178402679510698943348736559136784116995523/287578293727004781915872716373700000000000000000)]
    bernstein := [(9997895188914450366182053883885948948815114699934837/179561080961251766269422964369920000000000000000000000000), (20011824917846546880218012456932030538970306637222241/283154012285050862194090059198720000000000000000000000000), (450949136318294100704180050175013469526790421401657751/5521503239558491812784756154375040000000000000000000000000), (6276639235371725005315689266190680325062161065767041/70788503071262715548522514799680000000000000000000000000), (42175238910290925276724045042092111975243189725163517/460125269963207651065396346197920000000000000000000000000)]
    reserve := (55679633/1000000000000) }

theorem tilt_041_011_valid : tilt_041_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_011]
  · intro i; fin_cases i <;> norm_num [tilt_041_011]
  · norm_num [tilt_041_011]
  · norm_num [tilt_041_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_011]

def tilt_041_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (273/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1917/50000000), (5424211/100000000), (666073/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-6830481425796991275529412659744669767457485975923/242265871458262952397887771462375700000000000000000), (22986423679313253972953/34799167055075000000000), (-470470744145369187336468097589639502000082377975923/121132935729131476198943885731187850000000000000000), (22986423679313253972953/34799167055075000000000), (-934111006864941383397406782519534334232707269975923/242265871458262952397887771462375700000000000000000)]
    bernstein := [(8800732427330068180594574017086303765363391246313082437/151268446569061745887461632913093120000000000000000000000000), (17534515270568914712190182467685212739235456837401469041/238538704205058906976381805747569920000000000000000000000000), (394433944927372182508044025164653592670045012591340252551/4651504731998648686039445212077613440000000000000000000000000), (5489026877104900492860837100701195676247692577017053841/59634676051264726744095451436892480000000000000000000000000), (36920140372768038417985879819150613182808390537001175117/387625394333220723836620434339801120000000000000000000000000)]
    reserve := (11635913/200000000000) }

theorem tilt_041_012_valid : tilt_041_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_012]
  · intro i; fin_cases i <;> norm_num [tilt_041_012]
  · norm_num [tilt_041_012]
  · norm_num [tilt_041_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_012]

def tilt_041_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (84711/1562500), (168409/25000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-41667626586211269813045902123300530162957877/1497056121151893616778273907900000000000000000), (23000426423647369481547/35194298069900000000000), (-2877478173085584160392656939767785196738957877/748528060575946808389136953950000000000000000), (23000426423647369481547/35194298069900000000000), (-5713288719584957050972267977412269863314957877/1497056121151893616778273907900000000000000000)]
    bernstein := [(101559679845052414138304957689626799351596518599763/934747236621670160720092976640000000000000000000000000), (2369521609966687893905869769498789836118876465402267/19162318350744238294761906021120000000000000000000000000), (3870682134331218618228740560921378003994766292338049/28743477526116357442142859031680000000000000000000000000), (678681881164235038982185743766391528434042868239867/4790579587686059573690476505280000000000000000000000000), (346536463462712930513713951975071711324808286915083/2395289793843029786845238252640000000000000000000000000)]
    reserve := (2172987/20000000000) }

theorem tilt_041_013_valid : tilt_041_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_013]
  · intro i; fin_cases i <;> norm_num [tilt_041_013]
  · norm_num [tilt_041_013]
  · norm_num [tilt_041_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_013]

def tilt_041_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (135673/2500000), (666073/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-800185367482237385900463421398539772486834029/28449162639737483743739122202700000000000000000), (22986423679313253972953/34799167055075000000000), (-55245234358677435973265281118688840795498834029/14224581319868741871869561101350000000000000000), (22986423679313253972953/34799167055075000000000), (-109690283349872634560630098815979141818510834029/28449162639737483743739122202700000000000000000)]
    bernstein := [(2245328538445216149924864186291280558564084555404251/17763379599445843508285890936320000000000000000000000000), (51616181511643296637926494125849665463771791427977059/364149281788639791919860764194560000000000000000000000000), (83598313259414802571121617413021921482667336720397273/546223922682959687879791146291840000000000000000000000000), (14594111682570036318491435060238921993355195628472259/91037320447159947979965191048640000000000000000000000000), (7443496255845743919163183960139133547245788280583891/45518660223579973989982595524320000000000000000000000000)]
    reserve := (126402103/1000000000000) }

theorem tilt_041_014_valid : tilt_041_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_014]
  · intro i; fin_cases i <;> norm_num [tilt_041_014]
  · norm_num [tilt_041_014]
  · norm_num [tilt_041_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_014]

def tilt_041_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7373/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (168409/25000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-8019206540377571669746014309202985792660995523/287578293727004781915872716373700000000000000000), (23000426423647369481547/35194298069900000000000), (-552766692471528541184344681522881061288388995523/143789146863502390957936358186850000000000000000), (23000426423647369481547/35194298069900000000000), (-1097514178402679510698943348736559136784116995523/287578293727004781915872716373700000000000000000)]
    bernstein := [(9997895188914450366182053883885948948815114699934837/179561080961251766269422964369920000000000000000000000000), (20011824917846546880218012456932030538970306637222241/283154012285050862194090059198720000000000000000000000000), (450949136318294100704180050175013469526790421401657751/5521503239558491812784756154375040000000000000000000000000), (6276639235371725005315689266190680325062161065767041/70788503071262715548522514799680000000000000000000000000), (42175238910290925276724045042092111975243189725163517/460125269963207651065396346197920000000000000000000000000)]
    reserve := (55679633/1000000000000) }

theorem tilt_041_015_valid : tilt_041_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_015]
  · intro i; fin_cases i <;> norm_num [tilt_041_015]
  · norm_num [tilt_041_015]
  · norm_num [tilt_041_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_015]

def tilt_041_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (273/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1917/50000000), (5424211/100000000), (666073/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-6830481425796991275529412659744669767457485975923/242265871458262952397887771462375700000000000000000), (22986423679313253972953/34799167055075000000000), (-470470744145369187336468097589639502000082377975923/121132935729131476198943885731187850000000000000000), (22986423679313253972953/34799167055075000000000), (-934111006864941383397406782519534334232707269975923/242265871458262952397887771462375700000000000000000)]
    bernstein := [(8800732427330068180594574017086303765363391246313082437/151268446569061745887461632913093120000000000000000000000000), (17534515270568914712190182467685212739235456837401469041/238538704205058906976381805747569920000000000000000000000000), (394433944927372182508044025164653592670045012591340252551/4651504731998648686039445212077613440000000000000000000000000), (5489026877104900492860837100701195676247692577017053841/59634676051264726744095451436892480000000000000000000000000), (36920140372768038417985879819150613182808390537001175117/387625394333220723836620434339801120000000000000000000000000)]
    reserve := (11635913/200000000000) }

theorem tilt_041_016_valid : tilt_041_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_016]
  · intro i; fin_cases i <;> norm_num [tilt_041_016]
  · norm_num [tilt_041_016]
  · norm_num [tilt_041_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_016]

def tilt_041_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (84711/1562500), (168409/25000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1333364622858712577130522437452690961816305189/47905795876860595736904765052800000000000000000), (23000426423647369481547/35194298069900000000000), (-92079302110838645075678075642076200292248305189/23952897938430297868452382526400000000000000000), (23000426423647369481547/35194298069900000000000), (-182825239598818577574225628846699709622680305189/47905795876860595736904765052800000000000000000)]
    bernstein := [(3249547662294693253924859551308963480734310300664291/29911911571893445143042975252480000000000000000000000000), (75817267096997189519411112854837482526073790800869419/613194187223815625432380992675840000000000000000000000000), (123850689361407023767018126076671685105481895110358193/919791280835723438148571489013760000000000000000000000000), (21715963319781499648842824488974836099433025989172619/153298546805953906358095248168960000000000000000000000000), (11088238196150455784538591377701549071048478260629531/76649273402976953179047624084480000000000000000000000000)]
    reserve := (27159311/250000000000) }

theorem tilt_041_017_valid : tilt_041_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_017]
  · intro i; fin_cases i <;> norm_num [tilt_041_017]
  · norm_num [tilt_041_017]
  · norm_num [tilt_041_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_017]

def tilt_041_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (135673/2500000), (666073/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-3199771674420033135533775680227389970655047991/113796650558949934974956488810800000000000000000), (22986423679313253972953/34799167055075000000000), (-220979967639200827484993046469388594062703047991/56898325279474967487478244405400000000000000000), (22986423679313253972953/34799167055075000000000), (-438760163603981621834452317258549798154751047991/113796650558949934974956488810800000000000000000)]
    bernstein := [(9595115848123961333405146107011554448262991768580129/71053518397783374033143563745280000000000000000000000000), (219050238466520810874450705615058225508075207553826361/1456597127154559167679443056778240000000000000000000000000), (353275427780352697255069721833214140382378749339553467/2184895690731838751519164585167360000000000000000000000000), (61524133474174947751720660758058979694241168870307161/364149281788639791919860764194560000000000000000000000000), (31348160508106076147429761854553065018294265768823689/182074640894319895959930382097280000000000000000000000000)]
    reserve := (27008137/200000000000) }

theorem tilt_041_018_valid : tilt_041_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_018]
  · intro i; fin_cases i <;> norm_num [tilt_041_018]
  · norm_num [tilt_041_018]
  · norm_num [tilt_041_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_018]

def tilt_041_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (334927/50000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-7978977029245088941386933902333226251091564859/285963740605028622557991263165550000000000000000), (68651998460801/104490550000000), (-552485390051499068633839902833159180291794784359/142981870302514311278995631582775000000000000000), (68651998460801/104490550000000), (-1096991803073753048326292871763985134332498003859/285963740605028622557991263165550000000000000000)]
    bernstein := [(34548542435963623776233807801526666410794575388810021/178552969743627627743526252122880000000000000000000000000), (58748142496665033235030358323397329765078109567731153/281564298441874336057099089886080000000000000000000000000), (1206744513911861266602607057833451813120015170816594983/5490503819616549553113432252778560000000000000000000000000), (15972074695553169735281515669602360592904258225869553/70391074610468584014274772471520000000000000000000000000), (105233902802630017807548554710301544401778845439612461/457541984968045796092786021064880000000000000000000000000)]
    reserve := (96745919/500000000000) }

theorem tilt_041_019_valid : tilt_041_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_019]
  · intro i; fin_cases i <;> norm_num [tilt_041_019]
  · norm_num [tilt_041_019]
  · norm_num [tilt_041_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_019]

def tilt_041_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(33/400), (17/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5362867/100000000), (1/100000000), (2089811/50000000), (280899/6250000), (1/100000000), (5424211/100000000), (334927/50000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-8020541987625713123938618083530407368089064859/285963740605028622557991263165550000000000000000), (68651998460801/104490550000000), (-552440780156927756918615793612151637661708284359/142981870302514311278995631582775000000000000000), (68651998460801/104490550000000), (-1096861018326229800713292969140772867955327503859/285963740605028622557991263165550000000000000000)]
    bernstein := [(8978733213885554276981100489519212136424427499310021/178552969743627627743526252122880000000000000000000000000), (18435760271649933978741538107827505882557995444231153/281564298441874336057099089886080000000000000000000000000), (420835131929398424790460701309765710962379781608094983/5490503819616549553113432252778560000000000000000000000000), (5898671924707229288548369322719502852150813302369553/70391074610468584014274772471520000000000000000000000000), (39772273429017941744720634851499454513466382770112461/457541984968045796092786021064880000000000000000000000000)]
    reserve := (6285763/125000000000) }

theorem tilt_041_020_valid : tilt_041_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_041_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_041_020]
  · intro i; fin_cases i <;> norm_num [tilt_041_020]
  · norm_num [tilt_041_020]
  · norm_num [tilt_041_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_041_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_041_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_041_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_041_020]

def tiltBundle041_row : Alternative → Row
  | .zero => tilt_041_000
  | (.spike 0 false false) => tilt_041_001
  | (.spike 0 false true) => tilt_041_002
  | (.spike 0 true false) => tilt_041_003
  | (.spike 0 true true) => tilt_041_004
  | (.spike 1 false false) => tilt_041_005
  | (.spike 1 false true) => tilt_041_006
  | (.spike 1 true false) => tilt_041_007
  | (.spike 1 true true) => tilt_041_008
  | (.spike 2 false false) => tilt_041_009
  | (.spike 2 false true) => tilt_041_010
  | (.spike 2 true false) => tilt_041_011
  | (.spike 2 true true) => tilt_041_012
  | (.spike 3 false false) => tilt_041_013
  | (.spike 3 false true) => tilt_041_014
  | (.spike 3 true false) => tilt_041_015
  | (.spike 3 true true) => tilt_041_016
  | (.spike 4 false false) => tilt_041_017
  | (.spike 4 false true) => tilt_041_018
  | (.spike 4 true false) => tilt_041_019
  | (.spike 4 true true) => tilt_041_020

def tiltBundle041 : TiltBundle where
  interval := ⟨(33/400), (17/200)⟩
  lambda := ![(7473627/50000000), (7473627/50000000), (4972671/50000000), (230413/1562500), (230413/1562500), (15599843/100000000), (3766861/25000000)]
  row := tiltBundle041_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_041_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_041_001_valid | exact tilt_041_002_valid | exact tilt_041_003_valid | exact tilt_041_004_valid | exact tilt_041_005_valid | exact tilt_041_006_valid | exact tilt_041_007_valid | exact tilt_041_008_valid | exact tilt_041_009_valid | exact tilt_041_010_valid | exact tilt_041_011_valid | exact tilt_041_012_valid | exact tilt_041_013_valid | exact tilt_041_014_valid | exact tilt_041_015_valid | exact tilt_041_016_valid | exact tilt_041_017_valid | exact tilt_041_018_valid | exact tilt_041_019_valid | exact tilt_041_020_valid
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
