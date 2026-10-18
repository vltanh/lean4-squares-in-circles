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

def tilt_025_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (5577341/100000000), (134037/100000000)]
    alternative := .zero
    polynomial := [(-62242982077099523256920862907598977656299489/13969548128745686917308759840180000000000000000), (2667792523/4239369000), (-16104903499883273419409787262137495279828477721/776086007152538162072708880010000000000000000), (2667792523/4239369000), (-289826020015821822026119249855567316059256299489/13969548128745686917308759840180000000000000000)]
    bernstein := [(96595259363380420622557910423829416445673040801311/572192691353423336132966803053772800000000000000000000), (116842206866110204166825081356364586789702518035231/457754153082738668906373442443018240000000000000000000), (37586823833211760281603850222454710055580880533941/122067774155396978375032917984804864000000000000000000), (95743955145597071834948631036030466135209628056607/292962657972952748100079003163531673600000000000000000), (73107403612232203959502069470053607653836450643999/234370126378362198480063202530825338880000000000000000)]
    reserve := (168815961/1000000000000) }

theorem tilt_025_000_valid : tilt_025_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_000]
  · intro i; fin_cases i <;> norm_num [tilt_025_000]
  · norm_num [tilt_025_000]
  · norm_num [tilt_025_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_000]

def tilt_025_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14553/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (61/5000000), 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (5577341/100000000), (138191/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-2781663173539066338383912128747905734027050781/648111806036223467665955425728300000000000000000), (178521440868802322407/292921320739500000000), (-6525880882459670616055009381600623385409042050781/324055903018111733832977712864150000000000000000), (178521440868802322407/292921320739500000000), (-13048980101745802165771634851072498865084057050781/648111806036223467665955425728300000000000000000)]
    bernstein := [(4786736484493741869033363110515269208185401703192419/26546659575243713235597534237831168000000000000000000000), (621134558105833835769227526031191828150833814016011/2359703073354996732053114154473881600000000000000000000), (15972183442530712424817302234557739724633962083516201/50969586384467929412347265736635842560000000000000000000), (499478830782892052336226228148287574928094178688267/1510209966947197908513993058863284224000000000000000000), (1142893184232636333858679835186962367734295022381857/3624503920673274980433583341271882137600000000000000000)]
    reserve := (180314079/1000000000000) }

theorem tilt_025_001_valid : tilt_025_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_001]
  · intro i; fin_cases i <;> norm_num [tilt_025_001]
  · norm_num [tilt_025_001]
  · norm_num [tilt_025_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_001]

def tilt_025_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4311/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (473/12500000), (4239369/100000000), (1070457/25000000), (1/100000000), (5577341/100000000), (129961/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-120679476335267377829891283293185214581920554179/26209073761994387749545303403059900000000000000000), (358330165597749596917/550952634609000000000), (-280343180460714637814542428510986495825551125554179/13104536880997193874772651701529950000000000000000), (358330165597749596917/550952634609000000000), (-560565681445094008251254965738679806436520330554179/26209073761994387749545303403059900000000000000000)]
    bernstein := [(1165069743985153614696161454209110976635833546769909/6352211013557929717286246315913216000000000000000000000), (26127387041742513139586770232629294722724935016425749/95424325448114677530788944656829644800000000000000000000), (678907988074054670579287893195496238142607550632155959/2061165429679277034665041204587520327680000000000000000000), (21383837778813573056886274430746921873802190331794453/61071568286793393619704924580370972672000000000000000000), (49260826832436906052447593529103126638488265476275263/146571763888304144687291818992890334412800000000000000000)]
    reserve := (183411687/1000000000000) }

theorem tilt_025_002_valid : tilt_025_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_002]
  · intro i; fin_cases i <;> norm_num [tilt_025_002]
  · norm_num [tilt_025_002]
  · norm_num [tilt_025_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_002]

def tilt_025_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (61/5000000), 0, 0]] i.1) i.2
    mu := ![(2778103/50000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (5577341/100000000), (138191/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-1371270584817075204879589989815713095672872743/323895185610094998688279408602300000000000000000), (178521440868802322407/292921320739500000000), (-3261303295747866355558500646042217156622387872743/161947592805047499344139704301150000000000000000), (178521440868802322407/292921320739500000000), (-6521235320910915635912121702094618600149102872743/323895185610094998688279408602300000000000000000)]
    bernstein := [(3165387608064618199291690021064295553545362572736857/13266746802589491146271924576350208000000000000000000000), (379145390904942737149340281853602231036709484500433/1179266382452399213001948851231129600000000000000000000), (9466808000556072355465501486455622938795685042997003/25472153860971823000842095186592399360000000000000000000), (293607990535242646905463352396967199714086141627601/754730484769535496321247264787922944000000000000000000), (676750177874446358374416343157465167484630831264371/1811353163446885191170993435491015065600000000000000000)]
    reserve := (119297807/500000000000) }

theorem tilt_025_003_valid : tilt_025_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_003]
  · intro i; fin_cases i <;> norm_num [tilt_025_003]
  · norm_num [tilt_025_003]
  · norm_num [tilt_025_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_003]

def tilt_025_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2780861/50000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (5577341/100000000), (129961/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-1385730947362268585718963238052298483847963939/304907927138332359418718178137100000000000000000), (358330165597749596917/550952634609000000000), (-3261404100484915595892163603778903915320792963939/152453963569166179709359089068550000000000000000), (358330165597749596917/550952634609000000000), (-6521422470022468923198608244319755532157737963939/304907927138332359418718178137100000000000000000)]
    bernstein := [(17970194773960468597612852752343092741380315870869/73899578080391085454382819979264000000000000000000000), (370300564109120577374686305154060707800604418256309/1110135884052097194825839695688499200000000000000000000), (9331265421950127305503123146800318234549439087568919/23978935095525299408238137426871582720000000000000000000), (291235906764411250871157873684400459218824311150773/710486965793342204688537405240639488000000000000000000), (675001309127079459604631351556329145623274178877983/1705168717904021291252489772577534771200000000000000000)]
    reserve := (48634093/200000000000) }

theorem tilt_025_004_valid : tilt_025_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_004]
  · intro i; fin_cases i <;> norm_num [tilt_025_004]
  · norm_num [tilt_025_004]
  · norm_num [tilt_025_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_004]

def tilt_025_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (61/5000000), 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (4279939/100000000), (1/100000000), (5577341/100000000), (138191/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-1337633962903384094074087428139363947441490681/310956422725792991065919875212492000000000000000), (178521440868802322407/292921320739500000000), (-3131043927573082951747436077141242003504730090681/155478211362896495532959937606246000000000000000), (178521440868802322407/292921320739500000000), (-6260750221183262519400798066854344643062018690681/310956422725792991065919875212492000000000000000)]
    bernstein := [(2172690070257725925164697037215114643167404286832519/12736775074848480914060078088703672320000000000000000000), (286996643700264546751316595095160426959193397072911/1132157784430976081249784718995881984000000000000000000), (7425301199713623719113623883426491094813216522974101/24454608143709083354995349930311050854400000000000000000), (232592945408361832419600657863990733538963669687567/724580982035824691999862220157364469760000000000000000), (177141062092526678530204100974533732164476837480719/579664785628659753599889776125891575808000000000000000)]
    reserve := (85292001/500000000000) }

theorem tilt_025_005_valid : tilt_025_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_005]
  · intro i; fin_cases i <;> norm_num [tilt_025_005]
  · norm_num [tilt_025_005]
  · norm_num [tilt_025_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_005]

def tilt_025_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (4283717/100000000), (1/100000000), (5577341/100000000), (129961/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-293669600902437567568168584550460447953179377/64755636138330393502061067552300000000000000000), (358330165597749596917/550952634609000000000), (-692648785859561723549467243189610514799738179377/32377818069165196751030533776150000000000000000), (358330165597749596917/550952634609000000000), (-1385003902118221009531366317794670569151523179377/64755636138330393502061067552300000000000000000)]
    bernstein := [(3968895103074565820772003892000996870219908277367/15694620451041496555292433887232000000000000000000000), (80933453147837359064319217227790247421181691651287/235768076108978926030615229061529600000000000000000000), (2031215959889308775865755428385687147308645604793517/5092590443953944802261288947729039360000000000000000000), (63317656835295437846469005817414562379042738593239/150891568709746512659593746599378944000000000000000000), (48957648469979929435361002083414601245173801854423/120713254967797210127674997279503155200000000000000000)]
    reserve := (50576503/200000000000) }

theorem tilt_025_006_valid : tilt_025_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_006]
  · intro i; fin_cases i <;> norm_num [tilt_025_006]
  · norm_num [tilt_025_006]
  · norm_num [tilt_025_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_006]

def tilt_025_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (61/5000000), 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4237459/100000000), (1070457/25000000), (1/100000000), (5577341/100000000), (138191/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-8360064719223007008831424584448491328721832203/1943459419664423733158622294273900000000000000000), (178480512801465379177/292789348334500000000), (-19569131990694462043887152813993812524065171832203/971729709832211866579311147136950000000000000000), (178480512801465379177/292789348334500000000), (-39129903916669701080765474203403176556801621832203/1943459419664423733158622294273900000000000000000)]
    bernstein := [(13712566064360507314085361858225684658791343891089397/79604097829454796110177169173458944000000000000000000000), (5418819132409068117961463268583892034608567881095079/21227759421187945629380578446255718400000000000000000000), (46694161879341030775881353702165437002846084553213663/152839867832553208531540164813041172480000000000000000000), (4387880546553839622457204342764990830236849963575463/13585766029560285202803570205603659776000000000000000000), (10031621123073325031845165832063619385942387143273973/32605838470944684486728568493448783462400000000000000000)]
    reserve := (172259549/1000000000000) }

theorem tilt_025_007_valid : tilt_025_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_007]
  · intro i; fin_cases i <;> norm_num [tilt_025_007]
  · norm_num [tilt_025_007]
  · norm_num [tilt_025_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_007]

def tilt_025_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (6627/156250), (1070457/25000000), (1/100000000), (5577341/100000000), (129961/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-55308731831162063707682347837235153212915897/12195761929101872853246803608320000000000000000), (17920867626051855107/27560049504000000000), (-130448283453584030278840162529370642326838215897/6097880964550936426623401804160000000000000000), (17920867626051855107/27560049504000000000), (-86947086058445632831324214236968016500154505299/4065253976367290951082267869440000000000000000)]
    bernstein := [(742533499519565850386314700515090199799171786287/2955848571692382911650822933708800000000000000000000), (136474634557577388099522869763493772785541736454663/399630726892810169655191260637429760000000000000000000), (380752979733399339844012291264417839518718722876437/959113744542744407172459025529831424000000000000000000), (106820206195742316473793551982235211812580386523911/255763665211398508579322406807955046400000000000000000), (27520176359462157627602416573056324196009786017709/68203644056372935621152641815454679040000000000000000)]
    reserve := (251208233/1000000000000) }

theorem tilt_025_008_valid : tilt_025_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_008]
  · intro i; fin_cases i <;> norm_num [tilt_025_008]
  · norm_num [tilt_025_008]
  · norm_num [tilt_025_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_008]

def tilt_025_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (61/5000000), 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (213997/5000000), (1/100000000), (5577341/100000000), (138191/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-25143962672686906623577315928024074999246163/5845046905642824846628247262600000000000000000), (178521440868802322407/292921320739500000000), (-58854223377341668454658017076031873067329246163/2922523452821412423314123631300000000000000000), (178521440868802322407/292921320739500000000), (-117683302792010650002692456836135722059659246163/5845046905642824846628247262600000000000000000)]
    bernstein := [(40821149561507802054182049874779643387131153387437/239413121255130105717893007876096000000000000000000000), (5392995046803680697296365792174101488467861752453/21281166333789342730479378477875200000000000000000000), (139537074601213225280585335903617811230692047074823/459673192809849802978354575122104320000000000000000000), (4370973593912973325020934517845577577007279537541/13619946453625179347506802225840128000000000000000000), (3328859729349787008398591833559354969937693596037/10895957162900143478005441780672102400000000000000000)]
    reserve := (170505063/1000000000000) }

theorem tilt_025_009_valid : tilt_025_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_009]
  · intro i; fin_cases i <;> norm_num [tilt_025_009]
  · norm_num [tilt_025_009]
  · norm_num [tilt_025_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_009]

def tilt_025_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (2141859/50000000), (1/100000000), (5577341/100000000), (129961/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-2730004023153013960712093607867563160661767871/609782382651473257431968732519550000000000000000), (358330165597749596917/550952634609000000000), (-6522408870759529246578755170601542429084584267871/304891191325736628715984366259775000000000000000), (358330165597749596917/550952634609000000000), (-13042087737495905479196798247595217295008506767871/609782382651473257431968732519550000000000000000)]
    bernstein := [(45952690987682231871746518129028556432387176735641/147791043747954701919606149609472000000000000000000000), (891003005063044266351298973929862256820285170047801/2220149901635941744392305714133401600000000000000000000), (21911202567327160493377671665485056373960213565497091/47955237875336341678873803425281474560000000000000000000), (678731521130768398924880508920610086204193926499897/1420895937047002716411075657045377024000000000000000000), (1581039829247760617977576240385285648196752619068587/3410150248912806519386581576908904857600000000000000000)]
    reserve := (310930147/1000000000000) }

theorem tilt_025_010_valid : tilt_025_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_010]
  · intro i; fin_cases i <;> norm_num [tilt_025_010]
  · norm_num [tilt_025_010]
  · norm_num [tilt_025_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_010]

def tilt_025_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1453/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (61/5000000), 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (5577341/100000000), (138191/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-2781824417261787761128011419555231939748044531/648111806036223467665955425728300000000000000000), (178521440868802322407/292921320739500000000), (-6525881043703393337477753480891430711614763044531/324055903018111733832977712864150000000000000000), (178521440868802322407/292921320739500000000), (-13048980262989524887194378950363306191289778044531/648111806036223467665955425728300000000000000000)]
    bernstein := [(4780129877530177836502508944025563239094063262198669/26546659575243713235597534237831168000000000000000000000), (620547281217493274214774156130763348786207728572261/2359703073354996732053114154473881600000000000000000000), (15959497725026700844713363435809103304349675738134951/50969586384467929412347265736635842560000000000000000000), (499102940545189930685141170113284375434753595644517/1510209966947197908513993058863284224000000000000000000), (1141991003621115775918143524249992181252621695650607/3624503920673274980433583341271882137600000000000000000)]
    reserve := (180065211/1000000000000) }

theorem tilt_025_011_valid : tilt_025_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_011]
  · intro i; fin_cases i <;> norm_num [tilt_025_011]
  · norm_num [tilt_025_011]
  · norm_num [tilt_025_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_011]

def tilt_025_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (269/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1889/50000000), (5577341/100000000), (129961/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-2650618750962599636814057195179818110089717339743/575685352748923237894082303818373850000000000000000), (358330165597749596917/550952634609000000000), (-6157770436884597840973441764440675908158006324839743/287842676374461618947041151909186925000000000000000), (358330165597749596917/550952634609000000000), (-12312890255018233082310069471686171998205922932339743/575685352748923237894082303818373850000000000000000)]
    bernstein := [(25619980479595711625859565678483784249571060871276153/139527053541987549255275805706512384000000000000000000000), (574328079104323557690463501273977510417164038890577433/2096006404319635184368143214613386035200000000000000000000), (14921732168945289553299796087059666765908858686890404003/45273738333304119982351893435649138360320000000000000000000), (469978178066033082474370854024355091885178401197496601/1341444098764566517995611657352567062528000000000000000000), (1082691089575833248255310654871192017742087155522263371/3219465837034959643189467977646160950067200000000000000000)]
    reserve := (45905041/250000000000) }

theorem tilt_025_012_valid : tilt_025_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_012]
  · intro i; fin_cases i <;> norm_num [tilt_025_012]
  · norm_num [tilt_025_012]
  · norm_num [tilt_025_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_012]

def tilt_025_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (61/5000000), 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (2787289/50000000), (138191/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-685559237229239205231257339662751178622577633/161947683289841814671827778920350000000000000000), (178521440868802322407/292921320739500000000), (-1630652482527810030399288003034322117879340077633/80973841644920907335913889460175000000000000000), (178521440868802322407/292921320739500000000), (-3260619405818390821593344748728981484580057577633/161947683289841814671827778920350000000000000000)]
    bernstein := [(1585826578089230782542859937872800934676135101039967/6633377107551920728958065824577536000000000000000000000), (189851202446034000773426930162975537673919329994023/589633520671281842574050295518003200000000000000000000), (4739420362594517632787691201958047573042065874961693/12736084046499687799599486383188869120000000000000000000), (146982269636113240994666527123233579644374544993831/377365453229620379247392189131522048000000000000000000), (338802960502659744993028813167498027152034466947701/905677087751088910193741253915652915200000000000000000)]
    reserve := (47813551/200000000000) }

theorem tilt_025_013_valid : tilt_025_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_013]
  · intro i; fin_cases i <;> norm_num [tilt_025_013]
  · norm_num [tilt_025_013]
  · norm_num [tilt_025_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_013]

def tilt_025_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (2790053/50000000), (129961/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-692972339723711749188100381126689924443476889/152453878292569814606917447353450000000000000000), (358330165597749596917/550952634609000000000), (-1630701245347126209006250045060786356600870976889/76226939146284907303458723676725000000000000000), (358330165597749596917/550952634609000000000), (-3260709518354528706263311989740446023277298476889/152453878292569814606917447353450000000000000000)]
    bernstein := [(8959089517555131724147075123734271191713306650319/36949768371974317197037506766848000000000000000000000), (184759542738904050506954877288218079328596327667759/555067631543436409448830101653094400000000000000000000), (4657192012002755430971802053223057366176946647450869/11989460841338226444094730195706839040000000000000000000), (145367843079531981675226766981309704088278525701423/355243284187799302047251265057980416000000000000000000), (336900367245078620679762681589424962788574967029133/852583882050718324913403036139152998400000000000000000)]
    reserve := (24246673/100000000000) }

theorem tilt_025_014_valid : tilt_025_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_014]
  · intro i; fin_cases i <;> norm_num [tilt_025_014]
  · norm_num [tilt_025_014]
  · norm_num [tilt_025_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_014]

def tilt_025_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1453/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (61/5000000), 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (5577341/100000000), (138191/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-2781824417261787761128011419555231939748044531/648111806036223467665955425728300000000000000000), (178521440868802322407/292921320739500000000), (-6525881043703393337477753480891430711614763044531/324055903018111733832977712864150000000000000000), (178521440868802322407/292921320739500000000), (-13048980262989524887194378950363306191289778044531/648111806036223467665955425728300000000000000000)]
    bernstein := [(4780129877530177836502508944025563239094063262198669/26546659575243713235597534237831168000000000000000000000), (620547281217493274214774156130763348786207728572261/2359703073354996732053114154473881600000000000000000000), (15959497725026700844713363435809103304349675738134951/50969586384467929412347265736635842560000000000000000000), (499102940545189930685141170113284375434753595644517/1510209966947197908513993058863284224000000000000000000), (1141991003621115775918143524249992181252621695650607/3624503920673274980433583341271882137600000000000000000)]
    reserve := (180065211/1000000000000) }

theorem tilt_025_015_valid : tilt_025_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_015]
  · intro i; fin_cases i <;> norm_num [tilt_025_015]
  · norm_num [tilt_025_015]
  · norm_num [tilt_025_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_015]

def tilt_025_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (269/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1889/50000000), (5577341/100000000), (129961/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-2650618750962599636814057195179818110089717339743/575685352748923237894082303818373850000000000000000), (358330165597749596917/550952634609000000000), (-6157770436884597840973441764440675908158006324839743/287842676374461618947041151909186925000000000000000), (358330165597749596917/550952634609000000000), (-12312890255018233082310069471686171998205922932339743/575685352748923237894082303818373850000000000000000)]
    bernstein := [(25619980479595711625859565678483784249571060871276153/139527053541987549255275805706512384000000000000000000000), (574328079104323557690463501273977510417164038890577433/2096006404319635184368143214613386035200000000000000000000), (14921732168945289553299796087059666765908858686890404003/45273738333304119982351893435649138360320000000000000000000), (469978178066033082474370854024355091885178401197496601/1341444098764566517995611657352567062528000000000000000000), (1082691089575833248255310654871192017742087155522263371/3219465837034959643189467977646160950067200000000000000000)]
    reserve := (45905041/250000000000) }

theorem tilt_025_016_valid : tilt_025_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_016]
  · intro i; fin_cases i <;> norm_num [tilt_025_016]
  · norm_num [tilt_025_016]
  · norm_num [tilt_025_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_016]

def tilt_025_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (61/5000000), 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (2787289/50000000), (138191/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1371127908683667205072339346814468622984887391/323895366579683629343655557840700000000000000000), (178521440868802322407/292921320739500000000), (-3261304974489845249593185830736133202024419887391/161947683289841814671827778920350000000000000000), (178521440868802322407/292921320739500000000), (-6521238821071006831981299322125451935425854887391/323895366579683629343655557840700000000000000000)]
    bernstein := [(3171266609547211896107501129829017367485108051147809/13266754215103841457916131649155072000000000000000000000), (379668043849546354671583360962330300224824246008921/1179267041342563685148100591036006400000000000000000000), (9478098495267805729647801355273682630314879135623011/25472168092999375599198972766377738240000000000000000000), (293942546272505940316472058168861423360145738312537/754730906459240758494784378263044096000000000000000000), (677553135229188816738423472304562135089371844374027/1811354175502177820387482507831305830400000000000000000)]
    reserve := (239038619/1000000000000) }

theorem tilt_025_017_valid : tilt_025_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_017]
  · intro i; fin_cases i <;> norm_num [tilt_025_017]
  · norm_num [tilt_025_017]
  · norm_num [tilt_025_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_017]

def tilt_025_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (2790053/50000000), (129961/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1379595185354691967913826580171427254463534653/304907756585139629213834894706900000000000000000), (358330165597749596917/550952634609000000000), (-3261396141200159686482037715939490760607318534653/152453878292569814606917447353450000000000000000), (358330165597749596917/550952634609000000000), (-6521412687214964680996161605298810093960173534653/304907756585139629213834894706900000000000000000)]
    bernstein := [(19457566951750290336224891963336053287239995242763/73899536743948634394075013533696000000000000000000000), (392645016028038006586524666955679357535742666417643/1110135263086872818897660203306188800000000000000000000), (9813925258816513888484383272540245815536371327175113/23978921682676452888189460391413678080000000000000000000), (305537582341581058043626990612792722628270751668971/710486568375598604094502530115960832000000000000000000), (709327019586684796695161948940865197579886331240641/1705167764101436649826806072278305996800000000000000000)]
    reserve := (263297549/1000000000000) }

theorem tilt_025_018_valid : tilt_025_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_018]
  · intro i; fin_cases i <;> norm_num [tilt_025_018]
  · norm_num [tilt_025_018]
  · norm_num [tilt_025_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_018]

def tilt_025_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (5577341/100000000), (134037/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-59938260971532668092447254225395669755495739/13969548128745686917308759840180000000000000000), (2667792523/4239369000), (-144944274351375209377478614396573048002836505739/6984774064372843458654379920090000000000000000), (2667792523/4239369000), (-96609536813926295362288260512973566778639171913/4656516042915228972436253280060000000000000000)]
    bernstein := [(63664934915307756326539134945765998826083779861687/190730897117807778710988934351257600000000000000000000), (192361659802954333228088650613013224318903160818981/457754153082738668906373442443018240000000000000000000), (519527624580203286692943890262786263407726144356719/1098609967398572805375296261863243776000000000000000000), (144076140787032830066431943847262626554748845240357/292962657972952748100079003163531673600000000000000000), (111773034582588445876470569225317349587808227187749/234370126378362198480063202530825338880000000000000000)]
    reserve := (166897277/500000000000) }

theorem tilt_025_019_valid : tilt_025_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_019]
  · intro i; fin_cases i <;> norm_num [tilt_025_019]
  · norm_num [tilt_025_019]
  · norm_num [tilt_025_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_019]

def tilt_025_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558963/100000000), (1/100000000), (4239369/100000000), (1070457/25000000), (1/100000000), (5577341/100000000), (134037/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-62226605665728434693528143520435635465495739/13969548128745686917308759840180000000000000000), (2667792523/4239369000), (-144941953246693696889367143726505306831008505739/6984774064372843458654379920090000000000000000), (2667792523/4239369000), (-96607226629240555114680253103163392675517171913/4656516042915228972436253280060000000000000000)]
    bernstein := [(32431307714047362022637942637185839506119701861687/190730897117807778710988934351257600000000000000000000), (117403926920032534327657036334553436755391086818981/457754153082738668906373442443018240000000000000000000), (339636794455903477224788684797805874188526370356719/1098609967398572805375296261863243776000000000000000000), (96107472497111303187710190096119818030045859240357/292962657972952748100079003163531673600000000000000000), (73400002785717130847902647801768482440469209187749/234370126378362198480063202530825338880000000000000000)]
    reserve := (17003699/100000000000) }

theorem tilt_025_020_valid : tilt_025_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_025_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_025_020]
  · intro i; fin_cases i <;> norm_num [tilt_025_020]
  · norm_num [tilt_025_020]
  · norm_num [tilt_025_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_025_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_025_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_025_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_025_020]

def tiltBundle025_row : Alternative → Row
  | .zero => tilt_025_000
  | (.spike 0 false false) => tilt_025_001
  | (.spike 0 false true) => tilt_025_002
  | (.spike 0 true false) => tilt_025_003
  | (.spike 0 true true) => tilt_025_004
  | (.spike 1 false false) => tilt_025_005
  | (.spike 1 false true) => tilt_025_006
  | (.spike 1 true false) => tilt_025_007
  | (.spike 1 true true) => tilt_025_008
  | (.spike 2 false false) => tilt_025_009
  | (.spike 2 false true) => tilt_025_010
  | (.spike 2 true false) => tilt_025_011
  | (.spike 2 true true) => tilt_025_012
  | (.spike 3 false false) => tilt_025_013
  | (.spike 3 false true) => tilt_025_014
  | (.spike 3 true false) => tilt_025_015
  | (.spike 3 true true) => tilt_025_016
  | (.spike 4 false false) => tilt_025_017
  | (.spike 4 false true) => tilt_025_018
  | (.spike 4 true false) => tilt_025_019
  | (.spike 4 true true) => tilt_025_020

def tiltBundle025 : TiltBundle where
  interval := ⟨(1/80), (1/64)⟩
  lambda := ![(7276703/50000000), (7276703/50000000), (1743857/20000000), (14530119/100000000), (14530119/100000000), (830773/5000000), (3299641/20000000)]
  row := tiltBundle025_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_025_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_025_001_valid | exact tilt_025_002_valid | exact tilt_025_003_valid | exact tilt_025_004_valid | exact tilt_025_005_valid | exact tilt_025_006_valid | exact tilt_025_007_valid | exact tilt_025_008_valid | exact tilt_025_009_valid | exact tilt_025_010_valid | exact tilt_025_011_valid | exact tilt_025_012_valid | exact tilt_025_013_valid | exact tilt_025_014_valid | exact tilt_025_015_valid | exact tilt_025_016_valid | exact tilt_025_017_valid | exact tilt_025_018_valid | exact tilt_025_019_valid | exact tilt_025_020_valid
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
