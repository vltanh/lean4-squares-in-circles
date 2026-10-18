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

def tilt_019_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2801647/50000000), (3377/25000000)]
    alternative := .zero
    polynomial := [(144059404042854381812867482332475032407273/2166344353883351598523735501300000000000000000), (66337127596401/105991850000000), (-226345824805071879701108289456093392827717592727/1083172176941675799261867750650000000000000000), (66337127596401/105991850000000), (-452691793669547802256598391779669118130467592727/2166344353883351598523735501300000000000000000)]
    bernstein := [(2488441578836411396136220886389299190100505356399453673/5815236344877028571580478661148540928000000000000000000000), (1414226686276048455760825147884421569225482401003972073/2907618172438514285790239330574270464000000000000000000000), (761212645383296154824347651393469223127446500626884073/1453809086219257142895119665287135232000000000000000000000), (2632242606509997546561866980949742758191901163951877/4878553980601534036560804245929984000000000000000000000), (1303188220352660724255543696230198699678902875772677/2439276990300767018280402122964992000000000000000000000)]
    reserve := (42791753/100000000000) }

theorem tilt_019_000_valid : tilt_019_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_000]
  · intro i; fin_cases i <;> norm_num [tilt_019_000]
  · norm_num [tilt_019_000]
  · norm_num [tilt_019_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_000]

def tilt_019_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7241/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2163/50000000), 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2801647/50000000), (3577/20000000)]
    alternative := (.spike 0 false false)
    polynomial := [(2905431792822290194911393542653355052576401/15144652287636642347725215416580000000000000000), (35503719021333451299/75826569490000000000), (-1195950540232882211158182386161285327739280623599/7572326143818321173862607708290000000000000000), (35503719021333451299/75826569490000000000), (-2391903985897557244606559683716113308833613823599/15144652287636642347725215416580000000000000000)]
    bernstein := [(18751375766794663230629119273440374022887097785955533201/40653616427931852509205287630478822604800000000000000000000), (3418282916638869119667892599314484656895170344386184667/6775602737988642084867547938413137100800000000000000000000), (16211154693159840201324440215553818768065550483212494003/30490212320948889381903965722859116953600000000000000000000), (6170833869455440809221648834684568412171088501342383/11368460969779600813536154259082444800000000000000000000), (125642306955307721961214039432087722083608346184613/233598513077663030415126457378406400000000000000000000)]
    reserve := (461247421/1000000000000) }

theorem tilt_019_001_valid : tilt_019_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_001]
  · intro i; fin_cases i <;> norm_num [tilt_019_001]
  · norm_num [tilt_019_001]
  · norm_num [tilt_019_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_001]

def tilt_019_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (429/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (753/20000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2801647/50000000), (9379/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-7619248009397783863377406308750926167965046847/49835707499639028813821657315373300000000000000000), (8149960286967227727/8797323550000000000), (-7496116493471650015907797460011741311619813083046847/24917853749819514406910828657686650000000000000000), (8149960286967227727/8797323550000000000), (-14992225367695290634031731542617173872313458201046847/49835707499639028813821657315373300000000000000000)]
    bernstein := [(51806321989653946924980492121357767261631359165533578383553/133776708677482225350353556841279675957248000000000000000000000), (10621715490620281423012621659041730892141591836504623868651/22296118112913704225058926140213279326208000000000000000000000), (53670299524316401761240817926282565814208151719541951713859/100332531508111669012765167630959756967936000000000000000000000), (21056107672662756106727313823145558762003986809992559999/37409594149184067491709607617807515648000000000000000000000), (31434145448089047312387897307015846288017108293169948797/56114391223776101237564411426711273472000000000000000000000)]
    reserve := (193629827/500000000000) }

theorem tilt_019_002_valid : tilt_019_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_002]
  · intro i; fin_cases i <;> norm_num [tilt_019_002]
  · norm_num [tilt_019_002]
  · norm_num [tilt_019_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_002]

def tilt_019_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2163/50000000), 0, 0]] i.1) i.2
    mu := ![(5598859/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2801647/50000000), (3577/20000000)]
    alternative := (.spike 0 true false)
    polynomial := [(181564509913417233907133649168117031036859/720817298669513761412230449580000000000000000), (35503719021333451299/75826569490000000000), (-56921820714951810111656810938085616408122163141/360408649334756880706115224790000000000000000), (35503719021333451299/75826569490000000000), (-113843822994413533640547529009820400933275363141/720817298669513761412230449580000000000000000)]
    bernstein := [(1008657511907023559365575819483917543401049365511248059/1934929202610391198429672847100923084800000000000000000000), (546172892471541650176501543556064400763572167912835259/967464601305195599214836423550461542400000000000000000000), (286236814112695585188217554363162928711794939155331259/483732300652597799607418211775230771200000000000000000000), (978575436734277131442214827819941989682692907032591/1623262753867777851031604737500774400000000000000000000), (6647568594659752033144260151849325242548084751767/11118238040190259253641128339046400000000000000000000)]
    reserve := (32580569/62500000000) }

theorem tilt_019_003_valid : tilt_019_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_003]
  · intro i; fin_cases i <;> norm_num [tilt_019_003]
  · norm_num [tilt_019_003]
  · norm_num [tilt_019_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_003]

def tilt_019_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(14011/250000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2801647/50000000), (9379/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-25293462486698683893342914760849035840401/264862470673844607192490895840000000000000000), (8149960286967227727/8797323550000000000), (-39839690795981665294581201492184171205442240401/132431235336922303596245447920000000000000000), (8149960286967227727/8797323550000000000), (-79679356298500843890478509641453581561848640401/264862470673844607192490895840000000000000000)]
    bernstein := [(316139710374675175858087047870295801103930410274802799/710984780926201044048571734006589030400000000000000000000), (189756107944027517060889603376037239814191360844581999/355492390463100522024285867003294515200000000000000000000), (315845261720179978199073271221551596760722111340913997/533238585694650783036428800504941772800000000000000000000), (369953111099813005913065468690657862122016131236851/596463742387752553732023266784051200000000000000000000), (184179284169738778829318738927909558921147205387251/298231871193876276866011633392025600000000000000000000)]
    reserve := (22232523/50000000000) }

theorem tilt_019_004_valid : tilt_019_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_004]
  · intro i; fin_cases i <;> norm_num [tilt_019_004]
  · norm_num [tilt_019_004]
  · norm_num [tilt_019_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_004]

def tilt_019_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2163/50000000), 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (4240327/100000000), (1/100000000), (2801647/50000000), (3577/20000000)]
    alternative := (.spike 1 false false)
    polynomial := [(1297090463856826811029736347547886910885231/7208592468625833322097260900700000000000000000), (35503719021333451299/75826569490000000000), (-569251851645302859340153581479958598512167114769/3604296234312916661048630450350000000000000000), (35503719021333451299/75826569490000000000), (-1138505000381069575507118192696264744911245114769/7208592468625833322097260900700000000000000000)]
    bernstein := [(8694892276773289416804986678638465957620035528183186031/19350418064337412611971731062303752192000000000000000000000), (4765911430009149211250729329400297475706041161650270831/9675209032168706305985865531151876096000000000000000000000), (193420520262653879702802489276338994847278348173594987/372123424314181011768687135813533696000000000000000000000), (8618309395352229069939090001794782331785011195064819/16233572201625346150982995857637376000000000000000000000), (58479445733464659547246925414782780852737643661403/111188850696064014732760245600256000000000000000000000)]
    reserve := (449338729/1000000000000) }

theorem tilt_019_005_valid : tilt_019_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_005]
  · intro i; fin_cases i <;> norm_num [tilt_019_005]
  · norm_num [tilt_019_005]
  · norm_num [tilt_019_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_005]

def tilt_019_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (424403/10000000), (1/100000000), (2801647/50000000), (9379/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-1103912980776640148966654087937775482499391/13242354365099286579461601684700000000000000000), (8149960286967227727/8797323550000000000), (-1991868683450282080888592989391941535061044499391/6621177182549643289730800842350000000000000000), (8149960286967227727/8797323550000000000), (-3983736262987583385137037012129795132346606499391/13242354365099286579461601684700000000000000000)]
    bernstein := [(16237408016623832470058437412116781130544414949556111809/35547174325090174782324552827228127232000000000000000000000), (9702924759948580845342759736874607011158344661013699009/17773587162545087391162276413614063616000000000000000000000), (2302121679346451254972618977300463089940124323629797861/3808625820545375869534773517203013632000000000000000000000), (18858444983744856100011815468773682870416970989481341/29821454970713233877789054385258496000000000000000000000), (9389361459028001221262554015155222197327334541327741/14910727485356616938894527192629248000000000000000000000)]
    reserve := (228392387/500000000000) }

theorem tilt_019_006_valid : tilt_019_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_006]
  · intro i; fin_cases i <;> norm_num [tilt_019_006]
  · norm_num [tilt_019_006]
  · norm_num [tilt_019_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_006]

def tilt_019_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2163/50000000), 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (4237821/100000000), (2121089/50000000), (1/100000000), (2801647/50000000), (3577/20000000)]
    alternative := (.spike 1 true false)
    polynomial := [(1297121712499718144088968570852320967635853/7208587208114024951949834341700000000000000000), (3380744643619776527/7218421770000000000), (-569252482574773262446088012566571276859912364147/3604293604057012475974917170850000000000000000), (3380744643619776527/7218421770000000000), (-1138506262271259024610320114101713406040792364147/7208587208114024951949834341700000000000000000)]
    bernstein := [(8696887113963612511982112875788632862439700402010426253/19350403943258551879720318706386993152000000000000000000000), (1589049153270396935421714350049288495356876777833269551/3225067323876425313286719784397832192000000000000000000000), (7545611993765082039786212426222709924641159945642721959/14512802957443913909790239029790244864000000000000000000000), (2873727704702151972433850399797947352506832046194099/5411186785027559250481073463754752000000000000000000000), (58501864967124305658063480417407927608373070750289/111188769555360806516734386241536000000000000000000000)]
    reserve := (112360537/250000000000) }

theorem tilt_019_007_valid : tilt_019_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_007]
  · intro i; fin_cases i <;> norm_num [tilt_019_007]
  · norm_num [tilt_019_007]
  · norm_num [tilt_019_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_007]

def tilt_019_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (4241527/100000000), (2121089/50000000), (1/100000000), (2801647/50000000), (9379/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-11039727880706567461765838606249929785478821/132423609001206889486087828323100000000000000000), (16304813124773427717/17602337050000000000), (-19918677459435415841014685128774839750271493478821/66211804500603444743043914161550000000000000000), (16304813124773427717/17602337050000000000), (-39837343879142950975461908491711073250613201478821/132423609001206889486087828323100000000000000000)]
    bernstein := [(162337425596822216180310528546330334642228094116944108379/355471918674046759295395918519610638336000000000000000000000), (97006543008260642597543120657696285673157132483141151579/177735959337023379647697959259805319168000000000000000000000), (161107898539650708261868009181420270145602199426009182737/266603939005535069471546938889707978752000000000000000000000), (188531678792312119708905866352989105964624879036084271/298214696874200301422312012180881408000000000000000000000), (93863563253547636801259462488683454323183533125402671/149107348437100150711156006090440704000000000000000000000)]
    reserve := (228340717/500000000000) }

theorem tilt_019_008_valid : tilt_019_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_008]
  · intro i; fin_cases i <;> norm_num [tilt_019_008]
  · norm_num [tilt_019_008]
  · norm_num [tilt_019_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_008]

def tilt_019_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2163/50000000), 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (530041/12500000), (1/100000000), (2801647/50000000), (3577/20000000)]
    alternative := (.spike 2 false false)
    polynomial := [(907554401790791642338570464112279584606197/5046015918044120133026397229360000000000000000), (35503719021333451299/75826569490000000000), (-398476390533860115806972084601317664551229793803/2523007959022060066513198614680000000000000000), (35503719021333451299/75826569490000000000), (-796953688622122022405586507773099441382044193803/5046015918044120133026397229360000000000000000)]
    bernstein := [(6085327758902500212399812234186945847234255532910455797/13545295839434320160277216003003881881600000000000000000000), (3335589652332761266877061602423153067936251853629713397/6772647919717160080138608001501940940800000000000000000000), (1759852581539940491142250333940518741349708997470481397/3386323959858580040069304000750970470400000000000000000000), (6031896629599353034790332367033838811499745156253153/11363503221001946443185583895137484800000000000000000000), (40929310907057580117225308512553234945263439366361/77832213842479085227298519829708800000000000000000000)]
    reserve := (28078603/62500000000) }

theorem tilt_019_009_valid : tilt_019_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_009]
  · intro i; fin_cases i <;> norm_num [tilt_019_009]
  · norm_num [tilt_019_009]
  · norm_num [tilt_019_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_009]

def tilt_019_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (4244031/100000000), (1/100000000), (2801647/50000000), (9379/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-283953104496120879523582306851462384641489/12038506804845799505127095292900000000000000000), (8149960286967227727/8797323550000000000), (-1810789419290651889768989742635285771871318641489/6019253402422899752563547646450000000000000000), (8149960286967227727/8797323550000000000), (-3621578554628199283417099961688264692280252641489/12038506804845799505127095292900000000000000000)]
    bernstein := [(16692959169467444059757674134684818286663055411856363311/32315620637178851998433661629050650624000000000000000000000), (3262227065629162308603274780664021898232477876258024037/5385936772863141999738943604841775104000000000000000000000), (16098627504502066094804144371594370546634001271766568333/24236715477884138998825246221787987968000000000000000000000), (6254860725228169972271774969436071666856944992378513/9036806665877755033119032894029824000000000000000000000), (9346054765814224514875818529450650307173427992841139/13555209998816632549678549341044736000000000000000000000)]
    reserve := (516560067/1000000000000) }

theorem tilt_019_010_valid : tilt_019_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_010]
  · intro i; fin_cases i <;> norm_num [tilt_019_010]
  · norm_num [tilt_019_010]
  · norm_num [tilt_019_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_010]

def tilt_019_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14481/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2163/50000000), 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2801647/50000000), (3577/20000000)]
    alternative := (.spike 2 true false)
    polynomial := [(968424425019777344590371857653258348606667/5048217429212214115908405138860000000000000000), (35503719021333451299/75826569490000000000), (-398650180130466658038781175479751673773095793333/2524108714606107057954202569430000000000000000), (35503719021333451299/75826569490000000000), (-797301328685358335854906941331361000804540193333/5048217429212214115908405138860000000000000000)]
    bernstein := [(6250316749465131442501311307733959786377688305797752267/13551205475977284169735095876826274201600000000000000000000), (3418211996862371692255626012542641242280968758010385867/6775602737988642084867547938413137100800000000000000000000), (5403611851301962012453981641869129146461873301608501601/10163404106982963127301321907619705651200000000000000000000), (6170714876323972122400583145005547496794181284521183/11368460969779600813536154259082444800000000000000000000), (41879953962659260309365451400510515959873649130471/77866171025887676805042152459468800000000000000000000)]
    reserve := (230618477/500000000000) }

theorem tilt_019_011_valid : tilt_019_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_011]
  · intro i; fin_cases i <;> norm_num [tilt_019_011]
  · norm_num [tilt_019_011]
  · norm_num [tilt_019_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_011]

def tilt_019_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4289/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (753/20000000), (2801647/50000000), (9379/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-7618450812728846600559714991257774798160594447/49835707499639028813821657315373300000000000000000), (8149960286967227727/8797323550000000000), (-7496116492674453346970534642320423818468443278594447/24917853749819514406910828657686650000000000000000), (8149960286967227727/8797323550000000000), (-14992225366898093965094468724925856379162088396594447/49835707499639028813821657315373300000000000000000)]
    bernstein := [(51808461950779680318749371996416642762812089000375951155953/133776708677482225350353556841279675957248000000000000000000000), (10622072151025591625238015027846255521021163048809122099451/22296118112913704225058926140213279326208000000000000000000000), (53671904497446425889436902892302607761921666189581712591059/100332531508111669012765167630959756967936000000000000000000000), (21056706097257344211786823900863796363659467527243749199/37409594149184067491709607617807515648000000000000000000000), (31435043086076676291431430166509918584836887165266556397/56114391223776101237564411426711273472000000000000000000000)]
    reserve := (387275651/1000000000000) }

theorem tilt_019_012_valid : tilt_019_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_012]
  · intro i; fin_cases i <;> norm_num [tilt_019_012]
  · norm_num [tilt_019_012]
  · norm_num [tilt_019_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_012]

def tilt_019_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2163/50000000), 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (5600523/100000000), (3577/20000000)]
    alternative := (.spike 3 false false)
    polynomial := [(12711593109000077738434157066168880988248241/50457209315277543953734515578700000000000000000), (35503719021333451299/75826569490000000000), (-3984527322283549272927037189867931668202209751759/25228604657638771976867257789350000000000000000), (35503719021333451299/75826569490000000000), (-7969067356160207545931812813892929505285407751759/50457209315277543953734515578700000000000000000)]
    bernstein := [(70611601207901698700867575452677232576628926093957317041/135445039910339752777807675923074383872000000000000000000000), (12744963356507283909438710424262298380241428224411269947/22574173318389958796301279320512397312000000000000000000000), (60113912274731933277800140151729496225465524588457141523/101583779932754814583355756942305787904000000000000000000000), (3402412895029082192883186265036049988293912108390636347/5643543329597489699075319830128099328000000000000000000000), (69338913616560088407396137865950294288293845637285417/115963219101318281487849037605371904000000000000000000000)]
    reserve := (130332571/250000000000) }

theorem tilt_019_013_valid : tilt_019_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_013]
  · intro i; fin_cases i <;> norm_num [tilt_019_013]
  · norm_num [tilt_019_013]
  · norm_num [tilt_019_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_013]

def tilt_019_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2803033/50000000), (9379/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-3163634587135277457774480125429139668255501/33107809875773191944534052908950000000000000000), (8149960286967227727/8797323550000000000), (-4979961508114599469461743639597053666239885255501/16553904937886595972267026454475000000000000000), (8149960286967227727/8797323550000000000), (-9959919852594611803646029504713981903340102255501/33107809875773191944534052908950000000000000000)]
    bernstein := [(39512226041014413733201865429101905049323985729677507699/88873100411644801322065252001421197312000000000000000000000), (23716894738097347015444678378585153327106682580521206899/44436550205822400661032626000710598656000000000000000000000), (13158909900733318290236185578407238863655146937871862899/22218275102911200330516313000355299328000000000000000000000), (6889722034524816775505052606605523934888524343033795699/11109137551455600165258156500177649664000000000000000000000), (3430011836939937977889811717697053127641051502659165299/5554568775727800082629078250088824832000000000000000000000)]
    reserve := (444591511/1000000000000) }

theorem tilt_019_014_valid : tilt_019_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_014]
  · intro i; fin_cases i <;> norm_num [tilt_019_014]
  · norm_num [tilt_019_014]
  · norm_num [tilt_019_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_014]

def tilt_019_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14481/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2163/50000000), 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2801647/50000000), (3577/20000000)]
    alternative := (.spike 3 true false)
    polynomial := [(968424425019777344590371857653258348606667/5048217429212214115908405138860000000000000000), (35503719021333451299/75826569490000000000), (-398650180130466658038781175479751673773095793333/2524108714606107057954202569430000000000000000), (35503719021333451299/75826569490000000000), (-797301328685358335854906941331361000804540193333/5048217429212214115908405138860000000000000000)]
    bernstein := [(6250316749465131442501311307733959786377688305797752267/13551205475977284169735095876826274201600000000000000000000), (3418211996862371692255626012542641242280968758010385867/6775602737988642084867547938413137100800000000000000000000), (5403611851301962012453981641869129146461873301608501601/10163404106982963127301321907619705651200000000000000000000), (6170714876323972122400583145005547496794181284521183/11368460969779600813536154259082444800000000000000000000), (41879953962659260309365451400510515959873649130471/77866171025887676805042152459468800000000000000000000)]
    reserve := (230618477/500000000000) }

theorem tilt_019_015_valid : tilt_019_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_015]
  · intro i; fin_cases i <;> norm_num [tilt_019_015]
  · norm_num [tilt_019_015]
  · norm_num [tilt_019_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_015]

def tilt_019_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4289/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (753/20000000), (2801647/50000000), (9379/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-7618450812728846600559714991257774798160594447/49835707499639028813821657315373300000000000000000), (8149960286967227727/8797323550000000000), (-7496116492674453346970534642320423818468443278594447/24917853749819514406910828657686650000000000000000), (8149960286967227727/8797323550000000000), (-14992225366898093965094468724925856379162088396594447/49835707499639028813821657315373300000000000000000)]
    bernstein := [(51808461950779680318749371996416642762812089000375951155953/133776708677482225350353556841279675957248000000000000000000000), (10622072151025591625238015027846255521021163048809122099451/22296118112913704225058926140213279326208000000000000000000000), (53671904497446425889436902892302607761921666189581712591059/100332531508111669012765167630959756967936000000000000000000000), (21056706097257344211786823900863796363659467527243749199/37409594149184067491709607617807515648000000000000000000000), (31435043086076676291431430166509918584836887165266556397/56114391223776101237564411426711273472000000000000000000000)]
    reserve := (387275651/1000000000000) }

theorem tilt_019_016_valid : tilt_019_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_016]
  · intro i; fin_cases i <;> norm_num [tilt_019_016]
  · norm_num [tilt_019_016]
  · norm_num [tilt_019_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_016]

def tilt_019_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2163/50000000), 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (1400131/25000000), (3577/20000000)]
    alternative := (.spike 4 false false)
    polynomial := [(1270996555541981769502278637937333122366713/5045721832465208188127163197560000000000000000), (35503719021333451299/75826569490000000000), (-398452803536966375484899199858054957000720033287/2522860916232604094063581598780000000000000000), (35503719021333451299/75826569490000000000), (-796906878070488292951567901994747851334562433287/5045721832465208188127163197560000000000000000)]
    bernstein := [(7060723878700248574303598039950473191368136085804005113/13544506409469537641148488389234366873600000000000000000000), (3823270938073993874120841877376934489744449143232075513/6772253204734768820574244194617183436800000000000000000000), (6011064173198148796339277419517542692331840093667042539/10158379807102153230861366291925775155200000000000000000000), (1020669362768604770970027499714506872024533629554661113/1693063301183692205143561048654295859200000000000000000000), (6933518023968310486730740292997413611275651645464881/11596323980710220583175075675714355200000000000000000000)]
    reserve := (521297983/1000000000000) }

theorem tilt_019_017_valid : tilt_019_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_017]
  · intro i; fin_cases i <;> norm_num [tilt_019_017]
  · norm_num [tilt_019_017]
  · norm_num [tilt_019_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_017]

def tilt_019_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2803033/50000000), (9379/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-2398687550928132646150940658357771262243001/33107809875773191944534052908950000000000000000), (8149960286967227727/8797323550000000000), (-4979960743167563262316932016057586594871479243001/16553904937886595972267026454475000000000000000), (8149960286967227727/8797323550000000000), (-9959919087647575596501217881174514831971696243001/33107809875773191944534052908950000000000000000)]
    bernstein := [(41565617612394761203472180473700651914370635711843520199/88873100411644801322065252001421197312000000000000000000000), (24743591150432515284990969155293869954228541461247219399/44436550205822400661032626000710598656000000000000000000000), (13672258524664359605789454327169763230192944199397875399/22218275102911200330516313000355299328000000000000000000000), (7146396607592641598838552920894069314918041243599808199/11109137551455600165258156500177649664000000000000000000000), (3558349280135385878297922867748020443605595188505177799/5554568775727800082629078250088824832000000000000000000000)]
    reserve := (46769627/100000000000) }

theorem tilt_019_018_valid : tilt_019_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_018]
  · intro i; fin_cases i <;> norm_num [tilt_019_018]
  · norm_num [tilt_019_018]
  · norm_num [tilt_019_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_018]

def tilt_019_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2801647/50000000), (3377/25000000)]
    alternative := (.spike 4 true false)
    polynomial := [(1015323868973106669913333199572899082348921/4332688707766703197047471002600000000000000000), (66337127596401/105991850000000), (-452692101674684574276799936824158334805557594579/2166344353883351598523735501300000000000000000), (66337127596401/105991850000000), (-905385218673238121660269786981516242510197538079/4332688707766703197047471002600000000000000000)]
    bernstein := [(6928957897594268332226456871822750711233802841315754721/11630472689754057143160957322297081856000000000000000000000), (3804490372180732178882140584952930499814577464079991521/5815236344877028571580478661148540928000000000000000000000), (2010443543692579719227509415974822353805176022621815521/2907618172438514285790239330574270464000000000000000000000), (6902129321459467841944476894048169770810401458137629/9757107961203068073121608491859968000000000000000000000), (3425197873558389192333718957616125537611721464179229/4878553980601534036560804245929984000000000000000000000)]
    reserve := (148939731/250000000000) }

theorem tilt_019_019_valid : tilt_019_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_019]
  · intro i; fin_cases i <;> norm_num [tilt_019_019]
  · norm_num [tilt_019_019]
  · norm_num [tilt_019_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_019]

def tilt_019_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3/12500000), 0, 0]] i.1) i.2
    mu := ![(5601629/100000000), (1/100000000), (2119837/50000000), (2121089/50000000), (1/100000000), (2801647/50000000), (13509/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(705333957579503975554247067098834460560947/10591800896348243483335918525900000000000000000), (3111627373804962027/4971680214062500000), (-1106580606909595971409590065728297162218652412053/5295900448174121741667959262950000000000000000), (3111627373804962027/4971680214062500000), (-2213161919153149522323155685703661423271765385053/10591800896348243483335918525900000000000000000)]
    bernstein := [(12169548003476320006772924920445396398864340624667664547/28432149034724494742483056906788143104000000000000000000000), (6916042573788103401566289692695440597722886378577322147/14216074517362247371241528453394071552000000000000000000000), (11167712824260785970470111106609849628847511719510270441/21324111776043371056862292680091107328000000000000000000000), (677505464762413520980855082228934074137566362689837/1255393369601046217877210213122048000000000000000000000), (6373180722876202173466696750992970340917636453398103/11926237011209939069833497024659456000000000000000000000)]
    reserve := (26751293/62500000000) }

theorem tilt_019_020_valid : tilt_019_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_019_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_019_020]
  · intro i; fin_cases i <;> norm_num [tilt_019_020]
  · norm_num [tilt_019_020]
  · norm_num [tilt_019_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_019_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_019_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_019_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_019_020]

def tiltBundle019_row : Alternative → Row
  | .zero => tilt_019_000
  | (.spike 0 false false) => tilt_019_001
  | (.spike 0 false true) => tilt_019_002
  | (.spike 0 true false) => tilt_019_003
  | (.spike 0 true true) => tilt_019_004
  | (.spike 1 false false) => tilt_019_005
  | (.spike 1 false true) => tilt_019_006
  | (.spike 1 true false) => tilt_019_007
  | (.spike 1 true true) => tilt_019_008
  | (.spike 2 false false) => tilt_019_009
  | (.spike 2 false true) => tilt_019_010
  | (.spike 2 true false) => tilt_019_011
  | (.spike 2 true true) => tilt_019_012
  | (.spike 3 false false) => tilt_019_013
  | (.spike 3 false true) => tilt_019_014
  | (.spike 3 true false) => tilt_019_015
  | (.spike 3 true true) => tilt_019_016
  | (.spike 4 false false) => tilt_019_017
  | (.spike 4 false true) => tilt_019_018
  | (.spike 4 true false) => tilt_019_019
  | (.spike 4 true true) => tilt_019_020

def tiltBundle019 : TiltBundle where
  interval := ⟨(1/1280), (1/640)⟩
  lambda := ![(14482487/100000000), (14482487/100000000), (2123769/25000000), (14480699/100000000), (14480699/100000000), (16794399/100000000), (8392077/50000000)]
  row := tiltBundle019_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_019_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_019_001_valid | exact tilt_019_002_valid | exact tilt_019_003_valid | exact tilt_019_004_valid | exact tilt_019_005_valid | exact tilt_019_006_valid | exact tilt_019_007_valid | exact tilt_019_008_valid | exact tilt_019_009_valid | exact tilt_019_010_valid | exact tilt_019_011_valid | exact tilt_019_012_valid | exact tilt_019_013_valid | exact tilt_019_014_valid | exact tilt_019_015_valid | exact tilt_019_016_valid | exact tilt_019_017_valid | exact tilt_019_018_valid | exact tilt_019_019_valid | exact tilt_019_020_valid
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
