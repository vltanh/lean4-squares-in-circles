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

def tilt_036_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5509457/100000000), (387947/100000000)]
    alternative := .zero
    polynomial := [(-1777462670576840110961903146430046975907990091/119769108113526454524691202988150000000000000000), (67525008300857/105407325000000), (-413931572783101449249418136930184452409157990091/59884554056763227262345601494075000000000000000), (67525008300857/105407325000000), (-826085682895626058387874370713938857842407990091/119769108113526454524691202988150000000000000000)]
    bernstein := [(56323586662486969104034508703780651918263601985743581/2232657996608873165861024050924486656000000000000000000000), (20972089316538413652826683094021555418443465996814281/669797398982661949758307215277345996800000000000000000000), (20847446834181228957002968691551955206173672777112207/602817659084395754782476493749611397120000000000000000000), (140831448891469872366174153241183504677766833207583/4018784393895971698549843291664075980800000000000000000), (2627508891718782706798889326349876485322351072269/80375687877919433970996865833281519616000000000000000)]
    reserve := (3153393/125000000000) }

theorem tilt_036_000_valid : tilt_036_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_000]
  · intro i; fin_cases i <;> norm_num [tilt_036_000]
  · norm_num [tilt_036_000]
  · norm_num [tilt_036_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_000]

def tilt_036_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3683/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5509457/100000000), (391883/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-443745597497132704127796720477475237513035953/30246062860940468400644651653837500000000000000), (104770039806584708402083/165229354971900000000000), (-103531810929355328751887419995964862352630660953/15123031430470234200322325826918750000000000000), (104770039806584708402083/165229354971900000000000), (-206619876261213524799647043271452249467748285953/30246062860940468400644651653837500000000000000)]
    bernstein := [(19647357674146076067734902093979375723999211917301623/563827477519529112776433177823543296000000000000000000000), (6887694648364989454207543500580992604359315892849723/169148243255858733832929953347062988800000000000000000000), (6669123822983891318551085051263286675797526718139981/152233418930272860449636958012356689920000000000000000000), (44768631925103702525094140185464267626816239998589/1014889459535152402997579720082377932800000000000000000), (844979224087614301893728380133957907726779953927/20297789190703048059951594401647558656000000000000000)]
    reserve := (34846399/1000000000000) }

theorem tilt_036_001_valid : tilt_036_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_001]
  · intro i; fin_cases i <;> norm_num [tilt_036_001]
  · norm_num [tilt_036_001]
  · norm_num [tilt_036_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_001]

def tilt_036_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1091/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (383/10000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5509457/100000000), (384013/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-680458879826680467030743060528377512765867534617/45406404995687194302501277348124550000000000000000), (104799495555822263085917/161911132380900000000000), (-158459773166924192658194241742221784392577001034617/22703202497843597151250638674062275000000000000000), (104799495555822263085917/161911132380900000000000), (-316239087454021704849357740423915191272388134534617/45406404995687194302501277348124550000000000000000)]
    bernstein := [(749579157973159663208038418197856966119658550024293903/17274219147304379302653815654090539008000000000000000000000), (257530845899926810662971962460254533946709413748758003/5182265744191313790796144696227161702400000000000000000000), (12148440581591918903355101103524988738168298071780547909/228537919318836938174109981103617831075840000000000000000000), (81938593574659582676003755367407804090952924625896821/1523586128792246254494066540690785540505600000000000000000), (1571201616644506616203520936505838591272358152222703/30471722575844925089881330813815710810112000000000000000)]
    reserve := (2169647/50000000000) }

theorem tilt_036_002_valid : tilt_036_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_002]
  · intro i; fin_cases i <;> norm_num [tilt_036_002]
  · norm_num [tilt_036_002]
  · norm_num [tilt_036_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_002]

def tilt_036_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5459071/100000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5509457/100000000), (391883/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-110475399065103838001152875871042564622268851/7557744506537555133997870624426875000000000000), (104770039806584708402083/165229354971900000000000), (-25869638270394605135497634087365533197551200101/3778872253268777566998935312213437500000000000), (104770039806584708402083/165229354971900000000000), (-51628801141724106432994115298860023830480131351/7557744506537555133997870624426875000000000000)]
    bernstein := [(12502753710041761146458693447420973424341550582456241/140886568954437749549990243340071731200000000000000000000), (3999235031640310151813674242266183876653435401728941/42265970686331324864997073002021519360000000000000000000), (3716949092748297647032543626268610208969748146461227/38039373617698192378497365701819367424000000000000000000), (24857561869401717913784576449097957027946963847963/253595824117987949189982438012129116160000000000000000), (484579150464140220178356155117100417137216440609/5071916482359758983799648760242582323200000000000000)]
    reserve := (22185851/250000000000) }

theorem tilt_036_003_valid : tilt_036_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_003]
  · intro i; fin_cases i <;> norm_num [tilt_036_003]
  · norm_num [tilt_036_003]
  · norm_num [tilt_036_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_003]

def tilt_036_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5464519/100000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5509457/100000000), (384013/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-2212175980597842375642430347231143535176917211/148267137258832860128990184094462500000000000000), (104799495555822263085917/161911132380900000000000), (-517414541158629070666702517891799349100465542211/74133568629416430064495092047231250000000000000), (104799495555822263085917/161911132380900000000000), (-1032616906336660298957762605436367554665754167211/148267137258832860128990184094462500000000000000)]
    bernstein := [(6172284619418308936581714147950246973546724919239949/56406117630228725675325536971259904000000000000000000000), (1958400713000617197710079779285714113502333155960249/16921835289068617702597661091377971200000000000000000000), (88952952035660114811365288656619925044712203182414447/746252936247926040684556854129768529920000000000000000000), (596142197083944589379777818578478408067448838358143/4975019574986173604563712360865123532800000000000000000), (11702684708840469480659731381747671152394378930349/99500391499723472091274247217302470656000000000000000)]
    reserve := (109425801/1000000000000) }

theorem tilt_036_004_valid : tilt_036_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_004]
  · intro i; fin_cases i <;> norm_num [tilt_036_004]
  · norm_num [tilt_036_004]
  · norm_num [tilt_036_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_004]

def tilt_036_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2188989/50000000), (1/100000000), (5509457/100000000), (391883/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-3549450629134269724778968448381874415534031429/241859118816782133468343706963700000000000000000), (104770039806584708402083/165229354971900000000000), (-827881158075530571089821427738396472852265031429/120929559408391066734171853481850000000000000000), (104770039806584708402083/165229354971900000000000), (-1652212865521926872454863887028411071288996031429/241859118816782133468343706963700000000000000000)]
    bernstein := [(136693171351029041056758090375588007763461469599630739/4508580753287575864599146148856332288000000000000000000000), (48951824530906276566073988378449870933770073932664039/1352574225986272759379743844656899686400000000000000000000), (47816136787110267776982744469009192169145726893888833/1217316803387645483441769460191209717760000000000000000000), (321232927306151210568299859191426756609739995680177/8115445355917636556278463067941398118400000000000000000), (6021639752150387809842526508786008448543355565411/162308907118352731125569261358827962368000000000000000)]
    reserve := (1894903/62500000000) }

theorem tilt_036_005_valid : tilt_036_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_005]
  · intro i; fin_cases i <;> norm_num [tilt_036_005]
  · norm_num [tilt_036_005]
  · norm_num [tilt_036_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_005]

def tilt_036_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (4381939/100000000), (1/100000000), (5509457/100000000), (384013/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-2547670644268942920322223667599801340481211/170795812295389447343031873140052000000000000), (104799495555822263085917/161911132380900000000000), (-596033240568466930289071053295107414287272451/85397906147694723671515936570026000000000000), (104799495555822263085917/161911132380900000000000), (-1189518810492664917657819882922615027234063691/170795812295389447343031873140052000000000000)]
    bernstein := [(7353769922861727541223933540956024408898948085869/64976830720526180548632014298305003520000000000000000), (2329066490384535360026665907344285307768317332889/19493049216157854164589604289491501056000000000000000), (105692701847050506752783662387721481235970625853327/859643470432561368658401549166575196569600000000000000), (708216538016918092967577947552936662846703813023/5730956469550409124389343661110501310464000000000000), (13910750515553984349627798637269379729912774669/114619129391008182487786873222210026209280000000000)]
    reserve := (113175263/1000000000000) }

theorem tilt_036_006_valid : tilt_036_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_006]
  · intro i; fin_cases i <;> norm_num [tilt_036_006]
  · norm_num [tilt_036_006]
  · norm_num [tilt_036_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_006]

def tilt_036_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4214231/100000000), (2189979/50000000), (1/100000000), (5509457/100000000), (391883/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-15972090724263603542086750503212397965527848173/1088325751202505233670102147886050000000000000000), (104745003954968032360161/165148548697300000000000), (-3725504013721545694262663025687002739548041848173/544162875601252616835051073943025000000000000000), (104745003954968032360161/165148548697300000000000), (-7435035936718827784983239300870793081130555848173/1088325751202505233670102147886050000000000000000)]
    bernstein := [(6703428733347137414791261874575853289673524373831206787/182590762062866900464137764771482042368000000000000000000000), (778509053340552509968945815815319891298322516839195229/18259076206286690046413776477148204236800000000000000000000), (250747490094667725907463488685355120001613060736814921/5477722861886007013924132943144461271040000000000000000000), (240651456267547336071674707775257291552787302742207/5216878916081911441832507564899486924800000000000000000), (31914527295048432534722188505050553234135621622907/730363048251467601856551059085928169472000000000000000)]
    reserve := (18356429/500000000000) }

theorem tilt_036_007_valid : tilt_036_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_007]
  · intro i; fin_cases i <;> norm_num [tilt_036_007]
  · norm_num [tilt_036_007]
  · norm_num [tilt_036_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_007]

def tilt_036_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (843671/20000000), (2189979/50000000), (1/100000000), (5509457/100000000), (384013/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-3184675404923139965526786191631620516187738919/213502611543543490440814935173550000000000000000), (20965014404978235559199/32398063172300000000000), (-745034303320925022744873701690883750033915738919/106751305771771745220407467586775000000000000000), (20965014404978235559199/32398063172300000000000), (-1486883931236926905524220617190135879551643738919/213502611543543490440814935173550000000000000000)]
    bernstein := [(78062211620243648399929785485258242749927005038010489/731016210291861743779487221108703232000000000000000000000), (8263535137957142887744540394886139737840714711956263/73101621029186174377948722110870323200000000000000000000), (125145770863108670271190925592508754683666226529093563/1074593829129036763355846215029793751040000000000000000000), (838441557743660487958503906985288837507259714673547/7163958860860245089038974766865291673600000000000000000), (16444623985486423025550908728730354458789788098321/143279177217204901780779495337305833472000000000000000)]
    reserve := (106785883/1000000000000) }

theorem tilt_036_008_valid : tilt_036_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_008]
  · intro i; fin_cases i <;> norm_num [tilt_036_008]
  · norm_num [tilt_036_008]
  · norm_num [tilt_036_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_008]

def tilt_036_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (4377979/100000000), (1/100000000), (5509457/100000000), (391883/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-798630558137366202029720397893677097656770113/54418314163784018850120153783453750000000000000), (104770039806584708402083/165229354971900000000000), (-186273307098941132789507118570750812257112632613/27209157081892009425060076891726875000000000000), (104770039806584708402083/165229354971900000000000), (-371747983639744899376984516743607947416568495113/54418314163784018850120153783453750000000000000)]
    bernstein := [(30681395095413036658875900439541479111522724776763183/1014430901201848735107263828864689766400000000000000000000), (10991788809392399182517927768405164145957836790643283/304329270360554620532179148659406929920000000000000000000), (10738494992159120451525077786340787472427390751797301/273896343324499158478961233793466236928000000000000000000), (72143160500490776390578906659133784287370212981669/1825975622163327723193074891956441579520000000000000000), (1352183764393513478935725708730991332660858338367/36519512443266554463861497839128831590400000000000000)]
    reserve := (30244933/1000000000000) }

theorem tilt_036_009_valid : tilt_036_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_009]
  · intro i; fin_cases i <;> norm_num [tilt_036_009]
  · norm_num [tilt_036_009]
  · norm_num [tilt_036_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_009]

def tilt_036_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (219097/5000000), (1/100000000), (5509457/100000000), (384013/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-6346323302339909253242624581105499628757973599/426989628181530388082949743359800000000000000000), (104799495555822263085917/161911132380900000000000), (-1490060586710411158516762293897566037689683973599/213494814090765194041474871679900000000000000000), (104799495555822263085917/161911132380900000000000), (-2973774850118482407780281963214026575750609973599/426989628181530388082949743359800000000000000000)]
    bernstein := [(27114938410618637299218812935257960710773959390462841/162442113872136565338582171462402048000000000000000000000), (8442005435238810055444155815570005069939580060455541/48732634161640969601574651438720614400000000000000000000), (379752870699384041189522235446817023766852469752459923/2149109166528366759429442128447579095040000000000000000000), (2540737784050913350951309953997816866777567568796387/14327394443522445062862947522983860633600000000000000000), (50181930749951970958781935605655354023790785356441/286547888870448901257258950459677212672000000000000000)]
    reserve := (8346031/50000000000) }

theorem tilt_036_010_valid : tilt_036_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_010]
  · intro i; fin_cases i <;> norm_num [tilt_036_010]
  · norm_num [tilt_036_010]
  · norm_num [tilt_036_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_010]

def tilt_036_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(183/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5509457/100000000), (391883/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1775102990221341565501814752871707321298555687/120984251443761873602578606615350000000000000000), (104770039806584708402083/165229354971900000000000), (-414127364317654125756540307854821255781769055687/60492125721880936801289303307675000000000000000), (104770039806584708402083/165229354971900000000000), (-826479625645086909947578800956770804242239555687/120984251443761873602578606615350000000000000000)]
    bernstein := [(76332038024792103644071785523047286278569067317499617/2255309910078116451105732711294173184000000000000000000000), (26873512942618147721364246928943651822348872547379517/676592973023434935331719813388251955200000000000000000000), (26066912644782903804976920997942887793465131874274299/608933675721091441798547832049426759680000000000000000000), (175010349662588719955550438639689585534509540598731/4059557838140609611990318880329511731200000000000000000), (3298627394826467147183112749568903349604413178833/81191156762812192239806377606590234624000000000000000)]
    reserve := (8461369/250000000000) }

theorem tilt_036_011_valid : tilt_036_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_011]
  · intro i; fin_cases i <;> norm_num [tilt_036_011]
  · norm_num [tilt_036_011]
  · norm_num [tilt_036_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_011]

def tilt_036_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4337/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1903/50000000), (5509457/100000000), (384013/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-614688968102737254655428585489146947293364256677/41019885453022896158395409823632100000000000000000), (104799495555822263085917/161911132380900000000000), (-143151615190911455839884072303154731230360341256677/20509942726511448079197704911816050000000000000000), (104799495555822263085917/161911132380900000000000), (-285688541413720174425112716020820315513427318256677/41019885453022896158395409823632100000000000000000)]
    bernstein := [(690029452861344880380486998900011801998709071753665443/15605430352395078952266893515183620096000000000000000000000), (236511343737439842415844377368990447011121761773967543/4681629105718523685680068054555086028800000000000000000000), (11145045649608953586087116622378683403424834666539178529/206459843562186894538491001205879293870080000000000000000000), (75157698188845502886453315612278628832932746297107601/1376398957081245963589940008039195292467200000000000000000), (1442113042523484431795354940287513995589350951178243/27527979141624919271798800160783905849344000000000000000)]
    reserve := (8843453/200000000000) }

theorem tilt_036_012_valid : tilt_036_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_012]
  · intro i; fin_cases i <;> norm_num [tilt_036_012]
  · norm_num [tilt_036_012]
  · norm_num [tilt_036_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_012]

def tilt_036_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5506717/100000000), (391883/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-1767444080880183680229037853148158541843266827/120924082746745832360461449628350000000000000000), (104770039806584708402083/165229354971900000000000), (-413914631624083929360088762254098798804503766827/60462041373372916180230724814175000000000000000), (104770039806584708402083/165229354971900000000000), (-826061819167287675039948486655049439067164266827/120924082746745832360461449628350000000000000000)]
    bernstein := [(203129037039575830806079218443176850749503732029275357/2254188284271142362901390666764386304000000000000000000000), (64913324804007416526169903942178284270860635534733257/676256485281342708870417200029315891200000000000000000000), (60304255534067247390956250765343765393032139296040079/608630836753208437983375480026384302080000000000000000000), (403275193372284041094194335053310394195224108299551/4057538911688056253222503200175895347200000000000000000), (7864358310780478729162548060487082424025431662093/81150778233761125064450064003517906944000000000000000)]
    reserve := (11263979/125000000000) }

theorem tilt_036_013_valid : tilt_036_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_013]
  · intro i; fin_cases i <;> norm_num [tilt_036_013]
  · norm_num [tilt_036_013]
  · norm_num [tilt_036_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_013]

def tilt_036_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5512199/100000000), (384013/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-1352183987524104070961905648704328457922739/90613892764403242803654173550000000000000000), (104799495555822263085917/161911132380900000000000), (-316219609995156562099636690357689216721422739/45306946382201621401827086775000000000000000), (104799495555822263085917/161911132380900000000000), (-631087036002789020128311475066674104984922739/90613892764403242803654173550000000000000000)]
    bernstein := [(25854105878761686016893567419689448118906201644707/241309341509401637399579628404736000000000000000000000), (8212755757646281508691321746093781845289047047607/72392802452820491219873888521420800000000000000000000), (53321633094937362383987021071293233836653396151703/456074655452769094685205497684951040000000000000000000), (357385387042894126323675300340493118843804791207/3040497703018460631234703317899673600000000000000000), (7013146627377057180493988734072328245692081701/60809954060369212624694066357993472000000000000000)]
    reserve := (26785231/250000000000) }

theorem tilt_036_014_valid : tilt_036_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_014]
  · intro i; fin_cases i <;> norm_num [tilt_036_014]
  · norm_num [tilt_036_014]
  · norm_num [tilt_036_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_014]

def tilt_036_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(183/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5509457/100000000), (391883/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1775102990221341565501814752871707321298555687/120984251443761873602578606615350000000000000000), (104770039806584708402083/165229354971900000000000), (-414127364317654125756540307854821255781769055687/60492125721880936801289303307675000000000000000), (104770039806584708402083/165229354971900000000000), (-826479625645086909947578800956770804242239555687/120984251443761873602578606615350000000000000000)]
    bernstein := [(76332038024792103644071785523047286278569067317499617/2255309910078116451105732711294173184000000000000000000000), (26873512942618147721364246928943651822348872547379517/676592973023434935331719813388251955200000000000000000000), (26066912644782903804976920997942887793465131874274299/608933675721091441798547832049426759680000000000000000000), (175010349662588719955550438639689585534509540598731/4059557838140609611990318880329511731200000000000000000), (3298627394826467147183112749568903349604413178833/81191156762812192239806377606590234624000000000000000)]
    reserve := (8461369/250000000000) }

theorem tilt_036_015_valid : tilt_036_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_015]
  · intro i; fin_cases i <;> norm_num [tilt_036_015]
  · norm_num [tilt_036_015]
  · norm_num [tilt_036_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_015]

def tilt_036_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4337/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1903/50000000), (5509457/100000000), (384013/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-614688968102737254655428585489146947293364256677/41019885453022896158395409823632100000000000000000), (104799495555822263085917/161911132380900000000000), (-143151615190911455839884072303154731230360341256677/20509942726511448079197704911816050000000000000000), (104799495555822263085917/161911132380900000000000), (-285688541413720174425112716020820315513427318256677/41019885453022896158395409823632100000000000000000)]
    bernstein := [(690029452861344880380486998900011801998709071753665443/15605430352395078952266893515183620096000000000000000000000), (236511343737439842415844377368990447011121761773967543/4681629105718523685680068054555086028800000000000000000000), (11145045649608953586087116622378683403424834666539178529/206459843562186894538491001205879293870080000000000000000000), (75157698188845502886453315612278628832932746297107601/1376398957081245963589940008039195292467200000000000000000), (1442113042523484431795354940287513995589350951178243/27527979141624919271798800160783905849344000000000000000)]
    reserve := (8843453/200000000000) }

theorem tilt_036_016_valid : tilt_036_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_016]
  · intro i; fin_cases i <;> norm_num [tilt_036_016]
  · norm_num [tilt_036_016]
  · norm_num [tilt_036_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_016]

def tilt_036_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5506717/100000000), (391883/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1767446646630283587350818445892035600876786827/120924082746745832360461449628350000000000000000), (104770039806584708402083/165229354971900000000000), (-413914634189834029267210542846842675863537286827/60462041373372916180230724814175000000000000000), (104770039806584708402083/165229354971900000000000), (-826061821733037774947070267247793316126197786827/120924082746745832360461449628350000000000000000)]
    bernstein := [(203081011382094146276664452975928865463200243095595357/2254188284271142362901390666764386304000000000000000000000), (64898916088776842303232469245346378695782371105053257/676256485281342708870417200029315891200000000000000000000), (60291286763598222328370627491371057536741204621080079/608630836753208437983375480026384302080000000000000000000), (403188728653571962351829654969456725990980952059551/4057538911688056253222503200175895347200000000000000000), (7862628890017387232890435546811445676012577342093/81150778233761125064450064003517906944000000000000000)]
    reserve := (90090527/1000000000000) }

theorem tilt_036_017_valid : tilt_036_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_017]
  · intro i; fin_cases i <;> norm_num [tilt_036_017]
  · norm_num [tilt_036_017]
  · norm_num [tilt_036_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_017]

def tilt_036_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (27561/500000), (384013/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-23576156022015180355190825767981099386135283/1581514761959767450272469042800000000000000000), (104799495555822263085917/161911132380900000000000), (-5519063294909917136013106279810145276022135283/790757380979883725136234521400000000000000000), (104799495555822263085917/161911132380900000000000), (-11014550433797819091671021733852309452658135283/1581514761959767450272469042800000000000000000)]
    bernstein := [(73617964082757687091946638488341027187973570280197/601664733981578272630169432752128000000000000000000000), (23223849980009402375768348283296088773335304086097/180499420194473481789050829825638400000000000000000000), (1051778910001680054985137324069463244027861192314391/7960024430576280546897141595310653440000000000000000000), (7045215822491920259495360241932558383351268771879/53066829537175203645980943968737689600000000000000000), (138556956627644425428120274744637576025835711397/1061336590743504072919618879374753792000000000000000)]
    reserve := (191183/1562500000) }

theorem tilt_036_018_valid : tilt_036_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_018]
  · intro i; fin_cases i <;> norm_num [tilt_036_018]
  · norm_num [tilt_036_018]
  · norm_num [tilt_036_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_018]

def tilt_036_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5509457/100000000), (96987/25000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-6661088777977937623389828868472902208822953/453672033480931995669598483275000000000000000), (67525008300857/105407325000000), (-6271697301582697589374202198467590861911553937/907344066961863991339196966550000000000000000), (67525008300857/105407325000000), (-6258375124026741714127422540730645057493908031/907344066961863991339196966550000000000000000)]
    bernstein := [(3101768007892592443727786912767528124952388909378121/16914119330819617717022040860393472000000000000000000000), (961403539246169491413101788345481084543300670626821/5074235799245885315106612258118041600000000000000000000), (880208494711679390666606790181463997320339967833587/4566812219321296783595951032306237440000000000000000000), (5882070903557345485675184075798905489862369857603/30445414795475311890639673548708249600000000000000000), (116208902035771658117850966955250986492635705529/608908295909506237812793470974164992000000000000000)]
    reserve := (91691679/500000000000) }

theorem tilt_036_019_valid : tilt_036_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_019]
  · intro i; fin_cases i <;> norm_num [tilt_036_019]
  · norm_num [tilt_036_019]
  · norm_num [tilt_036_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_019]

def tilt_036_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(29/640), (3/64)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1092359/20000000), (1/100000000), (4216293/100000000), (2189979/50000000), (1/100000000), (5509457/100000000), (96987/25000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-6731303430741129080414774227977935147072953/453672033480931995669598483275000000000000000), (67525008300857/105407325000000), (-6271404088574829070805996342523674185358553937/907344066961863991339196966550000000000000000), (67525008300857/105407325000000), (-6257941481713346812645166794067718315064408031/907344066961863991339196966550000000000000000)]
    bernstein := [(495232778103165632608617398608201827048115574878121/16914119330819617717022040860393472000000000000000000000), (179501371202631917868435565931932263362175026126821/5074235799245885315106612258118041600000000000000000000), (176549715717492678967775441565555666623759648333587/4566812219321296783595951032306237440000000000000000000), (1191370937351444733178472578521160965938439157603/30445414795475311890639673548708249600000000000000000), (22402155547904866429609047746013388345306005529/608908295909506237812793470974164992000000000000000)]
    reserve := (7319813/250000000000) }

theorem tilt_036_020_valid : tilt_036_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_036_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_036_020]
  · intro i; fin_cases i <;> norm_num [tilt_036_020]
  · norm_num [tilt_036_020]
  · norm_num [tilt_036_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_036_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_036_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_036_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_036_020]

def tiltBundle036_row : Alternative → Row
  | .zero => tilt_036_000
  | (.spike 0 false false) => tilt_036_001
  | (.spike 0 false true) => tilt_036_002
  | (.spike 0 true false) => tilt_036_003
  | (.spike 0 true true) => tilt_036_004
  | (.spike 1 false false) => tilt_036_005
  | (.spike 1 false true) => tilt_036_006
  | (.spike 1 true false) => tilt_036_007
  | (.spike 1 true true) => tilt_036_008
  | (.spike 2 false false) => tilt_036_009
  | (.spike 2 false true) => tilt_036_010
  | (.spike 2 true false) => tilt_036_011
  | (.spike 2 true true) => tilt_036_012
  | (.spike 3 false false) => tilt_036_013
  | (.spike 3 false true) => tilt_036_014
  | (.spike 3 true false) => tilt_036_015
  | (.spike 3 true true) => tilt_036_016
  | (.spike 4 false false) => tilt_036_017
  | (.spike 4 false true) => tilt_036_018
  | (.spike 4 true false) => tilt_036_019
  | (.spike 4 true true) => tilt_036_020

def tiltBundle036 : TiltBundle where
  interval := ⟨(29/640), (3/64)⟩
  lambda := ![(7365991/50000000), (7365991/50000000), (1856081/20000000), (14640253/100000000), (14640253/100000000), (16157763/100000000), (15817363/100000000)]
  row := tiltBundle036_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_036_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_036_001_valid | exact tilt_036_002_valid | exact tilt_036_003_valid | exact tilt_036_004_valid | exact tilt_036_005_valid | exact tilt_036_006_valid | exact tilt_036_007_valid | exact tilt_036_008_valid | exact tilt_036_009_valid | exact tilt_036_010_valid | exact tilt_036_011_valid | exact tilt_036_012_valid | exact tilt_036_013_valid | exact tilt_036_014_valid | exact tilt_036_015_valid | exact tilt_036_016_valid | exact tilt_036_017_valid | exact tilt_036_018_valid | exact tilt_036_019_valid | exact tilt_036_020_valid
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
