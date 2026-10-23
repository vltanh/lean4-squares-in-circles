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

def tilt_044_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (73231/10000000)]
    alternative := .zero
    polynomial := [(-12690875811617375303183682070807080422086985053/400233786911336453385925257689550000000000000000), (27850252576419/42171830000000), (-690344009887639253713931914701604046278711985053/200116893455668226692962628844775000000000000000), (27850252576419/42171830000000), (-1367997143963661132124680147332401012135336985053/400233786911336453385925257689550000000000000000)]
    bernstein := [(98569761607887408451981481708970881293037232659251/2354316393596096784623089751115000000000000000000000000), (465140648444456492943569016262239754143155976090641/4708632787192193569246179502230000000000000000000000000), (67901421633258807919541636859636925298388466922105681/480280544293603744063110309227460000000000000000000000000), (54313934442363622116310801871270764723237335330513257/320187029529069162708740206151640000000000000000000000000), (117524272072133506975383777234741729539949535640267987/640374059058138325417480412303280000000000000000000000000)]
    reserve := (20933839/500000000000) }

theorem tilt_044_000_valid : tilt_044_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_000]
  · intro i; fin_cases i <;> norm_num [tilt_044_000]
  · norm_num [tilt_044_000]
  · norm_num [tilt_044_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_000]

def tilt_044_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![(7591/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (46001/6250000)]
    alternative := (.spike 0 false false)
    polynomial := [(-126860705841228448764283868667579248037625250797/4022592493716243272320399345408800000000000000000), (40806061626424625735149/62078283258560000000000), (-6907060247690126381248390907682975137349979250797/2011296246858121636160199672704400000000000000000), (40806061626424625735149/62078283258560000000000), (-13687259789539024313732497946698371026662333250797/4022592493716243272320399345408800000000000000000)]
    bernstein := [(1474749546178867209371812024265810935338852488257699/23662308786566136896002349090640000000000000000000000000), (5625673667208801046788857809147574608274365979511809/47324617573132273792004698181280000000000000000000000000), (777961557131536779358333891610759771201149642852924769/4827110992459491926784479214490560000000000000000000000000), (608794543595572114487594326632799091541455633476730393/3218073994972994617856319476327040000000000000000000000000), (1305884802853429030513775525254347876840508478705524163/6436147989945989235712638952654080000000000000000000000000)]
    reserve := (62324837/1000000000000) }

theorem tilt_044_001_valid : tilt_044_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_001]
  · intro i; fin_cases i <;> norm_num [tilt_044_001]
  · norm_num [tilt_044_001]
  · norm_num [tilt_044_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_001]

def tilt_044_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (219471/100000000), 0], ![0, 0, (4497/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (3947/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (182151/25000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-166881761060453787160799423813228839016110283936233/5239094188694295811478774541894847800000000000000000), (40774012230524965824851/61453128050640000000000), (-3025906629860103033355462055948099665290901186645411/873182364782382635246462423649141300000000000000000), (40774012230524965824851/61453128050640000000000), (-17988558018100164412971972911875369152729296835936233/5239094188694295811478774541894847800000000000000000)]
    bernstein := [(1555841346730885358507457105740616046960903492863230311/30818201109966445949875144364087340000000000000000000000000), (6643496006365125795020860074911663788338555555272285101/61636402219932891899750288728174680000000000000000000000000), (315808634601343353620835504164927718584463949433275780847/2095637675477718324591509816757939120000000000000000000000000), (751098051623049863906328846811361545734752435465296920677/4191275350955436649183019633515878240000000000000000000000000), (1620232175145967939163485250550212780564540440036245139207/8382550701910873298366039267031756480000000000000000000000000)]
    reserve := (10096899/200000000000) }

theorem tilt_044_002_valid : tilt_044_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_002]
  · intro i; fin_cases i <;> norm_num [tilt_044_002]
  · norm_num [tilt_044_002]
  · norm_num [tilt_044_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_002]

def tilt_044_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (113531/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5344229/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (46001/6250000)]
    alternative := (.spike 0 true false)
    polynomial := [(-126603532407316384702311821446944106939167602261/4020552211086799922982051882247200000000000000000), (40806061626424625735149/62078283258560000000000), (-6903364117073501021641751938143614251259793602261/2010276105543399961491025941123600000000000000000), (40806061626424625735149/62078283258560000000000), (-13680124701739685658581192054840284395580419602261/4020552211086799922982051882247200000000000000000)]
    bernstein := [(2626739287018776432741398845016695637670448586867387/23650307124039999546953246366160000000000000000000000000), (7929324905397113641268625692744450584536519818967817/47300614248079999093906492732320000000000000000000000000), (1012937387179112920162459236733917734783191944487528297/4824662653304159907578462258696640000000000000000000000000), (765471986541733889326065505616711595544614581630666209/3216441768869439938385641505797760000000000000000000000000), (1619342777243188644767663460878735950348490282616064219/6432883537738879876771283011595520000000000000000000000000)]
    reserve := (111065757/1000000000000) }

theorem tilt_044_003_valid : tilt_044_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_003]
  · intro i; fin_cases i <;> norm_num [tilt_044_003]
  · norm_num [tilt_044_003]
  · norm_num [tilt_044_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_003]

def tilt_044_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (211879/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2674827/50000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (182151/25000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-260507426929607927853654321340057656471196441/8197744290844331018909990123800000000000000000), (40774012230524965824851/61453128050640000000000), (-127831707915555256570700925632117437807004767969/36889849308799489585094955557100000000000000000), (40774012230524965824851/61453128050640000000000), (-253318848988744041790718962372174356705768767969/73779698617598979170189911114200000000000000000)]
    bernstein := [(6121240880273998013432661476758311930477440219447/48222025240260770699470530140000000000000000000000000), (159948824056640591013798727186291392268456196799493/867996454324693872590469542520000000000000000000000000), (20117174388412558285542538027705409575391371788885413/88535638341118775004227893337040000000000000000000000000), (1677347939298530746422580967031503301514742822540629/6558195432675464815127992099040000000000000000000000000), (31858765815246493088667086979900758719805200544791951/118047517788158366672303857782720000000000000000000000000)]
    reserve := (126938693/1000000000000) }

theorem tilt_044_004_valid : tilt_044_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_004]
  · intro i; fin_cases i <;> norm_num [tilt_044_004]
  · norm_num [tilt_044_004]
  · norm_num [tilt_044_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_004]

def tilt_044_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (451501/10000000), (1/100000000), (1073147/20000000), (46001/6250000)]
    alternative := (.spike 1 false false)
    polynomial := [(-12679791995836703275445725857478067336918853753/402071260323860608050112588272800000000000000000), (40806061626424625735149/62078283258560000000000), (-690382885037692182775442917037986683205392853753/201035630161930304025056294136400000000000000000), (40806061626424625735149/62078283258560000000000), (-1368085978079547662275440108218495299073866853753/402071260323860608050112588272800000000000000000)]
    bernstein := [(2541468638452062116474902683714964488203952942666567/40207126032386060805011258827280000000000000000000000000), (9630339676130276580338362468509018694206399423677197/80414252064772121610022517654560000000000000000000000000), (78186976192584804689801245008804731888088107214135581/482485512388632729660135105927360000000000000000000000000), (61135919966225561844920273435875748941894706521293557/321657008259088486440090070618240000000000000000000000000), (131097553524083834400519108029309084338495255065415287/643314016518176972880180141236480000000000000000000000000)]
    reserve := (987647/15625000000) }

theorem tilt_044_005_valid : tilt_044_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_005]
  · intro i; fin_cases i <;> norm_num [tilt_044_005]
  · norm_num [tilt_044_005]
  · norm_num [tilt_044_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_005]

def tilt_044_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4519233/100000000), (1/100000000), (1073147/20000000), (182151/25000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-14068273928034825772780453914549997513099535921/442660565025546538568220478553400000000000000000), (40774012230524965824851/61453128050640000000000), (-766961140281490900125186724873297796517127535921/221330282512773269284110239276700000000000000000), (40774012230524965824851/61453128050640000000000), (-1519854006634946974477592995832045595521155535921/442660565025546538568220478553400000000000000000)]
    bernstein := [(5473443151730118789462988748738542395804953486802319/44266056502554653856822047855340000000000000000000000000), (16022735960399395962310569032841801869390544292528229/88532113005109307713644095710680000000000000000000000000), (118949078568004198339933836176417986646558376389272117/531192678030655846281864574264080000000000000000000000000), (89406534746226511913626544410085739357406718075300749/354128452020437230854576382842720000000000000000000000000), (188810589876870643805097577347467171128809373904759359/708256904040874461709152765685440000000000000000000000000)]
    reserve := (123648763/1000000000000) }

theorem tilt_044_006_valid : tilt_044_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_006]
  · intro i; fin_cases i <;> norm_num [tilt_044_006]
  · norm_num [tilt_044_006]
  · norm_num [tilt_044_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_006]

def tilt_044_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4214887/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (46001/6250000)]
    alternative := (.spike 1 true false)
    polynomial := [(-126789599824095158122803609004610549755131372997/4020402436427865581678744089543200000000000000000), (40796199360276078025861/62044485403840000000000), (-6904032925508340550730756988355572647546253372997/2010201218213932790839372044771600000000000000000), (40796199360276078025861/62044485403840000000000), (-13681276251192585943338710367706534745337375372997/4020402436427865581678744089543200000000000000000)]
    bernstein := [(1842748084840465254434974065249378645964811586625099/23649426096634503421639671114960000000000000000000000000), (6368327989810052320778895406546117701579907870065209/47298852193269006843279342229920000000000000000000000000), (854422201543033244574001469998240108210500507001174169/4824482923713438698014492907451840000000000000000000000000), (660262189741179851241207671780134152620235784599202193/3216321949142292465342995271634560000000000000000000000000), (1409849171688983574049112430958041686700178013162297963/6432643898284584930685990543269120000000000000000000000000)]
    reserve := (77919357/1000000000000) }

theorem tilt_044_007_valid : tilt_044_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_007]
  · intro i; fin_cases i <;> norm_num [tilt_044_007]
  · norm_num [tilt_044_007]
  · norm_num [tilt_044_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_007]

def tilt_044_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4219479/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (182151/25000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-4689731920246034624005760307960547688101171123/147564860999004593504106836581800000000000000000), (4531553495491855175507/6831842838480000000000), (-9468383405832193372814002278398373168626117449/2732682611092677657483459936700000000000000000), (4531553495491855175507/6831842838480000000000), (-506602971994692407507950362725551603417709171123/147564860999004593504106836581800000000000000000)]
    bernstein := [(94573036721029886837757687511757653093568374058941/868028594111791726494746097540000000000000000000000000), (32042596255884004678493947621928879340649746037159/192895243135953716998832466120000000000000000000000000), (12329958885459200003619167741329114819687861000462357/59025944399601837401642734632720000000000000000000000000), (94307633482585433131074909251029699930494564665071/397481107068025841088503263520000000000000000000000000), (59312102581318152026202727191950797421113562777839517/236103777598407349606570938530880000000000000000000000000)]
    reserve := (54475761/500000000000) }

theorem tilt_044_008_valid : tilt_044_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_008]
  · intro i; fin_cases i <;> norm_num [tilt_044_008]
  · norm_num [tilt_044_008]
  · norm_num [tilt_044_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_008]

def tilt_044_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4515011/100000000), (1/100000000), (1073147/20000000), (46001/6250000)]
    alternative := (.spike 2 false false)
    polynomial := [(-126798200499650595240034629827039023284103482087/4020713493759912398450827101800800000000000000000), (40806061626424625735149/62078283258560000000000), (-6903830631918409247718682114880448398326317482087/2010356746879956199225413550900400000000000000000), (40806061626424625735149/62078283258560000000000), (-13680863063337167900197329599933857773368531482087/4020713493759912398450827101800800000000000000000)]
    bernstein := [(25389035611441453602921757806665123042802219515087193/402071349375991239845082710180080000000000000000000000000), (96252082381658782715392019809635151673496929879402963/804142698751982479690165420360160000000000000000000000000), (781561780824245138015497357675331873604967262775772099/4824856192511894878140992522160960000000000000000000000000), (611153803815235592813058856453098320481147740898567403/3216570795007929918760661681440640000000000000000000000000), (1310564569494878090458388301894214526018736700350380073/6433141590015859837521323362881280000000000000000000000000)]
    reserve := (63145597/1000000000000) }

theorem tilt_044_009_valid : tilt_044_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_009]
  · intro i; fin_cases i <;> norm_num [tilt_044_009]
  · norm_num [tilt_044_009]
  · norm_num [tilt_044_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_009]

def tilt_044_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (219471/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (2259617/50000000), (1/100000000), (1073147/20000000), (182151/25000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-63216533570687806553771413519506482641119519133/1991972983391644895396887011089400000000000000000), (40774012230524965824851/61453128050640000000000), (-1150411727283312334734313754370777465124755839711/331995497231940815899481168514900000000000000000), (40774012230524965824851/61453128050640000000000), (-6839253830129186201852111112705158308107415519133/1991972983391644895396887011089400000000000000000)]
    bernstein := [(33849361433238481259840382128589908667733617733508387/199197298339164489539688701108940000000000000000000000000), (90548281687059372436084603917607708648660908269098817/398394596678328979079377402217880000000000000000000000000), (215332335499414540050510199115226653208702675713201947/796789193356657958158754804435760000000000000000000000000), (476181012673056156404909361847827468705336561990920777/1593578386713315916317509608871520000000000000000000000000), (997420441198754378638089475212075505548931352270028307/3187156773426631832635019217743040000000000000000000000000)]
    reserve := (169928817/1000000000000) }

theorem tilt_044_010_valid : tilt_044_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_010]
  · intro i; fin_cases i <;> norm_num [tilt_044_010]
  · norm_num [tilt_044_010]
  · norm_num [tilt_044_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_010]

def tilt_044_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7357/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (46001/6250000)]
    alternative := (.spike 2 true false)
    polynomial := [(-126881101553332450292871579374104440560340770797/4022592493716243272320399345408800000000000000000), (40806061626424625735149/62078283258560000000000), (-6907080643402230382776978618389500329872694770797/2011296246858121636160199672704400000000000000000), (40806061626424625735149/62078283258560000000000), (-13687280185251128315261085657404896219185048770797/4022592493716243272320399345408800000000000000000)]
    bernstein := [(1352823306162646639424034026204894703192224316097699/23662308786566136896002349090640000000000000000000000000), (5381712335260860850735229200985017191487376904951809/47324617573132273792004698181280000000000000000000000000), (753066189464186894345083043229258031987505843691964769/4827110992459491926784479214490560000000000000000000000000), (592189951152484738007121300909276359840039670511610393/3218073994972994617856319476327040000000000000000000000000), (1272659977331865915044618230562607210824899451823604163/6436147989945989235712638952654080000000000000000000000000)]
    reserve := (2286883/40000000000) }

theorem tilt_044_011_valid : tilt_044_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_011]
  · intro i; fin_cases i <;> norm_num [tilt_044_011]
  · norm_num [tilt_044_011]
  · norm_num [tilt_044_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_011]

def tilt_044_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (219471/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2179/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (153/4000000), (1073147/20000000), (182151/25000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-2818339261894173260081808106526229498204854317/88490738766899684342180129075160000000000000000), (40774012230524965824851/61453128050640000000000), (-459979625260719525754686100480261240146836162951/132736108150349526513270193612740000000000000000), (40774012230524965824851/61453128050640000000000), (-911504232735756531729126776640943791799057762951/265472216300699053026540387225480000000000000000)]
    bernstein := [(28498754513524495320525251311750351398979107581539/520533757452351084365765465148000000000000000000000000), (349960383537626551091002321211880701520905127119747/3123202544714106506194592790888000000000000000000000000), (49367177993035242142585345386172776008461990751619427/318566659560838863631848464670576000000000000000000000000), (12988709851092423263944858499980771197508305977237273/70792591013519747473744103260128000000000000000000000000), (83914165939136341049418769452254474614517055749582729/424755546081118484842464619560768000000000000000000000000)]
    reserve := (54749099/1000000000000) }

theorem tilt_044_012_valid : tilt_044_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_012]
  · intro i; fin_cases i <;> norm_num [tilt_044_012]
  · norm_num [tilt_044_012]
  · norm_num [tilt_044_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_012]

def tilt_044_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (219471/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1072611/20000000), (46001/6250000)]
    alternative := (.spike 3 false false)
    polynomial := [(-42204921827447988682155741641439417174053199767/1340194449060403160848997034664800000000000000000), (40806061626424625735149/62078283258560000000000), (-2301142610321223231110798023088853052097387199767/670097224530201580424498517332400000000000000000), (40806061626424625735149/62078283258560000000000), (-4560080298814998473539440304536266687020721199767/1340194449060403160848997034664800000000000000000)]
    bernstein := [(855156360725137572798680534783681662965484243281689/7883496759178842122641159027440000000000000000000000000), (2602250166604833616600215049915166335028581130906899/15766993518357684245282318054880000000000000000000000000), (333476897494739464390286500043929441048011134201329459/1608233338872483793018796441597760000000000000000000000000), (252377009166005685693579522546745522314667337855663323/1072155559248322528679197627731840000000000000000000000000), (534217893805623023057146522274913187795499029554204793/2144311118496645057358395255463680000000000000000000000000)]
    reserve := (21694849/200000000000) }

theorem tilt_044_013_valid : tilt_044_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_013]
  · intro i; fin_cases i <;> norm_num [tilt_044_013]
  · norm_num [tilt_044_013]
  · norm_num [tilt_044_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_013]

def tilt_044_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (5368417/100000000), (182151/25000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-211024267270673133829408464442853334430271569681/6640122737222160189384962479361400000000000000000), (40774012230524965824851/61453128050640000000000), (-3834927228914988581577072747211074666921886523227/1106687122870360031564160413226900000000000000000), (40774012230524965824851/61453128050640000000000), (-22798539106219258355633028018823594667101047569681/6640122737222160189384962479361400000000000000000)]
    bernstein := [(4869425260176214797857395762687809440759567127182527/39059545513071530525793896937420000000000000000000000000), (14217721413227685754454436086876440085215902812477557/78119091026143061051587793874840000000000000000000000000), (597470752375758434563190686035684648418539959139647879/2656049094888864075753984991744560000000000000000000000000), (1346556137150612622390353666894269741520312977773662189/5312098189777728151507969983489120000000000000000000000000), (2843085019675522955753898821079406784993726573184322399/10624196379555456303015939966978240000000000000000000000000)]
    reserve := (24933343/200000000000) }

theorem tilt_044_014_valid : tilt_044_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_014]
  · intro i; fin_cases i <;> norm_num [tilt_044_014]
  · norm_num [tilt_044_014]
  · norm_num [tilt_044_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_014]

def tilt_044_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7357/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (46001/6250000)]
    alternative := (.spike 3 true false)
    polynomial := [(-126881101553332450292871579374104440560340770797/4022592493716243272320399345408800000000000000000), (40806061626424625735149/62078283258560000000000), (-6907080643402230382776978618389500329872694770797/2011296246858121636160199672704400000000000000000), (40806061626424625735149/62078283258560000000000), (-13687280185251128315261085657404896219185048770797/4022592493716243272320399345408800000000000000000)]
    bernstein := [(1352823306162646639424034026204894703192224316097699/23662308786566136896002349090640000000000000000000000000), (5381712335260860850735229200985017191487376904951809/47324617573132273792004698181280000000000000000000000000), (753066189464186894345083043229258031987505843691964769/4827110992459491926784479214490560000000000000000000000000), (592189951152484738007121300909276359840039670511610393/3218073994972994617856319476327040000000000000000000000000), (1272659977331865915044618230562607210824899451823604163/6436147989945989235712638952654080000000000000000000000000)]
    reserve := (2286883/40000000000) }

theorem tilt_044_015_valid : tilt_044_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_015]
  · intro i; fin_cases i <;> norm_num [tilt_044_015]
  · norm_num [tilt_044_015]
  · norm_num [tilt_044_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_015]

def tilt_044_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (219471/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2179/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (153/4000000), (1073147/20000000), (182151/25000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-2818339261894173260081808106526229498204854317/88490738766899684342180129075160000000000000000), (40774012230524965824851/61453128050640000000000), (-459979625260719525754686100480261240146836162951/132736108150349526513270193612740000000000000000), (40774012230524965824851/61453128050640000000000), (-911504232735756531729126776640943791799057762951/265472216300699053026540387225480000000000000000)]
    bernstein := [(28498754513524495320525251311750351398979107581539/520533757452351084365765465148000000000000000000000000), (349960383537626551091002321211880701520905127119747/3123202544714106506194592790888000000000000000000000000), (49367177993035242142585345386172776008461990751619427/318566659560838863631848464670576000000000000000000000000), (12988709851092423263944858499980771197508305977237273/70792591013519747473744103260128000000000000000000000000), (83914165939136341049418769452254474614517055749582729/424755546081118484842464619560768000000000000000000000000)]
    reserve := (54749099/1000000000000) }

theorem tilt_044_016_valid : tilt_044_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_016]
  · intro i; fin_cases i <;> norm_num [tilt_044_016]
  · norm_num [tilt_044_016]
  · norm_num [tilt_044_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_016]

def tilt_044_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1072611/20000000), (46001/6250000)]
    alternative := (.spike 4 false false)
    polynomial := [(-42204933045498049744674421591340901834617307367/1340194449060403160848997034664800000000000000000), (40806061626424625735149/62078283258560000000000), (-2301142621539273292173316703038754536757951307367/670097224530201580424498517332400000000000000000), (40806061626424625735149/62078283258560000000000), (-4560080310033048534601958984486168171681285307367/1340194449060403160848997034664800000000000000000)]
    bernstein := [(855089298851676889046948677834259613119450394930889/7883496759178842122641159027440000000000000000000000000), (2602115982987179073206089141123698011703082791944099/15766993518357684245282318054880000000000000000000000000), (333463204544017430247774734629425160350822219962334659/1608233338872483793018796441597760000000000000000000000000), (252367876307671528820172581897955550986268622073407723/1072155559248322528679197627731840000000000000000000000000), (534199619486292057533990628589631742513386066999665193/2144311118496645057358395255463680000000000000000000000000)]
    reserve := (54232869/500000000000) }

theorem tilt_044_017_valid : tilt_044_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_017]
  · intro i; fin_cases i <;> norm_num [tilt_044_017]
  · norm_num [tilt_044_017]
  · norm_num [tilt_044_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_017]

def tilt_044_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (5368417/100000000), (182151/25000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-210984611475639132883934992056914489803674879181/6640122737222160189384962479361400000000000000000), (40774012230524965824851/61453128050640000000000), (-3834914010316643914595248256415761718713020959727/1106687122870360031564160413226900000000000000000), (40774012230524965824851/61453128050640000000000), (-22798499450424224354687554546437655822474450879181/6640122737222160189384962479361400000000000000000)]
    bernstein := [(5106488911530708571929014310418958600427260626969027/39059545513071530525793896937420000000000000000000000000), (14692060358914769765643665104462494018323436349249057/78119091026143061051587793874840000000000000000000000000), (613605607788477415111083026245034563540952491621558379/2656049094888864075753984991744560000000000000000000000000), (1378840781647874675974853620315501989065259286504917689/5312098189777728151507969983489120000000000000000000000000), (2907684719073371041853943569482279956535126502126972899/10624196379555456303015939966978240000000000000000000000000)]
    reserve := (32684001/250000000000) }

theorem tilt_044_018_valid : tilt_044_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_018]
  · intro i; fin_cases i <;> norm_num [tilt_044_018]
  · norm_num [tilt_044_018]
  · norm_num [tilt_044_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_018]

def tilt_044_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (73231/10000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-12631868052388684756472114944948489703689209853/400233786911336453385925257689550000000000000000), (27850252576419/42171830000000), (-345172313608385435803179768529469819809145824739/100058446727834113346481314422387500000000000000), (27850252576419/42171830000000), (-1368057386381153058456246959172930789532894089103/400233786911336453385925257689550000000000000000)]
    bernstein := [(445592149794632652967425864914247043654983789825601/2354316393596096784623089751115000000000000000000000000), (1159179573268288321703034358085030337203226212358491/4708632787192193569246179502230000000000000000000000000), (138692774295025704388299065458759262451502294438277531/480280544293603744063110309227460000000000000000000000000), (101507743353051317813658181352277153398438815924902707/320187029529069162708740206151640000000000000000000000000), (211911007520627291649125326442765262209102107689367937/640374059058138325417480412303280000000000000000000000000)]
    reserve := (189266043/1000000000000) }

theorem tilt_044_019_valid : tilt_044_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_019]
  · intro i; fin_cases i <;> norm_num [tilt_044_019]
  · norm_num [tilt_044_019]
  · norm_num [tilt_044_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_019]

def tilt_044_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/100), (19/200)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
    cone := fun i => (![![0, 0, 0, (21947/10000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5346941/100000000), (1/100000000), (4217183/100000000), (4517121/100000000), (1/100000000), (1073147/20000000), (73231/10000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-12688602476433822684129585219046060599644709853/400233786911336453385925257689550000000000000000), (27850252576419/42171830000000), (-345141672620191369107598973544721069104872074739/100058446727834113346481314422387500000000000000), (27850252576419/42171830000000), (-1367878088004331653746266308959838215819843589103/400233786911336453385925257689550000000000000000)]
    bernstein := [(117769254140827274393127711201127223797823456325601/2354316393596096784623089751115000000000000000000000000), (503865904689597259215503873674091851195146063858491/4708632787192193569246179502230000000000000000000000000), (71885313007618473805255811194101011066212398449777531/480280544293603744063110309227460000000000000000000000000), (56992896973057693301565732563659724106096986340402707/320187029529069162708740206151640000000000000000000000000), (122929118870261642017128994522160106658012361899867937/640374059058138325417480412303280000000000000000000000000)]
    reserve := (6252837/125000000000) }

theorem tilt_044_020_valid : tilt_044_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_044_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_044_020]
  · intro i; fin_cases i <;> norm_num [tilt_044_020]
  · norm_num [tilt_044_020]
  · norm_num [tilt_044_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_044_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_044_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_044_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_044_020]

def tiltBundle044_row : Alternative → Row
  | .zero => tilt_044_000
  | (.spike 0 false false) => tilt_044_001
  | (.spike 0 false true) => tilt_044_002
  | (.spike 0 true false) => tilt_044_003
  | (.spike 0 true true) => tilt_044_004
  | (.spike 1 false false) => tilt_044_005
  | (.spike 1 false true) => tilt_044_006
  | (.spike 1 true false) => tilt_044_007
  | (.spike 1 true true) => tilt_044_008
  | (.spike 2 false false) => tilt_044_009
  | (.spike 2 false true) => tilt_044_010
  | (.spike 2 true false) => tilt_044_011
  | (.spike 2 true true) => tilt_044_012
  | (.spike 3 false false) => tilt_044_013
  | (.spike 3 false true) => tilt_044_014
  | (.spike 3 true false) => tilt_044_015
  | (.spike 3 true true) => tilt_044_016
  | (.spike 4 false false) => tilt_044_017
  | (.spike 4 false true) => tilt_044_018
  | (.spike 4 true false) => tilt_044_019
  | (.spike 4 true true) => tilt_044_020

def tiltBundle044 : TiltBundle where
  interval := ⟨(9/100), (19/200)⟩
  lambda := ![(7591187/50000000), (7591187/50000000), (1269161/12500000), (7356747/50000000), (7356747/50000000), (3062309/20000000), (14743433/100000000)]
  row := tiltBundle044_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_044_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_044_001_valid | exact tilt_044_002_valid | exact tilt_044_003_valid | exact tilt_044_004_valid | exact tilt_044_005_valid | exact tilt_044_006_valid | exact tilt_044_007_valid | exact tilt_044_008_valid | exact tilt_044_009_valid | exact tilt_044_010_valid | exact tilt_044_011_valid | exact tilt_044_012_valid | exact tilt_044_013_valid | exact tilt_044_014_valid | exact tilt_044_015_valid | exact tilt_044_016_valid | exact tilt_044_017_valid | exact tilt_044_018_valid | exact tilt_044_019_valid | exact tilt_044_020_valid
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
