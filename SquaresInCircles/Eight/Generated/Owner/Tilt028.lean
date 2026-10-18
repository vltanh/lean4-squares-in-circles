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

def tilt_028_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (5557957/100000000), (106207/50000000)]
    alternative := .zero
    polynomial := [(-21871719213880173461755795631472962355809287/2909200108788346623293893037731250000000000000), (267746938247213/423478400000000), (-18839670272831026852336184809170925152433934287/1454600054394173311646946518865625000000000000), (267746938247213/423478400000000), (-37657468826448173531210613822710377342512059287/2909200108788346623293893037731250000000000000)]
    bernstein := [(3615158419445031598209850221437553699093796310629513/30505174132728493488670171859320832000000000000000000000), (648454746271992021315094252981118198813025443265309/3813146766591061686083771482415104000000000000000000000), (286747108281077149035722145051253825983142418181911/1429930037471648132281414305905664000000000000000000000), (12507701143477844625426953560356528642504361343241/59580418227985338845058929412736000000000000000000000), (1476439913489901697266015866307150118787201627313/7447552278498167355632366176592000000000000000000000)]
    reserve := (118509679/1000000000000) }

theorem tilt_028_000_valid : tilt_028_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_000]
  · intro i; fin_cases i <;> norm_num [tilt_028_000]
  · norm_num [tilt_028_000]
  · norm_num [tilt_028_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_000]

def tilt_028_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2921/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (5557957/100000000), (216449/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1045891005792901419225449066929235129037769921/142294226410039753673186856788850000000000000000), (7102017071639166690349/11457684525200000000000), (-904710831210315904393581047007614149472708269921/71147113205019876836593428394425000000000000000), (7102017071639166690349/11457684525200000000000), (-1808375771414838907367936644948299063816378769921/142294226410039753673186856788850000000000000000)]
    bernstein := [(190551155355771610396472233963457572687403101557240479/1492063107521338447476155815442251776000000000000000000000), (11042154071787424531848659904579077485513352692907699/62169296146722435311506492310093824000000000000000000000), (14465700848985747763682483772343989068286135646998413/69940458165062739725444803848855552000000000000000000000), (209189657519120129028543695818863211521792966558851/971395252292538051742288942345216000000000000000000000), (74010101144372091997584544235975070427755264722879/364273219609701769403358353379456000000000000000000000)]
    reserve := (127709849/1000000000000) }

theorem tilt_028_001_valid : tilt_028_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_001]
  · intro i; fin_cases i <;> norm_num [tilt_028_001]
  · norm_num [tilt_028_001]
  · norm_num [tilt_028_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_001]

def tilt_028_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2163/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (3797/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (5557957/100000000), (208381/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-265802100332294604435518880967708364806775137447/34676810979618362871292056323029870000000000000000), (7116349400306270658401/11030606558800000000000), (-228805910043060603748181219423271295101906048037447/17338405489809181435646028161514935000000000000000), (7116349400306270658401/11030606558800000000000), (-457346017985788912891926919965574881839005320937447/34676810979618362871292056323029870000000000000000)]
    bernstein := [(49615135349580285258318948964004192813630528199210335353/363612717497643044661279392509773689651200000000000000000000), (8622676956368476645965302997491241697952954362720097679/45451589687205380582659924063721711206400000000000000000000), (3775332833990994719462834175994333007081398538263832891/17044346132702017718497471523895641702400000000000000000000), (164630425933453518475647834541366718758085360154899871/710181088862584071604061313495651737600000000000000000000), (19587543815688101408823692783749997816436029565912153/88772636107823008950507664186956467200000000000000000000)]
    reserve := (27290099/200000000000) }

theorem tilt_028_002_valid : tilt_028_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_002]
  · intro i; fin_cases i <;> norm_num [tilt_028_002]
  · norm_num [tilt_028_002]
  · norm_num [tilt_028_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_002]

def tilt_028_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5526489/100000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (5557957/100000000), (216449/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-138302993053318839445608049910010355422749807/18963137692527362749273781742195000000000000000), (7102017071639166690349/11457684525200000000000), (-120567101274912491334759451146439508742692099807/9481568846263681374636890871097500000000000000), (7102017071639166690349/11457684525200000000000), (-240995899556771663830073294242969007129961449807/18963137692527362749273781742195000000000000000)]
    bernstein := [(36728183188045509554582646550034939726219283211486993/198842910690795719221825049641038643200000000000000000000), (1943837396467883035221623155466094799905338145897733/8285121278783154967576043735043276800000000000000000000), (2459156753921496554591124890780793170669862640553971/9320761438631049338523049201923686400000000000000000000), (35258578295775502019577582227909047254997861666117/129455019980986796368375683360051200000000000000000000), (12631007427799030877844244504332904927893186747793/48545632492870048638140881260019200000000000000000000)]
    reserve := (184709543/1000000000000) }

theorem tilt_028_003_valid : tilt_028_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_003]
  · intro i; fin_cases i <;> norm_num [tilt_028_003]
  · norm_num [tilt_028_003]
  · norm_num [tilt_028_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_003]

def tilt_028_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1106397/20000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (5557957/100000000), (208381/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-138952549116983906446030797483959683990574483/18274454272444208397168135718575000000000000000), (7116349400306270658401/11030606558800000000000), (-120578105805556828768960433543349822130785824483/9137227136222104198584067859287500000000000000), (7116349400306270658401/11030606558800000000000), (-241017259061996673631474836289215684577581074483/18274454272444208397168135718575000000000000000)]
    bernstein := [(37938171570503937699999953676356333444423137466284717/191621541631824582642689750792404992000000000000000000000), (668678905965081391910519158835165484891936557407259/2661410300442008092259579872116736000000000000000000000), (2542371225672688994904164373593583015057294117907399/8982259763991777311376082068393984000000000000000000000), (12199336453833863816104507211010185190891147491291/41584535944406376441555935501824000000000000000000000), (13202091054966315352602824630541050903306151599917/46782602937457173496750427439552000000000000000000000)]
    reserve := (197984899/1000000000000) }

theorem tilt_028_004_valid : tilt_028_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_004]
  · intro i; fin_cases i <;> norm_num [tilt_028_004]
  · norm_num [tilt_028_004]
  · norm_num [tilt_028_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_004]

def tilt_028_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (861739/20000000), (1/100000000), (5557957/100000000), (216449/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-69772533086476656829490331735179292699627729/9482065254968978279458014094550000000000000000), (7102017071639166690349/11457684525200000000000), (-60287324206302906845814935675315465041951127729/4741032627484489139729007047275000000000000000), (7102017071639166690349/11457684525200000000000), (-120504875879519337034800381018895750791202627729/9482065254968978279458014094550000000000000000)]
    bernstein := [(11884778367903255982122346568131646139690135825721871/99426660567943513683609665872068608000000000000000000000), (2105819067465239250441191758423709375040018147282953/12428332570992939210451208234008576000000000000000000000), (925837376543246508463002211741083796568433896667037/4660624714122352203919203087753216000000000000000000000), (40231131851810797541771601522465220905183059939897/194192696421764675163300128656384000000000000000000000), (4733272734639033397202810477586933940159917399471/24274087052720584395412516082048000000000000000000000)]
    reserve := (59766557/500000000000) }

theorem tilt_028_005_valid : tilt_028_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_005]
  · intro i; fin_cases i <;> norm_num [tilt_028_005]
  · norm_num [tilt_028_005]
  · norm_num [tilt_028_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_005]

def tilt_028_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (269533/6250000), (1/100000000), (5557957/100000000), (208381/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-346999886282496817716659062481801609891123457/45683740230367915934377941210400000000000000000), (7116349400306270658401/11030606558800000000000), (-301429095630680370115806740082025521480059123457/22841870115183957967188970605200000000000000000), (7116349400306270658401/11030606558800000000000), (-602511191375078243413896821101569241350227123457/45683740230367915934377941210400000000000000000)]
    bernstein := [(98653288888907280196518023131411663591586694568573343/479028735957982678188062840826363904000000000000000000000), (15521123204921758080961698223152619417145629631406249/59878591994747834773507855103295488000000000000000000000), (2178115452147209151547118972733757189722107020065807/7484823999343479346688481887911936000000000000000000000), (281919216833066376670333366978513560183333867807801/935602999917934918336060235988992000000000000000000000), (33934637111081354624697743201875992819826847894143/116950374989741864792007529498624000000000000000000000)]
    reserve := (102972203/500000000000) }

theorem tilt_028_006_valid : tilt_028_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_006]
  · intro i; fin_cases i <;> norm_num [tilt_028_006]
  · norm_num [tilt_028_006]
  · norm_num [tilt_028_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_006]

def tilt_028_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (423283/10000000), (4310611/100000000), (1/100000000), (5557957/100000000), (216449/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-2232675118361775212453026882256142912791220639/303420948223202163436517135808100000000000000000), (5680287804986723815979/9161918206700000000000), (-1929208186627038223671665881630237260068063370639/151710474111601081718258567904050000000000000000), (5680287804986723815979/9161918206700000000000), (-3856183698135714672130878736378218377223335520639/303420948223202163436517135808100000000000000000)]
    bernstein := [(389772464818586358786495584832536310943235849497812961/3181599242040924317276093921971142656000000000000000000000), (68608153681775245410758780825700365079404701257524823/397699905255115539659511740246392832000000000000000000000), (590192487800856529852216168051965747910554957816417/2924264009228790732790527501811712000000000000000000000), (1307720923363770713983279749398192606801803199299527/6214061019611180307179870941349888000000000000000000000), (154082150268441004395899182723487560973956922594561/776757627451397538397483867668736000000000000000000000)]
    reserve := (122508347/1000000000000) }

theorem tilt_028_007_valid : tilt_028_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_007]
  · intro i; fin_cases i <;> norm_num [tilt_028_007]
  · norm_num [tilt_028_007]
  · norm_num [tilt_028_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_007]

def tilt_028_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (4236739/100000000), (4310611/100000000), (1/100000000), (5557957/100000000), (208381/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-5552110898281831708752011623581869144239566531/730952217590619278378835947485925000000000000000), (56944596669225187989793/88285590955900000000000), (-4822835276981213050956312918485276739249630941531/365476108795309639189417973742962500000000000000), (56944596669225187989793/88285590955900000000000), (-9640118443064144270203873825346971609355022316531/730952217590619278378835947485925000000000000000)]
    bernstein := [(1555692828050342263023572847752227549785556423427557869/7664589525123012004453662824710012928000000000000000000000), (245397931107708056743321867695256869749855870867945867/958073690640376500556707853088751616000000000000000000000), (103411420464909882305043111194641714387500627653834743/359277633990141187708765444908281856000000000000000000000), (4461803960514761709719202675953941109197198369660283/14969901416255882821198560204511744000000000000000000000), (536656254615146370868619521987719454412598635424269/1871237677031985352649820025563968000000000000000000000)]
    reserve := (202971447/1000000000000) }

theorem tilt_028_008_valid : tilt_028_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_008]
  · intro i; fin_cases i <;> norm_num [tilt_028_008]
  · norm_num [tilt_028_008]
  · norm_num [tilt_028_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_008]

def tilt_028_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (538587/12500000), (1/100000000), (5557957/100000000), (216449/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-348866410799578340550193297866032928878972837/47410337278252251362405122081200000000000000000), (7102017071639166690349/11457684525200000000000), (-301436694655988597161284583188660116620874972837/23705168639126125681202561040600000000000000000), (7102017071639166690349/11457684525200000000000), (-602524522901177615982018973079454200312870972837/47410337278252251362405122081200000000000000000)]
    bernstein := [(59385444829719414128807116636023850596471051519235963/497133418218806327245853132914163712000000000000000000000), (1169365539149663423039046571482967003513313828972101/6904630808594532322859071290474496000000000000000000000), (4627384854795346065720641037713266722485083471042561/23303128979006546589649365605351424000000000000000000000), (22342285673382066361484126744188889983797040371349/107884856384289567544672988913664000000000000000000000), (23656976571981128244984298157638927408305513228763/121370463432325763487757112527872000000000000000000000)]
    reserve := (119455749/1000000000000) }

theorem tilt_028_009_valid : tilt_028_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_009]
  · intro i; fin_cases i <;> norm_num [tilt_028_009]
  · norm_num [tilt_028_009]
  · norm_num [tilt_028_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_009]

def tilt_028_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4312529/100000000), (1/100000000), (5557957/100000000), (208381/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-344408081895925513638397952594968376605402387/45683750823630204403673893463450000000000000000), (7116349400306270658401/11030606558800000000000), (-301426573641978646399471282749895266185216902387/22841875411815102201836946731725000000000000000), (7116349400306270658401/11030606558800000000000), (-602508739202061367285304167547195563993828402387/45683750823630204403673893463450000000000000000)]
    bernstein := [(125857210553384376897404759457093467689776814102726413/479028847036388652127867565123305472000000000000000000000), (18921846496571610485471641287258453695542053689963259/59878605879548581515983445640413184000000000000000000000), (600746849102285071688937687442070878336056468233747/1727267477294670620653368624242688000000000000000000000), (335063307308514830861184458788726121856759824385291/935603216867946586187241338131456000000000000000000000), (40578166818799797580477035187186196138537858239213/116950402108493323273405167266432000000000000000000000)]
    reserve := (131367047/500000000000) }

theorem tilt_028_010_valid : tilt_028_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_010]
  · intro i; fin_cases i <;> norm_num [tilt_028_010]
  · norm_num [tilt_028_010]
  · norm_num [tilt_028_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_010]

def tilt_028_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3641/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (5557957/100000000), (216449/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1045954194570262679031579740336099372256479921/142294226410039753673186856788850000000000000000), (7102017071639166690349/11457684525200000000000), (-904710894399093265653387177681021013715926979921/71147113205019876836593428394425000000000000000), (7102017071639166690349/11457684525200000000000), (-1808375834603616268627742775621705928059597479921/142294226410039753673186856788850000000000000000)]
    bernstein := [(189887938737933176612948186927177351779786165242530479/1492063107521338447476155815442251776000000000000000000000), (11014518157902932991454276779337442495863705540397699/62169296146722435311506492310093824000000000000000000000), (14434608220459637880380478019092104232438514864628413/69940458165062739725444803848855552000000000000000000000), (208757783141341224830636372335843781186415509568851/971395252292538051742288942345216000000000000000000000), (73848135607050933501250596028827235345314574012879/364273219609701769403358353379456000000000000000000000)]
    reserve := (127265353/1000000000000) }

theorem tilt_028_011_valid : tilt_028_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_011]
  · intro i; fin_cases i <;> norm_num [tilt_028_011]
  · norm_num [tilt_028_011]
  · norm_num [tilt_028_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_011]

def tilt_028_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2157/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1893/50000000), (5557957/100000000), (208381/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-441698925900705295994860819723774990366936327667/57627252378559881411075289807300100000000000000000), (7116349400306270658401/11030606558800000000000), (-380238401880500555361055532513675745575327803327667/28813626189279940705537644903650050000000000000000), (7116349400306270658401/11030606558800000000000), (-760035104835100405426116204207627716160288670327667/57627252378559881411075289807300100000000000000000)]
    bernstein := [(82674663232738716524708578598762153262123949464737473133/604265537901008062104996830849795096576000000000000000000000), (14357288078653892765269394295824619435550913026570422219/75533192237626007763124603856224387072000000000000000000000), (6284415915231659651712609115555622546955320920774946551/28324947089109752911171726446084145152000000000000000000000), (274023480297824188156151432013111695365861920966038331/1180206128712906371298821935253506048000000000000000000000), (32605626403655400094748725274207648229197569183617933/147525766089113296412352741906688256000000000000000000000)]
    reserve := (136818431/1000000000000) }

theorem tilt_028_012_valid : tilt_028_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_012]
  · intro i; fin_cases i <;> norm_num [tilt_028_012]
  · norm_num [tilt_028_012]
  · norm_num [tilt_028_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_012]

def tilt_028_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (868/15625), (216449/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-553154792797563387633693410759739186987963/75852609060300667035774728192000000000000000), (7102017071639166690349/11457684525200000000000), (-482268718102521256092046744722488643522347963/37926304530150333517887364096000000000000000), (7102017071639166690349/11457684525200000000000), (-963984281412244948796459796034217547857707963/75852609060300667035774728192000000000000000)]
    bernstein := [(147517451252211579533143151340932082106258288403237/795372253980138322377045213886545920000000000000000000), (23401647547055880299139627288070195999984578136691/99421531747517290297130651735818240000000000000000000), (9864979427601158429263624955749567561586873519839/37283074405318983861423994400931840000000000000000000), (424284388600317617980368479326273830701364292259/1553461433554957660892666433372160000000000000000000), (50671720554149751091901068540474197526605130437/194182679194369707611583304171520000000000000000000)]
    reserve := (185469697/1000000000000) }

theorem tilt_028_013_valid : tilt_028_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_013]
  · intro i; fin_cases i <;> norm_num [tilt_028_013]
  · norm_num [tilt_028_013]
  · norm_num [tilt_028_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_013]

def tilt_028_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (1390179/25000000), (208381/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-347434461077613690851172812038802364724565371/45686100522344533153779145067400000000000000000), (7116349400306270658401/11030606558800000000000), (-301445085885708871342364138098706023005082565371/22843050261172266576889572533700000000000000000), (7116349400306270658401/11030606558800000000000), (-602542737310340128993877103385373243645440565371/45686100522344533153779145067400000000000000000)]
    bernstein := [(94285346146489470911751513553887633363332025054525029/479053485413179411962571208181940224000000000000000000000), (4991752599722608063812886577858703027881977815111249/19960561892215808831773800340914176000000000000000000000), (6329669041255349064499074194097058356958365984927263/22455632128742784935745525383528448000000000000000000000), (91130284989115768210527368570665717296908531352801/311883779565872012996465630326784000000000000000000000), (32868441058736863404237123949509562822663420487429/116956417337202004873674611372544000000000000000000000)]
    reserve := (98407953/500000000000) }

theorem tilt_028_014_valid : tilt_028_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_014]
  · intro i; fin_cases i <;> norm_num [tilt_028_014]
  · norm_num [tilt_028_014]
  · norm_num [tilt_028_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_014]

def tilt_028_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3641/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (5557957/100000000), (216449/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1045954194570262679031579740336099372256479921/142294226410039753673186856788850000000000000000), (7102017071639166690349/11457684525200000000000), (-904710894399093265653387177681021013715926979921/71147113205019876836593428394425000000000000000), (7102017071639166690349/11457684525200000000000), (-1808375834603616268627742775621705928059597479921/142294226410039753673186856788850000000000000000)]
    bernstein := [(189887938737933176612948186927177351779786165242530479/1492063107521338447476155815442251776000000000000000000000), (11014518157902932991454276779337442495863705540397699/62169296146722435311506492310093824000000000000000000000), (14434608220459637880380478019092104232438514864628413/69940458165062739725444803848855552000000000000000000000), (208757783141341224830636372335843781186415509568851/971395252292538051742288942345216000000000000000000000), (73848135607050933501250596028827235345314574012879/364273219609701769403358353379456000000000000000000000)]
    reserve := (127265353/1000000000000) }

theorem tilt_028_015_valid : tilt_028_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_015]
  · intro i; fin_cases i <;> norm_num [tilt_028_015]
  · norm_num [tilt_028_015]
  · norm_num [tilt_028_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_015]

def tilt_028_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2157/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1893/50000000), (5557957/100000000), (208381/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-441698925900705295994860819723774990366936327667/57627252378559881411075289807300100000000000000000), (7116349400306270658401/11030606558800000000000), (-380238401880500555361055532513675745575327803327667/28813626189279940705537644903650050000000000000000), (7116349400306270658401/11030606558800000000000), (-760035104835100405426116204207627716160288670327667/57627252378559881411075289807300100000000000000000)]
    bernstein := [(82674663232738716524708578598762153262123949464737473133/604265537901008062104996830849795096576000000000000000000000), (14357288078653892765269394295824619435550913026570422219/75533192237626007763124603856224387072000000000000000000000), (6284415915231659651712609115555622546955320920774946551/28324947089109752911171726446084145152000000000000000000000), (274023480297824188156151432013111695365861920966038331/1180206128712906371298821935253506048000000000000000000000), (32605626403655400094748725274207648229197569183617933/147525766089113296412352741906688256000000000000000000000)]
    reserve := (136818431/1000000000000) }

theorem tilt_028_016_valid : tilt_028_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_016]
  · intro i; fin_cases i <;> norm_num [tilt_028_016]
  · norm_num [tilt_028_016]
  · norm_num [tilt_028_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_016]

def tilt_028_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (868/15625), (216449/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-110631365347654219542545108063736505215583/15170521812060133407154945638400000000000000), (7102017071639166690349/11457684525200000000000), (-96453744027292392760425155370409517372287583/7585260906030066703577472819200000000000000), (7102017071639166690349/11457684525200000000000), (-192796856689237131301307765632755298239359583/15170521812060133407154945638400000000000000)]
    bernstein := [(29499220684442203968686841102850679118202112719617/159074450796027664475409042777309184000000000000000000), (4679795777195503543851971628484864804540097871031/19884306349503458059426130347163648000000000000000000), (1972795721612937177981951378591302023797103627699/7456614881063796772284798880186368000000000000000000), (84848536933161829113184628324958538679522970919/310692286710991532178533286674432000000000000000000), (10133301431058761581923167004572214365580214817/38836535838873941522316660834304000000000000000000)]
    reserve := (185442857/1000000000000) }

theorem tilt_028_017_valid : tilt_028_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_017]
  · intro i; fin_cases i <;> norm_num [tilt_028_017]
  · norm_num [tilt_028_017]
  · norm_num [tilt_028_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_017]

def tilt_028_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (1390179/25000000), (208381/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-346558918383160741244390175758116652690745371/45686100522344533153779145067400000000000000000), (7116349400306270658401/11030606558800000000000), (-301444210343014418392757355462425337293048745371/22843050261172266576889572533700000000000000000), (7116349400306270658401/11030606558800000000000), (-602541861767645676044270320749092557933406745371/45686100522344533153779145067400000000000000000)]
    bernstein := [(103474865058501815401994600757164292362876811920345029/479053485413179411962571208181940224000000000000000000000), (5374675383111227753891342583000657144262388508531249/19960561892215808831773800340914176000000000000000000000), (6760488007758487970236444973309778532549877100467263/22455632128742784935745525383528448000000000000000000000), (97114329501069814846566842496543652077385036932801/311883779565872012996465630326784000000000000000000000), (35112632968701358289291984046799460593462878307429/116956417337202004873674611372544000000000000000000000)]
    reserve := (53999641/250000000000) }

theorem tilt_028_018_valid : tilt_028_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_018]
  · intro i; fin_cases i <;> norm_num [tilt_028_018]
  · norm_num [tilt_028_018]
  · norm_num [tilt_028_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_018]

def tilt_028_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (5557957/100000000), (106207/50000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-85590707808772465352589031658317304126464523/11636800435153386493175572150925000000000000000), (267746938247213/423478400000000), (-150717509335611387946582492182846105084664881171/11636800435153386493175572150925000000000000000), (267746938247213/423478400000000), (-18828989828475326935153737893898473472567302081/1454600054394173311646946518865625000000000000)]
    bernstein := [(4292832995085833437868071354491955369875460038192319/15252587066364246744335085929660416000000000000000000000), (9920050957795125766632345956417955147916307151353/29790209113992669422529464706368000000000000000000000), (86623061257282955500325706821846930967490240118381/238321672911941355380235717650944000000000000000000000), (5553910407031434442719271710036620744795405726029/14895104556996334711264732353184000000000000000000000), (1344964365696498101103785037899145496520848166219/3723776139249083677816183088296000000000000000000000)]
    reserve := (281449499/1000000000000) }

theorem tilt_028_019_valid : tilt_028_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_019]
  · intro i; fin_cases i <;> norm_num [tilt_028_019]
  · norm_num [tilt_028_019]
  · norm_num [tilt_028_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_019]

def tilt_028_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/320), (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1382309/25000000), (1/100000000), (132337/3125000), (4310611/100000000), (1/100000000), (5557957/100000000), (106207/50000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-87464922391993952119207749290777614451214523/11636800435153386493175572150925000000000000000), (267746938247213/423478400000000), (-150713673069082428330851191500000451965893381171/11636800435153386493175572150925000000000000000), (267746938247213/423478400000000), (-18828276018336304297341497968838709293930270831/1454600054394173311646946518865625000000000000)]
    bernstein := [(1838670276790873567465644755614439550905532350223569/15252587066364246744335085929660416000000000000000000000), (164067217604594974853929149980891123474841079702671/953286691647765421520942870603776000000000000000000000), (144846826890837094937826341408061621986689913948893/714965018735824066140707152952832000000000000000000000), (789448859685034418119532873089843135704815083851/3723776139249083677816183088296000000000000000000000), (745983666181553281569867772006036580533785197469/3723776139249083677816183088296000000000000000000000)]
    reserve := (30137023/250000000000) }

theorem tilt_028_020_valid : tilt_028_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_028_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_028_020]
  · intro i; fin_cases i <;> norm_num [tilt_028_020]
  · norm_num [tilt_028_020]
  · norm_num [tilt_028_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_028_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_028_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_028_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_028_020]

def tiltBundle028_row : Alternative → Row
  | .zero => tilt_028_000
  | (.spike 0 false false) => tilt_028_001
  | (.spike 0 false true) => tilt_028_002
  | (.spike 0 true false) => tilt_028_003
  | (.spike 0 true true) => tilt_028_004
  | (.spike 1 false false) => tilt_028_005
  | (.spike 1 false true) => tilt_028_006
  | (.spike 1 true false) => tilt_028_007
  | (.spike 1 true true) => tilt_028_008
  | (.spike 2 false false) => tilt_028_009
  | (.spike 2 false true) => tilt_028_010
  | (.spike 2 true false) => tilt_028_011
  | (.spike 2 true true) => tilt_028_012
  | (.spike 3 false false) => tilt_028_013
  | (.spike 3 false true) => tilt_028_014
  | (.spike 3 true false) => tilt_028_015
  | (.spike 3 true true) => tilt_028_016
  | (.spike 4 false false) => tilt_028_017
  | (.spike 4 false true) => tilt_028_018
  | (.spike 4 true false) => tilt_028_019
  | (.spike 4 true true) => tilt_028_020

def tiltBundle028 : TiltBundle where
  interval := ⟨(7/320), (1/40)⟩
  lambda := ![(14605301/100000000), (14605301/100000000), (8882969/100000000), (14564229/100000000), (14564229/100000000), (16483339/100000000), (16294633/100000000)]
  row := tiltBundle028_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_028_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_028_001_valid | exact tilt_028_002_valid | exact tilt_028_003_valid | exact tilt_028_004_valid | exact tilt_028_005_valid | exact tilt_028_006_valid | exact tilt_028_007_valid | exact tilt_028_008_valid | exact tilt_028_009_valid | exact tilt_028_010_valid | exact tilt_028_011_valid | exact tilt_028_012_valid | exact tilt_028_013_valid | exact tilt_028_014_valid | exact tilt_028_015_valid | exact tilt_028_016_valid | exact tilt_028_017_valid | exact tilt_028_018_valid | exact tilt_028_019_valid | exact tilt_028_020_valid
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
